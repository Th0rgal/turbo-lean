import LeanNative.Frontend.ProofRetention
import LeanNative.Backend.LLVMAst.SemanticsProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.PTXLowerProofs
import LeanNative.Proofs.MetalLowerProofs

namespace LeanNative.Proofs

open LeanNative.IR LeanNative.Semantics LeanNative.Frontend.ProofRetention
open LeanNative.Backend LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst hiding ByteMemory Dim3
open LeanNative.Backend.MetalAst hiding ByteMemory Dim3
open LeanNative.Proofs.PTXSIMT LeanNative.Proofs.MetalSIMT
open LeanNative.Backend.PTXLower LeanNative.Backend.MetalLower

set_option autoImplicit false

-- Fact interpretation. Every helper below is a theorem: this module declares no `def`.

theorem evalExpr_isExclusive_of_obj (env : VarEnv) (st : HeapState) (o : VarId)
    (h : match env o with
      | some (.sarrayId b) =>
        (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
      | some (.objPtr i) => st.getObjRefCount i = 1
      | some _ => True
      | none => False) :
    evalExpr env st (.isExclusive o) = .ok (.bool true, st) := by
  simp only [evalExpr]
  cases henv : env o with
  | none => simp [henv] at h
  | some v =>
    cases v with
    | sarrayId b => simp only [henv] at h; rcases h with ⟨⟨buf, hf, he⟩, _⟩; simp [hf, he]
    | objPtr i => simp only [henv] at h; simp [h]
    | u64 _ | u256 _ | bool _ | tuple _ | rawPtrId _ | storageMapId _ | unit => simp

theorem evalExpr_ensureExclusive_of_obj (env : VarEnv) (st st1 : HeapState) (o : VarId)
    (ty : LNIRType) (vv : Val)
    (h : match env o with
      | some (.sarrayId b) =>
        (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
      | some (.objPtr i) => st.getObjRefCount i = 1
      | some _ => True
      | none => False)
    (he : evalExpr env st (.sarrayEnsureExclusive o ty) = .ok (vv, st1)) :
    st1 = st ∧ evalExpr env st (.scalar (.var o)) = .ok (vv, st) := by
  simp only [evalExpr] at he
  cases henv : env o with
  | none => simp [henv] at he
  | some v =>
    cases v with
    | sarrayId b =>
      simp only [henv] at h he; rcases h with ⟨⟨buf, hf, _⟩, hx⟩
      rw [ensureExclusive_of_exclusive st b buf hf hx] at he; cases he
      exact ⟨rfl, by simp [evalExpr, evalScalarExpr, henv]⟩
    | u64 _ | u256 _ | bool _ | tuple _ | objPtr _ | rawPtrId _ | storageMapId _ | unit =>
      simp [henv] at he

private theorem true_eval (env : VarEnv) (st : HeapState) :
    evalExpr env st (.scalar (.constBool true)) = .ok (.bool true, st) := by
  simp [evalExpr, evalScalarExpr]

private theorem ctorGet_state (env : VarEnv) (st st' : HeapState) (c : VarId) (i : Nat)
    (isObj : Bool) (v : Val) (he : evalCtorGet env st c i isObj = .ok (v, st')) : st' = st := by
  cases vc : env c with
  | none => simp [evalCtorGet, vc] at he
  | some val =>
    cases val with
    | objPtr oid =>
      cases ho : st.liveHeapObj oid with
      | error _ => simp [evalCtorGet, vc, ho, Except.bind] at he
      | ok o =>
        simp only [evalCtorGet, vc, ho, Except.bind] at he
        split at he <;> cases he <;> rfl
    | tuple xs =>
      cases xs with
      | nil => simp [evalCtorGet, vc] at he
      | cons _ _ =>
        simp only [evalCtorGet, vc] at he
        split at he <;> cases he <;> rfl
    | u64 _ | u256 _ | bool _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit =>
      simp [evalCtorGet, vc] at he

private theorem heap_state (env : VarEnv) (st st' : HeapState) (e : LNIRExpr) (v : Val)
    (hp : exprPreservesHeap e = true) (he : evalExpr env st e = .ok (v, st')) : st' = st := by
  cases e with
  | ctorGetObj c i => exact ctorGet_state env st st' c i true v he
  | ctorGetScalar c i _ => exact ctorGet_state env st st' c i false v he
  | constU256 _ => cases he <;> rfl
  | storageStore _ _ _ | allocCtor _ _ _ | sarrayEnsureExclusive _ _
  | sarraySet _ _ _ _ => simp [exprPreservesHeap] at hp
  | call fn args retTy isExt =>
    simp only [exprPreservesHeap, Bool.or_eq_true, beq_iff_eq] at hp
    simp only [evalExpr] at he
    cases hvl : evalVarList env args with
    | error _ => simp [hvl] at he
    | ok vals =>
      simp only [hvl] at he
      cases isExt with
      | true => simp at he
      | false =>
        rcases hp with ((rfl | rfl) | rfl) | rfl
        · simp only [beq_self_eq_true, Bool.true_or, ite_true] at he
          cases vals with
          | nil => simp at he
          | cons v0 rest =>
            cases rest with
            | nil => cases he; rfl
            | cons _ _ => simp at he
        · simp only [beq_self_eq_true, Bool.or_true, ite_true] at he
          cases vals with
          | nil => simp at he
          | cons v0 rest =>
            cases rest with
            | nil => cases he; rfl
            | cons _ _ => simp at he
        · simp only [show ("lean_native_sarray_len" == "lean_native_box_u64") = false from rfl,
            show ("lean_native_sarray_len" == "lean_native_unbox_u64") = false from rfl,
            show ("lean_native_sarray_len" == "lean_native_ensure_exclusive") = false from rfl,
            beq_self_eq_true, Bool.false_or, Bool.false_eq_true, ite_false, ite_true] at he
          split at he
          · split at he <;> cases he <;> rfl
          · cases he
        · simp only [show ("lean_native_ctor_tag" == "lean_native_box_u64") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_unbox_u64") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_ensure_exclusive") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_sarray_len") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_mark_mt") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_ctor_set") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_ctor_set_scalar") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_ctor_set_tag") = false from rfl,
            show ("lean_native_ctor_tag" == "lean_native_del_obj") = false from rfl,
            beq_self_eq_true, Bool.false_or, Bool.false_eq_true, ite_false, ite_true] at he
          split at he
          · rename_i objId
            cases ho : st.liveHeapObj objId with
            | error _ => simp [ho, Except.map] at he
            | ok o => simp only [ho, Except.map] at he; cases he; rfl
          · cases he; rfl
          · cases he; rfl
          · cases he; rfl
          · cases he
  | scalar _ | mulDivDown _ _ _ | mulDivUp _ _ _ | storageLoad _ _ | mkTuple _ | projTuple _ _
  | isExclusive _ | sarrayLen _ | sarrayDataPtr _ _ | sarrayGet _ _ _ | rawLoad _ _ _
  | boxScalar _ _ | unboxScalar _ _ =>
    revert he; simp only [evalExpr]; repeat split
    all_goals intro he; try split at he; all_goals try split at he
    all_goals simp at he; all_goals exact he.2.symm

private theorem survives_bind (env : VarEnv) (st : HeapState) (dst : VarId) (v : Val)
    (f : RetainedFact) (hm : factMentions dst f = false)
    (hf : match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False) :
    match f with
    | .idxLt i n =>
      ∃ iv nv : UInt64, (env.bind dst v) i = some (.u64 iv) ∧ (env.bind dst v) n = some (.u64 nv) ∧
        iv.toNat < nv.toNat
    | .noOverflowAdd a b nsw nuw =>
      ∃ av bv : UInt64, (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
        (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
        (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
    | .noOverflowSub a b nsw nuw =>
      ∃ av bv : UInt64, (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
        (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
        (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
    | .noOverflowMul a b nsw nuw =>
      ∃ av bv : UInt64, (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
        (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
        (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
    | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, (env.bind dst v) p = some (.u64 pv) ∧ pv.toNat % n = 0
    | .disjointSlices a b la lb =>
      ∃ av bv lav lbv : UInt64,
        (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
        (env.bind dst v) la = some (.u64 lav) ∧ (env.bind dst v) lb = some (.u64 lbv) ∧
        rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
    | .exclusiveObj o =>
      match (env.bind dst v) o with
      | some (.sarrayId b) =>
        (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
      | some (.objPtr i) => st.getObjRefCount i = 1
      | some _ => True
      | none => False := by
  cases f with
  | idxLt i n =>
    simp only [factMentions, Bool.or_eq_false_iff] at hm; rcases hm with ⟨hi, hn⟩
    rcases hf with ⟨iv, nv, h1, h2, hr⟩
    exact ⟨iv, nv, by simpa [VarEnv.bind, hi] using h1, by simpa [VarEnv.bind, hn] using h2, hr⟩
  | noOverflowAdd a b nsw nuw | noOverflowSub a b nsw nuw | noOverflowMul a b nsw nuw =>
    simp only [factMentions, Bool.or_eq_false_iff] at hm; rcases hm with ⟨ha, hb⟩
    rcases hf with ⟨av, bv, h1, h2, hnsw, hnuw⟩
    exact ⟨av, bv, by simpa [VarEnv.bind, ha] using h1, by simpa [VarEnv.bind, hb] using h2, hnsw, hnuw⟩
  | alignedPtr p n =>
    simp only [factMentions] at hm; rcases hf with ⟨hn, pv, hp, hmod⟩
    exact ⟨hn, pv, by simpa [VarEnv.bind, hm] using hp, hmod⟩
  | disjointSlices a b la lb =>
    simp only [factMentions, Bool.or_eq_false_iff] at hm
    rcases hm with ⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩
    rcases hf with ⟨av, bv, lav, lbv, h1, h2, h3, h4, hr⟩
    exact ⟨av, bv, lav, lbv, by simpa [VarEnv.bind, ha] using h1,
      by simpa [VarEnv.bind, hb] using h2, by simpa [VarEnv.bind, hla] using h3,
      by simpa [VarEnv.bind, hlb] using h4, hr⟩
  | exclusiveObj o =>
    simp only [factMentions] at hm
    simpa [VarEnv.bind, hm] using hf

private theorem holds_kill (env : VarEnv) (st : HeapState) (dst : VarId) (v : Val)
    (facts : FactEnv)
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False) :
    ∀ f, factMember (killVarFacts dst facts) f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64, (env.bind dst v) i = some (.u64 iv) ∧ (env.bind dst v) n = some (.u64 nv) ∧
          iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, (env.bind dst v) p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          (env.bind dst v) a = some (.u64 av) ∧ (env.bind dst v) b = some (.u64 bv) ∧
          (env.bind dst v) la = some (.u64 lav) ∧ (env.bind dst v) lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match (env.bind dst v) o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False := by
  intro f hmem; unfold killVarFacts factMember at hmem
  rw [List.contains_eq_mem] at hmem
  rcases List.mem_filter.mp (of_decide_eq_true hmem) with ⟨hin, hm⟩
  have hmem0 : factMember facts f = true := by
    unfold factMember; rw [List.contains_eq_mem]; exact decide_eq_true hin
  have hm0 : factMentions dst f = false := by simpa using hm
  have h0 := hf f hmem0
  cases f with
  | idxLt i n => exact survives_bind env st dst v (.idxLt i n) hm0 h0
  | noOverflowAdd a b nsw nuw => exact survives_bind env st dst v (.noOverflowAdd a b nsw nuw) hm0 h0
  | noOverflowSub a b nsw nuw => exact survives_bind env st dst v (.noOverflowSub a b nsw nuw) hm0 h0
  | noOverflowMul a b nsw nuw => exact survives_bind env st dst v (.noOverflowMul a b nsw nuw) hm0 h0
  | alignedPtr p n => exact survives_bind env st dst v (.alignedPtr p n) hm0 h0
  | disjointSlices a b la lb => exact survives_bind env st dst v (.disjointSlices a b la lb) hm0 h0
  | exclusiveObj o => exact survives_bind env st dst v (.exclusiveObj o) hm0 h0

private theorem holds_clear (env : VarEnv) (st st' : HeapState) (facts : FactEnv)
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False) :
    ∀ f, factMember (clearHeapFacts facts) f = true →
      match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st'.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st'.buffers b
        | some (.objPtr i) => st'.getObjRefCount i = 1
        | some _ => True
        | none => False := by
  intro f hmem; unfold clearHeapFacts factMember at hmem
  rw [List.contains_eq_mem] at hmem
  rcases List.mem_filter.mp (of_decide_eq_true hmem) with ⟨hin, hkeep⟩
  have hmem0 : factMember facts f = true := by
    unfold factMember; rw [List.contains_eq_mem]; exact decide_eq_true hin
  have h0 := hf f hmem0
  cases f with
  | exclusiveObj _ => simp at hkeep
  | _ => exact h0

private theorem holds_cons (env : VarEnv) (st : HeapState) (f0 : RetainedFact) (facts : FactEnv)
    (hf0 : match f0 with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False)
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False) :
    ∀ f, factMember (consFact facts f0) f = true →
      match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False := by
  intro f hmem; unfold consFact at hmem; split at hmem
  · exact hf f hmem
  · simp only [factMember, List.contains_eq_mem, List.decide_mem_cons, Bool.or_eq_true, beq_iff_eq] at hmem
    rcases hmem with rfl | hm
    · exact hf0
    · exact hf f (decide_eq_true hm)

private theorem intro_holds (env : VarEnv) (st st1 : HeapState) (dst : VarId) (val : LNIRExpr)
    (vv : Val) (facts : FactEnv) (hval : evalExpr env st val = .ok (vv, st1))
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64, (env.bind dst vv) i = some (.u64 iv) ∧ (env.bind dst vv) n = some (.u64 nv) ∧
          iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, (env.bind dst vv) p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (env.bind dst vv) la = some (.u64 lav) ∧ (env.bind dst vv) lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match (env.bind dst vv) o with
        | some (.sarrayId b) =>
          (∃ buf, st1.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st1.buffers b
        | some (.objPtr i) => st1.getObjRefCount i = 1
        | some _ => True
        | none => False) :
    ∀ f, factMember (introExprFact dst val facts) f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64, (env.bind dst vv) i = some (.u64 iv) ∧ (env.bind dst vv) n = some (.u64 nv) ∧
          iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, (env.bind dst vv) p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          (env.bind dst vv) a = some (.u64 av) ∧ (env.bind dst vv) b = some (.u64 bv) ∧
          (env.bind dst vv) la = some (.u64 lav) ∧ (env.bind dst vv) lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match (env.bind dst vv) o with
        | some (.sarrayId b) =>
          (∃ buf, st1.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st1.buffers b
        | some (.objPtr i) => st1.getObjRefCount i = 1
        | some _ => True
        | none => False := by
  cases val with
  | sarrayEnsureExclusive arrVar _ =>
    simp only [evalExpr] at hval
    cases ha : env arrVar with
    | none => simp [ha] at hval
    | some av =>
      cases av with
      | sarrayId bid =>
        simp only [ha] at hval
        cases hens : st.ensureExclusive bid with
        | error _ => simp [hens] at hval
        | ok s' =>
          simp only [hens] at hval; injection hval with hpair
          injection hpair with hvv hs; subst hvv; subst hs
          rcases ensureExclusive_post st s' bid hens with ⟨hexcl, buf1, hfind1⟩
          have hb1 : s'.buffers.find? (fun b => b.id == bid) = some buf1 := hfind1
          have hid := List.find?_some hb1
          have hex1 := hexcl buf1 (List.mem_of_find?_eq_some hb1) hid
          exact holds_cons _ _ _ _ (by simp [VarEnv.bind, hfind1, hex1, hexcl]) hf
      | u64 _ | u256 _ | bool _ | tuple _ | objPtr _ | rawPtrId _ | storageMapId _ | unit =>
        simp [ha] at hval
  | allocCtor tag objFields scalarFields =>
    simp only [evalExpr] at hval
    cases hobj : evalVarList env objFields with
    | error _ => simp [hobj] at hval
    | ok objs =>
      cases hsc : evalVarList env scalarFields with
      | error _ => simp [hobj, hsc] at hval
      | ok scalars =>
        simp only [hobj, hsc] at hval
        by_cases hemp : (objs.isEmpty && scalars.isEmpty) = true
        · simp only [hemp, ite_true] at hval
          injection hval with hpair; injection hpair with hvv hs
          subst hvv; subst hs
          exact holds_cons _ _ _ _ (by simp [VarEnv.bind]) hf
        · have hemp0 : (objs.isEmpty && scalars.isEmpty) = false := Bool.eq_false_iff.mpr hemp
          simp only [hemp0, Bool.false_eq_true, ite_false] at hval
          by_cases hwf : (!objs.all Val.wfField) = true
          · simp [hwf] at hval
          · have hwf0 : (!objs.all Val.wfField) = false := Bool.eq_false_iff.mpr hwf
            simp only [hwf0, Bool.false_eq_true, ite_false, HeapState.allocHeapCtor] at hval
            injection hval with hpair; injection hpair with hvv hs
            subst hvv; subst hs
            exact holds_cons _ _ _ _
              (by simp [VarEnv.bind, HeapState.getObjRefCount]) hf
  | _ => exact hf

theorem dischargeRetainedExclusivity_sound
    (fuel : Nat) (env : VarEnv) (st : HeapState) (facts : FactEnv) (code : LNIRCode)
    (hfacts : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
          env la = some (.u64 lav) ∧ env lb = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj o =>
        match env o with
        | some (.sarrayId b) =>
          (∃ buf, st.findBuffer b = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers b
        | some (.objPtr i) => st.getObjRefCount i = 1
        | some _ => True
        | none => False)
    (v : Val) (st' : HeapState)
    (heval : evalCode fuel env st code = .ok (v, st')) :
    evalCode fuel env st (dischargeRetainedExclusivity facts code) = .ok (v, st') := by
  induction code generalizing fuel env st facts v st' with
  | letBind dst _ val _ ih =>
    simp only [evalCode] at heval
    cases hval : evalExpr env st val with
    | error _ => simp [hval] at heval
    | ok pair =>
      rcases pair with ⟨vv, st1⟩; simp only [hval] at heval
      by_cases hp : exprPreservesExcl facts val = true
      · have hstep : st1 = st ∧ evalExpr env st (specializeExclExpr facts val) = .ok (vv, st) := by
          cases val with
          | isExclusive objVar =>
            have hst := heap_state env st st1 _ vv rfl hval
            by_cases hmem : factMember facts (.exclusiveObj objVar) = true
            · have hobj := hfacts _ hmem
              simp only at hobj
              rw [evalExpr_isExclusive_of_obj env st objVar hobj] at hval; cases hval; rw [hst]
              exact ⟨rfl, by simp [specializeExclExpr, hmem, true_eval]⟩
            · exact ⟨hst, by simp [specializeExclExpr, hmem, hst, hval]⟩
          | sarrayEnsureExclusive objVar ety =>
            have hmem : factMember facts (.exclusiveObj objVar) = true := by
              simpa [exprPreservesExcl] using hp
            have hobj := hfacts _ hmem
            simp only at hobj
            rcases evalExpr_ensureExclusive_of_obj env st st1 objVar ety vv hobj hval with ⟨hst, hev⟩
            exact ⟨hst, by simp [specializeExclExpr, hmem, hev]⟩
          | _ =>
            have hst := heap_state env st st1 _ vv (by simpa [exprPreservesExcl] using hp) hval
            exact ⟨hst, by simp [specializeExclExpr, hst, hval]⟩
        rcases hstep with ⟨hst, hev'⟩; rw [hst] at hval heval
        simp only [dischargeRetainedExclusivity, hp, ite_true, evalCode, hev']
        exact ih fuel _ st _
          (intro_holds env st st dst val vv _ hval (holds_kill env st dst vv facts hfacts)) v st' heval
      · have hp0 : exprPreservesExcl facts val = false := Bool.eq_false_iff.mpr hp
        have hvm : specializeExclExpr facts val = val := by
          cases val with
          | isExclusive _ => simp [exprPreservesExcl, exprPreservesHeap] at hp0
          | sarrayEnsureExclusive _ _ => simp only [exprPreservesExcl] at hp0; simp [specializeExclExpr, hp0]
          | _ => rfl
        simp only [dischargeRetainedExclusivity, hp0, Bool.false_eq_true, ite_false, hvm, evalCode, hval]
        exact ih fuel _ st1 _
          (intro_holds env st st1 dst val vv _ hval
            (holds_kill env st1 dst vv _ (holds_clear env st st1 facts hfacts))) v st' heval
  | rawStore ptrVar idxVar valVar _ _ ih =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hp : env ptrVar <;> cases hi : env idxVar <;> cases hv : env valVar
    all_goals simp only [hp, hi, hv] at heval ⊢; try exact heval
    rename_i pv iv vv
    cases pv <;> cases iv
    all_goals cases vv <;> try exact heval
    all_goals
      simp only at heval ⊢
      cases hw : st.writeElemExclusive _ _ _ with
      | error _ => rw [hw] at heval; exact heval
      | ok s1 => rw [hw] at heval; exact ih fuel env s1 _ (holds_clear env st s1 facts hfacts) v st' heval
  | incRef objVar cnt _ ih =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hinc : st.evalIncRef env objVar cnt with
    | error _ => rw [hinc] at heval; exact heval
    | ok s1 => rw [hinc] at heval; exact ih fuel env s1 _ (holds_clear env st s1 facts hfacts) v st' heval
  | decRef objVar cnt _ ih =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hdec : st.evalDecRef env objVar cnt with
    | error _ => rw [hdec] at heval; exact heval
    | ok s1 => rw [hdec] at heval; exact ih fuel env s1 _ (holds_clear env st s1 facts hfacts) v st' heval
  | parFor out _ _ _ _ _ ih =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hpar : evalParFor fuel env st _ _ _ with
    | error _ => simp [hpar] at heval
    | ok pr =>
      simp only [hpar] at heval
      exact ih fuel _ pr.2 _ (holds_kill env pr.2 out pr.1 _ (holds_clear env st pr.2 facts hfacts))
        v st' heval
  | seqFor idx lo hi acc init _ body _ ihb ihk =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hlo : env lo <;> cases hhi : env hi
    all_goals cases hinit : env init <;> simp only [hlo, hhi, hinit] at heval ⊢
    all_goals try exact heval
    rename_i vlo vhi vinit
    cases vlo <;> cases vhi <;> try exact heval
    rename_i uLo uHi
    dsimp only at heval ⊢
    have hloop : ∀ cnt cur av s0 pr,
        evalSeqLoop cnt cur idx acc av env s0 (fun e s => evalCode fuel e s body) = .ok pr →
        evalSeqLoop cnt cur idx acc av env s0
          (fun e s => evalCode fuel e s (dischargeRetainedExclusivity [] body)) = .ok pr := by
      intro cnt
      induction cnt with
      | zero => intro cur av s0 pr h; exact h
      | succ c ihc =>
        intro cur av s0 pr h
        simp only [evalSeqLoop] at h ⊢
        cases hs : evalCode fuel ((env.bind idx (.u64 cur.toUInt64)).bind acc av) s0 body with
        | error _ => simp [hs] at h
        | ok p1 =>
          simp only [hs] at h
          have hs' := ihb fuel _ s0 [] (fun _ hm => nomatch hm) p1.1 p1.2 hs
          simp only [hs']
          exact ihc (cur + 1) p1.1 p1.2 pr h
    cases hl : evalSeqLoop (uHi.toNat - uLo.toNat) uLo.toNat idx acc vinit env st
        (fun e s => evalCode fuel e s body) with
    | error _ => rw [hl] at heval; cases heval
    | ok pr =>
      rw [hl] at heval
      rw [hloop (uHi.toNat - uLo.toNat) uLo.toNat vinit st pr hl]
      exact ihk fuel _ pr.2 _ (holds_kill env pr.2 acc pr.1 _ (holds_clear env st pr.2 facts hfacts))
        v st' heval
  | ite c _ _ iht ihe =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hc : env c with
    | none => simp [hc] at heval
    | some cv =>
      cases cv with
      | bool b =>
        cases b <;> simp [hc] at heval ⊢
        · exact ihe fuel env st facts hfacts v st' heval
        · exact iht fuel env st facts hfacts v st' heval
      | u64 n =>
        by_cases hn : n = 0 <;> simp [hc, hn] at heval ⊢
        · exact ihe fuel env st facts hfacts v st' heval
        · exact iht fuel env st facts hfacts v st' heval
      | u256 w =>
        by_cases hw : w = UInt256.zero <;> simp [hc, hw] at heval ⊢
        · exact ihe fuel env st facts hfacts v st' heval
        · exact iht fuel env st facts hfacts v st' heval
      | tuple _ | objPtr _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit => simp [hc] at heval
  | ret _ => simpa [dischargeRetainedExclusivity] using heval
  | unreachable => simp [evalCode] at heval

theorem dischargeLocalExclusivity_refines (code : LNIRCode) :
    CodeRefines code (dischargeRetainedExclusivity [] code) :=
  fun fuel env st v st' h =>
    dischargeRetainedExclusivity_sound fuel env st [] code (fun _ hm => nomatch hm) v st' h

-- LLVM specialization.

private theorem llvm_lookup (st : ExecState) (v : VarId) (u u' : UInt64)
    (hreg : st.regs.lookup (llvmRegOf v) = some (.bits .i64 u.toBitVec))
    (henv : (match st.regs.lookup (llvmRegOf v) with
      | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
      | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
      | _ => none) = some (Val.u64 u')) : u' = u := by
  rw [hreg] at henv; cases henv; rfl

theorem llvmAlignedPtr_of_fact_sound (st : ExecState) (facts : FactEnv) (ptrVar : VarId)
    (ptr : BitVec 64) (ty : LLVMType) (fb : Nat)
    (hreg : st.regs.lookup (llvmRegOf ptrVar) = some (.ptr ptr))
    (hfb : isAligned ptr (effectiveAlign ty fb) = true)
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64,
          (match st.regs.lookup (llvmRegOf i) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 iv) ∧
          (match st.regs.lookup (llvmRegOf n) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd a b nsw nuw =>
        ∃ av bv : UInt64,
          (match st.regs.lookup (llvmRegOf a) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 av) ∧
          (match st.regs.lookup (llvmRegOf b) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 bv) ∧
          (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowSub a b nsw nuw =>
        ∃ av bv : UInt64,
          (match st.regs.lookup (llvmRegOf a) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 av) ∧
          (match st.regs.lookup (llvmRegOf b) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 bv) ∧
          (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .noOverflowMul a b nsw nuw =>
        ∃ av bv : UInt64,
          (match st.regs.lookup (llvmRegOf a) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 av) ∧
          (match st.regs.lookup (llvmRegOf b) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 bv) ∧
          (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
      | .alignedPtr p n =>
        0 < n ∧ ∃ pv : UInt64,
          (match st.regs.lookup (llvmRegOf p) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices a b la lb =>
        ∃ av bv lav lbv : UInt64,
          (match st.regs.lookup (llvmRegOf a) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 av) ∧
          (match st.regs.lookup (llvmRegOf b) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 bv) ∧
          (match st.regs.lookup (llvmRegOf la) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 lav) ∧
          (match st.regs.lookup (llvmRegOf lb) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 lbv) ∧
          rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj _ => True) :
    stepInstr {} 1 st (.load "dst" false ty (.reg (llvmRegOf ptrVar)) (alignOfFact facts ptrVar ty fb)) =
      stepInstr {} 1 st (.load "dst" false ty (.reg (llvmRegOf ptrVar)) fb) := by
  have hal : isAligned ptr (effectiveAlign ty (alignOfFact facts ptrVar ty fb)) = true := by
    induction facts with
    | nil => exact hfb
    | cons f rest ih =>
      have htail : ∀ g, factMember rest g = true →
          match g with
          | .idxLt i n =>
            ∃ iv nv : UInt64,
              (match st.regs.lookup (llvmRegOf i) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 iv) ∧
              (match st.regs.lookup (llvmRegOf n) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 nv) ∧ iv.toNat < nv.toNat
          | .noOverflowAdd a b nsw nuw =>
            ∃ av bv : UInt64,
              (match st.regs.lookup (llvmRegOf a) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 av) ∧
              (match st.regs.lookup (llvmRegOf b) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 bv) ∧
              (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
              (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
          | .noOverflowSub a b nsw nuw =>
            ∃ av bv : UInt64,
              (match st.regs.lookup (llvmRegOf a) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 av) ∧
              (match st.regs.lookup (llvmRegOf b) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 bv) ∧
              (nsw = true → subOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
              (nuw = true → subOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
          | .noOverflowMul a b nsw nuw =>
            ∃ av bv : UInt64,
              (match st.regs.lookup (llvmRegOf a) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 av) ∧
              (match st.regs.lookup (llvmRegOf b) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 bv) ∧
              (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
              (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
          | .alignedPtr p n =>
            0 < n ∧ ∃ pv : UInt64,
              (match st.regs.lookup (llvmRegOf p) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 pv) ∧ pv.toNat % n = 0
          | .disjointSlices a b la lb =>
            ∃ av bv lav lbv : UInt64,
              (match st.regs.lookup (llvmRegOf a) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 av) ∧
              (match st.regs.lookup (llvmRegOf b) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 bv) ∧
              (match st.regs.lookup (llvmRegOf la) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 lav) ∧
              (match st.regs.lookup (llvmRegOf lb) with
                | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
                | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
                | _ => none) = some (.u64 lbv) ∧
              rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true
          | .exclusiveObj _ => True :=
        fun g hg => hf g (by simp [factMember, List.contains_eq_mem] at hg ⊢; exact Or.inr hg)
      cases f with
      | alignedPtr p n =>
        simp only [alignOfFact]; split
        · next hp =>
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
          rcases hp with ⟨⟨⟨⟨rfl, hp2⟩, _⟩, _⟩, _⟩
          rcases hf (.alignedPtr p n) (by simp [factMember]) with ⟨hpos, pv, hpv, hmod⟩
          rw [hreg] at hpv; cases hpv
          have hnz : (n == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
          simpa [effectiveAlign, hnz, isAligned, hp2] using hmod
        · exact ih htail
      | _ => exact ih htail
  have h1 : isPow2 (effectiveAlign ty (alignOfFact facts ptrVar ty fb)) = true :=
    (Bool.and_eq_true_iff.mp hal).1
  have h2 : isPow2 (effectiveAlign ty fb) = true := (Bool.and_eq_true_iff.mp hfb).1
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, hreg,
    Option.getD_some, accessCheck, hal, hfb, h1, h2]

private theorem overflow_no (st : ExecState) (facts : FactEnv) (isMul : Bool) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup (llvmRegOf a) = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup (llvmRegOf b) = some (.bits .i64 bv.toBitVec))
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64,
          (match st.regs.lookup (llvmRegOf i) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 iv) ∧
          (match st.regs.lookup (llvmRegOf n) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → addOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowSub x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → subOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowMul x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → mulOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .alignedPtr p n =>
        0 < n ∧ ∃ pv : UInt64,
          (match st.regs.lookup (llvmRegOf p) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices x y la lb =>
        ∃ xv yv lav lbv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (match st.regs.lookup (llvmRegOf la) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lav) ∧
          (match st.regs.lookup (llvmRegOf lb) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lbv) ∧
          rangesDisjoint xv.toNat (lav.toNat * 8) yv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj _ => True) :
    flagsOverflow (overflowOf facts isMul a b)
      (if isMul then mulOverflowNSW .i64 av.toBitVec bv.toBitVec else addOverflowNSW .i64 av.toBitVec bv.toBitVec)
      (if isMul then mulOverflowNUW .i64 av.toBitVec bv.toBitVec else addOverflowNUW .i64 av.toBitVec bv.toBitVec) =
      false := by
  induction facts with
  | nil => rfl
  | cons f rest ih =>
    have hrest : flagsOverflow (overflowOf rest isMul a b)
        (if isMul then mulOverflowNSW .i64 av.toBitVec bv.toBitVec
         else addOverflowNSW .i64 av.toBitVec bv.toBitVec)
        (if isMul then mulOverflowNUW .i64 av.toBitVec bv.toBitVec
         else addOverflowNUW .i64 av.toBitVec bv.toBitVec) = false :=
      ih fun g hg => hf g (by
        simp only [factMember, List.contains_eq_mem, List.decide_mem_cons, Bool.or_eq_true] at hg ⊢
        exact Or.inr hg)
    cases f with
    | noOverflowAdd l r nsw nuw =>
      simp only [overflowOf]
      by_cases hhit : (!isMul && l == a && r == b) = true
      · simp only [hhit, ite_true]
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hhit
        rcases hhit with ⟨⟨rfl, hl⟩, hr⟩
        have hmem0 : factMember (.noOverflowAdd l r nsw nuw :: rest) (.noOverflowAdd l r nsw nuw) = true := by
          simp [factMember]
        have hfact := hf (.noOverflowAdd l r nsw nuw) hmem0
        simp only at hfact; rw [hl, hr] at hfact
        rcases hfact with ⟨av', bv', hav', hbv', h1, h2⟩
        cases llvm_lookup st a av av' ha hav'
        cases llvm_lookup st b bv bv' hb hbv'
        cases nsw <;> cases nuw
        all_goals
          simp [overflowFlagsOf, flagsOverflow] at h1 h2 ⊢
          try simp [h1, h2]
      · simp [Bool.eq_false_iff.mpr hhit, hrest]
    | noOverflowMul l r nsw nuw =>
      simp only [overflowOf]
      by_cases hhit : (isMul && l == a && r == b) = true
      · simp only [hhit, ite_true]
        simp only [Bool.and_eq_true, beq_iff_eq] at hhit
        rcases hhit with ⟨⟨rfl, hl⟩, hr⟩
        have hmem0 : factMember (.noOverflowMul l r nsw nuw :: rest) (.noOverflowMul l r nsw nuw) = true := by
          simp [factMember]
        have hfact := hf (.noOverflowMul l r nsw nuw) hmem0
        simp only at hfact; rw [hl, hr] at hfact
        rcases hfact with ⟨av', bv', hav', hbv', h1, h2⟩
        cases llvm_lookup st a av av' ha hav'
        cases llvm_lookup st b bv bv' hb hbv'
        cases nsw <;> cases nuw
        all_goals
          simp [overflowFlagsOf, flagsOverflow] at h1 h2 ⊢
          try simp [h1, h2]
      · simp [Bool.eq_false_iff.mpr hhit, hrest]
    | idxLt _ _ | noOverflowSub _ _ _ _ | alignedPtr _ _
    | disjointSlices _ _ _ _ | exclusiveObj _ => exact hrest

theorem llvmOverflowFlags_of_fact_sound (st : ExecState) (facts : FactEnv) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup (llvmRegOf a) = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup (llvmRegOf b) = some (.bits .i64 bv.toBitVec))
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64,
          (match st.regs.lookup (llvmRegOf i) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 iv) ∧
          (match st.regs.lookup (llvmRegOf n) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → addOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowSub x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → subOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowMul x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → mulOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .alignedPtr p n =>
        0 < n ∧ ∃ pv : UInt64,
          (match st.regs.lookup (llvmRegOf p) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices x y la lb =>
        ∃ xv yv lav lbv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (match st.regs.lookup (llvmRegOf la) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lav) ∧
          (match st.regs.lookup (llvmRegOf lb) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lbv) ∧
          rangesDisjoint xv.toNat (lav.toNat * 8) yv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj _ => True) :
    stepInstr {} 1 st (.add "dst" (overflowOf facts false a b) .i64
        (.reg (llvmRegOf a)) (.reg (llvmRegOf b))) =
      .inr (bindReg st "dst" (.bits .i64 (av.toBitVec + bv.toBitVec))) := by
  have hov := overflow_no st facts false a b av bv ha hb hf
  simp only [Bool.false_eq_true, ite_false] at hov
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, ha, hb, Option.getD_some]
  simp [binResult, hov]; rfl

theorem llvmMulOverflowFlags_of_fact_sound (st : ExecState) (facts : FactEnv) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup (llvmRegOf a) = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup (llvmRegOf b) = some (.bits .i64 bv.toBitVec))
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64,
          (match st.regs.lookup (llvmRegOf i) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 iv) ∧
          (match st.regs.lookup (llvmRegOf n) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → addOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowSub x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → subOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowMul x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → mulOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .alignedPtr p n =>
        0 < n ∧ ∃ pv : UInt64,
          (match st.regs.lookup (llvmRegOf p) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices x y la lb =>
        ∃ xv yv lav lbv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (match st.regs.lookup (llvmRegOf la) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lav) ∧
          (match st.regs.lookup (llvmRegOf lb) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lbv) ∧
          rangesDisjoint xv.toNat (lav.toNat * 8) yv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj _ => True) :
    stepInstr {} 1 st (.mul "dst" (overflowOf facts true a b) .i64
        (.reg (llvmRegOf a)) (.reg (llvmRegOf b))) =
      .inr (bindReg st "dst" (.bits .i64 (av.toBitVec * bv.toBitVec))) := by
  have hov := overflow_no st facts true a b av bv ha hb hf; simp only [ite_true] at hov
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, ha, hb, Option.getD_some]
  simp [binResult, hov]; rfl

theorem llvmSubOverflowFlags_of_fact_sound (st : ExecState) (facts : FactEnv) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup (llvmRegOf a) = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup (llvmRegOf b) = some (.bits .i64 bv.toBitVec))
    (hf : ∀ f, factMember facts f = true →
      match f with
      | .idxLt i n =>
        ∃ iv nv : UInt64,
          (match st.regs.lookup (llvmRegOf i) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 iv) ∧
          (match st.regs.lookup (llvmRegOf n) with
            | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x))
            | some (.ptr x) => some (Val.u64 (UInt64.ofBitVec x))
            | _ => none) = some (.u64 nv) ∧ iv.toNat < nv.toNat
      | .noOverflowAdd x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → addOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → addOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowSub x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → subOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → subOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .noOverflowMul x y nsw nuw =>
        ∃ xv yv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (nsw = true → mulOverflowNSW .i64 xv.toBitVec yv.toBitVec = false) ∧
          (nuw = true → mulOverflowNUW .i64 xv.toBitVec yv.toBitVec = false)
      | .alignedPtr p n =>
        0 < n ∧ ∃ pv : UInt64,
          (match st.regs.lookup (llvmRegOf p) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 pv) ∧ pv.toNat % n = 0
      | .disjointSlices x y la lb =>
        ∃ xv yv lav lbv : UInt64,
          (match st.regs.lookup (llvmRegOf x) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 xv) ∧
          (match st.regs.lookup (llvmRegOf y) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 yv) ∧
          (match st.regs.lookup (llvmRegOf la) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lav) ∧
          (match st.regs.lookup (llvmRegOf lb) with
            | some (.bits .i64 z) => some (Val.u64 (UInt64.ofBitVec z))
            | some (.ptr z) => some (Val.u64 (UInt64.ofBitVec z))
            | _ => none) = some (.u64 lbv) ∧
          rangesDisjoint xv.toNat (lav.toNat * 8) yv.toNat (lbv.toNat * 8) = true
      | .exclusiveObj _ => True) :
    stepInstr {} 1 st (.sub "dst" (subFlagsOf facts a b) .i64
        (.reg (llvmRegOf a)) (.reg (llvmRegOf b))) =
      .inr (bindReg st "dst" (.bits .i64 (av.toBitVec - bv.toBitVec))) := by
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, ha, hb, Option.getD_some]
  have hsub : flagsOverflow (subFlagsOf facts a b) (subOverflowNSW .i64 av.toBitVec bv.toBitVec)
      (subOverflowNUW .i64 av.toBitVec bv.toBitVec) = false := by
    induction facts with
    | nil => rfl
    | cons f rest ih =>
      cases f with
      | noOverflowSub l r nsw nuw =>
        simp only [subFlagsOf]
        by_cases hhit : (l == a && r == b) = true
        · simp only [hhit, ite_true]
          simp only [Bool.and_eq_true, beq_iff_eq] at hhit
          rcases hhit with ⟨hl, hr⟩; subst hl; subst hr
          have hmem0 : factMember (.noOverflowSub l r nsw nuw :: rest) (.noOverflowSub l r nsw nuw) = true := by
            simp [factMember]
          rcases hf (.noOverflowSub l r nsw nuw) hmem0 with ⟨av', bv', hav', hbv', h1, h2⟩
          cases llvm_lookup st l av av' ha hav'
          cases llvm_lookup st r bv bv' hb hbv'
          cases nsw <;> cases nuw
          all_goals
            simp [overflowFlagsOf, flagsOverflow] at h1 h2 ⊢
            try simp [h1, h2]
        · have hhit0 : (l == a && r == b) = false := Bool.eq_false_iff.mpr hhit
          simp only [hhit0, Bool.false_eq_true, ite_false]
          exact ih fun g hg => hf g (by
            simp only [factMember, List.contains_eq_mem, List.decide_mem_cons, Bool.or_eq_true] at hg ⊢
            exact Or.inr hg)
      | idxLt _ _ | noOverflowAdd _ _ _ _ | noOverflowMul _ _ _ _ | alignedPtr _ _
      | disjointSlices _ _ _ _ | exclusiveObj _ =>
        exact ih fun g hg => hf g (by
          simp only [factMember, List.contains_eq_mem, List.decide_mem_cons,
            Bool.or_eq_true] at hg ⊢
          exact Or.inr hg)
  simp only [binResult, hsub, Bool.false_eq_true, ite_false]; rfl

theorem add_nsw_poison_witness :
    stepInstr {} 1 {} (.add "r" .nsw .i64
        (.constInt .i64 0x7FFF_FFFF_FFFF_FFFF#64) (.constInt .i64 1#64)) =
      .inr (bindReg {} "r" .poison) :=
  add_nsw_overflow_poison .i64 _ _ (by decide)

private theorem bind_noalias (st : ExecState) (facts : FactEnv) (ptrA ptrB : VarId)
    (lenA lenB : Nat) (ps : List LLVMParam) (blocks : List LLVMBlock) (args : List LLVMVal) :
    bindArgs st (noaliasParams facts ptrA ptrB lenA lenB ps blocks) args = bindArgs st ps args := by
  let f : LLVMParam → LLVMParam := fun p => match p.ty with
    | .ptr _ => if p.name == llvmRegOf ptrA || p.name == llvmRegOf ptrB then
        withNoAlias true p else p
    | _ => p
  have hmap : ∀ (st0 : ExecState) (qs : List LLVMParam) (vs : List LLVMVal),
      bindArgs st0 (qs.map f) vs = bindArgs st0 qs vs := by
    intro st0 qs
    induction qs generalizing st0 with
    | nil =>
      intro vs
      cases vs <;> rfl
    | cons p qs ih =>
      intro vs
      cases vs with
      | nil => rfl
      | cons v vs =>
        have hname : (f p).name = p.name := by
          dsimp only [f]
          cases p.ty with
          | ptr _ =>
            by_cases hc : (p.name == llvmRegOf ptrA || p.name == llvmRegOf ptrB) = true
            · simp only [hc, ite_true, withNoAlias, Bool.not_true, Bool.false_eq_true, ite_false]
              split <;> rfl
            · simp [Bool.eq_false_iff.mpr hc]
          | _ => rfl
        simp only [List.map_cons, bindArgs, hname]
        exact ih (bindReg st0 p.name v) vs
  unfold noaliasParams
  dsimp only
  split
  · rfl
  · exact hmap st ps args

private theorem scalar_noalias_serialize_len (ty : LLVMType) (v : LLVMVal)
    (hs : isScalarNoAliasTy ty = true) :
    (serializeTypedVal ty v).length = ty.byteSize := by
  cases ty with
  | void => rfl
  | int w =>
    cases v with
    | bits w' bv =>
      by_cases hw : w' = w
      · subst hw
        simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
          ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      · simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
          hw, ByteMem.poisonBytes_length]
    | ptr _ | floatBits _ _ | aggNil | aggCons _ _ | poison =>
      simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
        ByteMem.poisonBytes_length]
  | float fw =>
    cases v with
    | floatBits fw' fb =>
      by_cases hfw : fw' = fw
      · subst hfw
        simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
          ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
      · simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
          hfw, ByteMem.poisonBytes_length]
    | bits _ _ | ptr _ | aggNil | aggCons _ _ | poison =>
      simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
        ByteMem.poisonBytes_length]
  | ptr _ =>
    cases v with
    | ptr p =>
      simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
        ByteMem.initBytes_length, ByteMem.bvToLEBytes, ByteMem.natToLEBytes_length]
    | bits _ _ | floatBits _ _ | aggNil | aggCons _ _ | poison =>
      simp [serializeTypedVal, serializeTypedValAux, LLVMType.byteSize,
        ByteMem.poisonBytes_length]
  | structFields _ _ | array _ _ | vec _ _ =>
    simp [isScalarNoAliasTy] at hs

theorem llvmNoAliasParam_of_disjoint_sound (st : ExecState) (facts : FactEnv)
    (ptrA ptrB lenA lenB : VarId) (as0 : Nat) (attrs0 : List ParamAttr)
    (ps : List LLVMParam) (blocks : List LLVMBlock) (args : List LLVMVal)
    (pa pb : BitVec 64) (la lb : UInt64)
    (hne : ptrA ≠ ptrB)
    (hall : ps.all (isCertifiedPtrParam ptrA ptrB) = true)
    (hsafe : blocksNoAliasSafe facts ptrA ptrB lenA lenB blocks = true)
    (hpa : st.regs.lookup (llvmRegOf ptrA) = some (.ptr pa))
    (hpb : st.regs.lookup (llvmRegOf ptrB) = some (.ptr pb))
    (hla : st.regs.lookup (llvmRegOf lenA) = some (.bits .i64 la.toBitVec))
    (hlb : st.regs.lookup (llvmRegOf lenB) = some (.bits .i64 lb.toBitVec))
    (hfIdx : ∀ i n, factMember facts (.idxLt i n) = true →
      (n = lenA → ∃ iv : UInt64, iv.toNat < la.toNat) ∧
      (n = lenB → ∃ iv : UInt64, iv.toNat < lb.toNat))
    (hmem : factMember facts (.disjointSlices ptrA ptrB lenA lenB) = true)
    (hdisj : rangesDisjoint pa.toNat (la.toNat * 8) pb.toNat (lb.toNat * 8) = true) :
    let p0 : LLVMParam := { name := llvmRegOf ptrA, ty := .ptr as0, attrs := attrs0 }
    (noaliasParams facts ptrA ptrB lenA lenB (p0 :: ps) blocks).any
        (fun p => p.attrs.contains .noalias) = true ∧
      bindArgs st (noaliasParams facts ptrA ptrB lenA lenB (p0 :: ps) blocks) args =
        bindArgs st (p0 :: ps) args ∧
      ∃ av bv : BitVec 64, ∃ lav lbv : UInt64,
        st.regs.lookup (llvmRegOf ptrA) = some (.ptr av) ∧
        st.regs.lookup (llvmRegOf ptrB) = some (.ptr bv) ∧
        st.regs.lookup (llvmRegOf lenA) = some (.bits .i64 lav.toBitVec) ∧
        st.regs.lookup (llvmRegOf lenB) = some (.bits .i64 lbv.toBitVec) ∧
        rangesDisjoint av.toNat (lav.toNat * 8) bv.toNat (lbv.toNat * 8) = true ∧
        (∀ blk ∈ blocks, ∀ ins ∈ blk.body,
          instrSafeForNoAlias (llvmRegOf ptrA) (llvmRegOf ptrB) ins = true) ∧
        (∀ (m : ByteMem) (blkW blkR : LLVMBlock) (volW volR : Bool) (tyW tyR : LLVMType)
            (valOp : Operand) (alW alR asW asR : Nat) (dstR : RegName) (v : LLVMVal),
          blkW ∈ blocks → blkR ∈ blocks →
          LLVMInstr.store volW tyW valOp (.reg (llvmRegOf ptrA)) alW asW ∈ blkW.body →
          LLVMInstr.load dstR volR tyR (.reg (llvmRegOf ptrB)) alR asR ∈ blkR.body →
          loadVal (storeTypedVal m av tyW v) bv tyR = loadVal m bv tyR) ∧
        ∀ (m : ByteMem) (bs : List MemByte) (offA offB width : Nat),
          offA + bs.length ≤ lav.toNat * 8 →
          offB + width ≤ lbv.toNat * 8 →
          (m.writeBytesAt (av.toNat + offA) bs).readBytesAt (bv.toNat + offB) width =
            m.readBytesAt (bv.toNat + offB) width := by
  intro p0
  have hneb : (ptrA != ptrB) = true := bne_iff_ne.mpr hne
  have hna : (withNoAlias true p0).attrs.contains .noalias = true := by
    simp only [withNoAlias, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hc : .noalias ∈ p0.attrs <;> simp [hc]
  have hsafeSplit : blocks.all (blockSafeForNoAlias (llvmRegOf ptrA) (llvmRegOf ptrB)) = true ∧
      ((!blocksDerefReg (llvmRegOf ptrA) blocks || hasPositiveSliceBound facts lenA) = true) ∧
      ((!blocksDerefReg (llvmRegOf ptrB) blocks || hasPositiveSliceBound facts lenB) = true) := by
    unfold blocksNoAliasSafe at hsafe
    simp only [Bool.and_eq_true] at hsafe
    exact ⟨hsafe.1.1, hsafe.1.2, hsafe.2⟩
  have hinsSafe : ∀ blk ∈ blocks, ∀ ins ∈ blk.body,
      instrSafeForNoAlias (llvmRegOf ptrA) (llvmRegOf ptrB) ins = true := by
    intro blk hblk ins hins
    have hb := List.all_eq_true.mp hsafeSplit.1 blk hblk
    unfold blockSafeForNoAlias at hb
    simp only [Bool.and_eq_true] at hb
    exact List.all_eq_true.mp hb.1.2 ins hins
  have hposFromBoundA : hasPositiveSliceBound facts lenA = true → 1 ≤ la.toNat := by
    intro hpos
    unfold hasPositiveSliceBound at hpos
    rcases List.any_eq_true.mp hpos with ⟨f, hfmem, hpred⟩
    cases f with
    | idxLt i n =>
      have hn : n = lenA := beq_iff_eq.mp hpred
      have hfm : factMember facts (.idxLt i n) = true := by
        simpa [factMember, List.contains_iff_mem] using hfmem
      rcases (hfIdx i n hfm).1 hn with ⟨iv, hlt⟩
      omega
    | noOverflowAdd _ _ _ _ | noOverflowSub _ _ _ _ | noOverflowMul _ _ _ _
    | alignedPtr _ _ | disjointSlices _ _ _ _ | exclusiveObj _ =>
      simp at hpred
  have hposFromBoundB : hasPositiveSliceBound facts lenB = true → 1 ≤ lb.toNat := by
    intro hpos
    unfold hasPositiveSliceBound at hpos
    rcases List.any_eq_true.mp hpos with ⟨f, hfmem, hpred⟩
    cases f with
    | idxLt i n =>
      have hn : n = lenB := beq_iff_eq.mp hpred
      have hfm : factMember facts (.idxLt i n) = true := by
        simpa [factMember, List.contains_iff_mem] using hfmem
      rcases (hfIdx i n hfm).2 hn with ⟨iv, hlt⟩
      omega
    | noOverflowAdd _ _ _ _ | noOverflowSub _ _ _ _ | noOverflowMul _ _ _ _
    | alignedPtr _ _ | disjointSlices _ _ _ _ | exclusiveObj _ =>
      simp at hpred
  have hsub : ∀ (m : ByteMem) (bs : List MemByte) (offA offB width : Nat),
      offA + bs.length ≤ la.toNat * 8 →
      offB + width ≤ lb.toNat * 8 →
      (m.writeBytesAt (pa.toNat + offA) bs).readBytesAt (pb.toNat + offB) width =
        m.readBytesAt (pb.toNat + offB) width := by
    intro m bs offA offB width ha hb
    have hor : pa.toNat + la.toNat * 8 ≤ pb.toNat ∨ pb.toNat + lb.toNat * 8 ≤ pa.toNat :=
      of_decide_eq_true hdisj
    have hsubDisj : rangesDisjoint (pa.toNat + offA) bs.length (pb.toNat + offB) width = true := by
      unfold rangesDisjoint
      exact decide_eq_true (by omega)
    exact ByteMem.readBytesAt_writeBytesAt_disjoint m (pa.toNat + offA) bs (pb.toNat + offB) width hsubDisj
  have hnoninterf : ∀ (m : ByteMem) (blkW blkR : LLVMBlock) (volW volR : Bool) (tyW tyR : LLVMType)
      (valOp : Operand) (alW alR asW asR : Nat) (dstR : RegName) (v : LLVMVal),
      blkW ∈ blocks → blkR ∈ blocks →
      LLVMInstr.store volW tyW valOp (.reg (llvmRegOf ptrA)) alW asW ∈ blkW.body →
      LLVMInstr.load dstR volR tyR (.reg (llvmRegOf ptrB)) alR asR ∈ blkR.body →
      loadVal (storeTypedVal m pa tyW v) pb tyR = loadVal m pb tyR := by
    intro m blkW blkR volW volR tyW tyR valOp alW alR asW asR dstR v hblkW hblkR hst hld
    have hderefA : blocksDerefReg (llvmRegOf ptrA) blocks = true :=
      List.any_eq_true.mpr ⟨blkW, hblkW, List.any_eq_true.mpr
        ⟨_, hst, by simp [instrDerefsReg]⟩⟩
    have hderefB : blocksDerefReg (llvmRegOf ptrB) blocks = true :=
      List.any_eq_true.mpr ⟨blkR, hblkR, List.any_eq_true.mpr
        ⟨_, hld, by simp [instrDerefsReg]⟩⟩
    have hboundA : hasPositiveSliceBound facts lenA = true := by
      have h := hsafeSplit.2.1
      rw [hderefA] at h
      simpa using h
    have hboundB : hasPositiveSliceBound facts lenB = true := by
      have h := hsafeSplit.2.2
      rw [hderefB] at h
      simpa using h
    have hla1 : 1 ≤ la.toNat := hposFromBoundA hboundA
    have hlb1 : 1 ≤ lb.toNat := hposFromBoundB hboundB
    have hsafeW := hinsSafe blkW hblkW _ hst
    have hsafeR := hinsSafe blkR hblkR _ hld
    simp only [instrSafeForNoAlias, beq_self_eq_true, Bool.true_or, Bool.or_true, ite_true,
      Bool.and_eq_true, decide_eq_true_eq] at hsafeW hsafeR
    have hlenW : (serializeTypedVal tyW v).length = tyW.byteSize :=
      scalar_noalias_serialize_len tyW v hsafeW.2.1
    have hszW : tyW.byteSize ≤ 8 := hsafeW.2.2
    have hszR : tyR.byteSize ≤ 8 := hsafeR.2.2
    unfold loadVal storeTypedVal
    have hrw := hsub m (serializeTypedVal tyW v) 0 0 tyR.byteSize
      (by omega) (by omega)
    simp only [Nat.add_zero] at hrw
    rw [hrw]
  refine ⟨?_, bind_noalias st facts ptrA ptrB lenA lenB (p0 :: ps) blocks args,
    pa, pb, la, lb, hpa, hpb, hla, hlb, hdisj, hinsSafe, hnoninterf, hsub⟩
  dsimp only [p0] at hna ⊢
  unfold noaliasParams
  rw [List.all_cons]
  have hp0 : isCertifiedPtrParam ptrA ptrB { name := llvmRegOf ptrA, ty := .ptr as0, attrs := attrs0 } = true := by
    simp [isCertifiedPtrParam]
  rw [hp0, Bool.true_and, hall, hneb, hmem, hsafe]
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false,
    List.map_cons, beq_self_eq_true, Bool.true_or, ite_true, List.any_cons, hna]

theorem readBytesAt_disjoint_of_fact (m : ByteMem) (base addr width : Nat) (bs : List MemByte)
    (hb : base + bs.length ≤ addr) :
    (m.writeBytesAt base bs).readBytesAt addr width = m.readBytesAt addr width :=
  ByteMem.readBytesAt_writeBytesAt_disjoint m base bs addr width
    (by unfold rangesDisjoint; exact decide_eq_true (Or.inl hb))

theorem launchBoundsCert_gid_lt_len (cert : LaunchBoundsCert) (gidVar lenVar : VarId)
    (gridDimX blockDimX runtimeLen ctaIdX tx : Nat)
    (hcert : launchCertCovers (some cert) gidVar lenVar = true)
    (hlaunch : launchCertMatchesLaunch cert gridDimX blockDimX runtimeLen = true)
    (hcta : ctaIdX < gridDimX) (htx : tx < blockDimX) :
    ctaIdX * blockDimX + tx < runtimeLen := by
  unfold launchCertCovers at hcert
  unfold launchCertMatchesLaunch at hlaunch
  simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hcert hlaunch
  rcases hcert with ⟨⟨⟨⟨_, _⟩, _⟩, hposC⟩, hminC⟩
  rcases hlaunch with ⟨⟨hg, hb⟩, hlen⟩
  have hposB : 0 < blockDimX := by rw [hb]; exact hposC
  have hstep : ctaIdX * blockDimX + tx < (ctaIdX + 1) * blockDimX := by
    rw [Nat.succ_mul]; omega
  have hctaGrid : (ctaIdX + 1) * blockDimX ≤ gridDimX * blockDimX :=
    Nat.mul_le_mul_right blockDimX (by omega)
  have hgridMin : gridDimX * blockDimX ≤ cert.minLen := by
    rw [hg, hb]; exact hminC
  omega

-- PTX: with an explicit `LaunchBoundsCert` and retained `idxLt`, the guarded gid prefix becomes
-- the unguarded 11-instruction preamble. Coverage (`(ctaId.x + 1) * blockSize ≤ len`) keeps
-- `gid * 8` and `nIn * len * 8 + gid * 8` non-wrapping in 64 bits across `shl.b64` and `add.u64`.

theorem ptxBoundsFreeLoad_sound (f : Nat) (doneLbl : String) (facts : FactEnv)
    (gidVar lenVar : VarId) (cert : LaunchBoundsCert) (suf : List PTXStmt) (cta : PTXCTAState)
    (done todo : List PTXThreadState) (blockSize gridDimX : Nat) (ctaId : PTXAst.Dim3)
    {rf : PTXRegFile} {nP nR nRd : Nat} (hrt : RegTyped rf nP nR nRd)
    (localBytes tx len nIn : Nat) (hr : 2 < nR) (hrd : 6 < nRd)
    (hcta : cta.ctaId = ctaId) (hblk : cta.blockDim = { x := blockSize, y := 1, z := 1 })
    (htx : tx < blockSize) (hctaX : ctaId.x < 2 ^ 32) (hblkX : blockSize < 2 ^ 32)
    (hgrid : ctaId.x < gridDimX)
    (hlaunch : launchCertMatchesLaunch cert gridDimX blockSize len = true)
    (houn : (nIn + 1) * len * 8 ≤ 2 ^ 64)
    (hdone : ∀ t ∈ done, t.halted = true) (saved : List MemAccessLog)
    (hn : cta.paramMem.lookupParam? "param_n" = some (BitVec.ofNat 64 len))
    (hout : cta.paramMem.lookupParam? "param_out" = some (BitVec.ofNat 64 (nIn * len * 8)))
    (hcert : launchCertCovers (some cert) gidVar lenVar = true)
    (hmem : factMember facts (.idxLt gidVar lenVar) = true) :
    runCTAWithGlobalLog (f + 11) (gidSetupWithFacts doneLbl facts gidVar lenVar (some cert) ++ suf)
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) } saved =
    runCTAWithGlobalLog f (gidSetupWithFacts doneLbl facts gidVar lenVar (some cert) ++ suf)
      { cta with threads := done ++
        (laneAt localBytes tx 11
          (rfSet (rfSet (rfSet (rf7 blockSize ctaId rf tx len)
            "%rd4" (BitVec.ofNat 64 (nIn * len * 8)))
            "%rd5" (BitVec.ofNat 64 ((ctaId.x * blockSize + tx) * 8)))
            "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + (ctaId.x * blockSize + tx) * 8)))
          false :: todo) } saved := by
  let stmts := gidSetupWithFacts doneLbl facts gidVar lenVar (some cert) ++ suf
  let gid := ctaId.x * blockSize + tx
  have htx32 : tx < 2 ^ 32 := Nat.lt_trans htx hblkX
  have hgid64 := laneOf1D_lt ctaId.x blockSize tx hctaX hblkX htx32
  have hcta64 : ctaId.x < 2 ^ 64 := by omega
  have hblk64 : blockSize < 2 ^ 64 := by omega
  have hprod : ctaId.x * blockSize < 2 ^ 64 := by omega
  have hgidLt : gid < len :=
    launchBoundsCert_gid_lt_len cert gidVar lenVar gridDimX blockSize len ctaId.x tx
      hcert hlaunch hgrid htx
  have hlen8 : nIn * len * 8 + len * 8 ≤ 2 ^ 64 := by
    have : (nIn + 1) * len * 8 = nIn * len * 8 + len * 8 := by simp [Nat.add_mul, Nat.one_mul]
    omega
  have hgid8 : gid * 8 < len * 8 := Nat.mul_lt_mul_of_pos_right hgidLt (by omega)
  have hgid61 : gid < 2 ^ 61 := by omega
  let r1 := rfSet rf "%r0" (BitVec.ofNat 64 ctaId.x)
  let r2 := rfSet r1 "%r1" (BitVec.ofNat 64 blockSize)
  let r3 := rfSet r2 "%r2" (BitVec.ofNat 64 tx)
  let r4 := rfSet r3 "%rd0" (BitVec.ofNat 64 (ctaId.x * blockSize))
  let r5 := rfSet r4 "%rd1" (BitVec.ofNat 64 tx)
  let r6 := rfSet r5 "%rd2" (BitVec.ofNat 64 gid)
  let r7 := rf7 blockSize ctaId rf tx len
  let r8 := rfSet r7 "%rd4" (BitVec.ofNat 64 (nIn * len * 8))
  let r9 := rfSet r8 "%rd4" (BitVec.ofNat 64 (nIn * len * 8))
  let r10 := rfSet r9 "%rd5" (BitVec.ofNat 64 (gid * 8))
  have hr8eq : r9 = r8 := rfSet_overwrite r7 "%rd4" _ _
  have hs0 : runCTAWithGlobalLog ((f + 10) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) } saved =
    runCTAWithGlobalLog (f + 10) stmts
      { cta with threads := done ++ (laneAt localBytes tx 1 r1 false :: todo) } saved := by
    apply pure_lane_step (f + 10) stmts cta done todo localBytes tx 0 rf r1
      (.mov .u32 "%r0" (.sreg .ctaidX)) saved hdone (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hex := exec_mov_sreg_r stmts
      { cta with threads := done ++ (laneAt localBytes tx 0 rf false :: todo) }
      (laneAt localBytes tx 0 rf false) hrt 0 (by omega) .ctaidX
      (BitVec.ofNat 64 ctaId.x) (by simp [evalSpecialReg, hcta]) (fit32_ofNat ctaId.x hctaX)
    rw [mask32_ofNat ctaId.x hctaX] at hex; exact hex
  have hs1 : runCTAWithGlobalLog ((f + 9) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 1 r1 false :: todo) } saved =
    runCTAWithGlobalLog (f + 9) stmts
      { cta with threads := done ++ (laneAt localBytes tx 2 r2 false :: todo) } saved := by
    apply pure_lane_step (f + 9) stmts cta done todo localBytes tx 1 r1 r2
      (.mov .u32 "%r1" (.sreg .ntidX)) saved hdone (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hex := exec_mov_sreg_r stmts
      { cta with threads := done ++ (laneAt localBytes tx 1 r1 false :: todo) }
      (laneAt localBytes tx 1 r1 false) hrt 1 (by omega) .ntidX
      (BitVec.ofNat 64 blockSize) (by simp [evalSpecialReg, hblk]) (fit32_ofNat blockSize hblkX)
    rw [mask32_ofNat blockSize hblkX] at hex; exact hex
  have hs2 : runCTAWithGlobalLog ((f + 8) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 2 r2 false :: todo) } saved =
    runCTAWithGlobalLog (f + 8) stmts
      { cta with threads := done ++ (laneAt localBytes tx 3 r3 false :: todo) } saved := by
    apply pure_lane_step (f + 8) stmts cta done todo localBytes tx 2 r2 r3
      (.mov .u32 "%r2" (.sreg .tidX)) saved hdone (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hex := exec_mov_sreg_r stmts
      { cta with threads := done ++ (laneAt localBytes tx 2 r2 false :: todo) }
      (laneAt localBytes tx 2 r2 false) hrt 2 (by omega) .tidX
      (BitVec.ofNat 64 tx) (by simp [evalSpecialReg, laneAt]) (fit32_ofNat tx htx32)
    rw [mask32_ofNat tx htx32] at hex; exact hex
  have hs3 : runCTAWithGlobalLog ((f + 7) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 3 r3 false :: todo) } saved =
    runCTAWithGlobalLog (f + 7) stmts
      { cta with threads := done ++ (laneAt localBytes tx 4 r4 false :: todo) } saved := by
    apply pure_lane_step (f + 7) stmts cta done todo localBytes tx 3 r3 r4
      (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1")) saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk0 : r3.regs.lookup "%r0" = some (.scalar (BitVec.ofNat 64 ctaId.x)) := by
      dsimp only [r3, r2, r1]
      rw [lookup_rfSet_ne _ "%r2" "%r0" _ (by decide),
          lookup_rfSet_ne _ "%r1" "%r0" _ (by decide), lookup_rfSet_self]
    have hlk1 : r3.regs.lookup "%r1" = some (.scalar (BitVec.ofNat 64 blockSize)) := by
      dsimp only [r3, r2]; rw [lookup_rfSet_ne _ "%r2" "%r1" _ (by decide), lookup_rfSet_self]
    have hex := exec_mul_wide_u32 stmts
      { cta with threads := done ++ (laneAt localBytes tx 3 r3 false :: todo) }
      (laneAt localBytes tx 3 r3 false) hrt 0 0 1 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 ctaId.x) (BitVec.ofNat 64 blockSize)
      (fit32_ofNat ctaId.x hctaX) (fit32_ofNat blockSize hblkX) hlk0 hlk1
    have hmul : BitVec.ofNat 64 ctaId.x * BitVec.ofNat 64 blockSize =
        BitVec.ofNat 64 (ctaId.x * blockSize) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hcta64, Nat.mod_eq_of_lt hblk64, Nat.mod_eq_of_lt hprod]
    rw [hmul] at hex; exact hex
  have hs4 : runCTAWithGlobalLog ((f + 6) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 4 r4 false :: todo) } saved =
    runCTAWithGlobalLog (f + 6) stmts
      { cta with threads := done ++ (laneAt localBytes tx 5 r5 false :: todo) } saved := by
    apply pure_lane_step (f + 6) stmts cta done todo localBytes tx 4 r4 r5
      (.cvt .none .u64 .u32 "%rd1" (.reg "%r2")) saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk2 : r4.regs.lookup "%r2" = some (.scalar (BitVec.ofNat 64 tx)) := by
      dsimp only [r4, r3]; rw [lookup_rfSet_ne _ "%rd0" "%r2" _ (by decide), lookup_rfSet_self]
    exact exec_cvt_u64_u32 stmts
      { cta with threads := done ++ (laneAt localBytes tx 4 r4 false :: todo) }
      (laneAt localBytes tx 4 r4 false) hrt 1 2 (by omega) (by omega)
      (BitVec.ofNat 64 tx) (fit32_ofNat tx htx32) hlk2
  have hs5 : runCTAWithGlobalLog ((f + 5) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 5 r5 false :: todo) } saved =
    runCTAWithGlobalLog (f + 5) stmts
      { cta with threads := done ++ (laneAt localBytes tx 6 r6 false :: todo) } saved := by
    apply pure_lane_step (f + 5) stmts cta done todo localBytes tx 5 r5 r6
      (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1")) saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk0 : r5.regs.lookup "%rd0" = some (.scalar (BitVec.ofNat 64 (ctaId.x * blockSize))) := by
      dsimp only [r5, r4]; rw [lookup_rfSet_ne _ "%rd1" "%rd0" _ (by decide), lookup_rfSet_self]
    have hlk1 : r5.regs.lookup "%rd1" = some (.scalar (BitVec.ofNat 64 tx)) :=
      lookup_rfSet_self r4 "%rd1" _
    have hex := exec_add_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 5 r5 false :: todo) }
      (laneAt localBytes tx 5 r5 false) hrt 2 0 1 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 (ctaId.x * blockSize)) (BitVec.ofNat 64 tx) hlk0 hlk1
    rw [add_ofNat64 (ctaId.x * blockSize) tx hgid64] at hex; exact hex
  have hs6 : runCTAWithGlobalLog ((f + 4) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 6 r6 false :: todo) } saved =
    runCTAWithGlobalLog (f + 4) stmts
      { cta with threads := done ++ (laneAt localBytes tx 7 r7 false :: todo) } saved := by
    apply pure_lane_step (f + 4) stmts cta done todo localBytes tx 6 r6 r7
      (.ldParam .u64 "%rd3" "param_n") saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_ldParam_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 6 r6 false :: todo) }
      (laneAt localBytes tx 6 r6 false) hrt 3 (by omega) "param_n" (BitVec.ofNat 64 len) hn
  have hs7 : runCTAWithGlobalLog ((f + 3) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 7 r7 false :: todo) } saved =
    runCTAWithGlobalLog (f + 3) stmts
      { cta with threads := done ++ (laneAt localBytes tx 8 r8 false :: todo) } saved := by
    apply pure_lane_step (f + 3) stmts cta done todo localBytes tx 7 r7 r8
      (.ldParam .u64 "%rd4" "param_out") saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_ldParam_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 7 r7 false :: todo) }
      (laneAt localBytes tx 7 r7 false) hrt 4 (by omega) "param_out"
      (BitVec.ofNat 64 (nIn * len * 8)) hout
  have hs8 : runCTAWithGlobalLog ((f + 2) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 8 r8 false :: todo) } saved =
    runCTAWithGlobalLog (f + 2) stmts
      { cta with threads := done ++ (laneAt localBytes tx 9 r9 false :: todo) } saved := by
    apply pure_lane_step (f + 2) stmts cta done todo localBytes tx 8 r8 r9
      (.cvtaToGlobal .u64 "%rd4" (.reg "%rd4")) saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    exact exec_cvta_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 8 r8 false :: todo) }
      (laneAt localBytes tx 8 r8 false) hrt 4 4 (by omega) (by omega)
      (BitVec.ofNat 64 (nIn * len * 8)) (lookup_rfSet_self r7 "%rd4" _)
  have hs9 : runCTAWithGlobalLog ((f + 1) + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 9 r9 false :: todo) } saved =
    runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 10 r10 false :: todo) } saved := by
    apply pure_lane_step (f + 1) stmts cta done todo localBytes tx 9 r9 r10
      (.shl .b64 "%rd5" (.reg "%rd2") (i64 3)) saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk2 : r9.regs.lookup "%rd2" = some (.scalar (BitVec.ofNat 64 gid)) := by
      dsimp only [r9, r8, r7, rf7]
      rw [lookup_rfSet_ne _ "%rd4" "%rd2" _ (by decide),
          lookup_rfSet_ne _ "%rd4" "%rd2" _ (by decide),
          lookup_rfSet_ne _ "%rd3" "%rd2" _ (by decide), lookup_rfSet_self]
    have hex := exec_shl_imm stmts
      { cta with threads := done ++ (laneAt localBytes tx 9 r9 false :: todo) }
      (laneAt localBytes tx 9 r9 false) hrt 5 2 3 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 gid) hlk2
    have hshl : BitVec.ofNat 64 gid <<< 3 = BitVec.ofNat 64 (gid * 8) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : gid < 2 ^ 64)]
      have h8 : gid * 8 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt h8]
      change gid <<< 3 % 2 ^ 64 = gid * 8
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
      have h8' : 2 ^ 3 * gid < 2 ^ 64 := by rw [Nat.mul_comm]; exact h8
      exact Nat.mod_eq_of_lt h8'
    rw [hshl] at hex; exact hex
  have hs10 : runCTAWithGlobalLog (f + 1) stmts
      { cta with threads := done ++ (laneAt localBytes tx 10 r10 false :: todo) } saved =
    runCTAWithGlobalLog f stmts
      { cta with threads := done ++
        (laneAt localBytes tx 11
          (rfSet (rfSet (rfSet r7 "%rd4" (BitVec.ofNat 64 (nIn * len * 8)))
            "%rd5" (BitVec.ofNat 64 (gid * 8)))
            "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8)))
          false :: todo) } saved := by
    have hr10eq : rfSet r10 "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8)) =
        rfSet (rfSet (rfSet r7 "%rd4" (BitVec.ofNat 64 (nIn * len * 8)))
          "%rd5" (BitVec.ofNat 64 (gid * 8)))
          "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8)) := by
      dsimp only [r10]; rw [hr8eq]
    rw [← hr10eq]
    apply pure_lane_step f stmts cta done todo localBytes tx 10 r10
      (rfSet r10 "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8)))
      (.add .none .u64 "%rd6" (.reg "%rd4") (.reg "%rd5")) saved hdone
      (by simp [stmts, gidSetupWithFacts, hcert, hmem, ins])
      (fun _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
    have hlk4 : r10.regs.lookup "%rd4" = some (.scalar (BitVec.ofNat 64 (nIn * len * 8))) := by
      dsimp only [r10, r9]; rw [lookup_rfSet_ne _ "%rd5" "%rd4" _ (by decide), lookup_rfSet_self]
    have hlk5 : r10.regs.lookup "%rd5" = some (.scalar (BitVec.ofNat 64 (gid * 8))) :=
      lookup_rfSet_self r9 "%rd5" _
    have hex := exec_add_rd stmts
      { cta with threads := done ++ (laneAt localBytes tx 10 r10 false :: todo) }
      (laneAt localBytes tx 10 r10 false) hrt 6 4 5 (by omega) (by omega) (by omega)
      (BitVec.ofNat 64 (nIn * len * 8)) (BitVec.ofNat 64 (gid * 8)) hlk4 hlk5
    rw [add_ofNat64 (nIn * len * 8) (gid * 8) (by omega)] at hex; exact hex
  have hf11 : f + 11 = (f + 10) + 1 := by omega
  have hf10 : f + 10 = (f + 9) + 1 := by omega
  have hf9 : f + 9 = (f + 8) + 1 := by omega
  have hf8 : f + 8 = (f + 7) + 1 := by omega
  have hf7 : f + 7 = (f + 6) + 1 := by omega
  have hf6 : f + 6 = (f + 5) + 1 := by omega
  have hf5 : f + 5 = (f + 4) + 1 := by omega
  have hf4 : f + 4 = (f + 3) + 1 := by omega
  have hf3 : f + 3 = (f + 2) + 1 := by omega
  have hf2 : f + 2 = (f + 1) + 1 := by omega
  rw [hf11, hs0, hf10, hs1, hf9, hs2, hf8, hs3, hf7, hs4, hf6, hs5, hf5, hs6,
      hf4, hs7, hf3, hs8, hf2, hs9, hs10]

-- Metal: an explicit `LaunchBoundsCert` plus retained `idxLt` emits the inner body with no guard.

private theorem metal_body (facts : FactEnv) (idxVar lenVar : VarId) (cert : LaunchBoundsCert)
    (inner : List MSLStmt)
    (hcert : launchCertCovers (some cert) idxVar lenVar = true)
    (h : factMember facts (.idxLt idxVar lenVar) = true) :
    guardedWithFacts inner facts idxVar lenVar (some cert) = inner ++ [.returnStmt] := by
  simp [guardedWithFacts, hcert, h]

theorem metalBoundsFreeLoad_sound (nIn len groupSize gridDimX gx stepsInner : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt) (facts : FactEnv) (idxVar lenVar : VarId) (cert : LaunchBoundsCert)
    (hInner : LaneInnerSpec nIn len stepsInner inWords specWord inner)
    (hlen64 : len * 8 ≤ 2 ^ 64)
    (hcert : launchCertCovers (some cert) idxVar lenVar = true)
    (hmem : factMember facts (.idxLt idxVar lenVar) = true)
    (hgx : gx < gridDimX)
    (hlaunch : launchCertMatchesLaunch cert gridDimX groupSize len = true) :
    let body := guardedWithFacts inner facts idxVar lenVar (some cert)
    let mkLane := fun tx => ({
      tid := { x := tx, y := 0, z := 0 }
      locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx, 0, 0)
      stmts := body
      halted := false } : MSLThreadState)
    ∀ (rem tx0 f : Nat) (g : MSLGroupState) (done : List MSLThreadState)
      (outMem0 outMem : MetalAst.ByteMemory),
      tx0 + rem = groupSize →
      (gx + 1) * groupSize < 2 ^ 32 →
      rem * (stepsInner + 1) ≤ f →
      g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
      g.constantBuffers = [(nIn + 1, MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
      (∀ j < nIn, g.deviceBuffers.lookup j =
        some (MetalAst.ByteMemory.ofU64Words (inWords j)) ∧ (inWords j).length = len) →
      g.deviceBuffers.lookup nIn = some outMem →
      outMem.bytes.size = len * 8 →
      (∀ i < len,
        (gx * groupSize ≤ i ∧ i < gx * groupSize + tx0 →
          outMem.readU64Word? i = some (specWord i)) ∧
        (¬ (gx * groupSize ≤ i ∧ i < gx * groupSize + tx0) →
          outMem.readU64Word? i = outMem0.readU64Word? i)) →
      (∀ a ∈ g.epochLog, SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + tx0)) a) →
      (∀ d ∈ done, d.halted = true) →
      g.threads = done ++ (List.range rem).map (fun d => mkLane (tx0 + d)) →
      ∃ (gFinal : MSLGroupState) (outMemFinal : MetalAst.ByteMemory),
        runGroupWithDeviceLog f g [] = .ok (gFinal, gFinal.epochLog.filter isDeviceAccess) ∧
        (∀ j < nIn, gFinal.deviceBuffers.lookup j =
          some (MetalAst.ByteMemory.ofU64Words (inWords j))) ∧
        gFinal.deviceBuffers.lookup nIn = some outMemFinal ∧
        outMemFinal.bytes.size = len * 8 ∧
        (∀ i < len,
          (gx * groupSize ≤ i ∧ i < (gx + 1) * groupSize →
            outMemFinal.readU64Word? i = some (specWord i)) ∧
          (¬ (gx * groupSize ≤ i ∧ i < (gx + 1) * groupSize) →
            outMemFinal.readU64Word? i = outMem0.readU64Word? i)) ∧
        (∀ a ∈ gFinal.epochLog.filter isDeviceAccess,
          SimtLogInv nIn (min len (gx * groupSize)) (min len ((gx + 1) * groupSize)) a) := by
  intro body mkLane
  have hbody : body = inner ++ [.returnStmt] := metal_body facts idxVar lenVar cert inner hcert hmem
  intro rem
  induction rem with
  | zero =>
    intro tx0 f g done outMem0 outMem htx _ _ hst hfn hbd hcb hin hout hsize hwords hlog hdone hthreads
    have htxEq : tx0 = groupSize := by omega
    have hcxEq : gx * groupSize + tx0 = (gx + 1) * groupSize := by
      rw [htxEq, Nat.succ_mul]
    have hallH : g.threads.all (·.halted) = true := by
      rw [hthreads, List.range_zero, List.map_nil, List.append_nil, List.all_eq_true]
      exact hdone
    have hinG : ∀ j < nIn, g.deviceBuffers.lookup j =
        some (MetalAst.ByteMemory.ofU64Words (inWords j)) := fun j hj => (hin j hj).1
    refine ⟨g, outMem, runGroupWithDeviceLog_all_halted f g hallH, hinG, hout, hsize, ?_, ?_⟩
    · intro i hi
      rw [← hcxEq]
      exact hwords i hi
    · intro a ha
      have ha' : a ∈ g.epochLog := by
        rcases List.mem_filter.mp ha with ⟨hm, _⟩; exact hm
      rw [← hcxEq]
      exact hlog a ha'
  | succ r ih =>
    intro tx0 f g done outMem0 outMem htx hgrid hfuel hst hfn hbd hcb hin hout hsize hwords hlog hdone hthreads
    have hltGrp : gx * groupSize + tx0 < (gx + 1) * groupSize := by
      rw [Nat.succ_mul]; omega
    have hcx : gx * groupSize + tx0 < len :=
      launchBoundsCert_gid_lt_len cert idxVar lenVar gridDimX groupSize len gx tx0
        hcert hlaunch hgx (by omega)
    have hcx32 : gx * groupSize + tx0 < 2 ^ 32 := Nat.lt_trans hltGrp hgrid
    have hfuel' : stepsInner + 1 ≤ f := by
      have : 1 * (stepsInner + 1) ≤ (r + 1) * (stepsInner + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    let todo := (List.range r).map (fun d => mkLane ((tx0 + 1) + d))
    have hmapSplit : (List.range (r + 1)).map (fun d => mkLane (tx0 + d)) = mkLane tx0 :: todo := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro d _
      dsimp only [Function.comp, Nat.succ_eq_add_one]
      have ha : tx0 + (d + 1) = (tx0 + 1) + d := by omega
      rw [ha]
    have hmk0 : mkLane tx0 = {
        tid := { x := tx0, y := 0, z := 0 }
        locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx0, 0, 0)
        stmts := inner ++ [.returnStmt]
        halted := false } := by
      dsimp only [mkLane]; rw [hbody]
    have hsplit : g.threads = done ++ ({
        tid := { x := tx0, y := 0, z := 0 }
        locals := initBuiltinLocal MSLLocals.empty "gid" .uint (gx * groupSize + tx0, 0, 0)
        stmts := inner ++ [.returnStmt]
        halted := false } :: todo) := by
      rw [hthreads, hmapSplit, hmk0]
    have hminLo : min len (gx * groupSize) = gx * groupSize :=
      Nat.min_eq_right (Nat.le_of_lt hcx |> fun h => by omega)
    have hminCx : min len (gx * groupSize + tx0) = gx * groupSize + tx0 :=
      Nat.min_eq_right (Nat.le_of_lt hcx)
    have hminCx1 : min len (gx * groupSize + (tx0 + 1)) = gx * groupSize + tx0 + 1 := by
      have heq : gx * groupSize + (tx0 + 1) = gx * groupSize + tx0 + 1 := by omega
      rw [heq]; exact Nat.min_eq_right (by omega)
    have hlogIn : ∀ a ∈ g.epochLog, SimtLogInv nIn (gx * groupSize) (gx * groupSize + tx0) a := by
      intro a ha
      have h0 := hlog a ha
      rwa [hminLo, hminCx] at h0
    obtain ⟨f', thH, g', outMem', hrun, hf', hhalt, hth, hst', hfn', hbd', hcb', hin', hout', hsize',
        hword, hother, hlog'⟩ :=
      hInner g done todo (gx * groupSize + tx0) tx0 (gx * groupSize) f outMem
        hcx hcx32 hlen64 (by omega) hfuel' hst hfn hbd hcb hin hout hsize hlogIn hdone hsplit
    have hfNext : r * (stepsInner + 1) ≤ f' := by
      have : (r + 1) * (stepsInner + 1) = r * (stepsInner + 1) + (stepsInner + 1) :=
        Nat.succ_mul r (stepsInner + 1)
      omega
    have hdoneNext : ∀ d ∈ done ++ [thH], d.halted = true := by
      intro d hd
      rcases List.mem_append.mp hd with h1 | h2
      · exact hdone d h1
      · rw [List.mem_singleton.mp h2]; exact hhalt
    have hthreadsNext : g'.threads = (done ++ [thH]) ++ todo := by
      rw [hth, List.append_assoc]; rfl
    have hlogNext : ∀ a ∈ g'.epochLog,
        SimtLogInv nIn (min len (gx * groupSize)) (min len (gx * groupSize + (tx0 + 1))) a := by
      rw [hminLo, hminCx1]
      exact hlog'
    have hrest := ih (tx0 + 1) f' g' (done ++ [thH]) outMem0 outMem' (by omega) hgrid
      hfNext hst' hfn' hbd' (hcb'.trans hcb) (fun j hj => ⟨hin' j hj, (hin j hj).2⟩) hout' hsize'
      (by
        intro i hi; constructor
        · intro hrange
          by_cases hc : i = gx * groupSize + tx0
          · subst hc; exact hword
          · rw [hother i hc]; exact (hwords i hi).1 (by omega)
        · intro hrange
          rw [hother i (by omega)]; exact (hwords i hi).2 (by omega))
      hlogNext hdoneNext hthreadsNext
    rcases hrest with ⟨gF, outF, hrun2, hinF, houtF, hsizeF, hwordsF, hlogF⟩
    refine ⟨gF, outF, by rw [hrun]; exact hrun2, hinF, houtF, hsizeF, hwordsF, hlogF⟩

theorem proofRetention_pipeline_nonvacuous :
    let facts : FactEnv :=
      [ .exclusiveObj 0, .noOverflowAdd 1 2 true true, .disjointSlices 3 4 16 32
      , .idxLt 5 6, .idxLt 0 16 ]
    let st : HeapState := { buffers := [{ id := 1, exclusive := true, data := #[42] }], nextId := 2 }
    let env := (VarEnv.empty).bind 0 (.sarrayId 1)
    let rawCode : LNIRCode := .letBind 7 .i1 (.isExclusive 0)
      (.letBind 8 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64) (.ret 8))
    let specCode := dischargeRetainedExclusivity facts rawCode
    let llvmSt := bindReg (bindReg {} "v1" (.bits .i64 4#64)) "v2" (.bits .i64 5#64)
    let llvmIns := emitVerifiedLLVMWithFacts facts 1 2
      [.add "s" .none .i64 (.reg "v1") (.reg "v2")]
    let blk : LLVMBlock :=
      { label := "entry"
      , body := [.load "r" false (.int .i64) (.reg "v3") 8]
      , term := .ret (some (.int .i64, .reg "r")) }
    let ps := noaliasParams facts 3 4 16 32 [{ ty := .ptr 0, name := "v3" }] [blk]
    specCode = .letBind 7 .i1 (.scalar (.constBool true))
        (.letBind 8 (.sarray .i64) (.scalar (.var 0)) (.ret 8)) ∧
      evalCode 3 env st specCode = .ok (.sarrayId 1, st) ∧
      execInstrs {} 1 llvmSt llvmIns = .inr (bindReg llvmSt "s" (.bits .i64 9#64)) ∧
      ps.any (fun p => p.attrs.contains .noalias) = true ∧
      bindArgs {} ps [.ptr 8#64] = some (bindReg {} "v3" (.ptr 8#64)) ∧
      (lowerBoundsFreePTXLoad facts 5 6 .u64 "%d" (.regOffset "%a" 0)).length = 1 ∧
      (lowerBoundsFreeMetalLoad facts 5 6 "buf").length = 1 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  decide

end LeanNative.Proofs
