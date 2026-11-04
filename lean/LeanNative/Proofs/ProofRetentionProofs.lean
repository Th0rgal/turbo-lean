import LeanNative.Frontend.ProofRetention
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.LLVMAst.Eval
import LeanNative.Backend.PTXAst.Syntax
import LeanNative.Backend.PTXAst.Eval
import LeanNative.Backend.MetalAst.Syntax
import LeanNative.Backend.MetalAst.Eval

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Frontend.ProofRetention
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst

set_option autoImplicit false

def ObjIsExclusive (env : VarEnv) (st : HeapState) (objVar : VarId) : Prop :=
  match env objVar with
  | some (.sarrayId bufId) =>
    ∃ buf, st.findBuffer bufId = some buf ∧ buf.exclusive = true
  | some (.objPtr objId) => st.getObjRefCount objId = 1
  | some _ => True
  | none => False

def FactHolds (env : VarEnv) (st : HeapState) (f : RetainedFact) : Prop :=
  match f with
  | .idxLt i n =>
    ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
  | .noOverflowAdd a b nsw nuw =>
    ∃ av bv : UInt64,
      env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
      (nsw = true →
        addOverflowNSW .i64 (BitVec.ofNat 64 av.toNat) (BitVec.ofNat 64 bv.toNat) = false) ∧
      (nuw = true →
        addOverflowNUW .i64 (BitVec.ofNat 64 av.toNat) (BitVec.ofNat 64 bv.toNat) = false)
  | .noOverflowMul a b nsw nuw =>
    ∃ av bv : UInt64,
      env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
      (nsw = true →
        mulOverflowNSW .i64 (BitVec.ofNat 64 av.toNat) (BitVec.ofNat 64 bv.toNat) = false) ∧
      (nuw = true →
        mulOverflowNUW .i64 (BitVec.ofNat 64 av.toNat) (BitVec.ofNat 64 bv.toNat) = false)
  | .alignedPtr p n =>
    0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
  | .disjointSlices a b =>
    ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧ av ≠ bv
  | .exclusiveObj o => ObjIsExclusive env st o

def FactEnvHolds (env : VarEnv) (st : HeapState) (facts : FactEnv) : Prop :=
  ∀ f, factMember facts f = true → FactHolds env st f

theorem evalExpr_isExclusive_of_obj
    (env : VarEnv) (st : HeapState) (objVar : VarId)
    (h : ObjIsExclusive env st objVar) :
    evalExpr env st (.isExclusive objVar) = .ok (.bool true, st) := by
  unfold ObjIsExclusive at h
  simp only [evalExpr]
  cases henv : env objVar with
  | none =>
    simp [henv] at h
  | some v =>
    cases v with
    | sarrayId bufId =>
      simp only [henv] at h
      rcases h with ⟨buf, hfind, hex⟩
      simp [henv, hfind, hex]
    | objPtr objId =>
      simp only [henv] at h
      simp [henv, h, show st.getObjRefCount objId ≠ 0 by omega]
    | u64 n => simp [henv]
    | u256 n => simp [henv]
    | bool b => simp [henv]
    | tuple vs => simp [henv]
    | rawPtrId n => simp [henv]
    | storageMapId n => simp [henv]
    | unit => simp [henv]

theorem constBool_true_eval (env : VarEnv) (st : HeapState) :
    evalExpr env st (.scalar (.constBool true)) = .ok (.bool true, st) := by
  simp [evalExpr, evalScalarExpr]

theorem evalCtorGet_state
    (env : VarEnv) (st st' : HeapState) (c : VarId) (i : Nat) (isObj : Bool) (v : Val)
    (he : evalCtorGet env st c i isObj = .ok (v, st')) :
    st' = st := by
  unfold evalCtorGet at he
  cases hc : env c with
  | none =>
    simp [hc] at he
  | some vc =>
    cases vc with
    | objPtr oid =>
      simp only [hc] at he
      cases ho : st.liveHeapObj oid with
      | error err =>
        simp [ho, Except.bind] at he
      | ok o =>
        simp only [ho, Except.bind] at he
        split at he
        · cases he
          rfl
        · cases he
    | tuple xs =>
      cases xs with
      | nil =>
        simp [hc] at he
      | cons tag vals =>
        simp only [hc] at he
        split at he
        · cases he
          rfl
        · cases he
    | u64 n => simp [hc] at he
    | u256 n => simp [hc] at he
    | bool b => simp [hc] at he
    | sarrayId n => simp [hc] at he
    | rawPtrId n => simp [hc] at he
    | storageMapId n => simp [hc] at he
    | unit => simp [hc] at he

theorem exprPreservesHeap_state
    (env : VarEnv) (st st' : HeapState) (e : LNIRExpr) (v : Val)
    (hp : exprPreservesHeap e = true)
    (he : evalExpr env st e = .ok (v, st')) :
    st' = st := by
  cases e with
  | scalar se =>
    simp only [evalExpr] at he
    split at he
    · cases he; rfl
    · cases he
  | constU256 val =>
    cases he
    rfl
  | mulDivDown a b d =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · split at he
        · cases he
        · split at he
          · cases he; rfl
          · cases he
      · cases he
    · cases he
    · cases he
    · cases he
  | mulDivUp a b d =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · split at he
        · cases he
        · split at he
          · cases he; rfl
          · cases he
      · cases he
    · cases he
    · cases he
    · cases he
  | storageLoad m s =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · cases he; rfl
      · cases he
    · cases he
    · cases he
    · cases he
  | mkTuple vs =>
    simp only [evalExpr] at he
    split at he
    · cases he; rfl
    · cases he
  | projTuple t i =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · cases he; rfl
      · cases he
    · cases he
    · cases he
  | ctorGetObj c i =>
    exact evalCtorGet_state env st st' c i true v he
  | ctorGetScalar c i ty =>
    exact evalCtorGet_state env st st' c i false v he
  | isExclusive o =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · cases he; rfl
      · cases he
    · split at he
      · cases he
      · cases he; rfl
    · cases he; rfl
    · cases he
  | sarrayLen a =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · cases he; rfl
      · cases he
    · cases he
    · cases he
  | sarrayDataPtr a ty =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · split at he
        · cases he; rfl
        · cases he
      · cases he
    · cases he; rfl
    · cases he
    · cases he
  | sarrayGet a i ty =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · cases he; rfl
      · cases he
    · cases he
    · cases he
    · cases he
  | rawLoad p i ty =>
    simp only [evalExpr] at he
    split at he
    · split at he
      · cases he; rfl
      · cases he
    · split at he
      · cases he; rfl
      · cases he
    · cases he
    · cases he
    · cases he
  | boxScalar x ty =>
    simp only [evalExpr] at he
    split at he
    · cases he; rfl
    · cases he
  | unboxScalar x ty =>
    simp only [evalExpr] at he
    split at he
    · cases he; rfl
    · cases he
  | storageStore _ _ _ => simp [exprPreservesHeap] at hp
  | allocCtor _ _ _ => simp [exprPreservesHeap] at hp
  | sarrayEnsureExclusive _ _ => simp [exprPreservesHeap] at hp
  | sarraySet _ _ _ _ => simp [exprPreservesHeap] at hp
  | call _ _ _ _ => simp [exprPreservesHeap] at hp

theorem fact_survives_bind
    (env : VarEnv) (st : HeapState) (dst : VarId) (v : Val) (f : RetainedFact)
    (hmention : factMentions dst f = false)
    (hf : FactHolds env st f) :
    FactHolds (env.bind dst v) st f := by
  cases f with
  | idxLt i n =>
    simp only [factMentions, Bool.or_eq_false_iff] at hmention
    rcases hmention with ⟨hi, hn⟩
    rcases hf with ⟨iv, nv, h1, h2, hlt⟩
    refine ⟨iv, nv, ?_, ?_, hlt⟩
    · simpa [VarEnv.bind, hi] using h1
    · simpa [VarEnv.bind, hn] using h2
  | noOverflowAdd a b nsw nuw =>
    simp only [factMentions, Bool.or_eq_false_iff] at hmention
    rcases hmention with ⟨ha, hb⟩
    rcases hf with ⟨av, bv, h1, h2, hnsw, hnuw⟩
    refine ⟨av, bv, ?_, ?_, hnsw, hnuw⟩
    · simpa [VarEnv.bind, ha] using h1
    · simpa [VarEnv.bind, hb] using h2
  | noOverflowMul a b nsw nuw =>
    simp only [factMentions, Bool.or_eq_false_iff] at hmention
    rcases hmention with ⟨ha, hb⟩
    rcases hf with ⟨av, bv, h1, h2, hnsw, hnuw⟩
    refine ⟨av, bv, ?_, ?_, hnsw, hnuw⟩
    · simpa [VarEnv.bind, ha] using h1
    · simpa [VarEnv.bind, hb] using h2
  | alignedPtr p n =>
    simp only [factMentions] at hmention
    rcases hf with ⟨hn, pv, hp, hmod⟩
    refine ⟨hn, pv, ?_, hmod⟩
    simpa [VarEnv.bind, hmention] using hp
  | disjointSlices a b =>
    simp only [factMentions, Bool.or_eq_false_iff] at hmention
    rcases hmention with ⟨ha, hb⟩
    rcases hf with ⟨av, bv, h1, h2, hne⟩
    refine ⟨av, bv, ?_, ?_, hne⟩
    · simpa [VarEnv.bind, ha] using h1
    · simpa [VarEnv.bind, hb] using h2
  | exclusiveObj o =>
    simp only [factMentions] at hmention
    simp only [FactHolds, ObjIsExclusive] at hf ⊢
    simpa [VarEnv.bind, hmention] using hf

theorem envHolds_killVar
    (env : VarEnv) (st : HeapState) (dst : VarId) (v : Val) (facts : FactEnv)
    (hf : FactEnvHolds env st facts) :
    FactEnvHolds (env.bind dst v) st (killVarFacts dst facts) := by
  intro f hmem
  unfold killVarFacts factMember at hmem
  have h1 : f ∈ facts.filter (fun g => !factMentions dst g) := List.mem_of_elem_eq_true hmem
  rw [List.mem_filter] at h1
  have hmem0 : factMember facts f = true := List.elem_eq_true_of_mem h1.1
  have hmention : factMentions dst f = false := by
    simpa using h1.2
  exact fact_survives_bind env st dst v f hmention (hf f hmem0)

theorem discharge_empty (code : LNIRCode) :
    dischargeRetainedExclusivity [] code = code := by
  induction code with
  | letBind dst ty val k ih =>
    cases val with
    | isExclusive objVar =>
      simp [dischargeRetainedExclusivity, factMember, killVarFacts, ih]
    | scalar se => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | constU256 n => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | mulDivDown a b d => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | mulDivUp a b d => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | storageLoad m s => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | storageStore m s v => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | mkTuple vs => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | projTuple t i => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | allocCtor tag n fs => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | ctorGetObj c i => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | ctorGetScalar c i ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | sarrayEnsureExclusive a ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | sarrayLen a => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | sarrayDataPtr a ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | sarrayGet a i ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | sarraySet a i v ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | rawLoad p i ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | boxScalar x ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | unboxScalar x ty => simp [dischargeRetainedExclusivity, killVarFacts, ih]
    | call fn cc ty args => simp [dischargeRetainedExclusivity, killVarFacts, ih]
  | rawStore p i v ty k ih =>
    simp [dischargeRetainedExclusivity, ih]
  | incRef v n k ih =>
    simp [dischargeRetainedExclusivity, ih]
  | decRef v n k ih =>
    simp [dischargeRetainedExclusivity, ih]
  | ite c t e iht ihe =>
    simp [dischargeRetainedExclusivity, iht, ihe]
  | seqFor idx lo hi acc init ty body k ihb ihk =>
    simp [dischargeRetainedExclusivity, ihb, ihk]
  | parFor out len ins ty ker k ih =>
    simp [dischargeRetainedExclusivity, ih]
  | ret v => rfl
  | unreachable => rfl

theorem dischargeRetainedExclusivity_sound
    (fuel : Nat) (env : VarEnv) (st : HeapState) (facts : FactEnv) (code : LNIRCode)
    (hfacts : FactEnvHolds env st facts) (v : Val) (st' : HeapState)
    (heval : evalCode fuel env st code = .ok (v, st')) :
    evalCode fuel env st (dischargeRetainedExclusivity facts code) = .ok (v, st') := by
  induction code generalizing env st facts with
  | letBind dst ty val k ih =>
    simp only [evalCode] at heval
    cases hval : evalExpr env st val with
    | error err =>
      simp [hval] at heval
    | ok pair =>
      rcases pair with ⟨vv, st1⟩
      simp only [hval] at heval
      by_cases hp : exprPreservesHeap val = true
      · have hst : st1 = st := exprPreservesHeap_state env st st1 val vv hp hval
        rw [hst] at heval
        have hkill : FactEnvHolds (env.bind dst vv) st (killVarFacts dst facts) :=
          envHolds_killVar env st dst vv facts hfacts
        cases val with
        | isExclusive objVar =>
          by_cases hmem : factMember facts (.exclusiveObj objVar) = true
          · have hobj : ObjIsExclusive env st objVar := by
              simpa [FactHolds] using hfacts (.exclusiveObj objVar) hmem
            have htrue := evalExpr_isExclusive_of_obj env st objVar hobj
            have hvv : vv = .bool true := by
              rw [htrue] at hval
              cases hval
              rfl
            rw [hvv] at heval hkill
            simp [dischargeRetainedExclusivity, evalCode, hmem, constBool_true_eval]
            exact ih (env.bind dst (.bool true)) st (killVarFacts dst facts) hkill heval
          · simp [dischargeRetainedExclusivity, evalCode, hmem, hval, hst]
            exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | scalar se =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | constU256 n =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | mulDivDown a b d =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | mulDivUp a b d =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | storageLoad m s =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | mkTuple vs =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | projTuple t i =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | ctorGetObj c i =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | ctorGetScalar c i ty2 =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | sarrayLen a =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | sarrayDataPtr a ty2 =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | sarrayGet a i ty2 =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | rawLoad p i ty2 =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | boxScalar x ty2 =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | unboxScalar x ty2 =>
          simp [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, hval, hst]
          exact ih (env.bind dst vv) st (killVarFacts dst facts) hkill heval
        | storageStore _ _ _ => simp [exprPreservesHeap] at hp
        | allocCtor _ _ _ => simp [exprPreservesHeap] at hp
        | sarrayEnsureExclusive _ _ => simp [exprPreservesHeap] at hp
        | sarraySet _ _ _ _ => simp [exprPreservesHeap] at hp
        | call _ _ _ _ => simp [exprPreservesHeap] at hp
      · have hp0 : exprPreservesHeap val = false := Bool.eq_false_iff.mpr hp
        cases val with
        | isExclusive _ => simp [exprPreservesHeap] at hp0
        | scalar _ => simp [exprPreservesHeap] at hp0
        | constU256 _ => simp [exprPreservesHeap] at hp0
        | mulDivDown _ _ _ => simp [exprPreservesHeap] at hp0
        | mulDivUp _ _ _ => simp [exprPreservesHeap] at hp0
        | storageLoad _ _ => simp [exprPreservesHeap] at hp0
        | mkTuple _ => simp [exprPreservesHeap] at hp0
        | projTuple _ _ => simp [exprPreservesHeap] at hp0
        | ctorGetObj _ _ => simp [exprPreservesHeap] at hp0
        | ctorGetScalar _ _ _ => simp [exprPreservesHeap] at hp0
        | sarrayLen _ => simp [exprPreservesHeap] at hp0
        | sarrayDataPtr _ _ => simp [exprPreservesHeap] at hp0
        | sarrayGet _ _ _ => simp [exprPreservesHeap] at hp0
        | rawLoad _ _ _ => simp [exprPreservesHeap] at hp0
        | boxScalar _ _ => simp [exprPreservesHeap] at hp0
        | unboxScalar _ _ => simp [exprPreservesHeap] at hp0
        | storageStore m s x =>
          simpa [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, discharge_empty, hval]
            using heval
        | allocCtor tag n fs =>
          simpa [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, discharge_empty, hval]
            using heval
        | sarrayEnsureExclusive a ty2 =>
          simpa [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, discharge_empty, hval]
            using heval
        | sarraySet a i x ty2 =>
          simpa [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, discharge_empty, hval]
            using heval
        | call fn cc rty args =>
          simpa [dischargeRetainedExclusivity, evalCode, exprPreservesHeap, discharge_empty, hval]
            using heval
  | rawStore p i vv ty k ih =>
    simpa [dischargeRetainedExclusivity, discharge_empty] using heval
  | incRef obj n k ih =>
    simpa [dischargeRetainedExclusivity, discharge_empty] using heval
  | decRef obj n k ih =>
    simpa [dischargeRetainedExclusivity, discharge_empty] using heval
  | ite c t e iht ihe =>
    simp only [evalCode] at heval
    simp only [dischargeRetainedExclusivity, evalCode]
    cases hc : env c with
    | none =>
      simp [hc] at heval
    | some cv =>
      cases cv with
      | bool b =>
        cases b
        · simp [hc] at heval ⊢
          exact ihe env st facts hfacts heval
        · simp [hc] at heval ⊢
          exact iht env st facts hfacts heval
      | u64 n =>
        by_cases hn : n = 0
        · simp [hc, hn] at heval ⊢
          exact ihe env st facts hfacts heval
        · simp [hc, hn] at heval ⊢
          exact iht env st facts hfacts heval
      | u256 w =>
        by_cases hw : w = UInt256.zero
        · simp [hc, hw] at heval ⊢
          exact ihe env st facts hfacts heval
        · simp [hc, hw] at heval ⊢
          exact iht env st facts hfacts heval
      | tuple xs => simp [hc] at heval
      | objPtr n => simp [hc] at heval
      | sarrayId n => simp [hc] at heval
      | rawPtrId n => simp [hc] at heval
      | storageMapId n => simp [hc] at heval
      | unit => simp [hc] at heval
  | seqFor idx lo hi acc init ty body k ihb ihk =>
    simpa [dischargeRetainedExclusivity, discharge_empty] using heval
  | parFor out len ins ty ker k ih =>
    simpa [dischargeRetainedExclusivity, discharge_empty] using heval
  | ret r =>
    simpa [dischargeRetainedExclusivity] using heval
  | unreachable =>
    simp [evalCode] at heval

end LeanNative.Proofs
