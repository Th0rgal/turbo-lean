import LeanNative.Frontend.ProofRetention
import LeanNative.Backend.LLVMAst.SemanticsProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.PTXSIMT2
import LeanNative.Proofs.MetalSIMT1

namespace LeanNative.Proofs

open LeanNative.IR LeanNative.Semantics LeanNative.Frontend.ProofRetention
open LeanNative.Backend LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst LeanNative.Backend.PTXAst LeanNative.Backend.MetalAst

set_option autoImplicit false

def ObjIsExclusive (env : VarEnv) (st : HeapState) (objVar : VarId) : Prop :=
  match env objVar with
  | some (.sarrayId bufId) =>
    (∃ buf, st.findBuffer bufId = some buf ∧ buf.exclusive = true) ∧ BuffersExclusiveFor st.buffers bufId
  | some (.objPtr objId) => st.getObjRefCount objId = 1
  | some _ => True
  | none => False

def FactHolds (env : VarEnv) (st : HeapState) (f : RetainedFact) : Prop :=
  match f with
  | .idxLt i n => ∃ iv nv : UInt64, env i = some (.u64 iv) ∧ env n = some (.u64 nv) ∧ iv.toNat < nv.toNat
  | .noOverflowAdd a b nsw nuw =>
    ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
      (nsw = true → addOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
      (nuw = true → addOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
  | .noOverflowMul a b nsw nuw =>
    ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧
      (nsw = true → mulOverflowNSW .i64 av.toBitVec bv.toBitVec = false) ∧
      (nuw = true → mulOverflowNUW .i64 av.toBitVec bv.toBitVec = false)
  | .alignedPtr p n => 0 < n ∧ ∃ pv : UInt64, env p = some (.u64 pv) ∧ pv.toNat % n = 0
  | .disjointSlices a b => ∃ av bv : UInt64, env a = some (.u64 av) ∧ env b = some (.u64 bv) ∧ av ≠ bv
  | .exclusiveObj o => ObjIsExclusive env st o

def FactEnvHolds (env : VarEnv) (st : HeapState) (facts : FactEnv) : Prop :=
  ∀ f, factMember facts f = true → FactHolds env st f

theorem evalExpr_isExclusive_of_obj (env : VarEnv) (st : HeapState) (objVar : VarId)
    (h : ObjIsExclusive env st objVar) : evalExpr env st (.isExclusive objVar) = .ok (.bool true, st) := by
  unfold ObjIsExclusive at h; simp only [evalExpr]
  cases henv : env objVar with
  | none => simp [henv] at h
  | some v =>
    cases v with
    | sarrayId bufId => simp only [henv] at h; rcases h with ⟨⟨buf, hfind, hex⟩, _⟩; simp [hfind, hex]
    | objPtr objId => simp only [henv] at h; simp [h]
    | u64 _ | u256 _ | bool _ | tuple _ | rawPtrId _ | storageMapId _ | unit => simp

theorem evalExpr_ensureExclusive_of_obj (env : VarEnv) (st st1 : HeapState) (objVar : VarId)
    (ty : LNIRType) (vv : Val) (h : ObjIsExclusive env st objVar)
    (heval : evalExpr env st (.sarrayEnsureExclusive objVar ty) = .ok (vv, st1)) :
    st1 = st ∧ evalExpr env st (.scalar (.var objVar)) = .ok (vv, st) := by
  unfold ObjIsExclusive at h; simp only [evalExpr] at heval
  cases henv : env objVar with
  | none => simp [henv] at heval
  | some v =>
    cases v with
    | sarrayId bufId =>
      simp only [henv] at h heval; rcases h with ⟨⟨buf, hfind, _⟩, hexcl⟩
      rw [ensureExclusive_of_exclusive st bufId buf hfind hexcl] at heval; cases heval
      exact ⟨rfl, by simp [evalExpr, evalScalarExpr, henv]⟩
    | u64 _ | u256 _ | bool _ | tuple _ | objPtr _ | rawPtrId _ | storageMapId _ | unit => simp [henv] at heval

private theorem constBool_true_eval (env : VarEnv) (st : HeapState) :
    evalExpr env st (.scalar (.constBool true)) = .ok (.bool true, st) := by simp [evalExpr, evalScalarExpr]

private theorem evalCtorGet_state (env : VarEnv) (st st' : HeapState) (c : VarId) (i : Nat)
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
    | u64 _ | u256 _ | bool _ | sarrayId _ | rawPtrId _ | storageMapId _ | unit => simp [evalCtorGet, vc] at he

private theorem exprPreservesHeap_state (env : VarEnv) (st st' : HeapState)
    (e : LNIRExpr) (v : Val) (hp : exprPreservesHeap e = true)
    (he : evalExpr env st e = .ok (v, st')) : st' = st := by
  cases e with
  | ctorGetObj c i => exact evalCtorGet_state env st st' c i true v he
  | ctorGetScalar c i _ => exact evalCtorGet_state env st st' c i false v he
  | constU256 _ => cases he <;> rfl
  | storageStore _ _ _ | allocCtor _ _ _ | sarrayEnsureExclusive _ _
  | sarraySet _ _ _ _ | call _ _ _ _ => simp [exprPreservesHeap] at hp
  | scalar _ | mulDivDown _ _ _ | mulDivUp _ _ _ | storageLoad _ _ | mkTuple _ | projTuple _ _
  | isExclusive _ | sarrayLen _ | sarrayDataPtr _ _ | sarrayGet _ _ _ | rawLoad _ _ _
  | boxScalar _ _ | unboxScalar _ _ =>
    revert he; simp only [evalExpr]; repeat split
    all_goals
      intro he; try split at he
      all_goals try split at he
      all_goals simp at he
      all_goals exact he.2.symm

private theorem fact_survives_bind (env : VarEnv) (st : HeapState) (dst : VarId) (v : Val)
    (f : RetainedFact) (hmention : factMentions dst f = false) (hf : FactHolds env st f) :
    FactHolds (env.bind dst v) st f := by
  cases f with
  | idxLt i n | disjointSlices i n =>
    simp only [factMentions, Bool.or_eq_false_iff] at hmention; rcases hmention with ⟨hi, hn⟩
    rcases hf with ⟨iv, nv, h1, h2, hr⟩
    exact ⟨iv, nv, by simpa [VarEnv.bind, hi] using h1, by simpa [VarEnv.bind, hn] using h2, hr⟩
  | noOverflowAdd a b nsw nuw | noOverflowMul a b nsw nuw =>
    simp only [factMentions, Bool.or_eq_false_iff] at hmention; rcases hmention with ⟨ha, hb⟩
    rcases hf with ⟨av, bv, h1, h2, hnsw, hnuw⟩
    exact ⟨av, bv, by simpa [VarEnv.bind, ha] using h1, by simpa [VarEnv.bind, hb] using h2, hnsw, hnuw⟩
  | alignedPtr p n =>
    simp only [factMentions] at hmention; rcases hf with ⟨hn, pv, hp, hmod⟩
    exact ⟨hn, pv, by simpa [VarEnv.bind, hmention] using hp, hmod⟩
  | exclusiveObj o =>
    simp only [factMentions] at hmention; simpa [FactHolds, ObjIsExclusive, VarEnv.bind, hmention] using hf

private theorem envHolds_killVar (env : VarEnv) (st : HeapState) (dst : VarId) (v : Val)
    (facts : FactEnv) (hf : FactEnvHolds env st facts) :
    FactEnvHolds (env.bind dst v) st (killVarFacts dst facts) := by
  intro f hmem; unfold killVarFacts factMember at hmem
  have h1 := List.mem_filter.mp (List.mem_of_elem_eq_true hmem)
  exact fact_survives_bind env st dst v f (by simpa using h1.2)
    (hf f (List.elem_eq_true_of_mem h1.1))

private theorem envHolds_cons (env : VarEnv) (st : HeapState) (f0 : RetainedFact) (facts : FactEnv)
    (hf0 : FactHolds env st f0) (hf : FactEnvHolds env st facts) : FactEnvHolds env st (consFact facts f0) := by
  intro f hmem; unfold consFact at hmem; split at hmem
  · exact hf f hmem
  · simp only [factMember, List.contains_eq_mem, List.decide_mem_cons, Bool.or_eq_true, beq_iff_eq] at hmem
    rcases hmem with rfl | hm
    · exact hf0
    · exact hf f (decide_eq_true hm)

private theorem intro_holds (env : VarEnv) (st st1 : HeapState) (dst : VarId) (val : LNIRExpr)
    (vv : Val) (facts : FactEnv) (hval : evalExpr env st val = .ok (vv, st1))
    (hf : FactEnvHolds (env.bind dst vv) st1 facts) :
    FactEnvHolds (env.bind dst vv) st1 (introExprFact dst val facts) := by
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
          exact envHolds_cons _ _ _ _ (by simp [FactHolds, ObjIsExclusive, VarEnv.bind, hfind1, hex1, hexcl]) hf
      | u64 _ | u256 _ | bool _ | tuple _ | objPtr _ | rawPtrId _ | storageMapId _ | unit => simp [ha] at hval
  | _ => exact hf

theorem dischargeRetainedExclusivity_sound
    (fuel : Nat) (env : VarEnv) (st : HeapState) (facts : FactEnv) (code : LNIRCode)
    (hfacts : FactEnvHolds env st facts) (v : Val) (st' : HeapState)
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
            have hst := exprPreservesHeap_state env st st1 _ vv rfl hval
            by_cases hmem : factMember facts (.exclusiveObj objVar) = true
            · have hobj : ObjIsExclusive env st objVar := by simpa [FactHolds] using hfacts _ hmem
              rw [evalExpr_isExclusive_of_obj env st objVar hobj] at hval; cases hval; rw [hst]
              exact ⟨rfl, by simp [specializeExclExpr, hmem, constBool_true_eval]⟩
            · exact ⟨hst, by simp [specializeExclExpr, hmem, hst, hval]⟩
          | sarrayEnsureExclusive objVar ety =>
            have hmem : factMember facts (.exclusiveObj objVar) = true := by simpa [exprPreservesExcl] using hp
            have hobj : ObjIsExclusive env st objVar := by simpa [FactHolds] using hfacts _ hmem
            rcases evalExpr_ensureExclusive_of_obj env st st1 objVar ety vv hobj hval with ⟨hst, hev⟩
            exact ⟨hst, by simp [specializeExclExpr, hmem, hev]⟩
          | _ =>
            have hst := exprPreservesHeap_state env st st1 _ vv (by simpa [exprPreservesExcl] using hp) hval
            exact ⟨hst, by simp [specializeExclExpr, hst, hval]⟩
        rcases hstep with ⟨hst, hev'⟩; rw [hst] at hval heval
        simp only [dischargeRetainedExclusivity, hp, ite_true, evalCode, hev']
        exact ih fuel _ st _ (intro_holds env st st dst val vv _ hval (envHolds_killVar env st dst vv facts hfacts)) v st' heval
      · have hp0 : exprPreservesExcl facts val = false := Bool.eq_false_iff.mpr hp
        have hvm : specializeExclExpr facts val = val := by
          cases val with
          | isExclusive _ => simp [exprPreservesExcl, exprPreservesHeap] at hp0
          | sarrayEnsureExclusive _ _ => simp only [exprPreservesExcl] at hp0; simp [specializeExclExpr, hp0]
          | _ => rfl
        simp only [dischargeRetainedExclusivity, hp0, Bool.false_eq_true, ite_false, hvm, evalCode, hval]
        exact ih fuel _ st1 _ (intro_holds env st st1 dst val vv [] hval (fun _ hm => nomatch hm)) v st' heval
  | rawStore _ _ _ _ _ ih =>
    exact CodeRefines.rawStore_congr (fun fl e s r sr h => ih fl e s [] (fun _ hm => nomatch hm) r sr h) fuel env st v st' heval
  | incRef _ _ _ ih =>
    exact CodeRefines.incRef_congr (fun fl e s r sr h => ih fl e s [] (fun _ hm => nomatch hm) r sr h) fuel env st v st' heval
  | decRef _ _ _ ih =>
    exact CodeRefines.decRef_congr (fun fl e s r sr h => ih fl e s [] (fun _ hm => nomatch hm) r sr h) fuel env st v st' heval
  | parFor _ _ _ _ _ _ ih =>
    exact CodeRefines.parFor_congr (fun fl e s r sr h => ih fl e s [] (fun _ hm => nomatch hm) r sr h) fuel env st v st' heval
  | seqFor idx lo hi acc init _ body _ _ ihk =>
    simp only [dischargeRetainedExclusivity, evalCode] at heval ⊢
    cases hlo : env lo <;> cases hhi : env hi
    all_goals cases hinit : env init <;> simp only [hlo, hhi, hinit] at heval ⊢
    all_goals try exact heval
    rename_i vlo vhi vinit
    cases vlo <;> cases vhi <;> try exact heval
    simp only at heval ⊢
    cases hl : evalSeqLoop _ _ idx acc vinit env st (fun e s => evalCode fuel e s body) with
    | error _ => simp [hl] at heval
    | ok pr => simp only [hl] at heval; exact ihk fuel _ pr.2 [] (fun _ hm => nomatch hm) v st' heval
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

theorem dischargeLocalExclusivity_refines (code : LNIRCode) : CodeRefines code (dischargeRetainedExclusivity [] code) :=
  fun fuel env st v st' h => dischargeRetainedExclusivity_sound fuel env st [] code (fun _ hm => nomatch hm) v st' h
def proofRetentionContract : LeanNative.Transform.VerifiedCodePassContract :=
  verifiedProofRetentionContract dischargeLocalExclusivity_refines
def proofRetentionPass : LeanNative.Transform.TransformPass :=
  LeanNative.Transform.TransformPass.ofVerifiedContract proofRetentionContract

def llvmFactEnv (st : ExecState) : VarEnv := fun v => match st.regs.lookup s!"v{v}" with
  | some (.bits .i64 x) => some (Val.u64 (UInt64.ofBitVec x)) | _ => none

private theorem llvmFactEnv_lookup_u64 (st : ExecState) (v : VarId) (u u' : UInt64)
    (hreg : st.regs.lookup s!"v{v}" = some (.bits .i64 u.toBitVec))
    (henv : llvmFactEnv st v = some (Val.u64 u')) : u' = u := by
  unfold llvmFactEnv at henv
  rw [hreg] at henv; cases henv; rfl

private theorem overflowOf_no_overflow (st : ExecState) (facts : FactEnv) (isMul : Bool) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup s!"v{a}" = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup s!"v{b}" = some (.bits .i64 bv.toBitVec))
    (hf : FactEnvHolds (llvmFactEnv st) .empty facts) :
    flagsOverflow (overflowOf facts isMul a b)
      (if isMul then mulOverflowNSW .i64 av.toBitVec bv.toBitVec else addOverflowNSW .i64 av.toBitVec bv.toBitVec)
      (if isMul then mulOverflowNUW .i64 av.toBitVec bv.toBitVec else addOverflowNUW .i64 av.toBitVec bv.toBitVec) = false := by
  have himp : ∀ (pickNsw : Bool) f, f ∈ facts →
      (match f with
        | .noOverflowAdd l r nsw nuw => !isMul && l == a && r == b && (if pickNsw then nsw else nuw)
        | .noOverflowMul l r nsw nuw => isMul && l == a && r == b && (if pickNsw then nsw else nuw)
        | _ => false) = true →
      (if pickNsw then if isMul then mulOverflowNSW .i64 av.toBitVec bv.toBitVec else addOverflowNSW .i64 av.toBitVec bv.toBitVec
       else if isMul then mulOverflowNUW .i64 av.toBitVec bv.toBitVec else addOverflowNUW .i64 av.toBitVec bv.toBitVec) = false := by
    intro pickNsw f hmem hp
    have hfact := hf f (List.elem_eq_true_of_mem hmem)
    cases f with
    | noOverflowAdd l r nsw nuw | noOverflowMul l r nsw nuw =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hp; rcases hp with ⟨⟨⟨hm, hl⟩, hr⟩, hn⟩
      rw [hl, hr] at hfact; rcases hfact with ⟨av', bv', hav', hbv', h1, h2⟩
      cases llvmFactEnv_lookup_u64 st a av av' ha hav'
      cases llvmFactEnv_lookup_u64 st b bv bv' hb hbv'
      cases pickNsw <;> cases isMul <;> simp_all
    | idxLt _ _ | alignedPtr _ _ | disjointSlices _ _ | exclusiveObj _ => simp at hp
  unfold overflowOf; dsimp only; split
  · rfl
  · next hnhit =>
    rw [Bool.not_eq_true'] at hnhit; rw [Bool.eq_false_iff, Classical.not_not] at hnhit
    split
    · next hboth =>
      rw [Bool.and_eq_true] at hboth
      rcases List.any_eq_true.mp hboth.1 with ⟨f1, hm1, hp1⟩
      rcases List.any_eq_true.mp hboth.2 with ⟨f2, hm2, hp2⟩
      have h1 := himp true f1 hm1 hp1; have h2 := himp false f2 hm2 hp2
      simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2; simp [flagsOverflow, h1, h2]
    · split
      · next hs =>
        rcases List.any_eq_true.mp hs with ⟨f1, hm1, hp1⟩
        simpa [flagsOverflow] using himp true f1 hm1 hp1
      · next hns =>
        have hu : (facts.any fun f =>
            match f with
            | .noOverflowAdd l r _ nuw => !isMul && l == a && r == b && nuw
            | .noOverflowMul l r _ nuw => isMul && l == a && r == b && nuw
            | _ => false) = true := by
          rcases List.any_eq_true.mp hnhit with ⟨f, hmem, hp⟩
          cases f with
          | noOverflowAdd l r nsw nuw | noOverflowMul l r nsw nuw =>
            simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
            rcases hp with ⟨⟨⟨hm, hl⟩, hr⟩, hn | hn⟩
            · exact absurd (List.any_eq_true.mpr ⟨_, hmem, by simp [hm, hl, hr, hn]⟩) hns
            · exact List.any_eq_true.mpr ⟨_, hmem, by simp [hm, hl, hr, hn]⟩
          | idxLt _ _ | alignedPtr _ _ | disjointSlices _ _ | exclusiveObj _ => simp at hp
        rcases List.any_eq_true.mp hu with ⟨f2, hm2, hp2⟩
        simpa [flagsOverflow] using himp false f2 hm2 hp2

theorem llvmOverflowFlags_of_fact_sound (st : ExecState) (facts : FactEnv) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup s!"v{a}" = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup s!"v{b}" = some (.bits .i64 bv.toBitVec))
    (hf : FactEnvHolds (llvmFactEnv st) .empty facts) :
    stepInstr {} 1 st (.add "dst" (overflowOf facts false a b) .i64 (.reg s!"v{a}") (.reg s!"v{b}")) =
      .inr (bindReg st "dst" (.bits .i64 (av.toBitVec + bv.toBitVec))) := by
  have hov := overflowOf_no_overflow st facts false a b av bv ha hb hf
  simp only [Bool.false_eq_true, ite_false] at hov
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, ha, hb, Option.getD_some]
  simp [binResult, hov]; rfl

theorem llvmMulOverflowFlags_of_fact_sound (st : ExecState) (facts : FactEnv) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup s!"v{a}" = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup s!"v{b}" = some (.bits .i64 bv.toBitVec))
    (hf : FactEnvHolds (llvmFactEnv st) .empty facts) :
    stepInstr {} 1 st (.mul "dst" (overflowOf facts true a b) .i64 (.reg s!"v{a}") (.reg s!"v{b}")) =
      .inr (bindReg st "dst" (.bits .i64 (av.toBitVec * bv.toBitVec))) := by
  have hov := overflowOf_no_overflow st facts true a b av bv ha hb hf; simp only [ite_true] at hov
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, ha, hb, Option.getD_some]
  simp [binResult, hov]; rfl

theorem llvmSubOverflowFlags_of_fact_sound (st : ExecState) (facts : FactEnv) (a b : VarId)
    (av bv : UInt64) (ha : st.regs.lookup s!"v{a}" = some (.bits .i64 av.toBitVec))
    (hb : st.regs.lookup s!"v{b}" = some (.bits .i64 bv.toBitVec))
    (hf : FactEnvHolds (llvmFactEnv st) .empty facts) :
    stepInstr {} 1 st (.sub "dst" (subOverflowOf facts a b) .i64 (.reg s!"v{a}") (.reg s!"v{b}")) =
      .inr (bindReg st "dst" (.bits .i64 (av.toBitVec - bv.toBitVec))) := by
  simp only [stepInstr, stepInstrWith, LLVMAst.evalOperand, lookupReg, ha, hb, Option.getD_some]
  unfold subOverflowOf binResult
  by_cases hmem : factMember facts (.idxLt b a) = true
  · rcases hf (.idxLt b a) hmem with ⟨bv', av', hbv', hav', hlt⟩
    cases llvmFactEnv_lookup_u64 st a av av' ha hav'
    cases llvmFactEnv_lookup_u64 st b bv bv' hb hbv'
    have hnuw : subOverflowNUW .i64 av.toBitVec bv.toBitVec = false := by
      unfold subOverflowNUW; exact decide_eq_false (by change ¬ av.toNat < bv.toNat; omega)
    simp [flagsOverflow, hmem, hnuw]; rfl
  · simp [flagsOverflow, hmem]; rfl

theorem add_nsw_poison_witness :
    stepInstr {} 1 {} (.add "r" .nsw .i64 (.constInt .i64 0x7FFF_FFFF_FFFF_FFFF#64) (.constInt .i64 1#64)) =
      .inr (bindReg {} "r" .poison) := add_nsw_overflow_poison .i64 _ _ (by decide)

private theorem bindArgs_noalias_invariant (st : ExecState) (ps : List LLVMParam) (args : List LLVMVal) :
    bindArgs st (ps.map (withNoAlias true)) args = bindArgs st ps args := by
  induction ps generalizing st args with
  | nil => cases args <;> rfl
  | cons p ps ih =>
    cases args with
    | nil => rfl
    | cons v vs =>
      have hname : (withNoAlias true p).name = p.name := by
        simp only [withNoAlias, Bool.not_true, Bool.false_eq_true, ite_false]; split <;> rfl
      simp only [List.map_cons, bindArgs, hname]; exact ih (bindReg st p.name v) vs

theorem llvmNoAliasParam_of_disjoint_sound (st : ExecState) (facts : FactEnv) (ptrA ptrB : VarId)
    (p0 : LLVMParam) (ps : List LLVMParam) (args : List LLVMVal) (hmem : factMember facts (.disjointSlices ptrA ptrB) = true) :
    (noaliasParams facts ptrA ptrB (p0 :: ps)).any (fun p => p.attrs.contains .noalias) = true ∧
      (noaliasParams facts ptrA ptrB (p0 :: ps)).all (fun p => p.attrs.contains .noalias) = true ∧
      bindArgs st (noaliasParams facts ptrA ptrB (p0 :: ps)) args = bindArgs st (p0 :: ps) args := by
  have hna (p : LLVMParam) : (withNoAlias true p).attrs.contains .noalias = true := by
    simp only [withNoAlias, Bool.not_true, Bool.false_eq_true, ite_false]; by_cases hc : .noalias ∈ p.attrs <;> simp [hc]
  have hall : (noaliasParams facts ptrA ptrB (p0 :: ps)).all (fun p => p.attrs.contains .noalias) = true := by
    simp only [noaliasParams, hmem, Bool.not_true, Bool.false_eq_true, ite_false, List.all_map]
    exact List.all_eq_true.mpr fun p _ => hna p
  refine ⟨?_, hall, by simp only [noaliasParams, hmem, Bool.not_true, Bool.false_eq_true, ite_false]
                       exact bindArgs_noalias_invariant st (p0 :: ps) args⟩
  simp only [noaliasParams, hmem, Bool.not_true, Bool.false_eq_true, ite_false, List.map_cons, List.any_cons, hna p0, Bool.true_or]

theorem readBytesAt_disjoint_of_fact (m : ByteMem) (base addr width : Nat) (bs : List MemByte) (hb : base + bs.length ≤ addr) :
    (m.writeBytesAt base bs).readBytesAt addr width = m.readBytesAt addr width :=
  ByteMem.readBytesAt_writeBytesAt_disjoint m base bs addr width (by unfold rangesDisjoint; exact decide_eq_true (Or.inl hb))

private theorem vreg0 : (s!"v{0}" = "v0") ∧ (s!"v{1}" = "v1") := by decide

theorem ptxBoundsFreeLoad_sound (iv nv base outBase : Nat) (raw : BitVec 64)
    (g g' : PTXAst.ByteMemory) (pMem : ParamMemory) (hiv : iv < nv) (hnv : nv < 2 ^ 64)
    (hbase : base < 2 ^ 64) (hout : outBase < 2 ^ 64) (halign : base % 8 = 0) (hoalign : outBase % 8 = 0)
    (hpIdx : pMem.lookupParam? "param_idx" = some (BitVec.ofNat 64 iv))
    (hpLen : pMem.lookupParam? "param_len" = some (BitVec.ofNat 64 nv))
    (hpAddr : pMem.lookupParam? "param_addr" = some (BitVec.ofNat 64 base))
    (hpOut : pMem.lookupParam? "param_out" = some (BitVec.ofNat 64 outBase))
    (hload : g.loadBits base 8 = some raw) (hstore : g.storeBits outBase 8 raw = some g') :
    let grid : PTXAst.Dim3 := ⟨1, 1, 1⟩
    evalPTXKernel 9 (boundsFreePTXKernel [.idxLt 0 1] 0 1) grid grid g pMem = .ok g' ∧
      evalPTXKernel 12 (boundsFreePTXKernel [] 0 1) grid grid g pMem = .ok g' := by
  intro grid
  have hcmp : evalPTXCmp .ge .u64 (BitVec.ofNat 64 iv) (BitVec.ofNat 64 nv) = false := by
    simp [evalPTXCmp, PTXAst.maskForType, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv,
      Nat.mod_eq_of_lt (Nat.lt_trans hiv hnv), hiv]
  have hbNat : (BitVec.ofNat 64 base).toNat = base := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbase]
  have hoNat : (BitVec.ofNat 64 outBase).toNat = outBase := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hout]
  have hnnB : ¬ ((base : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg base)
  have hnnO : ¬ ((outBase : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg outBase)
  have hu64w : PTXType.u64.bitWidth = 64 := rfl
  have hu64b : PTXType.u64.byteWidth = 8 := rfl
  have hu64p : (PTXType.u64 == PTXType.pred) = false := rfl
  have hpredNe : (PTXType.pred != PTXType.pred) = false := rfl
  have hglobEq : (StateSpace.global == StateSpace.global) = true := rfl
  have hglobNe : (StateSpace.global != StateSpace.global) = false := rfl
  have htidNe : (({ x := 0, y := 0, z := 0 } : PTXAst.Dim3) != { x := 0, y := 0, z := 0 }) = false := rfl
  have hrace : ∀ e, findCrossCTARace? [] e = none := fun _ => rfl
  let rf0 := PTXRegFile.ofRegDecls (boundsFreePTXKernel [] 0 1).regDecls
  have hrf0 : rf0 = { regs := [("%p0", .uninit), ("%v0", .uninit), ("%v1", .uninit), ("%addr", .uninit),
      ("%out", .uninit), ("%dst", .uninit)], decls := [("%p0", .pred), ("%v0", .u64), ("%v1", .u64),
      ("%addr", .u64), ("%out", .u64), ("%dst", .u64)], enforceDecls := true } := by decide
  let rf1 := rf0.setScalarRaw "%dst" 0#64
  let rf2 := rf1.setScalarRaw "%v0" (BitVec.ofNat 64 iv)
  let rf3 := rf2.setScalarRaw "%v1" (BitVec.ofNat 64 nv)
  let rf4 := rf3.setScalarRaw "%addr" (BitVec.ofNat 64 base)
  let rf5 := rf4.setScalarRaw "%out" (BitVec.ofNat 64 outBase)
  let log1 : List MemAccessLog :=
    [{ tid := ⟨0, 0, 0⟩, space := .global, addr := base, width := 8, isWrite := false, isAtomic := false }]
  let log2 : List MemAccessLog :=
    { tid := ⟨0, 0, 0⟩, space := .global, addr := outBase, width := 8, isWrite := true, isAtomic := false } :: log1
  let thAt (pc : Nat) (rf : PTXRegFile) (h : Bool := false) : PTXThreadState :=
    { tid := ⟨0, 0, 0⟩, pc := pc, regs := rf, localMem := PTXAst.ByteMemory.zeros 0, halted := h }
  let ctaAt (th : PTXThreadState) (gm : PTXAst.ByteMemory) (lg : List MemAccessLog) : PTXCTAState :=
    { gridDim := grid, blockDim := grid, ctaId := ⟨0, 0, 0⟩, threads := [th], globalMem := gm
    , sharedMem := PTXAst.ByteMemory.zeros 0, constMem := PTXAst.ByteMemory.zeros 0
    , paramMem := pMem, sharedLayout := { offsets := [], totalSize := 0 }, epochLog := lg }
  let okIns (ins : PTXInstr) : Bool := match ins with | .barSync _ | .shflSyncBfly .. => false | _ => true
  have hpure (f pc : Nat) (stmts : List PTXStmt) (rf rf' : PTXRegFile) (ins : PTXInstr)
      (hpc : stmts[pc]? = some (.instr none ins)) (hok : okIns ins = true)
      (hex : execNonBarrierInstr stmts (ctaAt (thAt pc rf) g []) (thAt pc rf) ins =
        .ok (thAt (pc + 1) rf', g, PTXAst.ByteMemory.zeros 0, [])) :
      runCTAWithGlobalLog (f + 1) stmts (ctaAt (thAt pc rf) g []) [] =
        runCTAWithGlobalLog f stmts (ctaAt (thAt (pc + 1) rf') g []) [] :=
    PTXSIMT.runCTA_pure_instr f stmts (ctaAt (thAt pc rf) g []) [] (thAt pc rf) [] ins rf' []
      rfl (fun _ h => nomatch h) rfl hpc (by intro b h; subst h; cases hok)
      (by intro d s o c m h; subst h; cases hok) hex
  have hmemStep (f pc : Nat) (stmts : List PTXStmt) (rf rf' : PTXRegFile)
      (gm gm' : PTXAst.ByteMemory) (lg lg' : List MemAccessLog) (gd : Option PTXPredGuard)
      (ins : PTXInstr) (hpc : stmts[pc]? = some (.instr gd ins)) (hok : okIns ins = true)
      (hex : execPredicatedInstr stmts (ctaAt (thAt pc rf) gm lg) (thAt pc rf) gd ins =
        .ok (thAt (pc + 1) rf', gm', PTXAst.ByteMemory.zeros 0, lg')) (hnc : lg = [] ∨ lg' ≠ []) :
      runCTAWithGlobalLog (f + 1) stmts (ctaAt (thAt pc rf) gm lg) [] =
        runCTAWithGlobalLog f stmts (ctaAt (thAt (pc + 1) rf') gm' lg') [] :=
    PTXSIMT.runCTAWithGlobalLog_step_no_clear f stmts _ _ []
      (PTXSIMT.step_non_barrier_instr stmts (ctaAt (thAt pc rf) gm lg) [] (thAt pc rf) [] gd ins
        (thAt (pc + 1) rf') gm' (PTXAst.ByteMemory.zeros 0) lg' rfl (fun _ h => nomatch h) rfl hpc
        (by intro b h; subst h; cases hok)
        (by intro d s o c m h; subst h; cases hok) hex) hnc
  have hlbl (f pc : Nat) (stmts : List PTXStmt) (rf : PTXRegFile) (gm : PTXAst.ByteMemory)
      (lg : List MemAccessLog) (lbl : String) (hpc : stmts[pc]? = some (.label lbl)) :
      runCTAWithGlobalLog (f + 1) stmts (ctaAt (thAt pc rf) gm lg) [] =
        runCTAWithGlobalLog f stmts (ctaAt (thAt (pc + 1) rf) gm lg) [] :=
    PTXSIMT.runCTA_label_step f stmts (ctaAt (thAt pc rf) gm lg) [] (thAt pc rf) [] lbl []
      rfl (fun _ h => nomatch h) rfl hpc
  have hret (f pc : Nat) (stmts : List PTXStmt) (rf : PTXRegFile) (gm : PTXAst.ByteMemory)
      (lg : List MemAccessLog) (hpc : stmts[pc]? = some (.instr none .ret)) :
      runCTAWithGlobalLog (f + 1) stmts (ctaAt (thAt pc rf) gm lg) [] =
        runCTAWithGlobalLog f stmts (ctaAt (thAt (pc + 1) rf true) gm lg) [] :=
    PTXSIMT.runCTA_ret_step f stmts (ctaAt (thAt pc rf) gm lg) [] (thAt pc rf) [] []
      rfl (fun _ h => nomatch h) rfl hpc
  have hpre (f : Nat) (mid : List PTXStmt) :
      let stmts := [ PTXStmt.instr none (.mov .u64 "%dst" (.immU64 0#64))
        , .instr none (.ldParam .u64 "%v0" "param_idx"), .instr none (.ldParam .u64 "%v1" "param_len")
        , .instr none (.ldParam .u64 "%addr" "param_addr"), .instr none (.ldParam .u64 "%out" "param_out") ] ++ mid
      runCTAWithGlobalLog (f + 5) stmts (ctaAt (thAt 0 rf0) g []) [] =
        runCTAWithGlobalLog f stmts (ctaAt (thAt 5 rf5) g []) [] := by
    intro stmts; rw [show f + 5 = ((((f + 1) + 1) + 1) + 1) + 1 by omega]
    rw [hpure _ 0 stmts rf0 rf1 _ rfl rfl (by simp [thAt, ctaAt, rf1, hrf0, execNonBarrierInstr,
      PTXAst.evalOperand, PTXRegFile.setScalar, PTXRegFile.setScalarRaw, List.lookup, hu64w, hu64p,
      PTXAst.maskForType, PTXOutcome.bind])]
    rw [hpure _ 1 stmts rf1 rf2 _ rfl rfl (by simp [thAt, ctaAt, rf1, rf2, hrf0, hpIdx,
      execNonBarrierInstr, PTXRegFile.setScalar, PTXRegFile.setScalarRaw, List.lookup, hu64w, hu64p,
      PTXAst.maskForType, PTXOutcome.bind])]
    rw [hpure _ 2 stmts rf2 rf3 _ rfl rfl (by simp [thAt, ctaAt, rf1, rf2, rf3, hrf0, hpLen,
      execNonBarrierInstr, PTXRegFile.setScalar, PTXRegFile.setScalarRaw, List.lookup, hu64w, hu64p,
      PTXAst.maskForType, PTXOutcome.bind])]
    rw [hpure _ 3 stmts rf3 rf4 _ rfl rfl (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, hrf0, hpAddr,
      execNonBarrierInstr, PTXRegFile.setScalar, PTXRegFile.setScalarRaw, List.lookup, hu64w, hu64p,
      PTXAst.maskForType, PTXOutcome.bind])]
    exact hpure _ 4 stmts rf4 rf5 _ rfl rfl (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, hrf0,
      hpOut, execNonBarrierInstr, PTXRegFile.setScalar, PTXRegFile.setScalarRaw, List.lookup, hu64w,
      hu64p, PTXAst.maskForType, PTXOutcome.bind])
  refine ⟨?_, ?_⟩
  · have hrun : runCTAWithGlobalLog 9 (boundsFreePTXKernel [.idxLt 0 1] 0 1).body
        (ctaAt (thAt 0 rf0) g []) [] = .ok (ctaAt (thAt 8 (rf5.setScalarRaw "%dst" raw) true) g' log2, log2) := by
      have hb : (boundsFreePTXKernel [.idxLt 0 1] 0 1).body =
          [ .instr none (.mov .u64 "%dst" (.immU64 0#64))
          , .instr none (.ldParam .u64 "%v0" "param_idx"), .instr none (.ldParam .u64 "%v1" "param_len")
          , .instr none (.ldParam .u64 "%addr" "param_addr"), .instr none (.ldParam .u64 "%out" "param_out") ] ++
          [ .instr none (.ldGlobal .u64 "%dst" (.regOffset "%addr" 0))
          , .instr none (.stGlobal .u64 (.regOffset "%out" 0) (.reg "%dst")), .instr none .ret ] := by decide
      rw [hb, show (9 : Nat) = 4 + 5 from rfl, hpre 4]
      rw [hmemStep 3 5 _ rf5 (rf5.setScalarRaw "%dst" raw) g g [] log1 none _ rfl rfl
        (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, hrf0, log1, execPredicatedInstr,
          evalPredGuard, execNonBarrierInstr, PTXAst.evalAddr, PTXRegFile.readScalarChecked,
          PTXRegFile.setScalar, PTXRegFile.setScalarRaw, PTXRegFile.setAssoc, List.lookup, hu64w,
          hu64b, hu64p, hbNat, hnnB, checkAligned, halign, PTXAst.recordEpochAccess,
          PTXAst.findDataRace?, hload, PTXAst.maskForType, PTXOutcome.bind]) (Or.inl rfl)]
      rw [hmemStep 2 6 _ (rf5.setScalarRaw "%dst" raw) (rf5.setScalarRaw "%dst" raw)
        g g' log1 log2 none _ rfl rfl
        (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, hrf0, log1, log2, execPredicatedInstr,
          evalPredGuard, execNonBarrierInstr, PTXAst.evalAddr, PTXAst.evalOperand,
          PTXRegFile.readScalarChecked, PTXRegFile.setScalarRaw, PTXRegFile.setAssoc, List.lookup,
          hu64w, hu64b, hu64p, hoNat, hnnO, checkAligned, hoalign, PTXAst.recordEpochAccess,
          PTXAst.findDataRace?, htidNe, hglobEq, hstore, PTXAst.maskForType, PTXOutcome.bind])
        (Or.inr (by simp [log2]))]
      rw [hret 1 7 _ _ _ _ rfl]
      simpa [ctaAt, thAt, log2, log1, hglobEq] using PTXSIMT.runCTAWithGlobalLog_done_halted 0 _
        (ctaAt (thAt 8 (rf5.setScalarRaw "%dst" raw) true) g' log2) [] rfl
    have hcta : initCTAState (boundsFreePTXKernel [.idxLt 0 1] 0 1) grid grid ⟨0, 0, 0⟩ g pMem =
        ctaAt (thAt 0 rf0) g [] := by
      simp [initCTAState, buildSharedLayout, boundsFreePTXKernel, rf0, ctaAt, thAt,
        show grid.coords = [⟨0, 0, 0⟩] from rfl]
    simp [evalPTXKernel, show grid.coords = [⟨0, 0, 0⟩] from rfl, evalPTXKernelLoop, hcta, hrun,
      ctaAt, log2, log1, checkCrossCTAGlobalLog, hrace, hglobNe, PTXOutcome.bind]
  · let rfP := rf5.setPredRaw "%p0" false
    let rfD := rfP.setScalarRaw "%dst" raw
    have hrun : runCTAWithGlobalLog 12 (boundsFreePTXKernel [] 0 1).body
        (ctaAt (thAt 0 rf0) g []) [] = .ok (ctaAt (thAt 11 rfD true) g' log2, log2) := by
      have hb : (boundsFreePTXKernel [] 0 1).body =
          [ .instr none (.mov .u64 "%dst" (.immU64 0#64))
          , .instr none (.ldParam .u64 "%v0" "param_idx"), .instr none (.ldParam .u64 "%v1" "param_len")
          , .instr none (.ldParam .u64 "%addr" "param_addr"), .instr none (.ldParam .u64 "%out" "param_out") ] ++
          [ .instr none (.setp .ge .u64 "%p0" (.reg "%v0") (.reg "%v1"))
          , .instr (some { predReg := "%p0", negated := false }) (.bra "$L_done")
          , .instr none (.ldGlobal .u64 "%dst" (.regOffset "%addr" 0)), .label "$L_done"
          , .instr none (.stGlobal .u64 (.regOffset "%out" 0) (.reg "%dst")), .instr none .ret ] := by decide
      rw [hb, show (12 : Nat) = 7 + 5 from rfl, hpre 7]
      rw [hpure 6 5 _ rf5 rfP _ rfl rfl (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, rfP, hrf0,
        hcmp, execNonBarrierInstr, PTXAst.evalOperand, PTXRegFile.readScalarChecked,
        PTXRegFile.setPred, PTXRegFile.setPredRaw, PTXRegFile.setScalarRaw, PTXRegFile.setAssoc,
        List.lookup, hu64w, hu64p, hpredNe, PTXOutcome.bind])]
      rw [hmemStep 5 6 _ rfP rfP g g [] [] (some { predReg := "%p0", negated := false }) _ rfl rfl
        (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, rfP, hrf0, execPredicatedInstr,
          evalPredGuard, PTXRegFile.readPredChecked, PTXRegFile.setPredRaw,
          PTXRegFile.setScalarRaw, PTXRegFile.setAssoc, hpredNe, PTXOutcome.bind]) (Or.inl rfl)]
      rw [hmemStep 4 7 _ rfP rfD g g [] log1 none _ rfl rfl
        (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, rfP, rfD, hrf0, log1, execPredicatedInstr,
          evalPredGuard, execNonBarrierInstr, PTXAst.evalAddr, PTXRegFile.readScalarChecked,
          PTXRegFile.setScalar, PTXRegFile.setPredRaw, PTXRegFile.setScalarRaw,
          PTXRegFile.setAssoc, List.lookup, hu64w, hu64b, hu64p, hbNat, hnnB, checkAligned, halign,
          PTXAst.recordEpochAccess, PTXAst.findDataRace?, hload, PTXAst.maskForType,
          PTXOutcome.bind]) (Or.inl rfl)]
      rw [hlbl 3 8 _ rfD g log1 "$L_done" rfl]
      rw [hmemStep 2 9 _ rfD rfD g g' log1 log2 none _ rfl rfl
        (by simp [thAt, ctaAt, rf1, rf2, rf3, rf4, rf5, rfP, rfD, hrf0, log1, log2,
          execPredicatedInstr, evalPredGuard, execNonBarrierInstr, PTXAst.evalAddr,
          PTXAst.evalOperand, PTXRegFile.readScalarChecked, PTXRegFile.setPredRaw,
          PTXRegFile.setScalarRaw, PTXRegFile.setAssoc, List.lookup, hu64w, hu64b, hu64p, hoNat,
          hnnO, checkAligned, hoalign, PTXAst.recordEpochAccess, PTXAst.findDataRace?, htidNe,
          hglobEq, hstore, PTXAst.maskForType, PTXOutcome.bind]) (Or.inr (by simp [log2]))]
      rw [hret 1 10 _ _ _ _ rfl]
      simpa [ctaAt, thAt, log2, log1, hglobEq] using
        PTXSIMT.runCTAWithGlobalLog_done_halted 0 _ (ctaAt (thAt 11 rfD true) g' log2) [] rfl
    have hcta : initCTAState (boundsFreePTXKernel [] 0 1) grid grid ⟨0, 0, 0⟩ g pMem =
        ctaAt (thAt 0 rf0) g [] := by
      simp [initCTAState, buildSharedLayout, boundsFreePTXKernel, rf0, ctaAt, thAt,
        show grid.coords = [⟨0, 0, 0⟩] from rfl]
    simp [evalPTXKernel, show grid.coords = [⟨0, 0, 0⟩] from rfl, evalPTXKernelLoop, hcta, hrun,
      ctaAt, log2, log1, checkCrossCTAGlobalLog, hrace, hglobNe, PTXOutcome.bind]

theorem metalBoundsFreeLoad_sound (iv nv : Nat) (word : BitVec 64)
    (bufMem outMem outMem' : MetalAst.ByteMemory) (hiv : iv < nv) (hnv : nv < 2 ^ 64)
    (hload : bufMem.loadBits (iv * 8) 8 = some word) (hstore : outMem.storeBits 0 8 word = some outMem') :
    let grid : MetalAst.Dim3 := ⟨1, 1, 1⟩
    let devBufs : List (Nat × MetalAst.ByteMemory) := [(0, bufMem), (1, outMem)]
    let constBufs : List (Nat × MetalAst.ByteMemory) :=
      [(2, MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 iv]),
       (3, MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 nv])]
    let devOut : List (Nat × MetalAst.ByteMemory) := [(0, bufMem), (1, outMem')]
    evalMSLKernel 6 (boundsFreeMetalKernel [.idxLt 0 1] 0 1) grid grid devBufs constBufs = .ok devOut ∧
      evalMSLKernel 7 (boundsFreeMetalKernel [] 0 1) grid grid devBufs constBufs = .ok devOut := by
  intro grid devBufs constBufs devOut
  have hci : (MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 iv]).loadBits 0 8 = some (BitVec.ofNat 64 iv) := by
    simpa [MetalAst.ByteMemory.readU64Word?] using MetalSIMT.ofU64Words_readU64Word [BitVec.ofNat 64 iv] 0 (by simp)
  have hcn : (MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 nv]).loadBits 0 8 = some (BitVec.ofNat 64 nv) := by
    simpa [MetalAst.ByteMemory.readU64Word?] using MetalSIMT.ofU64Words_readU64Word [BitVec.ofNat 64 nv] 0 (by simp)
  have hivNat : (BitVec.ofNat 64 iv).toNat = iv := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hiv hnv)]
  have hlt : BitVec.ult (BitVec.ofNat 64 iv) (BitVec.ofNat 64 nv) = true := by
    simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv, Nat.mod_eq_of_lt (Nat.lt_trans hiv hnv), hiv]
  have hcoords : grid.coords = [⟨0, 0, 0⟩] := rfl
  have htidNe : (({ x := 0, y := 0, z := 0 } : MetalAst.Dim3) != { x := 0, y := 0, z := 0 }) = false := rfl
  have hrace : ∀ t a w wr at_, findCrossGroupRace? t a w wr at_ [] = none := fun _ _ _ _ _ => rfl
  refine ⟨?_, ?_⟩
  · unfold evalMSLKernel boundsFreeMetalKernel lowerBoundsFreeMetalLoad; simp only [vreg0]
    simp [factMember, hcoords, evalMSLKernelLoop, initGroupState, buildKernelBindings,
      initThreadLocals, runGroupWithDeviceLog, stepGroup, MetalAst.stepFirstReadyThread,
      threadAtBarrier, threadAtSimdOp, execNonBarrierStmt, execStmtWithCall, evalExprWithCall,
      bindEval, readBoundElement, execIndexWrite, writeDeviceBuffer, loadTypedElem, storeTypedElem,
      structFieldNames, aggregateByteWidth, MSLType.byteWidth, MetalAst.maskForType, bindValue,
      MSLLocals.empty, MSLLocals.setTyped, MSLLocals.setAssoc, MSLLocals.setTypeAssoc,
      MSLLocals.lookup?, MSLLocals.lookupType?, MSLLocals.lookupArray?, List.lookup,
      devBufs, constBufs, devOut, setIndexedMem, MetalAst.recordEpochAccess,
      MetalAst.findDataRace?, findDataRaceGo, isDeviceAccess, checkCrossGroupDeviceLog,
      hrace, List.filter, hci, hcn, hivNat, hload, hstore, htidNe]
  · unfold evalMSLKernel boundsFreeMetalKernel lowerBoundsFreeMetalLoad; simp only [vreg0]
    simp [factMember, hcoords, evalMSLKernelLoop, initGroupState, buildKernelBindings,
      initThreadLocals, runGroupWithDeviceLog, stepGroup, MetalAst.stepFirstReadyThread,
      threadAtBarrier, threadAtSimdOp, execNonBarrierStmt, execStmtWithCall, evalExprWithCall,
      bindEval, finishCmp, inferExprType, evalTypedCmp, MSLBlock.toList, readBoundElement,
      execIndexWrite, writeDeviceBuffer, loadTypedElem, storeTypedElem, structFieldNames,
      aggregateByteWidth, MSLType.byteWidth, MetalAst.maskForType, bindValue, MSLLocals.empty,
      MSLLocals.setTyped, MSLLocals.setAssoc, MSLLocals.setTypeAssoc, MSLLocals.lookup?,
      MSLLocals.lookupType?, MSLLocals.lookupArray?, List.lookup, devBufs, constBufs, devOut,
      setIndexedMem, MetalAst.recordEpochAccess, MetalAst.findDataRace?, findDataRaceGo,
      isDeviceAccess, checkCrossGroupDeviceLog, hrace, List.filter, hci, hcn, hivNat, hlt,
      hload, hstore, htidNe,
      show evalMSLCast .ulong .ulong (BitVec.ofNat 64 iv) = .ok (BitVec.ofNat 64 iv) from rfl,
      show evalMSLCast .ulong .ulong (BitVec.ofNat 64 nv) = .ok (BitVec.ofNat 64 nv) from rfl,
      show promoteMSLArithType .ulong .ulong = .ulong from rfl]

theorem proofRetention_pipeline_nonvacuous :
    let facts : FactEnv := [.exclusiveObj 0, .noOverflowAdd 1 2 true true, .disjointSlices 3 4, .idxLt 5 6]
    let st : HeapState := { buffers := [{ id := 1, exclusive := true, data := #[42] }], nextId := 2 }
    let env := (VarEnv.empty).bind 0 (.sarrayId 1)
    let rawCode : LNIRCode := .letBind 7 .i1 (.isExclusive 0) (.letBind 8 (.sarray .i64) (.sarrayEnsureExclusive 0 .i64) (.ret 8))
    let specCode := dischargeRetainedExclusivity facts rawCode
    let llvmIns := emitVerifiedLLVMWithFacts facts 1 2 [.add "s" .none .i64 (.constInt .i64 4#64) (.constInt .i64 5#64)]
    let ps := noaliasParams facts 3 4 [{ ty := .ptr 0, name := "p" }]
    specCode = .letBind 7 .i1 (.scalar (.constBool true)) (.letBind 8 (.sarray .i64) (.scalar (.var 0)) (.ret 8)) ∧
      evalCode 3 env st specCode = .ok (.sarrayId 1, st) ∧
      execInstrs {} 1 {} llvmIns = .inr (bindReg {} "s" (.bits .i64 9#64)) ∧
      bindArgs {} ps [.ptr 8#64] = some (bindReg {} "p" (.ptr 8#64)) ∧
      (lowerBoundsFreePTXLoad facts 5 6 .u64 "%d" (.regOffset "%a" 0)).length = 1 ∧
      (lowerBoundsFreeMetalLoad facts 5 6 "buf").length = 1 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  simp [emitVerifiedLLVMWithFacts, attachOverflow, overflowOf, execInstrs, execInstrsWith,
    stepInstrWith, LLVMAst.evalOperand, binResult, flagsOverflow]; decide

end LeanNative.Proofs
