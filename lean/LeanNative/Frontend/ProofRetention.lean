import Lean.Compiler.LCNF.Basic
import LeanNative.IR.AST
import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.PTXAst.Syntax
import LeanNative.Backend.MetalAst.Syntax

/-!
# D1 proof-carrying LCNF (`LeanNative.Frontend.ProofRetention`)

Facts retained from pre-erasure `Lean.Compiler.LCNF.Code .pure` before `.mono` proof erasure,
and the verified specializations they justify on `LNIRCode`, `LLVMAst`, `PTXAst`, and `MetalAst`.
-/

namespace LeanNative.Frontend.ProofRetention

open LeanNative.IR
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst

set_option autoImplicit false

/-- A `Prop` witness that survived until the pure LCNF phase. -/
inductive RetainedFact where
  | idxLt (idxVar lenVar : VarId)
  | noOverflowAdd (lhs rhs : VarId) (nsw nuw : Bool)
  | noOverflowMul (lhs rhs : VarId) (nsw nuw : Bool)
  | alignedPtr (ptrVar : VarId) (alignBytes : Nat)
  | disjointSlices (ptrA ptrB : VarId)
  | exclusiveObj (objVar : VarId)
  deriving Repr, DecidableEq, Inhabited, BEq

abbrev FactEnv := List RetainedFact

def factMember (facts : FactEnv) (f : RetainedFact) : Bool :=
  facts.contains f

def consFact (facts : FactEnv) (f : RetainedFact) : FactEnv :=
  if factMember facts f then facts else f :: facts

/-- Mapping from LCNF `FVarId`s to LNIR `VarId`s threaded during pure-phase fact extraction. -/
structure RetentionState where
  fvarMap : List (Lean.FVarId × VarId) := []
  nextVar : VarId := 0
  facts : FactEnv := []
  deriving Inhabited

def internFVar (st : RetentionState) (fv : Lean.FVarId) : VarId × RetentionState :=
  match st.fvarMap.find? (fun p => p.1 == fv) with
  | some (_, vid) => (vid, st)
  | none =>
    let vid := st.nextVar
    (vid, { st with fvarMap := (fv, vid) :: st.fvarMap, nextVar := vid + 1 })

def internParams (st : RetentionState)
    (ps : List (Lean.Compiler.LCNF.Param .pure)) : RetentionState :=
  match ps with
  | [] => st
  | p :: rest =>
    let (_, st1) := internFVar st p.fvarId
    internParams st1 rest

def pushFactOpt (st : RetentionState) (opt : Option RetainedFact) : RetentionState :=
  match opt with
  | some f => { st with facts := consFact st.facts f }
  | none => st

def fvarsOfArgs (args : List (Lean.Compiler.LCNF.Arg .pure)) : List Lean.FVarId :=
  match args with
  | [] => []
  | .fvar x :: rest => x :: fvarsOfArgs rest
  | .erased :: rest => fvarsOfArgs rest
  | .type _ :: rest => fvarsOfArgs rest

def internFVarList (st : RetentionState) (fvs : List Lean.FVarId) :
    List VarId × RetentionState :=
  match fvs with
  | [] => ([], st)
  | fv :: rest =>
    let (v, st1) := internFVar st fv
    let (vs, st2) := internFVarList st1 rest
    (v :: vs, st2)

def nameIs (n : Lean.Name) (tail : String) : Bool :=
  n.toString.endsWith tail

def nameIn (n : Lean.Name) (tails : List String) : Bool :=
  tails.any (nameIs n)

def nameIsLt (n : Lean.Name) : Bool :=
  nameIn n ["decLt", "blt", "Nat.lt", "Nat.ble", "USize.lt", "Fin.mk"]

def nameIsAdd (n : Lean.Name) : Bool :=
  nameIn n [".add", "Nat.add", "HAdd.hAdd"]

def nameIsMul (n : Lean.Name) : Bool :=
  nameIn n [".mul", "Nat.mul", "HMul.hMul"]

def nameIsGet (n : Lean.Name) : Bool :=
  nameIn n ["Array.getInternal", "Array.get", "Array.uget", "GetElem.getElem"]

def nameIsIsExclusive (n : Lean.Name) : Bool :=
  nameIn n ["lean_is_exclusive", "isExclusive", "isExclusiveUnsafe"]

def nameIsEnsureExclusive (n : Lean.Name) : Bool :=
  nameIn n ["lean_sarray_ensure_exclusive", "sarrayEnsureExclusive"]

def alignOfName (n : Lean.Name) : Nat :=
  if nameIn n ["align8", "Align8", "aligned8"] then 8
  else if nameIn n ["align4", "Align4", "aligned4"] then 4
  else if nameIn n ["align2", "Align2", "aligned2"] then 2
  else if nameIn n ["align", "Align", "aligned"] then 1
  else 0

def nameIsDisjoint (n : Lean.Name) : Bool :=
  nameIn n ["disjoint", "Disjoint", "noalias", "NoAlias"]

def factOfConstVars (fnName : Lean.Name) (vids : List VarId)
    (dst : VarId) : Option RetainedFact :=
  match vids with
  | ia :: ib :: _ =>
    if nameIsLt fnName then some (.idxLt ia ib)
    else if nameIsAdd fnName then some (.noOverflowAdd ia ib true true)
    else if nameIsMul fnName then some (.noOverflowMul ia ib true true)
    else if nameIsGet fnName then some (.idxLt ib ia)
    else if nameIsDisjoint fnName then some (.disjointSlices ia ib)
    else
      let al := alignOfName fnName
      if al != 0 then some (.alignedPtr ia al) else none
  | [ia] =>
    let al := alignOfName fnName
    if nameIsIsExclusive fnName then some (.exclusiveObj ia)
    else if nameIsEnsureExclusive fnName then some (.exclusiveObj dst)
    else if al != 0 then some (.alignedPtr ia al)
    else none
  | [] => none

def extractLetFact (st : RetentionState) (lv : Lean.Compiler.LCNF.LetValue .pure)
    (dst : VarId) : RetentionState :=
  match lv with
  | .const fnName _ args _ =>
    let (vids, st1) := internFVarList st (fvarsOfArgs args.toList)
    pushFactOpt st1 (factOfConstVars fnName vids dst)
  | _ => st

def collectPureStep (fuel : Nat) (st : RetentionState)
    (work : Lean.Compiler.LCNF.Code .pure ⊕ List (Lean.Compiler.LCNF.Alt .pure)) :
    RetentionState :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    match work with
    | .inl (.let decl k) =>
      let (dst, st1) := internFVar st decl.fvarId
      let st2 := extractLetFact st1 decl.value dst
      collectPureStep fuel st2 (.inl k)
    | .inl (.fun decl k _) =>
      let st1 := internParams st decl.params.toList
      let st2 := collectPureStep fuel st1 (.inl decl.value)
      collectPureStep fuel st2 (.inl k)
    | .inl (.jp decl k) =>
      let st1 := internParams st decl.params.toList
      let st2 := collectPureStep fuel st1 (.inl decl.value)
      collectPureStep fuel st2 (.inl k)
    | .inl (.cases c) =>
      let (_, st1) := internFVar st c.discr
      collectPureStep fuel st1 (.inr c.alts.toList)
    | .inl (.return fv) => (internFVar st fv).2
    | .inl (.jmp fv args) =>
      let (_, st1) := internFVar st fv
      (internFVarList st1 (fvarsOfArgs args.toList)).2
    | .inl (.unreach _) => st
    | .inr [] => st
    | .inr (alt :: rest) =>
      let st1 := internParams st alt.getParams.toList
      let st2 := collectPureStep fuel st1 (.inl alt.getCode)
      collectPureStep fuel st2 (.inr rest)

def retainedPureFactsWithParams (fuel : Nat)
    (params : List (Lean.Compiler.LCNF.Param .pure))
    (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  let st0 := internParams {} params
  (collectPureStep fuel st0 (.inl code)).facts

def retainedPureFacts (fuel : Nat) (code : Lean.Compiler.LCNF.Code .pure) : FactEnv :=
  (collectPureStep fuel {} (.inl code)).facts

/-- Replace a retained `lean_is_exclusive` test by `true`. Sound for states in which
every `.exclusiveObj` fact in `facts` holds; `sarrayEnsureExclusive` is preserved
because it is the operation that establishes exclusivity. -/
def dischargeRetainedExclusivity (facts : FactEnv) (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty val k =>
    let k' := dischargeRetainedExclusivity facts k
    match val with
    | .isExclusive objVar =>
      if factMember facts (.exclusiveObj objVar) then
        .letBind dst ty (.scalar (.constBool true)) k'
      else .letBind dst ty val k'
    | _ => .letBind dst ty val k'
  | .rawStore p i v ty k =>
    .rawStore p i v ty (dischargeRetainedExclusivity facts k)
  | .incRef v n k => .incRef v n (dischargeRetainedExclusivity facts k)
  | .decRef v n k => .decRef v n (dischargeRetainedExclusivity facts k)
  | .ite c t e =>
    .ite c (dischargeRetainedExclusivity facts t) (dischargeRetainedExclusivity facts e)
  | .seqFor idx lo hi acc init ty body k =>
    .seqFor idx lo hi acc init ty
      (dischargeRetainedExclusivity facts body) (dischargeRetainedExclusivity facts k)
  | .parFor out len ins ty ker k =>
    .parFor out len ins ty ker (dischargeRetainedExclusivity facts k)
  | .ret v => .ret v
  | .unreachable => .unreachable

def overflowOf (facts : FactEnv) (isMul : Bool) (a b : VarId) : OverflowFlags :=
  let hit := facts.any fun f =>
    match f with
    | .noOverflowAdd l r nsw nuw => !isMul && l == a && r == b && (nsw || nuw)
    | .noOverflowMul l r nsw nuw => isMul && l == a && r == b && (nsw || nuw)
    | _ => false
  let nsw := facts.any fun f =>
    match f with
    | .noOverflowAdd l r nsw _ => !isMul && l == a && r == b && nsw
    | .noOverflowMul l r nsw _ => isMul && l == a && r == b && nsw
    | _ => false
  let nuw := facts.any fun f =>
    match f with
    | .noOverflowAdd l r _ nuw => !isMul && l == a && r == b && nuw
    | .noOverflowMul l r _ nuw => isMul && l == a && r == b && nuw
    | _ => false
  if !hit then .none else if nsw && nuw then .nswNuw else if nsw then .nsw else .nuw

def subOverflowOf (facts : FactEnv) (a b : VarId) : OverflowFlags :=
  if factMember facts (.idxLt b a) then .nuw else .none

def attachOverflow (facts : FactEnv) (a b : VarId) (ins : LLVMInstr) : LLVMInstr :=
  match ins with
  | .add dst _ w x y => .add dst (overflowOf facts false a b) w x y
  | .sub dst _ w x y => .sub dst (subOverflowOf facts a b) w x y
  | .mul dst _ w x y => .mul dst (overflowOf facts true a b) w x y
  | other => other

def emitVerifiedLLVMWithFacts (facts : FactEnv) (a b : VarId)
    (insns : List LLVMInstr) : List LLVMInstr :=
  match insns with
  | [] => []
  | ins :: rest =>
    attachOverflow facts a b ins :: emitVerifiedLLVMWithFacts facts a b rest

def withNoAlias (disjoint : Bool) (p : LLVMParam) : LLVMParam :=
  if !disjoint then p
  else if p.attrs.contains .noalias then p
  else { p with attrs := .noalias :: p.attrs }

def noaliasParams (facts : FactEnv) (ptrA ptrB : VarId) (ps : List LLVMParam) : List LLVMParam :=
  if !factMember facts (.disjointSlices ptrA ptrB) then ps
  else ps.map (withNoAlias true)

def emitVerifiedLLVMFnWithFacts (facts : FactEnv) (ptrA ptrB a b : VarId)
    (fn : LLVMFn) : LLVMFn :=
  { fn with
    params := noaliasParams facts ptrA ptrB fn.params
    blocks := fn.blocks.map fun blk =>
      { blk with body := emitVerifiedLLVMWithFacts facts a b blk.body } }

/-- A bounds check stays unless `idxLt` was retained. The unchecked form is sound
for states in which `idxLt` holds. -/
def lowerBoundsFreePTXLoad (facts : FactEnv) (idxVar lenVar : VarId) (ty : PTXType)
    (dst : String) (addr : PTXAddr) : List PTXStmt :=
  if factMember facts (.idxLt idxVar lenVar) then
    [.instr none (.ldGlobal ty dst addr)]
  else
    [ .instr none (.setp .ge .u64 "%p0" (.reg s!"%v{idxVar}") (.reg s!"%v{lenVar}"))
    , .instr (some { predReg := "%p0", negated := false }) (.bra "$L_done")
    , .instr none (.ldGlobal ty dst addr)
    , .label "$L_done" ]

def lowerBoundsFreeMetalLoad (facts : FactEnv) (idxVar lenVar : VarId)
    (buf : String) : List MSLStmt :=
  let idx := MSLExpr.var s!"v{idxVar}"
  let len := MSLExpr.var s!"v{lenVar}"
  let load := MSLStmt.assign "loaded" (.index buf idx)
  if factMember facts (.idxLt idxVar lenVar) then [load]
  else [.ifElse (.lt idx len) (.cons load .nil) .nil]

end LeanNative.Frontend.ProofRetention
