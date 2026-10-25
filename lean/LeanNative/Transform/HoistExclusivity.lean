import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Transform.Pass

namespace LeanNative.Transform

open LeanNative.IR

/-- Compute the maximum `VarId` referenced in a `ScalarExpr`. -/
def maxVarScalar : ScalarExpr → VarId
  | .constU64 _ | .constBool _ => 0
  | .var id => id
  | .binOp _ l r => Nat.max (maxVarScalar l) (maxVarScalar r)
  | .unaryOp _ a => maxVarScalar a
  | .select c t f => Nat.max (maxVarScalar c) (Nat.max (maxVarScalar t) (maxVarScalar f))
  | .fma a b c => Nat.max (maxVarScalar a) (Nat.max (maxVarScalar b) (maxVarScalar c))

/-- Compute the maximum `VarId` referenced in an `LNIRExpr`. -/
def maxVarExpr : LNIRExpr → VarId
  | .scalar e => maxVarScalar e
  | .constU256 _ => 0
  | .mulDivDown a b d => Nat.max a (Nat.max b d)
  | .mulDivUp a b d => Nat.max a (Nat.max b d)
  | .storageLoad m s => Nat.max m s
  | .storageStore m s v => Nat.max m (Nat.max s v)
  | .mkTuple fs => fs.foldl Nat.max 0
  | .projTuple v _ => v
  | .allocCtor _ os ss => Nat.max (os.foldl Nat.max 0) (ss.foldl Nat.max 0)
  | .ctorGetObj v _ => v
  | .ctorGetScalar v _ _ => v
  | .isExclusive v => v
  | .sarrayLen v => v
  | .sarrayDataPtr v _ => v
  | .sarrayEnsureExclusive v _ => v
  | .sarrayGet a i _ => Nat.max a i
  | .sarraySet a i v _ => Nat.max a (Nat.max i v)
  | .rawLoad p i _ => Nat.max p i
  | .boxScalar v _ => v
  | .unboxScalar v _ => v
  | .call _ args _ _ => args.foldl Nat.max 0

/-- Compute the maximum `VarId` referenced or bound in an `LNIRCode` block. -/
def maxVarCode : LNIRCode → VarId
  | .letBind dst _ val k => Nat.max dst (Nat.max (maxVarExpr val) (maxVarCode k))
  | .rawStore p i v _ k => Nat.max p (Nat.max i (Nat.max v (maxVarCode k)))
  | .incRef v _ k => Nat.max v (maxVarCode k)
  | .decRef v _ k => Nat.max v (maxVarCode k)
  | .ite c t e => Nat.max c (Nat.max (maxVarCode t) (maxVarCode e))
  | .seqFor idx lo hi acc init _ body k =>
    let m1 := Nat.max idx (Nat.max lo (Nat.max hi (Nat.max acc init)))
    Nat.max m1 (Nat.max (maxVarCode body) (maxVarCode k))
  | .parFor out len ins _ _ k =>
    Nat.max out (Nat.max len (Nat.max (ins.foldl Nat.max 0) (maxVarCode k)))
  | .ret v => v
  | .unreachable => 0

/-- Compute the maximum `VarId` in an `LNIRDecl`. -/
def maxVarDecl (d : LNIRDecl) : VarId :=
  let paramMax := d.params.foldl (fun acc p => Nat.max acc p.id) 0
  Nat.max paramMax (maxVarCode d.body)

/-- Information about a candidate scalar array inside a loop body. -/
structure LoopArrayCandidate where
  targetArr : VarId
  elemTy    : LNIRType
  deriving Repr, Inhabited, BEq

/-- Detect if `stepBody` performs `sarrayEnsureExclusive` or `sarraySet` on `accVar` or a loop-invariant array. -/
def findLoopArrayCandidate (aliases : List VarId) : LNIRCode → Option LoopArrayCandidate
  | .letBind dst _ (.sarrayEnsureExclusive arr elemTy) k =>
    if aliases.contains arr then
      some { targetArr := arr, elemTy := elemTy }
    else
      match findLoopArrayCandidate (dst :: aliases) k with
      | some c => some c
      | none => some { targetArr := arr, elemTy := elemTy }
  | .letBind dst _ (.sarraySet arr _ _ elemTy) k =>
    if aliases.contains arr then
      some { targetArr := arr, elemTy := elemTy }
    else
      match findLoopArrayCandidate (dst :: aliases) k with
      | some c => some c
      | none => some { targetArr := arr, elemTy := elemTy }
  | .letBind _ _ _ k => findLoopArrayCandidate aliases k
  | .rawStore _ _ _ _ k => findLoopArrayCandidate aliases k
  | .incRef _ _ k => findLoopArrayCandidate aliases k
  | .decRef _ _ k => findLoopArrayCandidate aliases k
  | .ite _ t e =>
    match findLoopArrayCandidate aliases t with
    | some c => some c
    | none => findLoopArrayCandidate aliases e
  | _ => none

/-- Check that none of the tracked array aliases escape via unknown function call, tuple packing,
    heap constructor, or reference-count increment (`incRef`) in `stepBody`. -/
def arrayAliasesNonEscaping (aliases : List VarId) : LNIRCode → Bool
  | .letBind dst _ (.sarrayEnsureExclusive arr _) k =>
    let aliases' := if aliases.contains arr then dst :: aliases else aliases
    arrayAliasesNonEscaping aliases' k
  | .letBind dst _ (.sarraySet arr _ val _) k =>
    if aliases.contains val then false
    else
      let aliases' := if aliases.contains arr then dst :: aliases else aliases
      arrayAliasesNonEscaping aliases' k
  | .letBind _ _ (.mkTuple fs) k =>
    if fs.any aliases.contains then false
    else arrayAliasesNonEscaping aliases k
  | .letBind _ _ (.allocCtor _ os ss) k =>
    if os.any aliases.contains || ss.any aliases.contains then false
    else arrayAliasesNonEscaping aliases k
  | .letBind _ _ (.call _ args _ _) k =>
    if args.any aliases.contains then false
    else arrayAliasesNonEscaping aliases k
  | .letBind _ _ _ k => arrayAliasesNonEscaping aliases k
  | .rawStore _ _ val _ k =>
    if aliases.contains val then false else arrayAliasesNonEscaping aliases k
  | .incRef objVar _ k =>
    if aliases.contains objVar then false else arrayAliasesNonEscaping aliases k
  | .decRef _ _ k => arrayAliasesNonEscaping aliases k
  | .ite _ t e => arrayAliasesNonEscaping aliases t && arrayAliasesNonEscaping aliases e
  | .seqFor _ _ _ _ _ _ body k =>
    arrayAliasesNonEscaping aliases body && arrayAliasesNonEscaping aliases k
  | .parFor _ _ _ _ _ k => arrayAliasesNonEscaping aliases k
  | .ret _ | .unreachable => true

/-- Substitute variable aliases inside `ScalarExpr`. -/
def substVarScalar (varMap : List (VarId × VarId)) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var ((varMap.lookup id).getD id)
  | .binOp op l r => .binOp op (substVarScalar varMap l) (substVarScalar varMap r)
  | .unaryOp op a => .unaryOp op (substVarScalar varMap a)
  | .select c t f => .select (substVarScalar varMap c) (substVarScalar varMap t) (substVarScalar varMap f)
  | .fma a b c => .fma (substVarScalar varMap a) (substVarScalar varMap b) (substVarScalar varMap c)

/-- Rewrite a loop body after hoisting `sarrayEnsureExclusive` and `sarrayDataPtr` (`rawPtrVar`).
    Replaces inside-loop `sarrayEnsureExclusive` with alias forwarding, `sarrayGet` with `rawLoad`,
    and `sarraySet` with `rawStore`. -/
def rewriteLoopBodyForHoistedArray
    (canonicalArrVar : VarId)
    (rawPtrVar : VarId)
    (arrAliases : List VarId)
    (varMap : List (VarId × VarId))
    (code : LNIRCode) : LNIRCode :=
  let resolve (v : VarId) : VarId := (varMap.lookup v).getD v
  match code with
  | .letBind dst ty (.sarrayEnsureExclusive arrVar _) k =>
    let arrVar' := resolve arrVar
    if arrAliases.contains arrVar || arrAliases.contains arrVar' then
      let arrAliases' := dst :: arrAliases
      let varMap' := (dst, canonicalArrVar) :: varMap
      rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases' varMap' k
    else
      .letBind dst ty (.sarrayEnsureExclusive arrVar' ty)
        (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.sarrayDataPtr arrVar elemTy) k =>
    let arrVar' := resolve arrVar
    if arrAliases.contains arrVar || arrAliases.contains arrVar' then
      let varMap' := (dst, rawPtrVar) :: varMap
      rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap' k
    else
      .letBind dst ty (.sarrayDataPtr arrVar' elemTy)
        (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.sarrayGet arrVar idxVar elemTy) k =>
    let arrVar' := resolve arrVar
    let idxVar' := resolve idxVar
    if arrAliases.contains arrVar || arrAliases.contains arrVar' then
      .letBind dst ty (.rawLoad rawPtrVar idxVar' elemTy)
        (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
    else
      .letBind dst ty (.sarrayGet arrVar' idxVar' elemTy)
        (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst _ (.sarraySet arrVar idxVar valVar elemTy) k =>
    let arrVar' := resolve arrVar
    let idxVar' := resolve idxVar
    let valVar' := resolve valVar
    if arrAliases.contains arrVar || arrAliases.contains arrVar' then
      let arrAliases' := dst :: arrAliases
      let varMap' := (dst, canonicalArrVar) :: varMap
      .rawStore rawPtrVar idxVar' valVar' elemTy
        (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases' varMap' k)
    else
      .letBind dst (.sarray elemTy) (.sarraySet arrVar' idxVar' valVar' elemTy)
        (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.scalar e) k =>
    .letBind dst ty (.scalar (substVarScalar varMap e))
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.mulDivDown a b d) k =>
    .letBind dst ty (.mulDivDown (resolve a) (resolve b) (resolve d))
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.mulDivUp a b d) k =>
    .letBind dst ty (.mulDivUp (resolve a) (resolve b) (resolve d))
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.storageLoad m s) k =>
    .letBind dst ty (.storageLoad (resolve m) (resolve s))
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.storageStore m s v) k =>
    .letBind dst ty (.storageStore (resolve m) (resolve s) (resolve v))
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty (.rawLoad ptrVar idxVar elemTy) k =>
    .letBind dst ty (.rawLoad (resolve ptrVar) (resolve idxVar) elemTy)
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .letBind dst ty val k =>
    .letBind dst ty val
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore (resolve ptrVar) (resolve idxVar) (resolve valVar) elemTy
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .incRef objVar count k =>
    .incRef (resolve objVar) count
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .decRef objVar count k =>
    .decRef (resolve objVar) count
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .ite condVar thenBranch elseBranch =>
    .ite (resolve condVar)
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap thenBranch)
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    .seqFor idxVar (resolve loVar) (resolve hiVar) accVar (resolve accInit) accTy
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap stepBody)
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    .parFor outVar (resolve lenVar) (inputs.map resolve) elemTy kernel
      (rewriteLoopBodyForHoistedArray canonicalArrVar rawPtrVar arrAliases varMap k)
  | .ret v => .ret (resolve v)
  | .unreachable => .unreachable

/-- Recursively hoist `sarrayEnsureExclusive` and `sarrayDataPtr` out of `seqFor` loops.
    Backed by `LeanNative.Proofs.LoopOptProofs.hoistExclusivity_sound`. -/
def hoistExclusivityCode (nextFree : VarId) (code : LNIRCode) : LNIRCode × VarId :=
  match code with
  | .letBind dst ty val k =>
    let (k', nextFree') := hoistExclusivityCode nextFree k
    (.letBind dst ty val k', nextFree')
  | .rawStore ptrVar idxVar valVar elemTy k =>
    let (k', nextFree') := hoistExclusivityCode nextFree k
    (.rawStore ptrVar idxVar valVar elemTy k', nextFree')
  | .incRef objVar count k =>
    let (k', nextFree') := hoistExclusivityCode nextFree k
    (.incRef objVar count k', nextFree')
  | .decRef objVar count k =>
    let (k', nextFree') := hoistExclusivityCode nextFree k
    (.decRef objVar count k', nextFree')
  | .ite condVar thenBranch elseBranch =>
    let (t', nf1) := hoistExclusivityCode nextFree thenBranch
    let (e', nf2) := hoistExclusivityCode nf1 elseBranch
    (.ite condVar t' e', nf2)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    let (stepBodySub, nf1) := hoistExclusivityCode nextFree stepBody
    let (k', nf2) := hoistExclusivityCode nf1 k
    let initAliases := [accVar, accInit]
    match findLoopArrayCandidate initAliases stepBodySub with
    | some cand =>
      let tracked := [cand.targetArr, accVar, accInit]
      if arrayAliasesNonEscaping tracked stepBodySub then
        let exclArrVar := nf2 + 1
        let rawPtrVar := nf2 + 2
        let nf3 := nf2 + 2
        let isAccArray := cand.targetArr == accVar || cand.targetArr == accInit
        let baseArr := if isAccArray then accInit else cand.targetArr
        let canonicalLoopArr := if isAccArray then accVar else exclArrVar
        let newAccInit := if isAccArray then exclArrVar else accInit
        let rewrittenBody :=
          rewriteLoopBodyForHoistedArray canonicalLoopArr rawPtrVar tracked [] stepBodySub
        let hoistedLoop : LNIRCode :=
          .letBind exclArrVar (.sarray cand.elemTy) (.sarrayEnsureExclusive baseArr cand.elemTy)
            (.letBind rawPtrVar (.rawPtr cand.elemTy) (.sarrayDataPtr exclArrVar cand.elemTy)
              (.seqFor idxVar loVar hiVar accVar newAccInit accTy rewrittenBody k'))
        (hoistedLoop, nf3)
      else
        (.seqFor idxVar loVar hiVar accVar accInit accTy stepBodySub k', nf2)
    | none =>
      (.seqFor idxVar loVar hiVar accVar accInit accTy stepBodySub k', nf2)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let (k', nf1) := hoistExclusivityCode nextFree k
    (.parFor outVar lenVar inputs elemTy kernel k', nf1)
  | .ret v => (.ret v, nextFree)
  | .unreachable => (.unreachable, nextFree)

/-- Run Loop Exclusivity & Data Pointer Hoisting on an `LNIRDecl`. -/
def hoistExclusivityDecl (d : LNIRDecl) : LNIRDecl :=
  let startId := maxVarDecl d + 100
  let (body', _) := hoistExclusivityCode startId d.body
  { d with body := body' }

/-- Verified Loop Exclusivity Hoisting Pass (`HoistExclusivity`). -/
def hoistExclusivityPass : TransformPass :=
  TransformPass.ofCodeTransform
    "HoistExclusivity"
    .verifiedKernelProof
    "LeanNative.Proofs.LoopOptProofs.hoistExclusivity_sound"
    "Hoists sarrayEnsureExclusive and sarrayDataPtr before seqFor loops and rewrites inside-loop sarrayGet/sarraySet to rawLoad/rawStore"
    (fun d =>
      let startId := maxVarDecl d + 100
      let (body', _) := hoistExclusivityCode startId d.body
      (body', none))

end LeanNative.Transform
