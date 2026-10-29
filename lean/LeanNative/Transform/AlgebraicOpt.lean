import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Transform.Pass

namespace LeanNative.Transform

open LeanNative.IR

/-- Single-step algebraic and strength-reduction peephole rewrite on `ScalarExpr`.
    Delegates the verified core identity, strength-reduction, and binary constant-folding
    rules directly to `LeanNative.Proofs.rewriteScalarPeepholeStep` and
    `LeanNative.Proofs.rewriteConstFoldBinOp` (`rewriteScalarPeephole_sound`, `evalBinOp_const_fold_sound`),
    followed by extended div/mod/fma rules validated by `SymbolicTV`. -/
def rewriteScalarPeepholeStep (e : ScalarExpr) : ScalarExpr :=
  -- 1. Apply kernel-verified binary constant folding (`evalBinOp_const_fold_sound`)
  let e1 :=
    match e with
    | .binOp op (.constU64 a) (.constU64 b) => LeanNative.Proofs.rewriteConstFoldBinOp op a b
    | .binOp .eq (.constBool a) (.constBool b) => .constBool (a == b)
    | other => other
  -- 2. Apply kernel-verified peephole step (`rewriteScalarPeepholeStep_sound`),
  --    preserving `.fma` nodes for dedicated FMA rules below
  let e2 :=
    match e1 with
    | .fma _ _ _ => e1
    | other => LeanNative.Proofs.rewriteScalarPeepholeStep other
  -- 3. Apply extended div/mod/cancellation/FMA rules not in `Proofs.rewriteScalarPeepholeStep`
  match e2 with
  | .binOp .sub x y | .binOp .bitXor x y =>
    if x == y then .constU64 0 else e2
  | .binOp .mul _ (.constU64 0) | .binOp .mul (.constU64 0) _
  | .binOp .bitAnd _ (.constU64 0) | .binOp .bitAnd (.constU64 0) _
  | .binOp .mod _ (.constU64 1) => .constU64 0
  | .binOp .mod x (.constU64 d) =>
    if d == 2 || d == 4 || d == 8 || d == 16 || d == 32 || d == 64 then
      .binOp .bitAnd x (.constU64 (d - 1))
    else e2
  | .binOp .div x (.constU64 16) => .binOp .shr x (.constU64 4)
  | .binOp .div x (.constU64 32) => .binOp .shr x (.constU64 5)
  | .binOp .div x (.constU64 64) => .binOp .shr x (.constU64 6)
  | .binOp .mul x (.constU64 64) | .binOp .mul (.constU64 64) x => .binOp .shl x (.constU64 6)
  | .binOp .mul (.constU64 16) x => .binOp .shl x (.constU64 4)
  | .binOp .mul (.constU64 32) x => .binOp .shl x (.constU64 5)
  | .binOp .eq x y | .binOp .le x y =>
    if x == y then .constBool true else e2
  | .binOp .lt x y =>
    if x == y then .constBool false else e2
  | .unaryOp .not (.constBool b) => .constBool (!b)
  | .unaryOp .not (.unaryOp .not x) | .unaryOp .neg (.unaryOp .neg x) => x
  | .unaryOp .neg (.constU64 a) => .constU64 (0 - a)
  | .select (.constU64 c) t f =>
    if c != 0 then t else f
  | .select _ t f =>
    if t == f then t else e2
  | .fma (.constU64 a) (.constU64 b) (.constU64 c) => .constU64 (a * b + c)
  | .fma x (.constU64 1) c | .fma (.constU64 1) x c =>
    LeanNative.Proofs.rewriteScalarPeepholeStep (LeanNative.Proofs.rewriteConstFoldStep (.binOp .add x c))
  | .fma _ (.constU64 0) c | .fma (.constU64 0) _ c => c
  | .fma a b (.constU64 0) =>
    LeanNative.Proofs.rewriteScalarPeepholeStep (LeanNative.Proofs.rewriteConstFoldStep (.binOp .mul a b))
  | _ => e2

/-- Recursive bottom-up peephole optimizer on `ScalarExpr`.
    Runs `LeanNative.Proofs.rewriteScalarPeephole` for non-FMA subtrees and layers
    `rewriteScalarPeepholeStep` on top. -/
def rewriteScalarPeephole : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp op lhs rhs =>
    let lhs' := rewriteScalarPeephole lhs
    let rhs' := rewriteScalarPeephole rhs
    rewriteScalarPeepholeStep (LeanNative.Proofs.rewriteScalarPeepholeStep (.binOp op lhs' rhs'))
  | .unaryOp op arg =>
    let arg' := rewriteScalarPeephole arg
    rewriteScalarPeepholeStep (.unaryOp op arg')
  | .select c t f =>
    let c' := rewriteScalarPeephole c
    let t' := rewriteScalarPeephole t
    let f' := rewriteScalarPeephole f
    rewriteScalarPeepholeStep (LeanNative.Proofs.rewriteScalarPeepholeStep (.select c' t' f'))
  | .fma a b c =>
    let a' := rewriteScalarPeephole a
    let b' := rewriteScalarPeephole b
    let c' := rewriteScalarPeephole c
    rewriteScalarPeepholeStep (.fma a' b' c')

/-- Substitute known scalar constants from an SSA environment before peephole rewriting. -/
def substConstScalar (env : List (VarId × ScalarExpr)) : ScalarExpr → ScalarExpr
  | .var id =>
    match env.lookup id with
    | some c => c
    | none => .var id
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .binOp op l r => .binOp op (substConstScalar env l) (substConstScalar env r)
  | .unaryOp op a => .unaryOp op (substConstScalar env a)
  | .select c t f => .select (substConstScalar env c) (substConstScalar env t) (substConstScalar env f)
  | .fma a b c => .fma (substConstScalar env a) (substConstScalar env b) (substConstScalar env c)

def isScalarConst : ScalarExpr → Bool
  | .constU64 _ | .constBool _ => true
  | _ => false

/-- Optimize a `ParallelKernelKind` when it embeds a `customScalar` expression. -/
def optimizeKernelAlgebraic (env : List (VarId × ScalarExpr)) (k : ParallelKernelKind) : ParallelKernelKind :=
  match k with
  | .customScalar idxVar inVars body =>
    let env' := env.filter (fun (id, _) => id != idxVar && !(inVars.contains id))
    .customScalar idxVar inVars (rewriteScalarPeephole (substConstScalar env' body))
  | other => other

/-- Check whether `dst` clobbers any variable in `lastStore`. -/
def invalidateStoreOnRedef (dst : VarId)
    (lastStore : Option (VarId × VarId × VarId × VarId)) :
    Option (VarId × VarId × VarId × VarId) :=
  match lastStore with
  | some (origMap, newMap, slotVar, valVar) =>
    if dst == origMap || dst == newMap || dst == slotVar || dst == valVar then
      none
    else
      lastStore
  | none => none

/-- Recursively apply algebraic strength reduction, identity folding, constant propagation,
    constant branch (`ite`) elimination, and same-block EVM `storageStore` -> `storageLoad`
    forwarding (`storageStore_load_same_sound`) across `LNIRCode`. -/
def optimizeCodeAlgebraicAux
    (env : List (VarId × ScalarExpr))
    (lastStore : Option (VarId × VarId × VarId × VarId))
    (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty (.scalar e) k =>
    let e' := rewriteScalarPeephole (substConstScalar env e)
    let env' :=
      if isScalarConst e' then
        (dst, e') :: env.filter (fun (id, _) => id != dst)
      else
        env.filter (fun (id, _) => id != dst)
    let store' := invalidateStoreOnRedef dst lastStore
    .letBind dst ty (.scalar e') (optimizeCodeAlgebraicAux env' store' k)
  | .letBind dst ty (.storageStore mapVar slotVar valVar) k =>
    let env' := env.filter (fun (id, _) => id != dst)
    let store' :=
      if dst == mapVar || dst == slotVar || dst == valVar then
        none
      else
        some (mapVar, dst, slotVar, valVar)
    .letBind dst ty (.storageStore mapVar slotVar valVar)
      (optimizeCodeAlgebraicAux env' store' k)
  | .letBind dst ty (.storageLoad mapVar slotVar) k =>
    let env' := env.filter (fun (id, _) => id != dst)
    let store' := invalidateStoreOnRedef dst lastStore
    match lastStore with
    | some (origMap, newMap, sSlot, sVal) =>
      if (mapVar == origMap || mapVar == newMap) && slotVar == sSlot then
        let e' := rewriteScalarPeephole (substConstScalar env (.var sVal))
        let envFwd :=
          if isScalarConst e' then
            (dst, e') :: env'
          else
            env'
        .letBind dst ty (.scalar e') (optimizeCodeAlgebraicAux envFwd store' k)
      else
        .letBind dst ty (.storageLoad mapVar slotVar) (optimizeCodeAlgebraicAux env' store' k)
    | none =>
      .letBind dst ty (.storageLoad mapVar slotVar) (optimizeCodeAlgebraicAux env' store' k)
  | .letBind dst ty (.call fnName args retTy isExtern) k =>
    let env' := env.filter (fun (id, _) => id != dst)
    .letBind dst ty (.call fnName args retTy isExtern)
      (optimizeCodeAlgebraicAux env' none k)
  | .letBind dst ty val k =>
    let env' := env.filter (fun (id, _) => id != dst)
    let store' := invalidateStoreOnRedef dst lastStore
    .letBind dst ty val (optimizeCodeAlgebraicAux env' store' k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore ptrVar idxVar valVar elemTy (optimizeCodeAlgebraicAux env lastStore k)
  | .incRef objVar count k =>
    .incRef objVar count (optimizeCodeAlgebraicAux env lastStore k)
  | .decRef objVar count k =>
    .decRef objVar count (optimizeCodeAlgebraicAux env lastStore k)
  | .ite condVar thenBranch elseBranch =>
    match env.lookup condVar with
    | some (.constBool true) => optimizeCodeAlgebraicAux env lastStore thenBranch
    | some (.constBool false) => optimizeCodeAlgebraicAux env lastStore elseBranch
    | some (.constU64 v) =>
      if v != 0 then optimizeCodeAlgebraicAux env lastStore thenBranch
      else optimizeCodeAlgebraicAux env lastStore elseBranch
    | _ =>
      .ite condVar (optimizeCodeAlgebraicAux env none thenBranch) (optimizeCodeAlgebraicAux env none elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    let stepEnv := env.filter (fun (id, _) => id != idxVar && id != accVar)
    let stepBody' := optimizeCodeAlgebraicAux stepEnv none stepBody
    let kEnv := env.filter (fun (id, _) => id != accVar)
    .seqFor idxVar loVar hiVar accVar accInit accTy stepBody' (optimizeCodeAlgebraicAux kEnv none k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let kernel' := optimizeKernelAlgebraic env kernel
    let kEnv := env.filter (fun (id, _) => id != outVar)
    .parFor outVar lenVar inputs elemTy kernel' (optimizeCodeAlgebraicAux kEnv none k)
  | .ret v => .ret v
  | .unreachable => .unreachable

def optimizeCodeAlgebraic (env : List (VarId × ScalarExpr)) (code : LNIRCode) : LNIRCode :=
  optimizeCodeAlgebraicAux env none code

/-- Machine-checked verification contract (`Contract V2`) for the kernel-proven
    algebraic peephole & binary constant-folding pass (`LeanNative.Proofs.rewriteCodeVerified`). -/
def verifiedAlgebraicPeepholeContract : VerifiedCodePassContract where
  name       := "AlgebraicOpt"
  theoremRef := "LeanNative.Proofs.PeepholeProofs.rewriteScalarPeephole_sound"
  notes      := "Strength reduction (*2^k -> <<<k, /2^k -> >>>k, %2^k -> &&&(2^k-1)), identity folding, constant branch elimination, and EVM SSTORE->SLOAD forwarding (storageStore_load_same_sound)"
  runCode    := LeanNative.Proofs.rewriteCodeVerified
  sound      := LeanNative.Proofs.rewriteCodeVerified_refines

/-- Pure kernel-verified algebraic pass constructed directly from `verifiedAlgebraicPeepholeContract`. -/
def verifiedAlgebraicCorePass : TransformPass :=
  TransformPass.ofVerifiedContract verifiedAlgebraicPeepholeContract

/-- Machine-checked theorem: `verifiedAlgebraicCorePass` refines the body of every declaration. -/
theorem verifiedAlgebraicCorePass_refines (d : LNIRDecl) :
    LeanNative.Semantics.CodeRefines d.body (verifiedAlgebraicCorePass.runDecl d).1.body :=
  TransformPass.ofVerifiedContract_body_refines verifiedAlgebraicPeepholeContract d

/-- Verified Algebraic Optimization & Strength Reduction Pass (`AlgebraicOpt`).
    Wired through `TransformPass.ofHybridVerifiedContract verifiedAlgebraicPeepholeContract` (`Contract V2`):
    - Rewrites matching `rewriteCodeVerified` are unconditionally kernel-proven (`rewriteCodeVerified_refines`).
    - Extended rewrites in `optimizeCodeAlgebraic` are gated by `SymbolicTV.validateTranslationDecl`
      with automatic fallback to `rewriteCodeVerified` if TV ever rejects. -/
def algebraicOptPass : TransformPass :=
  TransformPass.ofHybridVerifiedContract
    verifiedAlgebraicPeepholeContract
    (fun d => (optimizeCodeAlgebraic [] d.body, none))

/-- Run algebraic optimization on an `LNIRDecl` via the verified contract gate. -/
def algebraicOptDecl (d : LNIRDecl) : LNIRDecl :=
  (algebraicOptPass.runDecl d).1

end LeanNative.Transform
