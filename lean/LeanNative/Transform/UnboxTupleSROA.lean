import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Transform.Pass

namespace LeanNative.Transform

open LeanNative.IR

/-- Check whether `target` variable occurs in a `ScalarExpr`. -/
def scalarExprUsesVar (target : VarId) : ScalarExpr → Bool
  | .constU64 _ | .constBool _ => false
  | .var id => id == target
  | .binOp _ l r => scalarExprUsesVar target l || scalarExprUsesVar target r
  | .unaryOp _ a => scalarExprUsesVar target a
  | .select c t f =>
    scalarExprUsesVar target c || scalarExprUsesVar target t || scalarExprUsesVar target f
  | .fma a b c =>
    scalarExprUsesVar target a || scalarExprUsesVar target b || scalarExprUsesVar target c

/-- Check whether `target` variable occurs in a `ParallelKernelKind`. -/
def kernelUsesVar (target : VarId) : ParallelKernelKind → Bool
  | .customScalar idxVar inVars body =>
    inVars.contains target || (idxVar != target && scalarExprUsesVar target body)
  | _ => false

/-- Check whether `target` variable occurs in an `LNIRExpr`. -/
def exprUsesVar (target : VarId) : LNIRExpr → Bool
  | .scalar e => scalarExprUsesVar target e
  | .constU256 _ => false
  | .mulDivDown aVar bVar denomVar =>
    aVar == target || bVar == target || denomVar == target
  | .mulDivUp aVar bVar denomVar =>
    aVar == target || bVar == target || denomVar == target
  | .storageLoad mapVar slotVar =>
    mapVar == target || slotVar == target
  | .storageStore mapVar slotVar valVar =>
    mapVar == target || slotVar == target || valVar == target
  | .mkTuple fields => fields.contains target
  | .projTuple tupleVar _ => tupleVar == target
  | .allocCtor _ objFields scalarFields =>
    objFields.contains target || scalarFields.contains target
  | .ctorGetObj ctorVar _ => ctorVar == target
  | .ctorGetScalar ctorVar _ _ => ctorVar == target
  | .isExclusive objVar => objVar == target
  | .sarrayLen arrVar => arrVar == target
  | .sarrayDataPtr arrVar _ => arrVar == target
  | .sarrayEnsureExclusive arrVar _ => arrVar == target
  | .sarrayGet arrVar idxVar _ => arrVar == target || idxVar == target
  | .sarraySet arrVar idxVar valVar _ =>
    arrVar == target || idxVar == target || valVar == target
  | .rawLoad ptrVar idxVar _ => ptrVar == target || idxVar == target
  | .boxScalar valVar _ => valVar == target
  | .unboxScalar boxVar _ => boxVar == target
  | .call _ args _ _ => args.contains target

/-- Check whether `target` variable is referenced free in an `LNIRCode` block. -/
def codeUsesVar (target : VarId) : LNIRCode → Bool
  | .letBind dst _ val k =>
    exprUsesVar target val || (dst != target && codeUsesVar target k)
  | .rawStore ptrVar idxVar valVar _ k =>
    ptrVar == target || idxVar == target || valVar == target || codeUsesVar target k
  | .incRef objVar _ k =>
    objVar == target || codeUsesVar target k
  | .decRef objVar _ k =>
    objVar == target || codeUsesVar target k
  | .ite condVar thenBranch elseBranch =>
    condVar == target || codeUsesVar target thenBranch || codeUsesVar target elseBranch
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k =>
    loVar == target || hiVar == target || accInit == target ||
    (idxVar != target && accVar != target && codeUsesVar target stepBody) ||
    (accVar != target && codeUsesVar target k)
  | .parFor outVar lenVar inputs _ kernel k =>
    lenVar == target || inputs.contains target || kernelUsesVar target kernel ||
    (outVar != target && codeUsesVar target k)
  | .ret v => v == target
  | .unreachable => false

/-- Drop any tuple alias entry whose tuple variable or element fields mention `redefined`. -/
def invalidateTupleAlias (redefined : VarId) (env : List (VarId × List VarId)) : List (VarId × List VarId) :=
  env.filter (fun (tupVar, fields) => tupVar != redefined && !(fields.contains redefined))

/-- Drop any scalar variable alias entry mentioning `redefined`. -/
def invalidateScalarAlias (redefined : VarId) (senv : List (VarId × VarId)) : List (VarId × VarId) :=
  senv.filter (fun (dst, src) => dst != redefined && src != redefined)

/-- Resolve transitive scalar alias chains (`v -> v1 -> v2`) with bounded fuel. -/
def resolveScalarAlias (fuel : Nat) (senv : List (VarId × VarId)) (v : VarId) : VarId :=
  match fuel with
  | 0 => v
  | f + 1 =>
    match senv.lookup v with
    | some v' => if v' == v then v else resolveScalarAlias f senv v'
    | none => v

/-- Rewrite `LNIRCode` by forwarding `.projTuple dst idx` through known `.mkTuple fields`
    bindings (including nested $k$-tuples up to $k \le 8$ via transitive alias resolution)
    and eliminating dead `.mkTuple` bindings (SROA / tuple unboxing).
    Backed by `LeanNative.Proofs.LoopOptProofs.unboxTupleProj_sound`. -/
def optimizeCodeTupleSROAWithAliases
    (env : List (VarId × List VarId))
    (senv : List (VarId × VarId))
    (code : LNIRCode) : LNIRCode :=
  match code with
  | .letBind dst ty (.mkTuple fields) k =>
    let resolvedFields := fields.map (resolveScalarAlias 8 senv)
    let envClean := invalidateTupleAlias dst env
    let senvClean := invalidateScalarAlias dst senv
    let env' := (dst, resolvedFields) :: envClean
    let k' := optimizeCodeTupleSROAWithAliases env' senvClean k
    if codeUsesVar dst k' then
      .letBind dst ty (.mkTuple resolvedFields) k'
    else
      k'
  | .letBind dst ty (.projTuple tupleVar idx) k =>
    let rootTupleVar := resolveScalarAlias 8 senv tupleVar
    let (val', senvNext) : LNIRExpr × List (VarId × VarId) :=
      match env.lookup rootTupleVar with
      | some fields =>
        match fields[idx]? with
        | some fieldVar =>
          let rootField := resolveScalarAlias 8 senv fieldVar
          (.scalar (.var rootField), (dst, rootField) :: invalidateScalarAlias dst senv)
        | none => (.projTuple rootTupleVar idx, invalidateScalarAlias dst senv)
      | none => (.projTuple rootTupleVar idx, invalidateScalarAlias dst senv)
    let env' := invalidateTupleAlias dst env
    let k' := optimizeCodeTupleSROAWithAliases env' senvNext k
    match val' with
    | .scalar (.var rootField) =>
      if (env.lookup rootField).isSome && !(codeUsesVar dst k') then
        k'
      else
        .letBind dst ty val' k'
    | _ =>
      .letBind dst ty val' k'
  | .letBind dst ty (.scalar (.var srcVar)) k =>
    let rootSrc := resolveScalarAlias 8 senv srcVar
    let env' := invalidateTupleAlias dst env
    let senv' := (dst, rootSrc) :: invalidateScalarAlias dst senv
    .letBind dst ty (.scalar (.var rootSrc)) (optimizeCodeTupleSROAWithAliases env' senv' k)
  | .letBind dst ty val k =>
    let env' := invalidateTupleAlias dst env
    let senv' := invalidateScalarAlias dst senv
    .letBind dst ty val (optimizeCodeTupleSROAWithAliases env' senv' k)
  | .rawStore ptrVar idxVar valVar elemTy k =>
    .rawStore ptrVar idxVar valVar elemTy (optimizeCodeTupleSROAWithAliases env senv k)
  | .incRef objVar count k =>
    .incRef objVar count (optimizeCodeTupleSROAWithAliases env senv k)
  | .decRef objVar count k =>
    .decRef objVar count (optimizeCodeTupleSROAWithAliases env senv k)
  | .ite condVar thenBranch elseBranch =>
    .ite condVar (optimizeCodeTupleSROAWithAliases env senv thenBranch) (optimizeCodeTupleSROAWithAliases env senv elseBranch)
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    let stepEnv := invalidateTupleAlias accVar (invalidateTupleAlias idxVar env)
    let stepSenv := invalidateScalarAlias accVar (invalidateScalarAlias idxVar senv)
    let stepBody' := optimizeCodeTupleSROAWithAliases stepEnv stepSenv stepBody
    let kEnv := invalidateTupleAlias accVar env
    let kSenv := invalidateScalarAlias accVar senv
    .seqFor idxVar loVar hiVar accVar accInit accTy stepBody' (optimizeCodeTupleSROAWithAliases kEnv kSenv k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let kEnv := invalidateTupleAlias outVar env
    let kSenv := invalidateScalarAlias outVar senv
    .parFor outVar lenVar inputs elemTy kernel (optimizeCodeTupleSROAWithAliases kEnv kSenv k)
  | .ret v => .ret v
  | .unreachable => .unreachable

def optimizeCodeTupleSROA (env : List (VarId × List VarId)) (code : LNIRCode) : LNIRCode :=
  optimizeCodeTupleSROAWithAliases env [] code

/-- Run Tuple Unboxing & SROA on an `LNIRDecl`. -/
def unboxTupleSROADecl (d : LNIRDecl) : LNIRDecl :=
  { d with body := optimizeCodeTupleSROA [] d.body }

/-- Verified Tuple Unboxing & Scalar Replacement of Aggregates Pass (`UnboxTupleSROA`). -/
def unboxTupleSROAPass : TransformPass :=
  TransformPass.ofCodeTransform
    "UnboxTupleSROA"
    .verifiedKernelProof
    "LeanNative.Proofs.LoopOptProofs.unboxTupleProj_sound"
    "Forwards projTuple through SSA mkTuple alias map and eliminates dead tuple allocations"
    (fun d => (optimizeCodeTupleSROA [] d.body, none))

end LeanNative.Transform
