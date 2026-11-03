import LeanNative.IR.AST
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.KernelFusionProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.SymbolicTVDenote
import LeanNative.Proofs.SymbolicTVSoundness
import LeanNative.Proofs.SuperoptHelpersSoundness

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Transform

/-- Total structural equality checker on pure scalar `SymExpr` nodes
    (`.constU64`, `.constBool`, `.symVar`, `.binOp`, `.unaryOp`, `.ite`). -/
def pureSymExprEq : SymExpr → SymExpr → Bool
  | .constU64 a, .constU64 b => a == b
  | .constBool a, .constBool b => a == b
  | .symVar a, .symVar b => a == b
  | .binOp op1 l1 r1, .binOp op2 l2 r2 =>
    op1 == op2 && pureSymExprEq l1 l2 && pureSymExprEq r1 r2
  | .unaryOp op1 a1, .unaryOp op2 a2 =>
    op1 == op2 && pureSymExprEq a1 a2
  | .ite c1 t1 e1, .ite c2 t2 e2 =>
    pureSymExprEq c1 c2 && pureSymExprEq t1 t2 && pureSymExprEq e1 e2
  | _, _ => false

/-- Total structural equality checker on `List VarId`. -/
def varIdListEq : List VarId → List VarId → Bool
  | [], [] => true
  | x :: xs, y :: ys => x == y && varIdListEq xs ys
  | _, _ => false

/-- Total structural equality checker on `LNIRExpr` up to `evalExpr`-erased `LNIRType` annotations. -/
def lnirExprEvalEq : LNIRExpr → LNIRExpr → Bool
  | .scalar a, .scalar b => a == b
  | .constU256 a, .constU256 b => a == b
  | .mulDivDown a1 b1 c1, .mulDivDown a2 b2 c2 => a1 == a2 && b1 == b2 && c1 == c2
  | .mulDivUp a1 b1 c1, .mulDivUp a2 b2 c2 => a1 == a2 && b1 == b2 && c1 == c2
  | .storageLoad m1 s1, .storageLoad m2 s2 => m1 == m2 && s1 == s2
  | .storageStore m1 s1 v1, .storageStore m2 s2 v2 => m1 == m2 && s1 == s2 && v1 == v2
  | .mkTuple xs, .mkTuple ys => varIdListEq xs ys
  | .projTuple t1 i1, .projTuple t2 i2 => t1 == t2 && i1 == i2
  | .allocCtor tag1 os1 ss1, .allocCtor tag2 os2 ss2 =>
    tag1 == tag2 && varIdListEq os1 os2 && varIdListEq ss1 ss2
  | .ctorGetObj o1 i1, .ctorGetObj o2 i2 => o1 == o2 && i1 == i2
  | .ctorGetScalar o1 i1 _, .ctorGetScalar o2 i2 _ => o1 == o2 && i1 == i2
  | .isExclusive o1, .isExclusive o2 => o1 == o2
  | .sarrayLen a1, .sarrayLen a2 => a1 == a2
  | .sarrayDataPtr a1 _, .sarrayDataPtr a2 _ => a1 == a2
  | .sarrayEnsureExclusive a1 _, .sarrayEnsureExclusive a2 _ => a1 == a2
  | .sarrayGet a1 i1 _, .sarrayGet a2 i2 _ => a1 == a2 && i1 == i2
  | .sarraySet a1 i1 v1 _, .sarraySet a2 i2 v2 _ => a1 == a2 && i1 == i2 && v1 == v2
  | .rawLoad p1 i1 _, .rawLoad p2 i2 _ => p1 == p2 && i1 == i2
  | .boxScalar v1 _, .boxScalar v2 _ => v1 == v2
  | .unboxScalar o1 _, .unboxScalar o2 _ => o1 == o2
  | .call f1 as1 _ ext1, .call f2 as2 _ ext2 =>
    f1 == f2 && varIdListEq as1 as2 && ext1 == ext2
  | _, _ => false

/-- Total structural equality checker on `ParallelKernelKind`. -/
def parallelKernelEq : ParallelKernelKind → ParallelKernelKind → Bool
  | .mapScaleAdd s1 b1, .mapScaleAdd s2 b2 => s1 == s2 && b1 == b2
  | .zipAdd, .zipAdd => true
  | .zipMul, .zipMul => true
  | .saxpy a1, .saxpy a2 => a1 == a2
  | .dotProduct, .dotProduct => true
  | .stencil1D3Pt l1 c1 r1, .stencil1D3Pt l2 c2 r2 => l1 == l2 && c1 == c2 && r1 == r2
  | .customScalar idx1 ins1 body1, .customScalar idx2 ins2 body2 =>
    idx1 == idx2 && varIdListEq ins1 ins2 && body1 == body2
  | _, _ => false

/-- Context tracked during symbolic `LNIRCode` refinement checking:
    tracks variables proven bound in `env`, proven `.u64`, proven scalar constants,
    and proven non-shadowed `.mkTuple` bindings. -/
structure SymRefinesCtx where
  boundVars : List VarId := []
  u64Vars   : List VarId := []
  constU64  : List (VarId × UInt64) := []
  constBool : List (VarId × Bool) := []
  tuples    : List (VarId × List VarId) := []
  deriving Repr, Inhabited

def findConstU64 (v : VarId) : List (VarId × UInt64) → Option UInt64
  | [] => none
  | (k, n) :: rest => if k == v then some n else findConstU64 v rest

def findConstBool (v : VarId) : List (VarId × Bool) → Option Bool
  | [] => none
  | (k, b) :: rest => if k == v then some b else findConstBool v rest

def filterOutConstU64 (dst : VarId) : List (VarId × UInt64) → List (VarId × UInt64)
  | [] => []
  | (k, v) :: rest =>
    if k == dst then filterOutConstU64 dst rest else (k, v) :: filterOutConstU64 dst rest

def filterOutConstBool (dst : VarId) : List (VarId × Bool) → List (VarId × Bool)
  | [] => []
  | (k, v) :: rest =>
    if k == dst then filterOutConstBool dst rest else (k, v) :: filterOutConstBool dst rest

def filterOutVarId (dst : VarId) : List VarId → List VarId
  | [] => []
  | x :: rest =>
    if x == dst then filterOutVarId dst rest else x :: filterOutVarId dst rest

def findTupleField (tVar : VarId) (idx : Nat) : List (VarId × List VarId) → Option VarId
  | [] => none
  | (k, fs) :: rest =>
    if k == tVar then fs[idx]?
    else findTupleField tVar idx rest

def dropClobberedTuples (dst : VarId) : List (VarId × List VarId) → List (VarId × List VarId)
  | [] => []
  | (tVar, fs) :: rest =>
    if tVar == dst || fs.contains dst then dropClobberedTuples dst rest
    else (tVar, fs) :: dropClobberedTuples dst rest

def SymRefinesCtx.killVar (ctx : SymRefinesCtx) (dst : VarId) : SymRefinesCtx :=
  { boundVars := filterOutVarId dst ctx.boundVars
    u64Vars := filterOutVarId dst ctx.u64Vars
    constU64 := filterOutConstU64 dst ctx.constU64
    constBool := filterOutConstBool dst ctx.constBool
    tuples := dropClobberedTuples dst ctx.tuples }

def SymRefinesCtx.addBound (ctx : SymRefinesCtx) (dst : VarId) : SymRefinesCtx :=
  if ctx.boundVars.contains dst then ctx else { ctx with boundVars := dst :: ctx.boundVars }

def SymRefinesCtx.addBoundVars (ctx : SymRefinesCtx) : List VarId → SymRefinesCtx
  | [] => ctx
  | v :: vs => (ctx.addBound v).addBoundVars vs

def SymRefinesCtx.addU64 (ctx : SymRefinesCtx) (dst : VarId) : SymRefinesCtx :=
  let ctx1 := ctx.addBound dst
  if ctx1.u64Vars.contains dst then ctx1 else { ctx1 with u64Vars := dst :: ctx1.u64Vars }

def SymRefinesCtx.bindU64Vars (ctx : SymRefinesCtx) : List VarId → SymRefinesCtx
  | [] => ctx
  | v :: vs => ((ctx.killVar v).addU64 v).bindU64Vars vs

def SymRefinesCtx.addForcedVars (ctx : SymRefinesCtx) : List VarId → SymRefinesCtx
  | [] => ctx
  | v :: vs => (ctx.addU64 v).addForcedVars vs

/-- Substitute proven-constant scalar bindings from `SymRefinesCtx` into `ScalarExpr`. -/
def substKnownConsts (ctx : SymRefinesCtx) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id =>
    match findConstU64 id ctx.constU64 with
    | some n => .constU64 n
    | none =>
      match findConstBool id ctx.constBool with
      | some b => .constBool b
      | none => .var id
  | .binOp op l r => .binOp op (substKnownConsts ctx l) (substKnownConsts ctx r)
  | .unaryOp op a => .unaryOp op (substKnownConsts ctx a)
  | .select c t f =>
    .select (substKnownConsts ctx c) (substKnownConsts ctx t) (substKnownConsts ctx f)
  | .fma a b c =>
    .fma (substKnownConsts ctx a) (substKnownConsts ctx b) (substKnownConsts ctx c)

/-- Expand `.fma a b c` to `.binOp .add (.binOp .mul a b) c` (definitionally equal under `evalScalarExpr`). -/
def expandFmaScalar : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp op l r => .binOp op (expandFmaScalar l) (expandFmaScalar r)
  | .unaryOp op a => .unaryOp op (expandFmaScalar a)
  | .select c t f => .select (expandFmaScalar c) (expandFmaScalar t) (expandFmaScalar f)
  | .fma a b c =>
    .binOp .add (.binOp .mul (expandFmaScalar a) (expandFmaScalar b)) (expandFmaScalar c)

/-- Collect variables forced to `.u64` if evaluating `e` succeeds. -/
def forcedU64VarsOfScalar (e : ScalarExpr) : List VarId :=
  (collectScalarVars e).filter (fun id => varForcedU64 id e)

/-- Total symbolic scalar refinement checker: checks constant propagation, FMA contraction/expansion,
    algebraic peepholes (`rewriteScalarVerified`), and Alive2-style pure-`u64` `normSymExpr` equivalence. -/
def symbolicScalarRefines (ctx : SymRefinesCtx) (eSrc eTgt : ScalarExpr) : Bool :=
  let sSrc := expandFmaScalar (substKnownConsts ctx eSrc)
  let sTgt := expandFmaScalar (substKnownConsts ctx eTgt)
  sSrc == sTgt ||
  rewriteScalarVerified sSrc == rewriteScalarVerified sTgt ||
  contractKernelScalar sSrc == contractKernelScalar sTgt ||
  (let u64s := unionVars ctx.u64Vars (forcedU64VarsOfScalar sSrc)
   isPureU64ScalarExpr sSrc &&
   isPureU64ScalarExpr sTgt &&
   isPureU64SymExprIn u64s (scalarToSymExpr sSrc) &&
   isPureU64SymExprIn u64s (scalarToSymExpr sTgt) &&
   pureSymExprEq (normSymExpr (scalarToSymExpr sSrc)) (normSymExpr (scalarToSymExpr sTgt)))

/-- Update `SymRefinesCtx` after a `.letBind dst ty (.scalar eSrc)` succeeds in `src`. -/
def SymRefinesCtx.afterScalarLet (ctx : SymRefinesCtx) (dst : VarId) (eSrc : ScalarExpr) : SymRefinesCtx :=
  let sSrc := expandFmaScalar (substKnownConsts ctx eSrc)
  let ctxForced := ctx.addForcedVars (forcedU64VarsOfScalar sSrc)
  let isDstU64 :=
    isPureU64ScalarExpr sSrc &&
    isPureU64SymExprIn ctxForced.u64Vars (scalarToSymExpr sSrc)
  let ctxKilled := (ctxForced.killVar dst).addBound dst
  match rewriteScalarVerified sSrc with
  | .constU64 n =>
    { ctxKilled with
      u64Vars := if ctxKilled.u64Vars.contains dst then ctxKilled.u64Vars else dst :: ctxKilled.u64Vars
      constU64 := (dst, n) :: ctxKilled.constU64 }
  | .constBool b =>
    { ctxKilled with
      constBool := (dst, b) :: ctxKilled.constBool }
  | _ =>
    if isDstU64 then ctxKilled.addU64 dst else ctxKilled

/-- Check whether `dst` does not appear free anywhere in `code` (so binding `dst` is dead). -/
def varDeadInCode (dst : VarId) (code : LNIRCode) : Bool :=
  !(codeUsesVar dst code)

/-- Update `SymRefinesCtx` after `.letBind dst ty (.mkTuple fs)` succeeds in `src`. -/
def SymRefinesCtx.afterMkTupleLet (ctx : SymRefinesCtx) (dst : VarId) (fs : List VarId) : SymRefinesCtx :=
  let ctx1 := ((ctx.addBoundVars fs).killVar dst).addBound dst
  if fs.contains dst then ctx1
  else
    { ctx1 with tuples := (dst, fs) :: dropClobberedTuples dst ctx1.tuples }

/-- Total symbolic `LNIRExpr` refinement checker (including `.projTuple tVar idx -> .scalar (.var fVar)`). -/
def symbolicExprRefines (ctx : SymRefinesCtx) (eSrc eTgt : LNIRExpr) : Bool :=
  match eSrc, eTgt with
  | .scalar s1, .scalar s2 => symbolicScalarRefines ctx s1 s2
  | .projTuple tVar idx, .scalar eTgt =>
    match findTupleField tVar idx ctx.tuples with
    | some fVar => symbolicScalarRefines ctx (.var fVar) eTgt
    | none => false
  | _, _ => lnirExprEvalEq eSrc eTgt

/-- Total symbolic `ParallelKernelKind` refinement checker. -/
def symbolicKernelRefines (ctx : SymRefinesCtx) (kSrc kTgt : ParallelKernelKind) : Bool :=
  parallelKernelEq kSrc kTgt ||
  parallelKernelEq (specializeKernel kSrc) kTgt ||
  match kSrc, kTgt with
  | .customScalar idx1 ins1 body1, .customScalar idx2 ins2 body2 =>
    idx1 == idx2 &&
    varIdListEq ins1 ins2 &&
    symbolicScalarRefines (((ctx.killVar idx1).addU64 idx1).bindU64Vars ins1) body1 body2
  | _, _ => false

/-- Recursive total symbolic `LNIRCode` refinement checker. -/
def symbolicCodeRefinesAux (ctx : SymRefinesCtx) (src tgt : LNIRCode) : Bool :=
  match src with
  | .ret v1 =>
    match tgt with
    | .ret v2 => v1 == v2
    | _ => false
  | .unreachable =>
    match tgt with
    | .unreachable => true
    | _ => false
  | .letBind dst1 _ val1 k1 =>
    match val1 with
    | .mkTuple fs1 =>
      let keepBranch :=
        match tgt with
        | .letBind dst2 _ (.mkTuple fs2) k2 =>
          dst1 == dst2 &&
          varIdListEq fs1 fs2 &&
          symbolicCodeRefinesAux (ctx.afterMkTupleLet dst1 fs1) k1 k2
        | _ => false
      if keepBranch then true
      else
        fs1.all (fun f => ctx.boundVars.contains f) &&
        varDeadInCode dst1 tgt &&
        symbolicCodeRefinesAux (ctx.afterMkTupleLet dst1 fs1) k1 tgt
    | .scalar e1 =>
      match tgt with
      | .letBind dst2 _ (.scalar e2) k2 =>
        dst1 == dst2 &&
        symbolicScalarRefines ctx e1 e2 &&
        symbolicCodeRefinesAux (ctx.afterScalarLet dst1 e1) k1 k2
      | _ => false
    | .projTuple tVar idx =>
      match tgt with
      | .letBind dst2 _ (.scalar e2) k2 =>
        dst1 == dst2 &&
        (match findTupleField tVar idx ctx.tuples with
         | some fVar =>
           symbolicScalarRefines ctx (.var fVar) e2 &&
           symbolicCodeRefinesAux (ctx.afterScalarLet dst1 (.var fVar)) k1 k2
         | none => false)
      | .letBind dst2 _ val2 k2 =>
        dst1 == dst2 &&
        lnirExprEvalEq (.projTuple tVar idx) val2 &&
        symbolicCodeRefinesAux ((ctx.killVar dst1).addBound dst1) k1 k2
      | _ => false
    | _ =>
      match tgt with
      | .letBind dst2 _ val2 k2 =>
        dst1 == dst2 &&
        lnirExprEvalEq val1 val2 &&
        symbolicCodeRefinesAux ((ctx.killVar dst1).addBound dst1) k1 k2
      | _ => false
  | .rawStore p1 i1 v1 _ k1 =>
    match tgt with
    | .rawStore p2 i2 v2 _ k2 =>
      p1 == p2 && i1 == i2 && v1 == v2 &&
      symbolicCodeRefinesAux (((ctx.addBound p1).addU64 i1).addU64 v1) k1 k2
    | _ => false
  | .incRef o1 c1 k1 =>
    match tgt with
    | .incRef o2 c2 k2 =>
      o1 == o2 && c1 == c2 && symbolicCodeRefinesAux ctx k1 k2
    | _ => false
  | .decRef o1 c1 k1 =>
    match tgt with
    | .decRef o2 c2 k2 =>
      o1 == o2 && c1 == c2 && symbolicCodeRefinesAux ctx k1 k2
    | _ => false
  | .ite condVar t1 e1 =>
    let sameIte :=
      match tgt with
      | .ite c2 t2 e2 =>
        condVar == c2 &&
        symbolicCodeRefinesAux (ctx.addBound condVar) t1 t2 &&
        symbolicCodeRefinesAux (ctx.addBound condVar) e1 e2
      | _ => false
    if sameIte then true
    else
      match findConstBool condVar ctx.constBool with
      | some true => symbolicCodeRefinesAux ctx t1 tgt
      | some false => symbolicCodeRefinesAux ctx e1 tgt
      | none =>
        match findConstU64 condVar ctx.constU64 with
        | some n =>
          if n != 0 then symbolicCodeRefinesAux ctx t1 tgt
          else symbolicCodeRefinesAux ctx e1 tgt
        | none => false
  | .seqFor idx1 lo1 hi1 acc1 init1 _ step1 k1 =>
    match tgt with
    | .seqFor idx2 lo2 hi2 acc2 init2 _ step2 k2 =>
      idx1 == idx2 && lo1 == lo2 && hi1 == hi2 && acc1 == acc2 && init1 == init2 &&
      (let ctxBounds := ((ctx.addU64 lo1).addU64 hi1).addBound init1
       let stepCtx := (((ctxBounds.killVar idx1).addU64 idx1).killVar acc1).addBound acc1
       let contCtx := (ctxBounds.killVar acc1).addBound acc1
       symbolicCodeRefinesAux stepCtx step1 step2 &&
       symbolicCodeRefinesAux contCtx k1 k2)
    | _ => false
  | .parFor out1 len1 ins1 _ kern1 k1 =>
    match tgt with
    | .parFor out2 len2 ins2 _ kern2 k2 =>
      out1 == out2 && len1 == len2 && varIdListEq ins1 ins2 &&
      (let ctxLen := (ctx.addU64 len1).addBoundVars ins1
       symbolicKernelRefines ctxLen kern1 kern2 &&
       symbolicCodeRefinesAux ((ctxLen.killVar out1).addBound out1) k1 k2)
    | _ => false

/-- Top-level total symbolic `LNIRCode` refinement checker (`LNIRCode → LNIRCode → Bool`). -/
def symbolicCodeRefines (src tgt : LNIRCode) : Bool :=
  symbolicCodeRefinesAux {} src tgt

/-- Total declaration-level translation-validated optimizer wrapper (`Contract V2` `VerifiedTVPassContract`):
    returns `some tgt` iff `symbolicCodeRefines src.body tgt.body = true`. -/
def runSymbolicValidatedDecl (propose : LNIRDecl → LNIRDecl) (d : LNIRDecl) : Option LNIRDecl :=
  if symbolicCodeRefines d.body (propose d).body then some (propose d) else none

end LeanNative.Proofs
