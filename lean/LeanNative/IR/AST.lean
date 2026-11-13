import LeanNative.IR.Types

namespace LeanNative.IR

/-- Binary arithmetic, bitwise, comparison, and checked 256-bit EVM operators in LNIR. -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | mod
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | sar            -- Arithmetic shift right (64-bit / 256-bit EVM SAR)
  | eq
  | lt
  | le
  | addChecked256  -- 256-bit checked addition (traps/errors on overflow >= 2^256)
  | subChecked256  -- 256-bit checked subtraction (traps/errors on underflow < 0)
  | mulChecked256  -- 256-bit checked multiplication (traps/errors on overflow >= 2^256)
  | clmul64 | clmul64Hi -- carryless product low/high 64 bits (pclmulqdq / pmull)
  | gf2Affine      -- GF(2^8) affine map, low byte (vgf2p8affineqb)
  | eor3           -- a ^^^ b ^^^ c, with c the low 64 of the rhs word (vpternlogq / eor3)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Unary operators in LNIR. -/
inductive UnaryOp where
  | not
  | neg
  | clz256         -- 256-bit count leading zeros (EVM/Verity CLZ256)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Pure / scalar SSA expression in LNIR (verified core fragment). -/
inductive ScalarExpr where
  | constU64 (val : UInt64)
  | constBool (val : Bool)
  | var (id : VarId)
  | binOp (op : BinOp) (lhs rhs : ScalarExpr)
  | unaryOp (op : UnaryOp) (arg : ScalarExpr)
  | select (cond thenVal elseVal : ScalarExpr)
  | fma (a b c : ScalarExpr) -- a * b + c
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Data-parallel kernel pattern for GPU (MLIR/NVVM/PTX) and CPU SIMD lowering. -/
inductive ParallelKernelKind where
  | mapScaleAdd (scale : UInt64) (bias : UInt64)  -- out[i] = in0[i] * scale + bias
  | zipAdd                                        -- out[i] = in0[i] + in1[i]
  | zipMul                                        -- out[i] = in0[i] * in1[i]
  | saxpy (alphaBits : UInt64)                    -- out[i] = alpha * x[i] + y[i]
  | dotProduct                                    -- sum_i (in0[i] * in1[i])
  | stencil1D3Pt (wLeft wCenter wRight : UInt64)  -- 3-point 1D stencil
  | customScalar (idxVar : VarId) (inVars : List VarId) (body : ScalarExpr)
  deriving Repr, Inhabited, BEq

/-- Right-hand side of a let-binding in LNIR (including 256-bit EVM words and Storage Maps). -/
inductive LNIRExpr where
  | scalar (e : ScalarExpr)
  | constU256 (val : UInt256)
  | mulDivDown (aVar : VarId) (bVar : VarId) (denomVar : VarId)
  | mulDivUp (aVar : VarId) (bVar : VarId) (denomVar : VarId)
  | storageLoad (mapVar : VarId) (slotVar : VarId)
  | storageStore (mapVar : VarId) (slotVar : VarId) (valVar : VarId)
  | mkTuple (fields : List VarId)
  | projTuple (tupleVar : VarId) (idx : Nat)
  | allocCtor (tag : Nat) (objFields : List VarId) (scalarFields : List VarId)
  | ctorGetObj (ctorVar : VarId) (idx : Nat)
  | ctorGetScalar (ctorVar : VarId) (idx : Nat) (ty : LNIRType)
  | isExclusive (objVar : VarId)
  | sarrayLen (arrVar : VarId)
  | sarrayDataPtr (arrVar : VarId) (elemTy : LNIRType)
  | sarrayEnsureExclusive (arrVar : VarId) (elemTy : LNIRType)
  | sarrayGet (arrVar : VarId) (idxVar : VarId) (elemTy : LNIRType)
  | sarraySet (arrVar : VarId) (idxVar : VarId) (valVar : VarId) (elemTy : LNIRType)
  | rawLoad (ptrVar : VarId) (idxVar : VarId) (elemTy : LNIRType)
  | boxScalar (valVar : VarId) (ty : LNIRType)
  | unboxScalar (boxVar : VarId) (ty : LNIRType)
  | call (fnName : String) (args : List VarId) (retTy : LNIRType) (isExtern : Bool := false)
  deriving Repr, Inhabited, BEq

/-- Parameter in an LNIR function or join point. -/
structure LNIRParam where
  id     : VarId
  name   : String
  ty     : LNIRType
  borrow : Bool := false
  deriving Repr, Inhabited, BEq

/-- Structured ANF / SSA code block in LNIR. -/
inductive LNIRCode where
  | letBind (dst : VarId) (ty : LNIRType) (val : LNIRExpr) (k : LNIRCode)
  | rawStore (ptrVar : VarId) (idxVar : VarId) (valVar : VarId) (elemTy : LNIRType) (k : LNIRCode)
  | incRef (objVar : VarId) (count : Nat) (k : LNIRCode)
  | decRef (objVar : VarId) (count : Nat) (k : LNIRCode)
  | ite (condVar : VarId) (thenBranch : LNIRCode) (elseBranch : LNIRCode)
  | seqFor (idxVar : VarId) (loVar hiVar : VarId) (accVar : VarId) (accInit : VarId)
      (accTy : LNIRType) (stepBody : LNIRCode) (k : LNIRCode)
  | parFor (outVar : VarId) (lenVar : VarId) (inputs : List VarId) (elemTy : LNIRType)
      (kernel : ParallelKernelKind) (k : LNIRCode)
  | ret (var : VarId)
  | unreachable
  deriving Repr, Inhabited, BEq

/-- A refinement fact retained from the pure LCNF phase. Defined above `LNIRDecl` so a
declaration can carry it; backends consume it without importing `LeanNative.Semantics`. -/
inductive RetainedFact where
  | idxLt (idxVar lenVar : VarId)
  | noOverflowAdd (lhs rhs : VarId) (nsw nuw : Bool)
  | noOverflowSub (lhs rhs : VarId) (nsw nuw : Bool)
  | noOverflowMul (lhs rhs : VarId) (nsw nuw : Bool)
  | alignedPtr (ptrVar : VarId) (alignBytes : Nat)
  | disjointSlices (ptrA ptrB lenA lenB : VarId)
  | exclusiveObj (objVar : VarId)
  deriving Repr, DecidableEq, Inhabited

abbrev FactEnv := List RetainedFact

def factMember (facts : FactEnv) (f : RetainedFact) : Bool :=
  facts.contains f

def consFact (facts : FactEnv) (f : RetainedFact) : FactEnv :=
  if factMember facts f then facts else f :: facts

/-- Top-level function declaration in LNIR. -/
structure LNIRDecl where
  name          : String
  params        : List LNIRParam
  retTy         : LNIRType
  body          : LNIRCode
  assurance     : AssuranceLevel := .verifiedKernelProof
  isGpuCand     : Bool := false
  retainedFacts : FactEnv := []
  deriving Repr, Inhabited, BEq

/-- Complete compilation module in LNIR. -/
structure LNIRModule where
  moduleName : String
  decls      : List LNIRDecl
  deriving Repr, Inhabited, BEq

/-- Deterministic FNV-1a 64-bit structural fingerprint of an LNIR declaration for translation validation certificates. -/
def hashStringFNV64 (s : String) : String :=
  let prime : UInt64 := 1099511628211
  let offset : UInt64 := 14695981039346656037
  let h := s.toUTF8.foldl (fun acc b => (acc ^^^ b.toUInt64) * prime) offset
  let hexChars := "0123456789abcdef".toList
  let rec toHex (n : Nat) (val : UInt64) (acc : List Char) : String :=
    match n with
    | 0 => String.ofList acc
    | n' + 1 =>
      let nib := (val &&& 0xf).toNat
      let c := hexChars[nib]?.getD '0'
      toHex n' (val >>> 4) (c :: acc)
  toHex 16 h []

def LNIRDecl.structuralHash (d : LNIRDecl) : String :=
  hashStringFNV64 (reprStr d)

/-! ## Canonical de Bruijn Renaming & `modded-nanogpt` Token Stream Features -/

private def lookupDeBruijn (ctx : List VarId) (v : VarId) : VarId :=
  let rec findIdx ( idx : Nat ) : List VarId → VarId
    | [] => v
    | h :: t => if h == v then idx else findIdx (idx + 1) t
  findIdx 0 ctx

def ScalarExpr.canonicalDeBruijn (ctx : List VarId) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var (lookupDeBruijn ctx id)
  | .binOp op l r => .binOp op (l.canonicalDeBruijn ctx) (r.canonicalDeBruijn ctx)
  | .unaryOp op a => .unaryOp op (a.canonicalDeBruijn ctx)
  | .select c t e => .select (c.canonicalDeBruijn ctx) (t.canonicalDeBruijn ctx) (e.canonicalDeBruijn ctx)
  | .fma a b c => .fma (a.canonicalDeBruijn ctx) (b.canonicalDeBruijn ctx) (c.canonicalDeBruijn ctx)

def LNIRExpr.canonicalDeBruijn (ctx : List VarId) : LNIRExpr → LNIRExpr
  | .scalar e => .scalar (e.canonicalDeBruijn ctx)
  | .constU256 v => .constU256 v
  | .mulDivDown a b d => .mulDivDown (lookupDeBruijn ctx a) (lookupDeBruijn ctx b) (lookupDeBruijn ctx d)
  | .mulDivUp a b d => .mulDivUp (lookupDeBruijn ctx a) (lookupDeBruijn ctx b) (lookupDeBruijn ctx d)
  | .storageLoad m s => .storageLoad (lookupDeBruijn ctx m) (lookupDeBruijn ctx s)
  | .storageStore m s v => .storageStore (lookupDeBruijn ctx m) (lookupDeBruijn ctx s) (lookupDeBruijn ctx v)
  | .mkTuple fs => .mkTuple (fs.map (lookupDeBruijn ctx))
  | .projTuple tv idx => .projTuple (lookupDeBruijn ctx tv) idx
  | .allocCtor tag ofs sfs => .allocCtor tag (ofs.map (lookupDeBruijn ctx)) (sfs.map (lookupDeBruijn ctx))
  | .ctorGetObj cv idx => .ctorGetObj (lookupDeBruijn ctx cv) idx
  | .ctorGetScalar cv idx ty => .ctorGetScalar (lookupDeBruijn ctx cv) idx ty
  | .isExclusive ov => .isExclusive (lookupDeBruijn ctx ov)
  | .sarrayLen av => .sarrayLen (lookupDeBruijn ctx av)
  | .sarrayDataPtr av ety => .sarrayDataPtr (lookupDeBruijn ctx av) ety
  | .sarrayEnsureExclusive av ety => .sarrayEnsureExclusive (lookupDeBruijn ctx av) ety
  | .sarrayGet av iv ety => .sarrayGet (lookupDeBruijn ctx av) (lookupDeBruijn ctx iv) ety
  | .sarraySet av iv vv ety => .sarraySet (lookupDeBruijn ctx av) (lookupDeBruijn ctx iv) (lookupDeBruijn ctx vv) ety
  | .rawLoad pv iv ety => .rawLoad (lookupDeBruijn ctx pv) (lookupDeBruijn ctx iv) ety
  | .boxScalar vv ty => .boxScalar (lookupDeBruijn ctx vv) ty
  | .unboxScalar bv ty => .unboxScalar (lookupDeBruijn ctx bv) ty
  | .call fn args rty ext => .call fn (args.map (lookupDeBruijn ctx)) rty ext

def LNIRCode.canonicalDeBruijn (ctx : List VarId) : LNIRCode → LNIRCode
  | .letBind dst ty val k =>
    let val' := val.canonicalDeBruijn ctx
    let ctx' := dst :: ctx
    .letBind 0 ty val' (k.canonicalDeBruijn ctx')
  | .rawStore pv iv vv ety k =>
    .rawStore (lookupDeBruijn ctx pv) (lookupDeBruijn ctx iv) (lookupDeBruijn ctx vv) ety (k.canonicalDeBruijn ctx)
  | .incRef ov c k => .incRef (lookupDeBruijn ctx ov) c (k.canonicalDeBruijn ctx)
  | .decRef ov c k => .decRef (lookupDeBruijn ctx ov) c (k.canonicalDeBruijn ctx)
  | .ite cv t e => .ite (lookupDeBruijn ctx cv) (t.canonicalDeBruijn ctx) (e.canonicalDeBruijn ctx)
  | .seqFor iv lv hv av ai aty step k =>
    let lv' := lookupDeBruijn ctx lv
    let hv' := lookupDeBruijn ctx hv
    let ai' := lookupDeBruijn ctx ai
    let stepCtx := av :: iv :: ctx
    let kCtx := av :: ctx
    .seqFor 1 lv' hv' 0 ai' aty (step.canonicalDeBruijn stepCtx) (k.canonicalDeBruijn kCtx)
  | .parFor ov lv ins ety kern k =>
    let lv' := lookupDeBruijn ctx lv
    let ins' := ins.map (lookupDeBruijn ctx)
    let kern' := match kern with
      | .customScalar idxVar inVars body =>
        .customScalar 0 (List.range inVars.length) (body.canonicalDeBruijn (idxVar :: inVars.reverse ++ ctx))
      | other => other
    .parFor 0 lv' ins' ety kern' (k.canonicalDeBruijn (ov :: ctx))
  | .ret v => .ret (lookupDeBruijn ctx v)
  | .unreachable => .unreachable

def RetainedFact.canonicalDeBruijn (ctx : List VarId) : RetainedFact → RetainedFact
  | .idxLt i n => .idxLt (lookupDeBruijn ctx i) (lookupDeBruijn ctx n)
  | .noOverflowAdd a b nsw nuw =>
    .noOverflowAdd (lookupDeBruijn ctx a) (lookupDeBruijn ctx b) nsw nuw
  | .noOverflowSub a b nsw nuw =>
    .noOverflowSub (lookupDeBruijn ctx a) (lookupDeBruijn ctx b) nsw nuw
  | .noOverflowMul a b nsw nuw =>
    .noOverflowMul (lookupDeBruijn ctx a) (lookupDeBruijn ctx b) nsw nuw
  | .alignedPtr p n => .alignedPtr (lookupDeBruijn ctx p) n
  | .disjointSlices a b la lb =>
    .disjointSlices (lookupDeBruijn ctx a) (lookupDeBruijn ctx b)
      (lookupDeBruijn ctx la) (lookupDeBruijn ctx lb)
  | .exclusiveObj o => .exclusiveObj (lookupDeBruijn ctx o)

/-- Alpha-canonicalized de Bruijn representation of an `LNIRDecl` for `modded-nanogpt` training. -/
def LNIRDecl.canonicalDeBruijn (d : LNIRDecl) : LNIRDecl :=
  let initCtx := (d.params.map (·.id)).reverse
  let params' := (List.range d.params.length).zip d.params |>.map fun (idx, p) =>
    { p with id := idx, name := s!"p{idx}" }
  { d with
    params := params'
    body := d.body.canonicalDeBruijn initCtx
    retainedFacts := d.retainedFacts.map (RetainedFact.canonicalDeBruijn initCtx) }

/-- Structural features `(nInstr, nBlocks, nLoops, maxLoopDepth, u64Count, u256Count, boolCount)`
    extracted from an `LNIRDecl` for telemetry and cost/value head conditioning. -/
def LNIRDecl.telemetryFeaturesJson (d : LNIRDecl) : String :=
  let rec go (depth : Nat) : LNIRCode → Nat × Nat × Nat × Nat × Nat × Nat × Nat
    | .letBind _ ty _ k =>
      let (ni, nb, nl, md, u64c, u256c, bc) := go depth k
      let u64d := if ty == .i64 || ty == .usize then 1 else 0
      let u256d := if ty == .u256 || ty == .i256 then 1 else 0
      let bd := if ty == .i1 then 1 else 0
      (ni + 1, nb, nl, md, u64c + u64d, u256c + u256d, bc + bd)
    | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k =>
      let (ni, nb, nl, md, u64c, u256c, bc) := go depth k
      (ni + 1, nb, nl, md, u64c, u256c, bc)
    | .ite _ t e =>
      let (ni1, nb1, nl1, md1, u64_1, u256_1, b1) := go depth t
      let (ni2, nb2, nl2, md2, u64_2, u256_2, b2) := go depth e
      (ni1 + ni2 + 1, nb1 + nb2 + 2, nl1 + nl2, Nat.max md1 md2, u64_1 + u64_2, u256_1 + u256_2, b1 + b2 + 1)
    | .seqFor _ _ _ _ _ aty step k =>
      let (ni1, nb1, nl1, md1, u64_1, u256_1, b1) := go (depth + 1) step
      let (ni2, nb2, nl2, md2, u64_2, u256_2, b2) := go depth k
      let u64d := if aty == .i64 || aty == .usize then 1 else 0
      let u256d := if aty == .u256 || aty == .i256 then 1 else 0
      (ni1 + ni2 + 1, nb1 + nb2 + 1, nl1 + nl2 + 1, Nat.max (Nat.max (depth + 1) md1) md2,
       u64_1 + u64_2 + u64d, u256_1 + u256_2 + u256d, b1 + b2)
    | .parFor _ _ _ ety _ k =>
      let (ni, nb, nl, md, u64c, u256c, bc) := go (depth + 1) k
      let u64d := if ety == .i64 || ety == .usize then 1 else 0
      let u256d := if ety == .u256 || ety == .i256 then 1 else 0
      (ni + 1, nb + 1, nl + 1, Nat.max (depth + 1) md, u64c + u64d, u256c + u256d, bc)
    | .ret _ | .unreachable => (1, 1, 0, depth, 0, 0, 0)
  let (nInstr, nBlocks, nLoops, maxDepth, u64c, u256c, bc) := go 0 d.body
  s!"\{\"n_instr\":{nInstr},\"n_blocks\":{nBlocks},\"n_loops\":{nLoops},\"max_loop_depth\":{maxDepth},\"width_histogram\":\{\"u64\":{u64c},\"u256\":{u256c},\"bool\":{bc}}}"

/-- RC-ADT (Stage 1D heap) expressions: ctor ops, heap boxes, exclusivity tests, and the heap runtime calls. -/
def LNIRExpr.isRcAdtExpr : LNIRExpr → Bool
  | .allocCtor _ _ _ | .ctorGetObj _ _ | .ctorGetScalar _ _ _ | .isExclusive _
  | .boxScalar _ _ | .unboxScalar _ _ => true
  | .call fn _ retTy _ => fn.startsWith "lean_native_ctor_" || fn == "lean_native_del_obj" || retTy.containsHeapObject
  | _ => false

/-- Whether code touches a heap object: an RC-ADT expression, a heap-typed binder, or an RC op on a heap var. -/
def LNIRCode.containsRcAdt (objVars : List VarId) : LNIRCode → Bool
  | .letBind dst ty val k =>
    ty.containsHeapObject || val.isRcAdtExpr ||
    k.containsRcAdt (if ty.containsHeapObject then dst :: objVars else objVars)
  | .rawStore _ _ _ ety k => ety.containsHeapObject || k.containsRcAdt objVars
  | .incRef ov _ k | .decRef ov _ k => objVars.contains ov || k.containsRcAdt objVars
  | .ite _ t e => t.containsRcAdt objVars || e.containsRcAdt objVars
  | .seqFor _ _ _ av _ aty step k =>
    let objVars' := if aty.containsHeapObject then av :: objVars else objVars
    aty.containsHeapObject || step.containsRcAdt objVars' || k.containsRcAdt objVars'
  | .parFor ov _ _ ety _ k =>
    let objVars' := if ety.containsHeapObject then ov :: objVars else objVars
    ety.containsHeapObject || k.containsRcAdt objVars'
  | .ret _ | .unreachable => false

/-- A decl is RC-ADT if a param, the return type, or its body touches a heap object (P-cert C4/C5 gate). -/
def LNIRDecl.containsRcAdt (d : LNIRDecl) : Bool :=
  let objParams := d.params.filter (fun p => p.ty.containsHeapObject) |>.map (·.id)
  !objParams.isEmpty || d.retTy.containsHeapObject || d.body.containsRcAdt objParams

def LNIRModule.findRcAdtDecl? (m : LNIRModule) : Option String :=
  (m.decls.find? (·.containsRcAdt)).map (·.name)

mutual
  /-- Whether an `LNIRType` is or contains a scalar-array (`.sarray _`) or raw-pointer (`.rawPtr _`) view. -/
  def LNIRType.containsSarray : LNIRType → Bool
    | .sarray _ | .rawPtr _ => true
    | .tuple fs => LNIRType.listContainsSarray fs
    | _ => false

  def LNIRType.listContainsSarray : List LNIRType → Bool
    | [] => false
    | t :: ts => t.containsSarray || LNIRType.listContainsSarray ts
end

private def exprContainsSarray : LNIRExpr → Bool
  | .sarrayLen _ | .sarrayDataPtr _ _ | .sarrayEnsureExclusive _ _
  | .sarrayGet _ _ _ | .sarraySet _ _ _ _ | .rawLoad _ _ _ => true
  | .call fn _ _ _ => fn == "lean_native_ensure_exclusive" || fn == "lean_native_sarray_len"
  | _ => false

private def codeContainsSarray : LNIRCode → Bool
  | .letBind _ ty rhs k => ty.containsSarray || exprContainsSarray rhs || codeContainsSarray k
  | .rawStore _ _ _ _ _ | .parFor _ _ _ _ _ _ => true
  | .incRef _ _ k | .decRef _ _ k => codeContainsSarray k
  | .ite _ t e => codeContainsSarray t || codeContainsSarray e
  | .seqFor _ _ _ _ _ aty step k => aty.containsSarray || codeContainsSarray step || codeContainsSarray k
  | .ret _ | .unreachable => false

/-- Whether `d` uses `.sarray`/`.rawPtr` parameters, returns, or operations (64-bit `lean_sarray_object` layout). -/
def LNIRDecl.containsSarray (d : LNIRDecl) : Bool :=
  d.params.any (fun p => p.ty.containsSarray) || d.retTy.containsSarray || codeContainsSarray d.body

private def elemTypeOfBufTy? : LNIRType → Option LNIRType
  | .sarray et | .rawPtr et => some et
  | _ => none

private def bindElemEnv? (env : List (VarId × LNIRType)) (v : VarId) (ty : LNIRType) : Option (List (VarId × LNIRType)) :=
  match env.lookup v with
  | some oldTy =>
    if oldTy.containsSarray || ty.containsSarray then
      if oldTy == ty then some ((v, ty) :: env.filter (·.1 != v)) else none
    else
      some ((v, ty) :: env.filter (·.1 != v))
  | none => some ((v, ty) :: env)

private def checkRetCompat (env : List (VarId × LNIRType)) (expectedTy : LNIRType) (v : VarId) : Option String :=
  match env.lookup v with
  | some actualTy =>
    if expectedTy.containsSarray || actualTy.containsSarray then
      if expectedTy == actualTy then none else some "inconsistent_elem_type"
    else none
  | none =>
    if expectedTy.containsSarray then some "inconsistent_elem_type" else none

private def scalarExprRefsBufVar (env : List (VarId × LNIRType)) : ScalarExpr → Bool
  | .constU64 _ | .constBool _ => false
  | .var id => match env.lookup id with | some t => t.containsSarray | none => false
  | .binOp _ l r => scalarExprRefsBufVar env l || scalarExprRefsBufVar env r
  | .unaryOp _ a => scalarExprRefsBufVar env a
  | .select c t e | .fma c t e =>
    scalarExprRefsBufVar env c || scalarExprRefsBufVar env t || scalarExprRefsBufVar env e

private def envVarHasSarray (env : List (VarId × LNIRType)) (v : VarId) : Bool :=
  match env.lookup v with
  | some t => t.containsSarray
  | none => false

private def checkCallArgsCompat (env : List (VarId × LNIRType))
    (localSigs : List (String × List LNIRType × LNIRType))
    (callee : String) (args : List VarId) (dstTy : LNIRType) : Option String :=
  let anyBufArg := args.any (envVarHasSarray env)
  let sig? := localSigs.find? (fun (nm, pTys, _) => nm == callee && pTys.length == args.length)
  if dstTy.containsSarray && !(sig?.any (fun (_, _, rTy) => rTy == dstTy)) then
    some "inconsistent_elem_type"
  else
    match sig? with
    | some (_, pTys, _) =>
      let rec go : List VarId → List LNIRType → Option String
        | [], [] => none
        | av :: avs, pt :: pts =>
          match checkRetCompat env pt av with
          | some err => some err
          | none => go avs pts
        | _, _ => some "inconsistent_elem_type"
      go args pTys
    | none =>
      if anyBufArg then some "inconsistent_elem_type" else none

private def checkExprElemTypes (env : List (VarId × LNIRType))
    (localSigs : List (String × List LNIRType × LNIRType))
    (dstTy : LNIRType) : LNIRExpr → Option String
  | .scalar (.var src) =>
    checkRetCompat env dstTy src
  | .scalar se =>
    if dstTy.containsSarray || scalarExprRefsBufVar env se then some "inconsistent_elem_type"
    else none
  | .mkTuple fields =>
    match dstTy with
    | .tuple fieldTys =>
      if fields.length != fieldTys.length then
        if dstTy.containsSarray || fields.any (envVarHasSarray env) then
          some "inconsistent_elem_type"
        else none
      else
        let rec checkFields : List VarId → List LNIRType → Option String
          | [], [] => none
          | fv :: fvs, ft :: fts =>
            if ft.containsSarray || envVarHasSarray env fv then
              if env.lookup fv == some ft then checkFields fvs fts else some "inconsistent_elem_type"
            else checkFields fvs fts
          | _, _ => some "inconsistent_elem_type"
        checkFields fields fieldTys
    | _ =>
      if dstTy.containsSarray || fields.any (envVarHasSarray env) then
        some "inconsistent_elem_type"
      else none
  | .projTuple tupleVar idx =>
    match env.lookup tupleVar with
    | some (.tuple fieldTys) =>
      match fieldTys[idx]? with
      | some fTy =>
        if dstTy.containsSarray || fTy.containsSarray then
          if dstTy == fTy then none else some "inconsistent_elem_type"
        else none
      | none => if dstTy.containsSarray then some "inconsistent_elem_type" else none
    | _ => if dstTy.containsSarray then some "inconsistent_elem_type" else none
  | .sarrayDataPtr av et =>
    if env.lookup av == some (.sarray et) && dstTy == .rawPtr et then none
    else some "inconsistent_elem_type"
  | .sarrayEnsureExclusive av et =>
    if env.lookup av == some (.sarray et) && dstTy == .sarray et then none
    else some "inconsistent_elem_type"
  | .sarrayGet av _ et =>
    if env.lookup av == some (.sarray et) && !dstTy.containsSarray then none
    else some "inconsistent_elem_type"
  | .sarraySet av _ vv et =>
    if env.lookup av == some (.sarray et) && dstTy == .sarray et &&
       !envVarHasSarray env vv then none
    else some "inconsistent_elem_type"
  | .rawLoad pv _ et =>
    if env.lookup pv == some (.rawPtr et) && !dstTy.containsSarray then none
    else some "inconsistent_elem_type"
  | .sarrayLen av | .isExclusive av =>
    if dstTy.containsSarray then some "inconsistent_elem_type"
    else
      match env.lookup av with
      | some (.tuple _) =>
        if envVarHasSarray env av then some "inconsistent_elem_type" else none
      | _ => none
  | .call fn args retTy isExt =>
    if !isExt && fn == "lean_native_ensure_exclusive" then
      match args with
      | [av] =>
        match dstTy, env.lookup av with
        | .sarray et, some (.sarray et2) =>
          if et == et2 && (retTy == dstTy || retTy == .objPtr) then none
          else some "inconsistent_elem_type"
        | .sarray _, _ => some "inconsistent_elem_type"
        | _, some (.sarray _) => some "inconsistent_elem_type"
        | _, _ =>
          if dstTy.containsSarray || envVarHasSarray env av then some "inconsistent_elem_type"
          else none
      | _ =>
        if dstTy.containsSarray || args.any (envVarHasSarray env) then some "inconsistent_elem_type"
        else none
    else if !isExt && fn == "lean_native_sarray_len" then
      match args with
      | [av] =>
        if dstTy.containsSarray then some "inconsistent_elem_type"
        else
          match env.lookup av with
          | some (.sarray _) => none
          | _ => if envVarHasSarray env av then some "inconsistent_elem_type" else none
      | _ =>
        if dstTy.containsSarray || args.any (envVarHasSarray env) then some "inconsistent_elem_type"
        else none
    else if isExt then
      if dstTy.containsSarray || args.any (envVarHasSarray env) then some "inconsistent_elem_type"
      else none
    else
      checkCallArgsCompat env
        (("lean_native_sarray_uget64_le", [.sarray .i8, .usize], .i64) ::
         ("lean_native_sarray_uset64_le", [.sarray .i8, .usize, .i64], .sarray .i8) ::
         ("lean_native_gf2_affine64", [.i64, .i64, .i64], .i64) ::
         ("lean_native_ternary_logic64", [.i64, .i64, .i64, .i64], .i64) :: localSigs)
        fn args dstTy
  | .allocCtor _ ofs sfs =>
    if dstTy.containsSarray || sfs.any (envVarHasSarray env) ||
       ofs.any (fun fv => match env.lookup fv with | some (.tuple _) => envVarHasSarray env fv | some (.rawPtr _) => true | _ => false) then
      some "inconsistent_elem_type"
    else none
  | .mulDivDown a b d | .mulDivUp a b d =>
    if dstTy.containsSarray || envVarHasSarray env a || envVarHasSarray env b || envVarHasSarray env d then
      some "inconsistent_elem_type"
    else none
  | .storageLoad m s =>
    if dstTy.containsSarray || envVarHasSarray env m || envVarHasSarray env s then
      some "inconsistent_elem_type"
    else none
  | .storageStore m s v =>
    if dstTy.containsSarray || envVarHasSarray env m || envVarHasSarray env s || envVarHasSarray env v then
      some "inconsistent_elem_type"
    else none
  | .ctorGetObj v _ | .ctorGetScalar v _ _ | .boxScalar v _ | .unboxScalar v _ =>
    if dstTy.containsSarray || envVarHasSarray env v then some "inconsistent_elem_type"
    else none
  | .constU256 _ =>
    if dstTy.containsSarray then some "inconsistent_elem_type" else none

private partial def checkCodeElemTypes (env : List (VarId × LNIRType))
    (localSigs : List (String × List LNIRType × LNIRType))
    (expectedRetTy : LNIRType) :
    LNIRCode → Option String
  | .letBind dst ty rhs k =>
    checkExprElemTypes env localSigs ty rhs <|>
      match bindElemEnv? env dst ty with
      | some env' => checkCodeElemTypes env' localSigs expectedRetTy k
      | none => some "inconsistent_elem_type"
  | .rawStore pv _ vv et k =>
    if env.lookup pv == some (.rawPtr et) && !envVarHasSarray env vv then
      checkCodeElemTypes env localSigs expectedRetTy k
    else
      some "inconsistent_elem_type"
  | .incRef _ _ k | .decRef _ _ k => checkCodeElemTypes env localSigs expectedRetTy k
  | .ite _ t e =>
    checkCodeElemTypes env localSigs expectedRetTy t <|> checkCodeElemTypes env localSigs expectedRetTy e
  | .seqFor idxVar _ _ accVar accInit accTy step k =>
    match checkRetCompat env accTy accInit with
    | some err => some err
    | none =>
      match bindElemEnv? env idxVar .i64 >>= fun e1 => bindElemEnv? e1 accVar accTy with
      | some stepEnv =>
        checkCodeElemTypes stepEnv localSigs accTy step <|>
          match bindElemEnv? env accVar accTy with
          | some contEnv => checkCodeElemTypes contEnv localSigs expectedRetTy k
          | none => some "inconsistent_elem_type"
      | none => some "inconsistent_elem_type"
  | .parFor outVar _ inputs et _ k =>
    if !(inputs.all fun iv => env.lookup iv == some (.sarray et)) then
      some "inconsistent_elem_type"
    else
      match bindElemEnv? env outVar (.sarray et) with
      | some env' => checkCodeElemTypes env' localSigs expectedRetTy k
      | none => some "inconsistent_elem_type"
  | .ret v => checkRetCompat env expectedRetTy v
  | .unreachable => none

/-- Check that all `.sarray`/`.rawPtr` bindings, loop-carried accumulators, calls, tuples, returns,
    and element-typed operations in `d` agree on `elemTy` (optionally against `localSigs` of the enclosing module). -/
def LNIRDecl.checkElemTypes (d : LNIRDecl)
    (localSigs : List (String × List LNIRType × LNIRType) := []) : Option String :=
  let initEnv? := d.params.foldlM (fun acc p => bindElemEnv? acc p.id p.ty) []
  match initEnv? with
  | none => some "inconsistent_elem_type"
  | some env => checkCodeElemTypes env localSigs d.retTy d.body

/-- Count AST nodes in `LNIRCode` (shared by `EqSat` and `SymbolicTV` budget guards). -/
def LNIRCode.nodeSize : LNIRCode → Nat
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k
  | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    1 + k.nodeSize
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e =>
    1 + t.nodeSize + e.nodeSize
  | .ret _ | .unreachable => 1

/-- Simultaneous variable renaming across a `ScalarExpr`. -/
def ScalarExpr.rewriteSubst (subst : List (VarId × VarId)) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var ((subst.lookup id).getD id)
  | .binOp op l r => .binOp op (l.rewriteSubst subst) (r.rewriteSubst subst)
  | .unaryOp op a => .unaryOp op (a.rewriteSubst subst)
  | .select c t e =>
    .select (c.rewriteSubst subst) (t.rewriteSubst subst) (e.rewriteSubst subst)
  | .fma a b c =>
    .fma (a.rewriteSubst subst) (b.rewriteSubst subst) (c.rewriteSubst subst)

/-- Simultaneous variable renaming across an `LNIRExpr`. -/
def LNIRExpr.rewriteSubst (subst : List (VarId × VarId)) : LNIRExpr → LNIRExpr :=
  let rw (v : VarId) : VarId := (subst.lookup v).getD v
  fun
  | .scalar se => .scalar (se.rewriteSubst subst)
  | .constU256 w => .constU256 w
  | .mulDivDown a b d => .mulDivDown (rw a) (rw b) (rw d)
  | .mulDivUp a b d => .mulDivUp (rw a) (rw b) (rw d)
  | .storageLoad m s => .storageLoad (rw m) (rw s)
  | .storageStore m s v => .storageStore (rw m) (rw s) (rw v)
  | .mkTuple fs => .mkTuple (fs.map rw)
  | .projTuple tv idx => .projTuple (rw tv) idx
  | .allocCtor tag ofs sfs => .allocCtor tag (ofs.map rw) (sfs.map rw)
  | .ctorGetObj cv idx => .ctorGetObj (rw cv) idx
  | .ctorGetScalar cv idx ty => .ctorGetScalar (rw cv) idx ty
  | .isExclusive ov => .isExclusive (rw ov)
  | .sarrayLen av => .sarrayLen (rw av)
  | .sarrayDataPtr av et => .sarrayDataPtr (rw av) et
  | .sarrayEnsureExclusive av et => .sarrayEnsureExclusive (rw av) et
  | .sarrayGet av iv et => .sarrayGet (rw av) (rw iv) et
  | .sarraySet av iv vv et => .sarraySet (rw av) (rw iv) (rw vv) et
  | .rawLoad pv iv et => .rawLoad (rw pv) (rw iv) et
  | .boxScalar vv ty => .boxScalar (rw vv) ty
  | .unboxScalar bv ty => .unboxScalar (rw bv) ty
  | .call fn args rty ext => .call fn (args.map rw) rty ext

/-- Capture-avoiding binder freshening and substitution across `LNIRCode`
    (shared by `EqSat` branch cloning and `SymbolicTV` local-call inlining). -/
def LNIRCode.freshenBinders : LNIRCode → List (VarId × VarId) → StateM VarId LNIRCode
  | .letBind dst ty val k, subst => do
    let val' := val.rewriteSubst subst
    let fDst ← get
    set (fDst + 1)
    return .letBind fDst ty val' (← k.freshenBinders ((dst, fDst) :: subst))
  | .rawStore pv iv vv et k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    return .rawStore (rw pv) (rw iv) (rw vv) et (← k.freshenBinders subst)
  | .incRef ov c k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    return .incRef (rw ov) c (← k.freshenBinders subst)
  | .decRef ov c k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    return .decRef (rw ov) c (← k.freshenBinders subst)
  | .ite cv t e, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    return .ite (rw cv) (← t.freshenBinders subst) (← e.freshenBinders subst)
  | .seqFor iv lv hv av ai aty step k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    let fIv ← get
    let fAv := fIv + 1
    set (fIv + 2)
    let step' ← step.freshenBinders ((av, fAv) :: (iv, fIv) :: subst)
    let k' ← k.freshenBinders ((av, fAv) :: subst)
    return .seqFor fIv (rw lv) (rw hv) fAv (rw ai) aty step' k'
  | .parFor ov lv ins et kern k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    let fOv ← get
    set (fOv + 1)
    let kern' ← match kern with
      | .customScalar idxVar inVars body => do
        let fIdx ← get
        let fIns := (List.range inVars.length).map (fun i => fIdx + 1 + i)
        set (fIdx + 1 + inVars.length)
        let kSubst := (inVars.zip fIns) ++ ((idxVar, fIdx) :: subst)
        pure (.customScalar fIdx fIns (body.rewriteSubst kSubst))
      | other => pure other
    return .parFor fOv (rw lv) (ins.map rw) et kern' (← k.freshenBinders ((ov, fOv) :: subst))
  | .ret v, subst => return .ret ((subst.lookup v).getD v)
  | .unreachable, _ => return .unreachable

end LeanNative.IR
