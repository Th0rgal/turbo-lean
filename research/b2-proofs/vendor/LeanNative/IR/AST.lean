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

/-- Top-level function declaration in LNIR. -/
structure LNIRDecl where
  name       : String
  params     : List LNIRParam
  retTy      : LNIRType
  body       : LNIRCode
  assurance  : AssuranceLevel := .verifiedKernelProof
  isGpuCand  : Bool := false
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

/-- Alpha-canonicalized de Bruijn representation of an `LNIRDecl` for `modded-nanogpt` training. -/
def LNIRDecl.canonicalDeBruijn (d : LNIRDecl) : LNIRDecl :=
  let initCtx := (d.params.map (·.id)).reverse
  let params' := (List.range d.params.length).zip d.params |>.map fun (idx, p) =>
    { p with id := idx, name := s!"p{idx}" }
  { d with params := params', body := d.body.canonicalDeBruijn initCtx }

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

end LeanNative.IR
