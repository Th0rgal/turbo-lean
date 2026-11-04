import LeanNative.IR.AST
import LeanNative.Backend.PTXAst

/-!
# Typed LNIR → PTX 8.0 lowering (`LeanNative.Backend.PTXLower`)

Total, structural lowering of `ScalarExpr` / `ParallelKernelKind` into the typed
`PTXAst` consumed by `evalPTXKernel`. Register banks match the evaluator's
declared-width checks: `.b64` lives in `%rd*`, shift amounts and `clz.b64`
results live in `%r*` (32-bit), predicates live in `%p*`. Division by zero,
shifts, and `clz256` follow `LeanNative.Semantics.evalBinOp` / `evalUnaryOp`.
-/

namespace LeanNative.Backend.PTXLower

open LeanNative.IR
open LeanNative.Backend.PTXAst

inductive PReg where
  | rd : Nat → PReg
  | r : Nat → PReg
  deriving Repr, DecidableEq, Inhabited, BEq

def PReg.name : PReg → String
  | .rd n => s!"%rd{n}"
  | .r n => s!"%r{n}"

def PReg.bank : PReg → Nat
  | .rd _ => 0
  | .r _ => 1

structure PEnv where
  nextRd : Nat := 0
  nextR : Nat := 0
  nextP : Nat := 1
  deriving Repr, DecidableEq, Inhabited, BEq

def freshRd (e : PEnv) : PReg × PEnv :=
  (.rd e.nextRd, { e with nextRd := e.nextRd + 1 })

def freshR (e : PEnv) : PReg × PEnv :=
  (.r e.nextR, { e with nextR := e.nextR + 1 })

def freshP (e : PEnv) : String × PEnv :=
  (s!"%p{e.nextP}", { e with nextP := e.nextP + 1 })

def i64 (n : Nat) : PTXOperand := .immU64 (BitVec.ofNat 64 n)

def iOp (p : PReg) : PTXOperand := .reg p.name

def ins (i : PTXInstr) : PTXStmt := .instr none i

def lowerScalar (varOf : Nat → Option PReg) (e0 : PEnv) :
    ScalarExpr → List PTXStmt × PReg × PEnv
  | .constU64 v =>
    let (d, e1) := freshRd e0
    ([ins (.mov .u64 d.name (.immU64 v.toBitVec))], d, e1)
  | .constBool b =>
    let (d, e1) := freshRd e0
    ([ins (.mov .u64 d.name (i64 (if b then 1 else 0)))], d, e1)
  | .var id =>
    match varOf id with
    | some p => ([], p, e0)
    | none =>
      let (d, e1) := freshRd e0
      ([ins (.mov .u64 d.name (i64 0))], d, e1)
  | .binOp op lhs rhs =>
    let (ll, lr, e1) := lowerScalar varOf e0 lhs
    let (rl, rr, e2) := lowerScalar varOf e1 rhs
    let (d, e3) := freshRd e2
    let lo := iOp lr
    let ro := iOp rr
    let arith (i : PTXInstr) : List PTXStmt × PReg × PEnv :=
      (ll ++ rl ++ [ins i], d, e3)
    match op with
    | .add | .addChecked256 => arith (.add .none .u64 d.name lo ro)
    | .sub | .subChecked256 => arith (.sub .u64 d.name lo ro)
    | .mul | .mulChecked256 => arith (.mul .lo .u64 d.name lo ro)
    | .div =>
      let (p, e4) := freshP e3
      (ll ++ rl ++ [
        ins (.setp .eq .u64 p ro (i64 0)),
        ins (.selp .u64 d.name (i64 1) ro p),
        ins (.div .u64 d.name lo (iOp d)),
        ins (.selp .u64 d.name (i64 0) (iOp d) p)
      ], d, e4)
    | .mod =>
      let (p, e4) := freshP e3
      (ll ++ rl ++ [
        ins (.setp .eq .u64 p ro (i64 0)),
        ins (.selp .u64 d.name (i64 1) ro p),
        ins (.rem .u64 d.name lo (iOp d)),
        ins (.selp .u64 d.name lo (iOp d) p)
      ], d, e4)
    | .bitAnd => arith (.bitAnd .b64 d.name lo ro)
    | .bitOr => arith (.bitOr .b64 d.name lo ro)
    | .bitXor => arith (.bitXor .b64 d.name lo ro)
    | .shl | .shr | .sar =>
      let (sh, e4) := freshR e3
      let (msk, e5) := freshR e4
      let opI := match op with
        | .shl => .shl .b64 d.name lo (iOp msk)
        | .sar => .shr .s64 d.name lo (iOp msk)
        | _ => .shr .u64 d.name lo (iOp msk)
      (ll ++ rl ++ [
        ins (.cvt .none .u32 .u64 sh.name ro),
        ins (.bitAnd .b32 msk.name (iOp sh) (.immU64 63#64)),
        ins opI
      ], d, e5)
    | .eq | .lt | .le =>
      let (p, e4) := freshP e3
      let cmp := match op with | .lt => PTXCmpOp.lt | .le => .le | _ => .eq
      (ll ++ rl ++ [
        ins (.setp cmp .u64 p lo ro),
        ins (.selp .u64 d.name (i64 1) (i64 0) p)
      ], d, e4)
    | .clmul64 | .clmul64Hi =>
      let (bit, e4) := freshRd e3
      let (sh, e5) := freshRd e4
      let hi := op == .clmul64Hi
      let start := if hi then 1 else 0
      let steps := (List.range (64 - start)).foldl (fun acc k =>
        let i := start + k
        let bitI := if i == 0 then ins (.mov .u64 bit.name ro)
          else ins (.shr .u64 bit.name ro (i64 i))
        let shI := if hi then ins (.shr .u64 sh.name lo (i64 (64 - i)))
          else if i == 0 then ins (.mov .u64 sh.name lo)
          else ins (.shl .b64 sh.name lo (i64 i))
        acc ++ [bitI, ins (.bitAnd .b64 bit.name (iOp bit) (i64 1)),
          ins (.neg .s64 bit.name (iOp bit)), shI,
          ins (.bitAnd .b64 sh.name (iOp sh) (iOp bit)),
          ins (.bitXor .b64 d.name (iOp d) (iOp sh))]) [ins (.mov .u64 d.name (i64 0))]
      (ll ++ rl ++ steps, d, e5)
    | .gf2Affine =>
      let (t0, e4) := freshRd e3
      let (t1, e5) := freshRd e4
      let steps := (List.range 8).foldl (fun acc i =>
        let row := if i == 0 then ins (.mov .u64 t0.name ro)
          else ins (.shr .u64 t0.name ro (i64 (i * 8)))
        let place := if i == 0 then [] else [ins (.shl .b64 t0.name (iOp t0) (i64 i))]
        acc ++ [row, ins (.bitAnd .b64 t0.name (iOp t0) lo),
          ins (.bitAnd .b64 t0.name (iOp t0) (i64 255)),
          ins (.shr .u64 t1.name (iOp t0) (i64 4)),
          ins (.bitXor .b64 t0.name (iOp t0) (iOp t1)),
          ins (.shr .u64 t1.name (iOp t0) (i64 2)),
          ins (.bitXor .b64 t0.name (iOp t0) (iOp t1)),
          ins (.shr .u64 t1.name (iOp t0) (i64 1)),
          ins (.bitXor .b64 t0.name (iOp t0) (iOp t1)),
          ins (.bitAnd .b64 t0.name (iOp t0) (i64 1))] ++ place ++
          [ins (.bitOr .b64 d.name (iOp d) (iOp t0))]) [ins (.mov .u64 d.name (i64 0))]
      (ll ++ rl ++ steps, d, e5)
    | .eor3 =>
      let (t0, e4) := freshRd e3
      (ll ++ rl ++ [
        ins (.shr .u64 t0.name ro (i64 32)),
        ins (.bitXor .b64 d.name lo (iOp t0)),
        ins (.bitAnd .b64 t0.name ro (i64 4294967295)),
        ins (.bitXor .b64 d.name (iOp d) (iOp t0))
      ], d, e4)
  | .unaryOp op arg =>
    let (al, ar, e1) := lowerScalar varOf e0 arg
    let (d, e2) := freshRd e1
    match op with
    | .not => (al ++ [ins (.bitNot .b64 d.name (iOp ar))], d, e2)
    | .neg => (al ++ [ins (.neg .s64 d.name (iOp ar))], d, e2)
    | .clz256 =>
      let (c32, e3) := freshR e2
      (al ++ [
        ins (.clz .b64 c32.name (iOp ar)),
        ins (.cvt .none .u64 .u32 d.name (iOp c32)),
        ins (.add .none .u64 d.name (iOp d) (i64 192))
      ], d, e3)
  | .select c t f =>
    let (cl, cr, e1) := lowerScalar varOf e0 c
    let (tl, tr, e2) := lowerScalar varOf e1 t
    let (fl, fr, e3) := lowerScalar varOf e2 f
    let (p, e4) := freshP e3
    let (d, e5) := freshRd e4
    (cl ++ tl ++ fl ++ [
      ins (.setp .ne .u64 p (iOp cr) (i64 0)),
      ins (.selp .u64 d.name (iOp tr) (iOp fr) p)
    ], d, e5)
  | .fma a b c =>
    let (al, ar, e1) := lowerScalar varOf e0 a
    let (bl, br, e2) := lowerScalar varOf e1 b
    let (cl, cr, e3) := lowerScalar varOf e2 c
    let (d, e4) := freshRd e3
    (al ++ bl ++ cl ++ [ins (.mad .lo .u64 d.name (iOp ar) (iOp br) (iOp cr))], d, e4)

def gidSetup (doneLbl : String) : List PTXStmt :=
  [ ins (.mov .u32 "%r0" (.sreg .ctaidX))
  , ins (.mov .u32 "%r1" (.sreg .ntidX))
  , ins (.mov .u32 "%r2" (.sreg .tidX))
  , ins (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
  , ins (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
  , ins (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
  , ins (.ldParam .u64 "%rd3" "param_n")
  , ins (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
  , .instr (some { predReg := "%p0" }) (.bra doneLbl)
  , ins (.ldParam .u64 "%rd4" "param_out")
  , ins (.cvtaToGlobal .u64 "%rd4" (.reg "%rd4"))
  , ins (.shl .b64 "%rd5" (.reg "%rd2") (i64 3))
  , ins (.add .none .u64 "%rd6" (.reg "%rd4") (.reg "%rd5")) ]

/-- Same preamble as `gidSetup`, but the `setp.ge` / `bra` guard is omitted when a
retained `idxLt idxVar lenVar` covers every launched lane (`grid.x * block.x ≤ n`). -/
def gidSetupWithFacts (doneLbl : String) (facts : List RetainedFact)
    (idxVar : VarId := 0) (lenVar : VarId := 1) : List PTXStmt :=
  if !factMember facts (.idxLt idxVar lenVar) then gidSetup doneLbl
  else
    [ ins (.mov .u32 "%r0" (.sreg .ctaidX))
    , ins (.mov .u32 "%r1" (.sreg .ntidX))
    , ins (.mov .u32 "%r2" (.sreg .tidX))
    , ins (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
    , ins (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
    , ins (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
    , ins (.ldParam .u64 "%rd3" "param_n")
    , ins (.ldParam .u64 "%rd4" "param_out")
    , ins (.cvtaToGlobal .u64 "%rd4" (.reg "%rd4"))
    , ins (.shl .b64 "%rd5" (.reg "%rd2") (i64 3))
    , ins (.add .none .u64 "%rd6" (.reg "%rd4") (.reg "%rd5")) ]

def loadIn (k : Nat) (reg : String) : List PTXStmt :=
  [ ins (.ldParam .u64 reg s!"param_in{k}")
  , ins (.cvtaToGlobal .u64 reg (.reg reg))
  , ins (.add .none .u64 reg (.reg reg) (.reg "%rd5"))
  , ins (.ldGlobal .u64 reg (.regOffset reg 0)) ]

def kernelOf (name : String) (nIn : Nat) (env : PEnv) (body : List PTXStmt) : PTXKernel where
  name := name
  params := { ty := .u64, name := "param_out" } ::
    (List.range nIn).map (fun i => { ty := .u64, name := s!"param_in{i}" }) ++
    [{ ty := .u64, name := "param_n" }]
  regDecls :=
    [ { ty := .pred, prefixName := "%p", count := env.nextP }
    , { ty := .u32, prefixName := "%r", count := Nat.max 3 env.nextR }
    , { ty := .u64, prefixName := "%rd", count := Nat.max 7 env.nextRd } ]
  body := body ++ [.label s!"$L_done_{name}", ins .ret]

def baseEnv (extraRd : Nat) : PEnv := { nextRd := 7 + extraRd, nextR := 3, nextP := 1 }

def customVarOf (idxVar : Nat) (inVars : List VarId) (id : Nat) : Option PReg :=
  if id == idxVar then some (.rd 2)
  else match inVars.idxOf? id with
    | some k => some (.rd (7 + k))
    | none => none

def lowerKind (name : String) : ParallelKernelKind → PTXKernel
  | .mapScaleAdd scale bias =>
    let e0 := baseEnv 1
    let body := gidSetup s!"$L_done_{name}" ++ loadIn 0 "%rd7" ++ [
      ins (.mad .lo .u64 "%rd8" (.reg "%rd7") (.immU64 scale.toBitVec) (.immU64 bias.toBitVec)),
      ins (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg "%rd8")) ]
    kernelOf name 1 { e0 with nextRd := 9 } body
  | .zipAdd =>
    let body := gidSetup s!"$L_done_{name}" ++ loadIn 0 "%rd7" ++ loadIn 1 "%rd8" ++ [
      ins (.add .none .u64 "%rd9" (.reg "%rd7") (.reg "%rd8")),
      ins (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg "%rd9")) ]
    kernelOf name 2 { baseEnv 2 with nextRd := 10 } body
  | .zipMul =>
    let body := gidSetup s!"$L_done_{name}" ++ loadIn 0 "%rd7" ++ loadIn 1 "%rd8" ++ [
      ins (.mul .lo .u64 "%rd9" (.reg "%rd7") (.reg "%rd8")),
      ins (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg "%rd9")) ]
    kernelOf name 2 { baseEnv 2 with nextRd := 10 } body
  | .dotProduct =>
    -- Rejected by `wfPTXKernel` and `lowerDeclToPTX` (dotProduct is a reduction, not 1-D map).
    { name := name, params := [], regDecls := [], body := [ins .ret] }
  | .saxpy alpha =>
    let body := gidSetup s!"$L_done_{name}" ++ loadIn 0 "%rd7" ++ loadIn 1 "%rd8" ++ [
      ins (.mad .lo .u64 "%rd9" (.reg "%rd7") (.immU64 alpha.toBitVec) (.reg "%rd8")),
      ins (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg "%rd9")) ]
    kernelOf name 2 { baseEnv 2 with nextRd := 10 } body
  | .stencil1D3Pt wL wC wR =>
    let done := s!"$L_done_{name}"
    let bnd := s!"$L_boundary_{name}"
    let body := gidSetup done ++ [
      ins (.ldParam .u64 "%rd8" "param_in0"),
      ins (.cvtaToGlobal .u64 "%rd8" (.reg "%rd8")),
      ins (.add .none .u64 "%rd8" (.reg "%rd8") (.reg "%rd5")),
      ins (.ldGlobal .u64 "%rd7" (.regOffset "%rd8" 0)),
      ins (.setp .eq .u64 "%p1" (.reg "%rd2") (i64 0)),
      ins (.add .none .u64 "%rd9" (.reg "%rd2") (i64 1)),
      ins (.setp .ge .u64 "%p2" (.reg "%rd9") (.reg "%rd3")),
      ins (.bitOr .pred "%p1" (.reg "%p1") (.reg "%p2")),
      .instr (some { predReg := "%p1" }) (.bra bnd),
      ins (.ldGlobal .u64 "%rd10" (.regOffset "%rd8" (-8))),
      ins (.ldGlobal .u64 "%rd11" (.regOffset "%rd8" 8)),
      ins (.mul .lo .u64 "%rd12" (.reg "%rd10") (.immU64 wL.toBitVec)),
      ins (.mad .lo .u64 "%rd12" (.reg "%rd7") (.immU64 wC.toBitVec) (.reg "%rd12")),
      ins (.mad .lo .u64 "%rd7" (.reg "%rd11") (.immU64 wR.toBitVec) (.reg "%rd12")),
      .label bnd,
      ins (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg "%rd7")) ]
    kernelOf name 1 { nextRd := 13, nextR := 3, nextP := 3 } body
  | .customScalar idxVar inVars bodyExpr =>
    let loads := (List.range inVars.length).foldl (fun acc k => acc ++ loadIn k s!"%rd{7 + k}") []
    let (el, res, env) := lowerScalar (customVarOf idxVar inVars) (baseEnv inVars.length) bodyExpr
    let body := gidSetup s!"$L_done_{name}" ++ loads ++ el ++
      [ins (.stGlobal .u64 (.regOffset "%rd6" 0) (iOp res))]
    kernelOf name inVars.length env body

def lowerToPTX (name : String) (k : ParallelKernelKind) : PTXModule where
  kernels := [lowerKind name k]

/-- Fact-carrying twin of `lowerKind`: a retained `idxLt idxVar lenVar` drops the lane guard. -/
def lowerKindWithFacts (name : String) (facts : List RetainedFact)
    (k : ParallelKernelKind) (idxVar : VarId := 0) (lenVar : VarId := 1) : PTXKernel :=
  match k with
  | .dotProduct => lowerKind name .dotProduct
  | _ =>
    let base := lowerKind name k
    let effIdx := match k with | .customScalar iv _ _ => iv | _ => idxVar
    if !factMember facts (.idxLt effIdx lenVar) then base
    else { base with body := gidSetupWithFacts s!"$L_done_{name}" facts effIdx lenVar ++
        (base.body.drop (gidSetup s!"$L_done_{name}").length) }

def lowerToPTXWithFacts (name : String) (facts : List RetainedFact)
    (k : ParallelKernelKind) (idxVar : VarId := 0) (lenVar : VarId := 1) : PTXModule where
  kernels := [lowerKindWithFacts name facts k idxVar lenVar]

def ppLowered (name : String) (k : ParallelKernelKind) : String :=
  ppPTXModule (lowerToPTX name k)

def inferBinOpU64 : BinOp → Option Bool
  | .add => some false | .sub => some false | .mul => some false
  | .div => some false | .mod => some false | .bitAnd => some false
  | .bitOr => some false | .bitXor => some false | .shl => some false
  | .shr => some false | .sar => some false | .eor3 => some false
  | .eq => some true | .lt => some true | .le => some true
  | .addChecked256 => none | .subChecked256 => none | .mulChecked256 => none
  | .clmul64 => none | .clmul64Hi => none | .gf2Affine => none

def inferBinOpBool : BinOp → Option Bool
  | .eq => some true
  | .bitAnd => none | .bitOr => none
  | .add => none | .sub => none | .mul => none | .div => none | .mod => none
  | .bitXor => none | .shl => none | .shr => none | .sar => none
  | .lt => none | .le => none
  | .addChecked256 => none | .subChecked256 => none | .mulChecked256 => none
  | .clmul64 => none | .clmul64Hi => none | .gf2Affine => none | .eor3 => none

def inferUnaryOpU64 : UnaryOp → Option Bool
  | .not => some false | .neg => some false | .clz256 => none

def inferScalarSort (boundVars : List Nat) : ScalarExpr → Option Bool
  | .constU64 _ => some false
  | .constBool _ => some true
  | .var id => if id ∈ boundVars then some false else none
  | .binOp op l r =>
    match inferScalarSort boundVars l with
    | some sl =>
      match inferScalarSort boundVars r with
      | some sr =>
        if !sl && !sr then inferBinOpU64 op
        else if sl && sr then inferBinOpBool op
        else none
      | none => none
    | none => none
  | .unaryOp op a =>
    match inferScalarSort boundVars a with
    | some sa => if !sa then inferUnaryOpU64 op else none
    | none => none
  | .select c t f =>
    match inferScalarSort boundVars c with
    | some _ =>
      match inferScalarSort boundVars t with
      | some st =>
        match inferScalarSort boundVars f with
        | some sf => if st == sf then some st else none
        | none => none
      | none => none
    | none => none
  | .fma a b c =>
    match inferScalarSort boundVars a with
    | some sa =>
      match inferScalarSort boundVars b with
      | some sb =>
        match inferScalarSort boundVars c with
        | some sc => if !sa && !sb && !sc then some false else none
        | none => none
      | none => none
    | none => none

def kernelArity : ParallelKernelKind → Nat
  | .mapScaleAdd _ _ | .stencil1D3Pt _ _ _ => 1
  | .zipAdd | .zipMul | .dotProduct | .saxpy _ => 2
  | .customScalar _ inVars _ => inVars.length

def wfPTXKernel : ParallelKernelKind → Bool
  | .mapScaleAdd _ _ | .zipAdd | .zipMul | .saxpy _ | .stencil1D3Pt _ _ _ => true
  | .dotProduct => false
  | .customScalar idxVar inVars body =>
    decide (inVars.Nodup ∧ idxVar ∉ inVars) && (inferScalarSort (idxVar :: inVars) body).isSome

/-- Extract `(lenVar, inputs, kernel)` from a GPU 1-D `parFor` declaration body
(`parFor outVar lenVar inputs .i64 k (ret outVar)` or preceded by `let lenVar = sarrayLen arrVar`). -/
def extractDeclParFor : LNIRCode → Option (Option VarId × VarId × List VarId × ParallelKernelKind)
  | .parFor outVar lenVar inputs .i64 k (.ret retVar) =>
    if outVar == retVar then some (none, lenVar, inputs, k) else none
  | .letBind lenVar .i64 (.sarrayLen arrVar) (.parFor outVar lenVar' inputs .i64 k (.ret retVar)) =>
    if lenVar == lenVar' && outVar == retVar then some (some arrVar, lenVar, inputs, k) else none
  | _ => none

/-- Lower a top-level `LNIRDecl` containing a well-formed 1-D `parFor` kernel into a `PTXModule`
(`.dotProduct` reductions and ill-typed kernels return `none`). -/
def isSarrayI64 : LNIRType → Bool
  | .sarray .i64 => true
  | _ => false

def lowerDeclToPTX (d : LNIRDecl) : Option PTXModule :=
  if isSarrayI64 d.retTy then
    match extractDeclParFor d.body with
    | some (_, _, inputs, k) =>
      if wfPTXKernel k && inputs.length == kernelArity k then
        some (lowerToPTX s!"lean_native_decl_{d.name}" k)
      else none
    | none => none
  else none

def lowerDeclToPTXWithFacts (d : LNIRDecl) (idxVar : VarId := 0) : Option PTXModule :=
  if isSarrayI64 d.retTy then
    match extractDeclParFor d.body with
    | some (_, lenVar, inputs, k) =>
      if wfPTXKernel k && inputs.length == kernelArity k then
        some (lowerToPTXWithFacts s!"lean_native_decl_{d.name}" d.retainedFacts k idxVar lenVar)
      else none
    | none => none
  else none

def concatPTXMems : List ByteMemory → ByteMemory
  | [] => { bytes := #[] }
  | m :: ms => { bytes := m.bytes ++ (concatPTXMems ms).bytes }

def mkPTXGlobalMem (inWords : List (List (BitVec 64))) (nIn len : Nat) : ByteMemory :=
  concatPTXMems (((List.range nIn).map fun j => ByteMemory.ofU64Words (inWords[j]?.getD [])) ++
    [ByteMemory.zeros (len * 8)])

def mkPTXParamMem (nIn len : Nat) : ParamMemory :=
  { params := ("param_out", BitVec.ofNat 64 (nIn * len * 8)) ::
      (List.range nIn).map (fun j => (s!"param_in{j}", BitVec.ofNat 64 (j * len * 8))) ++
      [("param_n", BitVec.ofNat 64 len)] }

def maxMidStepsForKind : ParallelKernelKind → Nat
  | .mapScaleAdd _ _ => 5
  | .zipAdd | .zipMul | .dotProduct | .saxpy _ => 9
  | .stencil1D3Pt _ _ _ => 15
  | .customScalar idxVar inVars bodyExpr =>
    4 * inVars.length +
      (lowerScalar (customVarOf idxVar inVars) (baseEnv inVars.length) bodyExpr).1.length

def ctaStepsForKind (blockSize : Nat) (k : ParallelKernelKind) : Nat :=
  blockSize * (16 + maxMidStepsForKind k) + 1

/-- `M7` mutant of `lowerScalar`: swaps `.sub` operands `lo, ro` → `ro, lo`
    (`sub.u64 dst, rReg, lReg;`, matching `MLIRGPU.lean` mutant `M7`). -/
def ptxMutantM7Scalar (varOf : Nat → Option PReg) (e0 : PEnv) :
    ScalarExpr → List PTXStmt × PReg × PEnv
  | .binOp .sub lhs rhs =>
    let (ll, lr, e1) := lowerScalar varOf e0 lhs
    let (rl, rr, e2) := lowerScalar varOf e1 rhs
    let (d, e3) := freshRd e2
    (ll ++ rl ++ [ins (.sub .u64 d.name (iOp rr) (iOp lr))], d, e3)
  | e => lowerScalar varOf e0 e

def ptxMutantM7Kernel (name : String) (idxVar : Nat) (inVars : List VarId)
    (bodyExpr : ScalarExpr) : PTXKernel :=
  let loads := (List.range inVars.length).foldl (fun acc k => acc ++ loadIn k s!"%rd{7 + k}") []
  let (el, res, env) := ptxMutantM7Scalar (customVarOf idxVar inVars) (baseEnv inVars.length) bodyExpr
  let body := gidSetup s!"$L_done_{name}" ++ loads ++ el ++
    [ins (.stGlobal .u64 (.regOffset "%rd6" 0) (iOp res))]
  kernelOf name inVars.length env body

/-- `M8` mutant of `lowerScalar`: weakens `.lt` predicate from `setp.lt.u64` to `setp.le.u64`
    (matching `MLIRGPU.lean` mutant `M8`). -/
def ptxMutantM8Scalar (varOf : Nat → Option PReg) (e0 : PEnv) :
    ScalarExpr → List PTXStmt × PReg × PEnv
  | .binOp .lt lhs rhs =>
    let (ll, lr, e1) := lowerScalar varOf e0 lhs
    let (rl, rr, e2) := lowerScalar varOf e1 rhs
    let (d, e3) := freshRd e2
    let (p, e4) := freshP e3
    (ll ++ rl ++ [
      ins (.setp .le .u64 p (iOp lr) (iOp rr)),
      ins (.selp .u64 d.name (i64 1) (i64 0) p)
    ], d, e4)
  | e => lowerScalar varOf e0 e

def ptxMutantM8Kernel (name : String) (idxVar : Nat) (inVars : List VarId)
    (bodyExpr : ScalarExpr) : PTXKernel :=
  let loads := (List.range inVars.length).foldl (fun acc k => acc ++ loadIn k s!"%rd{7 + k}") []
  let (el, res, env) := ptxMutantM8Scalar (customVarOf idxVar inVars) (baseEnv inVars.length) bodyExpr
  let body := gidSetup s!"$L_done_{name}" ++ loads ++ el ++
    [ins (.stGlobal .u64 (.regOffset "%rd6" 0) (iOp res))]
  kernelOf name inVars.length env body

end LeanNative.Backend.PTXLower
