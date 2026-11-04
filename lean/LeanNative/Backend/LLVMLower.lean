import LeanNative.IR.AST
import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.LLVMAst.Eval
import LeanNative.Backend.LLVMAst.PP

/-!
# LNIR → typed LLVM AST lowering (`LeanNative.Backend.LLVMLower`)

Total, compositional lowering of the typed scalar/control-flow LNIR fragment
(`ScalarExpr`, `LNIRCode` with `letBind`, multi-block `ite` diamonds, `ret`, and
`LNIRDecl`) into `LeanNative.Backend.LLVMAst`, whose operational semantics
(`LLVMAst.stepInstr`, `LLVMAst.execBlockWith`, `LLVMAst.execFn`) is completely
independent of `LeanNative.Semantics.eval*`.

Key semantic obligations bridged by the lowering:
1. Total `u64` division and remainder (`a / 0 = 0`, `a % 0 = a` in LNIR vs UB in
   `LLVMAst.divOrRem`): lowered via zero-check `icmp eq`, safe divisor `select`,
   `udiv`/`urem`, and fallback `select`.
2. Masked 64-bit shifts (`b &&& 63` in LNIR vs poison for shift `≥ 64` in
   `LLVMAst.shiftResult`): lowered via `and i64 %b, 63` prior to `shl`/`lshr`/`ashr`.
3. Boolean values and comparisons (`.bool` in LNIR vs `i1` in `LLVMAst`): lowered
   to zero-extended `0`/`1` `i64` words via `icmp` + `zext i1 ... to i64`.
4. Structured `LNIRCode.ite` branches: lowered to multi-block CFG diamonds
   (`condBr`, branch sub-CFGs, and a join block with `PhiNode`).
-/

namespace LeanNative.Backend.LLVMLower

open LeanNative.IR
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVMAst

def c64 (n : Nat) : Operand := .constInt .i64 (BitVec.ofNat 64 n)

def c256 (n : Nat) : Operand := .constInt .i256 (BitVec.ofNat 256 n)

def w64 : LLVMType := .int .i64

def w256 : LLVMType := .int .i256

/-- SSA register name for a bound LNIR variable (`"v"` + decimal digits).
Disjoint from compiler temporaries (`"t"` + decimal digits). -/
def varReg (v : VarId) : RegName := "v" ++ ppInt v

/-- Fresh compiler temporary register (`"t"` + decimal digits). -/
def tmpReg (k : Nat) : RegName := "t" ++ ppInt k

/-- Fresh basic-block label (`"b"` + decimal digits), disjoint from `"entry"`. -/
def blkLabel (k : Nat) : BlockLabel := "b" ++ ppInt k

def entryLabel : BlockLabel := "entry"

/-- Type environment for the lowered scalar LNIR fragment (`.i64` words and `.i1` booleans). -/
abbrev ScalarTyEnv := VarId → Option LNIRType

def ScalarTyEnv.empty : ScalarTyEnv := fun _ => none

def ScalarTyEnv.bind (Γ : ScalarTyEnv) (x : VarId) (ty : LNIRType) : ScalarTyEnv :=
  fun y => if y == x then some ty else Γ y

/-- Guarded 64-bit unsigned `div` / `mod` sequence avoiding LLVM division-by-zero UB. -/
def emitDivRem (k : Nat) (isRem : Bool) (a b : Operand) : RegName × Nat × List LLVMInstr :=
  let z := tmpReg k
  let safe := tmpReg (k + 1)
  let raw := tmpReg (k + 2)
  let res := tmpReg (k + 3)
  let divOp : LLVMInstr :=
    if isRem then .urem raw .i64 a (.reg safe)
    else .udiv raw false .i64 a (.reg safe)
  let fallback : Operand := if isRem then a else c64 0
  (res, k + 4,
    [ .icmp z .eq w64 b (c64 0)
    , .select safe (.reg z) w64 (c64 1) b
    , divOp
    , .select res (.reg z) w64 fallback (.reg raw) ])

/-- Masked 64-bit shift sequence avoiding LLVM overshift poison (`amt = b & 63`). -/
def emitShift (k : Nat) (op : BinOp) (a b : Operand) : RegName × Nat × List LLVMInstr :=
  let amt := tmpReg k
  let res := tmpReg (k + 1)
  let shInstr : LLVMInstr :=
    match op with
    | .shr => .lshr res false .i64 a (.reg amt)
    | .sar => .ashr res false .i64 a (.reg amt)
    | _    => .shl res .none .i64 a (.reg amt)
  (res, k + 2, [.and_ amt .i64 b (c64 63), shInstr])

/-- `icmp` followed by `zext i1 -> i64` producing a `{0, 1}` 64-bit word. -/
def emitCmp (k : Nat) (pred : ICmpPred) (a b : Operand) : RegName × Nat × List LLVMInstr :=
  let bit := tmpReg k
  let res := tmpReg (k + 1)
  (res, k + 2, [.icmp bit pred w64 a b, .zext res .i1 (.reg bit) .i64])

/-- Lowered scalar expression output: inferred type, result register, updated temp
counter, and straight-line `LLVMAst` instruction list. -/
structure ScalarLowerRes where
  ty      : LNIRType
  dst     : RegName
  nextTmp : Nat
  instrs  : List LLVMInstr
  deriving Repr, BEq

/-- Type-checked 64-bit binary op tail emission after lowering `rl` and `rr`. -/
def lowerBinOp64 (op : BinOp) (rl rr : ScalarLowerRes) : Option ScalarLowerRes :=
  let pfx := rl.instrs ++ rr.instrs
  let k2 := rr.nextTmp
  match op with
  | .add =>
    let d := tmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.add d .none .i64 (.reg rl.dst) (.reg rr.dst)]⟩
  | .sub =>
    let d := tmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.sub d .none .i64 (.reg rl.dst) (.reg rr.dst)]⟩
  | .mul =>
    let d := tmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.mul d .none .i64 (.reg rl.dst) (.reg rr.dst)]⟩
  | .div =>
    let (d, k3, ops) := emitDivRem k2 false (.reg rl.dst) (.reg rr.dst)
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .mod =>
    let (d, k3, ops) := emitDivRem k2 true (.reg rl.dst) (.reg rr.dst)
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .bitAnd =>
    let d := tmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.and_ d .i64 (.reg rl.dst) (.reg rr.dst)]⟩
  | .bitOr =>
    let d := tmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.or_ d .i64 (.reg rl.dst) (.reg rr.dst)]⟩
  | .bitXor =>
    let d := tmpReg k2
    some ⟨.i64, d, k2 + 1, pfx ++ [.xor d .i64 (.reg rl.dst) (.reg rr.dst)]⟩
  | .shl =>
    let (d, k3, ops) := emitShift k2 .shl (.reg rl.dst) (.reg rr.dst)
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .shr =>
    let (d, k3, ops) := emitShift k2 .shr (.reg rl.dst) (.reg rr.dst)
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .sar =>
    let (d, k3, ops) := emitShift k2 .sar (.reg rl.dst) (.reg rr.dst)
    some ⟨.i64, d, k3, pfx ++ ops⟩
  | .eq =>
    let (d, k3, ops) := emitCmp k2 .eq (.reg rl.dst) (.reg rr.dst)
    some ⟨.i1, d, k3, pfx ++ ops⟩
  | .lt =>
    let (d, k3, ops) := emitCmp k2 .ult (.reg rl.dst) (.reg rr.dst)
    some ⟨.i1, d, k3, pfx ++ ops⟩
  | .le =>
    let (d, k3, ops) := emitCmp k2 .ule (.reg rl.dst) (.reg rr.dst)
    some ⟨.i1, d, k3, pfx ++ ops⟩
  | _ => none

/-- Type-checked binary op tail emission after lowering `rl` and `rr`. -/
def lowerBinOpStep (op : BinOp) (rl rr : ScalarLowerRes) : Option ScalarLowerRes :=
  match rl.ty with
  | .i64 =>
    match rr.ty with
    | .i64 => lowerBinOp64 op rl rr
    | _ => none
  | .i1 =>
    match rr.ty with
    | .i1 =>
      match op with
      | .eq =>
        let (d, k3, ops) := emitCmp rr.nextTmp .eq (.reg rl.dst) (.reg rr.dst)
        some ⟨.i1, d, k3, (rl.instrs ++ rr.instrs) ++ ops⟩
      | _ => none
    | _ => none
  | _ => none

/-- Exact recognizer for `LNIRType.i64` (avoids 18-constructor multi-match blowup). -/
def isI64Ty : LNIRType → Bool
  | .i64 => true
  | _ => false

/-- Exact recognizer for `LNIRType.i1`. -/
def isI1Ty : LNIRType → Bool
  | .i1 => true
  | _ => false

/-- Exact equality check restricted to supported scalar types (`.i64` or `.i1`). -/
def sameScalarTy (t1 t2 : LNIRType) : Bool :=
  (isI64Ty t1 && isI64Ty t2) || (isI1Ty t1 && isI1Ty t2)

/-- Compositional type-directed lowering of `ScalarExpr` into `LLVMAst` instructions.
`dst` holds the lowered `i64` representation (`0`/`1` when `ty = .i1`). -/
def lowerScalarExpr (Γ : ScalarTyEnv) : ScalarExpr → Nat → Option ScalarLowerRes
  | .constU64 n, k =>
    let r := tmpReg k
    some ⟨.i64, r, k + 1, [.add r .none .i64 (.constInt .i64 n.toBitVec) (c64 0)]⟩
  | .constBool b, k =>
    let r := tmpReg k
    some ⟨.i1, r, k + 1, [.add r .none .i64 (c64 (if b then 1 else 0)) (c64 0)]⟩
  | .var v, k =>
    match Γ v with
    | some ty =>
      if isI64Ty ty then some ⟨.i64, varReg v, k, []⟩
      else if isI1Ty ty then some ⟨.i1, varReg v, k, []⟩
      else none
    | none => none
  | .binOp op l r, k => do
    let rl ← lowerScalarExpr Γ l k
    let rr ← lowerScalarExpr Γ r rl.nextTmp
    lowerBinOpStep op rl rr
  | .unaryOp .not a, k => do
    let ra ← lowerScalarExpr Γ a k
    let d := tmpReg ra.nextTmp
    if isI64Ty ra.ty then
      some ⟨.i64, d, ra.nextTmp + 1,
        ra.instrs ++ [.xor d .i64 (.reg ra.dst) (c64 0xffffffffffffffff)]⟩
    else if isI1Ty ra.ty then
      some ⟨.i1, d, ra.nextTmp + 1,
        ra.instrs ++ [.xor d .i64 (.reg ra.dst) (c64 1)]⟩
    else
      none
  | .unaryOp .neg a, k => do
    let ra ← lowerScalarExpr Γ a k
    let d := tmpReg ra.nextTmp
    if isI64Ty ra.ty then
      some ⟨.i64, d, ra.nextTmp + 1,
        ra.instrs ++ [.sub d .none .i64 (c64 0) (.reg ra.dst)]⟩
    else
      none
  | .unaryOp .clz256 _, _ => none
  | .select c t e, k => do
    let rc ← lowerScalarExpr Γ c k
    let rt ← lowerScalarExpr Γ t rc.nextTmp
    let re ← lowerScalarExpr Γ e rt.nextTmp
    if (isI1Ty rc.ty || isI64Ty rc.ty) && sameScalarTy rt.ty re.ty then
      let nz := tmpReg re.nextTmp
      let d := tmpReg (re.nextTmp + 1)
      some ⟨rt.ty, d, re.nextTmp + 2,
        rc.instrs ++ rt.instrs ++ re.instrs ++
          [ .icmp nz .ne w64 (.reg rc.dst) (c64 0)
          , .select d (.reg nz) w64 (.reg rt.dst) (.reg re.dst) ]⟩
    else
      none
  | .fma a b c, k => do
    let ra ← lowerScalarExpr Γ a k
    let rb ← lowerScalarExpr Γ b ra.nextTmp
    let rc ← lowerScalarExpr Γ c rb.nextTmp
    if isI64Ty ra.ty && isI64Ty rb.ty && isI64Ty rc.ty then
      let p := tmpReg rc.nextTmp
      let d := tmpReg (rc.nextTmp + 1)
      some ⟨.i64, d, rc.nextTmp + 2,
        ra.instrs ++ rb.instrs ++ rc.instrs ++
          [ .mul p .none .i64 (.reg ra.dst) (.reg rb.dst)
          , .add d .none .i64 (.reg p) (.reg rc.dst) ]⟩
    else
      none

/-- Lowered CFG region for an `LNIRCode` sub-tree: a single phi-free `entryBlk`
labelled `lbl`, internal/join blocks `restBlks`, the unique `exitLbl` and `exitReg`
reaching the continuation, and updated counters. -/
structure CodeLowerRes where
  ty       : LNIRType
  exitReg  : RegName
  exitLbl  : BlockLabel
  nextTmp  : Nat
  nextBlk  : Nat
  entryBlk : LLVMBlock
  restBlks : List LLVMBlock
  deriving Repr, BEq

def exitTerminator (exitCont : Option BlockLabel) (r : RegName) : Terminator :=
  match exitCont with
  | none      => .ret (some (w64, .reg r))
  | some jLbl => .br jLbl

def mkJoinPhi (res tExitReg eExitReg : RegName) (tExitLbl eExitLbl : BlockLabel) : PhiNode :=
  { dst := res, ty := w64,
    incomings := [(.reg tExitReg, tExitLbl), (.reg eExitReg, eExitLbl)] }

def mkJoinBlk (jLbl : BlockLabel) (exitCont : Option BlockLabel)
    (res tExitReg eExitReg : RegName) (tExitLbl eExitLbl : BlockLabel) : LLVMBlock :=
  { label := jLbl,
    phis := [mkJoinPhi res tExitReg eExitReg tExitLbl eExitLbl],
    body := [],
    term := exitTerminator exitCont res }

def mkIteHeadBlk (lbl tLbl eLbl : BlockLabel) (condVar : VarId) (bit : RegName) : LLVMBlock :=
  { label := lbl, phis := [],
    body := [.icmp bit .ne w64 (.reg (varReg condVar)) (c64 0)],
    term := .condBr (.reg bit) tLbl eLbl }

/-- Compositional lowering of structured `LNIRCode` (`letBind` of scalar expressions,
multi-block `ite` diamonds with `PhiNode`, and `ret`) into `LLVMAst` CFG regions. -/
def lowerCode (Γ : ScalarTyEnv) (lbl : BlockLabel) (exitCont : Option BlockLabel) :
    LNIRCode → Nat → Nat → Option CodeLowerRes
  | .letBind dst declTy (.scalar se) k, kTmp, kBlk => do
    let rse ← lowerScalarExpr Γ se kTmp
    if sameScalarTy rse.ty declTy then
      let mov : LLVMInstr := .add (varReg dst) .none .i64 (.reg rse.dst) (c64 0)
      let rk ← lowerCode (Γ.bind dst rse.ty) lbl exitCont k rse.nextTmp kBlk
      some { rk with
        entryBlk := { rk.entryBlk with body := rse.instrs ++ [mov] ++ rk.entryBlk.body } }
    else
      none
  | .ret v, kTmp, kBlk =>
    match Γ v with
    | some ty =>
      if isI64Ty ty then
        some ⟨.i64, varReg v, lbl, kTmp, kBlk,
          { label := lbl, phis := [], body := [], term := exitTerminator exitCont (varReg v) }, []⟩
      else if isI1Ty ty then
        some ⟨.i1, varReg v, lbl, kTmp, kBlk,
          { label := lbl, phis := [], body := [], term := exitTerminator exitCont (varReg v) }, []⟩
      else none
    | none => none
  | .ite condVar t e, kTmp, kBlk =>
    match Γ condVar with
    | some cty =>
      if isI1Ty cty || isI64Ty cty then do
        let tLbl := blkLabel kBlk
        let eLbl := blkLabel (kBlk + 1)
        let jLbl := blkLabel (kBlk + 2)
        let bit := tmpReg kTmp
        let res := tmpReg (kTmp + 1)
        let rt ← lowerCode Γ tLbl (some jLbl) t (kTmp + 2) (kBlk + 3)
        let re ← lowerCode Γ eLbl (some jLbl) e rt.nextTmp rt.nextBlk
        if sameScalarTy rt.ty re.ty then
          let headBlk := mkIteHeadBlk lbl tLbl eLbl condVar bit
          let joinBlk := mkJoinBlk jLbl exitCont res rt.exitReg re.exitReg rt.exitLbl re.exitLbl
          some ⟨rt.ty, res, jLbl, re.nextTmp, re.nextBlk, headBlk,
            (rt.entryBlk :: rt.restBlks) ++ (re.entryBlk :: re.restBlks) ++ [joinBlk]⟩
        else
          none
      else
        none
    | none => none
  | _, _, _ => none

/-- Build the initial `ScalarTyEnv` left-to-right to match `LLVMAst.bindArgs`,
rejecting unsupported non-scalar parameter types. -/
def initParamTyEnvAcc (Γ : ScalarTyEnv) : List LNIRParam → Option ScalarTyEnv
  | [] => some Γ
  | p :: ps =>
    if isI64Ty p.ty then initParamTyEnvAcc (Γ.bind p.id .i64) ps
    else if isI1Ty p.ty then initParamTyEnvAcc (Γ.bind p.id .i1) ps
    else none

def initParamTyEnv (ps : List LNIRParam) : Option ScalarTyEnv :=
  initParamTyEnvAcc ScalarTyEnv.empty ps

def codeBlockFuel : LNIRCode → Nat
  | .letBind _ _ _ k => codeBlockFuel k
  | .ite _ t e => codeBlockFuel t + codeBlockFuel e + 2
  | _ => 1

/-- Lower a scalar `LNIRDecl` (including `ite` CFG diamonds) to a self-contained
`LLVMFn` returning an `i64` word. -/
def lowerDecl (d : LNIRDecl) : Option LLVMFn := do
  let Γ0 ← initParamTyEnv d.params
  let rc ← lowerCode Γ0 entryLabel none d.body 0 0
  if sameScalarTy rc.ty d.retTy then
    some { name := d.name
         , retTy := w64
         , params := d.params.map fun p => ⟨varReg p.id, w64, []⟩
         , cc := .ccc
         , blocks := rc.entryBlk :: rc.restBlks }
  else
    none

/-- Wrap a lowered `LLVMFn` into a single-function `LLVMModule`. -/
def modOfFn (fn : LLVMFn) : LLVMModule :=
  { dataLayout := TargetArch.x86_64.dataLayout
  , triple := TargetArch.x86_64.llvmTriple
  , fns := [fn] }

/-- Lower an `LNIRDecl` to a single-function `LLVMModule`. -/
def lowerModule (d : LNIRDecl) : Option LLVMModule :=
  (lowerDecl d).map modOfFn

/-- Lower and pretty-print an `LNIRDecl` via `LLVMAst.PP.ppModule`. -/
def ppLoweredDecl (d : LNIRDecl) : Option String := do
  let m ← lowerModule d
  some (PP.ppModule m)

def overflowFlagsOf (nsw nuw : Bool) : OverflowFlags :=
  if nsw && nuw then .nswNuw else if nsw then .nsw else if nuw then .nuw else .none

def overflowOf (facts : FactEnv) (isMul : Bool) (a b : VarId) : OverflowFlags :=
  match facts with
  | [] => .none
  | .noOverflowAdd l r nsw nuw :: rest =>
    if !isMul && l == a && r == b then overflowFlagsOf nsw nuw
    else overflowOf rest isMul a b
  | .noOverflowMul l r nsw nuw :: rest =>
    if isMul && l == a && r == b then overflowFlagsOf nsw nuw
    else overflowOf rest isMul a b
  | _ :: rest => overflowOf rest isMul a b

def subFlagsOf (facts : FactEnv) (a b : VarId) : OverflowFlags :=
  match facts with
  | [] => .none
  | .noOverflowSub l r nsw nuw :: rest =>
    if l == a && r == b then overflowFlagsOf nsw nuw else subFlagsOf rest a b
  | _ :: rest => subFlagsOf rest a b

def llvmRegOf (v : VarId) : String := "v" ++ ppInt v

def mergeFlags (old fresh : OverflowFlags) : OverflowFlags :=
  match old, fresh with
  | .none, f => f
  | f, .none => f
  | .nsw, .nuw | .nuw, .nsw | .nswNuw, _ | _, .nswNuw => .nswNuw
  | .nsw, .nsw => .nsw
  | .nuw, .nuw => .nuw

def attachOverflow (facts : FactEnv) (ins : LLVMInstr) : LLVMInstr :=
  match ins with
  | .add dst old .i64 (.reg x) (.reg y) =>
    match factOperands facts x y with
    | some (a, b) => .add dst (mergeFlags old (overflowOf facts false a b)) .i64 (.reg x) (.reg y)
    | none => ins
  | .sub dst old .i64 (.reg x) (.reg y) =>
    match factOperands facts x y with
    | some (a, b) => .sub dst (mergeFlags old (subFlagsOf facts a b)) .i64 (.reg x) (.reg y)
    | none => ins
  | .mul dst old .i64 (.reg x) (.reg y) =>
    match factOperands facts x y with
    | some (a, b) => .mul dst (mergeFlags old (overflowOf facts true a b)) .i64 (.reg x) (.reg y)
    | none => ins
  | _ => ins
where
  factOperands (facts : FactEnv) (x y : String) : Option (VarId × VarId) :=
    match facts with
    | [] => none
    | .noOverflowAdd a b _ _ :: rest | .noOverflowSub a b _ _ :: rest
    | .noOverflowMul a b _ _ :: rest =>
      if x == llvmRegOf a && y == llvmRegOf b then some (a, b)
      else factOperands rest x y
    | _ :: rest => factOperands rest x y

def alignOfFact (facts : FactEnv) (ptrVar : VarId) (ty : LLVMType) (fallback : Nat) : Nat :=
  match facts with
  | [] => fallback
  | .alignedPtr p n :: rest =>
    let eff := effectiveAlign ty fallback
    if p == ptrVar && isPow2 n && isPow2 eff && eff < n && n % eff == 0 then n
    else alignOfFact rest ptrVar ty fallback
  | _ :: rest => alignOfFact rest ptrVar ty fallback

def attachLoadStoreAlign (facts : FactEnv) (ptrVar : VarId) (ins : LLVMInstr) : LLVMInstr :=
  match ins with
  | .load dst vol ty (.reg r) al as_ =>
    if r == llvmRegOf ptrVar then .load dst vol ty (.reg r) (alignOfFact facts ptrVar ty al) as_
    else ins
  | .store vol ty valOp (.reg r) al as_ =>
    if r == llvmRegOf ptrVar then .store vol ty valOp (.reg r) (alignOfFact facts ptrVar ty al) as_
    else ins
  | other => other

def instrDstReg? : LLVMInstr → Option RegName
  | .alloca dst _ _ | .load dst _ _ _ _ _
  | .add dst _ _ _ _ | .sub dst _ _ _ _ | .mul dst _ _ _ _
  | .udiv dst _ _ _ _ | .sdiv dst _ _ _ _ | .urem dst _ _ _ | .srem dst _ _ _
  | .and_ dst _ _ _ | .or_ dst _ _ _ | .xor dst _ _ _
  | .shl dst _ _ _ _ | .lshr dst _ _ _ _ | .ashr dst _ _ _ _
  | .icmp dst _ _ _ _
  | .fadd dst _ _ _ | .fsub dst _ _ _ | .fmul dst _ _ _ | .fdiv dst _ _ _
  | .fcmp dst _ _ _ _
  | .zext dst _ _ _ | .sext dst _ _ _ | .trunc dst _ _ _
  | .bitcast dst _ _ _ | .inttoptr dst _ _ _ | .ptrtoint dst _ _ _
  | .getelementptr dst _ _ _ _ _ | .select dst _ _ _ _
  | .atomicrmw dst _ _ _ _ _ _ _
  | .insertelement dst _ _ _ _ _ _ | .extractelement dst _ _ _ _ _
  | .shufflevector dst _ _ _ _ _ _
  | .insertvalue dst _ _ _ _ _ | .extractvalue dst _ _ _ => some dst
  | .call dst? _ _ _ _ => dst?
  | .store _ _ _ _ _ _ => none

def factVarIds : RetainedFact → List VarId
  | .idxLt i n => [i, n]
  | .noOverflowAdd a b _ _ | .noOverflowSub a b _ _ | .noOverflowMul a b _ _ => [a, b]
  | .alignedPtr p _ => [p]
  | .disjointSlices a b la lb => [a, b, la, lb]
  | .exclusiveObj o => [o]

def killRegFacts (facts : FactEnv) (r : RegName) : FactEnv :=
  facts.filter fun f => !(factVarIds f).any (fun v => llvmRegOf v == r)

def termTargets : Terminator → List BlockLabel
  | .br lbl => [lbl]
  | .condBr _ tLbl eLbl => [tLbl, eLbl]
  | .switch _ _ defLbl cases => defLbl :: cases.map Prod.snd
  | .ret _ | .unreachable => []

def fnDefinesReg (fn : LLVMFn) (r : RegName) : Bool :=
  fn.blocks.any fun blk =>
    blk.phis.any (fun p => p.dst == r) ||
    blk.body.any (fun ins => instrDstReg? ins == some r)

def immutableParamFacts (fn : LLVMFn) (facts : FactEnv) : FactEnv :=
  facts.filter fun f =>
    (factVarIds f).all fun v =>
      let r := llvmRegOf v
      fn.params.any (·.name == r) && !fnDefinesReg fn r

def entryIsStraight (fn : LLVMFn) : Bool :=
  match fn.blocks with
  | [] => false
  | blk :: _ =>
    blk.phis.isEmpty && fn.blocks.all fun b => !(termTargets b.term).contains blk.label

def emitVerifiedLLVMWithFacts (facts : FactEnv) (a b : VarId)
    (insns : List LLVMInstr) (ptrVar : VarId := 0) : List LLVMInstr :=
  match insns with
  | [] => []
  | ins :: rest =>
    let ins' := attachLoadStoreAlign facts ptrVar (attachOverflow facts ins)
    let facts' := match instrDstReg? ins with
      | some dst => killRegFacts facts dst
      | none => facts
    ins' :: emitVerifiedLLVMWithFacts facts' a b rest ptrVar

def emitBlockBodyWithFacts (facts : FactEnv) (insns : List LLVMInstr) : List LLVMInstr :=
  match insns with
  | [] => []
  | ins :: rest =>
    let ins1 := attachOverflow facts ins
    let ins' := facts.foldl (fun acc f =>
      match f with
      | .alignedPtr ptrVar _ => attachLoadStoreAlign facts ptrVar acc
      | _ => acc) ins1
    let facts' := match instrDstReg? ins with
      | some dst => killRegFacts facts dst
      | none => facts
    ins' :: emitBlockBodyWithFacts facts' rest

def withNoAlias (disjoint : Bool) (p : LLVMParam) : LLVMParam :=
  if !disjoint then p
  else if p.attrs.contains .noalias then p
  else { p with attrs := .noalias :: p.attrs }

def isCertifiedPtrParam (ptrA ptrB : VarId) (p : LLVMParam) : Bool :=
  match p.ty with
  | .ptr _ => p.name == llvmRegOf ptrA || p.name == llvmRegOf ptrB
  | _ => true

def noaliasParams (facts : FactEnv) (ptrA ptrB lenA lenB : VarId)
    (ps : List LLVMParam) : List LLVMParam :=
  let allPtrCertified := ps.all (isCertifiedPtrParam ptrA ptrB)
  if !(ptrA != ptrB && factMember facts (.disjointSlices ptrA ptrB lenA lenB) && allPtrCertified) then ps
  else ps.map fun p =>
    match p.ty with
    | .ptr _ =>
      if p.name == llvmRegOf ptrA || p.name == llvmRegOf ptrB then withNoAlias true p else p
    | _ => p

def emitVerifiedLLVMFnWithFacts (facts : FactEnv) (ptrA ptrB lenA lenB : VarId)
    (a b : VarId) (fn : LLVMFn) (ptrVar : VarId := 0) : LLVMFn :=
  let entryFacts := if entryIsStraight fn then facts else immutableParamFacts fn facts
  let tailFacts := immutableParamFacts fn facts
  let blocks' := match fn.blocks with
    | [] => []
    | blk :: rest =>
      { blk with body := emitVerifiedLLVMWithFacts entryFacts a b blk.body ptrVar } ::
        rest.map fun blk' => { blk' with body := emitVerifiedLLVMWithFacts tailFacts a b blk'.body ptrVar }
  { fn with
    params := noaliasParams facts ptrA ptrB lenA lenB fn.params
    blocks := blocks' }

def applyRetainedFactsLLVMFn (facts : FactEnv) (fn : LLVMFn) : LLVMFn :=
  if facts.isEmpty then fn
  else
    let paramFacts := facts.filter fun f =>
      (factVarIds f).all fun v => fn.params.any (·.name == llvmRegOf v)
    let entryFacts := if entryIsStraight fn then paramFacts else immutableParamFacts fn facts
    let tailFacts := immutableParamFacts fn facts
    let blocks' := match fn.blocks with
      | [] => []
      | blk :: rest =>
        { blk with body := emitBlockBodyWithFacts entryFacts blk.body } ::
          rest.map fun b => { b with body := emitBlockBodyWithFacts tailFacts b.body }
    { fn with blocks := blocks' }

def lowerDeclWithFacts (d : LNIRDecl) : Option LLVMFn :=
  (lowerDecl d).map (applyRetainedFactsLLVMFn d.retainedFacts)

def lowerModuleWithFacts (d : LNIRDecl) : Option LLVMModule :=
  (lowerDeclWithFacts d).map modOfFn

def ppLoweredDeclWithFacts (d : LNIRDecl) : Option String := do
  let m ← lowerModuleWithFacts d
  some (PP.ppModule m)

/-- Wrap a single `ScalarExpr` over two `i64` parameters (`%v0`, `%v1`) as an `LNIRDecl`. -/
def mkBinScalarDecl (name : String) (retTy : LNIRType) (se : ScalarExpr) : LNIRDecl :=
  { name := name
  , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
  , retTy := retTy
  , body := .letBind 2 retTy (.scalar se) (.ret 2) }

/-! ## Emitter mutants (`M1`..`M5`)

Typed-AST analogues of the LLVM emitter mutants in `scripts/emitter_mutants.json`:
* `M1`: `sub` with swapped operands (`b - a` instead of `a - b`).
* `M2`: `shl` lowered as `lshr` (`a >>> (b & 63)` instead of `a <<< (b & 63)`).
* `M3`: 64-bit `lt` (`icmp ult i64`) relaxed to `icmp ule i64`.
* `M4`: 256-bit `lt` (`icmp ult i256`) relaxed to `icmp ule i256`.
* `M5`: unguarded `udiv` without the zero-divisor `select` guard (UB on `b = 0`). -/

def fnOf (name : String) (body : List LLVMInstr) : LLVMFn :=
  { name := name, retTy := w64,
    params := [⟨"v0", w64, []⟩, ⟨"v1", w64, []⟩], cc := .ccc,
    blocks := [{ label := entryLabel, phis := [], body := body,
                 term := .ret (some (w64, .reg "res")) }] }

def mutantM1 : LLVMFn :=
  fnOf "mutant_m1_sub_swap" [.sub "res" .none .i64 (.reg "v1") (.reg "v0")]

def mutantM2 : LLVMFn :=
  fnOf "mutant_m2_shl_as_shr"
    [.and_ "amt" .i64 (.reg "v1") (c64 63), .lshr "res" false .i64 (.reg "v0") (.reg "amt")]

def mutantM3 : LLVMFn :=
  fnOf "mutant_m3_ult64_as_ule64"
    [.icmp "cmp" .ule w64 (.reg "v0") (.reg "v1"), .zext "res" .i1 (.reg "cmp") .i64]

def specUlt256Fn : LLVMFn :=
  fnOf "spec_ult256"
    [ .zext "w0" .i64 (.reg "v0") .i256
    , .zext "w1" .i64 (.reg "v1") .i256
    , .icmp "cmp" .ult w256 (.reg "w0") (.reg "w1")
    , .zext "res" .i1 (.reg "cmp") .i64 ]

def mutantM4 : LLVMFn :=
  fnOf "mutant_m4_ult256_as_ule256"
    [ .zext "w0" .i64 (.reg "v0") .i256
    , .zext "w1" .i64 (.reg "v1") .i256
    , .icmp "cmp" .ule w256 (.reg "w0") (.reg "w1")
    , .zext "res" .i1 (.reg "cmp") .i64 ]

def mutantM5 : LLVMFn :=
  fnOf "mutant_m5_udiv_unguarded" [.udiv "res" false .i64 (.reg "v0") (.reg "v1")]

def specUdivGuardFn : LLVMFn :=
  fnOf "spec_udiv_guard"
    ((emitDivRem 0 false (.reg "v0") (.reg "v1")).2.2 ++
      [.add "res" .none .i64 (.reg (tmpReg 3)) (c64 0)])

/-- Execute a lowered 2-parameter `LLVMFn` on `x, y : BitVec 64` using `LLVMAst.execFn`. -/
def runFn2 (fn : LLVMFn) (x y : BitVec 64) (fuel : Nat) : ExecOutcome :=
  execFn { fns := [fn] } fn [.bits .i64 x, .bits .i64 y] fuel

end LeanNative.Backend.LLVMLower
