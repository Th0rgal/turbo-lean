import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval

/-!
# Formal Backend Semantics: `LeanMLIR` (`BitVec 64` + `PoisonOr`) and `LNSym` (`ARM64 NEON GF(2^128)`)

Milestone M5: Provides independent operational & denotational semantics for:
1. `LeanMLIR`: SSA/register IR over `BitVec 64` with explicit `PoisonOr` poison/trap propagation
   for `lowerToLeanMLIR_sound`.
2. `LNSym`: ARM64 NEON 128-bit `QReg` (`uint64x2_t`) state machine executing `pmullLo`, `pmullHi`,
   `eor128`, and polynomial reduction modulo $x^{128} + x^7 + x^2 + x + 1$ (`0x87`) across register
   files `q0..q7` for `arm64_f128_kernel_refines_lnir`.
-/

namespace LeanMLIR

open LeanNative.IR
open LeanNative.Semantics

/-- Explicit 3-valued Alive2 / VeLLVM / `lean-mlir` outcome (`PoisonOr α`) distinguishing:
    - `.val v`: defined result `v`
    - `.poison msg`: deferred poison value (propagates dataflow-wise, only traps when branched on or returned)
    - `.ub msg`: immediate undefined behavior (e.g. division/modulo by zero or `unreachable`) -/
inductive PoisonOr (α : Type) where
  | val    : α → PoisonOr α
  | poison : String → PoisonOr α
  | ub     : String → PoisonOr α
  deriving Repr, DecidableEq, Inhabited, BEq

namespace PoisonOr

/-- Alive2 / VeLLVM / `lean-mlir` 3-level refinement lattice (`UB ⊑ Poison ⊑ Val v`):
    - If `src` triggers immediate `.ub`, any `tgt` refines `src`.
    - If `src` is `.poison`, `tgt` refines `src` iff `tgt` is `.poison` or `.val v`
      (allowing `tgt` to refine `.poison` into `.val v` or remain `.poison`, never `.ub`).
    - If `src` is `.val v`, `tgt` must evaluate to the exact same `.val v`. -/
inductive Refines {α : Type} : PoisonOr α → PoisonOr α → Prop where
  | ubRefines (msg : String) (tgt : PoisonOr α) : Refines (.ub msg) tgt
  | poisonRefinesVal (msg : String) (v : α) : Refines (.poison msg) (.val v)
  | poisonRefinesPoison (m1 m2 : String) : Refines (.poison m1) (.poison m2)
  | valRefinesVal (v : α) : Refines (.val v) (.val v)

theorem Refines.refl {α : Type} (x : PoisonOr α) : Refines x x := by
  cases x with
  | val v => exact .valRefinesVal v
  | poison m => exact .poisonRefinesPoison m m
  | ub m => exact .ubRefines m (.ub m)

end PoisonOr

namespace LLVM

/-- LLVM IR arithmetic & shift poison flags (`nsw`, `nuw`, `exact`, `unmaskedShift`)
    following `opencompl/lean-mlir`, VeLLVM, and Alive2. -/
structure NoWrapFlags where
  nsw           : Bool := false
  nuw           : Bool := false
  exact         : Bool := false
  unmaskedShift : Bool := false
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Canonical 64-bit `BitVec 64` binary operator semantics shared across `LCNF`, `LNIR`, `SymExpr`, and `LeanMLIR`. -/
def evalBinOpBV64 (op : BinOp) (a b : BitVec 64) : Except UBError Val :=
  evalBinOp op (.u64 (UInt64.ofBitVec a)) (.u64 (UInt64.ofBitVec b))

/-- Effective 64-bit shift amount under `unmaskedShift`. -/
def shiftAmount64 (unmaskedShift : Bool) (b : BitVec 64) : BitVec 64 :=
  if unmaskedShift then b else b &&& 63#64

/-- Arithmetic right shift (`ashr`) over `BitVec 64`. -/
def arithShiftRight64 (a sh : BitVec 64) : BitVec 64 :=
  let shifted := a >>> sh
  let signBit := (a >>> 63#64) &&& 1#64
  if signBit != 0#64 && sh != 0#64 then
    shifted ||| (0xffffffffffffffff#64 <<< (64#64 - sh))
  else
    shifted

/-- Fallback 64-bit `BinOp` evaluation into `PoisonOr (BitVec 64)` for operators without `nuw`/`nsw`/`exact` flags. -/
def evalFallbackBinOp64 (op : BinOp) (a b : BitVec 64) : PoisonOr (BitVec 64) :=
  match evalBinOp op (.u64 (UInt64.ofBitVec a)) (.u64 (UInt64.ofBitVec b)) with
  | .ok (.u64 out) => .val out.toBitVec
  | .ok (.bool out) => .val (if out then 1#64 else 0#64)
  | .error .divisionByZero => .ub "division by zero UB"
  | _ => .poison "unsupported binOp64"

/-- Official `lean-mlir` / VeLLVM / Alive2 64-bit integer arithmetic & shift semantics with explicit
    `nuw`, `nsw`, `exact`, shift-width (`rhs ≥ 64` when `unmaskedShift = true`), and immediate
    division/modulo-by-zero `.ub` vs deferred `.poison`. -/
def evalArithWithFlags64 (op : BinOp) (flags : NoWrapFlags) (a b : BitVec 64) : PoisonOr (BitVec 64) :=
  match op with
  | .add =>
    let res := a + b
    let nuwPoison := flags.nuw && decide (a.toNat + b.toNat >= 18446744073709551616)
    let nswPoison := flags.nsw && decide (a.toInt + b.toInt < -9223372036854775808 || a.toInt + b.toInt >= 9223372036854775808)
    if nuwPoison || nswPoison then .poison "add nuw/nsw overflow poison" else .val res
  | .sub =>
    let res := a - b
    let nuwPoison := flags.nuw && decide (a.toNat < b.toNat)
    let nswPoison := flags.nsw && decide (a.toInt - b.toInt < -9223372036854775808 || a.toInt - b.toInt >= 9223372036854775808)
    if nuwPoison || nswPoison then .poison "sub nuw/nsw underflow poison" else .val res
  | .mul =>
    let res := a * b
    let nuwPoison := flags.nuw && decide (a.toNat * b.toNat >= 18446744073709551616)
    let nswPoison := flags.nsw && decide (a.toInt * b.toInt < -9223372036854775808 || a.toInt * b.toInt >= 9223372036854775808)
    if nuwPoison || nswPoison then .poison "mul nuw/nsw overflow poison" else .val res
  | .shl =>
    if flags.unmaskedShift && decide (b.toNat >= 64) then .poison "shl shift >= 64 poison"
    else
      let sh := shiftAmount64 flags.unmaskedShift b
      let res := a <<< sh
      let nuwPoison := flags.nuw && decide ((res >>> sh) != a)
      let nswPoison := flags.nsw && decide ((res.sshiftRight' sh) != a)
      if nuwPoison || nswPoison then .poison "shl nuw/nsw poison" else .val res
  | .shr =>
    if flags.unmaskedShift && decide (b.toNat >= 64) then .poison "lshr shift >= 64 poison"
    else
      let sh := shiftAmount64 flags.unmaskedShift b
      let res := a >>> sh
      let exactPoison := flags.exact && decide ((res <<< sh) != a)
      if exactPoison then .poison "lshr exact poison" else .val res
  | .sar =>
    if flags.unmaskedShift && decide (b.toNat >= 64) then .poison "ashr shift >= 64 poison"
    else
      let sh := b &&& 63#64
      let res := arithShiftRight64 a sh
      let exactPoison := flags.exact && decide ((res <<< sh) != a)
      if exactPoison then .poison "ashr exact poison" else .val res
  | .div =>
    if b == 0#64 then .ub "udiv by zero UB"
    else
      let res := a / b
      let exactPoison := flags.exact && decide (a % b != 0#64)
      if exactPoison then .poison "udiv exact non-zero remainder poison" else .val res
  | .mod =>
    if b == 0#64 then .ub "urem by zero UB" else .val (a % b)
  | .bitAnd => .val (a &&& b)
  | .bitOr  => .val (a ||| b)
  | .bitXor => .val (a ^^^ b)
  | _ => evalFallbackBinOp64 op a b

/-- Evaluate a `LeanMLIR` binary operator with `NoWrapFlags` on runtime `Val`s, routing
    flagged 64-bit integer operations through `evalArithWithFlags64` and converting
    division-by-zero errors into immediate `.ub`. -/
def evalValBinOpWithFlags (op : BinOp) (flags : NoWrapFlags) (v1 v2 : Val) : PoisonOr Val :=
  if flags == {} then
    match evalBinOp op v1 v2 with
    | .ok v => .val v
    | .error .divisionByZero => .ub "division by zero UB"
    | .error _ => .poison "binOp64 poison"
  else
    match v1, v2 with
    | .u64 a, .u64 b =>
      match evalArithWithFlags64 op flags a.toBitVec b.toBitVec with
      | .val w => .val (.u64 (UInt64.ofBitVec w))
      | .poison msg => .poison msg
      | .ub msg => .ub msg
    | _, _ =>
      match evalBinOp op v1 v2 with
      | .ok v => .val v
      | .error .divisionByZero => .ub "division by zero UB"
      | .error _ => .poison "binOp64 poison"

/-- `LeanMLIR` 64-bit SSA/register expression syntax (`LLVM.Expr`) over `BitVec 64` with `NoWrapFlags`. -/
inductive Expr where
  | const64   : BitVec 64 → Expr
  | constBool : Bool → Expr
  | var       : VarId → Expr
  | binOp64   : BinOp → NoWrapFlags → Expr → Expr → Expr
  | unaryOp64 : UnaryOp → Expr → Expr
  | select64  : Expr → Expr → Expr → Expr
  | fma64     : Expr → Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited, BEq

/-- `LeanMLIR` command/block syntax (`LLVM.Com`). -/
inductive Com where
  | letReg : VarId → LNIRType → Expr → Com → Com
  | condBr : VarId → Com → Com → Com
  | retReg : VarId → Com
  | trap   : String → Com
  deriving Repr, Inhabited, BEq

end LLVM

/-- Register, deferred-poison register overlay, and heap state for `LeanMLIR` evaluation. -/
structure EncodedMLIRState where
  env        : VarEnv
  poisonRegs : List (VarId × String) := []
  heap       : HeapState
  deriving Inhabited

/-- Look up whether register `id` currently holds a deferred `poison` value. -/
def lookupPoison : List (VarId × String) → VarId → Option String
  | [], _ => none
  | (r, msg) :: rest, id => if r == id then some msg else lookupPoison rest id

/-- Remove any deferred `poison` entry for register `id` when `id` is overwritten with a defined `.val`. -/
def clearPoison : List (VarId × String) → VarId → List (VarId × String)
  | [], _ => []
  | (r, msg) :: rest, id =>
    if r == id then clearPoison rest id else (r, msg) :: clearPoison rest id

/-- Record a deferred `poison` value in register `id` without immediately trapping at `letReg`. -/
def setPoison (poisonRegs : List (VarId × String)) (id : VarId) (msg : String) : List (VarId × String) :=
  (id, msg) :: clearPoison poisonRegs id

/-- Independent `LeanMLIR` scalar expression evaluator producing `PoisonOr Val` (with deferred register poison lookup). -/
def denoteExprWithPoison (env : VarEnv) (poisonRegs : List (VarId × String)) : LLVM.Expr → PoisonOr Val
  | .const64 w => .val (.u64 (UInt64.ofBitVec w))
  | .constBool b => .val (.bool b)
  | .var id =>
    match lookupPoison poisonRegs id with
    | some msg => .poison msg
    | none =>
      match env id with
      | some v => .val v
      | none => .poison s!"unbound register v{id}"
  | .binOp64 op flags lhs rhs =>
    match denoteExprWithPoison env poisonRegs lhs, denoteExprWithPoison env poisonRegs rhs with
    | .val v1, .val v2 => LLVM.evalValBinOpWithFlags op flags v1 v2
    | .ub msg, _ => .ub msg
    | _, .ub msg => .ub msg
    | .poison msg, _ => .poison msg
    | .val _, .poison msg => .poison msg
  | .unaryOp64 op arg =>
    match denoteExprWithPoison env poisonRegs arg with
    | .val v =>
      match evalUnaryOp op v with
      | .ok out => .val out
      | .error _ => .poison "unaryOp64 poison"
    | .poison msg => .poison msg
    | .ub msg => .ub msg
  | .select64 c t e =>
    match denoteExprWithPoison env poisonRegs c with
    | .val (.bool true) => denoteExprWithPoison env poisonRegs t
    | .val (.bool false) => denoteExprWithPoison env poisonRegs e
    | .val (.u64 n) => if n != 0 then denoteExprWithPoison env poisonRegs t else denoteExprWithPoison env poisonRegs e
    | .val (.u256 w) => if w != UInt256.zero then denoteExprWithPoison env poisonRegs t else denoteExprWithPoison env poisonRegs e
    | .val _ => .poison "select64 invalid condition"
    | .poison msg => .poison msg
    | .ub msg => .ub msg
  | .fma64 a b c =>
    match denoteExprWithPoison env poisonRegs a, denoteExprWithPoison env poisonRegs b with
    | .val va, .val vb =>
      match evalBinOp .mul va vb, denoteExprWithPoison env poisonRegs c with
      | .ok vab, .val vc =>
        match evalBinOp .add vab vc with
        | .ok v => .val v
        | .error _ => .poison "fma64 add poison"
      | .error _, _ => .poison "fma64 mul poison"
      | .ok _, .poison msg => .poison msg
      | .ok _, .ub msg => .ub msg
    | .ub msg, _ => .ub msg
    | _, .ub msg => .ub msg
    | .poison msg, _ => .poison msg
    | .val _, .poison msg => .poison msg

/-- Evaluate an `LLVM.Expr` in a poison-free register environment `env`. -/
def denoteExpr (env : VarEnv) (expr : LLVM.Expr) : PoisonOr Val :=
  denoteExprWithPoison env [] expr

/-- Independent `LeanMLIR` command denotation (`LeanMLIR.denote`) over `LLVM.Com`:
    - `.letReg` stores `.poison` as a deferred register value in `st.poisonRegs` (continuing into `k`),
      whereas `.ub` traps immediately!
    - `.condBr` traps with `.ub` if the branch condition register holds deferred `poison`.
    - `.retReg` returns `.poison` if the returned register holds deferred `poison`. -/
def denote (com : LLVM.Com) (st : EncodedMLIRState) : PoisonOr (Val × HeapState) :=
  match com with
  | .letReg dst _ty expr k =>
    match denoteExprWithPoison st.env st.poisonRegs expr with
    | .val v =>
      denote k { st with env := st.env.bind dst v, poisonRegs := clearPoison st.poisonRegs dst }
    | .poison msg =>
      denote k { st with poisonRegs := setPoison st.poisonRegs dst msg }
    | .ub msg => .ub msg
  | .condBr condVar thenCom elseCom =>
    match lookupPoison st.poisonRegs condVar with
    | some msg => .ub msg
    | none =>
      match st.env condVar with
      | some (.bool true) => denote thenCom st
      | some (.bool false) => denote elseCom st
      | some (.u64 n) =>
        if n != 0 then denote thenCom st else denote elseCom st
      | some (.u256 w) =>
        if w != UInt256.zero then denote thenCom st else denote elseCom st
      | some _ => .poison "condBr invalid condition type"
      | none => .poison s!"unbound condBr register v{condVar}"
  | .retReg v =>
    match lookupPoison st.poisonRegs v with
    | some msg => .poison msg
    | none =>
      match st.env v with
      | some val => .val (val, st.heap)
      | none => .poison s!"unbound return register v{v}"
  | .trap msg => .ub msg

/-- Lower a `ScalarExpr` into `LeanMLIR.LLVM.Expr`. -/
def lowerScalarToMLIR : ScalarExpr → LLVM.Expr
  | .constU64 v => .const64 v.toBitVec
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp op l r => .binOp64 op {} (lowerScalarToMLIR l) (lowerScalarToMLIR r)
  | .unaryOp op a => .unaryOp64 op (lowerScalarToMLIR a)
  | .select c t e => .select64 (lowerScalarToMLIR c) (lowerScalarToMLIR t) (lowerScalarToMLIR e)
  | .fma a b c => .fma64 (lowerScalarToMLIR a) (lowerScalarToMLIR b) (lowerScalarToMLIR c)

/-- Lower a scalar `LNIRCode` fragment into `LeanMLIR.LLVM.Com`, returning `.error` on non-scalar
    heap/loop constructs so `lowerLNIRToMLIR code = .ok mlirCom` is a non-trivial partial compilation pass. -/
def lowerLNIRToMLIR : LNIRCode → Except String LLVM.Com
  | .letBind dst ty (.scalar se) k =>
    match lowerLNIRToMLIR k with
    | .ok k' => .ok (.letReg dst ty (lowerScalarToMLIR se) k')
    | .error err => .error err
  | .letBind _ _ _ _ =>
    .error "lowerLNIRToMLIR: non-scalar LNIRExpr requires runtime lowering pass"
  | .ite condVar thenBranch elseBranch =>
    match lowerLNIRToMLIR thenBranch, lowerLNIRToMLIR elseBranch with
    | .ok t', .ok e' => .ok (.condBr condVar t' e')
    | .error err, _ => .error err
    | .ok _, .error err => .error err
  | .ret v => .ok (.retReg v)
  | .unreachable => .ok (.trap "unreachable")
  | _ => .error "lowerLNIRToMLIR: unsupported non-SSA statement in scalar MLIR dialect"

end LeanMLIR

namespace LNSym

open LeanNative.IR

/-- 128-bit ARM64 NEON vector register (`QReg` / `uint64x2_t`) storing low and high 64-bit lanes. -/
structure QReg where
  lo : UInt64
  hi : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

namespace QReg

def zero : QReg := ⟨0, 0⟩

def xor (a b : QReg) : QReg :=
  ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

/-- 64x64 -> 128 carryless polynomial multiplication (`PMULL` / `PMULL2`). -/
def pmull64 (a b : UInt64) : QReg :=
  ⟨clmul64 a b, clmul64Hi a b⟩

/-- $\mathbb{F}_{2^{128}}$ modular reduction of a 256-bit carryless product `(r0, r1, r2, r3)`
    modulo $p(x) = x^{128} + x^7 + x^2 + x + 1$ (`0x87`). -/
def reduceGF128 (lowProd midProd highProd : QReg) : QReg :=
  let r0 := lowProd.lo
  let r1 := lowProd.hi ^^^ midProd.lo
  let r2 := highProd.lo ^^^ midProd.hi
  let r3 := highProd.hi
  let red2Lo := clmul64 r2 0x87
  let red2Hi := clmul64Hi r2 0x87
  let red3Lo := clmul64 r3 0x87
  let red3Hi := clmul64Hi r3 0x87
  let foldLo := clmul64 red3Hi 0x87
  let foldHi := clmul64Hi red3Hi 0x87
  ⟨r0 ^^^ red2Lo ^^^ foldLo, r1 ^^^ red2Hi ^^^ red3Lo ^^^ foldHi⟩

/-- Full $\mathbb{F}_{2^{128}}$ multiplication (`a * b mod (x^128 + x^7 + x^2 + x + 1)`). -/
def mulGF128 (a b : QReg) : QReg :=
  let lowProd  := pmull64 a.lo b.lo
  let midProd  := xor (pmull64 a.lo b.hi) (pmull64 a.hi b.lo)
  let highProd := pmull64 a.hi b.hi
  reduceGF128 lowProd midProd highProd

end QReg

/-- Reference LNIR specification of one radix-2 $\mathbb{F}_{2^{128}}$ additive NTT butterfly lane:
    given `(u, v)` and twiddle `tw`, computes `p = v * tw` in $\mathbb{F}_{2^{128}}$ and returns
    `(u' = u ⊕ p, v' = u' ⊕ v)`. -/
def gf128ButterflyLane (u v tw : QReg) : QReg × QReg :=
  let p  := QReg.mulGF128 v tw
  let u' := QReg.xor u p
  let v' := QReg.xor u' v
  (u', v')

/-- ARM64 NEON register & slice state (`ArmState`). -/
structure ArmState where
  qregs    : Nat → QReg
  sliceU   : List QReg
  sliceV   : List QReg
  outU     : List QReg
  outV     : List QReg
  validABI : Bool
  deriving Inhabited

namespace ArmState

def readQ (s : ArmState) (r : Nat) : QReg :=
  s.qregs r

def writeQ (s : ArmState) (r : Nat) (v : QReg) : ArmState :=
  { s with qregs := fun k => if k == r then v else s.qregs k }

@[simp]
theorem readQ_writeQ_same (s : ArmState) (r : Nat) (v : QReg) :
    (s.writeQ r v).readQ r = v := by
  simp [readQ, writeQ]

end ArmState

/-- Concrete ARM64 NEON instructions for the $\mathbb{F}_{2^{128}}$ additive NTT butterfly kernel. -/
inductive Arm64Instr where
  | ld1ButterflyPair : Nat → Nat → Nat → Arm64Instr       -- load sliceU[idx] -> q[rdU], sliceV[idx] -> q[rdV]
  | pmullLow         : Nat → Nat → Nat → Arm64Instr       -- q[rd] := pmull64(q[rn].lo, q[rm].lo)
  | pmullMid         : Nat → Nat → Nat → Arm64Instr       -- q[rd] := pmull64(q[rn].lo, q[rm].hi) ⊕ pmull64(q[rn].hi, q[rm].lo)
  | pmullHigh        : Nat → Nat → Nat → Arm64Instr       -- q[rd] := pmull64(q[rn].hi, q[rm].hi)
  | reducePoly0x87   : Nat → Nat → Nat → Nat → Arm64Instr -- q[rd] := reduceGF128(q[rLo], q[rMid], q[rHi])
  | veor128          : Nat → Nat → Nat → Arm64Instr       -- q[rd] := q[rn] ⊕ q[rm]
  | st1ButterflyPair : Nat → Nat → Arm64Instr             -- append (q[rU], q[rV]) to (outU, outV)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Execute a single ARM64 NEON instruction on `ArmState`. -/
def execInstr (ins : Arm64Instr) (s : ArmState) : ArmState :=
  if !s.validABI then
    { s with outU := [], outV := [] }
  else
    match ins with
    | .ld1ButterflyPair idx rdU rdV =>
      let u := s.sliceU[idx]?.getD QReg.zero
      let v := s.sliceV[idx]?.getD QReg.zero
      (s.writeQ rdU u).writeQ rdV v
    | .pmullLow rd rn rm =>
      let a := s.readQ rn
      let b := s.readQ rm
      s.writeQ rd (QReg.pmull64 a.lo b.lo)
    | .pmullMid rd rn rm =>
      let a := s.readQ rn
      let b := s.readQ rm
      s.writeQ rd (QReg.xor (QReg.pmull64 a.lo b.hi) (QReg.pmull64 a.hi b.lo))
    | .pmullHigh rd rn rm =>
      let a := s.readQ rn
      let b := s.readQ rm
      s.writeQ rd (QReg.pmull64 a.hi b.hi)
    | .reducePoly0x87 rd rLo rMid rHi =>
      s.writeQ rd (QReg.reduceGF128 (s.readQ rLo) (s.readQ rMid) (s.readQ rHi))
    | .veor128 rd rn rm =>
      s.writeQ rd (QReg.xor (s.readQ rn) (s.readQ rm))
    | .st1ButterflyPair rU rV =>
      { s with outU := s.outU ++ [s.readQ rU], outV := s.outV ++ [s.readQ rV] }

/-- Run a sequence of ARM64 NEON instructions on `ArmState`. -/
def runArm64 (prog : List Arm64Instr) (s : ArmState) : ArmState :=
  prog.foldl (fun st ins => execInstr ins st) s

@[simp]
theorem runArm64_nil (s : ArmState) : runArm64 [] s = s := rfl

@[simp]
theorem runArm64_cons (ins : Arm64Instr) (rest : List Arm64Instr) (s : ArmState) :
    runArm64 (ins :: rest) s = runArm64 rest (execInstr ins s) := rfl

theorem runArm64_append (p1 p2 : List Arm64Instr) (s : ArmState) :
    runArm64 (p1 ++ p2) s = runArm64 p2 (runArm64 p1 s) := by
  unfold runArm64
  exact List.foldl_append

/-- Extract the resulting `(outU, outV)` butterfly slices from `ArmState`. -/
def extractSlice (s : ArmState) : List QReg × List QReg :=
  (s.outU, s.outV)

/-- 8-instruction ARM64 NEON sequence for butterfly index `idx` (twiddle in `q0`, scratch in `q1..q6`). -/
def butterflyStepInstrs (idx : Nat) : List Arm64Instr :=
  [ .ld1ButterflyPair idx 1 2
  , .pmullLow 3 2 0
  , .pmullMid 4 2 0
  , .pmullHigh 5 2 0
  , .reducePoly0x87 6 3 4 5
  , .veor128 1 1 6
  , .veor128 2 1 2
  , .st1ButterflyPair 1 2
  ]

/-! ## AVX-512 512-Bit `ZmmReg` / `Avx512Instr` Machine Model & Target-Checked Emission -/

/-- 512-bit AVX-512 register (`ZmmReg` / `__m512i`) composed of four 128-bit `QReg` lanes (`lane0..lane3`). -/
structure ZmmReg where
  lane0 : QReg
  lane1 : QReg
  lane2 : QReg
  lane3 : QReg
  deriving Repr, DecidableEq, Inhabited, BEq

namespace ZmmReg

def zero : ZmmReg :=
  ⟨QReg.zero, QReg.zero, QReg.zero, QReg.zero⟩

def xor (a b : ZmmReg) : ZmmReg :=
  { lane0 := QReg.xor a.lane0 b.lane0
    lane1 := QReg.xor a.lane1 b.lane1
    lane2 := QReg.xor a.lane2 b.lane2
    lane3 := QReg.xor a.lane3 b.lane3 }

def pmullLow (a b : ZmmReg) : ZmmReg :=
  { lane0 := QReg.pmull64 a.lane0.lo b.lane0.lo
    lane1 := QReg.pmull64 a.lane1.lo b.lane1.lo
    lane2 := QReg.pmull64 a.lane2.lo b.lane2.lo
    lane3 := QReg.pmull64 a.lane3.lo b.lane3.lo }

def pmullLoHi (a b : ZmmReg) : ZmmReg :=
  { lane0 := QReg.pmull64 a.lane0.lo b.lane0.hi
    lane1 := QReg.pmull64 a.lane1.lo b.lane1.hi
    lane2 := QReg.pmull64 a.lane2.lo b.lane2.hi
    lane3 := QReg.pmull64 a.lane3.lo b.lane3.hi }

def pmullHiLo (a b : ZmmReg) : ZmmReg :=
  { lane0 := QReg.pmull64 a.lane0.hi b.lane0.lo
    lane1 := QReg.pmull64 a.lane1.hi b.lane1.lo
    lane2 := QReg.pmull64 a.lane2.hi b.lane2.lo
    lane3 := QReg.pmull64 a.lane3.hi b.lane3.lo }

def pmullMid (a b : ZmmReg) : ZmmReg :=
  { lane0 := QReg.xor (QReg.pmull64 a.lane0.lo b.lane0.hi) (QReg.pmull64 a.lane0.hi b.lane0.lo)
    lane1 := QReg.xor (QReg.pmull64 a.lane1.lo b.lane1.hi) (QReg.pmull64 a.lane1.hi b.lane1.lo)
    lane2 := QReg.xor (QReg.pmull64 a.lane2.lo b.lane2.hi) (QReg.pmull64 a.lane2.hi b.lane2.lo)
    lane3 := QReg.xor (QReg.pmull64 a.lane3.lo b.lane3.hi) (QReg.pmull64 a.lane3.hi b.lane3.lo) }

def pmullHigh (a b : ZmmReg) : ZmmReg :=
  { lane0 := QReg.pmull64 a.lane0.hi b.lane0.hi
    lane1 := QReg.pmull64 a.lane1.hi b.lane1.hi
    lane2 := QReg.pmull64 a.lane2.hi b.lane2.hi
    lane3 := QReg.pmull64 a.lane3.hi b.lane3.hi }

/-- Semantics of `@llvm.x86.pclmulqdq.512(a, b, imm8)` across `imm8 ∈ {0, 1, 16, 17}`:
    - `imm8[0]` selects the 64-bit half of the first operand `a` (`0` = low, `1` = high),
    - `imm8[4]` selects the 64-bit half of the second operand `b` (`0` = low, `1` = high).
    Hence `imm8 = 1` (`0x01`) is `pmullHiLo a b` (`a.hi * b.lo`) and `imm8 = 16` (`0x10`) is `pmullLoHi a b` (`a.lo * b.hi`). -/
def pclmulqdq512Imm8 (a b : ZmmReg) (imm8 : UInt8) : ZmmReg :=
  if imm8 == 0 then pmullLow a b
  else if imm8 == 1 then pmullHiLo a b
  else if imm8 == 16 then pmullLoHi a b
  else if imm8 == 17 then pmullHigh a b
  else ZmmReg.zero

def reduceGF128 (lo mid hi : ZmmReg) : ZmmReg :=
  { lane0 := QReg.reduceGF128 lo.lane0 mid.lane0 hi.lane0
    lane1 := QReg.reduceGF128 lo.lane1 mid.lane1 hi.lane1
    lane2 := QReg.reduceGF128 lo.lane2 mid.lane2 hi.lane2
    lane3 := QReg.reduceGF128 lo.lane3 mid.lane3 hi.lane3 }

def mulGF128 (a b : ZmmReg) : ZmmReg :=
  reduceGF128 (pmullLow a b) (pmullMid a b) (pmullHigh a b)

end ZmmReg

/-- 4-way vectorized AVX-512 `VPCLMULQDQ` $\mathbb{F}_{2^{128}}$ additive NTT butterfly over `ZmmReg`. -/
def evalZmmButterfly4Way (u v tw : ZmmReg) : ZmmReg × ZmmReg :=
  let p  := ZmmReg.mulGF128 v tw
  let u' := ZmmReg.xor u p
  let v' := ZmmReg.xor u' v
  (u', v')

/-- AVX-512 512-bit register file and slice state (`ZmmState`), including runtime CPUID gate `hasAvx512Vpclmul`. -/
structure ZmmState where
  zregs            : Nat → ZmmReg
  sliceU           : List ZmmReg
  sliceV           : List ZmmReg
  outU             : List ZmmReg
  outV             : List ZmmReg
  hasAvx512Vpclmul : Bool
  deriving Inhabited

namespace ZmmState

def readZ (s : ZmmState) (r : Nat) : ZmmReg :=
  s.zregs r

def writeZ (s : ZmmState) (r : Nat) (v : ZmmReg) : ZmmState :=
  { s with zregs := fun k => if k == r then v else s.zregs k }

end ZmmState

/-- Concrete x86-64 AVX-512 `VPCLMULQDQ` instructions for the 4-way $\mathbb{F}_{2^{128}}$ butterfly kernel. -/
inductive Avx512Instr where
  | vmovdqu64LoadPair  : Nat → Nat → Nat → Avx512Instr       -- load sliceU[idx] -> zmm[rdU], sliceV[idx] -> zmm[rdV]
  | vpclmulqdqLowZmm   : Nat → Nat → Nat → Avx512Instr       -- zmm[rd] := lane-wise pclmulqdq(0x00, zmm[rn], zmm[rm])
  | vpclmulqdqMidZmm   : Nat → Nat → Nat → Avx512Instr       -- zmm[rd] := lane-wise pclmulqdq(0x01) ⊕ pclmulqdq(0x10)
  | vpclmulqdqHighZmm  : Nat → Nat → Nat → Avx512Instr       -- zmm[rd] := lane-wise pclmulqdq(0x11, zmm[rn], zmm[rm])
  | vreducePoly0x87Zmm : Nat → Nat → Nat → Nat → Avx512Instr -- zmm[rd] := lane-wise reduceGF128(zmm[rLo], zmm[rMid], zmm[rHi])
  | vpxorqZmm          : Nat → Nat → Nat → Avx512Instr       -- zmm[rd] := zmm[rn] ⊕ zmm[rm]
  | vmovdqu64StorePair : Nat → Nat → Avx512Instr             -- append (zmm[rU], zmm[rV]) to (outU, outV)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Execute a single AVX-512 instruction on `ZmmState`, clearing output slices if `hasAvx512Vpclmul = false`. -/
def execAvx512Instr (ins : Avx512Instr) (s : ZmmState) : ZmmState :=
  if !s.hasAvx512Vpclmul then
    { s with outU := [], outV := [] }
  else
    match ins with
    | .vmovdqu64LoadPair idx rdU rdV =>
      let u := s.sliceU[idx]?.getD ZmmReg.zero
      let v := s.sliceV[idx]?.getD ZmmReg.zero
      (s.writeZ rdU u).writeZ rdV v
    | .vpclmulqdqLowZmm rd rn rm =>
      s.writeZ rd (ZmmReg.pmullLow (s.readZ rn) (s.readZ rm))
    | .vpclmulqdqMidZmm rd rn rm =>
      s.writeZ rd (ZmmReg.pmullMid (s.readZ rn) (s.readZ rm))
    | .vpclmulqdqHighZmm rd rn rm =>
      s.writeZ rd (ZmmReg.pmullHigh (s.readZ rn) (s.readZ rm))
    | .vreducePoly0x87Zmm rd rLo rMid rHi =>
      s.writeZ rd (ZmmReg.reduceGF128 (s.readZ rLo) (s.readZ rMid) (s.readZ rHi))
    | .vpxorqZmm rd rn rm =>
      s.writeZ rd (ZmmReg.xor (s.readZ rn) (s.readZ rm))
    | .vmovdqu64StorePair rU rV =>
      { s with outU := s.outU ++ [s.readZ rU], outV := s.outV ++ [s.readZ rV] }

/-- Run a sequence of AVX-512 instructions on `ZmmState`. -/
def runAvx512 (prog : List Avx512Instr) (s : ZmmState) : ZmmState :=
  prog.foldl (fun st ins => execAvx512Instr ins st) s

theorem runAvx512_append (p1 p2 : List Avx512Instr) (s : ZmmState) :
    runAvx512 (p1 ++ p2) s = runAvx512 p2 (runAvx512 p1 s) := by
  unfold runAvx512
  exact List.foldl_append

def extractZmmSlice (s : ZmmState) : List ZmmReg × List ZmmReg :=
  (s.outU, s.outV)

/-- 8-instruction AVX-512 `VPCLMULQDQ` sequence for 512-bit butterfly index `idx` (twiddle in `zmm0`, scratch in `zmm1..zmm6`). -/
def avx512ButterflyStepInstrs (idx : Nat) : List Avx512Instr :=
  [ .vmovdqu64LoadPair idx 1 2
  , .vpclmulqdqLowZmm 3 2 0
  , .vpclmulqdqMidZmm 4 2 0
  , .vpclmulqdqHighZmm 5 2 0
  , .vreducePoly0x87Zmm 6 3 4 5
  , .vpxorqZmm 1 1 6
  , .vpxorqZmm 2 1 2
  , .vmovdqu64StorePair 1 2
  ]

/-- Target architecture and ISA feature configuration for AVX-512 `VPCLMULQDQ` emission. -/
structure Avx512TargetConfig where
  arch          : TargetArch
  hasAvx512F    : Bool := true
  hasAvx512Vl   : Bool := true
  hasVpclmulqdq : Bool := true
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Avx512TargetConfig

/-- Check that both the target architecture is `x86_64` (or `hybridCpuGpu`) and all required
    AVX-512 (`avx512f`, `avx512vl`) and carryless multiply (`vpclmulqdq`) ISA features are present. -/
def supportsAvx512Vpclmul (cfg : Avx512TargetConfig) : Bool :=
  (cfg.arch == .x86_64 || cfg.arch == .hybridCpuGpu) &&
  cfg.hasAvx512F && cfg.hasAvx512Vl && cfg.hasVpclmulqdq

end Avx512TargetConfig

/-- Versioned SSA 512-bit ZMM register `(reg, ver)` rendered in LLVM IR as `%zmm{reg}_s{ver}`. -/
structure SsaZmmReg where
  reg : Nat
  ver : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

namespace SsaZmmReg

def toLLVMName (r : SsaZmmReg) : String :=
  s!"%zmm{r.reg}_s{r.ver}"

end SsaZmmReg

/-- SSA register renaming, load pointer counter, and indexed store counter state for AVX-512 LLVM IR emission. -/
structure Avx512SsaMap where
  regVer   : Nat → Nat
  loadIdx  : Nat
  storeIdx : Nat
  deriving Inhabited

namespace Avx512SsaMap

def init : Avx512SsaMap :=
  { regVer := fun _ => 0, loadIdx := 0, storeIdx := 0 }

def curReg (m : Avx512SsaMap) (r : Nat) : SsaZmmReg :=
  ⟨r, m.regVer r⟩

def bumpReg (m : Avx512SsaMap) (rd : Nat) : SsaZmmReg × Avx512SsaMap :=
  let nextV := m.regVer rd + 1
  (⟨rd, nextV⟩, { m with regVer := fun k => if k == rd then nextV else m.regVer k })

end Avx512SsaMap

/-- Atomic LLVM 18 SSA IR instruction line emitted by the AVX-512 backend. -/
inductive Llvm18IrLine where
  | gepInU        : (loadIdx : Nat) → (dstU : SsaZmmReg) → (sliceIdx : Nat) → Llvm18IrLine
  | loadInU       : (loadIdx : Nat) → (dstU : SsaZmmReg) → Llvm18IrLine
  | gepInV        : (loadIdx : Nat) → (dstV : SsaZmmReg) → (sliceIdx : Nat) → Llvm18IrLine
  | loadInV       : (loadIdx : Nat) → (dstV : SsaZmmReg) → Llvm18IrLine
  | callPclmulImm : (dst : SsaZmmReg) → (sub : Nat) → (srcN srcM : SsaZmmReg) → (imm8 : UInt8) → Llvm18IrLine
  | xorMidTemps   : (dst : SsaZmmReg) → Llvm18IrLine
  | callGf128Red  : (dst srcLo srcMid srcHi : SsaZmmReg) → Llvm18IrLine
  | xorVec512     : (dst srcN srcM : SsaZmmReg) → Llvm18IrLine
  | gepOutU       : (storeIdx : Nat) → Llvm18IrLine
  | storeOutU     : (storeIdx : Nat) → (srcU : SsaZmmReg) → Llvm18IrLine
  | gepOutV       : (storeIdx : Nat) → Llvm18IrLine
  | storeOutV     : (storeIdx : Nat) → (srcV : SsaZmmReg) → Llvm18IrLine
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Llvm18IrLine

def toLLVMText : Llvm18IrLine → String
  | .gepInU loadIdx dstU sliceIdx =>
    let uPtr := s!"%in_u_ptr_{loadIdx}_{dstU.reg}_{dstU.ver}"
    s!"  {uPtr} = getelementptr <8 x i64>, ptr %in_u_base, i64 {sliceIdx}"
  | .loadInU loadIdx dstU =>
    let uPtr := s!"%in_u_ptr_{loadIdx}_{dstU.reg}_{dstU.ver}"
    s!"  {dstU.toLLVMName} = load <8 x i64>, ptr {uPtr}, align 64"
  | .gepInV loadIdx dstV sliceIdx =>
    let vPtr := s!"%in_v_ptr_{loadIdx}_{dstV.reg}_{dstV.ver}"
    s!"  {vPtr} = getelementptr <8 x i64>, ptr %in_v_base, i64 {sliceIdx}"
  | .loadInV loadIdx dstV =>
    let vPtr := s!"%in_v_ptr_{loadIdx}_{dstV.reg}_{dstV.ver}"
    s!"  {dstV.toLLVMName} = load <8 x i64>, ptr {vPtr}, align 64"
  | .callPclmulImm dst sub srcN srcM imm8 =>
    let lhs :=
      if sub == 1 then s!"{dst.toLLVMName}_lo_hi"
      else if sub == 2 then s!"{dst.toLLVMName}_hi_lo"
      else dst.toLLVMName
    s!"  {lhs} = call <8 x i64> @llvm.x86.pclmulqdq.512(<8 x i64> {srcN.toLLVMName}, <8 x i64> {srcM.toLLVMName}, i8 {imm8.toNat})"
  | .xorMidTemps dst =>
    let tmpA := s!"{dst.toLLVMName}_lo_hi"
    let tmpB := s!"{dst.toLLVMName}_hi_lo"
    s!"  {dst.toLLVMName} = xor <8 x i64> {tmpA}, {tmpB}"
  | .callGf128Red dst srcLo srcMid srcHi =>
    s!"  {dst.toLLVMName} = call <8 x i64> @lean_native_gf128_reduce_0x87_zmm(" ++
    s!"<8 x i64> {srcLo.toLLVMName}, <8 x i64> {srcMid.toLLVMName}, <8 x i64> {srcHi.toLLVMName})"
  | .xorVec512 dst srcN srcM =>
    s!"  {dst.toLLVMName} = xor <8 x i64> {srcN.toLLVMName}, {srcM.toLLVMName}"
  | .gepOutU storeIdx =>
    let outUPtr := s!"%out_u_ptr_{storeIdx}"
    s!"  {outUPtr} = getelementptr <8 x i64>, ptr %out_u_base, i64 {storeIdx}"
  | .storeOutU storeIdx srcU =>
    let outUPtr := s!"%out_u_ptr_{storeIdx}"
    s!"  store <8 x i64> {srcU.toLLVMName}, ptr {outUPtr}, align 64"
  | .gepOutV storeIdx =>
    let outVPtr := s!"%out_v_ptr_{storeIdx}"
    s!"  {outVPtr} = getelementptr <8 x i64>, ptr %out_v_base, i64 {storeIdx}"
  | .storeOutV storeIdx srcV =>
    let outVPtr := s!"%out_v_ptr_{storeIdx}"
    s!"  store <8 x i64> {srcV.toLLVMName}, ptr {outVPtr}, align 64"

end Llvm18IrLine

/-- Structured SSA LLVM 18 statement emitted from `Avx512Instr` with explicit versioned `SsaZmmReg`
    operands, globally fresh `loadIdx`, and indexed output store offsets `storeIdx`. -/
inductive Avx512LlvmStmt where
  | loadPair512    : (loadIdx : Nat) → (sliceIdx : Nat) → (dstU dstV : SsaZmmReg) → Avx512LlvmStmt
  | pclmulLow512   : (dst srcN srcM : SsaZmmReg) → Avx512LlvmStmt
  | pclmulMid512   : (dst srcN srcM : SsaZmmReg) → Avx512LlvmStmt
  | pclmulHigh512  : (dst srcN srcM : SsaZmmReg) → Avx512LlvmStmt
  | gf128Reduce512 : (dst srcLo srcMid srcHi : SsaZmmReg) → Avx512LlvmStmt
  | xor512         : (dst srcN srcM : SsaZmmReg) → Avx512LlvmStmt
  | storePair512   : (storeIdx : Nat) → (srcU srcV : SsaZmmReg) → Avx512LlvmStmt
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Avx512LlvmStmt

/-- Expand a structured `Avx512LlvmStmt` into its sequence of atomic `Llvm18IrLine` instructions. -/
def toIrLines : Avx512LlvmStmt → List Llvm18IrLine
  | .loadPair512 loadIdx sliceIdx dstU dstV =>
    [ .gepInU loadIdx dstU sliceIdx
    , .loadInU loadIdx dstU
    , .gepInV loadIdx dstV sliceIdx
    , .loadInV loadIdx dstV ]
  | .pclmulLow512 dst srcN srcM =>
    [ .callPclmulImm dst 0 srcN srcM 0 ]
  | .pclmulMid512 dst srcN srcM =>
    [ .callPclmulImm dst 1 srcN srcM 16
    , .callPclmulImm dst 2 srcN srcM 1
    , .xorMidTemps dst ]
  | .pclmulHigh512 dst srcN srcM =>
    [ .callPclmulImm dst 0 srcN srcM 17 ]
  | .gf128Reduce512 dst srcLo srcMid srcHi =>
    [ .callGf128Red dst srcLo srcMid srcHi ]
  | .xor512 dst srcN srcM =>
    [ .xorVec512 dst srcN srcM ]
  | .storePair512 storeIdx srcU srcV =>
    [ .gepOutU storeIdx
    , .storeOutU storeIdx srcU
    , .gepOutV storeIdx
    , .storeOutV storeIdx srcV ]

/-- Render a structured SSA `Avx512LlvmStmt` to valid SSA LLVM 18 IR text directly from its
    atomic `toIrLines` instructions (globally fresh temporary names, indexed `getelementptr` stores). -/
def toLLVMText (stmt : Avx512LlvmStmt) : String :=
  String.intercalate "\n" (stmt.toIrLines.map Llvm18IrLine.toLLVMText)

end Avx512LlvmStmt

/-- Emit a single `Avx512Instr` into a structured SSA `Avx512LlvmStmt` and updated `Avx512SsaMap`,
    enforcing `cfg.supportsAvx512Vpclmul = true`. -/
def emitAvx512InstrSSA (cfg : Avx512TargetConfig) (m : Avx512SsaMap) (ins : Avx512Instr) :
    Except String (Avx512LlvmStmt × Avx512SsaMap) :=
  if !cfg.supportsAvx512Vpclmul then
    .error s!"emitAvx512InstrSSA: target {reprStr cfg} lacks x86_64 AVX-512 + VPCLMULQDQ support"
  else
    match ins with
    | .vmovdqu64LoadPair idx rdU rdV =>
      let lIdx := m.loadIdx
      let (dstU, m1) := m.bumpReg rdU
      let (dstV, m2) := m1.bumpReg rdV
      .ok (.loadPair512 lIdx idx dstU dstV, { m2 with loadIdx := lIdx + 1 })
    | .vpclmulqdqLowZmm rd rn rm =>
      let srcN := m.curReg rn
      let srcM := m.curReg rm
      let (dst, m1) := m.bumpReg rd
      .ok (.pclmulLow512 dst srcN srcM, m1)
    | .vpclmulqdqMidZmm rd rn rm =>
      let srcN := m.curReg rn
      let srcM := m.curReg rm
      let (dst, m1) := m.bumpReg rd
      .ok (.pclmulMid512 dst srcN srcM, m1)
    | .vpclmulqdqHighZmm rd rn rm =>
      let srcN := m.curReg rn
      let srcM := m.curReg rm
      let (dst, m1) := m.bumpReg rd
      .ok (.pclmulHigh512 dst srcN srcM, m1)
    | .vreducePoly0x87Zmm rd rLo rMid rHi =>
      let srcLo  := m.curReg rLo
      let srcMid := m.curReg rMid
      let srcHi  := m.curReg rHi
      let (dst, m1) := m.bumpReg rd
      .ok (.gf128Reduce512 dst srcLo srcMid srcHi, m1)
    | .vpxorqZmm rd rn rm =>
      let srcN := m.curReg rn
      let srcM := m.curReg rm
      let (dst, m1) := m.bumpReg rd
      .ok (.xor512 dst srcN srcM, m1)
    | .vmovdqu64StorePair rU rV =>
      let srcU := m.curReg rU
      let srcV := m.curReg rV
      .ok (.storePair512 m.storeIdx srcU srcV, { m with storeIdx := m.storeIdx + 1 })

/-- Emit a sequence of `Avx512Instr` into an SSA `List Avx512LlvmStmt` program. -/
def emitAvx512ProgSSA (cfg : Avx512TargetConfig) (m : Avx512SsaMap) :
    List Avx512Instr → Except String (List Avx512LlvmStmt × Avx512SsaMap)
  | [] => .ok ([], m)
  | ins :: rest =>
    match emitAvx512InstrSSA cfg m ins with
    | .error err => .error err
    | .ok (stmt, m1) =>
      match emitAvx512ProgSSA cfg m1 rest with
      | .error err => .error err
      | .ok (stmts, m2) => .ok (stmt :: stmts, m2)

/-- Execution state for emitted SSA LLVM 18 512-bit vector instructions (`Llvm18IrLine` / `Avx512LlvmStmt`),
    including GEP pointer offset tables (`inUPtr`, `inVPtr`, `outUPtr`, `outVPtr`), intermediate
    `pclmulqdq.512` SSA temporaries (`loHiTemps`, `hiLoTemps`), 64-byte base pointer alignment
    (`aligned64`), and sticky memory fault tracking (`memFault`) for unaligned or out-of-bounds loads/stores. -/
structure Avx512LlvmExecState where
  ssaRegs   : SsaZmmReg → ZmmReg
  loHiTemps : SsaZmmReg → ZmmReg
  hiLoTemps : SsaZmmReg → ZmmReg
  inUPtr    : (Nat × SsaZmmReg) → Nat
  inVPtr    : (Nat × SsaZmmReg) → Nat
  outUPtr   : Nat → Nat
  outVPtr   : Nat → Nat
  sliceU    : List ZmmReg
  sliceV    : List ZmmReg
  outU      : List ZmmReg
  outV      : List ZmmReg
  outCapU   : Nat := 64
  outCapV   : Nat := 64
  aligned64 : Bool := true
  memFault  : Bool := false
  deriving Inhabited

namespace Avx512LlvmExecState

def readSsa (st : Avx512LlvmExecState) (r : SsaZmmReg) : ZmmReg :=
  st.ssaRegs r

def writeSsa (st : Avx512LlvmExecState) (dst : SsaZmmReg) (v : ZmmReg) : Avx512LlvmExecState :=
  { st with ssaRegs := fun k => if decide (k = dst) then v else st.ssaRegs k }

def writeLoHiTemp (st : Avx512LlvmExecState) (dst : SsaZmmReg) (v : ZmmReg) : Avx512LlvmExecState :=
  { st with loHiTemps := fun k => if decide (k = dst) then v else st.loHiTemps k }

def writeHiLoTemp (st : Avx512LlvmExecState) (dst : SsaZmmReg) (v : ZmmReg) : Avx512LlvmExecState :=
  { st with hiLoTemps := fun k => if decide (k = dst) then v else st.hiLoTemps k }

/-- Write a 512-bit `ZmmReg` value at indexed memory offset `idx` in `slots` (modeling `getelementptr` + `store`). -/
def writeOutAt (slots : List ZmmReg) (idx : Nat) (v : ZmmReg) : List ZmmReg :=
  if idx == slots.length then
    slots ++ [v]
  else if idx < slots.length then
    slots.set idx v
  else
    slots ++ List.replicate (idx - slots.length) ZmmReg.zero ++ [v]

end Avx512LlvmExecState

/-- Evaluate a single atomic `Llvm18IrLine` instruction on `Avx512LlvmExecState`, enforcing 64-byte alignment
    (`aligned64 = true`) and slice bounds (`idx < sliceU.length`, `idx < sliceV.length`, `idx ≤ outU.length`,
    `idx ≤ outV.length`) on every `load ... align 64` and `store ... align 64`. -/
def evalLlvm18IrLine (line : Llvm18IrLine) (st : Avx512LlvmExecState) : Avx512LlvmExecState :=
  match line with
  | .gepInU loadIdx dstU sliceIdx =>
    { st with inUPtr := fun k => if decide (k = (loadIdx, dstU)) then sliceIdx else st.inUPtr k }
  | .loadInU loadIdx dstU =>
    let idx := st.inUPtr (loadIdx, dstU)
    let fault := st.memFault || !st.aligned64 || !decide (idx < st.sliceU.length)
    { st.writeSsa dstU (st.sliceU[idx]?.getD ZmmReg.zero) with memFault := fault }
  | .gepInV loadIdx dstV sliceIdx =>
    { st with inVPtr := fun k => if decide (k = (loadIdx, dstV)) then sliceIdx else st.inVPtr k }
  | .loadInV loadIdx dstV =>
    let idx := st.inVPtr (loadIdx, dstV)
    let fault := st.memFault || !st.aligned64 || !decide (idx < st.sliceV.length)
    { st.writeSsa dstV (st.sliceV[idx]?.getD ZmmReg.zero) with memFault := fault }
  | .callPclmulImm dst sub srcN srcM imm8 =>
    let v := ZmmReg.pclmulqdq512Imm8 (st.readSsa srcN) (st.readSsa srcM) imm8
    if sub == 1 then st.writeLoHiTemp dst v
    else if sub == 2 then st.writeHiLoTemp dst v
    else st.writeSsa dst v
  | .xorMidTemps dst =>
    st.writeSsa dst (ZmmReg.xor (st.loHiTemps dst) (st.hiLoTemps dst))
  | .callGf128Red dst srcLo srcMid srcHi =>
    st.writeSsa dst (ZmmReg.reduceGF128 (st.readSsa srcLo) (st.readSsa srcMid) (st.readSsa srcHi))
  | .xorVec512 dst srcN srcM =>
    st.writeSsa dst (ZmmReg.xor (st.readSsa srcN) (st.readSsa srcM))
  | .gepOutU storeIdx =>
    { st with outUPtr := fun k => if decide (k = storeIdx) then storeIdx else st.outUPtr k }
  | .storeOutU storeIdx srcU =>
    let idx := st.outUPtr storeIdx
    let fault := st.memFault || !st.aligned64 || !decide (idx ≤ st.outU.length) || !decide (idx < st.outCapU)
    { st with outU := Avx512LlvmExecState.writeOutAt st.outU idx (st.readSsa srcU), memFault := fault }
  | .gepOutV storeIdx =>
    { st with outVPtr := fun k => if decide (k = storeIdx) then storeIdx else st.outVPtr k }
  | .storeOutV storeIdx srcV =>
    let idx := st.outVPtr storeIdx
    let fault := st.memFault || !st.aligned64 || !decide (idx ≤ st.outV.length) || !decide (idx < st.outCapV)
    { st with outV := Avx512LlvmExecState.writeOutAt st.outV idx (st.readSsa srcV), memFault := fault }

/-- Number of 512-bit pair stores performed by a single `Avx512Instr`. -/
def avx512InstrStoreCount : Avx512Instr → Nat
  | .vmovdqu64StorePair _ _ => 1
  | _ => 0

/-- Total number of 512-bit pair stores performed by a program `List Avx512Instr`. -/
def avx512ProgStoreCount : List Avx512Instr → Nat
  | [] => 0
  | ins :: rest => avx512InstrStoreCount ins + avx512ProgStoreCount rest

/-- Flatten a program `List Avx512LlvmStmt` into its exact sequence of atomic `Llvm18IrLine` instructions. -/
def flattenAvx512IrLines : List Avx512LlvmStmt → List Llvm18IrLine
  | [] => []
  | s :: rest => s.toIrLines ++ flattenAvx512IrLines rest

/-- Evaluate a flat list of atomic `Llvm18IrLine` instructions sequentially on `Avx512LlvmExecState`. -/
def evalLlvm18IrLines (lines : List Llvm18IrLine) (st : Avx512LlvmExecState) : Avx512LlvmExecState :=
  lines.foldl (fun acc line => evalLlvm18IrLine line acc) st

/-- Evaluate an emitted `Avx512LlvmStmt` by executing its expanded `stmt.toIrLines` atomic LLVM 18
    instructions sequentially via `evalLlvm18IrLine`. -/
def evalAvx512LlvmStmt (stmt : Avx512LlvmStmt) (st : Avx512LlvmExecState) : Avx512LlvmExecState :=
  evalLlvm18IrLines stmt.toIrLines st

/-- Execute an emitted SSA LLVM program `List Avx512LlvmStmt`. -/
def runAvx512LlvmProg (stmts : List Avx512LlvmStmt) (st : Avx512LlvmExecState) : Avx512LlvmExecState :=
  stmts.foldl (fun acc stmt => evalAvx512LlvmStmt stmt acc) st

def extractLlvmZmmSlice (st : Avx512LlvmExecState) : List ZmmReg × List ZmmReg :=
  (st.outU, st.outV)

/-- Stateful, target- and feature-checked SSA LLVM 18 IR emission for an `Avx512Instr` under
    `cfg : Avx512TargetConfig` and SSA map `m : Avx512SsaMap`. -/
def emitAvx512InstrLLVM (cfg : Avx512TargetConfig) (m : Avx512SsaMap) (ins : Avx512Instr) :
    Except String (String × Avx512SsaMap) :=
  match emitAvx512InstrSSA cfg m ins with
  | .ok (stmt, m') => .ok (stmt.toLLVMText, m')
  | .error err => .error err

/-- Emit a sequence of `Avx512Instr` into a flat list of atomic `Llvm18IrLine` instructions. -/
def emitAvx512ProgIrLines (cfg : Avx512TargetConfig) (m : Avx512SsaMap) (prog : List Avx512Instr) :
    Except String (List Llvm18IrLine × Avx512SsaMap) :=
  match emitAvx512ProgSSA cfg m prog with
  | .ok (stmts, m') => .ok (flattenAvx512IrLines stmts, m')
  | .error err => .error err

/-- Stateful, target- and feature-checked SSA LLVM 18 IR emission for an entire `List Avx512Instr` program. -/
def emitAvx512ProgLLVM (cfg : Avx512TargetConfig) (m : Avx512SsaMap) (prog : List Avx512Instr) :
    Except String (List String × Avx512SsaMap) :=
  match emitAvx512ProgSSA cfg m prog with
  | .ok (stmts, m') => .ok (stmts.map Avx512LlvmStmt.toLLVMText, m')
  | .error err => .error err

end LNSym
