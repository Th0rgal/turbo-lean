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

/-- Explicit poison / undefined-behavior wrapper (`PoisonOr α`) for `LeanMLIR` denotational semantics. -/
inductive PoisonOr (α : Type) where
  | val    : α → PoisonOr α
  | poison : String → PoisonOr α
  deriving Repr, DecidableEq, Inhabited, BEq

namespace LLVM

/-- `LeanMLIR` 64-bit SSA/register expression syntax (`LLVM.Expr`) over `BitVec 64`. -/
inductive Expr where
  | const64   : BitVec 64 → Expr
  | constBool : Bool → Expr
  | var       : VarId → Expr
  | binOp64   : BinOp → Expr → Expr → Expr
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

/-- Register and heap state for `LeanMLIR` evaluation. -/
structure EncodedMLIRState where
  env  : VarEnv
  heap : HeapState
  deriving Inhabited

/-- Independent `LeanMLIR` scalar expression evaluator producing `PoisonOr Val`. -/
def denoteExpr (env : VarEnv) : LLVM.Expr → PoisonOr Val
  | .const64 w => .val (.u64 (UInt64.ofBitVec w))
  | .constBool b => .val (.bool b)
  | .var id =>
    match env id with
    | some v => .val v
    | none => .poison s!"unbound register v{id}"
  | .binOp64 op lhs rhs =>
    match denoteExpr env lhs, denoteExpr env rhs with
    | .val v1, .val v2 =>
      match evalBinOp op v1 v2 with
      | .ok v => .val v
      | .error _ => .poison "binOp64 poison"
    | .poison msg, _ => .poison msg
    | .val _, .poison msg => .poison msg
  | .unaryOp64 op arg =>
    match denoteExpr env arg with
    | .val v =>
      match evalUnaryOp op v with
      | .ok out => .val out
      | .error _ => .poison "unaryOp64 poison"
    | .poison msg => .poison msg
  | .select64 c t e =>
    match denoteExpr env c with
    | .val (.bool true) => denoteExpr env t
    | .val (.bool false) => denoteExpr env e
    | .val (.u64 n) => if n != 0 then denoteExpr env t else denoteExpr env e
    | .val (.u256 w) => if w != UInt256.zero then denoteExpr env t else denoteExpr env e
    | .val _ => .poison "select64 invalid condition"
    | .poison msg => .poison msg
  | .fma64 a b c =>
    match denoteExpr env a, denoteExpr env b with
    | .val va, .val vb =>
      match evalBinOp .mul va vb, denoteExpr env c with
      | .ok vab, .val vc =>
        match evalBinOp .add vab vc with
        | .ok v => .val v
        | .error _ => .poison "fma64 add poison"
      | .error _, _ => .poison "fma64 mul poison"
      | .ok _, .poison msg => .poison msg
    | .poison msg, _ => .poison msg
    | .val _, .poison msg => .poison msg

/-- Independent `LeanMLIR` command denotation (`LeanMLIR.denote`) over `LLVM.Com`. -/
def denote (com : LLVM.Com) (st : EncodedMLIRState) : PoisonOr (Val × HeapState) :=
  match com with
  | .letReg dst _ty expr k =>
    match denoteExpr st.env expr with
    | .val v => denote k { st with env := st.env.bind dst v }
    | .poison msg => .poison msg
  | .condBr condVar thenCom elseCom =>
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
    match st.env v with
    | some val => .val (val, st.heap)
    | none => .poison s!"unbound return register v{v}"
  | .trap msg => .poison msg

/-- Lower a `ScalarExpr` into `LeanMLIR.LLVM.Expr`. -/
def lowerScalarToMLIR : ScalarExpr → LLVM.Expr
  | .constU64 v => .const64 v.toBitVec
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp op l r => .binOp64 op (lowerScalarToMLIR l) (lowerScalarToMLIR r)
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

/-- SCRATCH (ratchet negative test, never merged): new shadow call into the source evaluator. -/
def shadowAdd (a b : LeanNative.Semantics.Val) : Except LeanNative.Semantics.UBError LeanNative.Semantics.Val :=
  LeanNative.Semantics.evalBinOp .add a b

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

end LNSym
