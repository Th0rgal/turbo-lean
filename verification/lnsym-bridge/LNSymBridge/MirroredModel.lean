/-!
# Stage 3D Mirrored `LeanNative` Carryless & `LNSym` Model

This module contains exact, byte-synchronized slices of:
1. `LeanNative.IR.clmul64` and `LeanNative.IR.clmul64Hi` (`lean/LeanNative/IR/Types.lean`)
2. `LeanNative.Backend.Semantics.LNSym` (`lean/LeanNative/Backend/Semantics.lean`)

Enforced byte-for-byte against the root `LeanNative` compiler by `scripts/check_lnsym_bridge_sync.py`.
-/

namespace LeanNative.IR

-- BEGIN MIRRORED SLICE: lean/LeanNative/IR/Types.lean
/-- Carryless product, low 64 bits. One definition for Eval, LLVM, Metal and PTX. -/
def clmul64 (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a <<< iu) else acc) else acc
  go 0 0
/-- Carryless product, high 64 bits of the 128-bit polynomial product. -/
def clmul64Hi (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a >>> (64 - iu)) else acc) else acc
  go 1 0
-- END MIRRORED SLICE: lean/LeanNative/IR/Types.lean

end LeanNative.IR

namespace LeanNative.Backend.Semantics

-- BEGIN MIRRORED SLICE: lean/LeanNative/Backend/Semantics.lean
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

end LNSym
-- END MIRRORED SLICE: lean/LeanNative/Backend/Semantics.lean

end LeanNative.Backend.Semantics
