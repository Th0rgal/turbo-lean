import LeanNative.IR.Types
open LeanNative.IR

@[noinline, export p0_kmul]
def kmul (a b : UInt64) : UInt64 :=
  let lo := clmul64 a b
  let hi := clmul64Hi a b
  lo ^^^ clmul64 hi 0x1b ^^^ clmul64 (clmul64Hi hi 0x1b) 0x1b

@[noinline, export p0_emul0]
def emul0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := kmul a0 b0
  let p1 := kmul a1 b1
  let p2 := kmul a2 b2
  let c12 := kmul (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  p0 ^^^ c12

@[noinline, export p0_emul1]
def emul1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := kmul a0 b0
  let p1 := kmul a1 b1
  let p2 := kmul a2 b2
  let c01 := kmul (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let c12 := kmul (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  c01 ^^^ c12 ^^^ p2

@[noinline, export p0_emul2]
def emul2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := kmul a0 b0
  let p1 := kmul a1 b1
  let p2 := kmul a2 b2
  let c02 := kmul (a0 ^^^ a2) (b0 ^^^ b2) ^^^ p0 ^^^ p2
  c02 ^^^ p1 ^^^ p2


@[noinline, export p0_identity]
def identity (x : UInt64) : UInt64 := x

@[noinline, export p0_identity32]
def identity32 (x : UInt32) : UInt32 := x

@[noinline, export p0_identitySize]
def identitySize (x : USize) : USize := x

def zmmSliceStepLoop (i n : UInt64) (srcA srcB srcC dst : ByteArray) : ByteArray :=
  if _h : i < n then
    let off := (i <<< 3).toUSize
    let a := uget64LE srcA off
    let b := uget64LE srcB off
    let c := uget64LE srcC off
    let p := clmul64 a b ^^^ clmul64Hi a b
    let g := gf2Affine64 p 0x8040201008040201 0x63
    let t := ternaryLogic64 g c a 0x96
    zmmSliceStepLoop (i + 1) n srcA srcB srcC (uset64LE dst off t)
  else
    dst
termination_by n.toNat - i.toNat
decreasing_by
  have hlt : i.toNat < n.toNat := _h
  have hn : n.toNat < 18446744073709551616 := n.toBitVec.isLt
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1]
    exact Nat.mod_eq_of_lt (by omega)
  omega

@[noinline, export p0_zmm_slice_kernel]
def zmmSliceKernel (n : UInt64) (srcA srcB srcC dst : ByteArray) : ByteArray :=
  zmmSliceStepLoop 0 n srcA srcB srcC dst

def mkWordsBA (ws : List UInt64) : ByteArray := Id.run do
  let mut ba := ByteArray.mk (Array.replicate (ws.length * 8) 0)
  let mut idx : USize := 0
  for w in ws do
    ba := uset64LE ba (idx * 8) w
    idx := idx + 1
  return ba

def main (args : List String) : IO Unit := do
  let u := fun (s : String) => s.toNat!.toUInt64
  match args with
  | ["K", a, b] => IO.println (kmul (u a) (u b))
  | ["E", a0, a1, a2, b0, b1, b2] =>
    IO.println (emul0 (u a0) (u a1) (u a2) (u b0) (u b1) (u b2))
    IO.println (emul1 (u a0) (u a1) (u a2) (u b0) (u b1) (u b2))
    IO.println (emul2 (u a0) (u a1) (u a2) (u b0) (u b1) (u b2))
  | ["I", x] => IO.println (identity (u x))
  | ["Z", nStr, seedStr] =>
    let n := nStr.toNat!
    let seed := u seedStr
    let wsA := (List.range n).map fun i => seed + (i.toUInt64 * 0x9e3779b97f4a7c15)
    let wsB := (List.range n).map fun i => (seed ^^^ 0xfeedfacecafebeef) + (i.toUInt64 * 0xbf58476d1ce4e5b9)
    let wsC := (List.range n).map fun i => (seed <<< 7) ^^^ (i.toUInt64 * 0x94d049bb133111eb)
    let baA := mkWordsBA wsA
    let baB := mkWordsBA wsB
    let baC := mkWordsBA wsC
    let baDst := ByteArray.mk (Array.replicate (n * 8) 0)
    let out := zmmSliceKernel n.toUInt64 baA baB baC baDst
    let mut acc : UInt64 := 0
    for i in [:n] do
      let got := uget64LE out (i.toUSize * 8)
      let a := wsA[i]!
      let b := wsB[i]!
      let c := wsC[i]!
      let exp := ternaryLogic64 (gf2Affine64 (clmul64 a b ^^^ clmul64Hi a b) 0x8040201008040201 0x63) c a 0x96
      if got != exp then
        throw (IO.userError s!"Z mismatch at lane {i}: got {got}, expected {exp}")
      acc := acc ^^^ got
    IO.println acc
  | _ => throw (IO.userError "expected K a b, E a0 a1 a2 b0 b1 b2, I x, or Z n seed")
