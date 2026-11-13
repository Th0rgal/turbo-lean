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

def main (args : List String) : IO Unit := do
  let u := fun (s : String) => s.toNat!.toUInt64
  match args with
  | ["K", a, b] => IO.println (kmul (u a) (u b))
  | ["E", a0, a1, a2, b0, b1, b2] =>
    IO.println (emul0 (u a0) (u a1) (u a2) (u b0) (u b1) (u b2))
    IO.println (emul1 (u a0) (u a1) (u a2) (u b0) (u b1) (u b2))
    IO.println (emul2 (u a0) (u a1) (u a2) (u b0) (u b1) (u b2))
  | ["I", x] => IO.println (identity (u x))
  | _ => throw (IO.userError "expected K a b, E a0 a1 a2 b0 b1 b2, or I x")
