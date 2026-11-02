import LeanNative.Backend.LLVMAst

/-!
# LLVM AST executable regressions (C2a)

`#guard`s and non-vacuous regression theorems exercising `stepInstr`, `execBlock`,
`execFn`, byte-addressed memory, parallel phi, interprocedural calls, intrinsics,
IEEE 754 float semantics, and `llvm-as`-valid `PP` output.
-/

namespace LeanNative.Tests.LLVMAstTests

open LeanNative.Backend.LLVMAst
open LeanNative.Backend.TargetIR

def st0 : ExecState := {}

def i8v (n : Nat) : Operand := .constInt .i8 (BitVec.ofNat 8 n)
def i32v (n : Nat) : Operand := .constInt .i32 (BitVec.ofNat 32 n)
def i64v (n : Nat) : Operand := .constInt .i64 (BitVec.ofNat 64 n)

def i8b (n : Nat) : LLVMVal := .bits .i8 (BitVec.ofNat 8 n)
def i16b (n : Nat) : LLVMVal := .bits .i16 (BitVec.ofNat 16 n)
def i64b (n : Nat) : LLVMVal := .bits .i64 (BitVec.ofNat 64 n)
def i1b (b : Bool) : LLVMVal := .bits .i1 (if b then 1#1 else 0#1)

def isInrPoison (r : ExecOutcome ⊕ ExecState) : Bool :=
  match r with
  | .inr st => st.regs.head?.map (·.snd) == some .poison
  | _ => false

def isUb (msg : String) : ExecOutcome ⊕ ExecState → Bool
  | .inl (.ub m) => m == msg
  | _ => false

def isReturned (v : LLVMVal) : ExecOutcome → Bool
  | .returned (some w) => w == v
  | _ => false

def isOutOfFuel : ExecOutcome → Bool
  | .outOfFuel => true
  | _ => false

def boundReg (r : ExecOutcome ⊕ ExecState) : Option LLVMVal :=
  match r with
  | .inr st => st.regs.head?.map (·.snd)
  | _ => none

def addI8 (flags : OverflowFlags) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.add "r" flags .i8 (i8v a) (i8v b))

def subI8 (flags : OverflowFlags) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.sub "r" flags .i8 (i8v a) (i8v b))

def mulI8 (flags : OverflowFlags) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.mul "r" flags .i8 (i8v a) (i8v b))

#guard boundReg (addI8 .none 200 100) == some (i8b 44)
#guard isInrPoison (addI8 .nsw 200 100) = false
#guard isInrPoison (addI8 .nsw 100 100) = true
#guard isInrPoison (addI8 .nuw 200 100) = true
#guard isInrPoison (addI8 .nswNuw 1 1) = false
#guard boundReg (subI8 .none 5 10) == some (i8b 251)
#guard isInrPoison (subI8 .nuw 5 10) = true
#guard isInrPoison (subI8 .nsw 128 1) = true
#guard boundReg (mulI8 .none 20 20) == some (i8b 144)
#guard isInrPoison (mulI8 .nuw 20 20) = true
#guard isInrPoison (mulI8 .nsw 100 3) = true

def shlI8 (flags : OverflowFlags) (a amt : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.shl "r" flags .i8 (i8v a) (i8v amt))

#guard boundReg (shlI8 .none 3 2) == some (i8b 12)
#guard isInrPoison (shlI8 .none 1 8) = true
#guard isInrPoison (shlI8 .nuw 128 1) = true
#guard isInrPoison (shlI8 .nsw 64 1) = true

def lshrI8 (exact : Bool) (a amt : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.lshr "r" exact .i8 (i8v a) (i8v amt))

def ashrI8 (exact : Bool) (a amt : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.ashr "r" exact .i8 (i8v a) (i8v amt))

#guard boundReg (ashrI8 false 128 1) == some (i8b 192)
#guard isInrPoison (lshrI8 true 5 1) = true
#guard boundReg (lshrI8 true 6 1) == some (i8b 3)
#guard isInrPoison (ashrI8 true 253 1) = true

def udivI8 (exact : Bool) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.udiv "r" exact .i8 (i8v a) (i8v b))

def sdivI8 (exact : Bool) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.sdiv "r" exact .i8 (i8v a) (i8v b))

#guard isUb "division by zero" (udivI8 false 7 0)
#guard isUb "division by zero" (sdivI8 false 7 0)
#guard boundReg (udivI8 false 250 10) == some (i8b 25)
#guard isInrPoison (udivI8 true 7 2) = true
#guard boundReg (udivI8 true 8 2) == some (i8b 4)
#guard boundReg (sdivI8 false 250 2) == some (i8b 253)
#guard isInrPoison (sdivI8 true 251 2) = true
#guard isUb "signed division overflow" (sdivI8 false 128 255)

def uremI8 (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.urem "r" .i8 (i8v a) (i8v b))

#guard boundReg (uremI8 250 10) == some (i8b 0)
#guard isUb "division by zero" (uremI8 1 0)

def icmpI8 (p : ICmpPred) (a b : Nat) : Option LLVMVal :=
  boundReg (stepInstr {} 1 st0 (.icmp "c" p (.int .i8) (i8v a) (i8v b)))

#guard icmpI8 .ult 1 255 == some (i1b true)
#guard icmpI8 .slt 1 255 == some (i1b false)
#guard icmpI8 .eq 7 7 == some (i1b true)
#guard icmpI8 .sgt 255 1 == some (i1b false)

def icmpPtrTest : Bool :=
  let st : ExecState := { regs := [("p", .ptr 16#64), ("q", .ptr 32#64)] }
  boundReg (stepInstr {} 1 st (.icmp "c1" .ult (.ptr 0) (.reg "p") (.reg "q"))) == some (i1b true) &&
  boundReg (stepInstr {} 1 st (.icmp "c2" .eq (.ptr 0) (.reg "p") (.constNull))) == some (i1b false) &&
  boundReg (stepInstr {} 1 st0 (.icmp "c3" .eq (.ptr 0) .constNull .constNull)) == some (i1b true)

#guard icmpPtrTest

def selectI8 (cond : Operand) (t e : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} 1 st0 (.select "r" cond (.int .i8) (i8v t) (i8v e))

#guard boundReg (selectI8 (.constInt .i1 1#1) 3 4) == some (i8b 3)
#guard boundReg (selectI8 (.constInt .i1 0#1) 3 4) == some (i8b 4)
#guard isInrPoison (selectI8 .poison 3 4) = true

def phiPicks (prev : Option BlockLabel) : Bool :=
  resolvePhi st0 (.int .i8) prev [(.constInt .i8 1#8, "left"), (.constInt .i8 2#8, "right")] ==
    match prev with
    | some "left" => i8b 1
    | some "right" => i8b 2
    | _ => .poison

#guard phiPicks (some "left")
#guard phiPicks (some "right")
#guard phiPicks none
#guard phiPicks (some "missing")

def parallelPhiSwapFn : LLVMFn :=
  { name := "swap_phi"
    retTy := .int .i64
    params := [{ name := "a", ty := .int .i64 }, { name := "b", ty := .int .i64 }]
    blocks := [
      { label := "entry"
        body := [
          .add "x0" .none .i64 (.reg "a") (i64v 0),
          .add "y0" .none .i64 (.reg "b") (i64v 0)
        ]
        term := .br "loop" },
      { label := "loop"
        phis := [
          { dst := "x", ty := .int .i64, incomings := [(.reg "x0", "entry"), (.reg "y", "loop")] },
          { dst := "y", ty := .int .i64, incomings := [(.reg "y0", "entry"), (.reg "x", "loop")] }
        ]
        body := [.icmp "done" .eq (.int .i64) (.reg "x") (.reg "b")]
        term := .condBr (.reg "done") "exit" "loop" },
      { label := "exit"
        body := [.sub "diff" .none .i64 (.reg "x") (.reg "y")]
        term := .ret (some (.int .i64, .reg "diff")) }
    ] }

#guard isReturned (i64b 30) (execFn {} parallelPhiSwapFn [i64b 10, i64b 40] 8)

def storeLoadRoundtrip (n : Nat) : Bool :=
  match st0.mem.allocAligned 1 1 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    match stepInstr {} 1 st (.store false (.int .i8) (i8v n) (.reg "p") 1) with
    | .inr st2 =>
      match stepInstr {} 1 st2 (.load "out" false (.int .i8) (.reg "p") 1) with
      | .inr st3 => st3.regs.head?.map (·.snd) == some (i8b n)
      | _ => false
    | _ => false

#guard storeLoadRoundtrip 42
#guard storeLoadRoundtrip 255

def byteAliasSubslice : Bool :=
  match st0.mem.allocAligned 8 8 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    let word : BitVec 64 := 0x0807060504030201#64
    match stepInstr {} 1 st (.store false (.int .i64) (.constInt .i64 word) (.reg "p") 8) with
    | .inr st2 =>
      match stepInstr {} 1 st2 (.getelementptr "p2" true (.int .i8) (.reg "p") [(.i64, i64v 2)]) with
      | .inr st3 =>
        match stepInstr {} 1 st3 (.load "b2" false (.int .i16) (.reg "p2") 2) with
        | .inr st4 => st4.regs.head?.map (·.snd) == some (i16b 0x0403)
        | _ => false
      | _ => false
    | _ => false

#guard byteAliasSubslice

def structStoreLoadRoundtrip : Bool :=
  let sty := LLVMType.struct [.int .i32, .int .i64]
  match st0.mem.allocAligned sty.byteSize 8 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    let agg := Operand.constAgg [i32v 0x11223344, i64v 0x5566778899AABBCC]
    match stepInstr {} 1 st (.store false sty agg (.reg "p") 8) with
    | .inr st2 =>
      match stepInstr {} 1 st2 (.getelementptr "f1" true sty (.reg "p") [(.i64, i64v 0), (.i32, i32v 1)]) with
      | .inr st3 =>
        match stepInstr {} 1 st3 (.load "v1" false (.int .i64) (.reg "f1") 4) with
        | .inr st4 => st4.regs.head?.map (·.snd) == some (i64b 0x5566778899AABBCC)
        | _ => false
      | _ => false
    | _ => false

#guard structStoreLoadRoundtrip

def poisonStoreLoadsPoison : Bool :=
  match st0.mem.allocAligned 1 1 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    match stepInstr {} 1 st (.store false (.int .i8) .poison (.reg "p") 1) with
    | .inr st2 =>
      match stepInstr {} 1 st2 (.load "out" false (.int .i8) (.reg "p") 1) with
      | .inr st3 => st3.regs.head?.map (·.snd) == some .poison
      | _ => false
    | _ => false

#guard poisonStoreLoadsPoison

#guard isUb "load from null pointer" (stepInstr {} 1 st0 (.load "out" false (.int .i8) .constNull 1))

def misalignedLoadIsUb : Bool :=
  match st0.mem.allocAligned 8 8 with
  | none => false
  | some (ptr, mem1) =>
    let oddPtr := BitVec.ofNat 64 (ptr.toNat + 1)
    let st := { st0 with mem := mem1, regs := [("p", .ptr oddPtr)] }
    isUb "misaligned load" (stepInstr {} 1 st (.load "out" false (.int .i32) (.reg "p") 4))

#guard misalignedLoadIsUb

def oobLoadIsUb : Bool :=
  match st0.mem.allocAligned 4 4 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    isUb "load out of bounds" (stepInstr {} 1 st (.load "out" false (.int .i64) (.reg "p") 4))

#guard oobLoadIsUb

def gepSignedAndInbounds : Bool :=
  match st0.mem.allocAligned 16 8 with
  | none => false
  | some (ptr, mem1) =>
    let basePlus8 := BitVec.ofNat 64 (ptr.toNat + 8)
    let neg2 : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 2)
    let st := { st0 with mem := mem1, regs := [("p", .ptr basePlus8)] }
    let okBack :=
      boundReg (stepInstr {} 1 st (.getelementptr "q" true (.int .i32) (.reg "p") [(.i64, .constInt .i64 neg2)])) ==
        some (.ptr ptr)
    let poisonOob :=
      isInrPoison (stepInstr {} 1 st (.getelementptr "q2" true (.int .i64) (.reg "p") [(.i64, i64v 5)]))
    let nonInboundsOk :=
      boundReg (stepInstr {} 1 st (.getelementptr "q3" false (.int .i64) (.reg "p") [(.i64, i64v 5)])) ==
        some (.ptr (BitVec.ofNat 64 (basePlus8.toNat + 40)))
    okBack && poisonOob && nonInboundsOk

#guard gepSignedAndInbounds

def bitcastRoundtrip : Bool :=
  let d1bits : BitVec 64 := 0x3FF0000000000000#64
  let r1 := boundReg (stepInstr {} 1 st0 (.bitcast "i" (.float .f64) (.constFloat .f64 d1bits) (.int .i64)))
  let v16 := Operand.constAgg (List.replicate 16 (.constInt .i8 1#8))
  let r2 := stepInstr {} 1 st0 (.bitcast "w" (.vec 16 (.int .i8)) v16 (.vec 2 (.int .i64)))
  let bad := isUb "bitcast size mismatch" (stepInstr {} 1 st0 (.bitcast "bad" (.int .i32) (i32v 1) (.int .i64)))
  r1 == some (.bits .i64 d1bits) &&
    (match r2 with | .inr _ => true | _ => false) &&
    bad

#guard bitcastRoundtrip

def rmwAllOps : Bool :=
  match st0.mem.allocAligned 8 8 with
  | none => false
  | some (ptr, mem1) =>
    let mem2 := mem1.storeInt ptr .i64 10#64
    let st := { st0 with mem := mem2, regs := [("p", .ptr ptr)] }
    match stepInstr {} 1 st (.atomicrmw "o1" .add (.reg "p") (.int .i64) (i64v 5) .seqCst 8) with
    | .inr st2 =>
      match stepInstr {} 1 st2 (.atomicrmw "o2" .umax (.reg "p") (.int .i64) (i64v 20) .acqRel 8) with
      | .inr st3 =>
        st2.regs.head?.map (·.snd) == some (i64b 10) &&
        st3.regs.head?.map (·.snd) == some (i64b 15) &&
        st3.mem.loadInt? ptr .i64 == some 20#64
      | _ => false
    | _ => false

#guard rmwAllOps

def floatIEEEChecks : Bool :=
  let posZero64 : BitVec 64 := 0x0000000000000000#64
  let negZero64 : BitVec 64 := 0x8000000000000000#64
  let one64 : BitVec 64 := 0x3FF0000000000000#64
  let two64 : BitVec 64 := 0x4000000000000000#64
  let three64 : BitVec 64 := 0x4008000000000000#64
  let qnan64 : BitVec 64 := 0x7FF8000000000000#64
  let inf64 : BitVec 64 := 0x7FF0000000000000#64
  let addOk :=
    boundReg (stepInstr {} 1 st0 (.fadd "s" .f64 (.constFloat .f64 one64) (.constFloat .f64 two64))) ==
      some (.floatBits .f64 three64)
  let divZeroInf :=
    boundReg (stepInstr {} 1 st0 (.fdiv "inf" .f64 (.constFloat .f64 one64) (.constFloat .f64 posZero64))) ==
      some (.floatBits .f64 inf64)
  let zEq :=
    boundReg (stepInstr {} 1 st0 (.fcmp "z" .oeq .f64 (.constFloat .f64 posZero64) (.constFloat .f64 negZero64))) ==
      some (i1b true)
  let nanOeq :=
    boundReg (stepInstr {} 1 st0 (.fcmp "no" .oeq .f64 (.constFloat .f64 qnan64) (.constFloat .f64 one64))) ==
      some (i1b false)
  let nanUne :=
    boundReg (stepInstr {} 1 st0 (.fcmp "nu" .une .f64 (.constFloat .f64 qnan64) (.constFloat .f64 one64))) ==
      some (i1b true)
  let nanUno :=
    boundReg (stepInstr {} 1 st0 (.fcmp "un" .uno .f64 (.constFloat .f64 qnan64) (.constFloat .f64 one64))) ==
      some (i1b true)
  let nanOrd :=
    boundReg (stepInstr {} 1 st0 (.fcmp "or" .ord .f64 (.constFloat .f64 one64) (.constFloat .f64 two64))) ==
      some (i1b true)
  addOk && divZeroInf && zEq && nanOeq && nanUne && nanUno && nanOrd

#guard floatIEEEChecks

def calleeAddFn : LLVMFn :=
  { name := "callee_add"
    retTy := .int .i64
    params := [{ name := "x", ty := .int .i64 }, { name := "y", ty := .int .i64 }]
    blocks := [{
      label := "entry"
      body := [.add "s" .none .i64 (.reg "x") (.reg "y")]
      term := .ret (some (.int .i64, .reg "s"))
    }] }

def callerFn : LLVMFn :=
  { name := "caller"
    retTy := .int .i64
    params := [{ name := "a", ty := .int .i64 }]
    blocks := [{
      label := "entry"
      body := [
        .call (some "tmp") (.int .i64) "callee_add" [(.int .i64, .reg "a"), (.int .i64, i64v 7)],
        .call (some "bs") (.int .i64) "llvm.bswap.i64" [(.int .i64, .constInt .i64 0x0102030405060708#64)],
        .call (some "lz") (.int .i64) "llvm.ctlz.i64" [(.int .i64, .constInt .i64 0x0000000100000000#64), (.int .i1, .constInt .i1 0#1)],
        .add "res1" .none .i64 (.reg "tmp") (.reg "lz")
      ]
      term := .ret (some (.int .i64, .reg "res1"))
    }] }

def callMod : LLVMModule :=
  { dataLayout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
    triple := "x86_64-unknown-linux-gnu"
    externs := [
      { name := "llvm.bswap.i64", retTy := .int .i64, paramTys := [.int .i64] },
      { name := "llvm.ctlz.i64", retTy := .int .i64, paramTys := [.int .i64, .int .i1] }
    ]
    fns := [calleeAddFn, callerFn] }

#guard isReturned (i64b (10 + 7 + 31)) (execFn callMod callerFn [i64b 10] 4)
#guard isUb "unmodeled external call"
  (stepInstr callMod 2 st0 (.call (some "x") (.int .i64) "unknown_ext" []))
#guard isInrPoison
  (stepInstr callMod 2 st0 (.call (some "z") (.int .i64) "llvm.ctlz.i64"
    [(.int .i64, i64v 0), (.int .i1, .constInt .i1 1#1)]))

def wideSwitchFn (hi : Bool) : LLVMFn :=
  let matchKey : BitVec 256 := (1#256 <<< 200) ||| 7#256
  let otherKey : BitVec 256 := 7#256
  let scrut : BitVec 256 := if hi then matchKey else otherKey
  { name := "wide_sw"
    retTy := .int .i8
    params := []
    blocks := [
      { label := "entry"
        term := .switch .i256 (.constInt .i256 scrut) "def" [(matchKey, "hit")] },
      { label := "hit", term := .ret (some (.int .i8, i8v 77)) },
      { label := "def", term := .ret (some (.int .i8, i8v 11)) }
    ] }

#guard isReturned (i8b 77) (execFn {} (wideSwitchFn true) [] 4)
#guard isReturned (i8b 11) (execFn {} (wideSwitchFn false) [] 4)

def retFn : LLVMFn :=
  { name := "id"
    retTy := .int .i8
    params := [{ name := "x", ty := .int .i8, attrs := [.noundef] }]
    blocks := [{
      label := "entry"
      term := .ret (some (.int .i8, .reg "x"))
    }] }

def loopFn : LLVMFn :=
  { name := "spin"
    retTy := .void
    params := []
    blocks := [{ label := "entry", term := .br "entry" }] }

#guard isReturned (i8b 9) (execFn {} retFn [i8b 9] 4)
#guard isOutOfFuel (execFn {} loopFn [] 3)
#guard isOutOfFuel (execFn {} loopFn [] 8) && (execFn {} loopFn [] 0 == .outOfFuel)

def vecInsertExtract : Bool :=
  let vecOp := Operand.constAgg [.constInt .i8 1#8, .constInt .i8 2#8]
  match stepInstr {} 1 st0 (.insertelement "v" 2 (.int .i8) vecOp (.constInt .i8 9#8) .i32 (.constInt .i32 1#32)) with
  | .inr st1 =>
    match st1.regs.head? with
    | some (_, v) =>
      match stepInstr {} 1 { regs := [("v", v)] }
          (.extractelement "e" 2 (.int .i8) (.reg "v") .i32 (.constInt .i32 1#32)) with
      | .inr st2 => st2.regs.head?.map (·.snd) == some (i8b 9)
      | _ => false
    | _ => false
  | _ => false

#guard vecInsertExtract

def aggInsertExtract : Bool :=
  let aggOp := Operand.constAgg [.constInt .i8 1#8, .constInt .i64 2#64]
  let ty := LLVMType.struct [.int .i8, .int .i64]
  match stepInstr {} 1 st0 (.insertvalue "a" ty aggOp (.int .i64) (i64v 77) [1]) with
  | .inr st1 =>
    match st1.regs.head? with
    | some (_, v) =>
      match stepInstr {} 1 { regs := [("a", v)] } (.extractvalue "e" ty (.reg "a") [1]) with
      | .inr st2 => st2.regs.head?.map (·.snd) == some (i64b 77)
      | _ => false
    | _ => false
  | _ => false

#guard aggInsertExtract

#guard PP.ppInstr (.add "r" .nsw .i8 (.constInt .i8 1#8) (.constInt .i8 2#8)) ==
  "%r = add nsw i8 1, 2"
#guard PP.ppType (.int .i256) == "i256"
#guard PP.ppType (.ptr 0) == "ptr"
#guard PP.ppType (.ptr 3) == "ptr addrspace(3)"
#guard PP.ppType .void == "void"
#guard PP.ppType (LLVMType.struct [.int .i8, .array 4 (.vec 2 (.int .i32))]) ==
  "{ i8, [4 x <2 x i32>] }"
#guard PP.ppFloatHex .f32 0x3F800000#32 == "0x3FF0000000000000"
#guard PP.ppFloatHex .f32 0x7F800001#32 == "0x7FF0000020000000"

def fullIRFixtureFn : LLVMFn :=
  let pairTy := LLVMType.struct [.int .i32, .int .i64]
  let ovTy := LLVMType.struct [.int .i64, .int .i1]
  { name := "all_forms"
    cc := .fastcc
    retTy := .int .i64
    params := [
      { name := "arg", ty := .int .i64, attrs := [.noundef] },
      { name := "inptr", ty := .ptr 0, attrs := [.noalias, .nocapture] }
    ]
    blocks := [
      { label := "entry"
        body := [
          .alloca "slot" pairTy 8,
          .store false pairTy (Operand.constAgg [i32v 3, i64v 9]) (.reg "slot") 8,
          .getelementptr "fld" true pairTy (.reg "slot") [(.i64, i64v 0), (.i32, i32v 1)],
          .load "loaded" false (.int .i64) (.reg "fld") 4,
          .add "a1" .nsw .i64 (.reg "loaded") (.reg "arg"),
          .sub "a2" .nuw .i64 (.reg "a1") (i64v 1),
          .mul "a3" .none .i64 (.reg "a2") (i64v 2),
          .udiv "a4" true .i64 (.reg "a3") (i64v 2),
          .sdiv "a5" false .i64 (.reg "a4") (i64v 1),
          .urem "a6" .i64 (.reg "a5") (i64v 97),
          .srem "a7" .i64 (.reg "a6") (i64v 50),
          .and_ "b1" .i64 (.reg "a7") (i64v 255),
          .or_ "b2" .i64 (.reg "b1") (i64v 16),
          .xor "b3" .i64 (.reg "b2") (i64v 3),
          .shl "s1" .nuw .i64 (.reg "b3") (i64v 1),
          .lshr "s2" true .i64 (.reg "s1") (i64v 1),
          .ashr "s3" false .i64 (.reg "s2") (i64v 0),
          .trunc "n32" .i64 (.reg "s3") .i32,
          .zext "z64" .i32 (.reg "n32") .i64,
          .sext "x64" .i32 (.reg "n32") .i64,
          .fadd "fa" .f64 (.constFloat .f64 0x3FF0000000000000#64) (.constFloat .f64 0x4000000000000000#64),
          .fsub "fs" .f32 (.constFloat .f32 0x3F800000#32) (.constFloat .f32 0x00000000#32),
          .fmul "fm" .f64 (.reg "fa") (.constFloat .f64 0x4000000000000000#64),
          .fdiv "fd" .f64 (.reg "fm") (.constFloat .f64 0x4000000000000000#64),
          .fcmp "fc" .oeq .f64 (.reg "fd") (.reg "fa"),
          .bitcast "fcast" (.float .f32) (.reg "fs") (.int .i32),
          .ptrtoint "pi" 0 (.reg "inptr") .i64,
          .inttoptr "ip" .i64 (.reg "pi") 0,
          .icmp "pcmp" .eq (.ptr 0) (.reg "ip") (.reg "inptr"),
          .select "sel" (.reg "pcmp") (.int .i64) (.reg "z64") (.reg "x64"),
          .atomicrmw "old" .add (.reg "fld") (.int .i64) (i64v 4) .seqCst 8,
          .insertelement "v1" 2 (.int .i64) .constZero (.reg "sel") .i32 (i32v 0),
          .shufflevector "v2" 2 2 (.int .i64) (.reg "v1") .constZero [0, 2],
          .extractelement "ve" 2 (.int .i64) (.reg "v2") .i32 (i32v 0),
          .call (some "ov") ovTy "llvm.uadd.with.overflow.i64" [(.int .i64, .reg "ve"), (.int .i64, .reg "old")],
          .extractvalue "sum" ovTy (.reg "ov") [0],
          .insertvalue "pair2" pairTy .constZero (.int .i64) (.reg "sum") [1],
          .extractvalue "out0" pairTy (.reg "pair2") [1]
        ]
        term := .condBr (.reg "fc") "swblk" "trapblk" },
      { label := "swblk"
        phis := [
          { dst := "phi_v", ty := .int .i64, incomings := [(.reg "out0", "entry")] },
          { dst := "phi_pair", ty := pairTy, incomings := [(Operand.constAgg [i32v 3, i64v 9], "entry")] }
        ]
        term := .switch .i64 (.reg "phi_v") "retblk" [(0#64, "retblk"), (1#64, "retblk")] },
      { label := "retblk"
        phis := [
          { dst := "ans"
            ty := .int .i64
            incomings := [(.reg "phi_v", "swblk"), (.reg "phi_v", "swblk"), (.reg "phi_v", "swblk")] }
        ]
        term := .ret (some (.int .i64, .reg "ans")) },
      { label := "trapblk"
        body := [.call none .void "llvm.trap" []]
        term := .unreachable }
    ] }

def fullIRFixtureModule : LLVMModule :=
  { dataLayout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
    triple := "x86_64-unknown-linux-gnu"
    globals := [
      { name := "g_const", linkage := .private_, isConstant := true, ty := .int .i64, init := some (i64v 42), align := 8 },
      { name := "g_pair", linkage := .private_, isConstant := true,
        ty := LLVMType.struct [.int .i32, .int .i64], init := some (Operand.constAgg [i32v 3, i64v 9]), align := 8 },
      { name := "g_zero", linkage := .internal, isConstant := false, ty := .array 4 (.int .i32), init := none, align := 16 },
      { name := "g_ext", linkage := .external, isConstant := false, ty := .int .i64, init := none, align := 8 }
    ]
    externs := [
      { name := "llvm.uadd.with.overflow.i64", retTy := LLVMType.struct [.int .i64, .int .i1], paramTys := [.int .i64, .int .i64] },
      { name := "llvm.trap", retTy := .void, paramTys := [] }
    ]
    fns := [retFn, calleeAddFn, callerFn, fullIRFixtureFn] }

def renderedFullIR : String := PP.ppModule fullIRFixtureModule

#guard renderedFullIR.startsWith "target datalayout ="
#guard isReturned (i64b 26) (execFn fullIRFixtureModule fullIRFixtureFn [i64b 10, .ptr 4096#64] 16)

-- ABI layout & alignment checks (matching x86_64 DataLayout / LLVM 18)
#guard (LLVMType.int .i256).abiAlign == 16 && (LLVMType.int .i512).abiAlign == 16
#guard (LLVMType.vec 3 (.int .i32)).byteSize == 16 && (LLVMType.vec 3 (.int .i32)).abiAlign == 16
#guard (LLVMType.vec 4 (.int .i64)).byteSize == 32 && (LLVMType.vec 4 (.int .i64)).abiAlign == 32
#guard (LLVMType.vec 8 (.int .i1)).byteSize == 1 && (LLVMType.vec 8 (.int .i1)).abiAlign == 1
#guard (LLVMType.vec 16 (.int .i1)).byteSize == 2 && (LLVMType.vec 16 (.int .i1)).abiAlign == 2
#guard (LLVMType.struct []).byteSize == 0 && (LLVMType.struct []).abiAlign == 1
#guard (LLVMType.struct [.int .i32, .int .i64]).byteSize == 16 &&
  (LLVMType.struct [.int .i32, .int .i64]).abiAlign == 8
#guard (LLVMType.struct [.int .i32, .int .i64] true).byteSize == 12 &&
  (LLVMType.struct [.int .i32, .int .i64] true).abiAlign == 1
#guard (LLVMType.struct [.int .i64, .int .i256, .int .i64]).byteSize == 64 &&
  (LLVMType.struct [.int .i64, .int .i256, .int .i64]).abiAlign == 16
#guard (LLVMType.struct [.int .i64, .int .i1]).byteSize == 16 &&
  (LLVMType.struct [.int .i64, .int .i1]).abiAlign == 8
#guard (LLVMType.struct [.int .i8, .vec 4 (.int .i64)]).byteSize == 64 &&
  (LLVMType.struct [.int .i8, .vec 4 (.int .i64)]).abiAlign == 32

-- <8 x i1> LE bit-packing and <3 x i32> -> <6 x i16> bitcast
def i1VecBitpackCheck : Bool :=
  let v8 := Operand.constAgg [
    .constInt .i1 1#1, .constInt .i1 0#1, .constInt .i1 1#1, .constInt .i1 0#1,
    .constInt .i1 0#1, .constInt .i1 0#1, .constInt .i1 0#1, .constInt .i1 1#1
  ]
  let bc1 := boundReg (stepInstr {} 1 st0 (.bitcast "b" (.vec 8 (.int .i1)) v8 (.int .i8))) == some (i8b 133)
  let bc2 :=
    match stepInstr {} 1 st0 (.bitcast "v" (.int .i8) (i8v 133) (.vec 8 (.int .i1))) with
    | .inr st1 =>
      match st1.regs.head? with
      | some (_, vecVal) =>
        let rst : ExecState := { regs := [("v", vecVal)] }
        boundReg (stepInstr {} 1 rst (.extractelement "e0" 8 (.int .i1) (.reg "v") .i32 (i32v 0))) == some (i1b true) &&
        boundReg (stepInstr {} 1 rst (.extractelement "e1" 8 (.int .i1) (.reg "v") .i32 (i32v 1))) == some (i1b false) &&
        boundReg (stepInstr {} 1 rst (.extractelement "e2" 8 (.int .i1) (.reg "v") .i32 (i32v 2))) == some (i1b true) &&
        boundReg (stepInstr {} 1 rst (.extractelement "e7" 8 (.int .i1) (.reg "v") .i32 (i32v 7))) == some (i1b true)
      | none => false
    | _ => false
  let vPoison := Operand.constAgg [
    .constInt .i1 1#1, .poison, .constInt .i1 1#1, .constInt .i1 0#1,
    .constInt .i1 0#1, .constInt .i1 0#1, .constInt .i1 0#1, .constInt .i1 1#1
  ]
  let bcPoison := isInrPoison (stepInstr {} 1 st0 (.bitcast "bp" (.vec 8 (.int .i1)) vPoison (.int .i8)))
  let v3i32 := Operand.constAgg [i32v 1, i32v 2, i32v 3]
  let bcVec :=
    match stepInstr {} 1 st0 (.bitcast "v6" (.vec 3 (.int .i32)) v3i32 (.vec 6 (.int .i16))) with
    | .inr st1 =>
      match st1.regs.head? with
      | some (_, v6) =>
        v6.toList? == some [i16b 1, i16b 0, i16b 2, i16b 0, i16b 3, i16b 0]
      | none => false
    | _ => false
  bc1 && bc2 && bcPoison && bcVec

#guard i1VecBitpackCheck

-- Bitcast legality (reject ptr <-> int, cross-addrspace ptr, aggregate <-> int)
#guard isUb "bitcast size mismatch" (stepInstr {} 1 st0 (.bitcast "bad1" (.ptr 0) .constNull (.int .i64)))
#guard isUb "bitcast size mismatch" (stepInstr {} 1 st0 (.bitcast "bad2" (.ptr 0) .constNull (.ptr 3)))
#guard isUb "bitcast size mismatch"
  (stepInstr {} 1 st0 (.bitcast "bad3" (LLVMType.struct [.int .i64]) .constZero (.int .i64)))
#guard boundReg (stepInstr {} 1 st0 (.bitcast "okp" (.ptr 0) .constNull (.ptr 0))) == some (.ptr 0#64)

-- Division / remainder poison vs UB precedence
#guard isUb "division by zero" (stepInstr {} 1 st0 (.udiv "r" false .i8 .poison (i8v 0)))
#guard isUb "division by poison" (stepInstr {} 1 st0 (.udiv "r" false .i8 (i8v 1) .poison))
#guard isInrPoison (stepInstr {} 1 st0 (.udiv "r" false .i8 .poison (i8v 2)))
#guard isUb "signed division overflow" (stepInstr {} 1 st0 (.sdiv "r" false .i8 .poison (i8v 255)))
#guard isInrPoison (stepInstr {} 1 st0 (.sdiv "r" false .i8 .poison (i8v 2)))

-- OOB extractelement / insertelement -> poison (not UB)
#guard isInrPoison
  (stepInstr {} 1 st0 (.extractelement "oob1" 2 (.int .i8) .constZero .i32 (i32v 2)))
#guard isInrPoison
  (stepInstr {} 1 st0 (.insertelement "oob2" 2 (.int .i8) .constZero (i8v 7) .i32 (i32v 5)))

-- Alignment 0 uses ABI align; non-pow2 alignment is UB
def alignChecks : Bool :=
  match st0.mem.allocAligned 8 8 with
  | none => false
  | some (ptr, mem1) =>
    let mem2 := mem1.storeInt ptr .i64 99#64
    let oddPtr := BitVec.ofNat 64 (ptr.toNat + 4)
    let st := { st0 with mem := mem2, regs := [("p", .ptr ptr), ("odd", .ptr oddPtr)] }
    boundReg (stepInstr {} 1 st (.load "ok" false (.int .i64) (.reg "p") 0)) == some (i64b 99) &&
    isUb "misaligned load" (stepInstr {} 1 st (.load "mis" false (.int .i64) (.reg "odd") 0)) &&
    isUb "invalid alignment" (stepInstr {} 1 st (.load "bad" false (.int .i64) (.reg "p") 3))

#guard alignChecks

-- Globals (@sym), constant global write -> UB, calling convention mismatch -> UB, addrspace PP
def globalAndCCFn : LLVMFn :=
  let pairTy := LLVMType.struct [.int .i32, .int .i64]
  { name := "read_globals"
    cc := .ccc
    retTy := .int .i64
    params := []
    blocks := [{
      label := "entry"
      body := [
        .load "c" false (.int .i64) (.global "g_const") 8,
        .getelementptr "pf" true pairTy (.global "g_pair") [(.i64, i64v 0), (.i32, i32v 1)],
        .load "p1" false (.int .i64) (.reg "pf") 8,
        .add "sum" .nsw .i64 (.reg "c") (.reg "p1")
      ]
      term := .ret (some (.int .i64, .reg "sum"))
    }] }

def writeConstGlobalFn : LLVMFn :=
  { name := "write_const"
    cc := .ccc
    retTy := .void
    params := []
    blocks := [{
      label := "entry"
      body := [.store false (.int .i64) (i64v 1) (.global "g_const") 8]
      term := .ret none
    }] }

def badCCCallerFn : LLVMFn :=
  { name := "bad_cc"
    cc := .ccc
    retTy := .int .i64
    params := []
    blocks := [{
      label := "entry"
      body := [.call (some "r") (.int .i64) "all_forms" [(.int .i64, i64v 1), (.ptr 0, .constNull)] .ccc]
      term := .ret (some (.int .i64, .reg "r"))
    }] }

#guard isReturned (i64b 51) (execFn fullIRFixtureModule globalAndCCFn [] 4)
#guard execFn fullIRFixtureModule writeConstGlobalFn [] 4 == .ub "store out of bounds"
#guard execFn fullIRFixtureModule badCCCallerFn [] 4 == .ub "calling convention mismatch"

#guard PP.ppType (LLVMType.struct [.int .i32, .int .i64] true) == "<{ i32, i64 }>"
#guard PP.ppInstr (.load "x" false (.int .i32) (.reg "p") 4 3) ==
  "%x = load i32, ptr addrspace(3) %p, align 4"
#guard PP.ppInstr (.store false (.int .i32) (i32v 7) (.reg "p") 0 3) ==
  "store i32 7, ptr addrspace(3) %p"
#guard PP.ppInstr (.call (some "r") (.int .i64) "fn_fast" [(.int .i64, i64v 1)] .fastcc) ==
  "%r = call fastcc i64 @fn_fast(i64 1)"

theorem retFn_returns_arg (v : LLVMVal) (fuel : Nat) (hf : 0 < fuel) :
    execFn {} retFn [v] fuel = .returned (some v) := by
  cases fuel with
  | zero => omega
  | succ _ =>
    cases v <;> rfl

theorem nested_struct_ppType_injective (t1 t2 : LLVMType)
    (h : PP.ppType (LLVMType.struct [t1, .vec 4 t2]) = PP.ppType (LLVMType.struct [t2, .vec 4 t1])) :
    t1 = t2 := by
  have hinj := ppType_injective _ _ h
  injection hinj with _ hfs
  injection hfs with ht1 _

end LeanNative.Tests.LLVMAstTests
