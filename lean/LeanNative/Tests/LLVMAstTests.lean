import LeanNative.Backend.LLVMAst

/-!
# LLVM AST executable regressions (C2a)

`#guard`s that drive `stepInstr`, `execBlock`, `execFn`, and `PP` on concrete
operands. Constants are reduced by the evaluator, not by a closed `Bool` literal.
-/

namespace LeanNative.Tests.LLVMAstTests

open LeanNative.Backend.LLVMAst
open LeanNative.Backend.TargetIR

def st0 : ExecState := {}

def i8v (n : Nat) : Operand := .constInt .i8 (BitVec.ofNat 8 n)

def i8b (n : Nat) : LLVMVal := .bits .i8 (BitVec.ofNat 8 n)

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

def addI8 (flags : OverflowFlags) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.add "r" flags .i8 (i8v a) (i8v b))

def subI8 (flags : OverflowFlags) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.sub "r" flags .i8 (i8v a) (i8v b))

def mulI8 (flags : OverflowFlags) (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.mul "r" flags .i8 (i8v a) (i8v b))

def boundReg (r : ExecOutcome ⊕ ExecState) : Option LLVMVal :=
  match r with
  | .inr st => st.regs.head?.map (·.snd)
  | _ => none

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
  stepInstr {} st0 (.shl "r" flags .i8 (i8v a) (i8v amt))

#guard boundReg (shlI8 .none 3 2) == some (i8b 12)
#guard isInrPoison (shlI8 .none 1 8) = true
#guard isInrPoison (shlI8 .nuw 128 1) = true
#guard isInrPoison (shlI8 .nsw 64 1) = true

def ashrI8 (a amt : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.ashr "r" .i8 (i8v a) (i8v amt))

#guard boundReg (ashrI8 128 1) == some (i8b 192)

def udivI8 (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.udiv "r" .i8 (i8v a) (i8v b))

def sdivI8 (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.sdiv "r" .i8 (i8v a) (i8v b))

#guard isUb "division by zero" (udivI8 7 0)
#guard isUb "division by zero" (sdivI8 7 0)
#guard boundReg (udivI8 250 10) == some (i8b 25)
#guard boundReg (sdivI8 250 2) == some (i8b 253)
#guard isUb "signed division overflow" (sdivI8 128 255)

def uremI8 (a b : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.urem "r" .i8 (i8v a) (i8v b))

#guard boundReg (uremI8 250 10) == some (i8b 0)
#guard isUb "division by zero" (uremI8 1 0)

def icmpI8 (p : ICmpPred) (a b : Nat) : Option LLVMVal :=
  boundReg (stepInstr {} st0 (.icmp "c" p .i8 (i8v a) (i8v b)))

#guard icmpI8 .ult 1 255 == some (i1b true)
#guard icmpI8 .slt 1 255 == some (i1b false)
#guard icmpI8 .eq 7 7 == some (i1b true)
#guard icmpI8 .sgt 255 1 == some (i1b false)

def selectI8 (cond : Operand) (t e : Nat) : ExecOutcome ⊕ ExecState :=
  stepInstr {} st0 (.select "r" cond (.int .i8) (i8v t) (i8v e))

#guard boundReg (selectI8 (.constInt .i1 1#1) 3 4) == some (i8b 3)
#guard boundReg (selectI8 (.constInt .i1 0#1) 3 4) == some (i8b 4)
#guard isInrPoison (selectI8 .poison 3 4) = true

def phiPicks (prev : Option BlockLabel) : Bool :=
  resolvePhi st0 prev [(.constInt .i8 1#8, "left"), (.constInt .i8 2#8, "right")] ==
    match prev with
    | some "left" => i8b 1
    | some "right" => i8b 2
    | _ => .poison

#guard phiPicks (some "left")
#guard phiPicks (some "right")
#guard phiPicks none
#guard phiPicks (some "missing")

def storeLoadRoundtrip (n : Nat) : Bool :=
  match st0.mem.allocAligned 1 1 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    match stepInstr {} st (.store (.int .i8) (i8v n) (.reg "p") 1) with
    | .inr st2 =>
      match stepInstr {} st2 (.load "out" (.int .i8) (.reg "p") 1) with
      | .inr st3 => st3.regs.head?.map (·.snd) == some (i8b n)
      | _ => false
    | _ => false

#guard storeLoadRoundtrip 42
#guard storeLoadRoundtrip 255

def poisonStoreLoadsPoison : Bool :=
  match st0.mem.allocAligned 1 1 with
  | none => false
  | some (ptr, mem1) =>
    let st := { st0 with mem := mem1, regs := [("p", .ptr ptr)] }
    match stepInstr {} st (.store (.int .i8) .poison (.reg "p") 1) with
    | .inr st2 =>
      match stepInstr {} st2 (.load "out" (.int .i8) (.reg "p") 1) with
      | .inr st3 => st3.regs.head?.map (·.snd) == some .poison
      | _ => false
    | _ => false

#guard poisonStoreLoadsPoison

def nullLoadIsUb : Bool :=
  isUb "load from null pointer" (stepInstr {} st0 (.load "out" (.int .i8) .constNull 1))

#guard nullLoadIsUb

def gepScales : Bool :=
  boundReg (stepInstr {} { regs := [("p", .ptr (BitVec.ofNat 64 16))] }
    (.getelementptr "q" (.int .i8) (.reg "p") [.constInt .i64 4#64])) ==
    some (.ptr (BitVec.ofNat 64 20))

#guard gepScales

def rmwAdd : Bool :=
  match st0.mem.allocAligned 1 1 with
  | none => false
  | some (ptr, mem1) =>
    let mem2 := mem1.storeInt ptr .i8 10#8
    let st := { st0 with mem := mem2, regs := [("p", .ptr ptr)] }
    match stepInstr {} st (.atomicrmw "old" .add (.reg "p") .i8 (i8v 5) .monotonic 1) with
    | .inr st2 =>
      st2.regs.head?.map (·.snd) == some (i8b 10) && st2.mem.loadInt ptr .i8 == 15#8
    | _ => false

#guard rmwAdd

def retFn : LLVMFn :=
  { name := "id"
    retTy := .int .i8
    params := [{ name := "x", ty := .int .i8 }]
    blocks := [{
      label := "entry"
      term := .ret (some (.int .i8, .reg "x"))
    }] }

#guard isReturned (i8b 9) (execFn {} retFn [i8b 9] 4)

def loopFn : LLVMFn :=
  { name := "spin"
    retTy := .void
    params := []
    blocks := [{ label := "entry", term := .br "entry" }] }

#guard isOutOfFuel (execFn {} loopFn [] 3)
#guard isOutOfFuel (execFn {} loopFn [] 8) && (execFn {} loopFn [] 0 == .outOfFuel)

def condFn (c : Bool) : LLVMFn :=
  let bit : BitVec 1 := if c then 1#1 else 0#1
  { name := "pick"
    retTy := .int .i8
    params := []
    blocks := [
      { label := "entry"
        term := .condBr (.constInt .i1 bit) "t" "e" },
      { label := "t"
        term := .ret (some (.int .i8, .constInt .i8 1#8)) },
      { label := "e"
        term := .ret (some (.int .i8, .constInt .i8 2#8)) }
    ] }

#guard isReturned (i8b 1) (execFn {} (condFn true) [] 4)
#guard isReturned (i8b 2) (execFn {} (condFn false) [] 4)

def switchFn (k : Nat) : LLVMFn :=
  { name := "sw"
    retTy := .int .i8
    params := []
    blocks := [
      { label := "entry"
        term := .switch .i8 (.constInt .i8 (BitVec.ofNat 8 k)) "def"
          [(1#64, "one"), (2#64, "two")] },
      { label := "one", term := .ret (some (.int .i8, .constInt .i8 11#8)) },
      { label := "two", term := .ret (some (.int .i8, .constInt .i8 22#8)) },
      { label := "def", term := .ret (some (.int .i8, .constInt .i8 99#8)) }
    ] }

#guard isReturned (i8b 11) (execFn {} (switchFn 1) [] 4)
#guard isReturned (i8b 22) (execFn {} (switchFn 2) [] 4)
#guard isReturned (i8b 99) (execFn {} (switchFn 7) [] 4)

def phiLoop : LLVMFn :=
  { name := "count"
    retTy := .int .i8
    params := []
    blocks := [
      { label := "entry"
        body := [.add "i" .none .i8 (.constInt .i8 0#8) (.constInt .i8 0#8)]
        term := .br "body" },
      { label := "body"
        phis := [.phi "x" (.int .i8) [(.reg "i", "entry"), (.reg "y", "body")]]
        body := [.add "y" .none .i8 (.reg "x") (.constInt .i8 1#8)]
        term := .condBr (.constInt .i1 0#1) "body" "done" },
      { label := "done"
        term := .ret (some (.int .i8, .reg "y")) }
    ] }

#guard isReturned (i8b 1) (execFn {} phiLoop [] 8)

def ppAdd : String :=
  PP.ppInstr (.add "r" .nsw .i8 (.constInt .i8 1#8) (.constInt .i8 2#8))

#guard ppAdd == "%r = add nsw i8 i8 1, i8 2"

def ppRound (ins : LLVMInstr) : Bool :=
  PP.ppInstr ins ≠ "" && (PP.ppInstr ins).length > 3

#guard ppRound (.udiv "q" .i32 (.reg "a") (.reg "b"))
#guard ppRound (.atomicrmw "o" .xchg (.reg "p") .i64 (.reg "v") .seqCst 8)
#guard ppRound (.phi "x" (.int .i64) [(.reg "a", "L"), (.reg "b", "R")])
#guard PP.ppType (.int .i256) == "i256"
#guard PP.ppType (.ptr 0) == "ptr"
#guard PP.ppType .void == "void"
#guard PP.ppType (LLVMType.struct [.int .i8, .int .i32]) == "{ i8, i32 }"
#guard (PP.ppModule { dataLayout := "e", triple := "x", fns := [retFn] }).startsWith "target datalayout = \"e\""

def noEntryUb : Bool :=
  match execFn {} { name := "empty", retTy := .void, params := [], blocks := [] } [] 1 with
  | .ub m => m == "function has no entry block"
  | _ => false

#guard noEntryUb

def arityUb : Bool :=
  match execFn {} retFn [] 1 with
  | .ub m => m == "argument arity mismatch"
  | _ => false

#guard arityUb

def trapUb : Bool :=
  isUb "trap" (stepInstr {} st0 (.call none .void "llvm.trap" []))

#guard trapUb

def vecInsertExtract : Bool :=
  let vecOp := Operand.constAgg [.constInt .i8 1#8, .constInt .i8 2#8]
  match stepInstr {} st0 (.insertelement "v" 2 (.int .i8) vecOp (.constInt .i8 9#8) (.constInt .i32 1#32)) with
  | .inr st1 =>
    match st1.regs.head? with
    | some (_, v) =>
      match stepInstr {} { regs := [("v", v)] } (.extractelement "e" 2 (.int .i8) (.reg "v") (.constInt .i32 1#32)) with
      | .inr st2 => st2.regs.head?.map (·.snd) == some (i8b 9)
      | _ => false
    | _ => false
  | _ => false

#guard vecInsertExtract

def aggInsertExtract : Bool :=
  let aggOp := Operand.constAgg [.constInt .i8 1#8, .constInt .i8 2#8]
  let ty := LLVMType.struct [.int .i8, .int .i8]
  match stepInstr {} st0 (.insertvalue "a" ty aggOp (.constInt .i8 7#8) 0) with
  | .inr st1 =>
    match st1.regs.head? with
    | some (_, v) =>
      match stepInstr {} { regs := [("a", v)] } (.extractvalue "e" ty (.reg "a") 0) with
      | .inr st2 => st2.regs.head?.map (·.snd) == some (i8b 7)
      | _ => false
    | _ => false
  | _ => false

#guard aggInsertExtract

theorem retFn_returns_arg (v : LLVMVal) (fuel : Nat) (hf : 0 < fuel) :
    execFn {} retFn [v] fuel = .returned (some v) := by
  cases fuel with
  | zero => omega
  | succ k =>
    rfl

end LeanNative.Tests.LLVMAstTests
