import LeanNative.IR.AST
import FV.Compile.Subset

/-! Executable F64 lowering to clifv's actual CLIF AST. No source semantics are redefined. -/
namespace LeanNative.Backend.Clif

open IR

def clifTy : LNIRType → Clif.Ty
  | .i1 => .i8
  | _ => .i64

def checkTy (ty : LNIRType) : Except String Clif.Ty :=
  match ty with
  | .i1 => .ok .i8
  | .i64 => .ok .i64
  | _ => .error "CLIF: expected F64 scalar type"

abbrev Reg := Nat × Clif.Ty
abbrev Env := List (VarId × Reg)

structure Build where
  nextVal : Nat
  nextBlock : Nat := 1
  current : Clif.Block := { id := 0, term := .ret [] }
  blocks : List Clif.Block := []

abbrev M := StateT Build (Except String)

def fail {α : Type} (msg : String) : M α := throw msg

def fresh (ty : Clif.Ty) : M Reg := do
  let s ← get
  set { s with nextVal := s.nextVal + 1 }
  return (s.nextVal, ty)

def freshBlock : M Nat := do
  let s ← get
  set { s with nextBlock := s.nextBlock + 1 }
  return s.nextBlock

def emit (ty : Clif.Ty) (inst : Clif.Inst) : M Reg := do
  let r ← fresh ty
  modify fun s => { s with current.body := s.current.body ++ [⟨[r.1], inst⟩] }
  return r

def finish (term : Clif.Terminator) : M Unit :=
  modify fun s => { s with blocks := s.blocks ++ [{ s.current with term := term }] }

def beginBlock (id : Nat) (params : List Reg := []) : M Unit :=
  modify fun s => { s with current := { id := id, params := params, term := .ret [] } }

def lookup (env : Env) (id : VarId) : M Reg :=
  match env.lookup id with
  | some r => pure r
  | none => fail s!"CLIF: unbound LNIR variable {id}"

def expect (r : Reg) (ty : Clif.Ty) : M Unit :=
  if r.2 = ty then pure () else fail "CLIF: scalar type mismatch"

def const64 (n : UInt64) : M Reg := emit .i64 (.iconst .i64 n.toBitVec)

def binary (op : Clif.BinaryOp) (a b : Reg) : M Reg := do
  expect a .i64
  expect b .i64
  emit .i64 (.binary op .i64 a.1 b.1)

def cmp (cc : Clif.IntCC) (a b : Reg) : M Reg := do
  expect b a.2
  emit .i8 (.icmp cc a.2 a.1 b.1)

def select (c a b : Reg) : M Reg := do
  expect b a.2
  emit a.2 (.select a.2 c.1 a.1 b.1)

/-- The denominator is made nonzero before the eagerly evaluated division. -/
def totalDiv (rem : Bool) (a b : Reg) : M Reg := do
  expect a .i64
  expect b .i64
  let zero ← const64 0
  let one ← const64 1
  let z ← cmp .eq b zero
  let safe ← select z one b
  let q ← emit .i64 (.div (if rem then .urem else .udiv) .i64 a.1 safe.1)
  select z (if rem then a else zero) q

def lowerExpr (env : Env) : ScalarExpr → M Reg
  | .constU64 n => const64 n
  | .constBool b => emit .i8 (.iconst .i8 (if b then 1#8 else 0#8))
  | .var id => lookup env id
  | .binOp op lhs rhs => do
    let a ← lowerExpr env lhs
    let b ← lowerExpr env rhs
    match op with
    | .add => binary .iadd a b
    | .sub => binary .isub a b
    | .mul => binary .imul a b
    | .bitAnd => binary .band a b
    | .bitOr => binary .bor a b
    | .bitXor => binary .bxor a b
    | .shl => binary .ishl a b
    | .shr => binary .ushr a b
    | .sar => binary .sshr a b
    | .eq => cmp .eq a b
    | .lt => expect a .i64 *> expect b .i64 *> cmp .ult a b
    | .le => expect a .i64 *> expect b .i64 *> cmp .ule a b
    | .div =>
      if rhs == .constU64 2 then do
        let one ← const64 1
        binary .ushr a one
      else totalDiv false a b
    | .mod => totalDiv true a b
    | _ => fail "CLIF: binary operation outside F64"
  | .unaryOp op arg => do
    let a ← lowerExpr env arg
    match op with
    | .not =>
      if a.2 = .i8 then do
        let one ← emit .i8 (.iconst .i8 1#8)
        emit .i8 (.binary .bxor .i8 a.1 one.1)
      else emit .i64 (.unary .bnot .i64 a.1)
    | .neg => expect a .i64 *> emit .i64 (.unary .ineg .i64 a.1)
    | _ => fail "CLIF: unary operation outside F64"
  | .select cond yes no => do
    let c ← lowerExpr env cond
    let a ← lowerExpr env yes
    let b ← lowerExpr env no
    select c a b
  | .fma x y z => do
    let a ← lowerExpr env x
    let b ← lowerExpr env y
    let c ← lowerExpr env z
    let ab ← binary .imul a b
    binary .iadd ab c

/-- A loop-body return is a backedge; function returns leave the function. -/
inductive ReturnTo where
  | function (ty : Clif.Ty)
  | loop (header : Nat) (index : Reg) (ty : Clif.Ty)

def returnValue (dest : ReturnTo) (r : Reg) : M Unit := do
  match dest with
  | .function ty => expect r ty *> finish (.ret [r.1])
  | .loop header index ty =>
    expect r ty
    let one ← const64 1
    let next ← binary .iadd index one
    finish (.jump ⟨header, [next.1, r.1]⟩)

def lowerCode (env : Env) (dest : ReturnTo) : LNIRCode → M Unit
  | .letBind id ty (.scalar e) k => do
    let t ← ofExcept (checkTy ty)
    let r ← lowerExpr env e
    expect r t
    lowerCode ((id, r) :: env) dest k
  | .ite cond yes no => do
    let c ← lookup env cond
    let bt ← freshBlock
    let bf ← freshBlock
    finish (.brif c.1 ⟨bt, []⟩ ⟨bf, []⟩)
    beginBlock bt
    lowerCode env dest yes
    beginBlock bf
    lowerCode env dest no
  | .seqFor idx lo hi acc initial ty body k => do
    let t ← ofExcept (checkTy ty)
    let l ← lookup env lo
    let h ← lookup env hi
    let a ← lookup env initial
    expect l .i64
    expect h .i64
    expect a t
    let header ← freshBlock
    let step ← freshBlock
    let exit ← freshBlock
    let i ← fresh .i64
    let v ← fresh t
    finish (.jump ⟨header, [l.1, a.1]⟩)
    beginBlock header [i, v]
    let test ← cmp .ult i h
    finish (.brif test.1 ⟨step, []⟩ ⟨exit, []⟩)
    beginBlock step
    lowerCode ((acc, v) :: (idx, i) :: env) (.loop header i t) body
    beginBlock exit
    lowerCode ((acc, v) :: env) dest k
  | .ret id => lookup env id >>= returnValue dest
  | _ => fail "CLIF: code outside F64"

def buildDecl (d : LNIRDecl) : Except String (List Clif.Block) := do
  let ret ← checkTy d.retTy
  let params ← d.params.mapM fun p => checkTy p.ty
  let regs := (List.range params.length).zip params
  let env := (d.params.zip regs).foldl (fun e (p, r) => (p.id, r) :: e) []
  let (_, s) ← (lowerCode env (.function ret) d.body).run
    { nextVal := params.length, current := { id := 0, params := regs, term := .ret [] } }
  return s.blocks

def assemble (d : LNIRDecl) (blocks : List Clif.Block) : Clif.Function :=
  { name := d.name
    sig := { params := d.params.map fun p => { ty := clifTy p.ty }
             returns := [{ ty := clifTy d.retTy }] }
    blocks := blocks }

/-- Fail closed on unsupported/ill-typed LNIR and on the actual emitter subset check. -/
def lowerDecl (d : LNIRDecl) : Except String Clif.Function := do
  let blocks ← buildDecl d
  let f := assemble d blocks
  if Compile.functionE f then return f
  else throw "CLIF: generated function rejected by subset E"

end LeanNative.Backend.Clif
