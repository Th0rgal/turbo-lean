import FV.Clif.Run
import FV.Compile.Subset
import LeanNative.Semantics.Eval

/-!
# DRAFT — B2 specification, LNIR → CLIF half (statements only)

**DRAFT / CONJECTURE stage.** Every `theorem` here ends in `:= by sorry`. Nothing in this file is
a result. It records the *shape* of the B2 obligations against the *real* semantics:
LNIR = `LeanNative.Semantics.evalCode` (turbo-lean 4966384, vendored verbatim),
CLIF = `Clif.runLoop` (eth-act/clifv 5018b950). No semantics are defined here.

The lowering `lowerDecl` does not exist yet (there is no CLIF emitter in turbo-lean); it is a
section `variable`, so every statement is about whatever lowering is eventually written.
-/

namespace B2

open LeanNative.IR LeanNative.Semantics

/-! ## Fragment F₆₄ (syntactic, decidable) -/

/-- Binary operators admitted in F₆₄. `div`/`mod` are admitted only under `DivGuarded`
(LNIR returns 0 on `x/0` and `x%0`; CLIF `udiv`/`urem` trap `int_divz`). The `*Checked256`,
`clmul*`, `gf2Affine`, `eor3` operators are out of scope. -/
def binOpF : BinOp → Bool
  | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
  | .shl | .shr | .sar | .eq | .lt | .le => true
  | _ => false

def unOpF : UnaryOp → Bool
  | .not | .neg => true
  | .clz256 => false

def scalarF : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => true
  | .binOp op a b => binOpF op && scalarF a && scalarF b
  | .unaryOp op a => unOpF op && scalarF a
  | .select c t e => scalarF c && scalarF t && scalarF e
  | .fma a b c => scalarF a && scalarF b && scalarF c

def tyF : LNIRType → Bool
  | .i1 | .i64 => true
  | _ => false

/-- F₆₄ code: `letBind` of scalar expressions at `i1`/`i64`, `ite`, `seqFor`, `ret`. No heap,
no RC, no `parFor`, no calls, no 256-bit. -/
def codeF : LNIRCode → Bool
  | .letBind _ ty (.scalar e) k => tyF ty && scalarF e && codeF k
  | .ite _ t e => codeF t && codeF e
  | .seqFor _ _ _ _ _ ty body k => tyF ty && codeF body && codeF k
  | .ret _ => true
  | _ => false

def declF (d : LNIRDecl) : Bool :=
  d.params.all (fun p => tyF p.ty) && tyF d.retTy && codeF d.body

/-! ## Value correspondence (no new semantics: both sides are the repos' own `Val`s) -/

/-- LNIR `u64` ↔ CLIF `i64`, LNIR `bool` ↔ CLIF `i8` 0/1 (CLIF `icmp` result). -/
def ValRel : Val → Clif.Val → Prop
  | .u64 n, v => v = ⟨.i64, n.toBitVec⟩
  | .bool b, v => v = ⟨.i8, if b then 1#8 else 0#8⟩
  | _, _ => False

/-- Pointwise `ValRel` on argument lists (core has no `List.Forall₂`). -/
def ArgsRel (vs : List Val) (cvs : List Clif.Val) : Prop :=
  vs.length = cvs.length ∧ ∀ (i : Nat) v cv, vs[i]? = some v → cvs[i]? = some cv → ValRel v cv

def clifTy : LNIRType → Clif.Ty
  | .i1 => .i8
  | _ => .i64

/-- The LNIR entry state of `d` on argument values `vs`. -/
def entryEnv (d : LNIRDecl) (vs : List Val) : VarEnv :=
  (d.params.zip vs).foldl (fun env (p, v) => env.bind p.id v) VarEnv.empty

/-- Empty LNIR heap (F₆₄ never touches it). -/
def emptyHeap : HeapState := ⟨[], 0, [], []⟩

/-! ## Obligations on the (future) lowering -/

section
-- The B2 front end to be written: LNIR declaration → CLIF function.
variable (lowerDecl : LNIRDecl → Except String Clif.Function)

/-- (O1) Scope: every F₆₄ function lands in clifv's verified emitter subset E and the
decidable side conditions of `E2E.backend_correct_final_of_lower`. Statement kept in
`B2/SpecE2E.lean` (needs `FV.E2E.*`); here only subset E. -/
theorem lower_in_subsetE (d : LNIRDecl) (f : Clif.Function)
    (hd : declF d = true) (hl : lowerDecl d = .ok f) :
    Compile.functionE f = true := by
  sorry

/-- (O2) Signature: one `i64`/`i8` parameter per LNIR parameter, one return. -/
theorem lower_sig (d : LNIRDecl) (f : Clif.Function)
    (hd : declF d = true) (hl : lowerDecl d = .ok f) :
    f.sig.params.map (·.ty) = d.params.map (clifTy ·.ty) ∧
    f.sig.returns.map (·.ty) = [clifTy d.retTy] := by
  sorry

/-- (O3) **Forward simulation, LNIR → CLIF** (the B2 core lemma). If LNIR evaluates `d` to a
value, the CLIF function returns a related value. `DivGuarded` is the explicit side condition
for the div/mod-by-zero mismatch: the run never divides by zero (otherwise CLIF traps
`int_divz` where LNIR returns 0; the alternative is to lower `div` to
`select(y==0, 0, udiv x y')` — then this hypothesis disappears, see feasibility §Q4). -/
theorem lower_forward (DivGuarded : LNIRDecl → List Val → Prop)
    (d : LNIRDecl) (f : Clif.Function) (hd : declF d = true) (hl : lowerDecl d = .ok f)
    (vs : List Val) (cvs : List Clif.Val) (hargs : ArgsRel vs cvs)
    (hdiv : DivGuarded d vs)
    (fuel : Nat) (v : Val) (st : HeapState)
    (hev : evalCode fuel (entryEnv d vs) emptyHeap d.body = .ok (v, st))
    (env : Clif.Env) (p : Clif.Program) (hp : p.func? f.name = some f)
    (m0 : Clif.Mem) (cs : Clif.State)
    (hinit : Clif.initState p f.name cvs m0 = .ok cs) :
    ∃ n rv m, Clif.runLoop env p n cs = .returned [rv] m ∧ ValRel v rv := by
  sorry

/-- (O4) No spurious traps: on F₆₄ (with `DivGuarded`) the CLIF run of the lowered function
never traps and never gets stuck. Needed because `ArmRefines` says nothing on `stuck`. -/
theorem lower_no_trap (DivGuarded : LNIRDecl → List Val → Prop)
    (d : LNIRDecl) (f : Clif.Function) (hd : declF d = true) (hl : lowerDecl d = .ok f)
    (vs : List Val) (cvs : List Clif.Val) (hargs : ArgsRel vs cvs)
    (hdiv : DivGuarded d vs)
    (env : Clif.Env) (p : Clif.Program) (hp : p.func? f.name = some f)
    (m0 : Clif.Mem) (cs : Clif.State) (hinit : Clif.initState p f.name cvs m0 = .ok cs)
    (n : Nat) :
    (∀ c, Clif.runLoop env p n cs ≠ .trapped c) ∧
    (∀ msg, Clif.runLoop env p n cs ≠ .stuck msg) := by
  sorry

end

end B2
