import B2.Core
import FV.Clif.Run
import FV.Compile.Subset

/-! Historical DRAFT statements only. Superseded by research/B2-spec.md and
B2.Lowering; excluded from the active proof package root. -/

namespace B2

open LeanNative.IR LeanNative.Semantics

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
