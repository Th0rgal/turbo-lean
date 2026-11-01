import LeanNative.Backend.Clif

namespace B2.Lowering
open LeanNative.IR LeanNative.Backend.Clif

/-- Successful lowering has exactly the assembled function, with an accepted subset check. -/
theorem lower_success (d : LNIRDecl) (f : Clif.Function)
    (h : lowerDecl d = .ok f) :
    ∃ blocks, f = assemble d blocks ∧ Compile.functionE f = true := by
  change (Except.bind (buildDecl d) (fun blocks =>
    if Compile.functionE (assemble d blocks) then .ok (assemble d blocks)
    else .error "CLIF: generated function rejected by subset E")) = .ok f at h
  cases hb : buildDecl d with
  | error e => simp [hb, Except.bind] at h
  | ok blocks =>
    simp only [hb, Except.bind] at h
    split at h
    next he => cases h; exact ⟨blocks, rfl, he⟩
    next => cases h

/-- O1: every successful executable lowering is in the actual clifv emitter subset. -/
theorem lower_in_subsetE (d : LNIRDecl) (f : Clif.Function)
    (h : lowerDecl d = .ok f) : Compile.functionE f = true :=
  (lower_success d f h).choose_spec.2

/-- O2: the generated signature, independently of a fragment-membership premise. -/
theorem lower_sig (d : LNIRDecl) (f : Clif.Function) (h : lowerDecl d = .ok f) :
    f.sig.params.map (·.ty) = d.params.map (clifTy ·.ty) ∧
    f.sig.returns.map (·.ty) = [clifTy d.retTy] := by
  obtain ⟨_, rfl, _⟩ := lower_success d f h
  simp [assemble, List.map_map, Function.comp_def]

/-- Structural part of O6: the compiler cannot introduce external declarations. -/
theorem lower_declarations (d : LNIRDecl) (f : Clif.Function) (h : lowerDecl d = .ok f) :
    f.externs = [] ∧ f.sigDecls = [] ∧ f.globals = [] ∧ f.slots = [] := by
  obtain ⟨_, rfl, _⟩ := lower_success d f h
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms lower_in_subsetE
#print axioms lower_sig
#print axioms lower_declarations
end B2.Lowering
