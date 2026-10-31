import B2.CollatzClif
import B2.BackendEval
import FV.Backend.Regalloc
import FV.Backend.Encode
import FV.Backend.InputScope
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! O5 artifacts from clifv's real executable pipeline, including its checked spill allocation.
These definitions are not a model of compilation; each successful equation is kernel-checked. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace B2.Artifacts
open Backend
attribute [local irreducible] B2.Smoke.collatz

/-- Kernel-tied snapshot avoids repeatedly evaluating the LNIR lowering inside backend checks. -/
def input : Clif.Function :=
  { name := "collatz_steps"
    sig := { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩]
             returns := [⟨.i64, .none, .normal⟩] }
    blocks := [B2.CollatzClif.entryBlock, B2.CollatzClif.headerBlock,
      B2.CollatzClif.bodyBlock, B2.CollatzClif.exitBlock] }

theorem input_eq : input = B2.Smoke.collatz := by
  obtain ⟨blocks, hf, _⟩ := B2.Lowering.lower_success _ _ B2.Smoke.collatz_lowered
  have hb : blocks = [B2.CollatzClif.entryBlock, B2.CollatzClif.headerBlock,
      B2.CollatzClif.bodyBlock, B2.CollatzClif.exitBlock] := by
    simpa only [hf, LeanNative.Backend.Clif.assemble] using B2.CollatzClif.generated_blocks
  rw [hf, hb]
  rfl

#print axioms input_eq

def vc : VCode := (lowerFunction input).toOption.getD default
def vcp : VCode := (prepare vc).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

-- `cbv` produces kernel-checked equality proofs and uses Std's map lemmas;
-- direct decision reduction gets stuck on the emitter's opaque `mixHash`.
private theorem success {α : Type} [Inhabited α] (e : Except String α)
    (h : e.isOk = true) : e = .ok (e.toOption.getD default) := by
  cases e with
  | error _ => cases h
  | ok _ => rfl

theorem verifiable : Backend.verifiable B2.Smoke.collatz = true := by decide +kernel

#print axioms verifiable

theorem lower : lowerFunction B2.Smoke.collatz = .ok vc := by
  rw [← input_eq]
  exact success _ (by cbv)

#print axioms lower

theorem prepared : prepare vc = .ok vcp := success _ (by cbv)

#print axioms prepared

theorem allocation_checked : checkAlloc vcp rf = .ok () := by
  have h : (checkAlloc vcp rf).isOk = true := by cbv
  cases hc : checkAlloc vcp rf with
  | error _ => rw [hc] at h; cases h
  | ok u => cases u; rfl

#print axioms allocation_checked

theorem allocated : lowerRFunc vcp rf = .ok af := success _ (by cbv)

#print axioms allocated

theorem emitted : emitFunc 0 af = .ok fa := success _ (by cbv)

#print axioms emitted

theorem laid_out : fa.layout = .ok fb := success _ (by cbv)

#print axioms laid_out

end B2.Artifacts
