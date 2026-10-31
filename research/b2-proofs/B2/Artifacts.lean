import B2.BackendLower
import FV.Backend.Regalloc
import FV.Backend.Encode
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! The actual prepared, allocated, emitted and laid-out artifacts. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000
set_option Elab.async false
namespace B2.Artifacts
open Backend
def vcp : VCode := vc
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

theorem prepared : prepare vc = .ok vcp := by cbv

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
