import B2.BackendAlloc
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
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

theorem allocated : lowerRFunc vcp rf = .ok af := by cbv

#print axioms allocated

theorem emitted : emitFunc 0 af = .ok fa := by cbv

#print axioms emitted

theorem laid_out : fa.layout = .ok fb := by cbv

#print axioms laid_out

end B2.Artifacts
