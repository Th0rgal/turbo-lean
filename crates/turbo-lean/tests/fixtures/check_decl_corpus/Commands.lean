import Std

-- Minimized from eth-act/clifv@5018b95 FV/Backend/Proof/CSemRename.lean
-- (ispec_mapRegs), and FV/Arm/BitVec.lean (private/protected lemmas, local attributes).
namespace Corpus.Commands
set_option maxHeartbeats 4000000 in
theorem option_line (n : Nat) : n + 0 = n 
-- CORPUS-PROOF Corpus.Commands.option_line
:= by omega
-- CORPUS-END

set_option maxHeartbeats 4000000 in theorem option_inline : 2 + 2 = 4 
-- CORPUS-PROOF Corpus.Commands.option_inline
:= rfl
-- CORPUS-END

set_option maxHeartbeats 4000000 in
  theorem option_indented (n : Nat) : n = n 
-- CORPUS-PROOF Corpus.Commands.option_indented
:= rfl
-- CORPUS-END

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000 in
@[simp] theorem option_nested (n : Nat) : n + 0 = n 
-- CORPUS-PROOF Corpus.Commands.option_nested
:= rfl
-- CORPUS-END

private theorem hidden (n : Nat) : n = n 
-- CORPUS-PROOF Corpus.Commands.hidden
:= rfl
-- CORPUS-END

protected theorem visible (n : Nat) : n = n 
-- CORPUS-PROOF Corpus.Commands.visible
:= rfl
-- CORPUS-END


section Locals
  variable (n : Nat)
  @[simp] theorem add_zero : n + 0 = n 
-- CORPUS-PROOF Corpus.Commands.add_zero
:= rfl
-- CORPUS-END

  attribute [local simp] add_zero
  theorem uses_local : n + 0 = n 
-- CORPUS-PROOF Corpus.Commands.uses_local
:= by simp
-- CORPUS-END

end Locals
namespace Nested
  section
    variable {α : Type} (x : α)
    theorem identity : id x = x 
-- CORPUS-PROOF Corpus.Commands.Nested.identity
:= rfl
-- CORPUS-END

  end
end Nested
end Corpus.Commands
