import Std

namespace Corpus.Recursion
-- eth-act/clifv@5018b95 FV/Backend/Proof/DefGenOfV.lean: regsU/regsUL mutual
-- definitions, simp lemmas, and mem_regsUL structural recursion.
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n
  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end
@[simp] theorem even_zero : even 0 = true 
-- CORPUS-PROOF Corpus.Recursion.even_zero
:= rfl
-- CORPUS-END

@[simp] theorem odd_zero : odd 0 = false 
-- CORPUS-PROOF Corpus.Recursion.odd_zero
:= rfl
-- CORPUS-END

theorem even_step (n : Nat) : even (n + 1) = odd n 
-- CORPUS-PROOF Corpus.Recursion.even_step
:= rfl
-- CORPUS-END

-- FV/Backend/Proof/DefGenDom.lean: mutually recursive proof declarations.
mutual
  theorem even_self (n : Nat) : even n = even n 
-- CORPUS-PROOF Corpus.Recursion.even_self
:= by
    cases n with
    | zero => rfl
    | succ n => exact odd_self n
-- CORPUS-END

  theorem odd_self (n : Nat) : odd n = odd n 
-- CORPUS-PROOF Corpus.Recursion.odd_self
:= by
    cases n with
    | zero => rfl
    | succ n => exact even_self n
-- CORPUS-END

end
theorem length_copy : (xs : List Nat) → xs.length = xs.length
-- CORPUS-PROOF Corpus.Recursion.length_copy

  | [] => rfl
  | _ :: xs => by simpa using congrArg Nat.succ (length_copy xs)
-- CORPUS-END

end Corpus.Recursion
