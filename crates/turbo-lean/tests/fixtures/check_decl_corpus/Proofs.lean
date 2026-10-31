import Std
import Std.Tactic.BVDecide

namespace Corpus.Proofs
-- eth-act/clifv@5018b95 FV/Arm/Memory/MemoryProofs.lean: helper chains of `have`.
theorem have_chain (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c 
-- CORPUS-PROOF Corpus.Proofs.have_chain
:= by
  have h1 : a + 0 ≤ b := by omega
  have h2 : b ≤ c + 0 := by omega
  have h3 : a ≤ c := by omega
  exact h3
-- CORPUS-END

-- FV/ArmFault/Witness.lean: ldr_null_faults / ldr_mapped_ok (`decide +kernel`).
theorem kernel_witness : (7 : Nat) < 12 
-- CORPUS-PROOF Corpus.Proofs.kernel_witness
:= by decide +kernel
-- CORPUS-END

-- FV/Arm/Insts/Common.lean and FV/Arm/Memory/SeparateProofs.lean: bit-vector witnesses.
theorem bitvector_witness (x : BitVec 8) : x ^^^ x = 0 
-- CORPUS-PROOF Corpus.Proofs.bitvector_witness
:= by bv_decide
-- CORPUS-END

-- FV/Arm/Insts/Common.lean: rev_elems examples. Only admitted by fixture project policy.
theorem native_witness : (List.range 8).length = 8 
-- CORPUS-PROOF Corpus.Proofs.native_witness
:= by native_decide
-- CORPUS-END

-- FV/Arm/Memory/Separate.lean: mem_subset'_refl (structure-valued theorem `where`).
structure Bounds (a b : Nat) : Prop where
  lower : a ≤ b
  upper : b ≤ b
theorem bounds_refl (n : Nat) : Bounds n n where
  lower 
-- CORPUS-PROOF Corpus.Proofs.bounds_refl
:= by omega
  upper := by omega
-- CORPUS-END

-- Named `where` auxiliary: a minimal helper for the same structured proof style.
theorem with_aux (n : Nat) : n = n 
-- CORPUS-PROOF Corpus.Proofs.with_aux
:= helper n
where
  helper (k : Nat) : k = k := rfl
-- CORPUS-END

-- FV/Arm/Memory/Separate.lean: Decidable instance with proof branches.
instance decidableBounds (a b : Nat) : Decidable (Bounds a b) :=
  if h : a ≤ b then isTrue ⟨h, Nat.le_refl b⟩
  else isFalse (fun h' => h h'.lower)
theorem uses_instance : Bounds 2 3 
-- CORPUS-PROOF Corpus.Proofs.uses_instance
:= by decide +kernel
-- CORPUS-END

-- Anonymous examples elaborate but do not persist as user-facing env.constants theorems.
example : 3 + 4 = 7 := by decide +kernel
end Corpus.Proofs
