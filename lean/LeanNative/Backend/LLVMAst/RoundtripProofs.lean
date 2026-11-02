import LeanNative.Backend.LLVMAst.Syntax
import LeanNative.Backend.LLVMAst.PP

namespace LeanNative.Backend.LLVMAst

open LeanNative.Backend.TargetIR

theorem parseType_int (fuel : Nat) (w : IntWidth) (rest : List Char)
    (hsuf : PP.ValidTypeSuffix rest) :
    PP.parseType (fuel + 1) (PP.typeChars (.int w) ++ rest) = some (.int w, rest) := by
  cases w with
  | i1 => cases hsuf <;> rfl
  | i8 | i16 | i32 | i64 | i128 | i256 | i512 => rfl

theorem parseType_ptr (fuel : Nat) (as_ : AddrSpace) (rest : List Char)
    (hsuf : PP.ValidTypeSuffix rest) :
    PP.parseType (fuel + 1) (PP.typeChars (.ptr as_) ++ rest) = some (.ptr as_, rest) := by
  by_cases hz : as_ == 0
  · have ha : as_ = 0 := beq_iff_eq.mp hz
    subst ha
    cases hsuf <;> rfl
  · simp only [PP.typeChars, hz, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc, List.nil_append]
    simp only [PP.parseType]
    rw [readDigits_natDigits_delim as_ ')' rest rfl]
    rfl

theorem typeChars_head_not_brace (ty : LLVMType) (rest : List Char) :
    ∃ c cs, c ≠ '}' ∧ PP.typeChars ty ++ rest = c :: cs := by
  cases ty with
  | void => exact ⟨'v', 'o' :: 'i' :: 'd' :: rest, by decide, rfl⟩
  | int w => cases w <;> exact ⟨'i', _, by decide, rfl⟩
  | float fw =>
    cases fw with
    | f32 => exact ⟨'f', _, by decide, rfl⟩
    | f64 => exact ⟨'d', _, by decide, rfl⟩
  | ptr a =>
    by_cases ha : a == 0
    · simp only [PP.typeChars, ha, ↓reduceIte]
      exact ⟨'p', _, by decide, rfl⟩
    · simp only [PP.typeChars, ha, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc]
      exact ⟨'p', _, by decide, rfl⟩
  | structFields packed fs =>
    cases packed <;> cases fs <;> exact ⟨_, _, by decide, rfl⟩
  | array _ _ => exact ⟨'[', _, by decide, rfl⟩
  | vec _ _ => exact ⟨'<', _, by decide, rfl⟩

theorem parseType_struct_open (fuel : Nat) (c : Char) (cs : List Char) (hc : c ≠ '}')
    (h : LLVMType) (rest1 : List Char) (t : LLVMTypeFields) (rest2 : List Char)
    (hp1 : PP.parseType fuel (c :: cs) = some (h, rest1))
    (hp2 : PP.parseFieldsTail fuel rest1 = some (t, ' ' :: '}' :: rest2)) :
    PP.parseType (fuel + 1) ('{' :: ' ' :: c :: cs) = some (.structFields false (.cons h t), rest2) := by
  simp [PP.parseType, hc, hp1, hp2]

theorem parseType_packed_struct_open (fuel : Nat) (c : Char) (cs : List Char) (hc : c ≠ '}')
    (h : LLVMType) (rest1 : List Char) (t : LLVMTypeFields) (rest2 : List Char)
    (hp1 : PP.parseType fuel (c :: cs) = some (h, rest1))
    (hp2 : PP.parseFieldsTail fuel rest1 = some (t, ' ' :: '}' :: '>' :: rest2)) :
    PP.parseType (fuel + 1) ('<' :: '{' :: ' ' :: c :: cs) = some (.structFields true (.cons h t), rest2) := by
  simp [PP.parseType, hc, hp1, hp2]

theorem natDigits_head_not_brace (n : Nat) (rest : List Char) :
    ∃ c cs, c ≠ '{' ∧ TargetIR.natDigits n ++ rest = c :: cs := by
  unfold TargetIR.natDigits
  have haux : ∀ fuel m acc, 0 < fuel → ∃ c cs, (c = TargetIR.digitChar (m % 10) ∨ ∃ k < 10, c = TargetIR.digitChar k) ∧
      TargetIR.natDigitsAux fuel m acc ++ rest = c :: cs := by
    intro fuel
    induction fuel with
    | zero => intro _ _ h; omega
    | succ f ih =>
      intro m acc _
      simp only [TargetIR.natDigitsAux]
      by_cases hlt : m < 10
      · simp only [hlt, ↓reduceIte, List.cons_append]
        exact ⟨TargetIR.digitChar (m % 10), acc ++ rest, Or.inl rfl, rfl⟩
      · simp only [hlt, ↓reduceIte]
        cases f with
        | zero =>
          simp only [TargetIR.natDigitsAux, List.cons_append]
          exact ⟨TargetIR.digitChar (m % 10), acc ++ rest, Or.inl rfl, rfl⟩
        | succ f' =>
          rcases ih (m / 10) (TargetIR.digitChar (m % 10) :: acc) (by omega) with ⟨c, cs, hd, heq⟩
          refine ⟨c, cs, ?_, heq⟩
          rcases hd with rfl | ⟨k, hk, rfl⟩
          · exact Or.inr ⟨(m / 10) % 10, Nat.mod_lt _ (by decide), rfl⟩
          · exact Or.inr ⟨k, hk, rfl⟩
  rcases haux (n + 1) n [] (by omega) with ⟨c, cs, hd, heq⟩
  refine ⟨c, cs, ?_, heq⟩
  have hne : ∀ k < 10, TargetIR.digitChar k ≠ '{' := by
    intro k hk
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
    | m + 10 => omega
  rcases hd with rfl | ⟨k, hk, rfl⟩
  · exact hne (n % 10) (Nat.mod_lt n (by decide))
  · exact hne k hk

theorem parseType_vec_open (fuel : Nat) (c : Char) (cs : List Char) (hc : c ≠ '{')
    (n : Nat) (rest1 : List Char) (et : LLVMType) (rest2 : List Char)
    (hrd : TargetIR.readDigits 0 (c :: cs) = (n, ' ' :: 'x' :: ' ' :: rest1))
    (hp : PP.parseType fuel rest1 = some (et, '>' :: rest2)) :
    PP.parseType (fuel + 1) ('<' :: c :: cs) = some (.vec n et, rest2) := by
  simp [PP.parseType, hc, hrd, hp]

mutual
theorem parseType_roundtrip (fuel : Nat) (ty : LLVMType) (rest : List Char)
    (hf : PP.typeDepth ty ≤ fuel)
    (hsuf : PP.ValidTypeSuffix rest) :
    PP.parseType fuel (PP.typeChars ty ++ rest) = some (ty, rest) := by
  cases fuel with
  | zero =>
    cases ty <;> simp [PP.typeDepth] at hf
  | succ f =>
    cases ty with
    | void => rfl
    | int w => exact parseType_int f w rest hsuf
    | float fw => cases fw <;> rfl
    | ptr as_ => exact parseType_ptr f as_ rest hsuf
    | structFields packed fs =>
      cases packed with
      | false =>
        cases fs with
        | nil => rfl
        | cons h t =>
          simp only [PP.typeDepth, PP.fieldsDepth] at hf
          have hmax : Nat.max (PP.typeDepth h) (PP.fieldsDepth t) ≤ f := by omega
          have hh_le : PP.typeDepth h ≤ f := Nat.le_trans (Nat.le_max_left _ _) hmax
          have ht_le : PP.fieldsDepth t ≤ f := Nat.le_trans (Nat.le_max_right _ _) hmax
          have htsuf : PP.ValidTypeSuffix (PP.fieldsTailChars t ++ (' ' :: '}' :: rest)) := by
            cases t with
            | nil => exact .closeBrace rest
            | cons _ _ => exact .comma _
          simp only [PP.typeChars, List.cons_append, List.nil_append, List.append_assoc]
          rcases typeChars_head_not_brace h (PP.fieldsTailChars t ++ ' ' :: '}' :: rest) with ⟨c, cs, hc, heq⟩
          have hp1 : PP.parseType f (c :: cs) = some (h, PP.fieldsTailChars t ++ ' ' :: '}' :: rest) := by
            rw [← heq]
            exact parseType_roundtrip f h (PP.fieldsTailChars t ++ ' ' :: '}' :: rest) hh_le htsuf
          have hp2 : PP.parseFieldsTail f (PP.fieldsTailChars t ++ ' ' :: '}' :: rest) =
              some (t, ' ' :: '}' :: rest) :=
            parseFieldsTail_roundtrip f t (' ' :: '}' :: rest) ht_le (.closeBrace rest)
          rw [heq]
          exact parseType_struct_open f c cs hc h _ t rest hp1 hp2
      | true =>
        cases fs with
        | nil => rfl
        | cons h t =>
          simp only [PP.typeDepth, PP.fieldsDepth] at hf
          have hmax : Nat.max (PP.typeDepth h) (PP.fieldsDepth t) ≤ f := by omega
          have hh_le : PP.typeDepth h ≤ f := Nat.le_trans (Nat.le_max_left _ _) hmax
          have ht_le : PP.fieldsDepth t ≤ f := Nat.le_trans (Nat.le_max_right _ _) hmax
          have htsuf : PP.ValidTypeSuffix (PP.fieldsTailChars t ++ (' ' :: '}' :: '>' :: rest)) := by
            cases t with
            | nil => exact .closeBrace ('>' :: rest)
            | cons _ _ => exact .comma _
          simp only [PP.typeChars, List.cons_append, List.nil_append, List.append_assoc]
          rcases typeChars_head_not_brace h (PP.fieldsTailChars t ++ ' ' :: '}' :: '>' :: rest) with ⟨c, cs, hc, heq⟩
          have hp1 : PP.parseType f (c :: cs) = some (h, PP.fieldsTailChars t ++ ' ' :: '}' :: '>' :: rest) := by
            rw [← heq]
            exact parseType_roundtrip f h (PP.fieldsTailChars t ++ ' ' :: '}' :: '>' :: rest) hh_le htsuf
          have hp2 : PP.parseFieldsTail f (PP.fieldsTailChars t ++ ' ' :: '}' :: '>' :: rest) =
              some (t, ' ' :: '}' :: '>' :: rest) :=
            parseFieldsTail_roundtrip f t (' ' :: '}' :: '>' :: rest) ht_le (.closeBrace ('>' :: rest))
          rw [heq]
          exact parseType_packed_struct_open f c cs hc h _ t rest hp1 hp2
    | array n et =>
      simp only [PP.typeDepth] at hf
      simp only [PP.typeChars, List.cons_append, List.append_assoc, List.nil_append, PP.parseType]
      rw [readDigits_natDigits_delim n ' ' ('x' :: ' ' :: (PP.typeChars et ++ ']' :: rest)) rfl]
      simp only
      rw [parseType_roundtrip f et (']' :: rest) (by omega) (.closeBracket rest)]
      rfl
    | vec n et =>
      simp only [PP.typeDepth] at hf
      simp only [PP.typeChars, List.cons_append, List.append_assoc, List.nil_append]
      rcases natDigits_head_not_brace n (' ' :: 'x' :: ' ' :: (PP.typeChars et ++ '>' :: rest)) with ⟨c, cs, hc, heq⟩
      have hrd : TargetIR.readDigits 0 (c :: cs) = (n, ' ' :: 'x' :: ' ' :: (PP.typeChars et ++ '>' :: rest)) := by
        rw [← heq]
        exact readDigits_natDigits_delim n ' ' ('x' :: ' ' :: (PP.typeChars et ++ '>' :: rest)) rfl
      have hp : PP.parseType f (PP.typeChars et ++ '>' :: rest) = some (et, '>' :: rest) :=
        parseType_roundtrip f et ('>' :: rest) (by omega) (.closeAngle rest)
      rw [heq]
      exact parseType_vec_open f c cs hc n _ et rest hrd hp

theorem parseFieldsTail_roundtrip (fuel : Nat) (fs : LLVMTypeFields) (rest : List Char)
    (hf : PP.fieldsDepth fs ≤ fuel)
    (hsuf : PP.ValidTailSuffix rest) :
    PP.parseFieldsTail fuel (PP.fieldsTailChars fs ++ rest) = some (fs, rest) := by
  cases fuel with
  | zero =>
    cases fs <;> simp [PP.fieldsDepth] at hf
  | succ f =>
    cases fs with
    | nil =>
      cases hsuf with
      | closeBrace cs => rfl
    | cons h t =>
      simp only [PP.fieldsDepth] at hf
      have hmax : Nat.max (PP.typeDepth h) (PP.fieldsDepth t) ≤ f := by omega
      have hh_le : PP.typeDepth h ≤ f := Nat.le_trans (Nat.le_max_left _ _) hmax
      have ht_le : PP.fieldsDepth t ≤ f := Nat.le_trans (Nat.le_max_right _ _) hmax
      have htsuf : PP.ValidTypeSuffix (PP.fieldsTailChars t ++ rest) := by
        cases t with
        | nil =>
          cases hsuf with
          | closeBrace cs => exact .closeBrace cs
        | cons _ _ => exact .comma _
      simp only [PP.fieldsTailChars, List.cons_append, List.nil_append, List.append_assoc, PP.parseFieldsTail]
      rw [parseType_roundtrip f h (PP.fieldsTailChars t ++ rest) hh_le htsuf]
      simp only
      rw [parseFieldsTail_roundtrip f t rest ht_le hsuf]
end

theorem ppType_injective (t1 t2 : LLVMType) (h : PP.ppType t1 = PP.ppType t2) : t1 = t2 := by
  have hchars : PP.typeChars t1 = PP.typeChars t2 := by
    have hto := congrArg String.toList h
    simpa [PP.ppType] using hto
  let fuel := Nat.max (PP.typeDepth t1) (PP.typeDepth t2)
  have h1 := parseType_roundtrip fuel t1 [] (Nat.le_max_left _ _) .nil
  have h2 := parseType_roundtrip fuel t2 [] (Nat.le_max_right _ _) .nil
  simp only [List.append_nil] at h1 h2
  rw [hchars] at h1
  rw [h1] at h2
  injection h2 with hpair
  exact (Prod.mk.inj hpair).1

theorem ppInstr_nonempty (ins : LLVMInstr) : PP.ppInstr ins ≠ "" := by
  cases ins <;> simp [PP.ppInstr, PP.ppFlags, PP.ppExact, PP.ppVolatile, PP.ppICmp, PP.ppFCmp,
    PP.ppRMW, PP.ppOrdering, PP.ppAlign, PP.ppGEP, PP.ppPtr, PP.ppCC, PP.ppTypedOperand, PP.ppType]

end LeanNative.Backend.LLVMAst
