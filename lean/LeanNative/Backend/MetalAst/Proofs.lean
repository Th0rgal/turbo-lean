import LeanNative.Backend.MetalAst.Eval

/-!
# Metal MSL 3.0 Kernel-Checked Theorems (`LeanNative.Backend.MetalAst.Proofs`)

Kernel-checked theorems over `LeanNative.Backend.MetalAst`:
- `constant` and `device const` write rejection and multi-step `constantBuffers` immutability
- `device` / `threadgroup` / `thread` address-space isolation
- Out-of-bounds `device` and `thread` stack-array load/write trapping
- Division-by-zero, signed 32-bit overflow, shift-out-of-range, and float `%` traps
- Short-circuit C++ `?:`, `&&`, and `||` vs eager `metal::select`
- Integer rank promotion (`promoteMSLArithType`) and signed arithmetic right shift (`>>`)
- Multi-lane vector (`uint2`, `ulong2`, `uint4`) and struct (`ln_u256`) load/store roundtrip
- Epoch data-race detection: disjoint safety, non-atomic overlap race, atomic-atomic compatibility,
  and atomic-vs-non-atomic race detection
- Single-pass `stepSimdgroup` evaluation (evaluating `srcExpr` once per active lane)
- Lockstep `threadgroup_barrier` convergence vs divergence
- Monotone fuel stability (`runGroup_mono_fuel`) and fuel-independent determinism
- Pretty-printer structural well-formedness (`ppMSLModule`, `ppMSLKernel`, `ppMSLType`, `ppMSLStmt`)
-/

namespace LeanNative.Backend.MetalAst

theorem parseMSLScalarType_roundtrip (ty : MSLType) (h : CanonicalMSLValueType ty) :
    parseMSLScalarType (ppMSLType ty) = some ty := by
  cases ty <;> simp_all [CanonicalMSLValueType, ppMSLType, parseMSLScalarType]

set_option maxHeartbeats 1600000 in
theorem parseMSLParamType_roundtrip (ty : MSLType) (h : CanonicalMSLType ty) :
    parseMSLParamType (ppMSLType ty) = some ty := by
  cases ty with
  | pointer sp c el =>
    cases el <;> simp only [CanonicalMSLType, CanonicalMSLValueType, false_and] at h
    all_goals try contradiction
    all_goals cases sp <;> cases c <;> first | exact False.elim (Bool.noConfusion (h.2 rfl)) | decide
  | ref sp el =>
    cases el <;> simp only [CanonicalMSLType, CanonicalMSLValueType] at h
    all_goals try contradiction
    all_goals cases sp <;> decide
  | _ => first | contradiction | decide

theorem ppMSLType_injective_on_canonical (a b : MSLType)
    (ha : CanonicalMSLType a) (hb : CanonicalMSLType b)
    (h : ppMSLType a = ppMSLType b) : a = b := by
  have hp := congrArg parseMSLParamType h
  simpa only [parseMSLParamType_roundtrip a ha, parseMSLParamType_roundtrip b hb,
    Option.some.injEq] using hp

theorem scanMSLToken_append (delimiter : Char) (token rest : List Char)
    (h : delimiter ∉ token) :
    scanMSLToken delimiter (token ++ delimiter :: rest) = (token, delimiter :: rest) := by
  induction token with
  | nil => simp [scanMSLToken]
  | cons c cs ih =>
    have hc : c ≠ delimiter := fun he => h (by simp [he])
    have hs : delimiter ∉ cs := fun hm => h (by simp [hm])
    simp [scanMSLToken, hc, ih hs]

theorem canonicalMSLType_no_closeParen (ty : MSLType) (h : CanonicalMSLType ty) :
    ')' ∉ (ppMSLType ty).toList := by
  cases ty with
  | pointer sp c el =>
    cases el <;> simp only [CanonicalMSLType, CanonicalMSLValueType, false_and] at h
    all_goals try contradiction
    all_goals cases sp <;> cases c
    all_goals first | exact False.elim (Bool.noConfusion (h.2 rfl)) | decide
  | ref sp el =>
    cases el <;> simp only [CanonicalMSLType, CanonicalMSLValueType] at h
    all_goals try contradiction
    all_goals cases sp <;> decide
  | _ => first | contradiction | decide

theorem parseMSLType_roundtrip (ty : MSLType) (h : CanonicalMSLType ty)
    (rest : List Char) :
    parseMSLType ((ppMSLType ty).toList ++ ')' :: rest) = some (ty, ')' :: rest) := by
  simp [parseMSLType, scanMSLToken_append ')' _ rest (canonicalMSLType_no_closeParen ty h),
    parseMSLParamType_roundtrip ty h]

theorem stripPrefixChars_append (pre rest : List Char) :
    stripPrefixChars pre (pre ++ rest) = some rest := by
  induction pre <;> simp_all [stripPrefixChars]

theorem scanMSLName_append (name rest : List Char) (fuel : Nat)
    (hn : ∀ c ∈ name, mslNameChar c = true)
    (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ mslNameChar c = false)
    (hf : name.length < fuel) : scanMSLName fuel (name ++ rest) = some (name, rest) := by
  induction name generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      rcases hr with rfl | ⟨c, cs, rfl, hc⟩ <;> simp_all [scanMSLName]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [List.cons_append, scanMSLName, hn c (by simp), ↓reduceIte]
      rw [ih f (by intro x hx; exact hn x (by simp [hx])) (by simpa using hf)]
      rfl

theorem parseMSLExpr_bool_roundtrip (b : Bool) (rest : List Char) :
    parseMSLExpr 8 ((ppMSLExpr (.immBool b)).toList ++ ')' :: rest) =
      some (.immBool b, ')' :: rest) := by
  cases b <;> simp [parseMSLExpr, ppMSLExpr, scanMSLName, mslNameChar]

theorem validMSLExprSuffix_nameBoundary (rest : List Char) (h : ValidMSLExprSuffix rest) :
    rest = [] ∨ ∃ c cs, rest = c :: cs ∧ mslNameChar c = false := by
  cases rest with
  | nil => exact Or.inl rfl
  | cons c cs =>
    right
    refine ⟨c, cs, rfl, ?_⟩
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem stripPrefixChars_eq_some_iff (pre input rest : List Char) :
    stripPrefixChars pre input = some rest ↔ input = pre ++ rest := by
  induction pre generalizing input with
  | nil => simp [stripPrefixChars]
  | cons p ps ih =>
    cases input with
    | nil => simp [stripPrefixChars]
    | cons c cs =>
      by_cases h : p = c
      · simp_all [stripPrefixChars]
      · simp_all [stripPrefixChars, Ne.symm h]

theorem parseMSLExpr_var_roundtrip (name : String) (h : CanonicalMSLName name)
    (rest : List Char) (hr : ValidMSLExprSuffix rest) (fuel : Nat)
    (hf : name.toList.length < fuel) :
    parseMSLExpr (fuel + 1) (name.toList ++ rest) = some (.var name, rest) := by
  have hs := scanMSLName_append name.toList rest fuel h.2.1
    (validMSLExprSuffix_nameBoundary rest hr) hf
  rcases h with ⟨⟨c, cs, hn, hc⟩, hall, ht, hfalse, hul, hclz⟩
  have hc' : c ≠ '(' := by intro he; subst c; contradiction
  have hne : name.toList.isEmpty = false := by simp [hn]
  have hname : String.singleton c ++ String.ofList cs = name := by
    simpa using congrArg String.ofList hn.symm
  rw [hn] at hs
  simp only [List.cons_append] at hs
  have hul' : ¬ ['L', 'U'] <+: cs.reverse ++ [c] := by
    have hh := hul
    rw [hn] at hh
    intro hp
    have hp' := List.isPrefixOf_iff_prefix.mpr hp
    simp only [List.reverse_cons] at hh
    rw [hh] at hp'
    contradiction
  simp only [hn, List.cons_append]
  cases rest with
  | nil =>
    simp only [List.append_nil] at hs ⊢
    simp [parseMSLExpr, hc', hs, hname, ht, hfalse, hul']
  | cons d ds =>
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [parseMSLExpr, hc', hs, hname, ht, hfalse, hul']


theorem parseMSLStmt_return_roundtrip (indent : String) (rest : List Char) :
    parseMSLStmt 2 indent ((ppMSLStmt indent .returnStmt).toList ++ rest) =
      some (.returnStmt, rest) := by
  simp only [ppMSLStmt, String.toList_append, List.append_assoc]
  simp [parseMSLStmt, stripPrefixChars_append, parseMSLSimpleStmt,
    stripPrefixChars, String.reduceToList]

theorem parseMSLExpr_bool_suffix_roundtrip (b : Bool) (rest : List Char)
    (hr : ValidMSLExprSuffix rest) (fuel : Nat) (hf : 6 < fuel) :
    parseMSLExpr fuel ((ppMSLExpr (.immBool b)).toList ++ rest) =
      some (.immBool b, rest) := by
  cases fuel with
  | zero => omega
  | succ f =>
    have hs (chars : List Char) (hc : ∀ c ∈ chars, mslNameChar c = true)
        (hlen : chars.length < f) :=
      scanMSLName_append chars rest f hc (validMSLExprSuffix_nameBoundary rest hr) hlen
    cases b <;>
      simp only [ppMSLExpr, Bool.false_eq_true, ↓reduceIte, String.reduceToList]
    · have hscan := hs ['f', 'a', 'l', 's', 'e'] (by decide) (by simp; omega)
      simp only [parseMSLExpr, hscan]
      rfl

    · have hscan := hs ['t', 'r', 'u', 'e'] (by decide) (by simp; omega)
      simp only [parseMSLExpr, hscan]
      rfl

theorem mslNameChar_of_isDigit (c : Char) (h : c.isDigit = true) : mslNameChar c = true := by
  simp [mslNameChar, Char.isAlphanum, h]

theorem natRepr_mslNameChars (n : Nat) :
    ∀ c ∈ n.repr.toList, mslNameChar c = true := by
  intro c hc
  apply mslNameChar_of_isDigit
  rw [Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc

set_option maxHeartbeats 800000 in
theorem parseMSLExpr_u64_roundtrip (v : BitVec 64) (rest : List Char)
    (hr : ValidMSLExprSuffix rest) (fuel : Nat)
    (hf : v.toNat.repr.toList.length + 2 < fuel) :
    parseMSLExpr (fuel + 1) ((ppMSLExpr (.immU64 v)).toList ++ rest) =
      some (.immU64 v, rest) := by
  generalize hdigits : v.toNat.repr.toList = digits at hf
  have hd : ∀ c ∈ digits, c.isDigit = true := by
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (b := 10) (n := v.toNat) (by omega) (by omega)
      (by simpa only [← hdigits, Nat.toList_repr] using hc)
  have hn : digits ≠ [] := by rw [← hdigits]; simp
  have hs := scanMSLName_append (digits ++ ['U', 'L']) rest fuel
    (by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact mslNameChar_of_isDigit c (hd c hc)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> decide)
    (validMSLExprSuffix_nameBoundary rest hr) (by simpa using hf)
  have ht : String.ofList (digits ++ ['U', 'L']) ≠ "true" := by
    intro he
    have hh := congrArg String.toList he
    cases heq : digits with
    | nil => exact hn heq
    | cons c cs =>
      have hc := hd c (by simp [heq])
      simp only [String.toList_ofList, heq, List.cons_append, String.reduceToList,
        List.cons.injEq] at hh
      rcases hh with ⟨rfl, _⟩
      contradiction
  have hfalse : String.ofList (digits ++ ['U', 'L']) ≠ "false" := by
    intro he
    have hh := congrArg String.toList he
    cases heq : digits with
    | nil => exact hn heq
    | cons c cs =>
      have hc := hd c (by simp [heq])
      simp only [String.toList_ofList, heq, List.cons_append, String.reduceToList,
        List.cons.injEq] at hh
      rcases hh with ⟨rfl, _⟩
      contradiction
  have hnum : (String.ofList digits).toNat? = some v.toNat := by
    simpa only [← hdigits, String.ofList_toList] using Nat.toNat?_repr v.toNat
  have hv : v.toNat < 2^64 := v.isLt
  simp only [ppMSLExpr, String.toList_append, Nat.toString_eq_repr]
  rw [hdigits]
  change parseMSLExpr (fuel + 1) ((digits ++ ['U', 'L']) ++ rest) = _
  cases he : digits with
  | nil => exact False.elim (hn he)
  | cons c cs =>
    have hc := hd c (by simp [he])
    have hc' : c ≠ '(' := by intro hh; subst c; contradiction
    have hs' := hs
    simp only [he, List.cons_append] at hs'
    simp only [List.cons_append]
    simp only [parseMSLExpr]
    split
    all_goals try contradiction
    all_goals try { rename_i hh; simp [hc'] at hh }
    simp only [hs']
    have he' : c :: (cs ++ ['U', 'L']) = digits ++ ['U', 'L'] := by rw [he]; rfl
    rw [he']
    simp only [String.ofList_append] at ht hfalse
    simp [ht, hfalse, List.reverse_append, hnum, hv]

theorem parseMSLExpr_bitNot_step (a : MSLExpr) (rest : List Char) (fuel : Nat)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ')' :: rest) = some (a, ')' :: rest)) :
    parseMSLExpr (fuel + 1) ((ppMSLExpr (.bitNot a)).toList ++ rest) =
      some (.bitNot a, rest) := by
  simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append]
  simp [parseMSLExpr, h, stripPrefixChars]

theorem parseMSLExpr_logNot_step (a : MSLExpr) (rest : List Char) (fuel : Nat)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ')' :: rest) = some (a, ')' :: rest)) :
    parseMSLExpr (fuel + 1) ((ppMSLExpr (.logNot a)).toList ++ rest) =
      some (.logNot a, rest) := by
  simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append]
  simp [parseMSLExpr, h, stripPrefixChars]

theorem parseMSLExpr_neg_step (a : MSLExpr) (rest : List Char) (fuel : Nat)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ')' :: rest) = some (a, ')' :: rest)) :
    parseMSLExpr (fuel + 1) ((ppMSLExpr (.neg a)).toList ++ rest) =
      some (.neg a, rest) := by
  simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append]
  simp [parseMSLExpr, h, stripPrefixChars]

theorem parseMSLExpr_cast_step (ty : MSLType) (a : MSLExpr) (rest : List Char) (fuel : Nat)
    (ht : ty = .ulong ∨ ty = .long ∨ ty = .uint)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ')' :: rest) = some (a, ')' :: rest)) :
    parseMSLExpr (fuel + 1) ((ppMSLExpr (.cast ty a)).toList ++ rest) =
      some (.cast ty a, rest) := by
  rcases ht with rfl | rfl | rfl <;>
    simp [ppMSLExpr, ppMSLType, toString, String.toList_append, List.append_assoc,
      parseMSLExpr, mslNameChar, parseMSLScalarType, stripPrefixChars, h]

theorem ppMSLExpr_canonical_head (e : MSLExpr) (h : CanonicalMSLExpr e) :
    ∃ c cs, (ppMSLExpr e).toList = c :: cs ∧ c ≠ ')' := by
  cases e <;> simp_all [CanonicalMSLExpr, ppMSLExpr, toString, String.toList_append]
  case var name =>
    rcases h.1 with ⟨c, cs, he, hc⟩
    exact ⟨c, ⟨cs, he⟩, by intro hh; subst c; contradiction⟩
  case immU64 v =>
    have hn := Nat.toDigits_ne_nil (n := v.toNat) (b := 10)
    cases he : Nat.toDigits 10 v.toNat with
    | nil => contradiction
    | cons c cs =>
      refine ⟨c, ⟨cs ++ ['U', 'L'], rfl⟩, ?_⟩
      have hc := Nat.isDigit_of_mem_toDigits (b := 10) (n := v.toNat) (by omega) (by omega)
        (show c ∈ Nat.toDigits 10 v.toNat by simp [he])
      intro hh; subst c; contradiction
  case immBool b => cases b <;> simp
  case index name idx =>
    rcases h.1.1 with ⟨c, cs, he, hc⟩
    refine ⟨c, ⟨cs ++ '[' :: ((ppMSLExpr idx).toList ++ [']']), ?_⟩, ?_⟩
    · rw [he]; rfl
    · intro hh; subst c; contradiction

theorem parseMSLExpr_clz_step (a : MSLExpr) (ha : CanonicalMSLExpr a)
    (rest : List Char) (fuel : Nat) (hf : 4 < fuel)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ')' :: rest) = some (a, ')' :: rest)) :
    parseMSLExpr (fuel + 2) ((ppMSLExpr (.clz a)).toList ++ rest) =
      some (.clz a, rest) := by
  have hs := scanMSLName_append "clz".toList ('(' :: ((ppMSLExpr a).toList ++ ')' :: rest))
    (fuel + 1) (by decide) (by exact Or.inr ⟨'(', _, rfl, rfl⟩) (by simp; omega)
  rcases ppMSLExpr_canonical_head a ha with ⟨c, cs, he, hc⟩
  simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append]
  have hs' := hs
  simp only [String.reduceToList, List.cons_append, List.nil_append] at hs'
  rw [parseMSLExpr] <;> try { intros; contradiction }
  rw [hs']
  have hp : parseMSLExprArgs (fuel + 1) ((ppMSLExpr a).toList ++ ')' :: rest) =
      some (.cons a .nil, rest) := by
    rw [he] at h ⊢
    simp only [List.cons_append] at h ⊢
    simp [parseMSLExprArgs, hc, h]
  simp [hp]
  all_goals simp

theorem parseMSLExpr_index_step (name : String) (hn : CanonicalMSLName name)
    (idx : MSLExpr) (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel)
    (h : parseMSLExpr fuel ((ppMSLExpr idx).toList ++ ']' :: rest) = some (idx, ']' :: rest)) :
    parseMSLExpr (fuel + 1) ((ppMSLExpr (.index name idx)).toList ++ rest) =
      some (.index name idx, rest) := by
  have hs := scanMSLName_append name.toList ('[' :: ((ppMSLExpr idx).toList ++ ']' :: rest))
    fuel hn.2.1 (Or.inr ⟨'[', _, rfl, rfl⟩) hf
  rcases hn with ⟨⟨c, cs, he, hc⟩, _, ht, hfalse, hul, _⟩
  have hc' : c ≠ '(' := by intro hh; subst c; contradiction
  have hname : String.ofList (c :: cs) = name := by rw [← he]; simp
  have hul' : ¬ ['L', 'U'] <+: cs.reverse ++ [c] := by
    intro hp
    have hh := List.isPrefixOf_iff_prefix.mpr hp
    rw [he] at hul
    simp only [List.reverse_cons] at hul
    rw [hul] at hh
    contradiction
  simp only [String.ofList_cons] at hname
  simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
    List.append_assoc, List.cons_append, List.nil_append]
  rw [he] at hs ⊢
  simp only [List.cons_append] at hs ⊢
  rw [parseMSLExpr]
  · rw [hs]
    simp [hname, ht, hfalse, hul', h, stripPrefixChars]
  all_goals simp [hc']

theorem parseMSLExprTail_select_step (a b c : MSLExpr) (rest : List Char) (fuel : Nat)
    (hb : parseMSLExpr fuel ((ppMSLExpr b).toList ++ ' ' :: ':' :: ' ' ::
      ((ppMSLExpr c).toList ++ ')' :: rest)) =
      some (b, ' ' :: ':' :: ' ' :: ((ppMSLExpr c).toList ++ ')' :: rest)))
    (hc : parseMSLExpr fuel ((ppMSLExpr c).toList ++ ')' :: rest) = some (c, ')' :: rest)) :
    parseMSLExprTail (fuel + 1) a (' ' :: '?' :: ' ' ::
      ((ppMSLExpr b).toList ++ ' ' :: ':' :: ' ' :: ((ppMSLExpr c).toList ++ ')' :: rest))) =
      some (.select a b c, rest) := by
  simp [parseMSLExprTail, stripPrefixChars, hb, hc]

theorem parseMSLExprTail_binary_step (opcode : String) (ctor : MSLExpr → MSLExpr → MSLExpr)
    (hop : mslBinary opcode = some ctor) (hspace : ∀ c ∈ opcode.toList, c ≠ ' ')
    (hquestion : ∀ cs, opcode.toList ≠ '?' :: cs)
    (a b : MSLExpr) (rest : List Char) (fuel : Nat)
    (hb : parseMSLExpr fuel ((ppMSLExpr b).toList ++ ')' :: rest) = some (b, ')' :: rest)) :
    parseMSLExprTail (fuel + 1) a
      (' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest))) =
      some (ctor a b, rest) := by
  have ht : (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest)).takeWhile (· != ' ') =
      opcode.toList := by
    rw [List.takeWhile_append_of_pos (by intro c hc; simpa using hspace c hc)]
    simp
  have hq : stripPrefixChars [' ', '?', ' ']
      (' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest))) = none := by
    cases he : opcode.toList with
    | nil => rfl
    | cons c cs =>
      by_cases hc : c = '?'
      · subst c
        exact False.elim (hquestion cs he)
      · simp [stripPrefixChars, Ne.symm hc]
  simp only [parseMSLExprTail, hq]
  have hp := stripPrefixChars_append (opcode.toList ++ [' ']) ((ppMSLExpr b).toList ++ ')' :: rest)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hp
  simp [stripPrefixChars, ht, hp, hop, hb]

theorem parseMSLExprArgs_singleton_step (a : MSLExpr) (ha : CanonicalMSLExpr a)
    (rest : List Char) (fuel : Nat)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ')' :: rest) = some (a, ')' :: rest)) :
    parseMSLExprArgs (fuel + 1) ((ppMSLExpr a).toList ++ ')' :: rest) =
      some (.cons a .nil, rest) := by
  obtain ⟨c, cs, he, hc⟩ := ppMSLExpr_canonical_head a ha
  rw [he] at h ⊢
  simp only [List.cons_append] at h
  simp [parseMSLExprArgs, hc, h]

theorem parseMSLExprArgs_cons_step (a : MSLExpr) (ha : CanonicalMSLExpr a)
    (args : MSLExprList) (input rest : List Char) (fuel : Nat)
    (h : parseMSLExpr fuel ((ppMSLExpr a).toList ++ ',' :: ' ' :: input) =
      some (a, ',' :: ' ' :: input))
    (hs : parseMSLExprArgs fuel input = some (args, rest)) :
    parseMSLExprArgs (fuel + 1) ((ppMSLExpr a).toList ++ ',' :: ' ' :: input) =
      some (.cons a args, rest) := by
  obtain ⟨c, cs, he, hc⟩ := ppMSLExpr_canonical_head a ha
  rw [he] at h ⊢
  simp only [List.cons_append] at h
  simp [parseMSLExprArgs, hc, h, hs, stripPrefixChars]

theorem parseMSLExpr_builtin_step (name : String)
    (hn : name = "select" ∨ name = "fma")
    (a b c : MSLExpr) (input rest : List Char) (fuel : Nat)
    (hf : 6 < fuel)
    (h : parseMSLExprArgs fuel input = some (.cons a (.cons b (.cons c .nil)), rest)) :
    parseMSLExpr (fuel + 1) (name.toList ++ '(' :: input) =
      some (if name = "select" then .builtinSelect a b c else .fma a b c, rest) := by
  have hchars : ∀ c ∈ name.toList, mslNameChar c = true := by
    rcases hn with rfl | rfl <;> simp [mslNameChar] <;> decide
  have hlen : name.toList.length < fuel := by
    rcases hn with rfl | rfl <;> simp only [String.reduceToList, List.length_cons, List.length_nil] <;> omega
  have hs := scanMSLName_append name.toList ('(' :: input) fuel hchars
    (Or.inr ⟨'(', input, rfl, rfl⟩) hlen
  rcases hn with rfl | rfl
  all_goals
    simp only [String.reduceToList, List.cons_append, List.nil_append] at hs ⊢
    rw [parseMSLExpr]
    · rw [hs]
      simp [h]
    all_goals simp

theorem parseMSLExprArgs_three_step (a b c : MSLExpr)
    (ha : CanonicalMSLExpr a) (hb : CanonicalMSLExpr b) (hc : CanonicalMSLExpr c)
    (rest : List Char) (fuel : Nat)
    (pa : parseMSLExpr (fuel + 2) ((ppMSLExpr a).toList ++ ',' :: ' ' ::
      ((ppMSLExpr b).toList ++ ',' :: ' ' :: ((ppMSLExpr c).toList ++ ')' :: rest))) =
      some (a, ',' :: ' ' :: ((ppMSLExpr b).toList ++ ',' :: ' ' ::
        ((ppMSLExpr c).toList ++ ')' :: rest))))
    (pb : parseMSLExpr (fuel + 1) ((ppMSLExpr b).toList ++ ',' :: ' ' ::
      ((ppMSLExpr c).toList ++ ')' :: rest)) =
      some (b, ',' :: ' ' :: ((ppMSLExpr c).toList ++ ')' :: rest)))
    (pc : parseMSLExpr fuel ((ppMSLExpr c).toList ++ ')' :: rest) = some (c, ')' :: rest)) :
    parseMSLExprArgs (fuel + 3) ((ppMSLExpr a).toList ++ ',' :: ' ' ::
      ((ppMSLExpr b).toList ++ ',' :: ' ' :: ((ppMSLExpr c).toList ++ ')' :: rest))) =
      some (.cons a (.cons b (.cons c .nil)), rest) :=
  parseMSLExprArgs_cons_step a ha _ _ rest (fuel + 2) pa
    (parseMSLExprArgs_cons_step b hb _ _ rest (fuel + 1) pb
      (parseMSLExprArgs_singleton_step c hc rest fuel pc))

theorem parseMSLAttr_roundtrip (attr : MSLAttr) (fuel : Nat) :
    parseMSLAttr (fuel + 1) (ppMSLAttr attr).toList = some attr := by
  cases attr with
  | buffer n =>
    simpa [ppMSLAttr, parseMSLAttr, String.toList_append, List.reverse_append,
      toString, Nat.repr] using Nat.toNat?_repr n
  | _ => rfl

theorem ppMSLAttr_injective_via_parser : Function.Injective ppMSLAttr := by
  intro a b h
  have hp := congrArg (fun s : String => parseMSLAttr 1 s.toList) h
  simpa only [parseMSLAttr_roundtrip, Option.some.injEq] using hp

/-- `writeDeviceBuffer` never alters `constantBuffers` or `threadgroupArrays`. -/
theorem writeDeviceBuffer_preserves_const_and_tg (g g' : MSLGroupState)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64))
    (h : writeDeviceBuffer g bufIdx elemTy elemIdx val fields = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.threadgroupArrays = g.threadgroupArrays := by
  unfold writeDeviceBuffer at h
  cases hLookup : g.deviceBuffers.lookup bufIdx <;> simp [hLookup] at h
  case some mem =>
    cases hStore : storeTypedElem g.structs mem elemTy
        (elemIdx * aggregateByteWidth g.structs elemTy) val fields <;>
      simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `writeThreadgroupArray` never alters `constantBuffers` or `deviceBuffers`. -/
theorem writeThreadgroupArray_preserves_const_and_dev (g g' : MSLGroupState)
    (arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64))
    (h : writeThreadgroupArray g arrName elemTy elemIdx val fields = .ok g') :
    g'.constantBuffers = g.constantBuffers ∧ g'.deviceBuffers = g.deviceBuffers := by
  unfold writeThreadgroupArray at h
  cases hLookup : g.threadgroupArrays.lookup arrName <;> simp [hLookup] at h
  case some mem =>
    cases hStore : storeTypedElem g.structs mem elemTy
        (elemIdx * aggregateByteWidth g.structs elemTy) val fields <;>
      simp [hStore] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- `execIndexWrite` preserves `constantBuffers` across every address space and atomicity mode. -/
theorem execIndexWrite_preserves_constant_buffers (g g' : MSLGroupState)
    (tid : Dim3) (target : String) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold execIndexWrite at h
  cases hBind : g.bindings.lookup target <;> simp [hBind] at h
  case some binding =>
    cases binding with
    | constantBuf _ _ => simp at h
    | constantScalar _ _ => simp at h
    | deviceBuf bufIdx isConst elemTy =>
      cases isConst <;> simp at h
      cases hRec : recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device
          (elemIdx * aggregateByteWidth g.structs elemTy)
          (aggregateByteWidth g.structs elemTy) true atomic <;>
        simp [hRec, propagateErr] at h
      case ok log' =>
        exact (writeDeviceBuffer_preserves_const_and_tg
          { g with epochLog := log' } g' bufIdx elemTy elemIdx val fields h).1
    | threadgroupArr arrName elemTy =>
      simp at h
      cases hRec : recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup
          (elemIdx * aggregateByteWidth g.structs elemTy)
          (aggregateByteWidth g.structs elemTy) true atomic <;>
        simp [hRec, propagateErr] at h
      case ok log' =>
        exact (writeThreadgroupArray_preserves_const_and_dev
          { g with epochLog := log' } g' arrName elemTy elemIdx val fields h).1

/-- `execAtomicRMW` preserves `constantBuffers` across both `device` and `threadgroup` targets. -/
theorem execAtomicRMW_preserves_constant_buffers (g g' : MSLGroupState)
    (tid : Dim3) (ls ls' : MSLLocals) (declTy : Option MSLType) (dst : Option String)
    (target : String) (elemIdx : Nat) (rmw : MSLType → BitVec 64 → BitVec 64)
    (h : execAtomicRMW g tid ls declTy dst target elemIdx rmw = .ok (ls', g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold execAtomicRMW at h
  cases hB : g.bindings.lookup target <;> simp [hB] at h
  case some b =>
    cases b with
    | constantBuf _ _ => simp at h
    | constantScalar _ _ => simp at h
    | deviceBuf bufIdx isConst elemTy =>
      cases isConst <;> simp at h
      cases hM : g.deviceBuffers.lookup bufIdx <;> simp [hM] at h
      case some mem =>
        cases hL : mem.loadBits (elemIdx * aggregateByteWidth g.structs elemTy)
            elemTy.byteWidth <;> simp [hL] at h
        case some old =>
          cases hW : execIndexWrite g tid target elemIdx
              (maskForType elemTy (rmw elemTy (maskForType elemTy old))) [] true <;>
            simp [hW, propagateErr] at h
          case ok gMid =>
            rw [← h.2]
            exact execIndexWrite_preserves_constant_buffers g gMid tid target elemIdx _ [] true hW
    | threadgroupArr arrName elemTy =>
      simp at h
      cases hM : g.threadgroupArrays.lookup arrName <;> simp [hM] at h
      case some mem =>
        cases hL : mem.loadBits (elemIdx * aggregateByteWidth g.structs elemTy)
            elemTy.byteWidth <;> simp [hL] at h
        case some old =>
          cases hW : execIndexWrite g tid target elemIdx
              (maskForType elemTy (rmw elemTy (maskForType elemTy old))) [] true <;>
            simp [hW, propagateErr] at h
          case ok gMid =>
            rw [← h.2]
            exact execIndexWrite_preserves_constant_buffers g gMid tid target elemIdx _ [] true hW

/-- `constant` address-space immutability (statement level): executing ANY `MSLStmt` preserves
    `g.constantBuffers` bit-identically whenever it succeeds. -/
theorem exec_preserves_constant_buffers (g : MSLGroupState) (th : MSLThreadState)
    (stmt : MSLStmt) (rest : List MSLStmt) (th' : MSLThreadState) (g' : MSLGroupState)
    (h : execNonBarrierStmt g th stmt rest = .ok (th', g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold execNonBarrierStmt execStmtWithCall at h
  cases stmt with
  | varDecl ty name rhs =>
    dsimp only at h
    split at h
    · rename_i bufIdx elemTy _
      cases hC : g.constantBuffers.lookup bufIdx <;> simp [hC] at h
      case some mem =>
        cases hL : loadTypedElem g.structs mem elemTy 0 <;> simp [hL] at h
        rw [← h.2]
    · cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs <;>
        simp [hE, propagateErr] at h
      rw [← h.2]
  | arrayDecl elemTy name count initList =>
    dsimp only at h
    cases hE : evalExprSlotList kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog initList <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | assign name rhs =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | fieldAssign varName field rhs =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | indexAssign target idxExpr rhsExpr =>
    dsimp only at h
    cases hI : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr <;>
      simp [hI, propagateErr] at h
    case ok ei =>
      cases hR : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid ei.locals ei.log rhsExpr <;>
        simp [hR] at h
      case ok er =>
        cases hArr : er.locals.lookupArray? target with
        | some slots =>
          simp [hArr] at h
          cases hUpd : updateArraySlot g.structs
              ((er.locals.lookupType? target).getD (inferExprType g er.locals rhsExpr))
              slots ei.value.toNat er.value er.fields <;>
            simp [hUpd] at h
          rw [← h.2]
        | none =>
          simp [hArr] at h
          cases hW : execIndexWrite { g with epochLog := er.log } th.tid target
              ei.value.toNat er.value er.fields false <;>
            simp [hW] at h
          case ok gMid =>
            rw [← h.2]
            exact execIndexWrite_preserves_constant_buffers
              { g with epochLog := er.log } gMid th.tid target ei.value.toNat er.value er.fields false hW
  | derefAssign ptrName rhsExpr =>
    dsimp only at h
    cases hR : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhsExpr <;>
      simp [hR, propagateErr] at h
    case ok er =>
      cases hArr : er.locals.lookupArray? ptrName with
      | some slots =>
        simp [hArr] at h
        cases hUpd : updateArraySlot g.structs
            ((er.locals.lookupType? ptrName).getD (inferExprType g er.locals rhsExpr))
            slots 0 er.value er.fields <;>
          simp [hUpd] at h
        rw [← h.2]
      | none =>
        simp [hArr] at h
        cases hW : execIndexWrite { g with epochLog := er.log } th.tid ptrName
            0 er.value er.fields false <;>
          simp [hW] at h
        case ok gMid =>
          rw [← h.2]
          exact execIndexWrite_preserves_constant_buffers
            { g with epochLog := er.log } gMid th.tid ptrName 0 er.value er.fields false hW
  | callAssign declTy dst fnName args =>
    dsimp only at h
    cases hC : kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog fnName args <;>
      simp [hC, propagateErr] at h
    rw [← h.2]
  | exprStmt e =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog e <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | atomicFetchAdd declTy dst target idxOpt valExpr =>
    dsimp only at h
    cases idxOpt with
    | none =>
      cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog valExpr <;>
        simp [hV, propagateErr] at h
      case ok ev =>
        cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
            0 (fun _ old => old + ev.value) <;>
          simp [hA] at h
        case ok pair =>
          rw [← h.2]
          exact execAtomicRMW_preserves_constant_buffers
            { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
            0 _ hA
    | some idxExpr =>
      cases hI : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr <;>
        simp [hI, propagateErr] at h
      case ok ei =>
        cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid ei.locals ei.log valExpr <;>
          simp [hV] at h
        case ok ev =>
          cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
              ei.value.toNat (fun _ old => old + ev.value) <;>
            simp [hA] at h
          case ok pair =>
            rw [← h.2]
            exact execAtomicRMW_preserves_constant_buffers
              { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
              ei.value.toNat _ hA
  | atomicExchange declTy dst target idxOpt valExpr =>
    dsimp only at h
    cases idxOpt with
    | none =>
      cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog valExpr <;>
        simp [hV, propagateErr] at h
      case ok ev =>
        cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
            0 (fun _ _ => ev.value) <;>
          simp [hA] at h
        case ok pair =>
          rw [← h.2]
          exact execAtomicRMW_preserves_constant_buffers
            { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
            0 _ hA
    | some idxExpr =>
      cases hI : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr <;>
        simp [hI, propagateErr] at h
      case ok ei =>
        cases hV : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid ei.locals ei.log valExpr <;>
          simp [hV] at h
        case ok ev =>
          cases hA : execAtomicRMW { g with epochLog := ev.log } th.tid ev.locals declTy dst target
              ei.value.toNat (fun _ _ => ev.value) <;>
            simp [hA] at h
          case ok pair =>
            rw [← h.2]
            exact execAtomicRMW_preserves_constant_buffers
              { g with epochLog := ev.log } pair.2 th.tid ev.locals pair.1 declTy dst target
              ei.value.toNat _ hA
  | simdShuffleXor _ _ _ _ => simp at h
  | simdSum _ _ _ => simp at h
  | threadgroupBarrier => simp at h
  | ifElse cond thenBr elseBr =>
    dsimp only at h
    cases hC : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog cond <;>
      simp [hC, propagateErr] at h
    rw [← h.2]
  | forLoop loopVar ty initExpr condExpr stepExpr body =>
    dsimp only at h
    cases hInit : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog initExpr <;>
      simp [hInit, propagateErr] at h
    rw [← h.2]
  | whileLoop condExpr body =>
    dsimp only at h
    cases hC : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog condExpr <;>
      simp [hC, propagateErr] at h
    case ok ev =>
      split at h <;> simp at h <;> rw [← h.2]
  | returnVal e =>
    dsimp only at h
    cases hE : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog e <;>
      simp [hE, propagateErr] at h
    rw [← h.2]
  | returnStmt =>
    dsimp only at h
    simp at h
    rw [← h.2]

/-- Explicit write rejection for `constant` buffers: any indexed write targeting a `constant`
    buffer binding traps with `MSLOutcome.readOnlyViolation`. -/
theorem constant_write_rejected (g : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_const : g.bindings.lookup target = some (.constantBuf bufIdx elemTy)) :
    execIndexWrite g tid target elemIdx val fields atomic = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_const]

/-- Explicit write rejection for `device const T*` buffers: any indexed write targeting a
    read-only `device const` pointer traps with `MSLOutcome.readOnlyViolation`. -/
theorem device_const_write_rejected (g : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_ro : g.bindings.lookup target = some (.deviceBuf bufIdx true elemTy)) :
    execIndexWrite g tid target elemIdx val fields atomic = .readOnlyViolation target elemIdx := by
  unfold execIndexWrite
  rw [h_ro]

/-- Address-space isolation (`device` -> `threadgroup`): writing to a mutable `device` buffer
    never mutates per-threadgroup shared memory `threadgroupArrays`. -/
theorem device_write_preserves_threadgroup (g g' : MSLGroupState) (tid : Dim3) (target : String)
    (bufIdx : Nat) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_dev : g.bindings.lookup target = some (.deviceBuf bufIdx false elemTy))
    (h_exec : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.threadgroupArrays = g.threadgroupArrays := by
  unfold execIndexWrite at h_exec
  rw [h_dev] at h_exec
  dsimp only at h_exec
  cases hRec : recordEpochAccess g.epochLog tid (.deviceBuf bufIdx) .device
      (elemIdx * aggregateByteWidth g.structs elemTy)
      (aggregateByteWidth g.structs elemTy) true atomic <;>
    simp [hRec, propagateErr] at h_exec
  case ok log' =>
    exact (writeDeviceBuffer_preserves_const_and_tg
      { g with epochLog := log' } g' bufIdx elemTy elemIdx val fields h_exec).2

/-- Address-space isolation (`threadgroup` -> `device`): writing to a `threadgroup` shared array
    never mutates `deviceBuffers`. -/
theorem threadgroup_write_preserves_device (g g' : MSLGroupState) (tid : Dim3)
    (target arrName : String) (elemTy : MSLType) (elemIdx : Nat) (val : BitVec 64)
    (fields : List (String × BitVec 64)) (atomic : Bool)
    (h_tg : g.bindings.lookup target = some (.threadgroupArr arrName elemTy))
    (h_exec : execIndexWrite g tid target elemIdx val fields atomic = .ok g') :
    g'.deviceBuffers = g.deviceBuffers := by
  unfold execIndexWrite at h_exec
  rw [h_tg] at h_exec
  dsimp only at h_exec
  cases hRec : recordEpochAccess g.epochLog tid (.threadgroupArr arrName) .threadgroup
      (elemIdx * aggregateByteWidth g.structs elemTy)
      (aggregateByteWidth g.structs elemTy) true atomic <;>
    simp [hRec, propagateErr] at h_exec
  case ok log' =>
    exact (writeThreadgroupArray_preserves_const_and_dev
      { g with epochLog := log' } g' arrName elemTy elemIdx val fields h_exec).2

/-- Scalar out-of-bounds `device` buffer write safety: when `elemTy` is a scalar (`structFieldNames = []`)
    and `elemIdx * elemTy.byteWidth + elemTy.byteWidth > mem.bytes.size`, `writeDeviceBuffer`
    traps with `MSLOutcome.outOfBoundsWrite .device bufIdx elemIdx`. -/
theorem oob_device_write_caught (g : MSLGroupState) (bufIdx : Nat) (elemTy : MSLType)
    (elemIdx : Nat) (val : BitVec 64) (fields : List (String × BitVec 64)) (mem : ByteMemory)
    (h_scalar : structFieldNames g.structs elemTy = [])
    (h_w : aggregateByteWidth g.structs elemTy = elemTy.byteWidth)
    (h_buf : g.deviceBuffers.lookup bufIdx = some mem)
    (h_oob : mem.bytes.size < elemIdx * elemTy.byteWidth + elemTy.byteWidth) :
    writeDeviceBuffer g bufIdx elemTy elemIdx val fields =
      .outOfBoundsWrite .device bufIdx elemIdx := by
  unfold writeDeviceBuffer storeTypedElem
  rw [h_buf, h_w, h_scalar]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  unfold ByteMemory.storeBits
  have hNotLe : ¬ (elemIdx * elemTy.byteWidth + elemTy.byteWidth ≤ mem.bytes.size) :=
    Nat.not_le_of_gt h_oob
  simp [hNotLe]

/-- Out-of-bounds read on a `thread` local array (`arr[idx]` with `idx ≥ slots.length`) traps
    with `MSLOutcome.outOfBoundsLoad .thread 0 idx`. -/
theorem oob_thread_array_load_traps (g : MSLGroupState) (th : MSLThreadState)
    (arrName : String) (slots : List MSLLocalSlot) (idx : BitVec 64)
    (h_arr : th.locals.lookupArray? arrName = some slots)
    (h_oob : slots.length ≤ idx.toNat) :
    evalMSLExpr g th (.index arrName (.immU64 idx)) =
      .outOfBoundsLoad .thread 0 idx.toNat := by
  have hNone : slots[idx.toNat]? = none := List.getElem?_eq_none h_oob
  simp [evalMSLExpr, evalExprWithCall, bindEval, h_arr, hNone, propagateErr]

/-- Out-of-bounds write to a `thread` local array (`arr[idx] = v` with `idx ≥ slots.length`)
    traps with `MSLOutcome.outOfBoundsWrite .thread 0 idx`. -/
theorem oob_thread_array_write_traps (g : MSLGroupState) (th : MSLThreadState)
    (arrName : String) (slots : List MSLLocalSlot) (idx val : BitVec 64)
    (rest : List MSLStmt)
    (h_arr : th.locals.lookupArray? arrName = some slots)
    (h_oob : slots.length ≤ idx.toNat) :
    execNonBarrierStmt g th (.indexAssign arrName (.immU64 idx) (.immU64 val)) rest =
      .outOfBoundsWrite .thread 0 idx.toNat := by
  have hNotLt : ¬ (idx.toNat < slots.length) := Nat.not_lt.mpr h_oob
  simp [execNonBarrierStmt, execStmtWithCall, evalExprWithCall, updateArraySlot, h_arr, hNotLt]

private theorem promote_ulong_ulong : promoteMSLArithType .ulong .ulong = .ulong := rfl
private theorem promote_int_int : promoteMSLArithType .int .int = .int := rfl
private theorem promote_float_float : promoteMSLArithType .float .float = .float := rfl
private theorem cast_ulong_ulong (v : BitVec 64) : evalMSLCast .ulong .ulong v = .ok v := rfl
private theorem cast_float_float (v : BitVec 64) :
    evalMSLCast .float .float v = .ok (v &&& 0xFFFF_FFFF#64) := rfl

/-- Division by zero traps with `MSLOutcome.divisionByZero` rather than returning `0`. -/
theorem msl_div_zero_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .ulong)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_tyy : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th (.div (.var rx) (.var ry)) = .divisionByZero := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_ulong_ulong, MSLType.isVector, cast_ulong_ulong,
    evalTypedBin, propagateErr, h_rx, h_tyx, h_ry, h_tyy]

/-- Signed 32-bit `INT32_MIN / -1` traps with `MSLOutcome.signedDivOverflow`. -/
theorem msl_signed_div_overflow_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String)
    (h_rx : th.locals.lookup? rx = some 2147483648#64)
    (h_tyx : th.locals.lookupType? rx = some .int)
    (h_ry : th.locals.lookup? ry = some 4294967295#64)
    (h_tyy : th.locals.lookupType? ry = some .int) :
    evalMSLExpr g th (.div (.var rx) (.var ry)) = .signedDivOverflow := by
  have hCast1 : evalMSLCast .int .int 2147483648#64 = .ok 2147483648#64 := rfl
  have hCast2 : evalMSLCast .int .int 4294967295#64 = .ok 4294967295#64 := rfl
  have hDiv : evalTypedBin .int .div 2147483648#64 4294967295#64 = .signedDivOverflow := rfl
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_int_int, MSLType.isVector, hCast1, hCast2, hDiv, propagateErr,
    h_rx, h_tyx, h_ry, h_tyy]

/-- Production C++ ternary `((ry != 0UL) ? (rx / ry) : 0UL)` short-circuits `rx / ry` when
    `ry == 0` and safely returns `0#64` even without evaluating `rx`. -/
theorem msl_guarded_div_zero_safe (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_ty : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th
      (.select (.ne (.var ry) (.immU64 0#64)) (.div (.var rx) (.var ry)) (.immU64 0#64)) =
      .ok 0#64 := by
  have hCmp : evalTypedCmp .ulong .ne 0#64 0#64 = .ok 0#64 := rfl
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishCmp, inferExprType,
    promote_ulong_ulong, cast_ulong_ulong, hCmp, h_ry, h_ty]

/-- Mutant `M9` soundness witness: replacing C++ short-circuit `?:` with Metal's eager
    `select(0UL, rx / ry, ry != 0UL)` evaluates `rx / ry` when `ry == 0` and traps with
    `MSLOutcome.divisionByZero`. -/
theorem msl_builtinSelect_eager_div_zero_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .ulong)
    (h_ry : th.locals.lookup? ry = some 0#64)
    (h_tyy : th.locals.lookupType? ry = some .ulong) :
    evalMSLExpr g th
      (.builtinSelect (.immU64 0#64) (.div (.var rx) (.var ry)) (.ne (.var ry) (.immU64 0#64))) =
      .divisionByZero := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_ulong_ulong, MSLType.isVector, cast_ulong_ulong,
    evalTypedBin, propagateErr, h_rx, h_tyx, h_ry, h_tyy]

/-- Short-circuit logical AND (`&&`): `false && rhs` returns `0#64` (`false`) without evaluating
    `rhs` (even when `rhs` is `1UL / 0UL`). -/
theorem msl_logAnd_short_circuits_false (g : MSLGroupState) (th : MSLThreadState)
    (rhs : MSLExpr) :
    evalMSLExpr g th (.logAnd (.immBool false) rhs) = .ok 0#64 := rfl

/-- Short-circuit logical OR (`||`): `true || rhs` returns `1#64` (`true`) without evaluating
    `rhs` (even when `rhs` is `1UL / 0UL`). -/
theorem msl_logOr_short_circuits_true (g : MSLGroupState) (th : MSLThreadState)
    (rhs : MSLExpr) :
    evalMSLExpr g th (.logOr (.immBool true) rhs) = .ok 1#64 := rfl

/-- Floating-point remainder (`%`) is rejected with `MSLOutcome.unsupportedFloatOp` instead of
    silently applying integer modulo to IEEE-754 bit patterns. -/
theorem msl_float_rem_unsupported (g : MSLGroupState) (th : MSLThreadState)
    (rx ry : String) (vx vy : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_tyx : th.locals.lookupType? rx = some .float)
    (h_ry : th.locals.lookup? ry = some vy)
    (h_tyy : th.locals.lookupType? ry = some .float) :
    evalMSLExpr g th (.rem (.var rx) (.var ry)) = .unsupportedFloatOp "float remainder" := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishBin, inferExprType,
    promote_float_float, MSLType.isVector, cast_float_float, evalTypedBin, propagateErr,
    h_rx, h_tyx, h_ry, h_tyy]

/-- Shifting a 32-bit `uint` by an amount `≥ 32` traps with `MSLOutcome.shiftOutOfRange`. -/
theorem msl_uint_shift_ge_width_traps (g : MSLGroupState) (th : MSLThreadState)
    (rx : String) (vx amt : BitVec 64)
    (h_rx : th.locals.lookup? rx = some vx)
    (h_ty : th.locals.lookupType? rx = some .uint)
    (h_ge : 32 ≤ amt.toNat) :
    evalMSLExpr g th (.shl (.var rx) (.immU64 amt)) = .shiftOutOfRange := by
  simp [evalMSLExpr, evalExprWithCall, bindEval, finishShift, inferExprType,
    MSLType.isFloat, MSLType.isVector, MSLType.bitWidth, propagateErr, h_rx, h_ty, h_ge]

/-- Usual arithmetic conversion rank: `uint` + `ulong` promotes to 64-bit `.ulong` rather than
    truncating the 64-bit operand to 32-bit `.uint`. -/
theorem promoteMSLArithType_uint_ulong :
    promoteMSLArithType .uint .ulong = .ulong := rfl

/-- Mixed `uint + ulong` arithmetic preserves full 64-bit precision (`1u + 0x1_0000_0000UL`). -/
theorem msl_uint_add_ulong_promotes :
    let ls := (MSLLocals.empty.setTyped "u" .uint 1#64).setTyped "w" .ulong 0x1_0000_0000#64
    let g : MSLGroupState := { gridDim := {}, groupDim := {}, groupId := {} }
    let th : MSLThreadState := { tid := {}, locals := ls }
    evalMSLExpr g th (.add (.var "u") (.var "w")) = .ok 0x1_0000_0001#64 := rfl

/-- Arithmetic right shift (`>>`) on signed 32-bit `.int` sign-extends the high bit
    (`-8 >> 1 = -4`, represented masked to 32 bits as `0xFFFF_FFFC#64`). -/
theorem msl_signed_int_shr_sign_extends :
    let ls := MSLLocals.empty.setTyped "x" .int 0xFFFF_FFF8#64
    let g : MSLGroupState := { gridDim := {}, groupDim := {}, groupId := {} }
    let th : MSLThreadState := { tid := {}, locals := ls }
    evalMSLExpr g th (.shr (.var "x") (.immU64 1#64)) = .ok 0xFFFF_FFFC#64 := rfl

/-- Multi-lane `ulong2` store/load roundtrip preserves both `.x` and `.y` 64-bit lanes. -/
theorem ulong2_store_load_roundtrip :
    let m0 := ByteMemory.zeros 16
    let flds := [("x", 0x0123_4567_89AB_CDEF#64), ("y", 0xFEDC_BA98_7654_3210#64)]
    (storeTypedElem [] m0 .ulong2 0 0x0123_4567_89AB_CDEF#64 flds).bind
      (fun m1 => loadTypedElem [] m1 .ulong2 0) =
      some (0x0123_4567_89AB_CDEF#64, flds) := rfl

/-- Multi-lane `uint4` store/load roundtrip preserves all four 32-bit lanes (`x, y, z, w`). -/
theorem uint4_store_load_roundtrip :
    let m0 := ByteMemory.zeros 16
    let flds := [("x", 11#64), ("y", 22#64), ("z", 33#64), ("w", 44#64)]
    (storeTypedElem [] m0 .uint4 0 11#64 flds).bind
      (fun m1 => loadTypedElem [] m1 .uint4 0) =
      some (11#64, flds) := rfl

/-- Componentwise `ulong2` XOR (`a ^ b`) computes XOR independently on `.x` and `.y`. -/
theorem ulong2_componentwise_xor :
    let g : MSLGroupState := { gridDim := {}, groupDim := {}, groupId := {} }
    let ls0 := bindValue [] MSLLocals.empty "a" .ulong2 0xAA#64 [("x", 0xAA#64), ("y", 0xFF00#64)]
    let ls1 := bindValue [] ls0 "b" .ulong2 0x0F#64 [("x", 0x0F#64), ("y", 0x0FF0#64)]
    evalExprWithCall kernelCallEval 64 g {} ls1 [] (.bitXor (.var "a") (.var "b")) =
      .ok { value := 0xA5#64, fields := [("x", 0xA5#64), ("y", 0xF0F0#64)],
            locals := ls1, log := [] } := rfl

/-- Disjoint byte ranges never race: recording an access whose byte span lies strictly after a
    prior epoch entry succeeds without triggering `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_disjoint_ok (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat) (isWrite isAtomic : Bool)
    (h_disj : a.addr + a.width ≤ addr) :
    recordEpochAccess [a] tid tgt sp addr width isWrite isAtomic =
      .ok [{ tid, target := tgt, addr, width, isWrite, isAtomic }, a] := by
  have hNo : ¬ (addr < a.addr + a.width ∧ a.addr < addr + width) := by omega
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, rangesOverlap, hNo]

/-- Overlapping unsynchronized cross-thread non-atomic write/access on the same memory target
    traps with `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_overlap_races (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat)
    (h_diff : (tid != a.tid) = true)
    (h_tgt : tgt = a.target)
    (h_ov1 : addr < a.addr + a.width)
    (h_ov2 : a.addr < addr + width) :
    recordEpochAccess [a] tid tgt sp addr width true false =
      .dataRace sp (Nat.max addr a.addr) := by
  subst tgt
  have hTgt : (a.target == a.target) = true := by
    cases a.target with
    | deviceBuf idx => change (idx == idx) = true; simp
    | threadgroupArr nm => change (nm == nm) = true; simp
  have hOv : decide (addr < a.addr + a.width ∧ a.addr < addr + width) = true :=
    decide_eq_true ⟨h_ov1, h_ov2⟩
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, rangesOverlap, h_diff, hTgt, hOv]

/-- Concurrent atomic operations (`isAtomic = true` on both accesses) on the same address by
    distinct threads in the same barrier epoch NEVER trigger `MSLOutcome.dataRace`. -/
theorem recordEpochAccess_atomic_pair_compatible (a : MSLAccess) (tid : Dim3) (tgt : MSLMemTarget)
    (sp : MSLAddressSpace) (addr width : Nat)
    (h_atom : a.isAtomic = true) :
    recordEpochAccess [a] tid tgt sp addr width true true =
      .ok [{ tid, target := tgt, addr, width, isWrite := true, isAtomic := true }, a] := by
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, h_atom]

/-- Mixing an atomic write (`isAtomic = true`) with a non-atomic access (`a.isAtomic = false`) on
    overlapping bytes by distinct threads in the same barrier epoch traps with `.dataRace`. -/
theorem recordEpochAccess_atomic_vs_nonatomic_races (a : MSLAccess) (tid : Dim3)
    (tgt : MSLMemTarget) (sp : MSLAddressSpace) (addr width : Nat)
    (h_diff : (tid != a.tid) = true)
    (h_tgt : tgt = a.target)
    (h_nonatom : a.isAtomic = false)
    (h_ov1 : addr < a.addr + a.width)
    (h_ov2 : a.addr < addr + width) :
    recordEpochAccess [a] tid tgt sp addr width true true =
      .dataRace sp (Nat.max addr a.addr) := by
  subst tgt
  have hTgt : (a.target == a.target) = true := by
    cases a.target with
    | deviceBuf idx => change (idx == idx) = true; simp
    | threadgroupArr nm => change (nm == nm) = true; simp
  have hOv : decide (addr < a.addr + a.width ∧ a.addr < addr + width) = true :=
    decide_eq_true ⟨h_ov1, h_ov2⟩
  simp [recordEpochAccess, findDataRace?, findDataRaceGo, rangesOverlap,
    h_diff, hTgt, h_nonatom, hOv]

/-- Uniform `threadgroupBarrier` synchronization: when a non-empty threadgroup has every thread
    parked at `threadgroup_barrier`, `stepGroupBarrier` converges cleanly, advancing all threads
    past the barrier and clearing `epochLog`. -/
theorem threadgroupBarrier_uniform_converges (g : MSLGroupState)
    (h_nonempty : g.threads.isEmpty = false)
    (h_uniform : g.threads.all threadAtBarrier = true) :
    stepGroupBarrier g =
      .ok { g with threads := g.threads.map advanceBarrierThread, epochLog := [] } := by
  unfold stepGroupBarrier
  simp [h_nonempty, h_uniform]

/-- Divergent `threadgroupBarrier` detection: if the threadgroup is empty or at least one thread
    is not parked at `threadgroup_barrier` when barrier synchronization is attempted,
    `stepGroupBarrier` traps with `MSLOutcome.barrierDivergence`. -/
theorem threadgroupBarrier_divergent_errors (g : MSLGroupState)
    (h_div : (!g.threads.isEmpty && g.threads.all threadAtBarrier) = false) :
    stepGroupBarrier g = .barrierDivergence := by
  unfold stepGroupBarrier
  have hFalse : ¬ ((!g.threads.isEmpty && g.threads.all threadAtBarrier) = true) := by
    rw [h_div]; decide
  exact ite_eq_right_iff.mpr fun h => False.elim (hFalse h)

private theorem stepSimdgroup_preserves_const (g g' : MSLGroupState) (sgId : Nat)
    (h : stepSimdgroup g sgId = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepSimdgroup at h
  dsimp only at h
  cases hLive : g.threads.filter (fun th => !th.halted && simdgroupOf g.groupDim th.tid == sgId) with
  | nil => simp [hLive] at h
  | cons leader rest =>
    simp [hLive] at h
    cases hStmts : leader.stmts with
    | nil => simp [hStmts] at h
    | cons hd tl =>
      cases hd <;> simp [hStmts] at h
      case simdShuffleXor =>
        cases hCS : collectSimdShuffle g sgId g.epochLog g.threads <;>
          simp [hCS, propagateErr] at h
        rw [← h]
      case simdSum declTy dst leaderSrc =>
        cases hCS : collectSimdSum g sgId (inferExprType g leader.locals leaderSrc)
            g.epochLog g.threads <;>
          simp [hCS, propagateErr] at h
        rw [← h]

private theorem stepFirstReady_preserves_const (g : MSLGroupState) :
    ∀ (pre suf : List MSLThreadState) (progressed : Bool) (g' : MSLGroupState),
      stepFirstReadyThread g pre suf = .ok (progressed, g') →
      g'.constantBuffers = g.constantBuffers
  | _, [], _, g', h => by
    simp [stepFirstReadyThread] at h
    rw [← h.2]
  | pre, th :: suf, progressed, g', h => by
    unfold stepFirstReadyThread at h
    split at h
    · exact stepFirstReady_preserves_const g (th :: pre) suf progressed g' h
    · cases hStmts : th.stmts with
      | nil =>
        simp [hStmts] at h
        rw [← h.2]
      | cons s rest =>
        simp [hStmts] at h
        cases hExec : execNonBarrierStmt g th s rest <;>
          simp [hExec, propagateErr] at h
        case ok pair =>
          rw [← h.2]
          exact exec_preserves_constant_buffers g th s rest pair.1 pair.2 hExec

private theorem stepGroup_preserves_const (g g' : MSLGroupState) (done : Bool)
    (hStep : stepGroup g = .ok (done, g')) :
    g'.constantBuffers = g.constantBuffers := by
  unfold stepGroup at hStep
  split at hStep
  · simp at hStep
    exact congrArg MSLGroupState.constantBuffers hStep.2.symm
  · cases hReady : stepFirstReadyThread g [] g.threads <;>
      simp [hReady, propagateErr] at hStep
    case ok rpair =>
      rcases rpair with ⟨progressed, gMid⟩
      have hC1 := stepFirstReady_preserves_const g [] g.threads progressed gMid hReady
      cases progressed with
      | true =>
        simp at hStep
        exact (congrArg MSLGroupState.constantBuffers hStep.2.symm).trans hC1
      | false =>
        simp at hStep
        cases hFind : gMid.threads.find? (fun th => !th.halted && threadAtSimdOp th) with
        | some th =>
          simp [hFind] at hStep
          cases hSimd : stepSimdgroup gMid (simdgroupOf gMid.groupDim th.tid) <;>
            simp [hSimd] at hStep
          case ok synced =>
            have hEq1 := congrArg MSLGroupState.constantBuffers hStep.2.symm
            have hEq2 := stepSimdgroup_preserves_const gMid synced _ hSimd
            exact (hEq1.trans hEq2).trans hC1
        | none =>
          simp [hFind] at hStep
          cases hBar : stepGroupBarrier gMid <;> simp [hBar] at hStep
          case ok synced =>
            have hEq1 := congrArg MSLGroupState.constantBuffers hStep.2.symm
            unfold stepGroupBarrier at hBar
            split at hBar <;> simp at hBar
            have hEq2 : synced.constantBuffers = gMid.constantBuffers := by rw [← hBar]
            exact (hEq1.trans hEq2).trans hC1

/-- Multi-step `constant` buffer immutability: running an entire threadgroup for any `fuel`
    budget preserves `constantBuffers` unchanged. -/
theorem runGroup_preserves_constant_buffers (fuel : Nat) (g g' : MSLGroupState)
    (h : runGroup fuel g = .ok g') :
    g'.constantBuffers = g.constantBuffers := by
  induction fuel generalizing g with
  | zero =>
    unfold runGroup at h
    split at h <;> simp at h
    exact congrArg MSLGroupState.constantBuffers h.symm
  | succ f ih =>
    unfold runGroup at h
    cases hStep : stepGroup g <;> simp [hStep, propagateErr] at h
    case ok pair =>
      rcases pair with ⟨done, gNext⟩
      have hStepConst := stepGroup_preserves_const g gNext done hStep
      cases done with
      | true =>
        simp at h
        exact (congrArg MSLGroupState.constantBuffers h.symm).trans hStepConst
      | false =>
        simp at h
        exact (ih gNext h).trans hStepConst

/-- Halted threadgroup fixed-point: once all threads in `g` have halted, `runGroup` returns
    `.ok g` for every step budget `fuel`. -/
theorem runGroup_halted (fuel : Nat) (g : MSLGroupState)
    (h_halted : g.threads.all (·.halted) = true) :
    runGroup fuel g = .ok g := by
  cases fuel with
  | zero =>
    unfold runGroup
    simp [h_halted]
  | succ f =>
    unfold runGroup stepGroup
    simp [h_halted]

/-- Monotone fuel stability of `runGroup`: once `runGroup f1 g` reaches a terminal
    (non-`fuelExhausted`) outcome `out`, any larger step budget `f2 ≥ f1` reaches the exact same
    terminal outcome `out`. -/
theorem runGroup_mono_fuel (f1 f2 : Nat) (g : MSLGroupState)
    (out : MSLOutcome MSLGroupState)
    (h1 : runGroup f1 g = out)
    (h_term : out ≠ .fuelExhausted)
    (h_le : f1 ≤ f2) :
    runGroup f2 g = out := by
  induction f1 generalizing f2 g with
  | zero =>
    unfold runGroup at h1
    cases hAll : g.threads.all (·.halted)
    · simp [hAll] at h1
      exact False.elim (h_term h1.symm)
    · simp [hAll] at h1
      rw [runGroup_halted f2 g hAll]
      exact h1
  | succ f1' ih =>
    cases f2 with
    | zero => omega
    | succ f2' =>
      have hLe' : f1' ≤ f2' := Nat.le_of_succ_le_succ h_le
      unfold runGroup at h1 ⊢
      cases hStep : stepGroup g <;> simp [hStep, propagateErr] at h1 ⊢
      case ok pair =>
        rcases pair with ⟨done, g'⟩
        cases done with
        | true =>
          simp at h1 ⊢
          exact h1
        | false =>
          simp at h1 ⊢
          exact ih f2' g' h1 hLe'
      all_goals exact h1

/-- Fuel-independent operational determinism of the Metal SIMT threadgroup semantics (`runGroup`):
    any two executions from the same initial `MSLGroupState` under arbitrary step budgets `f1`
    and `f2` that both reach terminal (non-`fuelExhausted`) outcomes produce identical results. -/
theorem runGroup_deterministic (f1 f2 : Nat) (g : MSLGroupState)
    (out1 out2 : MSLOutcome MSLGroupState)
    (h1 : runGroup f1 g = out1)
    (h2 : runGroup f2 g = out2)
    (hne1 : out1 ≠ .fuelExhausted)
    (hne2 : out2 ≠ .fuelExhausted) :
    out1 = out2 := by
  by_cases hLe : f1 ≤ f2
  · have hMono := runGroup_mono_fuel f1 f2 g out1 h1 hne1 hLe
    exact hMono.symm.trans h2
  · have hLe2 : f2 ≤ f1 := by omega
    have hMono := runGroup_mono_fuel f2 f1 g out2 h2 hne2 hLe2
    exact h1.symm.trans hMono

/-- Pass 2 of `simd_sum` distributes the pre-evaluated reduction without adding or dropping
    threads (and without invoking expression evaluation). -/
theorem distributeSimdSum_length (g : MSLGroupState) (sgId : Nat)
    (samples : List (Dim3 × SimdSumSample)) (total : BitVec 64)
    (ths : List MSLThreadState) :
    (distributeSimdSum g sgId samples total ths).length = ths.length := by
  induction ths with
  | nil => rfl
  | cons th rest ih =>
    simp only [distributeSimdSum]
    split
    · cases samples.lookup th.tid <;> simp [ih]
    · simp [ih]

/-- Pass 2 of `simd_shuffle_xor` distributes the pre-evaluated partner values without adding or
    dropping threads (and without invoking expression evaluation). -/
theorem distributeSimdShuffle_length (g : MSLGroupState) (sgId : Nat)
    (samples : List (Dim3 × SimdShuffleSample))
    (laneVals : List (Nat × (BitVec 64 × List (String × BitVec 64))))
    (ths : List MSLThreadState) :
    (distributeSimdShuffle g sgId samples laneVals ths).length = ths.length := by
  induction ths with
  | nil => rfl
  | cons th rest ih =>
    simp only [distributeSimdShuffle]
    split
    · cases samples.lookup th.tid <;> simp [ih]
    · simp [ih]

/-- 1:1 injectivity of `ppMSLAddressSpace`: distinct MSL address spaces render to distinct tokens. -/
theorem ppMSLAddressSpace_injective (s1 s2 : MSLAddressSpace)
    (h : ppMSLAddressSpace s1 = ppMSLAddressSpace s2) :
    s1 = s2 := by
  cases s1 <;> cases s2 <;> first | rfl | exact absurd h (by decide)

/-- Read-only `device const` pointers render with the explicit `device const <T>*` qualifier. -/
theorem ppMSLType_device_const_pointer (elem : MSLType) :
    ppMSLType (.pointer .device true elem) = "device const " ++ ppMSLType elem ++ "*" := rfl

/-- Vector constructor `.structLit .ulong2 (cons a (cons b nil))` renders with Metal call syntax
    `ulong2(...)` rather than C struct brace syntax `{ ... }`. -/
theorem ppMSLExpr_ulong2_constructor (a b : MSLExpr) :
    ppMSLExpr (.structLit .ulong2 (.cons a (.cons b .nil))) =
      "ulong2(" ++ ppMSLExpr a ++ ", " ++ ppMSLExpr b ++ ")" := rfl

private theorem charList_isPrefixOf_append :
    ∀ (xs ys : List Char), List.isPrefixOf xs (xs ++ ys) = true
  | [], _ => rfl
  | x :: xs, ys => by
    simp [charList_isPrefixOf_append xs ys]

/-- Structural header well-formedness of `ppMSLModule`: every rendered Metal module begins with
    `#include <metal_stdlib>\nusing namespace metal;`. -/
theorem ppMSLModule_header_prefix (m : MSLModule) :
    List.isPrefixOf ppMSLModuleHeader.toList (ppMSLModule m).toList = true := by
  unfold ppMSLModule
  cases (m.structs.map ppMSLStructDecl ++ m.funcs.map ppMSLFuncDecl ++ m.kernels.map ppMSLKernel) with
  | nil =>
    rw [String.toList_append]
    exact charList_isPrefixOf_append _ _
  | cons b bs =>
    simp only [String.append_assoc, String.toList_append]
    exact charList_isPrefixOf_append _ _

/-- Structural signature well-formedness of `ppMSLKernel`: every rendered compute kernel begins
    with `kernel void <name>(\n`. -/
theorem ppMSLKernel_signature_prefix (k : MSLKernelDecl) :
    List.isPrefixOf (ppMSLKernelSignaturePrefix k.name).toList (ppMSLKernel k).toList = true := by
  unfold ppMSLKernel
  simp only [String.append_assoc, String.toList_append]
  exact charList_isPrefixOf_append _ _

private theorem getLast_append_singleton (xs : List Char) (c : Char) :
    (xs ++ [c]).getLast? = some c := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons y ys => exact ih

private theorem semicolon_toList_eq : ";".toList = [';'] := by decide

/-- Structural well-formedness of `ppMSLStmt` on `threadgroupBarrier`: renders a semicolon-terminated
    `threadgroup_barrier(mem_flags::mem_threadgroup);` statement for any indentation prefix. -/
theorem ppMSLStmt_barrier_semicolon (indent : String) :
    (ppMSLStmt indent .threadgroupBarrier).toList.getLast? = some ';' := by
  unfold ppMSLStmt
  simp only [String.append_assoc, String.toList_append, semicolon_toList_eq]
  rw [← List.append_assoc]
  exact getLast_append_singleton _ ';'

end LeanNative.Backend.MetalAst
