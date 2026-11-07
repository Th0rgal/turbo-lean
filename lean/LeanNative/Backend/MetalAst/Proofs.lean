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

private theorem parseMSLParamType_pointer_roundtrip (sp : MSLAddressSpace) (isConst : Bool)
    (el : MSLType) (hel : CanonicalMSLValueType el) (hconst : sp = .constant → isConst = false) :
    parseMSLParamType (ppMSLType (.pointer sp isConst el)) = some (.pointer sp isConst el) := by
  have hpel : parseMSLScalarType (ppMSLType el) = some el := parseMSLScalarType_roundtrip el hel
  have hscalar : parseMSLScalarType (ppMSLType (.pointer sp isConst el)) = none := by
    cases sp <;> cases isConst <;> cases el <;> first | exact False.elim hel | rfl
  have hrev (l : List Char) : (l ++ ['*']).reverse = '*' :: l.reverse := by simp
  cases sp <;> cases isConst
  all_goals try exact False.elim (Bool.noConfusion (hconst rfl))
  all_goals
    unfold parseMSLParamType
    rw [hscalar]
    simp only [ppMSLType, ppMSLAddressSpace, Bool.true_and, Bool.false_and, bne,
      Bool.false_eq_true, ↓reduceIte, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [hrev]
    simp [List.reverse_reverse, String.ofList_toList, hpel]

private theorem parseMSLParamType_ref_roundtrip (sp : MSLAddressSpace)
    (el : MSLType) (hel : CanonicalMSLValueType el) :
    parseMSLParamType (ppMSLType (.ref sp el)) = some (.ref sp el) := by
  have hpel : parseMSLScalarType (ppMSLType el) = some el := parseMSLScalarType_roundtrip el hel
  have hscalar : parseMSLScalarType (ppMSLType (.ref sp el)) = none := by
    cases sp <;> cases el <;> first | exact False.elim hel | rfl
  have hnotconst : ∀ rest, (ppMSLType el).toList ++ ['&'] ≠ 'c' :: 'o' :: 'n' :: 's' :: 't' :: ' ' :: rest := by
    intro rest heq
    cases el <;> first | exact False.elim hel | simp [ppMSLType] at heq
  have hrev (l : List Char) : (l ++ ['&']).reverse = '&' :: l.reverse := by simp
  have hnc : (match (ppMSLType el).toList ++ ['&'] with
      | 'c' :: 'o' :: 'n' :: 's' :: 't' :: ' ' :: rest => (true, rest)
      | chars => (false, chars)) = (false, (ppMSLType el).toList ++ ['&']) := by
    split
    · rename_i rest heq; exact False.elim (hnotconst rest heq)
    · rfl
  cases sp
  all_goals
    unfold parseMSLParamType
    rw [hscalar]
    simp only [ppMSLType, ppMSLAddressSpace, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    dsimp only [bind, Option.bind, pure]
    rw [hnc, hrev]
    simp [List.reverse_reverse, String.ofList_toList, hpel]

theorem parseMSLParamType_roundtrip (ty : MSLType) (h : CanonicalMSLType ty) :
    parseMSLParamType (ppMSLType ty) = some ty := by
  match ty with
  | .pointer sp c el => exact parseMSLParamType_pointer_roundtrip sp c el h.1 h.2
  | .ref sp el => exact parseMSLParamType_ref_roundtrip sp el h
  | .threadArr .. => exact False.elim h
  | .structTy .. => exact False.elim h
  | .void | .bool | .uchar | .ushort | .uint | .int | .ulong | .long
  | .half | .float | .double | .uint2 | .uint3 | .uint4 | .ulong2 | .atomicUint | .u256 =>
    unfold parseMSLParamType
    rw [parseMSLScalarType_roundtrip _ h]
    rfl

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

theorem takeWhile_mslName_append (xs rest : List Char)
    (hx : ∀ c ∈ xs, mslNameChar c = true)
    (hr : ∃ c cs, rest = c :: cs ∧ mslNameChar c = false) :
    (xs ++ rest).takeWhile mslNameChar = xs := by
  rw [List.takeWhile_append_of_pos hx]
  obtain ⟨c, cs, rfl, hc⟩ := hr
  simp [hc]

/-- A printed expression followed by an operator cannot be mistaken for a cast type. -/
theorem ppMSLExpr_not_cast_type (e : MSLExpr) (he : CanonicalMSLExpr e)
    (rest : List Char) :
    stripPrefixChars [')']
      (((ppMSLExpr e).toList ++ ' ' :: rest).drop
        (((ppMSLExpr e).toList ++ ' ' :: rest).takeWhile mslNameChar).length) = none := by
  cases e <;> simp_all only [CanonicalMSLExpr]
  all_goals try { simp [ppMSLExpr, toString, String.toList_append, List.append_assoc,
    mslNameChar, stripPrefixChars] }
  case var name =>
    have h := takeWhile_mslName_append name.toList (' ' :: rest) he.2.1 ⟨' ', rest, rfl, rfl⟩
    simp [ppMSLExpr, h, stripPrefixChars]
  case immU64 v =>
    have hchars : ∀ c ∈ v.toNat.repr.toList ++ ['U', 'L'], mslNameChar c = true := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact natRepr_mslNameChars _ c hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> decide
    have h := takeWhile_mslName_append _ (' ' :: rest) hchars ⟨' ', rest, rfl, rfl⟩
    simpa only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      ← List.append_assoc] using
      (show stripPrefixChars [')']
        ((v.toNat.repr.toList ++ ['U', 'L'] ++ ' ' :: rest).drop
          ((v.toNat.repr.toList ++ ['U', 'L'] ++ ' ' :: rest).takeWhile mslNameChar).length) = none by
        rw [h]; simp [stripPrefixChars])
  case immBool b => cases b <;> rfl
  case index name idx =>
    have h := takeWhile_mslName_append name.toList
      ('[' :: ((ppMSLExpr idx).toList ++ ']' :: ' ' :: rest)) he.1.2.1
      ⟨'[', _, rfl, rfl⟩
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [h]
    simp [stripPrefixChars]

theorem parseMSLExpr_paren_step (a : MSLExpr) (ha : CanonicalMSLExpr a)
    (input rest : List Char) (out : MSLExpr) (fuel : Nat)
    (pa : parseMSLExpr fuel ((ppMSLExpr a).toList ++ input) = some (a, input))
    (pt : parseMSLExprTail fuel a input = some (out, rest)) :
    parseMSLExpr (fuel + 1) ('(' :: ((ppMSLExpr a).toList ++ input)) =
      some (out, rest) := by
  cases a <;> simp_all only [CanonicalMSLExpr]
  all_goals try { exact False.elim ha }
  all_goals try {
    rename_i a b
    have hn := ppMSLExpr_not_cast_type a ha.1
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append] at pa ⊢
    rw [parseMSLExpr]
    simp only [hn]
    split <;> simp_all }
  case select a b c =>
    have hn := ppMSLExpr_not_cast_type a ha.1
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append] at pa ⊢
    rw [parseMSLExpr]
    simp only [hn]
    split <;> simp_all
  all_goals try {
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append] at pa ⊢
    simp [parseMSLExpr, pa, pt, mslNameChar, parseMSLScalarType, stripPrefixChars] }
  case var name =>
    simp only [ppMSLExpr] at pa ⊢
    obtain ⟨c, cs, he, hc⟩ := ha.1
    have hn : c ≠ '(' ∧ c ≠ '~' ∧ c ≠ '!' ∧ c ≠ '-' := by
      repeat' constructor
      all_goals intro h; subst c; contradiction
    rw [he] at pa ⊢
    simp [parseMSLExpr, hn, pa, pt, List.cons_append] at *
  case immU64 v =>
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append] at pa ⊢
    cases he : Nat.toDigits 10 v.toNat with
    | nil => exact False.elim (Nat.toDigits_ne_nil he)
    | cons c cs =>
      have hc := Nat.isDigit_of_mem_toDigits (b := 10) (n := v.toNat) (by omega) (by omega)
        (show c ∈ Nat.toDigits 10 v.toNat by simp [he])
      have hn : c ≠ '(' ∧ c ≠ '~' ∧ c ≠ '!' ∧ c ≠ '-' := by
        repeat' constructor
        all_goals intro h; subst c; contradiction
      simp only [Nat.toList_repr, he, List.cons_append] at pa ⊢
      simp [parseMSLExpr, hn, pa, pt]
  case immBool b =>
    cases b <;> simp only [ppMSLExpr, Bool.false_eq_true, ↓reduceIte,
      String.reduceToList, List.cons_append, List.nil_append] at pa ⊢
    all_goals simp [parseMSLExpr, pa, pt]
  case index name idx =>
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append] at pa ⊢
    obtain ⟨c, cs, he, hc⟩ := ha.1.1
    have hn : c ≠ '(' ∧ c ≠ '~' ∧ c ≠ '!' ∧ c ≠ '-' := by
      repeat' constructor
      all_goals intro h; subst c; contradiction
    rw [he] at pa ⊢
    simp [parseMSLExpr, hn, pa, pt, List.cons_append] at *

private theorem parseMSLExpr_binary_paren_step (opcode : String) (ctor : MSLExpr → MSLExpr → MSLExpr)
    (hop : mslBinary opcode = some ctor) (hspace : ∀ c ∈ opcode.toList, c ≠ ' ')
    (hquestion : ∀ cs, opcode.toList ≠ '?' :: cs)
    (a b : MSLExpr) (ha : CanonicalMSLExpr a) (rest : List Char) (fuel : Nat) (hf : 2 ≤ fuel)
    (pa : parseMSLExpr (fuel - 1)
      ((ppMSLExpr a).toList ++ (' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest)))) =
      some (a, ' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest))))
    (pb : parseMSLExpr (fuel - 2) ((ppMSLExpr b).toList ++ ')' :: rest) = some (b, ')' :: rest)) :
    parseMSLExpr fuel ((("(" ++ ppMSLExpr a ++ " " ++ opcode ++ " " ++ ppMSLExpr b ++ ")").toList) ++ rest) =
      some (ctor a b, rest) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
  have hpa : parseMSLExpr (f + 1)
      ((ppMSLExpr a).toList ++ (' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest)))) =
      some (a, ' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest))) := by
    simpa [Nat.add_sub_cancel] using pa
  have hpb : parseMSLExpr f ((ppMSLExpr b).toList ++ ')' :: rest) = some (b, ')' :: rest) := by
    simpa [Nat.add_sub_cancel] using pb
  have htail := parseMSLExprTail_binary_step opcode ctor hop hspace hquestion a b rest f hpb
  have hparen := parseMSLExpr_paren_step a ha
    (' ' :: (opcode.toList ++ ' ' :: ((ppMSLExpr b).toList ++ ')' :: rest)))
    rest (ctor a b) (f + 1) hpa htail
  simpa only [String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append] using hparen

set_option maxHeartbeats 1000000 in
theorem parseMSLExpr_roundtrip (e : MSLExpr) (he : CanonicalMSLExpr e)
    (rest : List Char) (hsuf : ValidMSLExprSuffix rest) (fuel : Nat)
    (hf : mslExprFuel e ≤ fuel) :
    parseMSLExpr fuel ((ppMSLExpr e).toList ++ rest) = some (e, rest) := by
  have hs_rparen : ∀ xs, ValidMSLExprSuffix (')' :: xs) := fun _ => Or.inl rfl
  have hs_comma : ∀ xs, ValidMSLExprSuffix (',' :: xs) := fun _ => Or.inr (Or.inl rfl)
  have hs_rbrack : ∀ xs, ValidMSLExprSuffix (']' :: xs) := fun _ => Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hs_space : ∀ xs, ValidMSLExprSuffix (' ' :: xs) := fun _ => Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  cases e
  case var name =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_var_roundtrip name he rest hsuf f (by simp [mslExprFuel] at hf; omega)
  case immU64 v =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_u64_roundtrip v rest hsuf f
      (by have hf' : v.toNat.repr.toList.length + 4 ≤ f + 1 := by simpa [mslExprFuel] using hf; omega)
  case immBool b =>
    exact parseMSLExpr_bool_suffix_roundtrip b rest hsuf fuel (by simp [mslExprFuel] at hf; omega)
  case bitNot a =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_bitNot_step a rest f
      (parseMSLExpr_roundtrip a he _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
  case logNot a =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_logNot_step a rest f
      (parseMSLExpr_roundtrip a he _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
  case neg a =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_neg_step a rest f
      (parseMSLExpr_roundtrip a he _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
  case cast ty a =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_cast_step ty a rest f he.1
      (parseMSLExpr_roundtrip a he.2 _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
  case clz a =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_clz_step a he rest f (by simp [mslExprFuel] at hf; omega)
      (parseMSLExpr_roundtrip a he _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
  case index name a =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslExprFuel] at hf; omega⟩
    exact parseMSLExpr_index_step name he.1 a rest f (by simp [mslExprFuel] at hf; omega)
      (parseMSLExpr_roundtrip a he.2 _ (hs_rbrack _) f (by simp [mslExprFuel] at hf; omega))
  case builtinSelect a b c =>
    have hgt : 7 < fuel := by simp [mslExprFuel] at hf; omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
    have hp := parseMSLExprArgs_three_step a b c he.1 he.2.1 he.2.2 rest f
      (parseMSLExpr_roundtrip a he.1 _ (hs_comma _) (f + 2) (by simp [mslExprFuel] at hf; omega))
      (parseMSLExpr_roundtrip b he.2.1 _ (hs_comma _) (f + 1) (by simp [mslExprFuel] at hf; omega))
      (parseMSLExpr_roundtrip c he.2.2 _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
    simpa [ppMSLExpr, toString, String.toList_append, List.append_assoc] using
      parseMSLExpr_builtin_step "select" (Or.inl rfl) a b c _ rest (f + 3) (by omega) hp
  case fma a b c =>
    have hgt : 7 < fuel := by simp [mslExprFuel] at hf; omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
    have hp := parseMSLExprArgs_three_step a b c he.1 he.2.1 he.2.2 rest f
      (parseMSLExpr_roundtrip a he.1 _ (hs_comma _) (f + 2) (by simp [mslExprFuel] at hf; omega))
      (parseMSLExpr_roundtrip b he.2.1 _ (hs_comma _) (f + 1) (by simp [mslExprFuel] at hf; omega))
      (parseMSLExpr_roundtrip c he.2.2 _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega))
    simpa [ppMSLExpr, toString, String.toList_append, List.append_assoc] using
      parseMSLExpr_builtin_step "fma" (Or.inr rfl) a b c _ rest (f + 3) (by omega) hp
  case select a b c =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by simp [mslExprFuel] at hf; omega⟩
    simp only [ppMSLExpr, toString, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    exact parseMSLExpr_paren_step a he.1 _ rest _ (f + 1)
      (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (f + 1) (by simp [mslExprFuel] at hf; omega))
      (parseMSLExprTail_select_step a b c rest f
        (parseMSLExpr_roundtrip b he.2.1 _ (hs_space _) f (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip c he.2.2 _ (hs_rparen _) f (by simp [mslExprFuel] at hf; omega)))
  case add a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "+" .add rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case sub a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "-" .sub rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case mul a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "*" .mul rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case div a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "/" .div rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case rem a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "%" .rem rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case bitAnd a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "&" .bitAnd rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case bitOr a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "|" .bitOr rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case bitXor a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "^" .bitXor rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case shl a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "<<" .shl rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case shr a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step ">>" .shr rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case logAnd a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "&&" .logAnd rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case logOr a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "||" .logOr rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case eq a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "==" .eq rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case ne a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "!=" .ne rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case lt a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "<" .lt rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case le a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step "<=" .le rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case gt a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step ">" .gt rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  case ge a b =>
    simpa [ppMSLExpr, toString, String.append_assoc] using
      parseMSLExpr_binary_paren_step ">=" .ge rfl (by decide) (by intro _ h; cases h)
        a b he.1 rest fuel (by simp [mslExprFuel] at hf; omega)
        (parseMSLExpr_roundtrip a he.1 _ (hs_space _) (fuel - 1) (by simp [mslExprFuel] at hf; omega))
        (parseMSLExpr_roundtrip b he.2 _ (hs_rparen _) (fuel - 2) (by simp [mslExprFuel] at hf; omega))
  all_goals exact False.elim he
termination_by sizeOf e

theorem ppMSLExpr_injective_on_canonical (a b : MSLExpr)
    (ha : CanonicalMSLExpr a) (hb : CanonicalMSLExpr b) (h : ppMSLExpr a = ppMSLExpr b) :
    a = b := by
  have pa := parseMSLExpr_roundtrip a ha [] trivial (max (mslExprFuel a) (mslExprFuel b)) (Nat.le_max_left ..)
  have pb := parseMSLExpr_roundtrip b hb [] trivial (max (mslExprFuel a) (mslExprFuel b)) (Nat.le_max_right ..)
  rw [h, pb] at pa
  exact (congrArg Prod.fst (Option.some.inj pa)).symm

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

theorem scanMSLToken_of_not_mem (delimiter : Char) (token : List Char)
    (h : delimiter ∉ token) : scanMSLToken delimiter token = (token, []) := by
  induction token with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ delimiter := fun he => h (by simp [he])
    have hs : delimiter ∉ cs := fun hm => h (by simp [hm])
    simp [scanMSLToken, hc, ih hs]

theorem canonicalMSLName_no_space (name : String) (h : CanonicalMSLName name) :
    ' ' ∉ name.toList := by
  intro hm
  have := h.2.1 ' ' hm
  contradiction

theorem parseMSLParamDeclChars_roundtrip (ty : MSLType) (name : String)
    (ht : CanonicalMSLType ty) (hn : CanonicalMSLName name) (attr : Option MSLAttr) :
    parseMSLParamDeclChars ((ppMSLType ty).toList ++ ' ' :: name.toList) attr =
      some { name, ty, attr } := by
  have hspace : ' ' ∉ name.toList.reverse := by
    simpa using canonicalMSLName_no_space name hn
  have hscan := scanMSLToken_append ' ' name.toList.reverse (ppMSLType ty).toList.reverse hspace
  have hne : name.toList.reverse.isEmpty = false := by
    obtain ⟨c, cs, he, _⟩ := hn.1
    simp [he]
  have hall : name.toList.reverse.all mslNameChar = true := by
    simpa using List.all_eq_true.mpr hn.2.1
  simp [parseMSLParamDeclChars, List.reverse_append, hscan, hne, hall,
    parseMSLParamType_roundtrip ty ht]

theorem canonicalMSLType_no_openBracket (ty : MSLType) (h : CanonicalMSLType ty) :
    '[' ∉ (ppMSLType ty).toList := by
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

theorem parseMSLParam_roundtrip (p : MSLParamDecl)
    (ht : CanonicalMSLType p.ty) (hn : CanonicalMSLName p.name) (fuel : Nat) :
    parseMSLParam (fuel + 1) (ppMSLParam p) = some p := by
  obtain ⟨ty, name, attr⟩ := p
  have hname : '[' ∉ name.toList := by
    intro hm
    have := hn.2.1 '[' hm
    contradiction
  have hdecl : '[' ∉ (ppMSLType ty).toList ++ ' ' :: name.toList := by
    simp [canonicalMSLType_no_openBracket ty ht, hname]
  have hpp : ppMSLParam { name, ty, attr } =
      match attr with
      | none => ppMSLType ty ++ " " ++ name
      | some a => "    " ++ ppMSLType ty ++ " " ++ name ++ " [[" ++ ppMSLAttr a ++ "]]" := by
    cases ty <;> cases attr <;> first | rfl | contradiction
  rw [hpp]
  cases attr with
  | none =>
    simp only [parseMSLParam, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [scanMSLToken_of_not_mem _ _ hdecl]
    exact parseMSLParamDeclChars_roundtrip ty name ht hn none
  | some a =>
    have hpre : '[' ∉ "    ".toList ++ (ppMSLType ty).toList ++ ' ' :: name.toList ++ [' '] := by
      simp [canonicalMSLType_no_openBracket ty ht, hname]
    have hs := scanMSLToken_append '[' _ ('[' :: ((ppMSLAttr a).toList ++ [']', ']'])) hpre
    simp only [parseMSLParam, String.toList_append, String.reduceToList,
      List.append_assoc, List.cons_append, List.nil_append] at hs ⊢
    rw [hs]
    simpa [List.reverse_append, stripPrefixChars, parseMSLAttr_roundtrip,
      List.append_assoc] using parseMSLParamDeclChars_roundtrip ty name ht hn (some a)

theorem ppMSLParam_injective_on_canonical (a b : MSLParamDecl)
    (ha : CanonicalMSLType a.ty ∧ CanonicalMSLName a.name)
    (hb : CanonicalMSLType b.ty ∧ CanonicalMSLName b.name)
    (h : ppMSLParam a = ppMSLParam b) : a = b := by
  have hp := congrArg (parseMSLParam 1) h
  simpa only [parseMSLParam_roundtrip a ha.1 ha.2 0,
    parseMSLParam_roundtrip b hb.1 hb.2 0, Option.some.injEq] using hp

theorem parseMSLStmt_returnVal_step (e : MSLExpr) (indent : String)
    (rest : List Char) (fuel : Nat)
    (hp : parseMSLExpr fuel ((ppMSLExpr e).toList ++ ';' :: rest) = some (e, ';' :: rest)) :
    parseMSLStmt (fuel + 1) indent ((ppMSLStmt indent (.returnVal e)).toList ++ rest) =
      some (.returnVal e, rest) := by
  simp only [ppMSLStmt, String.toList_append, List.append_assoc]
  simp [parseMSLStmt, stripPrefixChars_append, parseMSLSimpleStmt,
    stripPrefixChars, hp]

theorem parseMSLStmt_barrier_step (indent : String) (rest : List Char) (fuel : Nat) :
    parseMSLStmt (fuel + 1) indent ((ppMSLStmt indent .threadgroupBarrier).toList ++ rest) =
      some (.threadgroupBarrier, rest) := by
  simp only [ppMSLStmt, String.toList_append, List.append_assoc]
  simp [parseMSLStmt, stripPrefixChars_append, parseMSLSimpleStmt, stripPrefixChars]

theorem parseMSLStmt_return_step (indent : String) (rest : List Char) (fuel : Nat) :
    parseMSLStmt (fuel + 1) indent ((ppMSLStmt indent .returnStmt).toList ++ rest) =
      some (.returnStmt, rest) := by
  simp only [ppMSLStmt, String.toList_append, List.append_assoc]
  simp [parseMSLStmt, stripPrefixChars_append, parseMSLSimpleStmt, stripPrefixChars]

theorem parseMSLBlock_nil_step (indent : String) (rest : List Char) (fuel : Nat)
    (hr : stripPrefixChars indent.toList rest = none) :
    parseMSLBlock (fuel + 1) indent rest = some (.nil, rest) := by
  simp [parseMSLBlock, hr]

theorem parseMSLBlock_singleton_step (stmt : MSLStmt) (indent : String)
    (input rest : List Char) (fuel : Nat)
    (hi : (stripPrefixChars indent.toList input).isSome = true)
    (hp : parseMSLStmt fuel indent input = some (stmt, '\n' :: rest))
    (hr : stripPrefixChars indent.toList rest = none) :
    parseMSLBlock (fuel + 1) indent input = some (.cons stmt .nil, '\n' :: rest) := by
  simp [parseMSLBlock, hi, hp, hr]

theorem parseMSLBlock_cons_step (stmt : MSLStmt) (body : MSLBlock) (indent : String)
    (input next rest : List Char) (fuel : Nat)
    (hi : (stripPrefixChars indent.toList input).isSome = true)
    (hn : (stripPrefixChars indent.toList next).isSome = true)
    (hp : parseMSLStmt fuel indent input = some (stmt, '\n' :: next))
    (hb : parseMSLBlock fuel indent next = some (body, rest)) :
    parseMSLBlock (fuel + 1) indent input = some (.cons stmt body, rest) := by
  simp [parseMSLBlock, hi, hn, hp, hb]

theorem parseMSLStmt_ifElse_step (cond : MSLExpr) (yes no : MSLBlock)
    (indent : String) (condInput yesInput noInput rest : List Char) (fuel : Nat)
    (hc : parseMSLExpr fuel condInput = some (cond, ") {\n".toList ++ yesInput))
    (hy : parseMSLBlock fuel (indent ++ "    ") yesInput =
      some (yes, ("\n" ++ indent ++ "} else {\n").toList ++ noInput))
    (hn : parseMSLBlock fuel (indent ++ "    ") noInput =
      some (no, ("\n" ++ indent ++ "}").toList ++ rest)) :
    parseMSLStmt (fuel + 1) indent (indent.toList ++ "if (".toList ++ condInput) =
      some (.ifElse cond yes no, rest) := by
  have hy' : parseMSLBlock fuel (indent ++ "    ") yesInput =
      some (yes, ("\n" ++ indent ++ "}").toList ++ " else {\n".toList ++ noInput) := by
    simpa [String.toList_append, List.append_assoc] using hy
  have hs (pre : String) (xs : List Char) := stripPrefixChars_append pre.toList xs
  simp only [String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append] at hc hy' hn hs
  simp [parseMSLStmt, List.append_assoc, stripPrefixChars, hc, hy', hs]
  have hs' (xs : List Char) : stripPrefixChars (indent.toList ++ ['}'])
      (indent.toList ++ '}' :: xs) = some xs := by
    simpa [List.append_assoc] using stripPrefixChars_append (indent.toList ++ ['}']) xs
  simp [hs', stripPrefixChars, hn]

theorem parseMSLStmt_ifThen_step (cond : MSLExpr) (yes : MSLBlock)
    (indent : String) (condInput yesInput rest : List Char) (fuel : Nat)
    (hc : parseMSLExpr fuel condInput = some (cond, ") {\n".toList ++ yesInput))
    (hy : parseMSLBlock fuel (indent ++ "    ") yesInput =
      some (yes, ("\n" ++ indent ++ "}").toList ++ rest))
    (hr : stripPrefixChars " else {\n".toList rest = none) :
    parseMSLStmt (fuel + 1) indent (indent.toList ++ "if (".toList ++ condInput) =
      some (.ifElse cond yes .nil, rest) := by
  have hs' (xs : List Char) : stripPrefixChars (indent.toList ++ ['}'])
      (indent.toList ++ '}' :: xs) = some xs := by
    simpa [List.append_assoc] using stripPrefixChars_append (indent.toList ++ ['}']) xs
  simp only [String.toList_append, String.reduceToList, List.append_assoc,
    List.cons_append, List.nil_append] at hc hy hr
  simp [parseMSLStmt, List.append_assoc, stripPrefixChars_append,
    stripPrefixChars, hc, hy, hs', hr]

/-- A keyword followed by a non-name character cannot prefix a different name. -/
theorem stripPrefixChars_keyword_none (keyword name : List Char) (delimiter : Char)
    (tail rest : List Char) (hk : ∀ c ∈ keyword, mslNameChar c = true)
    (hn : ∀ c ∈ name, mslNameChar c = true) (hd : mslNameChar delimiter = false)
    (hne : keyword ≠ name) (hr : rest = [] ∨ ∃ c cs, rest = c :: cs ∧ mslNameChar c = false) :
    stripPrefixChars (keyword ++ delimiter :: tail) (name ++ rest) = none := by
  induction keyword generalizing name with
  | nil =>
    cases name with
    | nil => exact False.elim (hne rfl)
    | cons c cs =>
      have hc : delimiter ≠ c := by intro he; subst c; have hh := hn delimiter (by simp); rw [hd] at hh; contradiction
      simp [stripPrefixChars, hc]
  | cons k ks ih =>
    cases name with
    | nil =>
      rcases hr with rfl | ⟨c, cs, rfl, hc⟩
      · rfl
      · have hkc : k ≠ c := by intro he; subst k; have hh := hk c (by simp); rw [hc] at hh; contradiction
        simp [stripPrefixChars, hkc]
    | cons c cs =>
      by_cases he : k = c
      · subst c
        simp only [List.cons_append, stripPrefixChars, beq_self_eq_true, ↓reduceIte]
        exact ih cs (by intro c hc; exact hk c (by simp [hc]))
          (by intro c hc; exact hn c (by simp [hc]))
          (by intro he; exact hne (by rw [he]))
      · simp [stripPrefixChars, he]

theorem parseMSLSimpleStmt_assign_step (name : String) (hn : CanonicalMSLBindingName name)
    (rhs : MSLExpr) (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel)
    (hp : parseMSLExpr fuel ((ppMSLExpr rhs).toList ++ ';' :: rest) = some (rhs, ';' :: rest)) :
    parseMSLSimpleStmt fuel (name.toList ++ " = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) =
      some (.assign name rhs, rest) := by
  have hret : "return".toList ≠ name.toList := by
    intro he
    exact hn.2.2.1 (by simpa using congrArg String.ofList he.symm)
  have hbar : "threadgroup_barrier".toList ≠ name.toList := by
    intro he
    exact hn.2.2.2 (by simpa using congrArg String.ofList he.symm)
  have h1 := stripPrefixChars_keyword_none "return".toList name.toList ';' []
    (" = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) (by decide) hn.1.2.1 rfl hret
    (Or.inr ⟨' ', _, rfl, rfl⟩)
  have h2 := stripPrefixChars_keyword_none "return".toList name.toList ' ' []
    (" = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) (by decide) hn.1.2.1 rfl hret
    (Or.inr ⟨' ', _, rfl, rfl⟩)
  have h3 := stripPrefixChars_keyword_none "threadgroup_barrier".toList name.toList '('
    "mem_flags::mem_threadgroup);".toList
    (" = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) (by decide) hn.1.2.1 rfl hbar
    (Or.inr ⟨' ', _, rfl, rfl⟩)
  have hs := scanMSLName_append name.toList
    (" = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) fuel hn.1.2.1
    (Or.inr ⟨' ', _, rfl, rfl⟩) hf
  have hne : name.toList.isEmpty = false := by obtain ⟨c, cs, he, _⟩ := hn.1.1; simp [he]
  have hname : name ≠ "" := by intro he; simp [he] at hne
  simp only [String.reduceToList, List.cons_append, List.nil_append] at h1 h2 h3 hs
  simp only [parseMSLSimpleStmt, List.append_assoc, String.reduceToList,
    List.cons_append, List.nil_append, h1, h2, h3, hs]
  simp [hn.2.1, stripPrefixChars, hp, hname]

theorem parseMSLStmt_assign_step (name : String) (hn : CanonicalMSLBindingName name)
    (rhs : MSLExpr) (indent : String) (rest : List Char) (fuel : Nat)
    (hf : name.toList.length < fuel)
    (hp : parseMSLExpr fuel ((ppMSLExpr rhs).toList ++ ';' :: rest) = some (rhs, ';' :: rest)) :
    parseMSLStmt (fuel + 1) indent ((ppMSLStmt indent (.assign name rhs)).toList ++ rest) =
      some (.assign name rhs, rest) := by
  have hif : stripPrefixChars "if (".toList
      (name.toList ++ " = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) = none := by
    by_cases he : name = "if"
    · simp [he, stripPrefixChars]
    · have hne : "if".toList ≠ name.toList := by
        intro h; exact he (by simpa using congrArg String.ofList h.symm)
      simpa only [List.append_assoc, String.reduceToList, List.cons_append, List.nil_append] using stripPrefixChars_keyword_none "if".toList name.toList ' ' ['(']
        (" = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) (by decide) hn.1.2.1 rfl hne
        (Or.inr ⟨' ', _, rfl, rfl⟩)
  have hp' := parseMSLSimpleStmt_assign_step name hn rhs rest fuel hf hp
  simp only [List.append_assoc, String.reduceToList, List.cons_append, List.nil_append] at hif hp'
  simp only [ppMSLStmt, String.toList_append, List.append_assoc, parseMSLStmt,
    stripPrefixChars_append]
  simp [hif, hp']

theorem parseMSLSimpleStmt_indexAssign_step (name : String) (hn : CanonicalMSLBindingName name)
    (idx rhs : MSLExpr) (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel)
    (pi : parseMSLExpr fuel ((ppMSLExpr idx).toList ++ "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) =
      some (idx, "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest))
    (pr : parseMSLExpr fuel ((ppMSLExpr rhs).toList ++ ';' :: rest) = some (rhs, ';' :: rest)) :
    parseMSLSimpleStmt fuel (name.toList ++ '[' :: ((ppMSLExpr idx).toList ++
      "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest)) = some (.indexAssign name idx rhs, rest) := by
  have hret : "return".toList ≠ name.toList := by
    intro he; exact hn.2.2.1 (by simpa using congrArg String.ofList he.symm)
  have hbar : "threadgroup_barrier".toList ≠ name.toList := by
    intro he; exact hn.2.2.2 (by simpa using congrArg String.ofList he.symm)
  let input := '[' :: ((ppMSLExpr idx).toList ++ "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest)
  have hb : ∃ c cs, input = c :: cs ∧ mslNameChar c = false := ⟨'[', _, rfl, rfl⟩
  have h1 := stripPrefixChars_keyword_none "return".toList name.toList ';' [] input
    (by decide) hn.1.2.1 rfl hret (Or.inr hb)
  have h2 := stripPrefixChars_keyword_none "return".toList name.toList ' ' [] input
    (by decide) hn.1.2.1 rfl hret (Or.inr hb)
  have h3 := stripPrefixChars_keyword_none "threadgroup_barrier".toList name.toList '('
    "mem_flags::mem_threadgroup);".toList input (by decide) hn.1.2.1 rfl hbar (Or.inr hb)
  have hs := scanMSLName_append name.toList input fuel hn.1.2.1 (Or.inr hb) hf
  have hname : name ≠ "" := by
    obtain ⟨c, cs, he, _⟩ := hn.1.1
    intro h; simp [h] at he
  simp only [input, String.reduceToList, List.cons_append, List.nil_append, List.append_assoc] at h1 h2 h3 hs pi ⊢
  simp [parseMSLSimpleStmt, h1, h2, h3, hs, hname, hn.2.1, pi, pr, stripPrefixChars]

theorem parseMSLStmt_indexAssign_step (name : String) (hn : CanonicalMSLBindingName name)
    (idx rhs : MSLExpr) (indent : String) (rest : List Char) (fuel : Nat)
    (hf : name.toList.length < fuel)
    (pi : parseMSLExpr fuel ((ppMSLExpr idx).toList ++ "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) =
      some (idx, "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest))
    (pr : parseMSLExpr fuel ((ppMSLExpr rhs).toList ++ ';' :: rest) = some (rhs, ';' :: rest)) :
    parseMSLStmt (fuel + 1) indent ((ppMSLStmt indent (.indexAssign name idx rhs)).toList ++ rest) =
      some (.indexAssign name idx rhs, rest) := by
  let input := '[' :: ((ppMSLExpr idx).toList ++ "] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest)
  have hif : stripPrefixChars "if (".toList (name.toList ++ input) = none := by
    by_cases he : name = "if"
    · simp [he, input, stripPrefixChars]
    · have hne : "if".toList ≠ name.toList := by
        intro h; exact he (by simpa using congrArg String.ofList h.symm)
      simpa only [String.reduceToList, List.cons_append, List.nil_append] using
        stripPrefixChars_keyword_none "if".toList name.toList ' ' ['('] input
          (by decide) hn.1.2.1 rfl hne (Or.inr ⟨'[', _, rfl, rfl⟩)
  have hp := parseMSLSimpleStmt_indexAssign_step name hn idx rhs rest fuel hf pi pr
  simp only [input, List.append_assoc, String.reduceToList, List.cons_append, List.nil_append] at hif hp
  simp only [ppMSLStmt, String.toList_append, List.append_assoc, parseMSLStmt,
    stripPrefixChars_append]
  simp [hif, hp]

theorem parseMSLStmt_varDecl_step (ty : MSLType) (ht : CanonicalMSLValueType ty)
    (name : String) (hn : CanonicalMSLName name) (rhs : MSLExpr)
    (indent : String) (rest : List Char) (fuel : Nat)
    (hf : name.toList.length < fuel) (htf : (ppMSLType ty).toList.length < fuel)
    (hp : parseMSLExpr fuel ((ppMSLExpr rhs).toList ++ ';' :: rest) = some (rhs, ';' :: rest)) :
    parseMSLStmt (fuel + 1) indent ((ppMSLStmt indent (.varDecl ty name rhs)).toList ++ rest) =
      some (.varDecl ty name rhs, rest) := by
  have hchars : ∀ c ∈ (ppMSLType ty).toList, mslNameChar c = true := by
    cases ty <;> first | contradiction | decide
  have hscan := scanMSLName_append (ppMSLType ty).toList
    (' ' :: (name.toList ++ " = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest)) fuel
    hchars (Or.inr ⟨' ', _, rfl, rfl⟩) htf
  have hname := scanMSLName_append name.toList
    (" = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: rest) fuel hn.2.1
    (Or.inr ⟨' ', _, rfl, rfl⟩) hf
  have hne : name ≠ "" := by
    obtain ⟨c, cs, he, _⟩ := hn.1
    intro h; simp [h] at he
  simp only [String.reduceToList, List.cons_append, List.nil_append, List.append_assoc] at hscan hname
  cases ty <;> simp only [CanonicalMSLValueType] at ht
  all_goals try contradiction
  all_goals simp only [ppMSLType, String.reduceToList, List.cons_append, List.nil_append] at hscan
  all_goals simp only [ppMSLStmt, String.toList_append, List.append_assoc, parseMSLStmt,
    stripPrefixChars_append]
  all_goals simp [ppMSLType, stripPrefixChars, parseMSLSimpleStmt, hscan, hname,
    parseMSLScalarType, hne, hp]

theorem ppMSLStmt_indent_prefix (stmt : MSLStmt) (hs : CanonicalMSLStmt stmt)
    (indent : String) : ∃ text, ppMSLStmt indent stmt = indent ++ text := by
  cases stmt <;> simp only [CanonicalMSLStmt] at hs
  all_goals try contradiction
  all_goals simp only [ppMSLStmt, String.append_assoc]
  all_goals first | exact ⟨_, rfl⟩ | split <;> exact ⟨_, rfl⟩

theorem ppMSLStmt_strip_indent (stmt : MSLStmt) (hs : CanonicalMSLStmt stmt)
    (indent : String) (rest : List Char) :
    (stripPrefixChars indent.toList ((ppMSLStmt indent stmt).toList ++ rest)).isSome = true := by
  obtain ⟨text, he⟩ := ppMSLStmt_indent_prefix stmt hs indent
  simp [he, String.toList_append, List.append_assoc, stripPrefixChars_append]

theorem ppMSLBlock_nil (indent : String) : ppMSLBlock indent .nil = "" := rfl

theorem ppMSLBlock_singleton (indent : String) (stmt : MSLStmt) :
    ppMSLBlock indent (.cons stmt .nil) = ppMSLStmt indent stmt := by
  simp [ppMSLBlock, ppMSLBlockLines]

theorem ppMSLBlock_cons (indent : String) (stmt next : MSLStmt) (body : MSLBlock) :
    ppMSLBlock indent (.cons stmt (.cons next body)) =
      ppMSLStmt indent stmt ++ "\n" ++ ppMSLBlock indent (.cons next body) := by
  simp [ppMSLBlock, ppMSLBlockLines, String.intercalate_cons_cons]

theorem stripPrefixChars_append_cancel (pre a b : List Char) :
    stripPrefixChars (pre ++ a) (pre ++ b) = stripPrefixChars a b := by
  induction pre <;> simp_all [stripPrefixChars]

theorem stripPrefixChars_indent_close (indent : String) (rest : List Char) :
    stripPrefixChars (indent ++ "    ").toList (indent.toList ++ '}' :: rest) = none := by
  simp only [String.toList_append, stripPrefixChars_append_cancel]
  rfl

theorem stripPrefixChars_indent_newline (indent : String) (hi : ∃ cs, indent.toList = ' ' :: cs)
    (rest : List Char) : stripPrefixChars indent.toList ('\n' :: rest) = none := by
  obtain ⟨cs, he⟩ := hi
  simp [he, stripPrefixChars]

theorem indent_append_nonempty (indent : String) (hi : ∃ cs, indent.toList = ' ' :: cs) :
    ∃ cs, (indent ++ "    ").toList = ' ' :: cs := by
  obtain ⟨cs, he⟩ := hi
  exact ⟨cs ++ "    ".toList, by simp [String.toList_append, he]⟩

theorem ppMSLBlock_strip_indent (stmt : MSLStmt) (body : MSLBlock)
    (hs : CanonicalMSLStmt stmt) (indent : String) (rest : List Char) :
    (stripPrefixChars indent.toList ((ppMSLBlock indent (.cons stmt body)).toList ++ rest)).isSome = true := by
  cases body with
  | nil => simpa [ppMSLBlock_singleton] using ppMSLStmt_strip_indent stmt hs indent rest
  | cons next body =>
    rw [ppMSLBlock_cons]
    simpa only [String.toList_append, List.append_assoc] using
      ppMSLStmt_strip_indent stmt hs indent ("\n".toList ++ (ppMSLBlock indent (.cons next body)).toList ++ rest)

mutual
theorem parseMSLStmt_roundtrip (stmt : MSLStmt) (hs : CanonicalMSLStmt stmt)
    (indent : String) (hi : ∃ cs, indent.toList = ' ' :: cs)
    (rest : List Char) (fuel : Nat) (hf : mslStmtFuel stmt ≤ fuel) :
    parseMSLStmt fuel indent ((ppMSLStmt indent stmt).toList ++ '\n' :: rest) =
      some (stmt, '\n' :: rest) := by
  cases stmt <;> simp only [CanonicalMSLStmt, mslStmtFuel] at hs hf
  all_goals try contradiction
  all_goals obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  case varDecl ty name rhs =>
    exact parseMSLStmt_varDecl_step ty hs.1 name hs.2.1 rhs indent _ f (by omega) (by omega)
      (parseMSLExpr_roundtrip rhs hs.2.2 _ (by simp [ValidMSLExprSuffix]) f (by omega))
  case assign name rhs =>
    exact parseMSLStmt_assign_step name hs.1 rhs indent _ f (by omega)
      (parseMSLExpr_roundtrip rhs hs.2 _ (by simp [ValidMSLExprSuffix]) f (by omega))
  case indexAssign name idx rhs =>
    apply parseMSLStmt_indexAssign_step name hs.1 idx rhs indent _ f (by omega)
    · simpa only [List.append_assoc] using
        parseMSLExpr_roundtrip idx hs.2.1 ("] = ".toList ++ (ppMSLExpr rhs).toList ++ ';' :: '\n' :: rest)
          (by simp [ValidMSLExprSuffix]) f (by omega)
    · exact parseMSLExpr_roundtrip rhs hs.2.2 _ (by simp [ValidMSLExprSuffix]) f (by omega)
  case returnVal e =>
    exact parseMSLStmt_returnVal_step e indent _ f
      (parseMSLExpr_roundtrip e hs _ (by simp [ValidMSLExprSuffix]) f (by omega))
  case returnStmt => exact parseMSLStmt_return_step indent _ f
  case threadgroupBarrier => exact parseMSLStmt_barrier_step indent _ f
  case ifElse cond yes no =>
    have hi' := indent_append_nonempty indent hi
    have hclose (xs : List Char) := stripPrefixChars_indent_close indent xs
    cases no with
    | nil =>
      have hy := parseMSLBlock_roundtrip yes hs.2.1 (indent ++ "    ") hi'
        (indent.toList ++ '}' :: '\n' :: rest) (hclose _) f (by omega)
      have hc := parseMSLExpr_roundtrip cond hs.1
        (") {\n".toList ++ (ppMSLBlock (indent ++ "    ") yes).toList ++
          ("\n" ++ indent ++ "}").toList ++ '\n' :: rest)
        (by simp [ValidMSLExprSuffix]) f (by omega)
      have hp := parseMSLStmt_ifThen_step cond yes indent _ _ ('\n' :: rest) f
        (by simpa only [List.append_assoc] using hc)
        (by simpa [String.toList_append, List.append_assoc] using hy) rfl
      simpa [ppMSLStmt, MSLBlock.isEmpty, ppMSLBlock, String.toList_append, List.append_assoc] using hp
    | cons s ss =>
      have hn := parseMSLBlock_roundtrip (.cons s ss) hs.2.2 (indent ++ "    ") hi'
        (indent.toList ++ '}' :: '\n' :: rest) (hclose _) f (by omega)
      have hy := parseMSLBlock_roundtrip yes hs.2.1 (indent ++ "    ") hi'
        (indent.toList ++ "} else {\n".toList ++ (ppMSLBlock (indent ++ "    ") (.cons s ss)).toList ++
          ("\n" ++ indent ++ "}").toList ++ '\n' :: rest)
        (by simpa [List.append_assoc] using hclose (" else {\n".toList ++
          (ppMSLBlock (indent ++ "    ") (.cons s ss)).toList ++
          ("\n" ++ indent ++ "}").toList ++ '\n' :: rest)) f (by omega)
      have hc := parseMSLExpr_roundtrip cond hs.1
        (") {\n".toList ++ (ppMSLBlock (indent ++ "    ") yes).toList ++
          ("\n" ++ indent ++ "} else {\n").toList ++
          (ppMSLBlock (indent ++ "    ") (.cons s ss)).toList ++
          ("\n" ++ indent ++ "}").toList ++ '\n' :: rest)
        (by simp [ValidMSLExprSuffix]) f (by omega)
      have hp := parseMSLStmt_ifElse_step cond yes (.cons s ss) indent _ _ _ ('\n' :: rest) f
        (by simpa only [List.append_assoc] using hc)
        (by simpa [String.toList_append, List.append_assoc] using hy)
        (by simpa [String.toList_append, List.append_assoc] using hn)
      simpa [ppMSLStmt, MSLBlock.isEmpty, ppMSLBlock, String.toList_append, List.append_assoc] using hp
termination_by sizeOf stmt

theorem parseMSLBlock_roundtrip (body : MSLBlock) (hb : CanonicalMSLBlock body)
    (indent : String) (hi : ∃ cs, indent.toList = ' ' :: cs)
    (rest : List Char) (hr : stripPrefixChars indent.toList rest = none)
    (fuel : Nat) (hf : mslBlockFuel body ≤ fuel) :
    parseMSLBlock fuel indent ((ppMSLBlock indent body).toList ++ '\n' :: rest) =
      some (body, '\n' :: rest) := by
  cases body with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [mslBlockFuel] at hf; omega⟩
    simpa [ppMSLBlock_nil] using parseMSLBlock_nil_step indent ('\n' :: rest) f
      (stripPrefixChars_indent_newline indent hi rest)
  | cons stmt body =>
    simp only [CanonicalMSLBlock, mslBlockFuel] at hb hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases body with
    | nil =>
      rw [ppMSLBlock_singleton]
      exact parseMSLBlock_singleton_step stmt indent _ rest f
        (ppMSLStmt_strip_indent stmt hb.1 indent _)
        (parseMSLStmt_roundtrip stmt hb.1 indent hi rest f (by omega)) hr
    | cons next body =>
      rw [ppMSLBlock_cons]
      simp only [String.toList_append, String.reduceToList, List.append_assoc,
        List.cons_append, List.nil_append]
      apply parseMSLBlock_cons_step stmt (.cons next body) indent _
        ((ppMSLBlock indent (.cons next body)).toList ++ '\n' :: rest) ('\n' :: rest) f
      · exact ppMSLStmt_strip_indent stmt hb.1 indent _
      · exact ppMSLBlock_strip_indent next body hb.2.1 indent _
      · exact parseMSLStmt_roundtrip stmt hb.1 indent hi _ f (by omega)
      · exact parseMSLBlock_roundtrip (.cons next body) hb.2 indent hi rest hr f (by omega)
termination_by sizeOf body
end

theorem ppMSLStmt_injective_on_canonical (a b : MSLStmt)
    (ha : CanonicalMSLStmt a) (hb : CanonicalMSLStmt b)
    (indent : String) (hi : ∃ cs, indent.toList = ' ' :: cs)
    (h : ppMSLStmt indent a = ppMSLStmt indent b) : a = b := by
  have pa := parseMSLStmt_roundtrip a ha indent hi [] (max (mslStmtFuel a) (mslStmtFuel b)) (Nat.le_max_left ..)
  have pb := parseMSLStmt_roundtrip b hb indent hi [] (max (mslStmtFuel a) (mslStmtFuel b)) (Nat.le_max_right ..)
  rw [h, pb] at pa
  exact (congrArg Prod.fst (Option.some.inj pa)).symm

theorem ppMSLBlock_injective_on_canonical (a b : MSLBlock)
    (ha : CanonicalMSLBlock a) (hb : CanonicalMSLBlock b)
    (indent : String) (hi : ∃ cs, indent.toList = ' ' :: cs)
    (h : ppMSLBlock indent a = ppMSLBlock indent b) : a = b := by
  have hr : stripPrefixChars indent.toList [] = none := by obtain ⟨cs, he⟩ := hi; simp [he, stripPrefixChars]
  have pa := parseMSLBlock_roundtrip a ha indent hi [] hr (max (mslBlockFuel a) (mslBlockFuel b)) (Nat.le_max_left ..)
  have pb := parseMSLBlock_roundtrip b hb indent hi [] hr (max (mslBlockFuel a) (mslBlockFuel b)) (Nat.le_max_right ..)
  rw [h, pb] at pa
  exact (congrArg Prod.fst (Option.some.inj pa)).symm

theorem canonicalMSLParam_no_newline_comma (p : MSLParamDecl)
    (ht : CanonicalMSLType p.ty) (hn : CanonicalMSLName p.name) :
    '\n' ∉ (ppMSLParam p).toList ∧ ',' ∉ (ppMSLParam p).toList := by
  have hname (c : Char) (hc : mslNameChar c = false) : c ∉ p.name.toList := by
    intro hm; have hh := hn.2.1 c hm; rw [hc] at hh; contradiction
  have hty : '\n' ∉ (ppMSLType p.ty).toList ∧ ',' ∉ (ppMSLType p.ty).toList := by
    rcases p with ⟨ty, name, attr⟩
    change '\n' ∉ (ppMSLType ty).toList ∧ ',' ∉ (ppMSLType ty).toList
    cases ty with
    | pointer sp c el =>
      cases el <;> simp only [CanonicalMSLType, CanonicalMSLValueType, false_and] at ht
      all_goals try contradiction
      all_goals cases sp <;> cases c
      all_goals first | exact False.elim (Bool.noConfusion (ht.2 rfl)) | decide
    | ref sp el =>
      cases el <;> simp only [CanonicalMSLType, CanonicalMSLValueType] at ht
      all_goals try contradiction
      all_goals cases sp <;> decide
    | _ => first | contradiction | decide
  have hattr (a : MSLAttr) : '\n' ∉ (ppMSLAttr a).toList ∧ ',' ∉ (ppMSLAttr a).toList := by
    cases a with
    | buffer n =>
      have hd (c : Char) (hc : c.isDigit = false) : c ∉ n.repr.toList := by
        intro hm
        have hh := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
          (by simpa only [Nat.toList_repr] using hm)
        rw [hc] at hh; contradiction
      simp only [Nat.toList_repr] at hd
      simp [ppMSLAttr, toString, String.toList_append, hd '\n' rfl, hd ',' rfl]
    | _ => decide
  cases p with
  | mk ty name attr =>
    cases ty <;> first
      | contradiction
      | cases attr <;> simp_all [ppMSLParam, String.toList_append, hname '\n' rfl, hname ',' rfl]

theorem ppMSLParam_nonempty (p : MSLParamDecl) (ht : CanonicalMSLType p.ty)
    (hn : CanonicalMSLName p.name) : (ppMSLParam p).toList ≠ [] := by
  have hp := parseMSLParam_roundtrip p ht hn 0
  intro he
  have hs : ppMSLParam p = "" := by simpa using congrArg String.ofList he
  rw [hs] at hp
  contradiction

theorem parseMSLParams_roundtrip (ps : List MSLParamDecl)
    (hp : ∀ p ∈ ps, CanonicalMSLType p.ty ∧ CanonicalMSLName p.name)
    (rest : List Char) (fuel : Nat) (hf : ps.length + 1 ≤ fuel) :
    parseMSLParams fuel ((String.intercalate ",\n" (ps.map ppMSLParam)).toList ++ "\n) {\n".toList ++ rest) =
      some (ps, rest) := by
  induction ps generalizing fuel with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [parseMSLParams, scanMSLToken, stripPrefixChars]
  | cons p ps ih =>
    have hc := hp p (by simp)
    have hchars := canonicalMSLParam_no_newline_comma p hc.1 hc.2
    have hne := ppMSLParam_nonempty p hc.1 hc.2
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases ps with
    | nil =>
      have hs := scanMSLToken_append '\n' (ppMSLParam p).toList (')' :: ' ' :: '{' :: '\n' :: rest) hchars.1
      have hr : ∀ cs, (ppMSLParam p).toList.reverse ≠ ',' :: cs := by
        intro cs he
        have hm : ',' ∈ (ppMSLParam p).toList.reverse := by rw [he]; simp
        exact hchars.2 (List.mem_reverse.mp hm)
      simp only [List.map, String.intercalate_singleton, String.reduceToList,
        List.append_assoc, List.cons_append, List.nil_append]
      simp only [parseMSLParams, hs]
      simp only [List.isEmpty_eq_false_iff.mpr hne, Bool.false_eq_true, ↓reduceIte]
      simp [parseMSLParam_roundtrip p hc.1 hc.2, stripPrefixChars]
    | cons q qs =>
      have hs := scanMSLToken_append '\n' ((ppMSLParam p).toList ++ [','])
        ((String.intercalate ",\n" ((q :: qs).map ppMSLParam)).toList ++ "\n) {\n".toList ++ rest)
        (by simp [hchars.1])
      have hi := ih (by intro p hm; exact hp p (by simp [hm])) f (by simp at hf; simp; omega)
      simp only [List.map_cons, String.intercalate_cons_cons, String.toList_append,
        String.reduceToList, List.append_assoc, List.cons_append, List.nil_append] at hs hi ⊢
      simp only [parseMSLParams, hs]
      simp at hi
      simp [List.reverse_append, parseMSLParam_roundtrip p hc.1 hc.2, hi]

theorem canonicalMSLBlock_ofList (stmts : List MSLStmt)
    (hs : ∀ s ∈ stmts, CanonicalMSLStmt s) : CanonicalMSLBlock (MSLBlock.ofList stmts) := by
  induction stmts with
  | nil => trivial
  | cons s ss ih => exact ⟨hs s (by simp), ih (by intro x hx; exact hs x (by simp [hx]))⟩

theorem ppMSLBlockLines_ofList (stmts : List MSLStmt) (indent : String) :
    ppMSLBlockLines indent (MSLBlock.ofList stmts) = stmts.map (ppMSLStmt indent) := by
  induction stmts <;> simp_all [MSLBlock.ofList, ppMSLBlockLines]

theorem mslBlock_toList_ofList (stmts : List MSLStmt) : (MSLBlock.ofList stmts).toList = stmts := by
  induction stmts <;> simp_all [MSLBlock.ofList, MSLBlock.toList]

theorem parseMSLKernel_roundtrip (k : MSLKernelDecl) (hk : CanonicalMSLKernel k)
    (fuel : Nat) (hf : mslKernelFuel k ≤ fuel) : parseMSLKernel fuel (ppMSLKernel k) = some k := by
  obtain ⟨name, params, shared, body⟩ := k
  rcases hk with ⟨hname, hparams, rfl, hbody⟩
  simp only [mslKernelFuel] at hf
  have hs := scanMSLName_append name.toList
    ("(\n".toList ++ (String.intercalate ",\n" (params.map ppMSLParam)).toList ++ "\n) {\n".toList ++
      (String.intercalate "\n" (body.map (ppMSLStmt "    "))).toList ++ "\n}".toList)
    fuel hname.2.1 (Or.inr ⟨'(', _, rfl, rfl⟩) (by omega)
  have hp := parseMSLParams_roundtrip params hparams
    ((String.intercalate "\n" (body.map (ppMSLStmt "    "))).toList ++ "\n}".toList) fuel (by omega)
  have hb := parseMSLBlock_roundtrip (MSLBlock.ofList body) (canonicalMSLBlock_ofList body hbody)
    "    " ⟨_, rfl⟩ ['}'] rfl fuel (by omega)
  have hne : name ≠ "" := by obtain ⟨c, cs, he, _⟩ := hname.1; intro h; simp [h] at he
  simp only [ppMSLBlock, ppMSLBlockLines_ofList] at hb
  simp only [String.reduceToList, List.append_assoc, List.cons_append, List.nil_append] at hs hp
  simp only [parseMSLKernel, ppMSLKernel, ppMSLKernelSignaturePrefix, List.map_nil, List.nil_append,
    String.toList_append, List.append_assoc, stripPrefixChars_append]
  simp at hs hp hb
  simp [hs, hp, hb, hne, stripPrefixChars, mslBlock_toList_ofList]

theorem ppMSLKernel_injective_on_canonical (a b : MSLKernelDecl)
    (ha : CanonicalMSLKernel a) (hb : CanonicalMSLKernel b) (h : ppMSLKernel a = ppMSLKernel b) : a = b := by
  have pa := parseMSLKernel_roundtrip a ha (max (mslKernelFuel a) (mslKernelFuel b)) (Nat.le_max_left ..)
  have pb := parseMSLKernel_roundtrip b hb (max (mslKernelFuel a) (mslKernelFuel b)) (Nat.le_max_right ..)
  rw [h, pb] at pa
  exact (Option.some.inj pa).symm

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
