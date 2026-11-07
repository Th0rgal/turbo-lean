import LeanNative.Backend.StableHLOAst.Syntax
import LeanNative.Backend.StableHLOAst.Eval
import Std.Data.String.ToNat

namespace LeanNative.Backend.StableHLOAst

open LeanNative.IR

theorem stripPrefixChars_append (pre rest : List Char) :
    stripPrefixChars pre (pre ++ rest) = some rest := by
  induction pre <;> simp_all [stripPrefixChars]

theorem scanHLOFields_singleton_append (sep : Char) (field rest : List Char)
    (hn : sep ∉ field) (fuel : Nat) (hf : field.length < fuel) :
    scanHLOFields [sep] fuel (field ++ sep :: rest) =
      (scanHLOFields [sep] (fuel - field.length - 1) rest).map (fun fields => field :: fields) := by
  induction field generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [scanHLOFields, stripPrefixChars, List.nil_append, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, List.length_nil, Nat.sub_zero,
        Nat.add_sub_cancel]
      cases scanHLOFields [sep] f rest <;> rfl
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hc : sep ≠ c := by simp_all
      have ht : sep ∉ cs := by simp_all
      simp only [List.cons_append, scanHLOFields, List.isEmpty_cons, Bool.false_eq_true,
        ↓reduceIte, stripPrefixChars, beq_iff_eq, hc]
      rw [ih ht f (by simpa using hf)]
      cases h : scanHLOFields [sep] (f - cs.length - 1) rest <;>
        simp [List.length_cons, Nat.succ_sub_succ_eq_sub, h]

theorem scanHLOFields_singleton_last (sep : Char) (field : List Char)
    (hn : sep ∉ field) (fuel : Nat) (hf : field.length < fuel) :
    scanHLOFields [sep] fuel field = some [field] := by
  induction field generalizing fuel with
  | nil => cases fuel <;> simp_all [scanHLOFields]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hc : sep ≠ c := by simp_all
      have ht : sep ∉ cs := by simp_all
      simp [scanHLOFields, stripPrefixChars, hc, ih ht f (by simpa using hf)]

theorem scanHLOFields_intercalate (sep : Char) (fields : List (List Char))
    (hne : fields ≠ []) (hn : ∀ field ∈ fields, sep ∉ field)
    (fuel : Nat) (hf : (List.intercalate [sep] fields).length < fuel) :
    scanHLOFields [sep] fuel (List.intercalate [sep] fields) = some fields := by
  induction fields generalizing fuel with
  | nil => contradiction
  | cons field fields ih =>
    cases fields with
    | nil => simpa using scanHLOFields_singleton_last sep field (hn _ (by simp)) fuel (by simpa using hf)
    | cons next fields =>
      have he : List.intercalate [sep] (field :: next :: fields) =
          field ++ sep :: List.intercalate [sep] (next :: fields) := by
        simp [List.intercalate, List.intersperse]
      rw [he] at hf ⊢
      rw [scanHLOFields_singleton_append sep field _ (hn _ (by simp)) fuel (by simp at hf; omega)]
      rw [ih (by simp) (by intro x hx; exact hn x (by simp [hx])) _
        (by simp only [List.length_append, List.length_cons] at hf; omega)]
      rfl

theorem parseHLOFields_intercalate (sep : Char) (fields : List String)
    (hne : fields ≠ []) (hn : ∀ field ∈ fields, sep ∉ field.toList) :
    parseHLOFields (String.singleton sep) (String.intercalate (String.singleton sep) fields) =
      some fields := by
  unfold parseHLOFields
  have hs := scanHLOFields_intercalate sep (fields.map String.toList)
    (by simpa using hne) (by simpa using hn)
    ((List.intercalate [sep] (fields.map String.toList)).length + 1) (by omega)
  simpa [String.toList_intercalate, List.map_map] using congrArg
    (Option.map (List.map String.ofList)) hs

/-- Successful body parsing respects the printer's environment update at every step. -/
private theorem stripPrefixChars_ne_head (sep : List Char) (c : Char) (cs : List Char)
    (h : ∀ s ∈ sep.head?, s ≠ c) (hne : sep ≠ []) :
    stripPrefixChars sep (c :: cs) = none := by
  cases sep with
  | nil => contradiction
  | cons s ss => simp [stripPrefixChars, h s (by simp)]

/-- A delimiter-free prefix is accumulated without changing the remaining fields. -/
theorem scanHLOFields_prefix (sep pre rest : List Char) (fuel : Nat)
    (line : List Char) (lines : List (List Char)) (hne : sep ≠ [])
    (hn : ∀ a b, pre = a ++ b → b ≠ [] → stripPrefixChars sep (b ++ rest) = none)
    (hr : scanHLOFields sep fuel rest = some (line :: lines)) :
    scanHLOFields sep (pre.length + fuel) (pre ++ rest) = some ((pre ++ line) :: lines) := by
  induction pre with
  | nil => simpa using hr
  | cons c cs ih =>
    have ht : ∀ a b, cs = a ++ b → b ≠ [] → stripPrefixChars sep (b ++ rest) = none := by
      intro a b he hb
      exact hn (c :: a) b (by simp [he]) hb
    have hh := hn [] (c :: cs) rfl (by simp)
    simp only [List.cons_append] at hh
    have hs : sep.isEmpty = false := by cases sep <;> simp_all
    rw [List.length_cons, Nat.succ_add, List.cons_append, scanHLOFields]
    simp only [hs, Bool.false_eq_true, ↓reduceIte, hh, ih ht, bind, Option.bind, pure]
    rfl

/-- One delimiter is consumed before recursively scanning the suffix. -/
theorem scanHLOFields_delimiter (sep rest : List Char) (fuel : Nat) (hne : sep ≠ []) :
    scanHLOFields sep (fuel + 1) (sep ++ rest) =
      (scanHLOFields sep fuel rest).map ([] :: ·) := by
  cases sep with
  | nil => contradiction
  | cons c cs =>
    have hp := stripPrefixChars_append (c :: cs) rest
    simp only [List.cons_append] at hp
    simp only [List.cons_append, scanHLOFields, List.isEmpty_cons, Bool.false_eq_true,
      ↓reduceIte, hp]
    cases scanHLOFields (c :: cs) fuel rest <;> rfl

theorem parseBody_cons (tenv : TypeEnv) (line : String) (lines : List String)
    (op : StableHLOOp) (ops : List StableHLOOp)
    (hop : parseStableHLOOp tenv line = some op)
    (hrest : parseBody (bindResult tenv op) lines = some ops) :
    parseBody tenv (("    " ++ line) :: lines) = some (op :: ops) := by
  simp [parseBody, String.toList_append, hop, hrest]

/-- Multi-character separators split fields whose characters exclude the separator head. -/
theorem scanHLOFields_intercalate_head (c : Char) (sep : List Char)
    (fields : List (List Char)) (hne : fields ≠ [])
    (hn : ∀ field ∈ fields, c ∉ field) (fuel : Nat)
    (hf : (List.intercalate (c :: sep) fields).length < fuel) :
    scanHLOFields (c :: sep) fuel (List.intercalate (c :: sep) fields) = some fields := by
  have hprefix (pre rest : List Char) (hp : c ∉ pre) :
      ∀ a b, pre = a ++ b → b ≠ [] → stripPrefixChars (c :: sep) (b ++ rest) = none := by
    intro a b he hb
    cases b with
    | nil => contradiction
    | cons d ds =>
      have hd : c ≠ d := by intro hd; subst d; simp [he] at hp
      simp [stripPrefixChars, hd]
  have last (pre : List Char) (hp : c ∉ pre) (f : Nat) (h : pre.length < f) :
      scanHLOFields (c :: sep) f pre = some [pre] := by
    have hz : scanHLOFields (c :: sep) (f - pre.length) [] = some [[]] := by
      cases he : f - pre.length with
      | zero => omega
      | succ n => rfl
    have hs := scanHLOFields_prefix (c :: sep) pre [] (f - pre.length) [] []
      (by simp) (hprefix pre [] hp) hz
    simpa [Nat.add_sub_of_le (Nat.le_of_lt h)] using hs
  induction fields generalizing fuel with
  | nil => contradiction
  | cons field fields ih =>
    cases fields with
    | nil => simpa using last field (hn field (by simp)) fuel (by simpa using hf)
    | cons next fields =>
      have ht : (List.intercalate (c :: sep) (next :: fields)).length < fuel - field.length - 1 := by
        simp only [List.intercalate_cons_cons, List.length_append, List.length_cons] at hf
        omega
      have hs := ih (by simp) (by intro l hl; exact hn l (by simp [hl])) _ ht
      have hd := scanHLOFields_delimiter (c :: sep)
        (List.intercalate (c :: sep) (next :: fields)) (fuel - field.length - 1) (by simp)
      rw [hs] at hd
      have hp := scanHLOFields_prefix (c :: sep) field
        ((c :: sep) ++ List.intercalate (c :: sep) (next :: fields))
        (fuel - field.length - 1 + 1) [] (next :: fields) (by simp)
        (hprefix field _ (hn field (by simp))) hd
      have he : field.length + (fuel - field.length - 1 + 1) = fuel := by omega
      simpa [he, List.intercalate_cons_cons] using hp

theorem parseHLOFields_intercalate_head (c : Char) (sep : String) (fields : List String)
    (hne : fields ≠ []) (hn : ∀ field ∈ fields, c ∉ field.toList) :
    parseHLOFields (String.singleton c ++ sep)
      (String.intercalate (String.singleton c ++ sep) fields) = some fields := by
  unfold parseHLOFields
  have hs := scanHLOFields_intercalate_head c sep.toList (fields.map String.toList)
    (by simpa using hne) (by simpa using hn) _ (Nat.lt_succ_self _)
  simpa [String.toList_intercalate, String.toList_append, List.map_map] using
    congrArg (Option.map (List.map String.ofList)) hs

/-- Scanner composition across a delimiter-free chunk, preserving empty suffix fields. -/
theorem scanHLOFields_chunk (c : Char) (sep pre rest : List Char) (fuel : Nat)
    (hn : c ∉ pre) (hf : pre.length < fuel) :
    scanHLOFields (c :: sep) fuel (pre ++ rest) =
      (scanHLOFields (c :: sep) (fuel - pre.length) rest).bind
        (fun fields => match fields with
          | [] => none
          | line :: lines => some ((pre ++ line) :: lines)) := by
  induction pre generalizing fuel with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    cases hr : scanHLOFields (c :: sep) fuel rest with
    | none => rfl
    | some fields =>
      cases fields with
      | cons line lines => rfl
      | nil =>
        have nonempty : ∀ f xs, scanHLOFields (c :: sep) f xs ≠ some [] := by
          intro f
          induction f with
          | zero => simp [scanHLOFields]
          | succ f ih =>
            intro xs
            cases xs with
            | nil => simp [scanHLOFields]
            | cons x xs =>
              simp only [scanHLOFields, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
              split <;> simp only [bind, Option.bind, pure]
              · split <;> simp
              · split
                · simp
                · rename_i fields heq
                  cases fields <;> simp
        exact False.elim (nonempty fuel rest hr)
  | cons d ds ih =>
    have hd : c ≠ d := by simp_all
    have hs : c ∉ ds := by simp_all
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [List.cons_append, scanHLOFields, List.isEmpty_cons, Bool.false_eq_true,
        ↓reduceIte, stripPrefixChars, beq_iff_eq, hd]
      rw [ih fuel hs (by simpa using hf)]
      simp only [List.length_cons, Nat.succ_sub_succ_eq_sub]
      cases scanHLOFields (c :: sep) (fuel - ds.length) rest with
      | none => rfl
      | some fields => cases fields <;> rfl

/-- An identifier token recovers exactly its nonempty alphanumeric/underscore payload. -/
theorem parseSSAName_roundtrip (name : String) (hne : name.toList.isEmpty = false)
    (hchars : name.toList.all (fun c => c.isAlphanum || c == '_') = true) :
    parseSSAName ("%" ++ name) = some name := by
  simp [parseSSAName, String.toList_append, hne, hchars]

theorem CanonicalSSAName.parse_roundtrip (name : String) (h : CanonicalSSAName name) :
    parseSSAName ("%" ++ name) = some name :=
  parseSSAName_roundtrip name h.1 h.2

private theorem CanonicalSSAName.excludes (name : String) (h : CanonicalSSAName name)
    (c : Char) (hc : (c.isAlphanum || c == '_') = false) : c ∉ name.toList := by
  intro hm
  have := List.all_eq_true.mp h.2 c hm
  simp [hc] at this

private theorem tensorType_no_space (ty : TensorType) : ' ' ∉ (ppTensorType ty).toList := by
  have hn (n : Nat) : ' ' ∉ n.repr.toList := by
    intro h
    have := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using h)
    contradiction
  have he : ' ' ∉ (ppElemType ty.elem).toList := by cases ty.elem <;> decide
  have hi (ls : List String) (hh : ∀ s ∈ ls, ' ' ∉ s.toList) :
      ' ' ∉ (String.intercalate "x" ls).toList := by
    induction ls with
    | nil => simp
    | cons s ss ih =>
      cases ss with
      | nil => simpa using hh s (by simp)
      | cons t ts =>
        rw [String.intercalate_cons_cons]
        simp only [String.toList_append, List.mem_append, not_or]
        exact ⟨⟨hh s (by simp), by decide⟩,
          ih (by intro s hs; exact hh s (by simp [hs]))⟩
  cases ty with
  | mk shape elem =>
    cases shape with
    | nil => simpa [ppTensorType, toString, String.toList_append] using he
    | cons n ns =>
      have hs := hi ((n :: ns).map Nat.repr) (by
        intro s hs
        obtain ⟨m, _, rfl⟩ := List.mem_map.mp hs
        exact hn m)
      simpa [ppTensorType, ppShape, toString, String.toList_append, he] using hs

private theorem scanHLOFields_no_head (c : Char) (sep chars : List Char)
    (hn : c ∉ chars) (fuel : Nat) (hf : chars.length < fuel) :
    scanHLOFields (c :: sep) fuel chars = some [chars] := by
  have hs := scanHLOFields_intercalate_head c sep [chars] (by simp)
    (by simpa using hn) fuel (by simpa using hf)
  simpa using hs

private theorem parseHLOFields_no_head (c : Char) (sep text : String)
    (hn : c ∉ text.toList) :
    parseHLOFields (String.singleton c ++ sep) text = some [text] := by
  have hs := parseHLOFields_intercalate_head c sep [text] (by simp) (by simpa using hn)
  simpa using hs

private theorem scanHLOFields_return (sep : List Char) (name : String)
    (hn : ' ' ∉ name.toList) (fuel : Nat) (hf : name.toList.length + 8 < fuel) :
    scanHLOFields (' ' :: '=' :: sep) fuel ("return %".toList ++ name.toList) =
      some [("return %" ++ name).toList] := by
  have ht := scanHLOFields_no_head ' ' ('=' :: sep) name.toList hn (fuel - 8) (by omega)
  have hs := scanHLOFields_chunk ' ' ('=' :: sep) "return".toList
    (" %".toList ++ name.toList) fuel (by decide) (by simp at hf ⊢; omega)
  change scanHLOFields (' ' :: '=' :: sep) fuel ("return %".toList ++ name.toList) = _ at hs
  rw [hs]
  have he : fuel - "return".toList.length = (fuel - 8) + 2 := by simp at hf ⊢; omega
  rw [he]
  simp only [String.reduceToList, List.cons_append, List.nil_append, scanHLOFields,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, stripPrefixChars,
    Char.reduceBEq, ht, bind, Option.bind, pure]
  simp only [String.toList_append, String.reduceToList, List.cons_append, List.nil_append]

private theorem parseHLOFields_return (sep name : String) (hn : CanonicalSSAName name) :
    parseHLOFields (" =" ++ sep) ("return %" ++ name) = some ["return %" ++ name] := by
  have hs := scanHLOFields_return sep.toList name (hn.excludes _ ' ' rfl)
    (name.toList.length + 9) (by omega)
  unfold parseHLOFields
  have hf : ("return %" ++ name).toList.length + 1 = name.toList.length + 9 := by
    simp [String.toList_append]
  rw [hf]
  simp only [String.toList_append, String.reduceToList, List.cons_append, List.nil_append]
  change (scanHLOFields (' ' :: '=' :: sep.toList) (name.toList.length + 9)
    ("return %".toList ++ name.toList)).map _ = _
  rw [hs]
  simp only [Option.map_some, List.map_cons, List.map_nil, String.ofList_toList]

private theorem parseHLOFields_return_annotation (name : String) (ty : TensorType)
    (hn : CanonicalSSAName name) :
    parseHLOFields " : " ("return %" ++ name ++ " : " ++ ppTensorType ty) =
      some ["return %" ++ name, ppTensorType ty] := by
  have hn' := hn.excludes name ' ' rfl
  let rest := " : " ++ ppTensorType ty
  let fuel := name.toList.length + rest.toList.length + 1
  have ht := scanHLOFields_no_head ' ' [':', ' '] (ppTensorType ty).toList
    (tensorType_no_space ty) (rest.toList.length) (by
      simp [rest, String.toList_append]; omega)
  have hd := scanHLOFields_delimiter [' ', ':', ' '] (ppTensorType ty).toList
    rest.toList.length (by decide)
  rw [ht] at hd
  have hp := scanHLOFields_chunk ' ' [':', ' '] name.toList rest.toList fuel hn'
    (by dsimp [fuel]; omega)
  have hf : fuel - name.toList.length = rest.toList.length + 1 := by dsimp [fuel]; omega
  rw [hf] at hp
  have hr : rest.toList = [' ', ':', ' '] ++ (ppTensorType ty).toList := by
    simp [rest, String.toList_append]
  rw [← hr] at hd
  rw [hd] at hp
  have hs := scanHLOFields_chunk ' ' [':', ' '] "return".toList
    (" %".toList ++ name.toList ++ rest.toList) (fuel + 8) (by decide) (by simp)
  have he : fuel + 8 - "return".toList.length = fuel + 2 := by simp
  rw [he] at hs
  simp only [String.reduceToList, List.cons_append, List.nil_append, scanHLOFields,
    List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, stripPrefixChars,
    Char.reduceBEq] at hs
  change scanHLOFields [' ', ':', ' '] (fuel + 8)
    ("return".toList ++ (" %".toList ++ name.toList ++ rest.toList)) = _ at hs
  simp only [List.append_assoc] at hp hs
  rw [hp] at hs
  unfold parseHLOFields
  have hlen : ("return %" ++ name ++ " : " ++ ppTensorType ty).toList.length + 1 = fuel + 8 := by
    simp [fuel, rest, String.toList_append]
  rw [hlen]
  have hchars : ("return %" ++ name ++ " : " ++ ppTensorType ty).toList =
      "return".toList ++ (" %".toList ++ (name.toList ++ rest.toList)) := by
    simp [rest, String.toList_append, List.append_assoc]
  rw [hchars]
  change (scanHLOFields [' ', ':', ' '] (fuel + 8) _).map _ = _
  rw [hs]
  simp only [bind, Option.bind, pure, Option.map_some, List.map_cons, List.map_nil]
  simp only [String.ofList_toList, List.append_nil]
  congr 2
  apply String.ext_iff.mpr
  simp only [String.toList_ofList, String.toList_append, String.reduceToList,
    List.cons_append, List.nil_append]

theorem parseStableHLOOp_return_roundtrip (tenv : TypeEnv) (name : String)
    (hn : CanonicalSSAName name) (ht : (tenv name).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.returnOp name)) = some (.returnOp name) := by
  cases he : tenv name with
  | none => simp [he] at ht
  | some ty =>
    have hs := parseHLOFields_return_annotation name ty hn
    have hf := parseHLOFields_intercalate ' ' ["return", "%" ++ name] (by simp) (by
      intro s h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · decide
      · simp [String.toList_append, hn.excludes name ' ' rfl])
    change parseHLOFields " " ("return %" ++ name) = some ["return", "%" ++ name] at hf
    simp only [ppStableHLOOp, he, toString, parseStableHLOOp, hs, bind, Option.bind, pure]
    have hc := parseHLOFields_return " stablehlo.compare " name hn
    have hsel := parseHLOFields_return " stablehlo.select " name hn
    have hu := parseHLOFields_return " stablehlo." name hn
    have hd := parseHLOFields_return " stablehlo.dot_general " name hn
    have hk := parseHLOFields_return " stablehlo.constant dense<" name hn
    simp only [String.reduceAppend] at hc hsel hu hd hk
    simp only [hc, hsel, hu, hd, hk, hf, hn.parse_roundtrip name, he,
      beq_self_eq_true, ↓reduceIte]

private theorem nat_excludes (n : Nat) (c : Char) (hc : c.isDigit = false) :
    c ∉ n.repr.toList := by
  intro hm
  have := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
    (by simpa only [Nat.toList_repr] using hm)
  simp [hc] at this

theorem parseNatList_roundtrip (ns : List Nat) :
    parseNatList (ppNatList ns) = some ns := by
  have hs := parseHLOFields_intercalate_head ',' " " (ns.map Nat.repr)
  have hm : ∀ xs : List Nat, xs.mapM (String.toNat? ∘ Nat.repr) = some xs := by
    intro xs
    induction xs <;> simp_all [List.mapM_cons, Function.comp_def]
  cases ns with
  | nil => rfl
  | cons n ns =>
    have hp := hs (by simp) (by
      intro s hs
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hs
      exact nat_excludes n ',' rfl)
    simp only [String.singleton_eq_ofList, String.reduceOfList, String.reduceAppend] at hp
    unfold parseNatList ppNatList
    simp only [toString, String.toList_append, String.reduceToList,
      List.cons_append, List.nil_append, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.reverse_reverse]
    have hn : (String.intercalate ", " ((n :: ns).map Nat.repr)).toList.reverse.isEmpty = false := by
      have hne : (String.intercalate ", " ((n :: ns).map Nat.repr)).toList ≠ [] := by
        cases ns with
        | nil => simp [Nat.toList_repr, Nat.toDigits_ne_nil]
        | cons m ms =>
          simp [String.intercalate_cons_cons, String.toList_append]
      simpa using hne
    simp only [hn, Bool.false_eq_true, ↓reduceIte, String.ofList_toList, hp]
    simpa [List.mapM_map] using hm (n :: ns)

private theorem scanHLOFields_name (c : Char) (sep : List Char) (name : String)
    (hn : CanonicalSSAName name) (hc : (c.isAlphanum || c == '_') = false)
    (rest : List Char) (fuel : Nat) (hf : name.toList.length < fuel) :
    scanHLOFields (c :: sep) fuel (name.toList ++ rest) =
      (scanHLOFields (c :: sep) (fuel - name.toList.length) rest).bind
        (fun fields => match fields with
          | [] => none
          | line :: lines => some ((name.toList ++ line) :: lines)) :=
  scanHLOFields_chunk c sep name.toList rest fuel (hn.excludes name c hc) hf

private theorem scanHLOFields_type (c : Char) (sep : List Char) (ty : TensorType)
    (hc : c = ' ') (fuel : Nat) (hf : (ppTensorType ty).toList.length < fuel) :
    scanHLOFields (c :: sep) fuel (ppTensorType ty).toList =
      some [(ppTensorType ty).toList] := by
  subst c
  exact scanHLOFields_no_head ' ' sep _ (tensorType_no_space ty) fuel hf

private theorem parseStableHLOOp_ppTyped_binary (tenv : TypeEnv) (opName d a b : String)
    (op : StableHLOOp) (ty : TensorType)
    (hopName : (opName.toList.all fun c => c.isAlphanum || c == '_') = true)
    (hno_cmp : stripPrefixChars "compare ".toList (opName ++ " ").toList = none)
    (hno_sel : stripPrefixChars "select ".toList (opName ++ " ").toList = none)
    (hno_res : opName ≠ "reshape")
    (hno_cnv : opName ≠ "convert")
    (hno_slc : opName ≠ "slice")
    (hno_dot : stripPrefixChars "dot_general ".toList (opName ++ " ").toList = none)
    (hno_cst : stripPrefixChars "constant dense<".toList (opName ++ " ").toList = none)
    (hbin : parseBinaryOp ("stablehlo." ++ opName) d a b = some op)
    (hrt : resultTypeOf tenv op = some ty)
    (hd : CanonicalSSAName d) (ha : CanonicalSSAName a) (hb : CanonicalSSAName b) :
    parseStableHLOOp tenv (ppTyped d ("stablehlo." ++ opName ++ " %" ++ a ++ ", %" ++ b) (some ty)) =
      some op := by
  have hop_excl (c : Char) (hc : (c.isAlphanum || c == '_') = false) : c ∉ opName.toList := by
    intro hm; have := List.all_eq_true.mp hopName c hm; simp [hc] at this
  have hty_excl (c : Char) (hc : (c.isDigit || "tensor<>xiufb".toList.contains c) = false) :
      c ∉ (ppTensorType ty).toList := by
    have hn (n : Nat) : c ∉ n.repr.toList := by
      intro hm
      have hd0 := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
        (by simpa only [Nat.toList_repr] using hm)
      simp [hd0] at hc
    have hlit_all : ∀ d ∈ "tensor<>xiufbi186324".toList, (d.isDigit || "tensor<>xiufb".toList.contains d) = true := by
      decide
    have hlit : ∀ d ∈ "tensor<>xiufbi186324".toList, c ≠ d := by
      intro d hd heq
      subst heq
      have hmem := hlit_all c hd
      rw [hmem] at hc
      contradiction
    have hel : c ∉ (ppElemType ty.elem).toList := by
      intro hm
      have hsub : ∀ x ∈ (ppElemType ty.elem).toList, x ∈ "tensor<>xiufbi186324".toList := by
        cases ty.elem <;> decide
      exact hlit c (hsub c hm) rfl
    have hi (ls : List String) (hh : ∀ s ∈ ls, c ∉ s.toList) : c ∉ (String.intercalate "x" ls).toList := by
      induction ls with
      | nil => simp
      | cons s ss ih =>
        cases ss with
        | nil => simpa using hh s (by simp)
        | cons t ts =>
          rw [String.intercalate_cons_cons]
          simp only [String.toList_append, List.mem_append, not_or]
          refine ⟨⟨hh s (by simp), ?_⟩, ih (fun z hz => hh z (by simp [hz]))⟩
          intro hx
          simp only [String.reduceToList, List.mem_singleton] at hx
          exact hlit c (by subst hx; decide) rfl
    rcases ty with ⟨shape, elem⟩
    cases shape with
    | nil =>
      rw [show ppTensorType { shape := [], elem := elem } = "tensor<" ++ ppElemType elem ++ ">" from rfl]
      simp only [String.toList_append, List.mem_append, not_or]
      refine ⟨⟨?_, hel⟩, ?_⟩
      · intro hm
        exact hlit c ((show ∀ x ∈ "tensor<".toList, x ∈ "tensor<>xiufbi186324".toList by decide) c hm) rfl
      · intro hm
        exact hlit c ((show ∀ x ∈ ">".toList, x ∈ "tensor<>xiufbi186324".toList by decide) c hm) rfl
    | cons n ns =>
      have hs := hi ((n :: ns).map Nat.repr) (fun s hs => by obtain ⟨m, _, rfl⟩ := List.mem_map.mp hs; exact hn m)
      rw [show ppTensorType { shape := n :: ns, elem := elem } =
          "tensor<" ++ String.intercalate "x" ((n :: ns).map Nat.repr) ++ "x" ++ ppElemType elem ++ ">" by
        simp [ppTensorType, ppShape, toString, String.append_assoc]]
      simp only [String.toList_append, List.mem_append, not_or]
      refine ⟨⟨⟨⟨?_, hs⟩, ?_⟩, hel⟩, ?_⟩
      · intro hm
        exact hlit c ((show ∀ x ∈ "tensor<".toList, x ∈ "tensor<>xiufbi186324".toList by decide) c hm) rfl
      · intro hm
        exact hlit c ((show ∀ x ∈ "x".toList, x ∈ "tensor<>xiufbi186324".toList by decide) c hm) rfl
      · intro hm
        exact hlit c ((show ∀ x ∈ ">".toList, x ∈ "tensor<>xiufbi186324".toList by decide) c hm) rfl
  have hsingle (sep : List Char) (xs : List Char) (fuel : Nat) (hne : sep ≠ [])
      (c : Char) (hc : c ∈ sep) (hn : c ∉ xs) (hf : xs.length < fuel) :
      scanHLOFields sep fuel xs = some [xs] := by
    have hz : scanHLOFields sep (fuel - xs.length) [] = some [[]] := by
      cases hsub : fuel - xs.length with
      | zero => omega
      | succ k => rfl
    have hstrip_none : ∀ (s y : List Char), c ∈ s → c ∉ y → stripPrefixChars s y = none := by
      intro s
      induction s with
      | nil => intros _ h; simp at h
      | cons p ps ih =>
        intro y hcs hnin
        cases y with
        | nil => rfl
        | cons z zs =>
          simp only [stripPrefixChars]
          rcases List.mem_cons.mp hcs with rfl | hps
          · have hne_cz : (c == z) = false := beq_eq_false_iff_ne.mpr (fun heq => hnin (by simp [heq]))
            simp [hne_cz]
          · split
            · exact ih zs hps (fun hm => hnin (by simp [hm]))
            · rfl
    have hp := scanHLOFields_prefix sep xs [] (fuel - xs.length) [] [] hne
      (fun x y he _ => by
        rw [List.append_nil]
        exact hstrip_none sep y hc (fun hm => hn (by simp [he, hm]))) hz
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hf)] using hp
  let args := "%" ++ a ++ ", %" ++ b
  let suffix := opName ++ " " ++ args
  let operation := "%" ++ d ++ " = stablehlo." ++ suffix
  let annotation := ppTensorType ty
  have hpp : ppTyped d ("stablehlo." ++ opName ++ " %" ++ a ++ ", %" ++ b) (some ty) =
      operation ++ " : " ++ annotation := by
    apply String.ext_iff.mpr
    simp [ppTyped, operation, suffix, args, annotation, toString, String.toList_append]
  have hcolon_op : ':' ∉ operation.toList := by
    simp [operation, suffix, args, String.toList_append, hd.excludes d ':' rfl,
      hop_excl ':' rfl, ha.excludes a ':' rfl, hb.excludes b ':' rfl]
  have hcolon_ann : ':' ∉ annotation.toList := hty_excl ':' rfl
  have hsplit_ann : parseHLOFields " : " (operation ++ " : " ++ annotation) = some [operation, annotation] := by
    unfold parseHLOFields
    let sep := " : ".toList
    let rfuel := sep.length + annotation.toList.length
    have hr := hsingle sep annotation.toList rfuel (by decide) ':' (by decide) hcolon_ann (by dsimp [rfuel, sep]; omega)
    have hd_del : scanHLOFields sep (rfuel + 1) (sep ++ annotation.toList) = some [[], annotation.toList] := by
      rw [scanHLOFields_delimiter sep annotation.toList rfuel (by decide), hr]; rfl
    have hp := scanHLOFields_prefix sep operation.toList (sep ++ annotation.toList) (rfuel + 1)
      [] [annotation.toList] (by decide)
      (fun x y he hy => by
        cases y with
        | nil => contradiction
        | cons c0 cs =>
          cases cs with
          | nil =>
            simp only [sep, List.cons_append, List.nil_append, stripPrefixChars]
            split
            · decide
            · rfl
          | cons c1 cs' =>
            have hc1 : (':' == c1) = false := beq_eq_false_iff_ne.mpr (fun h => hcolon_op (by subst h; simp [he]))
            simp only [sep, List.cons_append, List.nil_append, stripPrefixChars]
            split
            · simp [hc1]
            · rfl) hd_del
    have hlen : (operation ++ " : " ++ annotation).toList.length + 1 = operation.toList.length + (rfuel + 1) := by
      simp [rfuel, sep, String.toList_append]; omega
    have hchars : (operation ++ " : " ++ annotation).toList = operation.toList ++ (sep ++ annotation.toList) := by
      simp [sep, String.toList_append, List.append_assoc]
    rw [hlen, hchars, hp]; simp
  have hdot_suf : '.' ∉ suffix.toList := by
    simp [suffix, args, String.toList_append, hop_excl '.' rfl, ha.excludes a '.' rfl, hb.excludes b '.' rfl]
  have hnonmatch (tag : String) (htag_sp : ' ' ∉ tag.toList.dropLast)
      (htag : stripPrefixChars tag.toList (opName ++ " ").toList = none) :
      parseHLOFields (" = stablehlo." ++ tag) operation = some [operation] := by
    let sep := (" = stablehlo." ++ tag).toList
    have hsep_eq : sep = ' ' :: '=' :: ' ' :: 's' :: 't' :: 'a' :: 'b' :: 'l' :: 'e' :: 'h' :: 'l' :: 'o' :: '.' :: tag.toList := by
      simp [sep, String.toList_append]
    have hsep_ne : sep ≠ [] := by simp [hsep_eq]
    have hafter := hsingle sep suffix.toList (suffix.toList.length + 1) hsep_ne '.' (by simp [hsep_eq]) hdot_suf (by omega)
    let mid := " = stablehlo.".toList
    have hno_suf : stripPrefixChars tag.toList suffix.toList = none := by
      have hsuf_eq : suffix.toList = (opName ++ " ").toList ++ args.toList := by
        simp [suffix, String.toList_append, List.append_assoc]
      rw [hsuf_eq]
      have haux : ∀ (t u v : List Char), stripPrefixChars t u = none → u.getLast? = some ' ' →
          ' ' ∉ t.dropLast → stripPrefixChars t (u ++ v) = none := by
        intro t
        induction t with
        | nil => intros _ _ h; simp [stripPrefixChars] at h
        | cons tc tcs ih =>
          intro u v hno hlast hsp
          cases u with
          | nil => simp at hlast
          | cons uc ucs =>
            cases ucs with
            | nil =>
              simp at hlast; subst uc
              cases tcs with
              | nil => simp [stripPrefixChars] at hno
              | cons tc2 tcs2 =>
                have hne : tc ≠ ' ' := fun h => by subst tc; simp [List.dropLast_cons_cons] at hsp
                simp [stripPrefixChars, hne]
            | cons uc2 ucs2 =>
              simp only [List.cons_append, stripPrefixChars] at hno ⊢
              split at hno
              · rename_i heq; simp only [heq, ↓reduceIte]
                cases tcs with
                | nil => simp [stripPrefixChars] at hno
                | cons tc2 tcs2 =>
                  exact ih (uc2 :: ucs2) v hno (by simpa using hlast)
                    (by intro hm; apply hsp; simp [List.dropLast_cons_cons, hm])
              · rename_i hne; simp [hne]
      exact haux tag.toList (opName ++ " ").toList args.toList htag
        (by simp [String.toList_append, List.getLast?_concat]) htag_sp
    have hmid : ∀ x y, mid = x ++ y → y ≠ [] → stripPrefixChars sep (y ++ suffix.toList) = none := by
      intro x y he hy
      cases x with
      | nil =>
        simp [List.nil_append] at he; subst he
        have hs2 : sep = mid ++ tag.toList := by simp [sep, mid, String.toList_append]
        have happ : ∀ (m t r : List Char), stripPrefixChars (m ++ t) (m ++ r) = stripPrefixChars t r := by
          intro m; induction m <;> simp_all [stripPrefixChars]
        rw [hs2, happ]; exact hno_suf
      | cons c0 xs =>
        have hm : mid = ' ' :: ['=', ' ', 's', 't', 'a', 'b', 'l', 'e', 'h', 'l', 'o', '.'] := by decide
        rw [hm, List.cons_append, List.cons.injEq] at he
        rcases he with ⟨_, he2⟩
        rcases xs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
        all_goals simp only [List.nil_append, List.cons_append, List.cons.injEq] at he2
        · subst he2; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩; rw [hsep_eq]; rfl
        · rcases he2 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hnil⟩
          simp at hnil; exact False.elim (hy hnil.2)
    have hmid_scan := scanHLOFields_prefix sep mid suffix.toList (suffix.toList.length + 1)
      suffix.toList [] hsep_ne hmid hafter
    let pre := ("%" ++ d).toList
    have hpre : ∀ x y, pre = x ++ y → y ≠ [] → stripPrefixChars sep (y ++ (mid ++ suffix.toList)) = none := by
      intro x y he hy
      cases y with
      | nil => contradiction
      | cons z zs =>
        have hnsp : ' ' ∉ pre := by simp [pre, String.toList_append, hd.excludes d ' ' rfl]
        have hz : ' ' ≠ z := fun h => hnsp (by subst h; simp [he])
        rw [hsep_eq]; simp [stripPrefixChars, hz]
    have hfull := scanHLOFields_prefix sep pre (mid ++ suffix.toList)
      (mid.length + (suffix.toList.length + 1)) (mid ++ suffix.toList) [] hsep_ne hpre hmid_scan
    unfold parseHLOFields
    have hlen : operation.toList.length + 1 = pre.length + (mid.length + (suffix.toList.length + 1)) := by
      simp [operation, pre, mid, String.toList_append]; omega
    have hchars : operation.toList = pre ++ (mid ++ suffix.toList) := by
      simp [operation, pre, mid, String.toList_append, List.append_assoc]
    rw [hlen, hchars]; change (scanHLOFields sep _ _).map _ = _; rw [hfull]
    simp only [Option.map_some, List.map_cons, List.map_nil]
    congr 2; apply String.ext_iff.mpr; simp [operation, pre, mid, String.toList_append, List.append_assoc]
  have hcmp := hnonmatch "compare " (by decide) hno_cmp
  have hsel := hnonmatch "select " (by decide) hno_sel
  have hdot := hnonmatch "dot_general " (by decide) hno_dot
  have hcst : parseHLOFields " = stablehlo.constant dense<" operation = some [operation] := by
    unfold parseHLOFields
    have hlt_op : '<' ∉ operation.toList := by
      simp [operation, suffix, args, String.toList_append, hd.excludes d '<' rfl,
        hop_excl '<' rfl, ha.excludes a '<' rfl, hb.excludes b '<' rfl]
    rw [hsingle (" = stablehlo.constant dense<".toList) operation.toList (operation.toList.length + 1)
      (by decide) '<' (by decide) hlt_op (by omega)]
    simp
  have hst : parseHLOFields " = stablehlo." operation = some ["%" ++ d, suffix] := by
    unfold parseHLOFields
    let sep := " = stablehlo.".toList
    let rfuel := sep.length + suffix.toList.length
    have hr := hsingle sep suffix.toList rfuel (by decide) '.' (by decide) hdot_suf (by dsimp [rfuel, sep]; omega)
    have hd_del : scanHLOFields sep (rfuel + 1) (sep ++ suffix.toList) = some [[], suffix.toList] := by
      rw [scanHLOFields_delimiter sep suffix.toList rfuel (by decide), hr]; rfl
    have hp := scanHLOFields_prefix sep ("%" ++ d).toList (sep ++ suffix.toList) (rfuel + 1)
      [] [suffix.toList] (by decide)
      (fun x y he hy => by
        cases y with
        | nil => contradiction
        | cons z zs =>
          have hnsp : ' ' ∉ ("%" ++ d).toList := by simp [String.toList_append, hd.excludes d ' ' rfl]
          have hz : ' ' ≠ z := fun h => hnsp (by subst h; simp [he])
          simp [sep, stripPrefixChars, hz]) hd_del
    have hlen : operation.toList.length + 1 = ("%" ++ d).toList.length + (rfuel + 1) := by
      simp [operation, rfuel, sep, String.toList_append]; omega
    have hchars : operation.toList = ("%" ++ d).toList ++ (sep ++ suffix.toList) := by
      simp [operation, sep, String.toList_append, List.append_assoc]
    rw [hlen, hchars, hp]; simp
  let payload := "stablehlo." ++ suffix
  have hdims : parseHLOFields ", dims = " payload = some [payload] := by
    unfold parseHLOFields
    have heq_pl : '=' ∉ payload.toList := by
      simp [payload, suffix, args, String.toList_append, hop_excl '=' rfl, ha.excludes a '=' rfl, hb.excludes b '=' rfl]
    rw [hsingle (", dims = ".toList) payload.toList (payload.toList.length + 1)
      (by decide) '=' (by decide) heq_pl (by omega)]
    simp
  have hsp_pl : parseHLOFields " " payload =
      some ["stablehlo." ++ opName, "%" ++ a ++ ",", "%" ++ b] := by
    have hp := parseHLOFields_intercalate ' ' ["stablehlo." ++ opName, "%" ++ a ++ ",", "%" ++ b] (by simp) (by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
      · simp [String.toList_append, hop_excl ' ' rfl]
      · simp [String.toList_append, ha.excludes a ' ' rfl]
      · simp [String.toList_append, hb.excludes b ' ' rfl])
    have heq : payload = String.intercalate " " ["stablehlo." ++ opName, "%" ++ a ++ ",", "%" ++ b] := by
      apply String.ext_iff.mpr; simp [payload, suffix, args, String.toList_append]
    rw [heq]; simpa using hp
  have hpct_pl : parseHLOFields " %" payload =
      some ["stablehlo." ++ opName, a ++ ",", b] := by
    have hp := parseHLOFields_intercalate_head ' ' "%" ["stablehlo." ++ opName, a ++ ",", b] (by simp) (by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
      · simp [String.toList_append, hop_excl ' ' rfl]
      · simp [String.toList_append, ha.excludes a ' ' rfl]
      · simp [String.toList_append, hb.excludes b ' ' rfl])
    have heq : payload = String.intercalate " %" ["stablehlo." ++ opName, a ++ ",", b] := by
      apply String.ext_iff.mpr; simp [payload, suffix, args, String.toList_append]
    rw [heq]; simpa using hp
  have hsp_op : parseHLOFields " " operation =
      some ["%" ++ d, "=", "stablehlo." ++ opName, "%" ++ a ++ ",", "%" ++ b] := by
    have hp := parseHLOFields_intercalate ' '
      ["%" ++ d, "=", "stablehlo." ++ opName, "%" ++ a ++ ",", "%" ++ b] (by simp) (by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl
      · simp [String.toList_append, hd.excludes d ' ' rfl]
      · decide
      · simp [String.toList_append, hop_excl ' ' rfl]
      · simp [String.toList_append, ha.excludes a ' ' rfl]
      · simp [String.toList_append, hb.excludes b ' ' rfl])
    have heq : operation = String.intercalate " "
        ["%" ++ d, "=", "stablehlo." ++ opName, "%" ++ a ++ ",", "%" ++ b] := by
      apply String.ext_iff.mpr; simp [operation, suffix, args, String.toList_append]
    rw [heq]; simpa using hp
  have hnot_ret : "%" ++ d ≠ "return" := by
    intro h
    have := congrArg String.toList h
    simp [String.toList_append] at this
  have hnot_res : "stablehlo." ++ opName ≠ "stablehlo.reshape" := by
    intro h; apply hno_res
    have := congrArg (fun s : String => String.ofList (s.toList.drop 10)) h
    simpa [String.toList_append, String.ofList_toList] using this
  have hnot_cnv : "stablehlo." ++ opName ≠ "stablehlo.convert" := by
    intro h; apply hno_cnv
    have := congrArg (fun s : String => String.ofList (s.toList.drop 10)) h
    simpa [String.toList_append, String.ofList_toList] using this
  have ha_last : ("%" ++ a ++ ",").toList.getLast? = some ',' := by
    simp [String.toList_append, List.append_assoc, List.getLast?_concat]
  have ha_take : String.ofList (("%" ++ a ++ ",").toList.take (("%" ++ a ++ ",").toList.length - 1)) = "%" ++ a := by
    have heq : ("%" ++ a ++ ",").toList = ("%" ++ a).toList ++ [','] := by
      simp [String.toList_append, List.append_assoc]
    rw [heq, List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left]
    exact String.ofList_toList _
  rw [hpp]
  unfold parseStableHLOOp
  simp only [hsplit_ann, hcmp, hsel, hst, hd.parse_roundtrip d, payload, hdims, hsp_pl, hpct_pl,
    hnot_res, hnot_cnv, hdot, hcst, hsp_op, hnot_ret, ha_last, ha_take,
    ha.parse_roundtrip a, hb.parse_roundtrip b, hbin, hrt, annotation,
    bind, Option.bind, pure, bne_self_eq_false, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

theorem parseStableHLOOp_binary_roundtrip (tenv : TypeEnv) (d a b : String)
    (op : StableHLOOp)
    (hop : op = .add d a b ∨ op = .subtract d a b ∨ op = .multiply d a b ∨
      op = .divide d a b ∨ op = .remainder d a b ∨ op = .maximum d a b ∨
      op = .minimum d a b ∨ op = .and d a b ∨ op = .or d a b ∨ op = .xor d a b ∨
      op = .shiftLeft d a b ∨ op = .shiftRightArithmetic d a b ∨ op = .shiftRightLogical d a b)
    (hd : CanonicalSSAName d) (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (ht : (resultTypeOf tenv op).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv op) = some op := by
  cases he : resultTypeOf tenv op with
  | none => simp [he] at ht
  | some ty =>
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "add" d a b (.add d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "subtract" d a b (.subtract d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "multiply" d a b (.multiply d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "divide" d a b (.divide d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "remainder" d a b (.remainder d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "maximum" d a b (.maximum d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "minimum" d a b (.minimum d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "and" d a b (.and d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "or" d a b (.or d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "xor" d a b (.xor d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "shift_left" d a b (.shiftLeft d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "shift_right_arithmetic" d a b (.shiftRightArithmetic d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb
    · simpa [ppStableHLOOp, he, toString, String.append_assoc] using
        parseStableHLOOp_ppTyped_binary tenv "shift_right_logical" d a b (.shiftRightLogical d a b) ty
          (by decide) rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl he hd ha hb

theorem parseStableHLOOp_add_roundtrip (tenv : TypeEnv) (d a b : String)
    (hd : CanonicalSSAName d) (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (ht : (resultTypeOf tenv (.add d a b)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.add d a b)) = some (.add d a b) :=
  parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inl rfl) hd ha hb ht

/-- Generated decimal suffixes preserve the SSA identifier alphabet. -/
theorem CanonicalSSAName.append_nat (pre : String) (h : CanonicalSSAName pre) (n : Nat) :
    CanonicalSSAName (pre ++ n.repr) := by
  have hd : n.repr.toList.all (fun c => c.isAlphanum || c == '_') = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have hc := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using hc)
    simp [Char.isAlphanum, hc]
  constructor
  · cases he : pre.toList with
    | nil => have := h.1; simp [he] at this
    | cons c cs => simp [String.toList_append, he]
  · rw [String.toList_append, List.all_append, h.2, hd]; rfl

/-- Canonicality is compositional with exactly the printer's SSA environment threading. -/
theorem CanonicalBody.append (tenv : TypeEnv) (xs ys : List StableHLOOp) :
    CanonicalBody tenv (xs ++ ys) ↔
      CanonicalBody tenv xs ∧ CanonicalBody (xs.foldl bindResult tenv) ys := by
  induction xs generalizing tenv with
  | nil => simp [CanonicalBody]
  | cons op ops ih => simp [CanonicalBody, ih, and_assoc]

/-- A closing tensor delimiter disambiguates `i1` from `i16`. -/
theorem parseElemType_roundtrip (ty : ElemType) (fuel : Nat) (rest : List Char) :
    parseElemType (fuel + 1) ((ppElemType ty).toList ++ '>' :: rest) =
      some (ty, '>' :: rest) := by
  cases ty <;> rfl

theorem ppElemType_injective_via_parser : Function.Injective ppElemType := by
  intro a b h
  have hp := congrArg (fun s : String => parseElemType 1 (s.toList ++ ['>'])) h
  simpa only [parseElemType_roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using hp

theorem parseElemType_complete (ty : ElemType) :
    parseElemType 1 (ppElemType ty).toList = some (ty, []) := by
  cases ty <;> rfl

theorem ppTensorType_fields (ty : TensorType) :
    ppTensorType ty = "tensor<" ++
      String.intercalate "x" (ty.shape.map Nat.repr ++ [ppElemType ty.elem]) ++ ">" := by
  cases ty with
  | mk shape elem =>
    cases shape with
    | nil => simp [ppTensorType, toString]
    | cons n ns =>
      rw [String.intercalate_append_of_ne_nil (by simp : (n :: ns).map Nat.repr ≠ [])
          (by simp : [ppElemType elem] ≠ [])]
      simp [ppTensorType, ppShape, toString, String.append_assoc]

theorem parseTensorType_roundtrip (ty : TensorType) :
    parseTensorType (ppTensorType ty) = some ty := by
  have hn (n : Nat) : 'x' ∉ n.repr.toList := by
    intro h
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using h)
    contradiction
  have he : 'x' ∉ (ppElemType ty.elem).toList := by cases ty.elem <;> decide
  have hs := parseHLOFields_intercalate 'x' (ty.shape.map Nat.repr ++ [ppElemType ty.elem])
    (by simp) (by
      intro field h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h; exact hn n
      · obtain rfl := List.mem_singleton.mp h; exact he)
  have hx : String.singleton 'x' = "x" := by decide
  rw [hx] at hs
  rw [ppTensorType_fields]
  simp only [parseTensorType, String.toList_append, String.reduceToList,
    List.cons_append, List.nil_append, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.reverse_reverse]
  simp only [String.ofList_toList]
  rw [hs]
  have hmap : ∀ xs : List Nat, xs.mapM (String.toNat? ∘ Nat.repr) = some xs := by
    intro xs
    induction xs <;> simp_all [List.mapM_cons, Function.comp_def]
  simp [parseElemType_complete, hmap]

theorem ppTensorType_injective : Function.Injective ppTensorType := by
  intro a b h
  have hp := congrArg parseTensorType h
  simpa only [parseTensorType_roundtrip, Option.some.injEq] using hp

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem parseStableHLOOp_convert_reshape_roundtrip (tenv : TypeEnv) (d s : String)
    (elem : ElemType) (shape : List Nat) (op : StableHLOOp)
    (hop : op = .convert d s elem ∨ op = .reshape d s shape)
    (hd : CanonicalSSAName d) (hs : CanonicalSSAName s)
    (ht : (resultTypeOf tenv op).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv op) = some op := by
  cases he : tenv s with
  | none => rcases hop with rfl | rfl <;> simp [resultTypeOf, he] at ht
  | some ty =>
    have hdscan := fun sep => scanHLOFields_name ' ' sep d hd rfl
    have hsscan := fun sep => scanHLOFields_name ' ' sep s hs rfl
    have hsend := fun sep => scanHLOFields_no_head ' ' sep s.toList (hs.excludes s ' ' rfl)
    have hscomma := fun sep => scanHLOFields_no_head ',' sep s.toList (hs.excludes s ',' rfl)
    have hty := fun sep rest fuel => scanHLOFields_chunk ' ' sep (ppTensorType ty).toList rest fuel
      (tensorType_no_space ty)
    have hout := fun (t : TensorType) sep => scanHLOFields_type ' ' sep t rfl
    have hprefix (t : TensorType) : stripPrefixChars [':', ' '] (ppTensorType t).toList = none := by
      cases t with
      | mk shape elem => cases shape <;> simp [ppTensorType, toString, String.toList_append, stripPrefixChars]
    rcases hop with rfl | rfl
    all_goals (
    have hvol : (resultTypeOf tenv (.reshape d s shape)).isSome = true →
        (ty.shape.foldl (· * ·) 1 == shape.foldl (· * ·) 1) = true := by
      simp [resultTypeOf, he]
    try (have hv := hvol ht)
    simp only [ppStableHLOOp, resultTypeOf, he, Option.map_some, toString,
      Option.bind]
    try simp only [hv, ↓reduceIte]
    unfold parseStableHLOOp parseHLOFields
    simp only [String.toList_append, String.reduceToList, List.append_assoc,
      List.cons_append, List.nil_append, List.length_append, List.length_cons]
    repeat first
      | (rw [hdscan] <;> try omega)
      | (rw [hsscan] <;> try omega)
      | (rw [hsend] <;> try omega)
      | (rw [hscomma] <;> try omega)
      | (rw [hty] <;> try omega)
      | (rw [hout] <;> try omega)
      | simp only [scanHLOFields, stripPrefixChars, List.isEmpty_cons,
          hprefix,
          String.toList_ofList, String.ofList_toList, List.length_append, List.length_cons,
          Bool.false_eq_true, ↓reduceIte, Char.reduceBEq, bind, Option.bind, pure,
          Option.map_some, List.map_cons, List.map_nil, List.append_nil,
          Nat.add_eq, Nat.add_assoc, Nat.add_sub_cancel_left]
    simp [hd.parse_roundtrip d, hs.parse_roundtrip s,
      parseTensorType_roundtrip, he, resultTypeOf,
      String.ofList_append, String.append_assoc, toString]
    try (have hv' := beq_iff_eq.mp hv; simp only [hv', ↓reduceIte])
    try (suffices h : (_ : Prop) from ite_eq_left h)
    all_goals try
      constructor
      · change (_ == _ && _ == _) = true
        have helem (e : ElemType) : (e == e) = true := by cases e <;> rfl
        simp [helem]
      · simp only [← String.append_assoc]; rfl
    all_goals try ((try simp only [Nat.add_eq]) <;> omega)
    )

theorem parseStableHLOOp_convert_roundtrip (tenv : TypeEnv) (d s : String)
    (elem : ElemType) (hd : CanonicalSSAName d) (hs : CanonicalSSAName s)
    (ht : (resultTypeOf tenv (.convert d s elem)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.convert d s elem)) = some (.convert d s elem) :=
  parseStableHLOOp_convert_reshape_roundtrip tenv d s elem [] _ (Or.inl rfl) hd hs ht

theorem parseStableHLOOp_reshape_roundtrip (tenv : TypeEnv) (d s : String)
    (shape : List Nat) (hd : CanonicalSSAName d) (hs : CanonicalSSAName s)
    (ht : (resultTypeOf tenv (.reshape d s shape)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.reshape d s shape)) = some (.reshape d s shape) :=
  parseStableHLOOp_convert_reshape_roundtrip tenv d s .ui64 shape _ (Or.inr rfl) hd hs ht

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem parseStableHLOOp_select_roundtrip (tenv : TypeEnv) (d p t e : String)
    (hd : CanonicalSSAName d) (hp : CanonicalSSAName p)
    (ht : CanonicalSSAName t) (he : CanonicalSSAName e)
    (hw : (resultTypeOf tenv (.select d p t e)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.select d p t e)) = some (.select d p t e) := by
  cases hpt : tenv p with
  | none => simp [resultTypeOf, hpt] at hw
  | some pt =>
    cases htt : tenv t with
    | none => simp [resultTypeOf, hpt, htt] at hw
    | some tt =>
      cases hrt : resultTypeOf tenv (.select d p t e) with
      | none => simp [hrt] at hw
      | some out =>
        have hdscan := fun sep => scanHLOFields_name ' ' sep d hd rfl
        have hpscan := fun sep => scanHLOFields_name ' ' sep p hp rfl
        have htscan := fun sep => scanHLOFields_name ' ' sep t ht rfl
        have hescan := fun sep => scanHLOFields_name ' ' sep e he rfl
        have hpcomma := fun sep => scanHLOFields_name ',' sep p hp rfl
        have htcomma := fun sep => scanHLOFields_name ',' sep t ht rfl
        have hecomma := fun sep => scanHLOFields_no_head ',' sep e.toList (he.excludes e ',' rfl)
        have heend := fun sep => scanHLOFields_no_head ' ' sep e.toList (he.excludes e ' ' rfl)
        have hty := fun (ty : TensorType) sep rest fuel =>
          scanHLOFields_chunk ' ' sep (ppTensorType ty).toList rest fuel (tensorType_no_space ty)
        have hout := fun (ty : TensorType) sep => scanHLOFields_type ' ' sep ty rfl
        have hprefix (ty : TensorType) : stripPrefixChars [':', ' '] (ppTensorType ty).toList = none := by
          cases ty with
          | mk shape elem => cases shape <;> simp [ppTensorType, toString, String.toList_append, stripPrefixChars]
        simp only [ppStableHLOOp, hrt, hpt, htt, toString]
        unfold parseStableHLOOp parseHLOFields
        simp only [String.toList_append, String.reduceToList, List.append_assoc,
          List.cons_append, List.nil_append, List.length_append, List.length_cons]
        repeat first
          | (rw [hdscan] <;> try omega)
          | (rw [hpscan] <;> try omega)
          | (rw [htscan] <;> try omega)
          | (rw [hescan] <;> try omega)
          | (rw [hpcomma] <;> try omega)
          | (rw [htcomma] <;> try omega)
          | (rw [hecomma] <;> try omega)
          | (rw [heend] <;> try omega)
          | (rw [hout] <;> try omega)
          | (rw [hty] <;> try omega)
          | simp only [scanHLOFields, stripPrefixChars, List.isEmpty_cons, hprefix,
              String.toList_ofList, List.length_append, List.length_cons,
              Bool.false_eq_true, ↓reduceIte, Char.reduceBEq, bind, Option.bind, pure,
              Option.map_some, List.map_cons, List.map_nil, List.append_nil,
              Nat.add_eq, Nat.add_assoc, Nat.add_sub_cancel_left]
        simp [hd.parse_roundtrip d, hp.parse_roundtrip p, ht.parse_roundtrip t,
          he.parse_roundtrip e, hrt, hpt, htt, String.ofList_append, toString, String.append_assoc]
        · simp only [← String.append_assoc]; rfl
        all_goals try ((try simp only [Nat.add_eq]) <;> omega)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem parseStableHLOOp_compare_roundtrip (tenv : TypeEnv) (d a b : String) (dir : CompareDir)
    (hd : CanonicalSSAName d) (ha : CanonicalSSAName a) (hb : CanonicalSSAName b)
    (hw : (resultTypeOf tenv (.compare d a b dir)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.compare d a b dir)) = some (.compare d a b dir) := by
  cases hat : tenv a with
  | none => simp [resultTypeOf, hat] at hw
  | some ty =>
    have hrt : resultTypeOf tenv (.compare d a b dir) = some { ty with elem := .i1 } := by
      unfold resultTypeOf at hw ⊢
      simp only [hat] at hw ⊢
      split <;> simp_all
    have hdscan := fun sep => scanHLOFields_name ' ' sep d hd rfl
    have hascan := fun sep => scanHLOFields_name ' ' sep a ha rfl
    have hbscan := fun sep => scanHLOFields_name ' ' sep b hb rfl
    have hacomma := fun sep => scanHLOFields_name ',' sep a ha rfl
    have hbcomma := fun sep => scanHLOFields_name ',' sep b hb rfl
    have hdir : CanonicalSSAName (ppCompareDir dir) := by cases dir <;> constructor <;> decide
    have hkind : CanonicalSSAName (ppCompareType ty.elem) := by cases ty.elem <;> constructor <;> decide
    have hdirspace := fun sep => scanHLOFields_name ' ' sep (ppCompareDir dir) hdir rfl
    have hdircomma := fun sep => scanHLOFields_name ',' sep (ppCompareDir dir) hdir rfl
    have hkindspace := fun sep => scanHLOFields_name ' ' sep (ppCompareType ty.elem) hkind rfl
    have hkindend := fun sep => scanHLOFields_no_head ',' sep (ppCompareType ty.elem).toList
      (hkind.excludes _ ',' rfl)
    have hkindspaceend := fun sep => scanHLOFields_no_head ' ' sep (ppCompareType ty.elem).toList
      (hkind.excludes _ ' ' rfl)
    have hkindassign (sep : List Char) :
        stripPrefixChars ('=' :: sep) (ppCompareType ty.elem).toList = none := by
      cases ty.elem <;> rfl
    have hkindprefix (rest : List Char) :
        stripPrefixChars [':', ' '] ((ppCompareType ty.elem).toList ++ rest) = none := by
      cases ty.elem <;> rfl
    have hdirprefix (rest : List Char) :
        stripPrefixChars [':', ' '] ((ppCompareDir dir).toList ++ rest) = none := by
      cases dir <;> rfl
    have htypeprefix (t : TensorType) (rest : List Char) :
        stripPrefixChars [':', ' '] ((ppTensorType t).toList ++ rest) = none := by
      cases t with
      | mk shape elem => cases shape <;> simp [ppTensorType, toString, String.toList_append, stripPrefixChars]
    have hty := fun (t : TensorType) sep rest fuel =>
      scanHLOFields_chunk ' ' sep (ppTensorType t).toList rest fuel (tensorType_no_space t)
    have hout := fun (t : TensorType) sep => scanHLOFields_type ' ' sep t rfl
    have hprefix (t : TensorType) : stripPrefixChars [':', ' '] (ppTensorType t).toList = none := by
      cases t with
      | mk shape elem => cases shape <;> simp [ppTensorType, toString, String.toList_append, stripPrefixChars]
    simp only [ppStableHLOOp, hat, hrt, ppCompare, toString]
    unfold parseStableHLOOp parseHLOFields
    simp only [String.toList_append, String.reduceToList, List.append_assoc,
      List.cons_append, List.nil_append, List.length_append, List.length_cons]
    repeat first
      | (rw [hdscan] <;> try omega)
      | (rw [hascan] <;> try omega)
      | (rw [hbscan] <;> try omega)
      | (rw [hacomma] <;> try omega)
      | (rw [hbcomma] <;> try omega)
      | (rw [hdirspace] <;> try omega)
      | (rw [hdircomma] <;> try omega)
      | (rw [hkindspace] <;> try omega)
      | (rw [hkindend] <;> try omega)
      | (rw [hkindspaceend] <;> try omega)
      | (rw [hout] <;> try omega)
      | (rw [hty] <;> try omega)
      | simp only [hkindassign, hkindprefix, hdirprefix, htypeprefix, scanHLOFields, stripPrefixChars, List.isEmpty_cons, hprefix,
          String.toList_ofList, String.ofList_toList, List.length_append, List.length_cons,
          Bool.false_eq_true, ↓reduceIte, Char.reduceBEq, bind, Option.bind, pure,
          Option.map_some, List.map_cons, List.map_nil, List.append_nil,
          Nat.add_eq, Nat.add_assoc, Nat.add_sub_cancel_left]
    have hdirparse : parseCompareDir (ppCompareDir dir) = some dir := by cases dir <;> rfl
    simp [hd.parse_roundtrip d, ha.parse_roundtrip a, hb.parse_roundtrip b,
      hdirparse, hrt, hat, String.ofList_append, toString, String.append_assoc]
    · simp only [← String.append_assoc, String.reduceAppend]
    all_goals try ((try simp only [Nat.add_eq]) <;> omega)

theorem numElements_scalar (e : ElemType) :
    ({ shape := [], elem := e : TensorType }).numElements = 1 := rfl

theorem evalOp_constant_preserves_type (env : Env) (dst : String) (v : TensorVal)
    (h : v.data.size = v.ty.numElements) :
    ∃ env', evalOp env (.constant dst v) = .ok env' ∧ env' dst = some v := by
  unfold evalOp evalConstant
  simp [h, Env.bind]

theorem evalOp_preserves_tensorType (env : Env) (dst : String) (v : TensorVal)
    (h : v.wellFormed) :
    match evalOp env (.constant dst v) with
    | .ok env' => ∃ t, env' dst = some t ∧ t.ty = v.ty ∧ t.wellFormed
    | .error _ => False := by
  unfold TensorVal.wellFormed at h
  unfold evalOp evalConstant
  simp [h, Env.bind, TensorVal.wellFormed]

theorem reshape_invalid_volume_errors (env : Env) (dst src : String) (a : TensorVal)
    (outShape : List Nat) (hsrc : env src = some a)
    (hwf : a.data.size = a.ty.numElements)
    (hvol : a.ty.shape.foldl (· * ·) 1 ≠ outShape.foldl (· * ·) 1) :
    evalOp env (.reshape dst src outShape) =
      .error (.volumeMismatch (a.ty.shape.foldl (· * ·) 1) (outShape.foldl (· * ·) 1)) := by
  have hwf' : a.data.size = a.ty.shape.foldl (· * ·) 1 := by
    simpa [TensorType.numElements] using hwf
  unfold evalOp evalReshape reshapeData lookup checkWellFormed TensorType.numElements
  simp [hsrc, hwf', hvol, bind, Except.bind]

theorem maskWidth_idem (w : Nat) (x : BitVec 64) :
    maskWidth w (maskWidth w x) = maskWidth w x := by
  unfold maskWidth
  split
  · rfl
  · rename_i hge
    have hw : w ≤ 64 := Nat.le_of_lt (Nat.lt_of_not_ge hge)
    have hdvd : 2 ^ w ∣ 2 ^ 64 := ⟨2 ^ (64 - w), by rw [← Nat.pow_add, Nat.add_sub_of_le hw]⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod]

theorem maskWidth_add_left (w : Nat) (x y : BitVec 64) :
    maskWidth w (maskWidth w x + y) = maskWidth w (x + y) := by
  unfold maskWidth
  split
  · rfl
  · rename_i hge
    have hw : w < 64 := Nat.lt_of_not_ge hge
    have hlt64 : ∀ n, n % 2 ^ w < 2 ^ 64 := fun n =>
      Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos w)) (Nat.pow_lt_pow_right (by decide) hw)
    have hdvd : 2 ^ w ∣ 2 ^ 64 :=
      ⟨2 ^ (64 - w), by rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hw)]⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_add, Nat.mod_eq_of_lt (hlt64 x.toNat),
      Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_add_mod]

theorem maskWidth_add_right (w : Nat) (x y : BitVec 64) :
    maskWidth w (x + maskWidth w y) = maskWidth w (x + y) := by
  rw [BitVec.add_comm x, maskWidth_add_left, BitVec.add_comm]

theorem elemBin_add_comm (e : ElemType) (x y : BitVec 64) :
    elemBin e (· + ·) x y = elemBin e (· + ·) y x := by
  unfold elemBin
  cases isFloat e
  · cases intBitWidth? e <;> simp [BitVec.add_comm]
  · simp

theorem elemBin_add_assoc (e : ElemType) (x y z : BitVec 64)
    (hf : isFloat e = false) (hw : (intBitWidth? e).isSome = true) :
    (do
      let xy ← elemBin e (· + ·) x y
      elemBin e (· + ·) xy z) =
    (do
      let yz ← elemBin e (· + ·) y z
      elemBin e (· + ·) x yz) := by
  unfold elemBin
  rcases hW : intBitWidth? e with _ | w
  · simp [hW] at hw
  · simp [hf, bind, Except.bind, maskWidth_idem, maskWidth_add_left, maskWidth_add_right,
      BitVec.add_assoc]

theorem zipMap_comm (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, f x y = f y x) :
    ∀ (xs ys : List (BitVec 64)), xs.length = ys.length →
      (xs.zip ys).map (fun (x, y) => f x y) = (ys.zip xs).map (fun (x, y) => f x y)
  | [], [], _ => rfl
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
    simp [hf x y, zipMap_comm f hf xs ys (Nat.succ.inj h)]

theorem addAt_assoc (w : Nat) (a b c : BitVec 64) :
    addAt w (addAt w a b) c = addAt w a (addAt w b c) := by
  unfold addAt
  simp only [maskWidth_add_left, maskWidth_add_right, BitVec.add_assoc]

theorem zipWithTotal_comm (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, f x y = f y x) (a b : Array (BitVec 64))
    (hlen : a.size = b.size) :
    zipWithTotal f a b = zipWithTotal f b a := by
  unfold zipWithTotal
  have hlist : a.toList.length = b.toList.length := by simp [hlen]
  rw [zipMap_comm f hf a.toList b.toList hlist]

theorem zipMap_assoc (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y z, f (f x y) z = f x (f y z)) :
    ∀ (xs ys zs : List (BitVec 64)), xs.length = ys.length → ys.length = zs.length →
      (((xs.zip ys).map (fun (x, y) => f x y)).zip zs).map (fun (x, y) => f x y) =
      (xs.zip ((ys.zip zs).map (fun (x, y) => f x y))).map (fun (x, y) => f x y)
  | [], [], [], _, _ => rfl
  | _ :: _, [], _, h1, _ => by cases h1
  | [], _ :: _, _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp [hf x y z, zipMap_assoc f hf xs ys zs (Nat.succ.inj h1) (Nat.succ.inj h2)]

theorem zipWithTotal_assoc (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y z, f (f x y) z = f x (f y z))
    (a b c : Array (BitVec 64))
    (hab : a.size = b.size) (hbc : b.size = c.size) :
    zipWithTotal f (zipWithTotal f a b) c = zipWithTotal f a (zipWithTotal f b c) := by
  unfold zipWithTotal
  have hab' : a.toList.length = b.toList.length := by simp [hab]
  have hbc' : b.toList.length = c.toList.length := by simp [hbc]
  simp [zipMap_assoc f hf a.toList b.toList c.toList hab' hbc']

theorem stablehlo_add_comm (env : Env) (x y : TensorVal)
    (hx : env "x" = some x) (hy : env "y" = some y) (hty : x.ty = y.ty)
    (hwx : x.data.size = x.ty.numElements) (hwy : y.data.size = y.ty.numElements) :
    evalOp env (.add "d" "x" "y") = evalOp env (.add "d" "y" "x") := by
  have hlen : x.data.size = y.data.size := by rw [hwx, hwy, hty]
  unfold evalOp evalAdd lookup checkWellFormed
  simp [hx, hy, hty, hwx, hwy, bind, Except.bind]
  cases isFloat y.ty.elem
  · cases intBitWidth? y.ty.elem
    · rfl
    · rename_i w
      have hf : ∀ p q : BitVec 64, addAt w p q = addAt w q p := by
        intro p q
        unfold addAt
        simp [BitVec.add_comm]
      simp [zipWithTotal_comm _ hf _ _ hlen]
  · rfl

theorem stablehlo_add_assoc (env : Env) (x y z : TensorVal)
    (hx : env "x" = some x) (hy : env "y" = some y) (hz : env "z" = some z)
    (hty : x.ty = y.ty ∧ y.ty = z.ty)
    (hwx : x.data.size = x.ty.numElements)
    (hwy : y.data.size = y.ty.numElements)
    (hwz : z.data.size = z.ty.numElements)
    (hf : isFloat x.ty.elem = false) (hWsome : (intBitWidth? x.ty.elem).isSome = true) :
    (do
      let e1 ← evalOp env (.add "xy" "x" "y")
      let e2 ← evalOp e1 (.add "r" "xy" "z")
      pure (e2 "r")) =
    (do
      let e1 ← evalOp env (.add "yz" "y" "z")
      let e2 ← evalOp e1 (.add "r" "x" "yz")
      pure (e2 "r")) := by
  unfold evalOp evalAdd lookup checkWellFormed
  rcases hty with ⟨hty1, hty2⟩
  have hlen1 : x.data.size = y.data.size := by rw [hwx, hwy, hty1]
  have hlen2 : y.data.size = z.data.size := by rw [hwy, hwz, hty2]
  rcases hW : intBitWidth? x.ty.elem with _ | w
  · simp [hW] at hWsome
  · have hW' : intBitWidth? z.ty.elem = some w := by simpa [hty1, hty2] using hW
    have hf' : isFloat z.ty.elem = false := by simpa [hty1, hty2] using hf
    have hxy : (zipWithTotal (addAt w) x.data y.data).size = z.data.size := by
      unfold zipWithTotal
      simp [hlen1, hlen2]
    have hyz : (zipWithTotal (addAt w) y.data z.data).size = z.data.size := by
      unfold zipWithTotal
      simp [hlen2]
    simp [hx, hy, hz, hty1, hty2, hwx, hwy, hwz, hf', hW', Env.bind,
      bind, Except.bind, pure, Except.pure, hxy, hyz,
      zipWithTotal_assoc (addAt w) (addAt_assoc w) x.data y.data z.data hlen1 hlen2]

theorem evalOp_add_result_type (env : Env) (a b : TensorVal)
    (ha : env "a" = some a) (hb : env "b" = some b) (hty : a.ty = b.ty)
    (hwa : a.wellFormed) (hwb : b.wellFormed)
    (hf : isFloat a.ty.elem = false)
    (hW : (intBitWidth? a.ty.elem).isSome = true) :
    match evalOp env (.add "d" "a" "b") with
    | .ok env' => ∃ t, env' "d" = some t ∧ t.ty = a.ty ∧ t.wellFormed
    | .error _ => False := by
  unfold TensorVal.wellFormed at hwa hwb
  have hlen : a.data.size = b.data.size := by rw [hwa, hwb, hty]
  unfold evalOp evalAdd lookup checkWellFormed
  rcases hwidth : intBitWidth? a.ty.elem with _ | w
  · simp [hwidth] at hW
  · have hwidth' : intBitWidth? b.ty.elem = some w := by simpa [hty] using hwidth
    have hf' : isFloat b.ty.elem = false := by simpa [hty] using hf
    have hsz : (zipWithTotal (addAt w) a.data b.data).size = b.data.size := by
      unfold zipWithTotal
      simp [hlen]
    simp [ha, hb, hty, hwa, hwb, hf', hwidth', hsz, Env.bind, TensorVal.wellFormed,
      bind, Except.bind]

theorem isSigned_i1 : isSigned .i1 = false := rfl

theorem intBitWidth_float (e : ElemType) (h : isFloat e = true) : intBitWidth? e = none := by
  cases e <;> simp [isFloat, intBitWidth?] at *

theorem evalOps_nil (env : Env) : evalOps env [] = .ok env := rfl

theorem evalOps_singleton (env : Env) (op : StableHLOOp) :
    evalOps env [op] = evalOp env op := by
  have hex : ∀ (r : Except ShapeError Env), (r >>= fun e => Except.ok e) = r := by
    intro r
    cases r <;> rfl
  cases op <;> exact hex (evalOp env _)

private def isNatListChar (c : Char) : Bool :=
  c.isDigit || c == '[' || c == ']' || c == ',' || c == ' '

private def isTensorTypeChar (c : Char) : Bool :=
  c.isDigit || "tensor<>xiufb".toList.contains c

theorem intercalate_all (sep : String) (xs : List String) (p : Char → Bool)
    (hsep : sep.toList.all p = true) (hxs : ∀ s ∈ xs, s.toList.all p = true) :
    (String.intercalate sep xs).toList.all p = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simpa using hxs x (by simp)
    | cons y ys =>
      rw [String.intercalate_cons_cons]
      simp only [String.toList_append, List.all_append, Bool.and_eq_true]
      exact ⟨⟨hxs x (by simp), hsep⟩, ih (fun z hz => hxs z (by simp [hz]))⟩

private theorem ssaName_excludes (name : String) (h : CanonicalSSAName name)
    (c : Char) (hc : (c.isAlphanum || c == '_') = false) : c ∉ name.toList := by
  intro hm
  have := List.all_eq_true.mp h.2 c hm
  simp [hc] at this

private theorem tensorType_chars (ty : TensorType) :
    (ppTensorType ty).toList.all isTensorTypeChar = true := by
  have hnat (m : Nat) : m.repr.toList.all isTensorTypeChar = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using hc)
    simp [isTensorTypeChar, hd]
  have hel : (ppElemType ty.elem).toList.all isTensorTypeChar = true := by
    cases ty.elem <;> decide
  rcases ty with ⟨shape, elem⟩
  cases shape with
  | nil =>
    rw [show ppTensorType { shape := [], elem := elem } = "tensor<" ++ ppElemType elem ++ ">" from rfl]
    simp only [String.toList_append, List.all_append, Bool.and_eq_true]
    exact ⟨⟨by decide, hel⟩, by decide⟩
  | cons n ns =>
    have hs := intercalate_all "x" ((n :: ns).map Nat.repr) isTensorTypeChar (by decide) (fun s hs => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hs; exact hnat m)
    rw [show ppTensorType { shape := n :: ns, elem := elem } =
        "tensor<" ++ String.intercalate "x" ((n :: ns).map Nat.repr) ++ "x" ++ ppElemType elem ++ ">" by
      simp [ppTensorType, ppShape, toString, String.append_assoc]]
    simp only [String.toList_append, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨⟨by decide, hs⟩, by decide⟩, hel⟩, by decide⟩

private theorem tensorType_excludes (ty : TensorType) (c : Char)
    (hc : isTensorTypeChar c = false) : c ∉ (ppTensorType ty).toList := by
  intro hm
  have := List.all_eq_true.mp (tensorType_chars ty) c hm
  simp [hc] at this

theorem ppNatList_chars (ns : List Nat) :
    (ppNatList ns).toList.all isNatListChar = true := by
  have hnat (m : Nat) : m.repr.toList.all isNatListChar = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega)
      (by simpa only [Nat.toList_repr] using hc)
    simp [isNatListChar, hd]
  unfold ppNatList
  rw [String.toList_append, String.toList_append]
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨by decide, intercalate_all ", " (ns.map toString) isNatListChar (by decide) ?_⟩, by decide⟩
  intro s hs
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hs
  exact hnat m

theorem ppNatList_excludes (ns : List Nat) (c : Char) (hc : isNatListChar c = false) :
    c ∉ (ppNatList ns).toList := by
  intro hm
  have := List.all_eq_true.mp (ppNatList_chars ns) c hm
  simp [hc] at this

theorem stripPrefixChars_none_of_absent (sep xs : List Char) (c : Char)
    (hc : c ∈ sep) (hn : c ∉ xs) : stripPrefixChars sep xs = none := by
  induction sep generalizing xs with
  | nil => simp at hc
  | cons p ps ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [stripPrefixChars]
      rcases List.mem_cons.mp hc with hpc | hps
      · subst p
        have hne : (c == x) = false := beq_eq_false_iff_ne.mpr (fun he => hn (by simp [he]))
        simp [hne]
      · split
        · exact ih xs hps (fun hm => hn (by simp [hm]))
        · rfl

private theorem stripPrefixChars_length_le :
    ∀ (sep xs rest : List Char), stripPrefixChars sep xs = some rest → rest.length + sep.length = xs.length
  | [], xs, rest, h => by simp [stripPrefixChars] at h; subst h; simp
  | _ :: _, [], _, h => by simp [stripPrefixChars] at h
  | p :: ps, x :: xs, rest, h => by
    simp only [stripPrefixChars] at h
    split at h
    · have ih := stripPrefixChars_length_le ps xs rest h
      simp; omega
    · contradiction

private theorem scanHLOFields_always (sep : List Char) (hne : sep ≠ []) :
    ∀ (xs : List Char) (fuel : Nat), xs.length < fuel → ∃ f fs, scanHLOFields sep fuel xs = some (f :: fs)
  | [], 0, hf => by simp at hf
  | [], _ + 1, _ => ⟨[], [], rfl⟩
  | x :: xs, 0, hf => by simp at hf
  | x :: xs, k + 1, hf => by
    have hs : sep.isEmpty = false := by cases sep <;> simp_all
    simp only [scanHLOFields, hs, Bool.false_eq_true, ↓reduceIte]
    cases hst : stripPrefixChars sep (x :: xs) with
    | some rest =>
      have hle := stripPrefixChars_length_le sep (x :: xs) rest hst
      have hpos : 0 < sep.length := List.length_pos_iff.mpr hne
      obtain ⟨f, fs, hrec⟩ := scanHLOFields_always sep hne rest k (by simp at hf hle; omega)
      exact ⟨[], f :: fs, by simp [hrec]⟩
    | none =>
      obtain ⟨f, fs, hrec⟩ := scanHLOFields_always sep hne xs k (by simp at hf; omega)
      exact ⟨x :: f, fs, by simp [hrec]⟩

private theorem scanHLOFields_cons_nonmatch (sep : List Char) (c : Char) (cs : List Char)
    (fuel : Nat) (line : List Char) (lines : List (List Char))
    (hne : sep ≠ []) (hno : stripPrefixChars sep (c :: cs) = none)
    (hr : scanHLOFields sep fuel cs = some (line :: lines)) :
    scanHLOFields sep (fuel + 1) (c :: cs) = some ((c :: line) :: lines) := by
  have hs : sep.isEmpty = false := by cases sep <;> simp_all
  simp [scanHLOFields, hs, hno, hr]

theorem scanHLOFields_single_of_absent (sep xs : List Char) (fuel : Nat)
    (hne : sep ≠ []) (c : Char) (hc : c ∈ sep) (hn : c ∉ xs) (hf : xs.length < fuel) :
    scanHLOFields sep fuel xs = some [xs] := by
  have hz : scanHLOFields sep (fuel - xs.length) [] = some [[]] := by
    cases hsub : fuel - xs.length with
    | zero => omega
    | succ k => rfl
  have hp := scanHLOFields_prefix sep xs [] (fuel - xs.length) [] [] hne
    (fun a b he _ => by
      rw [List.append_nil]
      exact stripPrefixChars_none_of_absent sep b c hc (fun hm => hn (by simp [he, hm]))) hz
  simpa [Nat.add_sub_of_le (Nat.le_of_lt hf)] using hp

theorem parseHLOFields_single_of_absent (sep text : String)
    (hne : sep.toList ≠ []) (c : Char) (hc : c ∈ sep.toList) (hn : c ∉ text.toList) :
    parseHLOFields sep text = some [text] := by
  unfold parseHLOFields
  rw [scanHLOFields_single_of_absent sep.toList text.toList (text.toList.length + 1) hne c hc hn (by omega)]
  simp

theorem parseHLOFields_pair_of_no_prefix (sep lhs rhs : String)
    (hne : sep.toList ≠ [])
    (hlhs : ∀ a b, lhs.toList = a ++ b → b ≠ [] →
      stripPrefixChars sep.toList (b ++ (sep.toList ++ rhs.toList)) = none)
    (c₂ : Char) (hc₂ : c₂ ∈ sep.toList) (hrhs : c₂ ∉ rhs.toList) :
    parseHLOFields sep (lhs ++ sep ++ rhs) = some [lhs, rhs] := by
  unfold parseHLOFields
  have hsep_pos : 0 < sep.toList.length := List.length_pos_iff.mpr hne
  let rfuel := sep.toList.length + rhs.toList.length
  have hr : scanHLOFields sep.toList rfuel rhs.toList = some [rhs.toList] :=
    scanHLOFields_single_of_absent sep.toList rhs.toList rfuel hne c₂ hc₂ hrhs (by dsimp [rfuel]; omega)
  have hd : scanHLOFields sep.toList (rfuel + 1) (sep.toList ++ rhs.toList) = some [[], rhs.toList] := by
    rw [scanHLOFields_delimiter sep.toList rhs.toList rfuel hne, hr]; rfl
  have hp := scanHLOFields_prefix sep.toList lhs.toList (sep.toList ++ rhs.toList)
    (rfuel + 1) [] [rhs.toList] hne hlhs hd
  have hlen : (lhs ++ sep ++ rhs).toList.length + 1 = lhs.toList.length + (rfuel + 1) := by
    simp [rfuel, String.toList_append]; omega
  have hchars : (lhs ++ sep ++ rhs).toList = lhs.toList ++ (sep.toList ++ rhs.toList) := by
    simp [String.toList_append, List.append_assoc]
  rw [hlen, hchars, hp]
  simp

theorem parseHLOFields_pair_head (c₁ : Char) (ds : String) (lhs rhs : String)
    (hlhs : c₁ ∉ lhs.toList)
    (c₂ : Char) (hc₂ : c₂ ∈ (String.singleton c₁ ++ ds).toList) (hrhs : c₂ ∉ rhs.toList) :
    parseHLOFields (String.singleton c₁ ++ ds) (lhs ++ (String.singleton c₁ ++ ds) ++ rhs) =
      some [lhs, rhs] := by
  apply parseHLOFields_pair_of_no_prefix _ _ _ (by simp [String.toList_append]) _ c₂ hc₂ hrhs
  intro a b he hb
  cases b with
  | nil => contradiction
  | cons x xs =>
    have hx : c₁ ≠ x := fun h => hlhs (by subst h; simp [he])
    simp [String.toList_append, stripPrefixChars, hx]

theorem parseHLOFields_pair_second (s₀ s₁ : Char) (ds : String) (lhs rhs : String)
    (hne01 : s₁ ≠ s₀) (hlhs : s₁ ∉ lhs.toList)
    (c₂ : Char) (hc₂ : c₂ ∈ (String.ofList [s₀, s₁] ++ ds).toList) (hrhs : c₂ ∉ rhs.toList) :
    parseHLOFields (String.ofList [s₀, s₁] ++ ds) (lhs ++ (String.ofList [s₀, s₁] ++ ds) ++ rhs) =
      some [lhs, rhs] := by
  apply parseHLOFields_pair_of_no_prefix _ _ _ (by simp [String.toList_append]) _ c₂ hc₂ hrhs
  intro a b he hb
  cases b with
  | nil => contradiction
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [String.toList_append, String.toList_ofList, List.cons_append, List.nil_append,
        stripPrefixChars]
      split
      · simp [hne01]
      · rfl
    | cons y ys =>
      have hy : s₁ ≠ y := fun h => hlhs (by subst h; simp [he])
      simp only [String.toList_append, String.toList_ofList, List.cons_append, List.nil_append,
        stripPrefixChars]
      split
      · simp [hy]
      · rfl

private theorem parseHLOFields_head_of_no_prefix (sep lhs rhs : String)
    (hne : sep.toList ≠ [])
    (hlhs : ∀ a b, lhs.toList = a ++ b → b ≠ [] →
      stripPrefixChars sep.toList (b ++ (sep.toList ++ rhs.toList)) = none) :
    ∃ f fs, parseHLOFields sep (lhs ++ sep ++ rhs) = some (lhs :: f :: fs) := by
  unfold parseHLOFields
  have hsep_pos : 0 < sep.toList.length := List.length_pos_iff.mpr hne
  let rfuel := sep.toList.length + rhs.toList.length
  obtain ⟨f, fs, hr⟩ := scanHLOFields_always sep.toList hne rhs.toList rfuel (by dsimp [rfuel]; omega)
  have hd : scanHLOFields sep.toList (rfuel + 1) (sep.toList ++ rhs.toList) = some ([] :: f :: fs) := by
    rw [scanHLOFields_delimiter sep.toList rhs.toList rfuel hne, hr]; rfl
  have hp := scanHLOFields_prefix sep.toList lhs.toList (sep.toList ++ rhs.toList)
    (rfuel + 1) [] (f :: fs) hne hlhs hd
  have hlen : (lhs ++ sep ++ rhs).toList.length + 1 = lhs.toList.length + (rfuel + 1) := by
    simp [rfuel, String.toList_append]; omega
  have hchars : (lhs ++ sep ++ rhs).toList = lhs.toList ++ (sep.toList ++ rhs.toList) := by
    simp [String.toList_append, List.append_assoc]
  refine ⟨String.ofList f, fs.map String.ofList, ?_⟩
  rw [hlen, hchars, hp]
  simp

private theorem parseHLOFields_head_char (c : Char) (ds lhs rhs : String)
    (hlhs : c ∉ lhs.toList) :
    ∃ f fs, parseHLOFields (String.singleton c ++ ds) (lhs ++ (String.singleton c ++ ds) ++ rhs) =
      some (lhs :: f :: fs) := by
  apply parseHLOFields_head_of_no_prefix _ _ _ (by simp [String.toList_append])
  intro a b he hb
  cases b with
  | nil => contradiction
  | cons x xs =>
    have hx : c ≠ x := fun h => hlhs (by subst h; simp [he])
    simp [String.toList_append, stripPrefixChars, hx]

private theorem parseHLOFields_head_second (s₀ s₁ : Char) (ds lhs rhs : String)
    (hne01 : s₁ ≠ s₀) (hlhs : s₁ ∉ lhs.toList) :
    ∃ f fs, parseHLOFields (String.ofList [s₀, s₁] ++ ds) (lhs ++ (String.ofList [s₀, s₁] ++ ds) ++ rhs) =
      some (lhs :: f :: fs) := by
  apply parseHLOFields_head_of_no_prefix _ _ _ (by simp [String.toList_append])
  intro a b he hb
  cases b with
  | nil => contradiction
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [String.toList_append, String.toList_ofList, List.cons_append, List.nil_append, stripPrefixChars]
      split
      · simp [hne01]
      · rfl
    | cons y ys =>
      have hy : s₁ ≠ y := fun h => hlhs (by subst h; simp [he])
      simp only [String.toList_append, String.toList_ofList, List.cons_append, List.nil_append, stripPrefixChars]
      split
      · simp [hy]
      · rfl

private theorem stripPrefixChars_append_left (m t r : List Char) :
    stripPrefixChars (m ++ t) (m ++ r) = stripPrefixChars t r := by
  induction m <;> simp_all [stripPrefixChars]

private theorem mid_suffix_no_stablehlo (tag : List Char) :
    ∀ (m b rest : List Char),
      m = ['=', ' ', 's', 't', 'a', 'b', 'l', 'e', 'h', 'l', 'o', '.'] →
      ∀ a, m = a ++ b → b ≠ [] →
      stripPrefixChars (' ' :: '=' :: ' ' :: 's' :: 't' :: 'a' :: 'b' :: 'l' :: 'e' :: 'h' :: 'l' :: 'o' :: '.' :: tag)
        (b ++ rest) = none := by
  intro m b rest hm a he hb
  subst hm
  rcases a with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
  · subst he; rfl
  · rcases he with ⟨_, rfl⟩; rfl
  · rcases he with ⟨_, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩; rfl
  · rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hnil⟩
    simp at hnil; exact False.elim (hb hnil.2)

theorem parseHLOFields_stablehlo_nonmatch (tag d after : String)
    (hd : CanonicalSSAName d) (hdot : '.' ∉ after.toList)
    (hno : stripPrefixChars tag.toList after.toList = none) :
    parseHLOFields (" = stablehlo." ++ tag) ("%" ++ d ++ " = stablehlo." ++ after) =
      some ["%" ++ d ++ " = stablehlo." ++ after] := by
  let sep := (" = stablehlo." ++ tag).toList
  have hsep_eq : sep = ' ' :: '=' :: ' ' :: 's' :: 't' :: 'a' :: 'b' :: 'l' :: 'e' :: 'h' :: 'l' :: 'o' :: '.' :: tag.toList := by
    simp [sep, String.toList_append]
  have hsep_ne : sep ≠ [] := by simp [hsep_eq]
  have hdot_mem : '.' ∈ sep := by simp [hsep_eq]
  have hafter : scanHLOFields sep (after.toList.length + 1) after.toList = some [after.toList] :=
    scanHLOFields_single_of_absent sep after.toList (after.toList.length + 1) hsep_ne '.' hdot_mem hdot (by omega)
  let mid := " = stablehlo.".toList
  have hmid : ∀ a b, mid = a ++ b → b ≠ [] → stripPrefixChars sep (b ++ after.toList) = none := by
    intro a b he hb
    cases a with
    | nil =>
      simp [List.nil_append] at he; subst he
      have hs2 : sep = mid ++ tag.toList := by simp [sep, mid, String.toList_append]
      rw [hs2, stripPrefixChars_append_left]; exact hno
    | cons c0 as =>
      have hm : mid = ' ' :: ['=', ' ', 's', 't', 'a', 'b', 'l', 'e', 'h', 'l', 'o', '.'] := by decide
      rw [hm, List.cons_append, List.cons.injEq] at he
      rw [hsep_eq]
      exact mid_suffix_no_stablehlo tag.toList _ b after.toList rfl as he.2 hb
  have hmid_scan := scanHLOFields_prefix sep mid after.toList (after.toList.length + 1)
    after.toList [] hsep_ne hmid hafter
  let pre := ("%" ++ d).toList
  have hpre : ∀ a b, pre = a ++ b → b ≠ [] → stripPrefixChars sep (b ++ (mid ++ after.toList)) = none := by
    intro a b he hb
    cases b with
    | nil => contradiction
    | cons x xs =>
      have hnsp : ' ' ∉ pre := by simp [pre, String.toList_append, ssaName_excludes d hd ' ' rfl]
      have hx : ' ' ≠ x := fun h => hnsp (by subst h; simp [he])
      rw [hsep_eq]; simp [stripPrefixChars, hx]
  have hfull := scanHLOFields_prefix sep pre (mid ++ after.toList)
    (mid.length + (after.toList.length + 1)) (mid ++ after.toList) [] hsep_ne hpre hmid_scan
  unfold parseHLOFields
  have hlen : ("%" ++ d ++ " = stablehlo." ++ after).toList.length + 1 =
      pre.length + (mid.length + (after.toList.length + 1)) := by
    simp [pre, mid, String.toList_append]; omega
  have hchars : ("%" ++ d ++ " = stablehlo." ++ after).toList = pre ++ (mid ++ after.toList) := by
    simp [pre, mid, String.toList_append, List.append_assoc]
  rw [hlen, hchars]
  change (scanHLOFields sep _ _).map _ = _
  rw [hfull]
  simp only [Option.map_some, List.map_cons, List.map_nil]
  congr 2
  apply String.ext_iff.mpr
  simp [pre, mid, String.toList_append, List.append_assoc]

private theorem tensorType_beq_refl (ty : TensorType) : (ty == ty) = true := by
  change (ty.shape == ty.shape && ty.elem == ty.elem) = true
  have he : (ty.elem == ty.elem) = true := by cases ty.elem <;> rfl
  simp [he]

theorem parseStableHLOOp_broadcastInDim_roundtrip (tenv : TypeEnv) (d s : String)
    (shape dims : List Nat) (hd : CanonicalSSAName d) (hs : CanonicalSSAName s)
    (ht : (resultTypeOf tenv (.broadcastInDim d s shape dims)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.broadcastInDim d s shape dims)) =
      some (.broadcastInDim d s shape dims) := by
  cases hts : tenv s with
  | none => simp [resultTypeOf, hts] at ht
  | some ty =>
    have hrt : resultTypeOf tenv (.broadcastInDim d s shape dims) = some { ty with shape := shape } := by
      unfold resultTypeOf at ht ⊢
      simp only [hts, Option.bind_some] at ht ⊢
      split at ht <;> simp_all
    let outTy : TensorType := { ty with shape := shape }
    let suffix := "broadcast_in_dim %" ++ s ++ ", dims = " ++ ppNatList dims
    let operation := "%" ++ d ++ " = stablehlo." ++ suffix
    let annotation := "(" ++ ppTensorType ty ++ ") -> " ++ ppTensorType outTy
    have hpp : ppStableHLOOp tenv (.broadcastInDim d s shape dims) = operation ++ " : " ++ annotation := by
      apply String.ext_iff.mpr
      simp [ppStableHLOOp, hrt, hts, ppBroadcast, operation, suffix, annotation, outTy, toString, String.toList_append]
    have hcolon_op : ':' ∉ operation.toList := by
      simp [operation, suffix, String.toList_append, ssaName_excludes d hd ':' rfl,
        ssaName_excludes s hs ':' rfl, ppNatList_excludes dims ':' rfl]
    have hcolon_ann : ':' ∉ annotation.toList := by
      simp [annotation, String.toList_append, tensorType_excludes ty ':' rfl,
        tensorType_excludes outTy ':' rfl]
    have hsplit_ann : parseHLOFields " : " (operation ++ " : " ++ annotation) = some [operation, annotation] := by
      simpa using parseHLOFields_pair_second ' ' ':' " " operation annotation
        (by decide) hcolon_op ':' (by decide) hcolon_ann
    have hdot_suf : '.' ∉ suffix.toList := by
      simp [suffix, String.toList_append, ssaName_excludes s hs '.' rfl, ppNatList_excludes dims '.' rfl]
    have hcmp : parseHLOFields " = stablehlo.compare " operation = some [operation] := by
      simpa [operation, String.append_assoc] using
        parseHLOFields_stablehlo_nonmatch "compare " d suffix hd hdot_suf
          (by simp [suffix, String.toList_append, stripPrefixChars])
    have hsel : parseHLOFields " = stablehlo.select " operation = some [operation] := by
      simpa [operation, String.append_assoc] using
        parseHLOFields_stablehlo_nonmatch "select " d suffix hd hdot_suf
          (by simp [suffix, String.toList_append, stripPrefixChars])
    have hst : parseHLOFields " = stablehlo." operation = some ["%" ++ d, suffix] := by
      simpa [operation, String.append_assoc] using
        parseHLOFields_pair_head ' ' "= stablehlo." ("%" ++ d) suffix
          (by simp [String.toList_append, ssaName_excludes d hd ' ' rfl]) '.' (by decide) hdot_suf
    have hdims : parseHLOFields ", dims = " ("stablehlo." ++ suffix) =
        some ["stablehlo.broadcast_in_dim %" ++ s, ppNatList dims] := by
      have hp := parseHLOFields_pair_head ',' " dims = " ("stablehlo.broadcast_in_dim %" ++ s) (ppNatList dims)
        (by simp [String.toList_append, ssaName_excludes s hs ',' rfl]) '=' (by decide)
        (ppNatList_excludes dims '=' rfl)
      have heq : "stablehlo." ++ suffix = "stablehlo.broadcast_in_dim %" ++ s ++ ", dims = " ++ ppNatList dims := by
        apply String.ext_iff.mpr; simp [suffix, String.toList_append]
      rw [heq]; simpa [String.append_assoc] using hp
    have harg : parseHLOFields " " ("stablehlo.broadcast_in_dim %" ++ s) =
        some ["stablehlo.broadcast_in_dim", "%" ++ s] := by
      have hp := parseHLOFields_intercalate ' ' ["stablehlo.broadcast_in_dim", "%" ++ s] (by simp) (by
        intro x hx; simp at hx; rcases hx with rfl | rfl
        · decide
        · simp [String.toList_append, ssaName_excludes s hs ' ' rfl])
      have heq : "stablehlo.broadcast_in_dim %" ++ s = "stablehlo.broadcast_in_dim" ++ " " ++ ("%" ++ s) := by
        apply String.ext_iff.mpr; simp [String.toList_append]
      rw [heq]; simpa [String.append_assoc] using hp
    have harrow : parseHLOFields " -> " annotation =
        some ["(" ++ ppTensorType ty ++ ")", ppTensorType outTy] := by
      simpa [annotation, String.append_assoc] using
        parseHLOFields_pair_second ' ' '-' "> " ("(" ++ ppTensorType ty ++ ")") (ppTensorType outTy)
          (by decide) (by simp [String.toList_append, tensorType_excludes ty '-' rfl])
          '-' (by decide) (tensorType_excludes outTy '-' rfl)
    rw [hpp]
    unfold parseStableHLOOp
    simp only [hsplit_ann, hcmp, hsel, hst, hd.parse_roundtrip d, hdims, harg,
      hs.parse_roundtrip s, parseNatList_roundtrip, harrow, parseTensorType_roundtrip,
      hts, bind, Option.bind, pure, toString]
    dsimp only [outTy]
    rw [hrt]
    have hann_eq : (annotation == "(" ++ ppTensorType ty ++ ") -> " ++ ppTensorType outTy) = true := by
      simp [annotation, String.append_assoc]
    simp [outTy, tensorType_beq_refl, hann_eq]

theorem parseStableHLOOp_dotGeneral_roundtrip (tenv : TypeEnv) (d a b : String)
    (lb rb lc rc shape : List Nat) (hd : CanonicalSSAName d) (ha : CanonicalSSAName a)
    (hb : CanonicalSSAName b) (hlb : lb = []) (hrb : rb = [])
    (ht : (resultTypeOf tenv (.dotGeneral d a b lb rb lc rc shape)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.dotGeneral d a b lb rb lc rc shape)) =
      some (.dotGeneral d a b lb rb lc rc shape) := by
  subst hlb; subst hrb
  cases hta : tenv a with
  | none => simp [resultTypeOf, hta] at ht
  | some ta =>
    cases htb : tenv b with
    | none => simp [resultTypeOf, hta, htb] at ht
    | some tb =>
      have hrt : resultTypeOf tenv (.dotGeneral d a b [] [] lc rc shape) = some { ta with shape := shape } := by
        cases hok1 : dotOperandOk ta.shape [] lc with
        | error _ => simp [resultTypeOf, hta, htb, hok1] at ht
        | ok lf =>
          cases hok2 : dotOperandOk tb.shape [] rc with
          | error _ => simp [resultTypeOf, hta, htb, hok1, hok2] at ht
          | ok rf =>
            unfold resultTypeOf at ht ⊢
            simp only [hta, htb, hok1, hok2] at ht ⊢
            split at ht
            · rename_i hcond; simp only [hcond, ↓reduceIte]
            · simp at ht
      let outTy : TensorType := { ta with shape := shape }
      let contraction := ppNatList lc ++ " x " ++ ppNatList rc
      let dotPayload := "%" ++ a ++ ", %" ++ b ++ ", contracting_dims = " ++ contraction
      let suffix := "dot_general " ++ dotPayload
      let operation := "%" ++ d ++ " = stablehlo." ++ suffix
      let annotation := "(" ++ ppTensorType ta ++ ", " ++ ppTensorType tb ++ ") -> " ++ ppTensorType outTy
      have hpp : ppStableHLOOp tenv (.dotGeneral d a b [] [] lc rc shape) = operation ++ " : " ++ annotation := by
        apply String.ext_iff.mpr
        simp [ppStableHLOOp, hrt, hta, htb, ppDot, operation, suffix, dotPayload, contraction,
          annotation, outTy, toString, String.toList_append]
      have hcolon_op : ':' ∉ operation.toList := by
        simp [operation, suffix, dotPayload, contraction, String.toList_append,
          ssaName_excludes d hd ':' rfl, ssaName_excludes a ha ':' rfl, ssaName_excludes b hb ':' rfl,
          ppNatList_excludes lc ':' rfl, ppNatList_excludes rc ':' rfl]
      have hcolon_ann : ':' ∉ annotation.toList := by
        simp [annotation, String.toList_append, tensorType_excludes ta ':' rfl,
          tensorType_excludes tb ':' rfl, tensorType_excludes outTy ':' rfl]
      have hsplit_ann : parseHLOFields " : " (operation ++ " : " ++ annotation) = some [operation, annotation] := by
        simpa using parseHLOFields_pair_second ' ' ':' " " operation annotation
          (by decide) hcolon_op ':' (by decide) hcolon_ann
      have hdot_suf : '.' ∉ suffix.toList := by
        simp [suffix, dotPayload, contraction, String.toList_append,
          ssaName_excludes a ha '.' rfl, ssaName_excludes b hb '.' rfl,
          ppNatList_excludes lc '.' rfl, ppNatList_excludes rc '.' rfl]
      have hcmp : parseHLOFields " = stablehlo.compare " operation = some [operation] := by
        simpa [operation, String.append_assoc] using
          parseHLOFields_stablehlo_nonmatch "compare " d suffix hd hdot_suf
            (by simp [suffix, dotPayload, String.toList_append, stripPrefixChars])
      have hsel : parseHLOFields " = stablehlo.select " operation = some [operation] := by
        simpa [operation, String.append_assoc] using
          parseHLOFields_stablehlo_nonmatch "select " d suffix hd hdot_suf
            (by simp [suffix, dotPayload, String.toList_append, stripPrefixChars])
      have hst : parseHLOFields " = stablehlo." operation = some ["%" ++ d, suffix] := by
        simpa [operation, String.append_assoc] using
          parseHLOFields_pair_head ' ' "= stablehlo." ("%" ++ d) suffix
            (by simp [String.toList_append, ssaName_excludes d hd ' ' rfl]) '.' (by decide) hdot_suf
      let payload := "stablehlo." ++ suffix
      have heq_rhs : '=' ∉ contraction.toList := by
        simp [contraction, String.toList_append, ppNatList_excludes lc '=' rfl, ppNatList_excludes rc '=' rfl]
      have hdims_none : parseHLOFields ", dims = " payload = some [payload] := by
        unfold parseHLOFields
        let sepTail := " dims = ".toList
        have htail_scan : scanHLOFields (',' :: sepTail) (contraction.toList.length + 1) contraction.toList =
            some [contraction.toList] :=
          scanHLOFields_single_of_absent (',' :: sepTail) contraction.toList (contraction.toList.length + 1)
            (by decide) '=' (by decide) heq_rhs (by omega)
        let ckw := " contracting_dims = ".toList
        have hckw := scanHLOFields_chunk ',' sepTail ckw contraction.toList
          (ckw.length + contraction.toList.length + 1) (by decide) (by dsimp [ckw]; omega)
        have hckw_sub : ckw.length + contraction.toList.length + 1 - ckw.length = contraction.toList.length + 1 := by omega
        rw [hckw_sub, htail_scan] at hckw
        simp only [Option.bind] at hckw
        have hstep2 := scanHLOFields_cons_nonmatch (',' :: sepTail) ',' (ckw ++ contraction.toList)
          (ckw.length + contraction.toList.length + 1) (ckw ++ contraction.toList) []
          (by decide) (by simp [sepTail, ckw, stripPrefixChars]) hckw
        let pb := (" %" ++ b).toList
        have hpb := scanHLOFields_chunk ',' sepTail pb (',' :: (ckw ++ contraction.toList))
          (pb.length + (ckw.length + contraction.toList.length + 2))
          (by simp [pb, String.toList_append, ssaName_excludes b hb ',' rfl]) (by omega)
        have hpb_sub : pb.length + (ckw.length + contraction.toList.length + 2) - pb.length =
            ckw.length + contraction.toList.length + 2 := by omega
        rw [hpb_sub, hstep2] at hpb
        simp only [Option.bind] at hpb
        have hstep1 := scanHLOFields_cons_nonmatch (',' :: sepTail) ',' (pb ++ (',' :: (ckw ++ contraction.toList)))
          (pb.length + (ckw.length + contraction.toList.length + 2))
          (pb ++ (',' :: (ckw ++ contraction.toList))) []
          (by decide) (by simp [sepTail, pb, String.toList_append, stripPrefixChars]) hpb
        let pa := ("stablehlo.dot_general %" ++ a).toList
        have hpa := scanHLOFields_chunk ',' sepTail pa (',' :: (pb ++ (',' :: (ckw ++ contraction.toList))))
          (pa.length + (pb.length + (ckw.length + contraction.toList.length + 2) + 1))
          (by simp [pa, String.toList_append, ssaName_excludes a ha ',' rfl]) (by omega)
        have hpa_sub : pa.length + (pb.length + (ckw.length + contraction.toList.length + 2) + 1) - pa.length =
            pb.length + (ckw.length + contraction.toList.length + 2) + 1 := Nat.add_sub_cancel_left _ _
        rw [hpa_sub, hstep1] at hpa
        simp only [Option.bind] at hpa
        have hp_chars : payload.toList = pa ++ (',' :: (pb ++ (',' :: (ckw ++ contraction.toList)))) := by
          simp [payload, suffix, dotPayload, pa, pb, ckw, String.toList_append, List.append_assoc]
        have hp_len : payload.toList.length + 1 =
            pa.length + (pb.length + (ckw.length + contraction.toList.length + 2) + 1) := by
          rw [hp_chars]; simp only [List.length_append, List.length_cons]; omega
        rw [hp_len, hp_chars]
        change (scanHLOFields (',' :: sepTail) _ _).map _ = _
        rw [hpa]
        simp only [Option.map_some, List.map_cons, List.map_nil]
        congr 2
        apply String.ext_iff.mpr
        rw [String.toList_ofList, hp_chars]
      obtain ⟨sp1, sp2, hsp_dot⟩ : ∃ f fs, parseHLOFields " " payload = some ("stablehlo.dot_general" :: f :: fs) := by
        have hp_sp : payload = "stablehlo.dot_general" ++ " " ++ dotPayload := by
          apply String.ext_iff.mpr; simp [payload, suffix, String.toList_append]
        rw [hp_sp]
        simpa using parseHLOFields_head_char ' ' "" "stablehlo.dot_general" dotPayload (by decide)
      obtain ⟨pct1, pct2, hpct_dot⟩ : ∃ f fs, parseHLOFields " %" payload = some ("stablehlo.dot_general" :: f :: fs) := by
        let restPct := a ++ ", %" ++ b ++ ", contracting_dims = " ++ contraction
        have hp_pct : payload = "stablehlo.dot_general" ++ " %" ++ restPct := by
          apply String.ext_iff.mpr; simp [payload, suffix, dotPayload, restPct, String.toList_append]
        rw [hp_pct]
        simpa using parseHLOFields_head_second ' ' '%' "" "stablehlo.dot_general" restPct (by decide) (by decide)
      have hdot_op : parseHLOFields " = stablehlo.dot_general " operation = some ["%" ++ d, dotPayload] := by
        have hp := parseHLOFields_pair_head ' ' "= stablehlo.dot_general " ("%" ++ d) dotPayload
          (by simp [String.toList_append, ssaName_excludes d hd ' ' rfl]) '.' (by decide)
          (by simp [dotPayload, contraction, String.toList_append, ssaName_excludes a ha '.' rfl,
            ssaName_excludes b hb '.' rfl, ppNatList_excludes lc '.' rfl, ppNatList_excludes rc '.' rfl])
        have heq : operation = "%" ++ d ++ " = stablehlo.dot_general " ++ dotPayload := by
          apply String.ext_iff.mpr; simp [operation, suffix, String.toList_append]
        rw [heq]; simpa [String.append_assoc] using hp
      have hcdims : parseHLOFields ", contracting_dims = " dotPayload =
          some ["%" ++ a ++ ", %" ++ b, contraction] := by
        unfold parseHLOFields
        let sepTail := " contracting_dims = ".toList
        let rf := sepTail.length + contraction.toList.length + 1
        have htail_scan : scanHLOFields (',' :: sepTail) rf contraction.toList =
            some [contraction.toList] :=
          scanHLOFields_single_of_absent (',' :: sepTail) contraction.toList rf
            (by decide) '=' (by decide) heq_rhs (by dsimp [rf]; omega)
        have hdelim : scanHLOFields (',' :: sepTail) (rf + 1)
            ((',' :: sepTail) ++ contraction.toList) = some [[], contraction.toList] := by
          rw [scanHLOFields_delimiter (',' :: sepTail) contraction.toList rf (by decide),
            htail_scan]; rfl
        let pb := (" %" ++ b).toList
        have hpb := scanHLOFields_chunk ',' sepTail pb ((',' :: sepTail) ++ contraction.toList)
          (pb.length + (rf + 1))
          (by simp [pb, String.toList_append, ssaName_excludes b hb ',' rfl]) (by omega)
        have hpb_sub : pb.length + (rf + 1) - pb.length = rf + 1 := Nat.add_sub_cancel_left _ _
        rw [hpb_sub, hdelim] at hpb
        simp only [Option.bind, List.append_nil] at hpb
        have hstep1 := scanHLOFields_cons_nonmatch (',' :: sepTail) ',' (pb ++ ((',' :: sepTail) ++ contraction.toList))
          (pb.length + (rf + 1)) pb [contraction.toList]
          (by decide) (by simp [sepTail, pb, String.toList_append, stripPrefixChars]) hpb
        let pa := ("%" ++ a).toList
        have hpa := scanHLOFields_chunk ',' sepTail pa (',' :: (pb ++ ((',' :: sepTail) ++ contraction.toList)))
          (pa.length + (pb.length + (rf + 1) + 1))
          (by simp [pa, String.toList_append, ssaName_excludes a ha ',' rfl]) (by omega)
        have hpa_sub : pa.length + (pb.length + (rf + 1) + 1) - pa.length =
            pb.length + (rf + 1) + 1 := Nat.add_sub_cancel_left _ _
        rw [hpa_sub, hstep1] at hpa
        simp only [Option.bind] at hpa
        have hdp_chars : dotPayload.toList = pa ++ (',' :: (pb ++ ((',' :: sepTail) ++ contraction.toList))) := by
          simp [dotPayload, pa, pb, sepTail, String.toList_append, List.append_assoc]
        have hdp_len : dotPayload.toList.length + 1 =
            pa.length + (pb.length + (rf + 1) + 1) := by
          rw [hdp_chars]; dsimp only [rf]; simp only [List.length_append, List.length_cons]; omega
        rw [hdp_len, hdp_chars]
        change (scanHLOFields (',' :: sepTail) _ _).map _ = _
        rw [hpa]
        simp only [Option.map_some, List.map_cons, List.map_nil, String.ofList_toList]
        congr 2
        apply String.ext_iff.mpr
        simp [pa, pb, String.toList_append]
      have hab_args : parseHLOFields ", " ("%" ++ a ++ ", %" ++ b) = some ["%" ++ a, "%" ++ b] := by
        have hp := parseHLOFields_intercalate_head ',' " " ["%" ++ a, "%" ++ b] (by simp) (by
          intro x hx; simp at hx; rcases hx with rfl | rfl
          · simp [String.toList_append, ssaName_excludes a ha ',' rfl]
          · simp [String.toList_append, ssaName_excludes b hb ',' rfl])
        have heq : "%" ++ a ++ ", %" ++ b = String.intercalate ", " ["%" ++ a, "%" ++ b] := by
          apply String.ext_iff.mpr; simp [String.toList_append]
        rw [heq]; simpa using hp
      have hxc : parseHLOFields " x " contraction = some [ppNatList lc, ppNatList rc] := by
        simpa [contraction, String.append_assoc] using
          parseHLOFields_pair_second ' ' 'x' " " (ppNatList lc) (ppNatList rc)
            (by decide) (ppNatList_excludes lc 'x' rfl) 'x' (by decide) (ppNatList_excludes rc 'x' rfl)
      have harrow : parseHLOFields " -> " annotation =
          some ["(" ++ ppTensorType ta ++ ", " ++ ppTensorType tb ++ ")", ppTensorType outTy] := by
        simpa [annotation, String.append_assoc] using
          parseHLOFields_pair_second ' ' '-' "> " ("(" ++ ppTensorType ta ++ ", " ++ ppTensorType tb ++ ")") (ppTensorType outTy)
            (by decide) (by simp [String.toList_append, tensorType_excludes ta '-' rfl, tensorType_excludes tb '-' rfl])
            '-' (by decide) (tensorType_excludes outTy '-' rfl)
      rw [hpp]
      unfold parseStableHLOOp
      cases sp2 <;> cases pct2 <;>
        simp only [hsplit_ann, hcmp, hsel, hst, hd.parse_roundtrip d,
          show "stablehlo." ++ suffix = payload from rfl, hdims_none, hsp_dot, hpct_dot,
          hdot_op, hcdims, hab_args, ha.parse_roundtrip a, hb.parse_roundtrip b,
          hxc, parseNatList_roundtrip, harrow, parseTensorType_roundtrip,
          hta, htb, bind, Option.bind, pure, toString]
      all_goals (
        dsimp only [outTy]
        rw [hrt]
        have hann_eq : (annotation == "(" ++ ppTensorType ta ++ ", " ++ ppTensorType tb ++ ") -> " ++ ppTensorType outTy) = true := by
          simp [annotation, String.append_assoc]
        simp [outTy, tensorType_beq_refl, hann_eq])

/-! ### Slice roundtrip -/

private def isSliceRangeChar (c : Char) : Bool :=
  c.isDigit || c == ':' || c == ',' || c == ' '

private def hasNoSpaceColon : List Char → Bool
  | [] => true
  | [_] => true
  | a :: b :: cs => !(a == ' ' && b == ':') && hasNoSpaceColon (b :: cs)

private theorem hasNoSpaceColon_of_no_colon :
    ∀ xs : List Char, ':' ∉ xs → hasNoSpaceColon xs = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: cs, h => by
    have hb : (b == ':') = false := beq_eq_false_iff_ne.mpr (fun hb => h (by subst hb; simp))
    have ht : ':' ∉ b :: cs := fun hm => h (by simp [hm])
    simp [hasNoSpaceColon, hb, hasNoSpaceColon_of_no_colon (b :: cs) ht]

private theorem hasNoSpaceColon_of_no_space :
    ∀ xs : List Char, ' ' ∉ xs → hasNoSpaceColon xs = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: cs, h => by
    have ha : (a == ' ') = false := beq_eq_false_iff_ne.mpr (fun ha => h (by subst ha; simp))
    have ht : ' ' ∉ b :: cs := fun hm => h (by simp [hm])
    simp [hasNoSpaceColon, ha, hasNoSpaceColon_of_no_space (b :: cs) ht]

private theorem hasNoSpaceColon_append :
    ∀ (xs ys : List Char),
      hasNoSpaceColon xs = true → hasNoSpaceColon ys = true →
      (xs.getLast? ≠ some ' ' ∨ ys.head? ≠ some ':') →
      hasNoSpaceColon (xs ++ ys) = true
  | [], ys, _, hy, _ => hy
  | [x], [], _, _, _ => rfl
  | [x], y :: ys, _, hy, hbd => by
    rcases hbd with h1 | h2
    · have hx : (x == ' ') = false := beq_eq_false_iff_ne.mpr (fun he => h1 (by simp [he]))
      simp only [List.cons_append, List.nil_append, hasNoSpaceColon, hx, Bool.false_and,
        Bool.not_false, Bool.true_and]
      exact hy
    · have hy' : (y == ':') = false := beq_eq_false_iff_ne.mpr (fun he => h2 (by simp [he]))
      simp only [List.cons_append, List.nil_append, hasNoSpaceColon, hy', Bool.and_false,
        Bool.not_false, Bool.true_and]
      exact hy
  | x :: x2 :: xs, ys, hx, hy, hbd => by
    simp only [hasNoSpaceColon, Bool.and_eq_true] at hx
    have hlast : (x :: x2 :: xs).getLast? = (x2 :: xs).getLast? := List.getLast?_cons_cons
    have ih := hasNoSpaceColon_append (x2 :: xs) ys hx.2 hy (by rwa [← hlast])
    simpa [hasNoSpaceColon, hx.1] using ih

private theorem no_space_colon_strip_none :
    ∀ (xs : List Char), hasNoSpaceColon xs = true → xs.getLast? ≠ some ' ' →
      ∀ a b rest, xs = a ++ b → b ≠ [] → stripPrefixChars [' ', ':', ' '] (b ++ rest) = none
  | [], _, _, a, b, _, he, hb => by
    have := List.append_eq_nil_iff.mp he.symm; exact False.elim (hb this.2)
  | [x], _, hlast, a, b, rest, he, hb => by
    have hx : (' ' == x) = false := beq_eq_false_iff_ne.mpr (fun h => hlast (by simp [h.symm]))
    rcases a with _ | ⟨a0, as⟩
    · simp at he; subst he; simp [stripPrefixChars, hx]
    · simp at he; obtain ⟨_, hnil⟩ := he; exact False.elim (hb hnil.2)
  | x :: y :: xs, hok, hlast, a, b, rest, he, hb => by
    simp only [hasNoSpaceColon, Bool.and_eq_true] at hok
    have hlast' : (y :: xs).getLast? ≠ some ' ' := by rwa [List.getLast?_cons_cons] at hlast
    cases a with
    | nil =>
      simp at he; subst he
      simp only [List.cons_append, stripPrefixChars]
      cases hx : (' ' == x)
      · rfl
      · have hx' : x = ' ' := (beq_iff_eq.mp hx).symm
        subst hx'
        have hy : (':' == y) = false := by
          cases hyb : (':' == y)
          · rfl
          · have hy' : y = ':' := (beq_iff_eq.mp hyb).symm
            subst hy'; simp at hok
        simp [hy]
    | cons a0 as =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact no_space_colon_strip_none (y :: xs) hok.2 hlast' as b rest he.2 hb

private theorem nat_repr_head_ne_colon (n : Nat) : (n.repr.toList).head? ≠ some ':' := by
  cases h : n.repr.toList with
  | nil =>
    have hn : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
    rw [← @Nat.toList_repr n, h] at hn; exact False.elim (hn rfl)
  | cons c cs =>
    simp only [List.head?_cons, ne_eq, Option.some.injEq]
    intro hc; subst hc
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega)
      (by rw [← @Nat.toList_repr n, h]; exact List.mem_cons_self)
    simp at hd

private theorem ppSliceRanges_props :
    ∀ (starts limits strides : List Nat) (r : String),
      r ∈ ppSliceRanges starts limits strides →
      ' ' ∉ r.toList ∧ ',' ∉ r.toList ∧ r.toList.all isSliceRangeChar = true ∧
      r.toList.head? ≠ some ':' ∧ r.toList ≠ []
  | st :: sts, lm :: lms, sr :: srs, r, hr => by
    simp only [ppSliceRanges, List.mem_cons] at hr
    have hnat_nosp (m : Nat) : ' ' ∉ m.repr.toList := by
      intro hm; have := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega) (by simpa [Nat.toList_repr] using hm); simp at this
    have hnat_nocom (m : Nat) : ',' ∉ m.repr.toList := by
      intro hm; have := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega) (by simpa [Nat.toList_repr] using hm); simp at this
    have hnat_all (m : Nat) : m.repr.toList.all isSliceRangeChar = true := by
      apply List.all_eq_true.mpr; intro c hc
      have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega) (by simpa [Nat.toList_repr] using hc)
      simp [isSliceRangeChar, hd]
    rcases hr with rfl | hr
    · have hstr : (s!"{st}:{lm}:{sr}").toList = st.repr.toList ++ (':' :: lm.repr.toList) ++ (':' :: sr.repr.toList) := by
        simp [toString, String.toList_append, List.append_assoc]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hstr]; simp only [List.mem_append, List.mem_cons, not_or]
        exact ⟨⟨hnat_nosp st, by decide, hnat_nosp lm⟩, by decide, hnat_nosp sr⟩
      · rw [hstr]; simp only [List.mem_append, List.mem_cons, not_or]
        exact ⟨⟨hnat_nocom st, by decide, hnat_nocom lm⟩, by decide, hnat_nocom sr⟩
      · rw [hstr]; simp only [List.all_append, List.all_cons, Bool.and_eq_true]
        exact ⟨⟨hnat_all st, by decide, hnat_all lm⟩, by decide, hnat_all sr⟩
      · rw [hstr]
        cases hst : st.repr.toList with
        | nil =>
          have hn : Nat.toDigits 10 st ≠ [] := Nat.toDigits_ne_nil
          rw [← @Nat.toList_repr st, hst] at hn; exact False.elim (hn rfl)
        | cons c cs =>
          have := nat_repr_head_ne_colon st
          simpa [hst] using this
      · rw [hstr]; simp
    · exact ppSliceRanges_props sts lms srs r hr
  | [], _, _, _, hr => by simp [ppSliceRanges] at hr
  | _ :: _, [], _, _, hr => by simp [ppSliceRanges] at hr
  | _ :: _, _ :: _, [], _, hr => by simp [ppSliceRanges] at hr

private theorem sliceRanges_intercalate_noSpaceColon :
    ∀ rs : List String,
      (∀ r ∈ rs, ' ' ∉ r.toList ∧ r.toList.head? ≠ some ':') →
      hasNoSpaceColon ((String.intercalate ", " rs ++ "]").toList) = true
  | [], _ => rfl
  | [r], hr => by
    obtain ⟨hnsp, _⟩ := hr r (by simp)
    rw [String.intercalate_singleton, String.toList_append]
    exact hasNoSpaceColon_append r.toList [']']
      (hasNoSpaceColon_of_no_space r.toList hnsp) rfl (Or.inr (by simp))
  | r1 :: r2 :: rs, hr => by
    obtain ⟨hnsp1, _⟩ := hr r1 (by simp)
    obtain ⟨_, hhd2⟩ := hr r2 (by simp)
    have ih := sliceRanges_intercalate_noSpaceColon (r2 :: rs) (fun u hu => hr u (by simp [hu]))
    have heq : (String.intercalate ", " (r1 :: r2 :: rs) ++ "]").toList =
        (r1.toList ++ [',', ' ']) ++ (String.intercalate ", " (r2 :: rs) ++ "]").toList := by
      rw [String.intercalate_cons_cons]
      simp [String.toList_append, List.append_assoc]
    rw [heq]
    have h1 : hasNoSpaceColon (r1.toList ++ [',', ' ']) = true :=
      hasNoSpaceColon_append r1.toList [',', ' ']
        (hasNoSpaceColon_of_no_space r1.toList hnsp1) rfl (Or.inr (by simp))
    have hhd_rest : ((String.intercalate ", " (r2 :: rs) ++ "]").toList).head? ≠ some ':' := by
      cases hrs : rs with
      | nil =>
        simp only [String.intercalate_singleton, String.toList_append]
        cases hr2 : r2.toList with
        | nil => simp
        | cons c cs => simpa [hr2] using hhd2
      | cons r3 rs' =>
        rw [String.intercalate_cons_cons]
        simp only [String.toList_append, List.append_assoc]
        cases hr2 : r2.toList with
        | nil => simp
        | cons c cs => simpa [hr2] using hhd2
    exact hasNoSpaceColon_append _ _ h1 ih (Or.inr hhd_rest)

theorem parseSliceRanges_roundtrip (starts limits strides : List Nat)
    (h12 : starts.length = limits.length) (h23 : limits.length = strides.length) :
    parseSliceRanges ("[" ++ String.intercalate ", " (ppSliceRanges starts limits strides) ++ "]") =
      some (starts, limits, strides) := by
  let parseOne : String → Option (Nat × Nat × Nat) := fun field => do
    let [start, limit, stride] ← parseHLOFields ":" field | none
    return (← start.toNat?, ← limit.toNat?, ← stride.toNat?)
  have hitem (st lm sr : Nat) : parseOne s!"{st}:{lm}:{sr}" = some (st, lm, sr) := by
    dsimp only [parseOne]
    have hnat_nocol (m : Nat) : ':' ∉ m.repr.toList := by
      intro hm; have := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega) (by simpa [Nat.toList_repr] using hm); simp at this
    have hp := parseHLOFields_intercalate ':' [st.repr, lm.repr, sr.repr] (by simp) (by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> exact hnat_nocol _)
    have hstr : (s!"{st}:{lm}:{sr}" : String) = String.intercalate ":" [st.repr, lm.repr, sr.repr] := by
      apply String.ext_iff.mpr; simp [toString, String.toList_append]
    have hcolon : String.singleton ':' = ":" := rfl
    rw [hcolon] at hp
    rw [hstr, hp]
    simp [bind, Option.bind, pure]
  have hmapM : ∀ (sts lms srs : List Nat), sts.length = lms.length → lms.length = srs.length →
      ∃ triples : List (Nat × Nat × Nat),
        (ppSliceRanges sts lms srs).mapM parseOne = some triples ∧
        triples.map (·.1) = sts ∧ triples.map (·.2.1) = lms ∧ triples.map (·.2.2) = srs := by
    intro sts
    induction sts with
    | nil =>
      intro lms srs hl1 hl2
      cases lms with
      | cons _ _ => simp at hl1
      | nil =>
        cases srs with
        | cons _ _ => simp at hl2
        | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
    | cons st sts ih =>
      intro lms srs hl1 hl2
      cases lms with
      | nil => simp at hl1
      | cons lm lms =>
        cases srs with
        | nil => simp at hl2
        | cons sr srs =>
          obtain ⟨tr, htr, h1, h2, h3⟩ := ih lms srs (by simp at hl1; omega) (by simp at hl2; omega)
          refine ⟨(st, lm, sr) :: tr, ?_, by simp [h1], by simp [h2], by simp [h3]⟩
          simp only [ppSliceRanges, List.mapM_cons]
          rw [hitem st lm sr, htr]; rfl
  obtain ⟨triples, htr, hm1, hm2, hm3⟩ := hmapM starts limits strides h12 h23
  unfold parseSliceRanges
  change (do
    let '[' :: chars := ("[" ++ String.intercalate ", " (ppSliceRanges starts limits strides) ++ "]").toList | none
    let ']' :: rev := chars.reverse | none
    let fields ← if rev.isEmpty then some [] else parseHLOFields ", " (String.ofList rev.reverse)
    let triples ← fields.mapM parseOne
    pure (triples.map Prod.fst, triples.map (fun t : Nat × Nat × Nat => t.2.1), triples.map (fun t : Nat × Nat × Nat => t.2.2))) = _
  cases hne_rs : ppSliceRanges starts limits strides with
  | nil =>
    rw [hne_rs] at htr
    simp only [List.mapM_nil, pure, Option.some.injEq] at htr
    subst htr
    simp [hm1, hm2, hm3]
  | cons r0 rs =>
    have hprops := fun r (hr : r ∈ r0 :: rs) => ppSliceRanges_props starts limits strides r (hne_rs ▸ hr)
    have hne_inter : (String.intercalate ", " (r0 :: rs)).toList.reverse.isEmpty = false := by
      obtain ⟨_, _, _, _, hr0_ne⟩ := hprops r0 (by simp)
      have hne_l : (String.intercalate ", " (r0 :: rs)).toList ≠ [] := by
        cases rs with
        | nil => simpa using hr0_ne
        | cons r1 rs' =>
          rw [String.intercalate_cons_cons]
          simp [String.toList_append, hr0_ne]
      simpa using hne_l
    have hp := parseHLOFields_intercalate_head ',' " " (r0 :: rs) (by simp) (by
      intro r hr; exact (hprops r hr).2.1)
    simp only [String.toList_append, String.reduceToList, List.cons_append, List.nil_append,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_reverse,
      hne_inter, Bool.false_eq_true, ↓reduceIte, String.ofList_toList]
    simp only [String.singleton_eq_ofList, String.reduceOfList, String.reduceAppend] at hp
    rw [hp, ← hne_rs]
    dsimp only [bind, Option.bind, pure]
    rw [htr]
    simp [hm1, hm2, hm3]

theorem parseStableHLOOp_slice_roundtrip (tenv : TypeEnv) (d s : String)
    (starts limits strides : List Nat) (hd : CanonicalSSAName d) (hs : CanonicalSSAName s)
    (ht : (resultTypeOf tenv (.slice d s starts limits strides)).isSome = true) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.slice d s starts limits strides)) =
      some (.slice d s starts limits strides) := by
  cases hts : tenv s with
  | none => simp [resultTypeOf, hts] at ht
  | some sty =>
    have hsl : starts.length = sty.shape.length ∧ limits.length = sty.shape.length ∧
        strides.length = sty.shape.length ∧
        ∃ oty, resultTypeOf tenv (.slice d s starts limits strides) = some oty := by
      cases hrt : resultTypeOf tenv (.slice d s starts limits strides) with
      | none => simp [hrt] at ht
      | some oty =>
        refine ⟨?_, ?_, ?_, oty, rfl⟩
        all_goals (
          unfold resultTypeOf at hrt
          simp only [hts, Option.bind_some] at hrt
          split at hrt
          · simp at hrt
          · rename_i hlen_ok
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hlen_ok
            omega)
    rcases hsl with ⟨hl1, hl2, hl3, oty, hrt⟩
    let inner := String.intercalate ", " (ppSliceRanges starts limits strides)
    let suffix := "slice %" ++ s ++ " [" ++ inner ++ "]"
    let operation := "%" ++ d ++ " = stablehlo." ++ suffix
    let annotation := "(" ++ ppTensorType sty ++ ") -> " ++ ppTensorType oty
    have hpp : ppStableHLOOp tenv (.slice d s starts limits strides) = operation ++ " : " ++ annotation := by
      apply String.ext_iff.mpr
      simp [ppStableHLOOp, hts, hrt, operation, suffix, inner, annotation, toString, String.toList_append]
    have hinner_chars : inner.toList.all isSliceRangeChar = true :=
      intercalate_all ", " (ppSliceRanges starts limits strides) isSliceRangeChar (by decide)
        (fun r hr => (ppSliceRanges_props starts limits strides r hr).2.2.1)
    have hinner_excl (c : Char) (hc : isSliceRangeChar c = false) : c ∉ inner.toList := by
      intro hm; have := List.all_eq_true.mp hinner_chars c hm; simp [hc] at this
    have hcolon_ann : ':' ∉ annotation.toList := by
      simp [annotation, String.toList_append, tensorType_excludes sty ':' rfl, tensorType_excludes oty ':' rfl]
    have hop_nsc : hasNoSpaceColon operation.toList = true := by
      let preOp := "%" ++ d ++ " = stablehlo.slice %" ++ s ++ " ["
      have hpre_nocol : ':' ∉ preOp.toList := by
        simp [preOp, String.toList_append, ssaName_excludes d hd ':' rfl, ssaName_excludes s hs ':' rfl]
      have hpre_last : preOp.toList.getLast? ≠ some ' ' := by
        have hch : preOp.toList = ("%" ++ d ++ " = stablehlo.slice %" ++ s ++ " ").toList ++ ['['] := by
          simp [preOp, String.toList_append, List.append_assoc]
        rw [hch, List.getLast?_concat]; decide
      have hrng_nsc : hasNoSpaceColon (inner ++ "]").toList = true :=
        sliceRanges_intercalate_noSpaceColon _ (fun r hr =>
          ⟨(ppSliceRanges_props starts limits strides r hr).1,
           (ppSliceRanges_props starts limits strides r hr).2.2.2.1⟩)
      have hop_eq : operation.toList = preOp.toList ++ (inner ++ "]").toList := by
        simp [operation, suffix, preOp, String.toList_append, List.append_assoc]
      rw [hop_eq]
      exact hasNoSpaceColon_append _ _ (hasNoSpaceColon_of_no_colon _ hpre_nocol) hrng_nsc (Or.inl hpre_last)
    have hop_last : operation.toList.getLast? ≠ some ' ' := by
      have hop_end : operation.toList = ("%" ++ d ++ " = stablehlo.slice %" ++ s ++ " [" ++ inner).toList ++ [']'] := by
        simp [operation, suffix, String.toList_append, List.append_assoc]
      rw [hop_end, List.getLast?_concat]; decide
    have hsplit_ann : parseHLOFields " : " (operation ++ " : " ++ annotation) = some [operation, annotation] :=
      parseHLOFields_pair_of_no_prefix " : " operation annotation (by decide)
        (fun a b he hb => no_space_colon_strip_none operation.toList hop_nsc hop_last a b _ he hb)
        ':' (by decide) hcolon_ann
    have hdot_suf : '.' ∉ suffix.toList := by
      simp [suffix, String.toList_append, ssaName_excludes s hs '.' rfl, hinner_excl '.' rfl]
    have hcmp : parseHLOFields " = stablehlo.compare " operation = some [operation] := by
      simpa [operation, String.append_assoc] using
        parseHLOFields_stablehlo_nonmatch "compare " d suffix hd hdot_suf
          (by simp [suffix, String.toList_append, stripPrefixChars])
    have hsel : parseHLOFields " = stablehlo.select " operation = some [operation] := by
      simpa [operation, String.append_assoc] using
        parseHLOFields_stablehlo_nonmatch "select " d suffix hd hdot_suf
          (by simp [suffix, String.toList_append, stripPrefixChars])
    have hst : parseHLOFields " = stablehlo." operation = some ["%" ++ d, suffix] := by
      simpa [operation, String.append_assoc] using
        parseHLOFields_pair_head ' ' "= stablehlo." ("%" ++ d) suffix
          (by simp [String.toList_append, ssaName_excludes d hd ' ' rfl]) '.' (by decide) hdot_suf
    let payload := "stablehlo." ++ suffix
    have hdims_none : parseHLOFields ", dims = " payload = some [payload] :=
      parseHLOFields_single_of_absent ", dims = " payload (by decide) '=' (by decide)
        (by simp [payload, suffix, String.toList_append, ssaName_excludes s hs '=' rfl, hinner_excl '=' rfl])
    obtain ⟨sp1, sp2, hsp_sl⟩ : ∃ f fs, parseHLOFields " " payload = some ("stablehlo.slice" :: f :: fs) := by
      have hp_sp : payload = "stablehlo.slice" ++ " " ++ ("%" ++ s ++ " [" ++ inner ++ "]") := by
        apply String.ext_iff.mpr; simp [payload, suffix, String.toList_append]
      rw [hp_sp]
      simpa using parseHLOFields_head_char ' ' "" "stablehlo.slice" _ (by decide)
    have hpct_sl : parseHLOFields " %" payload = some ["stablehlo.slice", s ++ " [" ++ inner ++ "]"] := by
      have hp := parseHLOFields_pair_second ' ' '%' "" "stablehlo.slice" (s ++ " [" ++ inner ++ "]")
        (by decide) (by decide) '%' (by decide)
        (by simp [String.toList_append, ssaName_excludes s hs '%' rfl, hinner_excl '%' rfl])
      have heq : payload = "stablehlo.slice" ++ " %" ++ (s ++ " [" ++ inner ++ "]") := by
        apply String.ext_iff.mpr; simp [payload, suffix, String.toList_append]
      rw [heq]; simpa [String.append_assoc] using hp
    have hbrk_sl : parseHLOFields " [" (s ++ " [" ++ inner ++ "]") = some [s, inner ++ "]"] := by
      have hp := parseHLOFields_pair_head ' ' "[" s (inner ++ "]")
        (ssaName_excludes s hs ' ' rfl) '[' (by decide)
        (by simp [String.toList_append, hinner_excl '[' rfl])
      have heq : s ++ " [" ++ inner ++ "]" = s ++ " [" ++ (inner ++ "]") := by
        apply String.ext_iff.mpr; simp [String.toList_append]
      rw [heq]; simpa [String.append_assoc] using hp
    have hrng : parseSliceRanges ("[" ++ (inner ++ "]")) = some (starts, limits, strides) := by
      simpa [inner, String.append_assoc] using
        parseSliceRanges_roundtrip starts limits strides (hl1.trans hl2.symm) (hl2.trans hl3.symm)
    have harrow : parseHLOFields " -> " annotation =
        some ["(" ++ ppTensorType sty ++ ")", ppTensorType oty] := by
      simpa [annotation, String.append_assoc] using
        parseHLOFields_pair_second ' ' '-' "> " ("(" ++ ppTensorType sty ++ ")") (ppTensorType oty)
          (by decide) (by simp [String.toList_append, tensorType_excludes sty '-' rfl])
          '-' (by decide) (tensorType_excludes oty '-' rfl)
    rw [hpp]
    unfold parseStableHLOOp
    cases sp2 <;>
      simp only [hsplit_ann, hcmp, hsel, hst, hd.parse_roundtrip d,
        show "stablehlo." ++ suffix = payload from rfl, hdims_none, hsp_sl, hpct_sl,
        hbrk_sl, hs.parse_roundtrip s, hrng, harrow, parseTensorType_roundtrip,
        bind, Option.bind, pure, toString]
    all_goals simp [hts, hrt, tensorType_beq_refl, annotation, String.append_assoc]

/-! ### Constant roundtrip -/

private def denseBodyUi64 (v : TensorVal) : String :=
  if v.data.size == 0 then ""
  else if v.data.all (· == v.data[0]!) then v.data[0]!.toNat.repr
  else ppNatList (v.data.toList.map BitVec.toNat)

private theorem ppDense_ui64_eq (v : TensorVal) (helem : v.ty.elem = .ui64)
    (hshape : v.ty.shape = [] ∨ ∃ n, v.ty.shape = [n]) (hsz : v.data.size = v.ty.numElements) :
    ppDense v.ty (v.data.map (maskWidth (storageBitWidth v.ty.elem))) =
      "dense<" ++ denseBodyUi64 v ++ ">" := by
  have hmw : maskWidth (storageBitWidth v.ty.elem) = id := by
    rw [helem]; funext x; rfl
  rw [hmw, Array.map_id]
  have hbit : ppBit v.ty.elem = fun x : BitVec 64 => x.toNat.repr := by
    rw [helem]; funext x; rfl
  unfold ppDense denseBodyUi64
  by_cases hz : (v.data.size == 0) = true
  · simp [hz]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    by_cases hsp : v.data.all (· == v.data[0]!) = true
    · simp [hsp, hbit, toString]
    · simp only [hsp, Bool.false_eq_true, ↓reduceIte]
      have hne0 : v.data.size ≠ 0 := fun h => hz (beq_iff_eq.mpr h)
      have hpos : 0 < v.data.size := by omega
      rcases hshape with hnil | ⟨n, hn⟩
      · have h1 : v.data.toList.length = 1 := by
          rw [Array.length_toList]; simpa [TensorType.numElements, hnil] using hsz
        rcases hlist : v.data.toList with _ | ⟨x, _ | ⟨y, ys⟩⟩
        · simp [hlist] at h1
        · have hv : v.data = #[x] := Array.ext' (by simp [hlist])
          rw [hv] at hsp; simp at hsp
        · simp [hlist] at h1
      · have hnsz : v.data.size = n := by simpa [TensorType.numElements, hn] using hsz
        have hnpos : 0 < n := by omega
        have hn0 : (n == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
        have hstrs_len : (v.data.toList.map (ppBit v.ty.elem)).length = n := by simp [hnsz]
        have hdiv : n / n = 1 := Nat.div_self hnpos
        simp only [hn, List.foldr_cons, List.foldr_nil, hn0, Bool.false_eq_true, ↓reduceIte,
          hstrs_len, hdiv, groupEvery, List.headD_cons]
        simp only [ppNatList, hbit, List.map_map, Function.comp_def, toString]
        rw [List.take_of_length_le (by simp [hnsz])]

private theorem denseBodyUi64_chars (v : TensorVal) :
    (denseBodyUi64 v).toList.all isNatListChar = true := by
  unfold denseBodyUi64
  split
  · rfl
  · split
    · apply List.all_eq_true.mpr; intro c hc
      have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := v.data[0]!.toNat) (by omega) (by omega)
        (by simpa [Nat.toList_repr] using hc)
      simp [isNatListChar, hd]
    · exact ppNatList_chars _

theorem parseStableHLOOp_constant_roundtrip (tenv : TypeEnv) (d : String) (v : TensorVal)
    (hd : CanonicalSSAName d) (helem : v.ty.elem = .ui64)
    (hshape : v.ty.shape = [] ∨ ∃ n, v.ty.shape = [n])
    (hsz : v.data.size = v.ty.numElements) :
    parseStableHLOOp tenv (ppStableHLOOp tenv (.constant d v)) = some (.constant d v) := by
  let body := denseBodyUi64 v
  let suffix := "constant dense<" ++ body ++ ">"
  let operation := "%" ++ d ++ " = stablehlo." ++ suffix
  let annotation := ppTensorType v.ty
  have hpp : ppStableHLOOp tenv (.constant d v) = operation ++ " : " ++ annotation := by
    apply String.ext_iff.mpr
    simp [ppStableHLOOp, ppDense_ui64_eq v helem hshape hsz, operation, suffix, body, annotation,
      toString, String.toList_append]
  have hbody_excl (c : Char) (hc : isNatListChar c = false) : c ∉ body.toList := by
    intro hm; have := List.all_eq_true.mp (denseBodyUi64_chars v) c hm; simp [hc] at this
  have hcolon_op : ':' ∉ operation.toList := by
    simp [operation, suffix, String.toList_append, ssaName_excludes d hd ':' rfl, hbody_excl ':' rfl]
  have hsplit_ann : parseHLOFields " : " (operation ++ " : " ++ annotation) = some [operation, annotation] := by
    simpa using parseHLOFields_pair_second ' ' ':' " " operation annotation
      (by decide) hcolon_op ':' (by decide) (tensorType_excludes v.ty ':' rfl)
  have hdot_suf : '.' ∉ suffix.toList := by
    simp [suffix, String.toList_append, hbody_excl '.' rfl]
  have hcmp : parseHLOFields " = stablehlo.compare " operation = some [operation] := by
    simpa [operation, String.append_assoc] using
      parseHLOFields_stablehlo_nonmatch "compare " d suffix hd hdot_suf
        (by simp [suffix, String.toList_append, stripPrefixChars])
  have hsel : parseHLOFields " = stablehlo.select " operation = some [operation] := by
    simpa [operation, String.append_assoc] using
      parseHLOFields_stablehlo_nonmatch "select " d suffix hd hdot_suf
        (by simp [suffix, String.toList_append, stripPrefixChars])
  have hst : parseHLOFields " = stablehlo." operation = some ["%" ++ d, suffix] := by
    simpa [operation, String.append_assoc] using
      parseHLOFields_pair_head ' ' "= stablehlo." ("%" ++ d) suffix
        (by simp [String.toList_append, ssaName_excludes d hd ' ' rfl]) '.' (by decide) hdot_suf
  let payload := "stablehlo." ++ suffix
  have hdims_none : parseHLOFields ", dims = " payload = some [payload] :=
    parseHLOFields_single_of_absent ", dims = " payload (by decide) '=' (by decide)
      (by simp [payload, suffix, String.toList_append, hbody_excl '=' rfl])
  obtain ⟨sp1, sp2, hsp_c⟩ : ∃ f fs, parseHLOFields " " payload = some ("stablehlo.constant" :: f :: fs) := by
    have hp_sp : payload = "stablehlo.constant" ++ " " ++ ("dense<" ++ body ++ ">") := by
      apply String.ext_iff.mpr; simp [payload, suffix, String.toList_append]
    rw [hp_sp]
    simpa using parseHLOFields_head_char ' ' "" "stablehlo.constant" _ (by decide)
  have hpct_none : parseHLOFields " %" payload = some [payload] :=
    parseHLOFields_single_of_absent " %" payload (by decide) '%' (by decide)
      (by simp [payload, suffix, String.toList_append, hbody_excl '%' rfl])
  have hdotg_none : parseHLOFields " = stablehlo.dot_general " operation = some [operation] := by
    simpa [operation, String.append_assoc] using
      parseHLOFields_stablehlo_nonmatch "dot_general " d suffix hd hdot_suf
        (by simp [suffix, String.toList_append, stripPrefixChars])
  have hconst_op : parseHLOFields " = stablehlo.constant dense<" operation = some ["%" ++ d, body ++ ">"] := by
    have hp := parseHLOFields_pair_head ' ' "= stablehlo.constant dense<" ("%" ++ d) (body ++ ">")
      (by simp [String.toList_append, ssaName_excludes d hd ' ' rfl]) '.' (by decide)
      (by simp [String.toList_append, hbody_excl '.' rfl])
    have heq : operation = "%" ++ d ++ " = stablehlo.constant dense<" ++ (body ++ ">") := by
      apply String.ext_iff.mpr; simp [operation, suffix, String.toList_append]
    rw [heq]; simpa [String.append_assoc] using hp
  have hrev : (body ++ ">").toList.reverse = '>' :: body.toList.reverse := by
    simp [String.toList_append]
  have helem_bne : (v.ty.elem != .ui64) = false := by rw [helem]; rfl
  let ns := v.data.toList.map BitVec.toNat
  have hlen_ns : ns.length = v.ty.numElements := by simp [ns, hsz]
  have hall_lt : ns.all (· < 2 ^ 64) = true := by
    apply List.all_eq_true.mpr; intro m hm
    obtain ⟨bv, _, rfl⟩ := List.mem_map.mp hm
    exact decide_eq_true bv.isLt
  have hbv_arr : (ns.map (BitVec.ofNat 64)).toArray = v.data := by
    have hbv_map : ns.map (BitVec.ofNat 64) = v.data.toList := by
      simp only [ns, List.map_map, Function.comp_def]
      have hid : (fun x : BitVec 64 => BitVec.ofNat 64 x.toNat) = id := by
        funext x; exact BitVec.eq_of_toNat_eq (by simp)
      rw [hid]; exact List.map_id _
    rw [hbv_map, Array.toArray_toList]
  have hmapM_nat : ∀ xs : List Nat, (xs.map Nat.repr).mapM String.toNat? = some xs := by
    intro xs; induction xs <;> simp_all [List.mapM_cons]
  rw [hpp]
  unfold parseStableHLOOp
  simp only [hsplit_ann, hcmp, hsel, hst, hd.parse_roundtrip d,
    show "stablehlo." ++ suffix = payload from rfl,
    hdims_none, hsp_c, hpct_none, hdotg_none, hconst_op,
    annotation, parseTensorType_roundtrip, hrev, helem_bne,
    Bool.false_eq_true, ↓reduceIte, List.reverse_reverse, String.ofList_toList,
    bind, Option.bind, pure]
  split
  · rename_i src makeOp hmatch
    split at hmatch
    · simp_all
    · simp_all
    · split at hmatch <;> simp_all
  · (
    dsimp only [body, denseBodyUi64]
    by_cases hz : (v.data.size == 0) = true
    · have hsz0 : v.data.size = 0 := beq_iff_eq.mp hz
      have hnum0 : v.ty.numElements = 0 := by omega
      have hempty_arr : (List.map (BitVec.ofNat 64) []).toArray = v.data :=
        (Array.eq_empty_of_size_eq_zero hsz0).symm
      simp only [hz, ↓reduceIte, String.isEmpty_iff, hnum0, List.length_nil, bne_self_eq_false,
        List.all_nil, Bool.not_true, Bool.or_self, Bool.false_eq_true, hempty_arr]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      have hne0 : v.data.size ≠ 0 := fun h => hz (beq_iff_eq.mpr h)
      have hpos : 0 < v.data.size := by omega
      by_cases hsp : v.data.all (· == v.data[0]!) = true
      · simp only [hsp, ↓reduceIte]
        let n0 := v.data[0]!.toNat
        have hn0_ne : n0.repr.isEmpty = false := by
          rw [Bool.eq_false_iff, ne_eq, String.isEmpty_iff]
          intro he
          have hn_nil : Nat.toDigits 10 n0 ≠ [] := Nat.toDigits_ne_nil
          rw [← @Nat.toList_repr n0, he] at hn_nil; exact hn_nil rfl
        have htonat : n0.repr.toNat? = some n0 := by simp
        have hall_list : ∀ x ∈ v.data.toList, x = v.data[0]! := by
          intro x hx
          have hmem : x ∈ v.data := Array.mem_def.mpr hx
          exact beq_iff_eq.mp (Array.all_eq_true_iff_forall_mem.mp hsp x hmem)
        have hlist_eq : List.replicate v.ty.numElements v.data[0]! = v.data.toList := by
          rw [← hsz, ← Array.length_toList]
          exact (List.eq_replicate_iff.mpr ⟨rfl, hall_list⟩).symm
        have hns_rep : List.replicate v.ty.numElements n0 = ns := by
          dsimp only [ns, n0]
          rw [← hlist_eq, List.map_replicate]
        simp only [show v.data[0]!.toNat = n0 from rfl, hn0_ne, Bool.false_eq_true, ↓reduceIte,
          htonat, hns_rep]
        rcases hcs : n0.repr.toList with _ | ⟨c0, cs⟩
        · have hn_nil : Nat.toDigits 10 n0 ≠ [] := Nat.toDigits_ne_nil
          rw [← @Nat.toList_repr n0, hcs] at hn_nil; exact False.elim (hn_nil rfl)
        · have hc0 : c0 ≠ '[' := by
            intro hc; subst hc
            have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n0) (by omega) (by omega)
              (by rw [← @Nat.toList_repr n0, hcs]; exact List.mem_cons_self)
            simp at hd
          simp [hc0, hlen_ns, hbv_arr]
          intro x hx
          obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
          exact w.isLt
      · simp only [hsp, Bool.false_eq_true, ↓reduceIte]
        have hlen_ns0 : ns.length = v.data.size := by simp [ns]
        have hns_ne : ns ≠ [] := by
          intro hnil; rw [hnil] at hlen_ns0; simp at hlen_ns0; omega
        have hpp_ne : (ppNatList ns).isEmpty = false := by simp [ppNatList]
        rcases hns_cons : ns with _ | ⟨m0, ms⟩
        · exact False.elim (hns_ne hns_cons)
        · have hp_fields := parseHLOFields_intercalate_head ',' " " ((m0 :: ms).map Nat.repr) (by simp) (by
            intro s hs; obtain ⟨m, _, rfl⟩ := List.mem_map.mp hs
            intro hm; have := Nat.isDigit_of_mem_toDigits (b := 10) (n := m) (by omega) (by omega) (by simpa [Nat.toList_repr] using hm); simp at this)
          simp only [String.singleton_eq_ofList, String.reduceOfList, String.reduceAppend] at hp_fields
          have hpp_list : (ppNatList (m0 :: ms)).toList =
              '[' :: ((String.intercalate ", " ((m0 :: ms).map Nat.repr)).toList ++ [']']) := by
            simp [ppNatList, toString, String.toList_append]
          simp only [show v.data.toList.map BitVec.toNat = ns from rfl, hpp_ne, Bool.false_eq_true, ↓reduceIte]
          rw [hns_cons, hpp_list]
          simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.cons_append, List.nil_append, List.reverse_reverse, String.ofList_toList]
          rw [hp_fields]
          dsimp only
          rw [hmapM_nat, ← hns_cons]
          simp only [hlen_ns, bne_self_eq_false, hall_lt, Bool.not_true, Bool.or_self,
            Bool.false_eq_true, ↓reduceIte, hbv_arr])

/-! ### Full op, body, and FuncOp roundtrip & canonical injectivity -/

theorem parseStableHLOOp_roundtrip (tenv : TypeEnv) (op : StableHLOOp)
    (h : CanonicalStableHLOOp tenv op) :
    parseStableHLOOp tenv (ppStableHLOOp tenv op) = some op := by
  cases op with
  | constant d v =>
    rcases h with ⟨hd, helem, hshape, hsz⟩
    exact parseStableHLOOp_constant_roundtrip tenv d v hd helem hshape hsz
  | add d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inl rfl) hd ha hb ht
  | subtract d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inl rfl) hd ha hb ht
  | multiply d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | divide d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | remainder d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | maximum d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | minimum d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | and d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | or d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | xor d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | shiftLeft d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | shiftRightArithmetic d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl) hd ha hb ht
  | shiftRightLogical d a b =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_binary_roundtrip tenv d a b _ (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr rfl) hd ha hb ht
  | compare d a b dir =>
    rcases h with ⟨hd, ha, hb, ht⟩
    exact parseStableHLOOp_compare_roundtrip tenv d a b dir hd ha hb ht
  | select d p t e =>
    rcases h with ⟨hd, hp, ht, he, hw⟩
    exact parseStableHLOOp_select_roundtrip tenv d p t e hd hp ht he hw
  | broadcastInDim d s shape dims =>
    rcases h with ⟨hd, hs, ht⟩
    exact parseStableHLOOp_broadcastInDim_roundtrip tenv d s shape dims hd hs ht
  | reshape d s shape =>
    rcases h with ⟨hd, hs, ht⟩
    exact parseStableHLOOp_reshape_roundtrip tenv d s shape hd hs ht
  | slice d s starts limits strides =>
    rcases h with ⟨hd, hs, ht⟩
    exact parseStableHLOOp_slice_roundtrip tenv d s starts limits strides hd hs ht
  | dotGeneral d a b lb rb lc rc shape =>
    rcases h with ⟨hd, ha, hb, hlb, hrb, ht⟩
    exact parseStableHLOOp_dotGeneral_roundtrip tenv d a b lb rb lc rc shape hd ha hb hlb hrb ht
  | convert d s elem =>
    rcases h with ⟨hd, hs, ht⟩
    exact parseStableHLOOp_convert_roundtrip tenv d s elem hd hs ht
  | returnOp s =>
    rcases h with ⟨hs, ht⟩
    exact parseStableHLOOp_return_roundtrip tenv s hs ht
  | dynamicSlice _ _ _ _ => exact False.elim h
  | reduce _ _ _ _ _ _ => exact False.elim h

theorem ppStableHLOOp_injective_on_canonical (tenv : TypeEnv) (a b : StableHLOOp)
    (ha : CanonicalStableHLOOp tenv a) (hb : CanonicalStableHLOOp tenv b)
    (h : ppStableHLOOp tenv a = ppStableHLOOp tenv b) : a = b := by
  have hp := congrArg (parseStableHLOOp tenv) h
  rwa [parseStableHLOOp_roundtrip tenv a ha, parseStableHLOOp_roundtrip tenv b hb,
    Option.some.injEq] at hp

theorem parseBody_roundtrip (tenv : TypeEnv) (ops : List StableHLOOp)
    (h : CanonicalBody tenv ops) :
    parseBody tenv (ppBody tenv ops) = some ops := by
  induction ops generalizing tenv with
  | nil => rfl
  | cons op ops ih =>
    exact parseBody_cons tenv _ _ op ops
      (parseStableHLOOp_roundtrip tenv op h.1)
      (ih (bindResult tenv op) h.2)

theorem ppBody_injective_on_canonical (tenv : TypeEnv) (a b : List StableHLOOp)
    (ha : CanonicalBody tenv a) (hb : CanonicalBody tenv b)
    (h : ppBody tenv a = ppBody tenv b) : a = b := by
  have hp := congrArg (parseBody tenv) h
  rwa [parseBody_roundtrip tenv a ha, parseBody_roundtrip tenv b hb,
    Option.some.injEq] at hp

private theorem ppTyped_no_newline (d opStr : String) (ty : Option TensorType)
    (hd : CanonicalSSAName d) (hop : '\n' ∉ opStr.toList) :
    '\n' ∉ (ppTyped d opStr ty).toList := by
  cases ty with
  | none => simp [ppTyped, toString, String.toList_append, ssaName_excludes d hd '\n' rfl, hop]
  | some t =>
    simp [ppTyped, toString, String.toList_append, ssaName_excludes d hd '\n' rfl,
      hop, tensorType_excludes t '\n' rfl]

private theorem ppStableHLOOp_no_newline (tenv : TypeEnv) (op : StableHLOOp)
    (h : CanonicalStableHLOOp tenv op) :
    '\n' ∉ (ppStableHLOOp tenv op).toList := by
  cases op with
  | constant d v =>
    rcases h with ⟨hd, helem, hshape, hsz⟩
    have hbd : '\n' ∉ (denseBodyUi64 v).toList := by
      intro hm; have := List.all_eq_true.mp (denseBodyUi64_chars v) '\n' hm; simp [isNatListChar] at this
    simp [ppStableHLOOp, ppDense_ui64_eq v helem hshape hsz, toString, String.toList_append,
      ssaName_excludes d hd '\n' rfl, hbd, tensorType_excludes v.ty '\n' rfl]
  | add d a b | subtract d a b | multiply d a b | divide d a b | remainder d a b
  | maximum d a b | minimum d a b | and d a b | or d a b | xor d a b
  | shiftLeft d a b | shiftRightArithmetic d a b | shiftRightLogical d a b =>
    rcases h with ⟨hd, ha, hb, _⟩
    exact ppTyped_no_newline d _ _ hd
      (by simp [toString, String.toList_append, ssaName_excludes a ha '\n' rfl, ssaName_excludes b hb '\n' rfl])
  | compare d a b dir =>
    rcases h with ⟨hd, ha, hb, hw⟩
    have hdir : '\n' ∉ (ppCompareDir dir).toList := by cases dir <;> decide
    cases hta : tenv a with
    | none => simp [resultTypeOf, hta] at hw
    | some ty =>
      have hct : '\n' ∉ (ppCompareType ty.elem).toList := by cases ty.elem <;> decide
      cases hrt : resultTypeOf tenv (.compare d a b dir) with
      | none => simp [hrt] at hw
      | some oty =>
        simp [ppStableHLOOp, hta, hrt, ppCompare, toString, String.toList_append,
          ssaName_excludes d hd '\n' rfl, ssaName_excludes a ha '\n' rfl,
          ssaName_excludes b hb '\n' rfl, hdir, hct,
          tensorType_excludes ty '\n' rfl, tensorType_excludes { ty with elem := .i1 } '\n' rfl]
  | select d p t e =>
    rcases h with ⟨hd, hp, ht, he, hw⟩
    cases hrt : resultTypeOf tenv (.select d p t e) with
    | none => simp [hrt] at hw
    | some oty =>
      cases htp : tenv p with
      | none => simp [resultTypeOf, htp] at hrt
      | some pt =>
        cases htt : tenv t with
        | none => simp [resultTypeOf, htp, htt] at hrt
        | some tt =>
          simp [ppStableHLOOp, hrt, htp, htt, toString, String.toList_append,
            ssaName_excludes d hd '\n' rfl, ssaName_excludes p hp '\n' rfl,
            ssaName_excludes t ht '\n' rfl, ssaName_excludes e he '\n' rfl,
            tensorType_excludes pt '\n' rfl, tensorType_excludes tt '\n' rfl]
  | broadcastInDim d s shape dims =>
    rcases h with ⟨hd, hs, hw⟩
    cases hts : tenv s with
    | none => simp [resultTypeOf, hts] at hw
    | some ty =>
      cases hrt : resultTypeOf tenv (.broadcastInDim d s shape dims) with
      | none => simp [hrt] at hw
      | some oty =>
        simp [ppStableHLOOp, hts, hrt, ppBroadcast, toString, String.toList_append,
          ssaName_excludes d hd '\n' rfl, ssaName_excludes s hs '\n' rfl,
          ppNatList_excludes dims '\n' rfl, tensorType_excludes ty '\n' rfl,
          tensorType_excludes { ty with shape := shape } '\n' rfl]
  | reshape d s shape =>
    rcases h with ⟨hd, hs, hw⟩
    cases hts : tenv s with
    | none => simp [resultTypeOf, hts] at hw
    | some ty =>
      cases hrt : resultTypeOf tenv (.reshape d s shape) with
      | none => simp [hrt] at hw
      | some oty =>
        simp [ppStableHLOOp, hts, hrt, toString, String.toList_append,
          ssaName_excludes d hd '\n' rfl, ssaName_excludes s hs '\n' rfl,
          tensorType_excludes ty '\n' rfl, tensorType_excludes { ty with shape := shape } '\n' rfl]
  | slice d s starts limits strides =>
    rcases h with ⟨hd, hs, hw⟩
    have hrng : '\n' ∉ (String.intercalate ", " (ppSliceRanges starts limits strides)).toList := by
      intro hm
      have hc := List.all_eq_true.mp (intercalate_all ", " (ppSliceRanges starts limits strides)
        isSliceRangeChar (by decide) (fun r hr => (ppSliceRanges_props starts limits strides r hr).2.2.1)) '\n' hm
      simp [isSliceRangeChar] at hc
    cases hts : tenv s with
    | none => simp [resultTypeOf, hts] at hw
    | some sty =>
      cases hrt : resultTypeOf tenv (.slice d s starts limits strides) with
      | none => simp [hrt] at hw
      | some oty =>
        simp [-String.toList_intercalate, ppStableHLOOp, hts, hrt, toString, String.toList_append,
          ssaName_excludes d hd '\n' rfl, ssaName_excludes s hs '\n' rfl, hrng,
          tensorType_excludes sty '\n' rfl, tensorType_excludes oty '\n' rfl]
  | dotGeneral d a b lb rb lc rc shape =>
    rcases h with ⟨hd, ha, hb, rfl, rfl, hw⟩
    cases hta : tenv a with
    | none => simp [resultTypeOf, hta] at hw
    | some ta =>
      cases htb : tenv b with
      | none => simp [resultTypeOf, hta, htb] at hw
      | some tb =>
        cases hrt : resultTypeOf tenv (.dotGeneral d a b [] [] lc rc shape) with
        | none => simp [hrt] at hw
        | some oty =>
          simp [ppStableHLOOp, hta, htb, hrt, ppDot, toString, String.toList_append,
            ssaName_excludes d hd '\n' rfl, ssaName_excludes a ha '\n' rfl, ssaName_excludes b hb '\n' rfl,
            ppNatList_excludes lc '\n' rfl, ppNatList_excludes rc '\n' rfl,
            tensorType_excludes ta '\n' rfl, tensorType_excludes tb '\n' rfl,
            tensorType_excludes { ta with shape := shape } '\n' rfl]
  | convert d s elem =>
    rcases h with ⟨hd, hs, hw⟩
    cases hts : tenv s with
    | none => simp [resultTypeOf, hts] at hw
    | some ty =>
      cases hrt : resultTypeOf tenv (.convert d s elem) with
      | none => simp [hrt] at hw
      | some oty =>
        simp [ppStableHLOOp, hts, hrt, toString, String.toList_append,
          ssaName_excludes d hd '\n' rfl, ssaName_excludes s hs '\n' rfl,
          tensorType_excludes ty '\n' rfl, tensorType_excludes { ty with elem := elem } '\n' rfl]
  | returnOp s =>
    rcases h with ⟨hs, hw⟩
    cases hts : tenv s with
    | none => simp [hts] at hw
    | some ty =>
      simp [ppStableHLOOp, hts, toString, String.toList_append,
        ssaName_excludes s hs '\n' rfl, tensorType_excludes ty '\n' rfl]
  | dynamicSlice _ _ _ _ => exact False.elim h
  | reduce _ _ _ _ _ _ => exact False.elim h

private theorem ppBody_no_newline :
    ∀ (tenv : TypeEnv) (ops : List StableHLOOp), CanonicalBody tenv ops →
      ∀ line ∈ ppBody tenv ops, '\n' ∉ line.toList
  | _, [], _, _, hmem => by simp [ppBody] at hmem
  | tenv, op :: ops, ⟨hop, hrest⟩, line, hmem => by
    simp only [ppBody, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp [String.toList_append, ppStableHLOOp_no_newline tenv op hop]
    · exact ppBody_no_newline (bindResult tenv op) ops hrest line hmem

private def isParamFieldChar (c : Char) : Bool :=
  c.isAlphanum || " %_:tensor<>xiufb,".toList.contains c

private theorem paramsStr_chars (params : List (String × TensorType))
    (hp : ∀ p ∈ params, CanonicalSSAName p.1) :
    (String.intercalate ", " (params.map fun (n, ty) => s!"%{n}: {ppTensorType ty}")).toList.all
      isParamFieldChar = true := by
  apply intercalate_all ", " _ isParamFieldChar (by decide)
  intro s hs
  obtain ⟨⟨n, ty⟩, hmem, rfl⟩ := List.mem_map.mp hs
  have hn := hp (n, ty) hmem
  have hn_all : n.toList.all isParamFieldChar = true := by
    apply List.all_eq_true.mpr; intro c hc
    have h1 := List.all_eq_true.mp hn.2 c hc
    rcases Bool.or_eq_true_iff.mp h1 with hal | hus
    · simp [isParamFieldChar, hal]
    · have hc_eq : c = '_' := beq_iff_eq.mp hus; subst hc_eq; decide
  have hty_all : (ppTensorType ty).toList.all isParamFieldChar = true := by
    apply List.all_eq_true.mpr; intro c hc
    have h1 := List.all_eq_true.mp (tensorType_chars ty) c hc
    unfold isTensorTypeChar at h1
    rcases Bool.or_eq_true_iff.mp h1 with hdig | hmemc
    · have hal : c.isAlphanum = true := by simp [Char.isAlphanum, hdig]
      simp [isParamFieldChar, hal]
    · have hsub : ("tensor<>xiufb".toList).all isParamFieldChar = true := by decide
      exact List.all_eq_true.mp hsub c (List.contains_iff_mem.mp hmemc)
  simp only [toString, String.toList_append, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨by decide, hn_all⟩, by decide⟩, hty_all⟩

theorem parseFuncOp_roundtrip (f : FuncOp) (hf : CanonicalFuncOp f) :
    parseFuncOp (ppFuncOp f) = some f := by
  rcases f with ⟨name, params, result, body⟩
  rcases hf with ⟨hname, hparams, hbody⟩
  dsimp only at hname hparams hbody
  let fmtParam : String × TensorType → String := fun (n, ty) => s!"%{n}: {ppTensorType ty}"
  let paramsStr := String.intercalate ", " (params.map fmtParam)
  let tenv0 := params.foldl (fun e (n, ty) => e.bind n ty) TypeEnv.empty
  let header := "  func.func @" ++ name ++ "(" ++ paramsStr ++ ") -> " ++ ppTensorType result ++ " {"
  have hp_excl (c : Char) (hc : isParamFieldChar c = false) : c ∉ paramsStr.toList := by
    intro hm; have := List.all_eq_true.mp (paramsStr_chars params hparams) c hm; simp [hc] at this
  have hhdr_nl : '\n' ∉ header.toList := by
    simp [header, String.toList_append, ssaName_excludes name hname '\n' rfl,
      hp_excl '\n' rfl, tensorType_excludes result '\n' rfl]
  have hat : parseHLOFields " @" header =
      some ["  func.func", name ++ "(" ++ paramsStr ++ ") -> " ++ ppTensorType result ++ " {"] := by
    have hp := parseHLOFields_pair_second ' ' '@' "" "  func.func"
      (name ++ "(" ++ paramsStr ++ ") -> " ++ ppTensorType result ++ " {")
      (by decide) (by decide) '@' (by decide)
      (by simp [String.toList_append, ssaName_excludes name hname '@' rfl,
        hp_excl '@' rfl, tensorType_excludes result '@' rfl])
    have heq : header = "  func.func" ++ " @" ++ (name ++ "(" ++ paramsStr ++ ") -> " ++ ppTensorType result ++ " {") := by
      apply String.ext_iff.mpr; simp [header, String.toList_append]
    rw [heq]; simpa [String.append_assoc] using hp
  have hlp : parseHLOFields "(" (name ++ "(" ++ paramsStr ++ ") -> " ++ ppTensorType result ++ " {") =
      some [name, paramsStr ++ ") -> " ++ ppTensorType result ++ " {"] := by
    have hp := parseHLOFields_pair_head '(' "" name (paramsStr ++ ") -> " ++ ppTensorType result ++ " {")
      (ssaName_excludes name hname '(' rfl) '(' (by decide)
      (by simp [String.toList_append, hp_excl '(' rfl, tensorType_excludes result '(' rfl])
    have heq : name ++ "(" ++ paramsStr ++ ") -> " ++ ppTensorType result ++ " {" =
        name ++ "(" ++ (paramsStr ++ ") -> " ++ ppTensorType result ++ " {") := by
      apply String.ext_iff.mpr; simp [String.toList_append]
    rw [heq]; simpa [String.append_assoc] using hp
  have hrp : parseHLOFields ") -> " (paramsStr ++ ") -> " ++ ppTensorType result ++ " {") =
      some [paramsStr, ppTensorType result ++ " {"] := by
    have hp := parseHLOFields_pair_head ')' " -> " paramsStr (ppTensorType result ++ " {")
      (hp_excl ')' rfl) ')' (by decide)
      (by simp [String.toList_append, tensorType_excludes result ')' rfl])
    have heq : paramsStr ++ ") -> " ++ ppTensorType result ++ " {" =
        paramsStr ++ ") -> " ++ (ppTensorType result ++ " {") := by
      apply String.ext_iff.mpr; simp [String.toList_append]
    rw [heq]; simpa [String.append_assoc] using hp
  have hbr : parseHLOFields " {" (ppTensorType result ++ " {") = some [ppTensorType result, ""] := by
    have hp := parseHLOFields_pair_second ' ' '{' "" (ppTensorType result) ""
      (by decide) (tensorType_excludes result '{' rfl) '{' (by decide) (by simp)
    simpa [String.append_assoc] using hp
  -- Params parsing roundtrip `hpr`
  let parseParam : String → Option (String × TensorType) := fun param => do
    let [pname, pty] ← parseHLOFields ": " param | none
    return (← parseSSAName pname, ← parseTensorType pty)
  have hparam_one (n : String) (ty : TensorType) (hn : CanonicalSSAName n) :
      parseParam (fmtParam (n, ty)) = some (n, ty) := by
    dsimp only [parseParam, fmtParam]
    have hp := parseHLOFields_pair_head ':' " " ("%" ++ n) (ppTensorType ty)
      (by simp [String.toList_append, ssaName_excludes n hn ':' rfl])
      ':' (by decide) (tensorType_excludes ty ':' rfl)
    have heq : s!"%{n}: {ppTensorType ty}" = ("%" ++ n) ++ ": " ++ ppTensorType ty := by
      apply String.ext_iff.mpr; simp [toString, String.toList_append]
    rw [heq]; simp only [String.singleton_eq_ofList, String.reduceOfList, String.reduceAppend] at hp
    rw [hp]
    simp [hn.parse_roundtrip n, parseTensorType_roundtrip, bind, Option.bind, pure]
  have hpr : ∀ (f : String → Option (String × TensorType)),
      (∀ s, f s = parseParam s) →
      (if paramsStr.isEmpty then some [] else
        Option.bind (parseHLOFields ", " paramsStr) (fun __do_lift => List.mapM f __do_lift)) =
        some params := by
    intro f hf
    have hfeq : f = parseParam := funext hf
    subst hfeq
    cases params with
    | nil => rfl
    | cons p0 ps =>
      have hp_ne : paramsStr.isEmpty = false := by
        rcases p0 with ⟨n0, ty0⟩
        cases ps with
        | nil => simp [paramsStr, fmtParam, toString]
        | cons p1 ps' =>
          dsimp only [paramsStr]
          rw [List.map_cons, List.map_cons, String.intercalate_cons_cons]
          simp [fmtParam, toString]
      have hp_split := parseHLOFields_intercalate_head ',' " " ((p0 :: ps).map fmtParam) (by simp) (by
        intro s hs; obtain ⟨⟨n, ty⟩, hmem, rfl⟩ := List.mem_map.mp hs
        simp [fmtParam, toString, String.toList_append,
          ssaName_excludes n (hparams (n, ty) hmem) ',' rfl, tensorType_excludes ty ',' rfl])
      simp only [String.singleton_eq_ofList, String.reduceOfList, String.reduceAppend] at hp_split
      have hmapM : ∀ qs : List (String × TensorType), (∀ q ∈ qs, CanonicalSSAName q.1) →
          (qs.map fmtParam).mapM parseParam = some qs := by
        intro qs
        induction qs with
        | nil => intro _; rfl
        | cons q qs ih =>
          intro hq
          rcases q with ⟨qn, qty⟩
          simp only [List.map_cons, List.mapM_cons]
          rw [hparam_one qn qty (hq (qn, qty) (by simp)), ih (fun u hu => hq u (by simp [hu]))]
          rfl
      simp only [hp_ne, Bool.false_eq_true, ↓reduceIte]
      dsimp only [paramsStr]
      rw [hp_split]
      exact hmapM (p0 :: ps) hparams
  dsimp only [Option.bind] at hpr
  -- Body / lines roundtrip
  cases body with
  | nil =>
    have hlines : parseHLOFields "\n" (ppFuncOp ⟨name, params, result, []⟩) =
        some [header, "", "  }"] := by
      have hp := parseHLOFields_intercalate '\n' [header, "", "  }"] (by simp) (by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
        · exact hhdr_nl
        · simp
        · decide)
      have hnl : String.singleton '\n' = "\n" := rfl
      rw [hnl] at hp
      have heq : ppFuncOp ⟨name, params, result, []⟩ = String.intercalate "\n" [header, "", "  }"] := by
        apply String.ext_iff.mpr
        simp [ppFuncOp, ppBody, header, paramsStr, fmtParam, toString, String.toList_append]
      rw [heq]; exact hp
    unfold parseFuncOp
    rw [hlines]
    simp only [hat, hlp, hname.parse_roundtrip name, hrp, hbr, parseTensorType_roundtrip,
      bind, Option.bind, pure]
    rw [hpr _ (fun s => by
      dsimp only [parseParam, bind, Option.bind, pure]
      cases parseHLOFields ": " s with
      | none => rfl
      | some xs => rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl)]
    rfl
  | cons op0 ops =>
    let bLines := ppBody tenv0 (op0 :: ops)
    have hlines : parseHLOFields "\n" (ppFuncOp ⟨name, params, result, op0 :: ops⟩) =
        some (header :: (bLines ++ ["  }"])) := by
      have hp := parseHLOFields_intercalate '\n' (header :: (bLines ++ ["  }"])) (by simp) (by
        intro x hx; simp at hx; rcases hx with rfl | hmem | rfl
        · exact hhdr_nl
        · exact ppBody_no_newline tenv0 (op0 :: ops) hbody x hmem
        · decide)
      have hnl : String.singleton '\n' = "\n" := rfl
      rw [hnl] at hp
      have hne_bl : bLines ≠ [] := by simp [bLines, ppBody]
      have heq : ppFuncOp ⟨name, params, result, op0 :: ops⟩ =
          String.intercalate "\n" (header :: (bLines ++ ["  }"])) := by
        have hinter : String.intercalate "\n" (header :: (bLines ++ ["  }"])) =
            header ++ "\n" ++ String.intercalate "\n" bLines ++ "\n" ++ "  }" := by
          cases hbl : bLines with
          | nil => exact False.elim (hne_bl hbl)
          | cons bl0 bls =>
            simp only [List.cons_append]
            rw [String.intercalate_cons_cons]
            have h2 := String.intercalate_append_of_ne_nil (s := "\n")
              (by simp : bl0 :: bls ≠ []) (by simp : ["  }"] ≠ [])
            simp only [List.cons_append, String.intercalate_singleton] at h2
            rw [h2]; simp [String.append_assoc]
        rw [hinter]
        apply String.ext_iff.mpr
        simp [ppFuncOp, bLines, tenv0, header, paramsStr, fmtParam, toString, String.toList_append]
      rw [heq]; exact hp
    have hrev_bl : (bLines ++ ["  }"]).reverse = "  }" :: bLines.reverse := by simp
    have hne_empty_line : (bLines.reverse == [""]) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro heq
      have hbl_eq : bLines = [""] := by
        have := congrArg List.reverse heq; simpa using this
      simp only [bLines, ppBody, List.cons.injEq] at hbl_eq
      have hch := congrArg String.toList hbl_eq.1
      simp [String.toList_append] at hch
    have hpbody : parseBody tenv0 bLines = some (op0 :: ops) :=
      parseBody_roundtrip tenv0 (op0 :: ops) hbody
    unfold parseFuncOp
    rw [hlines]
    simp only [hat, hlp, hname.parse_roundtrip name, hrp, hbr, parseTensorType_roundtrip,
      bind, Option.bind, pure]
    rw [hpr _ (fun s => by
      dsimp only [parseParam, bind, Option.bind, pure]
      cases parseHLOFields ": " s with
      | none => rfl
      | some xs => rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl)]
    simp only [hrev_bl, hne_empty_line, Bool.false_eq_true, ↓reduceIte, List.reverse_reverse]
    dsimp only [tenv0, bLines] at hpbody ⊢
    rw [hpbody]

theorem ppFuncOp_injective_on_canonical (a b : FuncOp)
    (ha : CanonicalFuncOp a) (hb : CanonicalFuncOp b)
    (h : ppFuncOp a = ppFuncOp b) : a = b := by
  have hp := congrArg parseFuncOp h
  rwa [parseFuncOp_roundtrip a ha, parseFuncOp_roundtrip b hb, Option.some.injEq] at hp

end LeanNative.Backend.StableHLOAst
