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

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
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
    have hdscan := fun sep => scanHLOFields_name ' ' sep d hd rfl
    have hascan := fun sep => scanHLOFields_name ' ' sep a ha rfl
    have hbscan := fun sep => scanHLOFields_name ' ' sep b hb rfl
    have htscan := fun sep => scanHLOFields_type ' ' sep ty rfl
    have hbend := fun sep => scanHLOFields_no_head ' ' sep b.toList (hb.excludes b ' ' rfl)
    have hacomma := fun sep => scanHLOFields_name ',' sep a ha rfl
    have hbcomma := fun sep => scanHLOFields_no_head ',' sep b.toList (hb.excludes b ',' rfl)
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [ppStableHLOOp, ppTyped, he, toString]
    all_goals
    (
    unfold parseStableHLOOp parseHLOFields
    simp only [String.toList_append, String.reduceToList, List.append_assoc,
      List.cons_append, List.nil_append, List.length_append, List.length_cons]
    simp only [scanHLOFields, stripPrefixChars,
      List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Char.reduceBEq,
      bind, Option.bind, pure, Nat.add_assoc]
    repeat first
      | (rw [hdscan] <;> try (simp only [Nat.add]; omega))
      | (rw [hascan] <;> try (simp only [Nat.add]; omega))
      | (rw [hbscan] <;> try (simp only [Nat.add]; omega))
      | (rw [htscan] <;> try omega)
      | (rw [hbend] <;> try omega)
      | (rw [hacomma] <;> try omega)
      | (rw [hbcomma] <;> try omega)
      | simp only [scanHLOFields, stripPrefixChars, List.isEmpty_cons,
          String.toList_ofList, String.ofList_toList, List.length_append, List.length_cons,
          List.length_nil,
          Bool.false_eq_true, ↓reduceIte, Char.reduceBEq, bind, Option.bind, pure,
          Option.map_some, List.map_cons, List.map_nil, List.append_nil,
          Nat.add_eq, Nat.add_assoc, Nat.add_sub_cancel_left]
    have hpd : parseSSAName (String.ofList ('%' :: d.toList)) = some d := by
      simpa [String.toList_append] using hd.parse_roundtrip d
    have hpb : parseSSAName (String.ofList ('%' :: b.toList)) = some b := by
      simpa [String.toList_append] using hb.parse_roundtrip b
    simp only [String.reduceOfList, hpd, hpb]
    simp [List.take_succ_cons,
      ha.parse_roundtrip a, parseBinaryOp, he, String.ofList_append]
    · change (( '%' :: a.toList) ++ [',']).getLast? = some ','
      exact List.getLast?_concat
    all_goals (try simp only [Nat.add_eq]) <;> omega
    )

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

end LeanNative.Backend.StableHLOAst
