import LeanNative.Proofs.H3.RcCore

/-!
# H3.1 Step 1: soundness of `reset`/`reuse` on the RC core calculus (`RcCoreReuse.lean`)

Proofs of the conjectures stated in `RcCore.lean`. No `sorry`; standard axioms only.

**Heap well-formedness preservation.** `HeapWFP s pend` is preserved by each primitive:
`wfp_take` (consume a credit into `pend`), `wfp_decr` (`rc - 1`), `wfp_free` (free at
`rc = 1`, fields become pending), `wfp_addTok` / `wfp_dropTok` (reserve / unreserve a slot),
`wf_install` (write a fresh object), `wf_pushPtr` / `wf_pushLit` (`inc`). `decV_wf` and
`decL_wf` lift this through the recursive release cascade. The per-construct step lemmas
(`wf_stepCtor`, `wf_push`, `wf_stepDec`, `wf_stepResetExcl`, `wf_stepResetShared`,
`wf_stepReuseSlot`, `wf_stepReuseNull`) give `eval_preserves_wf` and `wfPreservation`.

**Semantic preservation.** The in-place and pure-allocation runs are related by a partial
address injection `φ` (`HRel`): every live in-place object sits at `φ a` in the pure heap with
the same tag and count and renamed fields. Reserved slots have no image: they correspond to
the cell the pure run has already freed. At an exclusive `reset` (`rc = 1`), exact accounting
(`unique_ref`) shows that no environment credit, heap field or pending reference still points
at the slot, so writing into it in place is unobservable; `reuse` then extends `φ` with
`slot ↦ fresh` (`hrel_alloc`, `sim_alloc`). Since the counts agree, both runs take the same
branch at every `dec` (`decV_sim`). `eval_sim` is the simulation, `denote_sim` transports the
read-back, `resetReuseSoundness` is the headline theorem, and `eraseSoundness` is its form
against the syntactic erasure `erase` (`eval_erase`).

**Witnesses.** `#guard`s on `exclSt` (exclusive: reused in place, no allocation), `sharedSt`
(shared: fresh allocation, alias intact), `badSt` (ill-accounted, `badSt_not_wf`: the in-place
run corrupts the alias, so `HeapWF` cannot be dropped) and an unbalanced double `dec`
(stuck). `exclSt_wf` and `sharedSt_wf` show that the positive witnesses satisfy the hypotheses.
-/

namespace LeanNative.Proofs.H3.RcCore

/-! ## Bags -/

section Bags

variable {α β : Type}

/-- Apply `f` to every value of a bag. -/
def mapBag (f : α → β) (l : List (Var × α)) : List (Var × β) :=
  l.map fun p => (p.1, f p.2)

theorem lookup_mem (x : Var) (v : α) (l : List (Var × α)) (h : lookup l x = some v) :
    (x, v) ∈ l := by
  induction l with
  | nil => simp [lookup] at h
  | cons p r ih =>
    obtain ⟨y, u⟩ := p
    by_cases hy : y = x
    · subst hy
      simp [lookup] at h
      subst h
      simp
    · simp [lookup, hy] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem take_some (x : Var) (l : List (Var × α)) (v : α) (l' : List (Var × α))
    (h : take l x = some (v, l')) : (x, v) ∈ l ∧ ∀ p, p ∈ l' → p ∈ l := by
  induction l generalizing l' with
  | nil => simp [take] at h
  | cons p r ih =>
    obtain ⟨y, u⟩ := p
    by_cases hy : y = x
    · subst hy
      simp [take] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, fun q hq => List.mem_cons_of_mem _ hq⟩
    · cases ht : take r x with
      | none => simp [take, hy, ht] at h
      | some q =>
        obtain ⟨w, r'⟩ := q
        simp [take, hy, ht] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih r' ht
        refine ⟨List.mem_cons_of_mem _ h1, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · simp
        · exact List.mem_cons_of_mem _ (h2 q hq)

/-- `take` splits any additive count over a bag. -/
theorem take_sum (f : α → Nat) (F : List (Var × α) → Nat)
    (hc : ∀ p r, F (p :: r) = f p.2 + F r)
    (x : Var) (l : List (Var × α)) (v : α) (l' : List (Var × α))
    (h : take l x = some (v, l')) : F l = f v + F l' := by
  induction l generalizing l' with
  | nil => simp [take] at h
  | cons p r ih =>
    obtain ⟨y, u⟩ := p
    by_cases hy : y = x
    · subst hy
      simp [take] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc _ _
    · cases ht : take r x with
      | none => simp [take, hy, ht] at h
      | some q =>
        obtain ⟨w, r'⟩ := q
        simp [take, hy, ht] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := ih r' ht
        rw [hc, hc, h1]
        omega

theorem take_mapBag (f : α → β) (x : Var) (l : List (Var × α)) :
    take (mapBag f l) x = (take l x).map fun q => (f q.1, mapBag f q.2) := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨y, u⟩ := p
    by_cases hy : y = x
    · simp [mapBag, take, hy]
    · have ih' : take (mapBag f r) x = (take r x).map fun q => (f q.1, mapBag f q.2) := ih
      simp only [mapBag, List.map_cons] at ih' ⊢
      simp only [take, hy, ite_false, ih']
      cases take r x with
      | none => rfl
      | some q => rfl

theorem lookup_mapBag (f : α → β) (x : Var) (l : List (Var × α)) :
    lookup (mapBag f l) x = (lookup l x).map f := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨y, u⟩ := p
    by_cases hy : y = x
    · simp [mapBag, lookup, hy]
    · have ih' : lookup (mapBag f r) x = (lookup r x).map f := ih
      simp only [mapBag, List.map_cons] at ih' ⊢
      simp only [lookup, hy, ite_false, ih']

theorem mem_mapBag (f : α → β) (l : List (Var × α)) (y : Var) (u : β)
    (h : (y, u) ∈ mapBag f l) : ∃ v, (y, v) ∈ l ∧ u = f v := by
  simp only [mapBag, List.mem_map] at h
  obtain ⟨⟨z, v⟩, hv, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨v, hv, rfl⟩

theorem mapBag_congr (f g : α → β) (l : List (Var × α)) (h : ∀ y v, (y, v) ∈ l → f v = g v) :
    mapBag f l = mapBag g l := by
  unfold mapBag
  apply List.map_congr_left
  intro p hp
  obtain ⟨y, v⟩ := p
  simp [h y v hp]

end Bags

theorem takeMany_some (env : List (Var × Val)) (ys : List Var) (vs : List Val)
    (env' : List (Var × Val)) (h : takeMany env ys = some (vs, env')) :
    (∀ v, v ∈ vs → ∃ y, (y, v) ∈ env) ∧ (∀ p, p ∈ env' → p ∈ env) ∧
      ∀ a, envRefs a env = cntV a vs + envRefs a env' := by
  induction ys generalizing env vs env' with
  | nil =>
    simp [takeMany] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, fun _ hp => hp, fun _ => by simp [cntV]⟩
  | cons y ys ih =>
    cases ht : take env y with
    | none => simp [takeMany, ht] at h
    | some q =>
      obtain ⟨v, e1⟩ := q
      cases hm : takeMany e1 ys with
      | none => simp [takeMany, ht, hm] at h
      | some q2 =>
        obtain ⟨vs1, e2⟩ := q2
        simp [takeMany, ht, hm] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hmem, hsub⟩ := take_some y env v e1 ht
        obtain ⟨i1, i2, i3⟩ := ih e1 vs1 e2 hm
        refine ⟨?_, fun p hp => hsub p (i2 p hp), fun a => ?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact ⟨y, hmem⟩
          · obtain ⟨z, hz⟩ := i1 u hu
            exact ⟨z, hsub _ hz⟩
        · have h1 := take_sum (valRef a) (envRefs a) (fun _ _ => rfl) y env v e1 ht
          rw [h1, i3 a]
          simp only [cntV]
          omega

theorem takeMany_mapBag (f : Val → Val) (env : List (Var × Val)) (ys : List Var) :
    takeMany (mapBag f env) ys =
      (takeMany env ys).map fun q => (q.1.map f, mapBag f q.2) := by
  induction ys generalizing env with
  | nil => rfl
  | cons y ys ih =>
    simp only [takeMany, take_mapBag]
    cases take env y with
    | none => rfl
    | some q =>
      obtain ⟨v, e1⟩ := q
      simp only [Option.map_some, ih]
      cases takeMany e1 ys with
      | none => rfl
      | some q2 => rfl

/-! ## Counting -/

theorem valRef_eq_zero (a : Addr) (v : Val) : valRef a v = 0 ↔ v ≠ .ptr a := by
  cases v with
  | lit n => simp [valRef]
  | ptr b =>
    by_cases hb : b = a
    · simp [valRef, hb]
    · simp [valRef, hb]

theorem cntV_append (a : Addr) (xs ys : List Val) : cntV a (xs ++ ys) = cntV a xs + cntV a ys := by
  induction xs with
  | nil => simp [cntV]
  | cons v vs ih =>
    simp only [List.cons_append, cntV, ih]
    omega

theorem cntV_eq_zero (a : Addr) (vs : List Val) : cntV a vs = 0 ↔ .ptr a ∉ vs := by
  induction vs with
  | nil => simp [cntV]
  | cons v vs ih =>
    have hv := valRef_eq_zero a v
    simp only [cntV, Nat.add_eq_zero_iff, hv, ih, List.mem_cons, not_or]
    constructor
    · intro h
      exact ⟨fun he => h.1 he.symm, h.2⟩
    · intro h
      exact ⟨fun he => h.1 he.symm, h.2⟩

theorem envRefs_eq_zero (a : Addr) (env : List (Var × Val)) :
    envRefs a env = 0 ↔ ∀ x, (x, .ptr a) ∉ env := by
  induction env with
  | nil => simp [envRefs]
  | cons p r ih =>
    obtain ⟨y, v⟩ := p
    have hv := valRef_eq_zero a v
    simp only [envRefs, Nat.add_eq_zero_iff, hv, ih, List.mem_cons, not_or, Prod.mk.injEq]
    constructor
    · intro h x
      exact ⟨fun he => h.1 he.2.symm, h.2 x⟩
    · intro h
      exact ⟨fun he => (h y).1 ⟨rfl, he.symm⟩, fun x => (h x).2⟩

theorem tokRefs_eq_zero (a : Addr) (toks : List (Var × Tok)) :
    tokRefs a toks = 0 ↔ ∀ w, (w, .slot a) ∉ toks := by
  induction toks with
  | nil => simp [tokRefs]
  | cons p r ih =>
    obtain ⟨y, k⟩ := p
    have hk : tokRef a k = 0 ↔ k ≠ .slot a := by
      cases k with
      | null => simp [tokRef]
      | slot b =>
        by_cases hb : b = a
        · simp [tokRef, hb]
        · simp [tokRef, hb]
    simp only [tokRefs, Nat.add_eq_zero_iff, hk, ih, List.mem_cons, not_or, Prod.mk.injEq]
    constructor
    · intro h x
      exact ⟨fun he => h.1 he.2.symm, h.2 x⟩
    · intro h
      exact ⟨fun he => (h y).1 ⟨rfl, he.symm⟩, fun x => (h x).2⟩

theorem envRefs_take (a x : Nat) (l l' : List (Var × Val)) (v : Val)
    (h : take l x = some (v, l')) : envRefs a l = valRef a v + envRefs a l' :=
  take_sum (valRef a) (envRefs a) (fun _ _ => rfl) x l v l' h

theorem tokRefs_take (a w : Nat) (l l' : List (Var × Tok)) (k : Tok)
    (h : take l w = some (k, l')) : tokRefs a l = tokRef a k + tokRefs a l' :=
  take_sum (tokRef a) (tokRefs a) (fun _ _ => rfl) w l k l' h

/-! ## Sums over addresses -/

theorem sumBelow_congr (f g : Nat → Nat) (n : Nat) (h : ∀ b, b < n → f b = g b) :
    sumBelow f n = sumBelow g n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumBelow]
    rw [ih (fun b hb => h b (by omega)), h m (by omega)]

theorem sumBelow_update (f g : Nat → Nat) (a n : Nat) (ha : a < n)
    (h : ∀ b, b ≠ a → f b = g b) : sumBelow g n + f a = sumBelow f n + g a := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [sumBelow]
    by_cases ham : a = m
    · subst ham
      have hc := sumBelow_congr f g a (fun b hb => h b (by omega))
      omega
    · have h1 := ih (by omega)
      have h2 := h m (fun he => ham he.symm)
      omega

theorem le_sumBelow (f : Nat → Nat) (n b : Nat) (hb : b < n) : f b ≤ sumBelow f n := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [sumBelow]
    by_cases hbm : b = m
    · subst hbm
      omega
    · have := ih (by omega)
      omega

theorem sumBelow_eq_zero (f : Nat → Nat) (n : Nat) (h : ∀ b, b < n → f b = 0) :
    sumBelow f n = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumBelow]
    rw [ih (fun b hb => h b (by omega)), h m (by omega)]

/-! ## Heap updates -/

theorem Heap.set_cells (h : Heap) (a : Addr) (c : HCell) (b : Addr) :
    (h.set a c).cells b = if b = a then c else h.cells b := rfl

@[simp] theorem Heap.set_cells_self (h : Heap) (a : Addr) (c : HCell) :
    (h.set a c).cells a = c := by
  simp [Heap.set]

theorem Heap.set_cells_ne (h : Heap) (a : Addr) (c : HCell) (b : Addr) (hb : b ≠ a) :
    (h.set a c).cells b = h.cells b := by
  simp [Heap.set, hb]

@[simp] theorem Heap.set_next (h : Heap) (a : Addr) (c : HCell) : (h.set a c).next = h.next :=
  rfl

@[simp] theorem Heap.grow_cells (h : Heap) : h.grow.cells = h.cells := rfl

@[simp] theorem Heap.grow_next (h : Heap) : h.grow.next = h.next + 1 := rfl

theorem Heap.set_set (h : Heap) (a : Addr) (c c' : HCell) : (h.set a c).set a c' = h.set a c' := by
  cases h
  simp only [Heap.set, Heap.mk.injEq, and_true]
  funext b
  by_cases hb : b = a
  · simp [hb]
  · simp [hb]

theorem heapRefs_set (h : Heap) (a x : Addr) (c : HCell) (ha : a < h.next) :
    heapRefs (h.set a c) x + cellRefs x (h.cells a) = heapRefs h x + cellRefs x c := by
  have key := sumBelow_update (fun b => cellRefs x (h.cells b))
    (fun b => cellRefs x ((h.set a c).cells b)) a h.next ha
    (fun b hb => by simp [Heap.set_cells_ne _ _ _ _ hb])
  rw [Heap.set_cells_self] at key
  exact key

theorem heapRefs_grow (h : Heap) (x : Addr) (hf : h.cells h.next = .free) :
    heapRefs h.grow x = heapRefs h x := by
  simp [heapRefs, sumBelow, hf, cellRefs]

theorem heapRefs_eq_zero (h : Heap) (x : Addr)
    (hn : ∀ b t fs rc, h.cells b = .obj t fs rc → .ptr x ∉ fs) : heapRefs h x = 0 := by
  apply sumBelow_eq_zero
  intro b _
  cases hc : h.cells b with
  | free => rfl
  | resv => rfl
  | obj t fs rc => exact (cntV_eq_zero x fs).mpr (hn b t fs rc hc)

theorem not_mem_of_heapRefs_zero (h : Heap) (x b : Addr) (t : Nat) (fs : List Val) (rc : Nat)
    (h0 : heapRefs h x = 0) (hb : b < h.next) (hc : h.cells b = .obj t fs rc) :
    .ptr x ∉ fs := by
  have hle := le_sumBelow (fun b => cellRefs x (h.cells b)) h.next b hb
  have hz : cellRefs x (h.cells b) = 0 := by
    simp only [heapRefs] at h0
    omega
  rw [hc] at hz
  exact (cntV_eq_zero x fs).mp hz

theorem cellRefs_free_resv (x : Addr) : cellRefs x .free = cellRefs x .resv := rfl

/-! ## Liveness -/

/-- A cell that is not an object. -/
def Dead (c : HCell) : Prop := ∀ t fs rc, c ≠ .obj t fs rc

theorem dead_free : Dead .free := fun _ _ _ h => HCell.noConfusion h

theorem dead_resv : Dead .resv := fun _ _ _ h => HCell.noConfusion h

theorem live_set_obj (h : Heap) (a b : Addr) (t : Nat) (fs : List Val) (rc : Nat)
    (hl : Live h b) : Live (h.set a (.obj t fs rc)) b := by
  by_cases hb : b = a
  · subst hb
    exact ⟨t, fs, rc, Heap.set_cells_self _ _ _⟩
  · obtain ⟨t', fs', rc', hc⟩ := hl
    exact ⟨t', fs', rc', by rw [Heap.set_cells_ne _ _ _ _ hb, hc]⟩

theorem live_set_obj_self (h : Heap) (a : Addr) (t : Nat) (fs : List Val) (rc : Nat) :
    Live (h.set a (.obj t fs rc)) a :=
  ⟨t, fs, rc, Heap.set_cells_self _ _ _⟩

theorem live_set_dead (h : Heap) (a b : Addr) (c : HCell) (hc : Dead c) :
    Live (h.set a c) b ↔ b ≠ a ∧ Live h b := by
  by_cases hb : b = a
  · subst hb
    simp only [Live, Heap.set_cells_self, ne_eq, not_true_eq_false, false_and, iff_false]
    intro ⟨t, fs, rc, he⟩
    exact hc t fs rc he
  · simp only [Live, Heap.set_cells_ne _ _ _ _ hb, ne_eq, hb, not_false_eq_true, true_and]

theorem live_ne_of_dead (h : Heap) (a b : Addr) (hd : Dead (h.cells a)) (hl : Live h b) :
    b ≠ a := by
  intro he
  subst he
  obtain ⟨t, fs, rc, hc⟩ := hl
  exact hd t fs rc hc

theorem live_lt (h : Heap) (a : Addr) (hb : ∀ a, h.next ≤ a → h.cells a = .free)
    (hl : Live h a) : a < h.next := by
  apply Nat.lt_of_not_le
  intro hle
  obtain ⟨t, fs, rc, hc⟩ := hl
  rw [hb a hle] at hc
  exact HCell.noConfusion hc

theorem live_grow (h : Heap) (a : Addr) : Live h.grow a ↔ Live h a := Iff.rfl

theorem obj_set_cases (h : Heap) (a b : Addr) (c : HCell) (t : Nat) (fs : List Val) (rc : Nat)
    (hb : (h.set a c).cells b = .obj t fs rc) :
    (b = a ∧ c = .obj t fs rc) ∨ (b ≠ a ∧ h.cells b = .obj t fs rc) := by
  by_cases hba : b = a
  · subst hba
    rw [Heap.set_cells_self] at hb
    exact Or.inl ⟨rfl, hb⟩
  · rw [Heap.set_cells_ne _ _ _ _ hba] at hb
    exact Or.inr ⟨hba, hb⟩

theorem resv_set_cases (h : Heap) (a b : Addr) (c : HCell) (hb : (h.set a c).cells b = .resv) :
    (b = a ∧ c = .resv) ∨ (b ≠ a ∧ h.cells b = .resv) := by
  by_cases hba : b = a
  · subst hba
    rw [Heap.set_cells_self] at hb
    exact Or.inl ⟨rfl, hb⟩
  · rw [Heap.set_cells_ne _ _ _ _ hba] at hb
    exact Or.inr ⟨hba, hb⟩

theorem valRef_self (a : Addr) : valRef a (.ptr a) = 1 := by
  simp [valRef]

theorem valRef_ne {a b : Addr} (h : a ≠ b) : valRef b (.ptr a) = 0 := by
  simp [valRef, h]

theorem tokRef_self (a : Addr) : tokRef a (.slot a) = 1 := by
  simp [tokRef]

theorem tokRef_ne {a b : Addr} (h : a ≠ b) : tokRef b (.slot a) = 0 := by
  simp [tokRef, h]

theorem ne_of_lt_le {a n b : Nat} (ha : a < n) (hb : n ≤ b) : b ≠ a := by
  omega

/-! ## Heap well-formedness: single steps -/

section WF

variable {s : St} {P : List Val}

theorem wfp_lit {n : Nat} (hw : HeapWFP s (.lit n :: P)) : HeapWFP s P where
  bounded := hw.bounded
  envLive := hw.envLive
  pendLive a ha := hw.pendLive a (List.mem_cons_of_mem _ ha)
  fieldLive := hw.fieldLive
  tokResv := hw.tokResv
  resvTok := hw.resvTok
  rcPos := hw.rcPos
  rcExact a t fs rc hc := by
    have h1 := hw.rcExact a t fs rc hc
    simp only [cntV, valRef] at h1
    omega

theorem wfp_take {x : Var} {v : Val} {env' : List (Var × Val)} (hw : HeapWFP s P)
    (ht : take s.env x = some (v, env')) : HeapWFP { s with env := env' } (v :: P) := by
  obtain ⟨hmem, hsub⟩ := take_some x s.env v env' ht
  refine ⟨hw.bounded, fun y a hy => hw.envLive y a (hsub _ hy), ?_, hw.fieldLive, hw.tokResv,
    hw.resvTok, hw.rcPos, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · subst he
      exact hw.envLive x a hmem
    · exact hw.pendLive a ha
  · intro a t fs rc hc
    have h1 := hw.rcExact a t fs rc hc
    have h2 := envRefs_take a x s.env env' v ht
    dsimp only
    simp only [cntV]
    omega

theorem wfp_decr {a t rc : Nat} {fs : List Val} (hw : HeapWFP s (.ptr a :: P))
    (hc : s.heap.cells a = .obj t fs (rc + 2)) :
    HeapWFP { s with heap := s.heap.set a (.obj t fs (rc + 1)) } P := by
  have ha : a < s.heap.next := live_lt s.heap a hw.bounded ⟨t, fs, rc + 2, hc⟩
  have hrefs : ∀ x, heapRefs (s.heap.set a (.obj t fs (rc + 1))) x = heapRefs s.heap x := by
    intro x
    have := heapRefs_set s.heap a x (.obj t fs (rc + 1)) ha
    rw [hc] at this
    simp only [cellRefs] at this
    omega
  constructor
  · intro b hb
    have hne : b ≠ a := ne_of_lt_le ha hb
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hw.bounded b hb
  · intro x b hx
    exact live_set_obj _ _ _ _ _ _ (hw.envLive x b hx)
  · intro b hb
    exact live_set_obj _ _ _ _ _ _ (hw.pendLive b (List.mem_cons_of_mem _ hb))
  · intro b t' fs' rc' c hb hcm
    apply live_set_obj
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨hba, he⟩ | ⟨_, hb'⟩
    · injection he with _ hfs
      subst hfs
      exact hw.fieldLive _ _ _ _ c hc hcm
    · exact hw.fieldLive _ _ _ _ c hb' hcm
  · intro w b hb
    have hr := hw.tokResv w b hb
    have hne : b ≠ a := by
      intro he
      subst he
      rw [hc] at hr
      exact HCell.noConfusion hr
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hr
  · intro b hb
    rcases resv_set_cases _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.resvTok b hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · injection he with _ _ hrc
      omega
    · exact hw.rcPos b _ _ _ hb'
  · intro b t' fs' rc' hb
    dsimp only
    rw [hrefs]
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨hba, he⟩ | ⟨hne, hb'⟩
    · subst hba
      injection he with _ _ hrc
      have h1 := hw.rcExact b t fs (rc + 2) hc
      simp only [cntV] at h1
      rw [valRef_self] at h1
      omega
    · have h1 := hw.rcExact b t' fs' rc' hb'
      simp only [cntV] at h1
      rw [valRef_ne (fun he => hne he.symm)] at h1
      omega

theorem unique_ref {a t : Nat} {fs : List Val} (hw : HeapWFP s (.ptr a :: P))
    (hc : s.heap.cells a = .obj t fs 1) :
    envRefs a s.env = 0 ∧ heapRefs s.heap a = 0 ∧ cntV a P = 0 := by
  have h1 := hw.rcExact a t fs 1 hc
  simp only [cntV] at h1
  rw [valRef_self] at h1
  omega

theorem wfp_free {a t : Nat} {fs : List Val} (hw : HeapWFP s (.ptr a :: P))
    (hc : s.heap.cells a = .obj t fs 1) :
    HeapWFP { s with heap := s.heap.set a .free } (fs ++ P) := by
  obtain ⟨he0, hh0, hp0⟩ := unique_ref hw hc
  have ha : a < s.heap.next := live_lt s.heap a hw.bounded ⟨t, fs, 1, hc⟩
  have hlive : ∀ b, Live s.heap b → b ≠ a → Live (s.heap.set a .free) b :=
    fun b hb hne => (live_set_dead _ _ _ _ dead_free).mpr ⟨hne, hb⟩
  have hnf : ∀ b t' fs' rc', s.heap.cells b = .obj t' fs' rc' → .ptr a ∉ fs' :=
    fun b t' fs' rc' hb => not_mem_of_heapRefs_zero _ _ _ _ _ _ hh0
      (live_lt _ _ hw.bounded ⟨t', fs', rc', hb⟩) hb
  have hrefs : ∀ x, heapRefs (s.heap.set a .free) x + cntV x fs = heapRefs s.heap x := by
    intro x
    have := heapRefs_set s.heap a x .free ha
    rw [hc] at this
    simp only [cellRefs] at this
    omega
  constructor
  · intro b hb
    dsimp only at hb ⊢
    by_cases hba : b = a
    · rw [hba]
      exact Heap.set_cells_self _ _ _
    · rw [Heap.set_cells_ne _ _ _ _ hba]
      exact hw.bounded b hb
  · intro x b hx
    apply hlive b (hw.envLive x b hx)
    intro hba
    rw [hba] at hx
    exact (envRefs_eq_zero _ _).mp he0 x hx
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · apply hlive b (hw.fieldLive a t fs 1 b hc hb)
      intro hba
      rw [hba] at hb
      exact hnf _ _ _ _ hc hb
    · apply hlive b (hw.pendLive b (List.mem_cons_of_mem _ hb))
      intro hba
      rw [hba] at hb
      exact (cntV_eq_zero _ _).mp hp0 hb
  · intro b t' fs' rc' c hb hcm
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · apply hlive c (hw.fieldLive b t' fs' rc' c hb' hcm)
      intro hca
      rw [hca] at hcm
      exact hnf _ _ _ _ hb' hcm
  · intro w b hb
    have hr := hw.tokResv w b hb
    have hne : b ≠ a := by
      intro he
      rw [he, hc] at hr
      exact HCell.noConfusion hr
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hr
  · intro b hb
    rcases resv_set_cases _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.resvTok b hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.rcPos b _ _ _ hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨hne, hb'⟩
    · exact HCell.noConfusion he
    · have h1 := hw.rcExact b t' fs' rc' hb'
      have h2 := hrefs b
      simp only [cntV] at h1
      rw [valRef_ne (fun he => hne he.symm)] at h1
      dsimp only
      rw [cntV_append]
      omega

theorem wfp_addTok {a : Addr} (w : Var) (hw : HeapWFP s P) (hf : s.heap.cells a = .free)
    (ha : a < s.heap.next) :
    HeapWFP { s with toks := (w, .slot a) :: s.toks, heap := s.heap.set a .resv } P := by
  have hd : Dead (s.heap.cells a) := by
    rw [hf]
    exact dead_free
  have hlive : ∀ b, Live (s.heap.set a .resv) b ↔ Live s.heap b := by
    intro b
    rw [live_set_dead _ _ _ _ dead_resv]
    constructor
    · exact fun h => h.2
    · intro hb
      exact ⟨live_ne_of_dead _ _ _ hd hb, hb⟩
  have hrefs : ∀ x, heapRefs (s.heap.set a .resv) x = heapRefs s.heap x := by
    intro x
    have := heapRefs_set s.heap a x .resv ha
    rw [hf] at this
    simp only [cellRefs] at this
    omega
  have hnt : tokRefs a s.toks = 0 := by
    apply (tokRefs_eq_zero _ _).mpr
    intro w' hw'
    have := hw.tokResv w' a hw'
    rw [hf] at this
    exact HCell.noConfusion this
  constructor
  · intro b hb
    have hne : b ≠ a := ne_of_lt_le ha hb
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hw.bounded b hb
  · intro x b hx
    exact (hlive b).mpr (hw.envLive x b hx)
  · intro b hb
    exact (hlive b).mpr (hw.pendLive b hb)
  · intro b t' fs' rc' c hb hcm
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact (hlive c).mpr (hw.fieldLive b t' fs' rc' c hb' hcm)
  · intro w' b hb
    rcases List.mem_cons.mp hb with he | hb
    · simp only [Prod.mk.injEq, Tok.slot.injEq] at he
      rw [he.2]
      exact Heap.set_cells_self _ _ _
    · have hr := hw.tokResv w' b hb
      have hne : b ≠ a := by
        intro he
        rw [he, hf] at hr
        exact HCell.noConfusion hr
      dsimp only
      rw [Heap.set_cells_ne _ _ _ _ hne]
      exact hr
  · intro b hb
    dsimp only
    simp only [tokRefs]
    rcases resv_set_cases _ _ _ _ hb with ⟨hba, _⟩ | ⟨hne, hb'⟩
    · rw [hba, tokRef_self, hnt]
    · rw [tokRef_ne (fun he => hne he.symm), hw.resvTok b hb']
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.rcPos b _ _ _ hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · dsimp only
      rw [hrefs]
      exact hw.rcExact b t' fs' rc' hb'

theorem resv_lt (hw : HeapWFP s P) {a : Addr} (hr : s.heap.cells a = .resv) :
    a < s.heap.next := by
  apply Nat.lt_of_not_le
  intro hle
  rw [hw.bounded a hle] at hr
  exact HCell.noConfusion hr

theorem wfp_dropTok {w a : Nat} {toks' : List (Var × Tok)} (hw : HeapWFP s P)
    (ht : take s.toks w = some (.slot a, toks')) :
    HeapWFP { s with toks := toks', heap := s.heap.set a .free } P := by
  obtain ⟨hmem, hsub⟩ := take_some w s.toks (.slot a) toks' ht
  have hr : s.heap.cells a = .resv := hw.tokResv w a hmem
  have hd : Dead (s.heap.cells a) := by
    rw [hr]
    exact dead_resv
  have ha : a < s.heap.next := resv_lt hw hr
  have hlive : ∀ b, Live (s.heap.set a .free) b ↔ Live s.heap b := by
    intro b
    rw [live_set_dead _ _ _ _ dead_free]
    constructor
    · exact fun h => h.2
    · intro hb
      exact ⟨live_ne_of_dead _ _ _ hd hb, hb⟩
  have hrefs : ∀ x, heapRefs (s.heap.set a .free) x = heapRefs s.heap x := by
    intro x
    have := heapRefs_set s.heap a x .free ha
    rw [hr] at this
    simp only [cellRefs] at this
    omega
  have hcnt := fun b => tokRefs_take b w s.toks toks' (.slot a) ht
  have hnt : tokRefs a toks' = 0 := by
    have h1 := hcnt a
    have h2 := hw.resvTok a hr
    rw [tokRef_self] at h1
    omega
  constructor
  · intro b hb
    dsimp only at hb ⊢
    by_cases hba : b = a
    · rw [hba]
      exact Heap.set_cells_self _ _ _
    · rw [Heap.set_cells_ne _ _ _ _ hba]
      exact hw.bounded b hb
  · intro x b hx
    exact (hlive b).mpr (hw.envLive x b hx)
  · intro b hb
    exact (hlive b).mpr (hw.pendLive b hb)
  · intro b t' fs' rc' c hb hcm
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact (hlive c).mpr (hw.fieldLive b t' fs' rc' c hb' hcm)
  · intro w' b hb
    have hr' := hw.tokResv w' b (hsub _ hb)
    have hne : b ≠ a := by
      intro he
      rw [he] at hb
      exact (tokRefs_eq_zero _ _).mp hnt w' hb
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hr'
  · intro b hb
    rcases resv_set_cases _ _ _ _ hb with ⟨_, he⟩ | ⟨hne, hb'⟩
    · exact HCell.noConfusion he
    · have h1 := hcnt b
      have h2 := hw.resvTok b hb'
      rw [tokRef_ne (fun he => hne he.symm)] at h1
      dsimp only
      omega
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.rcPos b _ _ _ hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · dsimp only
      rw [hrefs]
      exact hw.rcExact b t' fs' rc' hb'

theorem wfp_dropNull {w : Nat} {toks' : List (Var × Tok)} (hw : HeapWFP s P)
    (ht : take s.toks w = some (.null, toks')) : HeapWFP { s with toks := toks' } P := by
  obtain ⟨_, hsub⟩ := take_some w s.toks .null toks' ht
  have hcnt := fun b => tokRefs_take b w s.toks toks' .null ht
  refine ⟨hw.bounded, hw.envLive, hw.pendLive, hw.fieldLive,
    fun w' b hb => hw.tokResv w' b (hsub _ hb), ?_, hw.rcPos, hw.rcExact⟩
  intro b hb
  have h1 := hcnt b
  have h2 := hw.resvTok b hb
  simp only [tokRef] at h1
  dsimp only
  omega

theorem wfp_pushNull (w : Var) (hw : HeapWFP s P) :
    HeapWFP { s with toks := (w, .null) :: s.toks } P := by
  refine ⟨hw.bounded, hw.envLive, hw.pendLive, hw.fieldLive, ?_, ?_, hw.rcPos, hw.rcExact⟩
  · intro w' b hb
    rcases List.mem_cons.mp hb with he | hb
    · simp at he
    · exact hw.tokResv w' b hb
  · intro b hb
    dsimp only
    simp only [tokRefs, tokRef, Nat.zero_add]
    exact hw.resvTok b hb

theorem wfp_grow (hw : HeapWFP s P) : HeapWFP { s with heap := s.heap.grow } P := by
  have hf : s.heap.cells s.heap.next = .free := hw.bounded _ (Nat.le_refl _)
  refine ⟨?_, hw.envLive, hw.pendLive, hw.fieldLive, hw.tokResv, hw.resvTok, hw.rcPos, ?_⟩
  · intro b hb
    exact hw.bounded b (Nat.le_of_succ_le hb)
  · intro b t fs rc hb
    dsimp only
    rw [heapRefs_grow _ _ hf]
    exact hw.rcExact b t fs rc hb

theorem wf_pushLit {x : Var} {n : Nat} (hw : HeapWFP s P) :
    HeapWFP { s with env := (x, .lit n) :: s.env } P := by
  refine ⟨hw.bounded, ?_, hw.pendLive, hw.fieldLive, hw.tokResv, hw.resvTok, hw.rcPos, ?_⟩
  · intro y b hy
    rcases List.mem_cons.mp hy with he | hy
    · simp at he
    · exact hw.envLive y b hy
  · intro b t fs rc hb
    dsimp only
    simp only [envRefs, valRef, Nat.zero_add]
    exact hw.rcExact b t fs rc hb

theorem wf_pushPtr {x : Var} {a t rc : Nat} {fs : List Val} (hw : HeapWFP s P)
    (hc : s.heap.cells a = .obj t fs rc) :
    HeapWFP { s with env := (x, .ptr a) :: s.env, heap := s.heap.set a (.obj t fs (rc + 1)) }
      P := by
  have ha : a < s.heap.next := live_lt s.heap a hw.bounded ⟨t, fs, rc, hc⟩
  have hrefs : ∀ x, heapRefs (s.heap.set a (.obj t fs (rc + 1))) x = heapRefs s.heap x := by
    intro x
    have := heapRefs_set s.heap a x (.obj t fs (rc + 1)) ha
    rw [hc] at this
    simp only [cellRefs] at this
    omega
  constructor
  · intro b hb
    have hne : b ≠ a := ne_of_lt_le ha hb
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hw.bounded b hb
  · intro y b hy
    apply live_set_obj
    rcases List.mem_cons.mp hy with he | hy
    · simp only [Prod.mk.injEq, Val.ptr.injEq] at he
      rw [he.2]
      exact ⟨t, fs, rc, hc⟩
    · exact hw.envLive y b hy
  · intro b hb
    exact live_set_obj _ _ _ _ _ _ (hw.pendLive b hb)
  · intro b t' fs' rc' c hb hcm
    apply live_set_obj
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · injection he with _ hfs
      subst hfs
      exact hw.fieldLive _ _ _ _ c hc hcm
    · exact hw.fieldLive _ _ _ _ c hb' hcm
  · intro w b hb
    have hr := hw.tokResv w b hb
    have hne : b ≠ a := by
      intro he
      rw [he, hc] at hr
      exact HCell.noConfusion hr
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hr
  · intro b hb
    rcases resv_set_cases _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.resvTok b hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · injection he with _ _ hrc
      omega
    · exact hw.rcPos b _ _ _ hb'
  · intro b t' fs' rc' hb
    dsimp only
    rw [hrefs]
    simp only [envRefs]
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨hba, he⟩ | ⟨hne, hb'⟩
    · subst hba
      injection he with _ _ hrc
      have h1 := hw.rcExact b t fs rc hc
      rw [valRef_self]
      omega
    · have h1 := hw.rcExact b t' fs' rc' hb'
      rw [valRef_ne (fun he => hne he.symm)]
      omega

theorem wf_install {a : Addr} {x : Var} {t : Nat} {ys : List Var} {vs : List Val}
    {env' : List (Var × Val)} (hw : HeapWF s) (hf : s.heap.cells a = .free)
    (ha : a < s.heap.next) (hm : takeMany s.env ys = some (vs, env')) :
    HeapWF { env := (x, .ptr a) :: env', toks := s.toks, heap := s.heap.set a (.obj t vs 1) } := by
  obtain ⟨hvs, hsub, hcnt⟩ := takeMany_some s.env ys vs env' hm
  have hd : Dead (s.heap.cells a) := by
    rw [hf]
    exact dead_free
  have hvl : ∀ b, .ptr b ∈ vs → Live s.heap b := by
    intro b hb
    obtain ⟨y, hy⟩ := hvs _ hb
    exact hw.envLive y b hy
  have hrefs : ∀ c, heapRefs (s.heap.set a (.obj t vs 1)) c = heapRefs s.heap c + cntV c vs := by
    intro c
    have := heapRefs_set s.heap a c (.obj t vs 1) ha
    rw [hf] at this
    simp only [cellRefs] at this
    omega
  have hea : envRefs a env' = 0 := by
    apply (envRefs_eq_zero _ _).mpr
    intro y hy
    exact live_ne_of_dead _ _ _ hd (hw.envLive y a (hsub _ hy)) rfl
  have hha : heapRefs s.heap a = 0 := by
    apply heapRefs_eq_zero
    intro b t' fs' rc' hb hm'
    exact live_ne_of_dead _ _ _ hd (hw.fieldLive b t' fs' rc' a hb hm') rfl
  have hva : cntV a vs = 0 := by
    apply (cntV_eq_zero _ _).mpr
    intro hm'
    exact live_ne_of_dead _ _ _ hd (hvl a hm') rfl
  constructor
  · intro b hb
    have hne : b ≠ a := ne_of_lt_le ha hb
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hw.bounded b hb
  · intro y b hy
    rcases List.mem_cons.mp hy with he | hy
    · simp only [Prod.mk.injEq, Val.ptr.injEq] at he
      rw [he.2]
      exact live_set_obj_self _ _ _ _ _
    · exact live_set_obj _ _ _ _ _ _ (hw.envLive y b (hsub _ hy))
  · intro b hb
    simp at hb
  · intro b t' fs' rc' c hb hcm
    apply live_set_obj
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · injection he with _ hfs
      subst hfs
      exact hvl c hcm
    · exact hw.fieldLive b t' fs' rc' c hb' hcm
  · intro w b hb
    have hr := hw.tokResv w b hb
    have hne : b ≠ a := by
      intro he
      rw [he, hf] at hr
      exact HCell.noConfusion hr
    dsimp only
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hr
  · intro b hb
    rcases resv_set_cases _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · exact HCell.noConfusion he
    · exact hw.resvTok b hb'
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨_, hb'⟩
    · injection he with _ _ hrc
      omega
    · exact hw.rcPos b _ _ _ hb'
  · intro b t' fs' rc' hb
    dsimp only
    rw [hrefs]
    simp only [envRefs, cntV]
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨hba, he⟩ | ⟨hne, hb'⟩
    · subst hba
      injection he with _ _ hrc
      rw [valRef_self]
      omega
    · have h1 := hw.rcExact b t' fs' rc' hb'
      have h2 := hcnt b
      simp only [cntV] at h1
      rw [valRef_ne (fun he => hne he.symm)]
      omega

end WF

/-! ## The release cascade -/

theorem decL_wf (d : Heap → Val → Option Heap)
    (hd : ∀ (s : St) (v : Val) (P : List Val) (h' : Heap),
      HeapWFP s (v :: P) → d s.heap v = some h' → HeapWFP { s with heap := h' } P) :
    ∀ (fs : List Val) (s : St) (P : List Val) (h' : Heap),
      HeapWFP s (fs ++ P) → decL d s.heap fs = some h' → HeapWFP { s with heap := h' } P := by
  intro fs
  induction fs with
  | nil =>
    intro s P h' hw hl
    simp only [decL, Option.some.injEq] at hl
    subst hl
    exact hw
  | cons v vs ih =>
    intro s P h' hw hl
    simp only [decL] at hl
    cases e : d s.heap v with
    | none => simp [e] at hl
    | some h1 =>
      simp only [e, Option.bind_some] at hl
      exact ih { s with heap := h1 } P h' (hd s v (vs ++ P) h1 hw e) hl

theorem decV_wf : ∀ (n : Nat) (s : St) (v : Val) (P : List Val) (h' : Heap),
    HeapWFP s (v :: P) → decV n s.heap v = some h' → HeapWFP { s with heap := h' } P := by
  intro n
  induction n with
  | zero =>
    intro s v P h' hw hd
    cases v with
    | lit k =>
      simp only [decV, Option.some.injEq] at hd
      subst hd
      exact wfp_lit hw
    | ptr a => simp [decV] at hd
  | succ n ih =>
    intro s v P h' hw hd
    cases v with
    | lit k =>
      simp only [decV, Option.some.injEq] at hd
      subst hd
      exact wfp_lit hw
    | ptr a =>
      obtain ⟨t, fs, rc, hc⟩ := hw.pendLive a (by simp)
      match rc, hc with
      | 0, hc => simp [decV, hc] at hd
      | 1, hc =>
        simp only [decV, hc] at hd
        exact decL_wf (decV n) ih fs { s with heap := s.heap.set a .free } P h'
          (wfp_free hw hc) hd
      | r + 2, hc =>
        simp only [decV, hc, Option.some.injEq] at hd
        subst hd
        exact wfp_decr hw hc

/-! ## Evaluation steps preserve `HeapWF` -/

theorem exclusive_some {inPlace : Bool} {h : Heap} {v : Val} {a : Addr} {fs : List Val}
    (hx : exclusive inPlace h v = some (a, fs)) : v = .ptr a ∧ ∃ t, h.cells a = .obj t fs 1 := by
  cases v with
  | lit _ => simp [exclusive] at hx
  | ptr b =>
    cases inPlace with
    | false => simp [exclusive] at hx
    | true =>
      cases hc : h.cells b with
      | free => simp [exclusive, hc] at hx
      | resv => simp [exclusive, hc] at hx
      | obj t fs' rc =>
        match rc, hc with
        | 0, hc => simp [exclusive, hc] at hx
        | 1, hc =>
          simp [exclusive, hc] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨rfl, t, hc⟩
        | r + 2, hc => simp [exclusive, hc] at hx

theorem exclusive_false (h : Heap) (v : Val) : exclusive false h v = none := by
  cases v with
  | lit _ => rfl
  | ptr _ => rfl

section Steps

variable {s : St}

theorem envPts {x : Var} {v : Val} (hw : HeapWF s) (hl : lookup s.env x = some v) :
    PtsLive s.heap v := by
  intro b hb
  subst hb
  exact hw.envLive x b (lookup_mem x _ s.env hl)

theorem fieldPts {a t rc i : Nat} {fs : List Val} {v : Val} (hw : HeapWF s)
    (hc : s.heap.cells a = .obj t fs rc) (hv : fs[i]? = some v) : PtsLive s.heap v := by
  intro b hb
  subst hb
  exact hw.fieldLive a t fs rc b hc (List.mem_of_getElem? hv)

theorem wf_push {x : Var} {v : Val} {h' : Heap} (hw : HeapWF s) (hv : PtsLive s.heap v)
    (hi : incV s.heap v = some h') : HeapWF { s with env := (x, v) :: s.env, heap := h' } := by
  cases v with
  | lit n =>
    simp only [incV, Option.some.injEq] at hi
    subst hi
    exact wf_pushLit hw
  | ptr a =>
    obtain ⟨t, fs, rc, hc⟩ := hv a rfl
    simp only [incV, hc, Option.some.injEq] at hi
    subst hi
    exact wf_pushPtr hw hc

theorem wf_stepCtor {x : Var} {t : Nat} {ys : List Var} {vs : List Val}
    {env' : List (Var × Val)} (hw : HeapWF s) (hm : takeMany s.env ys = some (vs, env')) :
    HeapWF { s with
      env := (x, .ptr (s.heap.alloc (.obj t vs 1)).1) :: env'
      heap := (s.heap.alloc (.obj t vs 1)).2 } := by
  have hw' := wfp_grow hw
  have hf : ({ s with heap := s.heap.grow } : St).heap.cells s.heap.next = .free :=
    hw.bounded _ (Nat.le_refl _)
  have hlt : s.heap.next < ({ s with heap := s.heap.grow } : St).heap.next :=
    Nat.lt_succ_self _
  exact wf_install hw' hf hlt hm

theorem wf_stepDec {x : Var} {n : Nat} {v : Val} {env' : List (Var × Val)} {h' : Heap}
    (hw : HeapWF s) (ht : take s.env x = some (v, env')) (hd : decV n s.heap v = some h') :
    HeapWF { s with env := env', heap := h' } :=
  decV_wf n { s with env := env' } v [] h' (wfp_take hw ht) hd

theorem wfp_resetPend (w : Var) {x : Var} {a t : Nat} {fs : List Val}
    {env' : List (Var × Val)} (hw : HeapWF s) (ht : take s.env x = some (.ptr a, env'))
    (hc : s.heap.cells a = .obj t fs 1) :
    HeapWFP { env := env', toks := (w, .slot a) :: s.toks, heap := s.heap.set a .resv }
      (fs ++ []) := by
  have hw0 := wfp_take hw ht
  have hw1 := wfp_free hw0 hc
  have ha : a < s.heap.next := live_lt s.heap a hw.bounded ⟨t, fs, 1, hc⟩
  have hw2 := wfp_addTok w hw1 (Heap.set_cells_self _ _ _) ha
  dsimp only at hw2
  rw [Heap.set_set] at hw2
  exact hw2

theorem wf_stepResetExcl {w x : Var} {n a t : Nat} {fs : List Val} {env' : List (Var × Val)}
    {h' : Heap} (hw : HeapWF s) (ht : take s.env x = some (.ptr a, env'))
    (hc : s.heap.cells a = .obj t fs 1) (hr : resetV n s.heap a fs = some h') :
    HeapWF { env := env', toks := (w, .slot a) :: s.toks, heap := h' } := by
  cases n with
  | zero => simp [resetV] at hr
  | succ m =>
    simp only [resetV] at hr
    exact decL_wf (decV m) (decV_wf m) fs _ [] h' (wfp_resetPend w hw ht hc) hr

theorem wf_stepResetShared {w x : Var} {n : Nat} {v : Val} {env' : List (Var × Val)}
    {h' : Heap} (hw : HeapWF s) (ht : take s.env x = some (v, env'))
    (hd : decV n s.heap v = some h') :
    HeapWF { env := env', toks := (w, .null) :: s.toks, heap := h' } :=
  wfp_pushNull w (wf_stepDec hw ht hd)

theorem wf_stepReuseSlot {x w : Var} {a t : Nat} {ys : List Var} {vs : List Val}
    {toks' : List (Var × Tok)} {env' : List (Var × Val)} (hw : HeapWF s)
    (ht : take s.toks w = some (.slot a, toks')) (hm : takeMany s.env ys = some (vs, env')) :
    HeapWF { env := (x, .ptr a) :: env', toks := toks', heap := s.heap.set a (.obj t vs 1) } := by
  have hw1 := wfp_dropTok hw ht
  have hr : s.heap.cells a = .resv := hw.tokResv w a (take_some w s.toks _ toks' ht).1
  have h2 := wf_install (x := x) (t := t) hw1 (Heap.set_cells_self _ _ _) (resv_lt hw hr) hm
  dsimp only at h2
  rw [Heap.set_set] at h2
  exact h2

theorem wf_stepReuseNull {x w : Var} {t : Nat} {ys : List Var} {vs : List Val}
    {toks' : List (Var × Tok)} {env' : List (Var × Val)} (hw : HeapWF s)
    (ht : take s.toks w = some (.null, toks')) (hm : takeMany s.env ys = some (vs, env')) :
    HeapWF {
      env := (x, .ptr (s.heap.alloc (.obj t vs 1)).1) :: env'
      toks := toks'
      heap := (s.heap.alloc (.obj t vs 1)).2 } :=
  wf_stepCtor (s := { s with toks := toks' }) (wfp_dropNull hw ht) hm

end Steps

/-- **Heap well-formedness preservation**: every terminating evaluation (in either mode) of
    any program from a well-formed state ends in a well-formed state, and the returned value
    points into the live heap. -/
theorem eval_preserves_wf (inPlace : Bool) : ∀ (n : Nat) (e : Expr) (s s' : St) (v : Val),
    HeapWF s → eval inPlace n e s = some (v, s') → HeapWF s' ∧ PtsLive s'.heap v := by
  intro n
  induction n with
  | zero =>
    intro e s s' v _ h
    simp [eval] at h
  | succ n ih =>
    intro e s s' v hw h
    cases e with
    | ret x =>
      simp only [eval] at h
      cases hl : lookup s.env x with
      | none => simp [hl] at h
      | some u =>
        simp [hl] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hw, envPts hw hl⟩
    | lit x m k =>
      simp only [eval] at h
      exact ih k _ s' v (wf_pushLit hw) h
    | ctor x t ys k =>
      simp only [eval] at h
      cases hm : takeMany s.env ys with
      | none => simp [hm] at h
      | some q =>
        obtain ⟨vs, env'⟩ := q
        simp only [hm] at h
        exact ih k _ s' v (wf_stepCtor hw hm) h
    | proj x y i k =>
      simp only [eval] at h
      cases hl : lookup s.env y with
      | none => simp [hl] at h
      | some u =>
        cases u with
        | lit _ => simp [hl] at h
        | ptr a =>
          cases hc : s.heap.cells a with
          | free => simp [hl, hc] at h
          | resv => simp [hl, hc] at h
          | obj t fs rc =>
            cases hv : fs[i]? with
            | none => simp [hl, hc, hv] at h
            | some u =>
              cases hi : incV s.heap u with
              | none => simp [hl, hc, hv, hi] at h
              | some h' =>
                simp only [hl, hc, hv, hi] at h
                exact ih k _ s' v (wf_push hw (fieldPts hw hc hv) hi) h
    | case x bs =>
      simp only [eval] at h
      cases hl : lookup s.env x with
      | none => simp [hl] at h
      | some u =>
        cases ht : tagOf s.heap u with
        | none => simp [hl, ht] at h
        | some tg =>
          cases hb : bs[tg]? with
          | none => simp [hl, ht, hb] at h
          | some b =>
            simp only [hl, ht, hb] at h
            exact ih b s s' v hw h
    | inc x k =>
      simp only [eval] at h
      cases hl : lookup s.env x with
      | none => simp [hl] at h
      | some u =>
        cases hi : incV s.heap u with
        | none => simp [hl, hi] at h
        | some h' =>
          simp only [hl, hi] at h
          exact ih k _ s' v (wf_push hw (envPts hw hl) hi) h
    | dec x k =>
      simp only [eval] at h
      cases ht : take s.env x with
      | none => simp [ht] at h
      | some q =>
        obtain ⟨u, env'⟩ := q
        cases hd : decV n s.heap u with
        | none => simp [ht, hd] at h
        | some h' =>
          simp only [ht, hd] at h
          exact ih k _ s' v (wf_stepDec hw ht hd) h
    | reset w x k =>
      simp only [eval] at h
      cases ht : take s.env x with
      | none => simp [ht] at h
      | some q =>
        obtain ⟨u, env'⟩ := q
        cases hx : exclusive inPlace s.heap u with
        | some q2 =>
          obtain ⟨a, fs⟩ := q2
          obtain ⟨rfl, t, hc⟩ := exclusive_some hx
          cases hr : resetV n s.heap a fs with
          | none => simp [ht, hx, hr] at h
          | some h' =>
            simp only [ht, hx, hr] at h
            exact ih k _ s' v (wf_stepResetExcl hw ht hc hr) h
        | none =>
          cases hd : decV n s.heap u with
          | none => simp [ht, hx, hd] at h
          | some h' =>
            simp only [ht, hx, hd] at h
            exact ih k _ s' v (wf_stepResetShared hw ht hd) h
    | reuse x w t ys k =>
      simp only [eval] at h
      cases ht : take s.toks w with
      | none => simp [ht] at h
      | some q =>
        obtain ⟨tk, toks'⟩ := q
        cases hm : takeMany s.env ys with
        | none =>
          cases tk with
          | null => simp [ht, hm] at h
          | slot _ => simp [ht, hm] at h
        | some q2 =>
          obtain ⟨vs, env'⟩ := q2
          cases tk with
          | null =>
            simp only [ht, hm] at h
            exact ih k _ s' v (wf_stepReuseNull hw ht hm) h
          | slot a =>
            simp only [ht, hm] at h
            by_cases hr : s.heap.cells a = .resv
            · simp only [hr, ite_true] at h
              exact ih k _ s' v (wf_stepReuseSlot hw ht hm) h
            · simp [hr] at h

/-! ## Simulation of in-place by pure-allocation evaluation -/

/-- Rename the pointer of a value. -/
def ren (φ : Addr → Addr) : Val → Val
  | .lit n => .lit n
  | .ptr a => .ptr (φ a)

/-- Point update of an address map. -/
def upd (φ : Addr → Addr) (a b : Addr) : Addr → Addr :=
  fun c => if c = a then b else φ c

/-- Forget a token: the pure-allocation run only ever holds `null`. -/
def eraseTok (_ : Tok) : Tok := .null

/-- Heap correspondence under `φ`: each live in-place object is a pure-allocation object at
    `φ a` with the same tag, renamed fields and the same count; `φ` is injective on live
    objects; the pure-allocation heap is bounded by its `next`. Reserved cells and garbage of
    the in-place heap are unconstrained. -/
structure HRel (φ : Addr → Addr) (h1 h2 : Heap) : Prop where
  cell : ∀ a t fs rc, h1.cells a = .obj t fs rc →
    h2.cells (φ a) = .obj t (fs.map (ren φ)) rc
  inj : ∀ a b, Live h1 a → Live h1 b → φ a = φ b → a = b
  bounded : ∀ a, h2.next ≤ a → h2.cells a = .free

/-- State correspondence: related heaps, renamed environment, erased tokens. -/
structure SimSt (φ : Addr → Addr) (s1 s2 : St) : Prop where
  heap : HRel φ s1.heap s2.heap
  env : s2.env = mapBag (ren φ) s1.env
  toks : s2.toks = mapBag eraseTok s1.toks

/-- Result correspondence (the in-place result is well-formed). -/
def SimRes (r1 r2 : Val × St) : Prop :=
  ∃ ψ, HeapWF r1.2 ∧ HRel ψ r1.2.heap r2.2.heap ∧ PtsLive r1.2.heap r1.1 ∧ r2.1 = ren ψ r1.1

theorem ren_id (v : Val) : ren id v = v := by
  cases v with
  | lit _ => rfl
  | ptr _ => rfl

theorem map_ren_id (vs : List Val) : vs.map (ren id) = vs := by
  have h : ren id = id := funext ren_id
  rw [h, List.map_id]

theorem mapBag_ren_id (env : List (Var × Val)) : mapBag (ren id) env = env := by
  induction env with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨y, v⟩ := p
    have ih' : mapBag (ren id) r = r := ih
    simp only [mapBag, List.map_cons] at ih' ⊢
    rw [ih', ren_id]

theorem ren_upd (φ : Addr → Addr) (a b : Addr) (v : Val) (hv : ∀ c, v = .ptr c → c ≠ a) :
    ren (upd φ a b) v = ren φ v := by
  cases v with
  | lit _ => rfl
  | ptr c => simp [ren, upd, hv c rfl]

theorem map_ren_upd (φ : Addr → Addr) (a b : Addr) (fs : List Val)
    (h : ∀ c, .ptr c ∈ fs → c ≠ a) : fs.map (ren (upd φ a b)) = fs.map (ren φ) := by
  apply List.map_congr_left
  intro v hv
  apply ren_upd
  intro c hc
  subst hc
  exact h c hv

theorem hrel_lt {φ : Addr → Addr} {h1 h2 : Heap} {a : Addr} (hr : HRel φ h1 h2)
    (hl : Live h1 a) : φ a < h2.next := by
  obtain ⟨t, fs, rc, hc⟩ := hl
  apply Nat.lt_of_not_le
  intro hle
  have h1 := hr.cell a t fs rc hc
  rw [hr.bounded _ hle] at h1
  exact HCell.noConfusion h1

theorem hrel_id {s : St} (hw : HeapWF s) : HRel id s.heap s.heap where
  cell a t fs rc hc := by
    rw [map_ren_id]
    exact hc
  inj _ _ _ _ h := h
  bounded := hw.bounded

theorem hrel_grow1 {φ : Addr → Addr} {h1 h2 : Heap} (hr : HRel φ h1 h2) : HRel φ h1.grow h2 :=
  ⟨hr.cell, hr.inj, hr.bounded⟩

theorem live_set_obj_cases (h : Heap) (a b : Addr) (t : Nat) (fs : List Val) (rc : Nat)
    (hl : Live (h.set a (.obj t fs rc)) b) : b = a ∨ (b ≠ a ∧ Live h b) := by
  by_cases hba : b = a
  · exact Or.inl hba
  · obtain ⟨t', fs', rc', hc⟩ := hl
    rw [Heap.set_cells_ne _ _ _ _ hba] at hc
    exact Or.inr ⟨hba, t', fs', rc', hc⟩

theorem hrel_set_obj {φ : Addr → Addr} {h1 h2 : Heap} {a : Addr} (hr : HRel φ h1 h2)
    (ha : Live h1 a) (t : Nat) (fs : List Val) (rc : Nat) :
    HRel φ (h1.set a (.obj t fs rc)) (h2.set (φ a) (.obj t (fs.map (ren φ)) rc)) := by
  constructor
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨hba, he⟩ | ⟨hba, hb'⟩
    · rw [hba, Heap.set_cells_self]
      injection he with h1 h2 h3
      rw [h1, h2, h3]
    · have hne : φ b ≠ φ a := fun he => hba (hr.inj b a ⟨t', fs', rc', hb'⟩ ha he)
      rw [Heap.set_cells_ne _ _ _ _ hne]
      exact hr.cell b t' fs' rc' hb'
  · intro b c hb hc hbc
    have hb' : Live h1 b := by
      rcases live_set_obj_cases _ _ _ _ _ _ hb with hba | ⟨_, hbl⟩
      · rw [hba]
        exact ha
      · exact hbl
    have hc' : Live h1 c := by
      rcases live_set_obj_cases _ _ _ _ _ _ hc with hca | ⟨_, hcl⟩
      · rw [hca]
        exact ha
      · exact hcl
    exact hr.inj b c hb' hc' hbc
  · intro b hb
    have hne : b ≠ φ a := ne_of_lt_le (hrel_lt hr ha) hb
    rw [Heap.set_cells_ne _ _ _ _ hne]
    exact hr.bounded b hb

theorem hrel_set_dead {φ : Addr → Addr} {h1 h2 : Heap} {a : Addr} (hr : HRel φ h1 h2)
    (ha : Live h1 a) (c : HCell) (hc : Dead c) :
    HRel φ (h1.set a c) (h2.set (φ a) .free) := by
  constructor
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨_, he⟩ | ⟨hba, hb'⟩
    · exact absurd he (hc t' fs' rc')
    · have hne : φ b ≠ φ a := fun he => hba (hr.inj b a ⟨t', fs', rc', hb'⟩ ha he)
      rw [Heap.set_cells_ne _ _ _ _ hne]
      exact hr.cell b t' fs' rc' hb'
  · intro b c' hb hc' hbc
    have hb' := ((live_set_dead _ _ _ _ hc).mp hb).2
    have hc'' := ((live_set_dead _ _ _ _ hc).mp hc').2
    exact hr.inj b c' hb' hc'' hbc
  · intro b hb
    by_cases hba : b = φ a
    · rw [hba]
      exact Heap.set_cells_self _ _ _
    · rw [Heap.set_cells_ne _ _ _ _ hba]
      exact hr.bounded b hb

theorem hrel_alloc {φ : Addr → Addr} {h1 h2 : Heap} {a : Addr} {vs : List Val}
    (hr : HRel φ h1 h2) (ha : ¬ Live h1 a)
    (hfl : ∀ b t fs rc c, h1.cells b = .obj t fs rc → .ptr c ∈ fs → Live h1 c)
    (hvs : ∀ c, .ptr c ∈ vs → Live h1 c) (t : Nat) :
    HRel (upd φ a h2.next) (h1.set a (.obj t vs 1))
      (h2.alloc (.obj t (vs.map (ren φ)) 1)).2 := by
  have hne : ∀ c, Live h1 c → c ≠ a := fun c hc he => ha (he ▸ hc)
  have hupd : ∀ c, c ≠ a → upd φ a h2.next c = φ c := fun c hc => by simp [upd, hc]
  have hupd_a : upd φ a h2.next a = h2.next := by simp [upd]
  have hcells : ∀ c, c ≠ h2.next →
      (h2.alloc (.obj t (vs.map (ren φ)) 1)).2.cells c = h2.cells c :=
    fun c hc => Heap.set_cells_ne _ _ _ _ hc
  constructor
  · intro b t' fs' rc' hb
    rcases obj_set_cases _ _ _ _ _ _ _ hb with ⟨hba, he⟩ | ⟨hba, hb'⟩
    · injection he with e1 e2 e3
      rw [hba, hupd_a, ← e1, ← e2, ← e3, map_ren_upd φ _ _ vs (fun c hc => hne c (hvs c hc))]
      exact Heap.set_cells_self _ _ _
    · have hl : Live h1 b := ⟨t', fs', rc', hb'⟩
      rw [hupd b hba, hcells _ (Nat.ne_of_lt (hrel_lt hr hl)), hr.cell b t' fs' rc' hb',
        map_ren_upd φ _ _ fs' (fun c hc => hne c (hfl b t' fs' rc' c hb' hc))]
  · intro b c hb hc hbc
    rcases live_set_obj_cases _ _ _ _ _ _ hb with hba | ⟨hba, hbl⟩
    · rcases live_set_obj_cases _ _ _ _ _ _ hc with hca | ⟨hca, hcl⟩
      · rw [hba, hca]
      · exfalso
        rw [hba, hupd_a, hupd c hca] at hbc
        exact Nat.ne_of_lt (hrel_lt hr hcl) hbc.symm
    · rcases live_set_obj_cases _ _ _ _ _ _ hc with hca | ⟨hca, hcl⟩
      · exfalso
        rw [hca, hupd_a, hupd b hba] at hbc
        exact Nat.ne_of_lt (hrel_lt hr hbl) hbc
      · rw [hupd b hba, hupd c hca] at hbc
        exact hr.inj b c hbl hcl hbc
  · intro c hc
    have hc' : h2.next + 1 ≤ c := hc
    rw [hcells c (ne_of_lt_le (Nat.lt_succ_self _) hc')]
    exact hr.bounded c (Nat.le_of_succ_le hc')

theorem sim_alloc {φ : Addr → Addr} {h1 h2 : Heap} {a : Addr} {x : Var} {t : Nat}
    {vs : List Val} {env' : List (Var × Val)} {toks1 toks2 : List (Var × Tok)}
    (hr : HRel φ h1 h2) (ha : ¬ Live h1 a)
    (hfl : ∀ b t fs rc c, h1.cells b = .obj t fs rc → .ptr c ∈ fs → Live h1 c)
    (hvs : ∀ c, .ptr c ∈ vs → Live h1 c) (henv : ∀ y c, (y, .ptr c) ∈ env' → Live h1 c)
    (htk : toks2 = mapBag eraseTok toks1) :
    SimSt (upd φ a h2.next)
      { env := (x, .ptr a) :: env', toks := toks1, heap := h1.set a (.obj t vs 1) }
      { env := (x, .ptr (h2.alloc (.obj t (vs.map (ren φ)) 1)).1) :: mapBag (ren φ) env'
        toks := toks2
        heap := (h2.alloc (.obj t (vs.map (ren φ)) 1)).2 } := by
  refine ⟨hrel_alloc hr ha hfl hvs t, ?_, htk⟩
  have e1 : ren (upd φ a h2.next) (.ptr a) = .ptr h2.next := by
    simp [ren, upd]
  have e2 : mapBag (ren (upd φ a h2.next)) env' = mapBag (ren φ) env' := by
    apply mapBag_congr
    intro y v hy
    apply ren_upd
    intro c hc he
    subst hc
    exact ha (he ▸ henv y c hy)
  show _ = (x, ren (upd φ a h2.next) (.ptr a)) :: mapBag (ren (upd φ a h2.next)) env'
  rw [e1, e2]
  rfl

theorem tagOf_sim {φ : Addr → Addr} {h1 h2 : Heap} {v : Val} (hr : HRel φ h1 h2)
    (hv : PtsLive h1 v) : tagOf h2 (ren φ v) = tagOf h1 v := by
  cases v with
  | lit _ => rfl
  | ptr a =>
    obtain ⟨t, fs, rc, hc⟩ := hv a rfl
    simp [tagOf, ren, hc, hr.cell a t fs rc hc]

theorem incV_sim {φ : Addr → Addr} {h1 h2 : Heap} {v : Val} (hr : HRel φ h1 h2)
    (hv : PtsLive h1 v) :
    ∃ h1' h2', incV h1 v = some h1' ∧ incV h2 (ren φ v) = some h2' ∧ HRel φ h1' h2' := by
  cases v with
  | lit _ => exact ⟨h1, h2, rfl, rfl, hr⟩
  | ptr a =>
    obtain ⟨t, fs, rc, hc⟩ := hv a rfl
    refine ⟨_, _, ?_, ?_, hrel_set_obj hr ⟨t, fs, rc, hc⟩ t fs (rc + 1)⟩
    · simp [incV, hc]
    · simp [incV, ren, hr.cell a t fs rc hc]

theorem decL_sim (φ : Addr → Addr) (n : Nat)
    (ih : ∀ (s1 : St) (h2 : Heap) (v : Val) (P : List Val), HeapWFP s1 (v :: P) →
      HRel φ s1.heap h2 → ORel (HRel φ) (decV n s1.heap v) (decV n h2 (ren φ v))) :
    ∀ (fs : List Val) (s1 : St) (h2 : Heap) (P : List Val), HeapWFP s1 (fs ++ P) →
      HRel φ s1.heap h2 →
      ORel (HRel φ) (decL (decV n) s1.heap fs) (decL (decV n) h2 (fs.map (ren φ))) := by
  intro fs
  induction fs with
  | nil =>
    intro s1 h2 P _ hr
    exact hr
  | cons v vs ihl =>
    intro s1 h2 P hw hr
    have key := ih s1 h2 v (vs ++ P) hw hr
    simp only [decL, List.map_cons]
    cases e1 : decV n s1.heap v with
    | none =>
      cases e2 : decV n h2 (ren φ v) with
      | none => simp [ORel]
      | some _ =>
        rw [e1, e2] at key
        simp [ORel] at key
    | some h1' =>
      cases e2 : decV n h2 (ren φ v) with
      | none =>
        rw [e1, e2] at key
        simp [ORel] at key
      | some h2' =>
        rw [e1, e2] at key
        simp only [Option.bind_some]
        exact ihl { s1 with heap := h1' } h2' P (decV_wf n s1 v (vs ++ P) h1' hw e1) key

theorem decV_sim (φ : Addr → Addr) : ∀ (n : Nat) (s1 : St) (h2 : Heap) (v : Val)
    (P : List Val), HeapWFP s1 (v :: P) → HRel φ s1.heap h2 →
    ORel (HRel φ) (decV n s1.heap v) (decV n h2 (ren φ v)) := by
  intro n
  induction n with
  | zero =>
    intro s1 h2 v P _ hr
    cases v with
    | lit _ => exact hr
    | ptr _ => simp [decV, ren, ORel]
  | succ n ih =>
    intro s1 h2 v P hw hr
    cases v with
    | lit _ => exact hr
    | ptr a =>
      obtain ⟨t, fs, rc, hc⟩ := hw.pendLive a (by simp)
      have hc2 := hr.cell a t fs rc hc
      match rc, hc, hc2 with
      | 0, hc, hc2 => simp [decV, ren, hc, hc2, ORel]
      | 1, hc, hc2 =>
        simp only [decV, ren, hc, hc2]
        exact decL_sim φ n ih fs { s1 with heap := s1.heap.set a .free } _ P (wfp_free hw hc)
          (hrel_set_dead hr ⟨t, fs, 1, hc⟩ .free dead_free)
      | r + 2, hc, hc2 =>
        simp only [decV, ren, hc, hc2]
        exact hrel_set_obj hr ⟨t, fs, r + 2, hc⟩ t fs (r + 1)

/-- **Simulation**: from corresponding states, in-place and pure-allocation evaluation get stuck
    together, or both return, with related results. -/
theorem eval_sim : ∀ (n : Nat) (e : Expr) (s1 s2 : St) (φ : Addr → Addr),
    HeapWF s1 → SimSt φ s1 s2 → ORel SimRes (eval true n e s1) (eval false n e s2) := by
  intro n
  induction n with
  | zero =>
    intro e s1 s2 φ _ _
    simp [eval, ORel]
  | succ n ih =>
    intro e s1 s2 φ hw hs
    obtain ⟨hr, he, ht⟩ := hs
    cases e with
    | ret x =>
      simp only [eval]
      rw [he, lookup_mapBag]
      cases hl : lookup s1.env x with
      | none => simp [ORel]
      | some u =>
        show SimRes (u, s1) (ren φ u, s2)
        exact ⟨φ, hw, hr, envPts hw hl, rfl⟩
    | lit x m k =>
      simp only [eval]
      apply ih k _ _ φ (wf_pushLit hw)
      refine ⟨hr, ?_, ht⟩
      show (x, Val.lit m) :: s2.env = (x, ren φ (.lit m)) :: mapBag (ren φ) s1.env
      rw [he]
      rfl
    | ctor x t ys k =>
      simp only [eval]
      rw [he, takeMany_mapBag]
      cases hm : takeMany s1.env ys with
      | none => simp [ORel]
      | some q =>
        obtain ⟨vs, env'⟩ := q
        obtain ⟨hvs, hsub, _⟩ := takeMany_some s1.env ys vs env' hm
        simp only [Option.map_some]
        apply ih k _ _ (upd φ s1.heap.next s2.heap.next) (wf_stepCtor hw hm)
        refine sim_alloc (a := s1.heap.next) (hrel_grow1 hr) ?_ hw.fieldLive ?_ ?_ ht
        · intro hl
          obtain ⟨t', fs', rc', hc⟩ := hl
          rw [Heap.grow_cells, hw.bounded _ (Nat.le_refl _)] at hc
          exact HCell.noConfusion hc
        · intro c hc
          obtain ⟨y, hy⟩ := hvs _ hc
          exact hw.envLive y c hy
        · intro y c hy
          exact hw.envLive y c (hsub _ hy)
    | proj x y i k =>
      simp only [eval]
      rw [he, lookup_mapBag]
      cases hl : lookup s1.env y with
      | none => simp [ORel]
      | some u =>
        cases u with
        | lit _ => simp [ORel, ren]
        | ptr a =>
          obtain ⟨t, fs, rc, hc⟩ := envPts hw hl a rfl
          have hc2 := hr.cell a t fs rc hc
          simp only [Option.map_some, ren, hc, hc2, List.getElem?_map]
          cases hv : fs[i]? with
          | none => simp [ORel]
          | some u =>
            obtain ⟨h1', h2', hi1, hi2, hr'⟩ := incV_sim hr (fieldPts hw hc hv)
            simp only [Option.map_some, hi1, hi2]
            exact ih k _ _ φ (wf_push hw (fieldPts hw hc hv) hi1) ⟨hr', rfl, ht⟩
    | case x bs =>
      simp only [eval]
      rw [he, lookup_mapBag]
      cases hl : lookup s1.env x with
      | none => simp [ORel]
      | some u =>
        simp only [Option.map_some, tagOf_sim hr (envPts hw hl)]
        cases htg : tagOf s1.heap u with
        | none => simp [ORel]
        | some tg =>
          cases hb : bs[tg]? with
          | none => simp [ORel, hb]
          | some b =>
            simp only [hb]
            exact ih b s1 s2 φ hw ⟨hr, he, ht⟩
    | inc x k =>
      simp only [eval]
      rw [he, lookup_mapBag]
      cases hl : lookup s1.env x with
      | none => simp [ORel]
      | some u =>
        obtain ⟨h1', h2', hi1, hi2, hr'⟩ := incV_sim hr (envPts hw hl)
        simp only [Option.map_some, hi1, hi2]
        exact ih k _ _ φ (wf_push hw (envPts hw hl) hi1) ⟨hr', rfl, ht⟩
    | dec x k =>
      simp only [eval]
      rw [he, take_mapBag]
      cases htk : take s1.env x with
      | none => simp [ORel]
      | some q =>
        obtain ⟨u, env'⟩ := q
        simp only [Option.map_some]
        have key : ORel (HRel φ) (decV n s1.heap u) (decV n s2.heap (ren φ u)) :=
          decV_sim φ n { s1 with env := env' } s2.heap u [] (wfp_take hw htk) hr
        cases e1 : decV n s1.heap u with
        | none =>
          cases e2 : decV n s2.heap (ren φ u) with
          | none => simp [ORel]
          | some _ =>
            rw [e1, e2] at key
            simp [ORel] at key
        | some h1' =>
          cases e2 : decV n s2.heap (ren φ u) with
          | none =>
            rw [e1, e2] at key
            simp [ORel] at key
          | some h2' =>
            rw [e1, e2] at key
            exact ih k _ _ φ (wf_stepDec hw htk e1) ⟨key, rfl, ht⟩
    | reset w x k =>
      simp only [eval]
      rw [he, ht, take_mapBag]
      cases htk : take s1.env x with
      | none => simp [ORel]
      | some q =>
        obtain ⟨u, env'⟩ := q
        simp only [Option.map_some, exclusive_false]
        cases hx : exclusive true s1.heap u with
        | some q2 =>
          obtain ⟨a, fs⟩ := q2
          obtain ⟨rfl, t, hc⟩ := exclusive_some hx
          have hc2 := hr.cell a t fs 1 hc
          simp only [ren]
          cases n with
          | zero => simp [resetV, decV, ORel]
          | succ m =>
            simp only [resetV, decV, hc2]
            have key : ORel (HRel φ) (decL (decV m) (s1.heap.set a .resv) fs)
                (decL (decV m) (s2.heap.set (φ a) .free) (fs.map (ren φ))) :=
              decL_sim φ m (decV_sim φ m) fs _ _ [] (wfp_resetPend w hw htk hc)
                (hrel_set_dead hr ⟨t, fs, 1, hc⟩ .resv dead_resv)
            cases e1 : decL (decV m) (s1.heap.set a .resv) fs with
            | none =>
              cases e2 : decL (decV m) (s2.heap.set (φ a) .free) (fs.map (ren φ)) with
              | none => simp [ORel]
              | some _ =>
                rw [e1, e2] at key
                simp [ORel] at key
            | some h1' =>
              cases e2 : decL (decV m) (s2.heap.set (φ a) .free) (fs.map (ren φ)) with
              | none =>
                rw [e1, e2] at key
                simp [ORel] at key
              | some h2' =>
                rw [e1, e2] at key
                exact ih k _ _ φ (wf_stepResetExcl (n := m + 1) hw htk hc e1) ⟨key, rfl, rfl⟩
        | none =>
          have key : ORel (HRel φ) (decV n s1.heap u) (decV n s2.heap (ren φ u)) :=
            decV_sim φ n { s1 with env := env' } s2.heap u [] (wfp_take hw htk) hr
          cases e1 : decV n s1.heap u with
          | none =>
            cases e2 : decV n s2.heap (ren φ u) with
            | none => simp [ORel]
            | some _ =>
              rw [e1, e2] at key
              simp [ORel] at key
          | some h1' =>
            cases e2 : decV n s2.heap (ren φ u) with
            | none =>
              rw [e1, e2] at key
              simp [ORel] at key
            | some h2' =>
              rw [e1, e2] at key
              exact ih k _ _ φ (wf_stepResetShared hw htk e1) ⟨key, rfl, rfl⟩
    | reuse x w t ys k =>
      simp only [eval]
      rw [he, ht, take_mapBag, takeMany_mapBag]
      cases htk : take s1.toks w with
      | none => simp [ORel]
      | some q =>
        obtain ⟨tk, toks'⟩ := q
        cases hm : takeMany s1.env ys with
        | none =>
          cases tk with
          | null => simp [ORel, eraseTok]
          | slot _ => simp [ORel, eraseTok]
        | some q2 =>
          obtain ⟨vs, env'⟩ := q2
          obtain ⟨hvs, hsub, _⟩ := takeMany_some s1.env ys vs env' hm
          have hvl : ∀ c, .ptr c ∈ vs → Live s1.heap c := by
            intro c hc
            obtain ⟨y, hy⟩ := hvs _ hc
            exact hw.envLive y c hy
          have hel : ∀ y c, (y, .ptr c) ∈ env' → Live s1.heap c :=
            fun y c hy => hw.envLive y c (hsub _ hy)
          simp only [Option.map_some, eraseTok]
          cases tk with
          | null =>
            apply ih k _ _ (upd φ s1.heap.next s2.heap.next) (wf_stepReuseNull hw htk hm)
            refine sim_alloc (a := s1.heap.next) (hrel_grow1 hr) ?_ hw.fieldLive hvl hel rfl
            intro hl
            obtain ⟨t', fs', rc', hc⟩ := hl
            rw [Heap.grow_cells, hw.bounded _ (Nat.le_refl _)] at hc
            exact HCell.noConfusion hc
          | slot a =>
            have hra : s1.heap.cells a = .resv :=
              hw.tokResv w a (take_some w s1.toks _ toks' htk).1
            simp only [hra, ite_true]
            apply ih k _ _ (upd φ a s2.heap.next) (wf_stepReuseSlot hw htk hm)
            refine sim_alloc hr ?_ hw.fieldLive hvl hel rfl
            intro hl
            obtain ⟨t', fs', rc', hc⟩ := hl
            rw [hra] at hc
            exact HCell.noConfusion hc

/-! ## Observables -/

theorem denote_sim {ψ : Addr → Addr} {h1 h2 : Heap} (hr : HRel ψ h1 h2)
    (hfl : ∀ b t fs rc c, h1.cells b = .obj t fs rc → .ptr c ∈ fs → Live h1 c) :
    ∀ (k : Nat) (v : Val), PtsLive h1 v → denote k h2 (ren ψ v) = denote k h1 v := by
  intro k
  induction k with
  | zero =>
    intro v _
    cases v with
    | lit _ => rfl
    | ptr _ => rfl
  | succ k ih =>
    intro v hv
    cases v with
    | lit _ => rfl
    | ptr a =>
      obtain ⟨t, fs, rc, hc⟩ := hv a rfl
      have hc2 := hr.cell a t fs rc hc
      have hfs : ∀ l : List Val, (∀ c, .ptr c ∈ l → Live h1 c) →
          (l.map (ren ψ)).mapM (denote k h2) = l.mapM (denote k h1) := by
        intro l
        induction l with
        | nil =>
          intro _
          rfl
        | cons u us ihl =>
          intro hl
          simp only [List.map_cons, List.mapM_cons]
          have hu : PtsLive h1 u := fun c hc => hl c (List.mem_cons.mpr (Or.inl hc.symm))
          rw [ih u hu, ihl (fun c hc => hl c (List.mem_cons_of_mem _ hc))]
      simp only [denote, ren, hc, hc2]
      rw [hfs fs (fun c hm => hfl a t fs rc c hc hm)]

theorem orel_mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ (o1 : Option α) (o2 : Option β), ORel R o1 o2 → ORel S o1 o2 := by
  intro o1 o2 ho
  cases o1 with
  | none =>
    cases o2 with
    | none => trivial
    | some _ => simp [ORel] at ho
  | some a =>
    cases o2 with
    | none => simp [ORel] at ho
    | some b => exact h a b ho

/-! ## Main theorems -/

/-- **Heap well-formedness preservation** (`WFPreservation`). -/
theorem wfPreservation : WFPreservation :=
  fun inPlace n e s s' v hw h => eval_preserves_wf inPlace n e s s' v hw h

/-- **`reset`/`reuse` soundness** (`ResetReuseSoundness`): in-place and pure-allocation
    evaluation agree on termination and on the observable value, at every read-back depth. -/
theorem resetReuseSoundness : ResetReuseSoundness := by
  intro n e s hw htoks
  have hsim : SimSt id s s := by
    refine ⟨hrel_id hw, (mapBag_ren_id _).symm, ?_⟩
    rw [htoks]
    rfl
  refine orel_mono ?_ _ _ (eval_sim n e s s id hw hsim)
  intro r1 r2 hres k
  obtain ⟨ψ, hw1, hr1, hp1, hv⟩ := hres
  rw [hv, denote_sim hr1 hw1.fieldLive k r1.1 hp1]

/-! ## Syntactic erasure -/

/-- Every token in the bag is `null`. -/
def NullToks (toks : List (Var × Tok)) : Prop :=
  ∀ p, p ∈ toks → p.2 = .null

/-- A pure-allocation run of `e` is a run of `erase e`, which never reads or writes tokens. -/
theorem eval_erase : ∀ (n : Nat) (e : Expr) (s s' : St) (v : Val) (t : List (Var × Tok)),
    NullToks s.toks → eval false n e s = some (v, s') →
    eval false n (erase e) { s with toks := t } = some (v, { s' with toks := t }) := by
  intro n
  induction n with
  | zero =>
    intro e s s' v t _ h
    simp [eval] at h
  | succ n ih =>
    intro e s s' v t hn h
    cases e with
    | ret x =>
      simp only [eval] at h
      cases hl : lookup s.env x with
      | none => simp [hl] at h
      | some u =>
        simp [hl] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [erase, eval, hl]
    | lit x m k =>
      simp only [eval] at h
      simp only [erase, eval]
      refine ih k _ s' v t ?_ h
      exact hn
    | ctor x tg ys k =>
      simp only [eval] at h
      simp only [erase, eval]
      cases hm : takeMany s.env ys with
      | none => simp [hm] at h
      | some q =>
        obtain ⟨vs, env'⟩ := q
        simp only [hm] at h ⊢
        refine ih k _ s' v t ?_ h
        exact hn
    | proj x y i k =>
      simp only [eval] at h
      simp only [erase, eval]
      cases hl : lookup s.env y with
      | none => simp [hl] at h
      | some u =>
        cases u with
        | lit _ => simp [hl] at h
        | ptr a =>
          cases hc : s.heap.cells a with
          | free => simp [hl, hc] at h
          | resv => simp [hl, hc] at h
          | obj tg fs rc =>
            cases hv : fs[i]? with
            | none => simp [hl, hc, hv] at h
            | some u =>
              cases hi : incV s.heap u with
              | none => simp [hl, hc, hv, hi] at h
              | some h' =>
                simp only [hl, hc, hv, hi] at h ⊢
                refine ih k _ s' v t ?_ h
                exact hn
    | case x bs =>
      simp only [eval] at h
      simp only [erase, eval, List.getElem?_map]
      cases hl : lookup s.env x with
      | none => simp [hl] at h
      | some u =>
        cases htg : tagOf s.heap u with
        | none => simp [hl, htg] at h
        | some tg =>
          cases hb : bs[tg]? with
          | none => simp [hl, htg, hb] at h
          | some b =>
            simp only [hl, htg, hb] at h
            simp only [htg, hb, Option.map_some]
            exact ih b s s' v t hn h
    | inc x k =>
      simp only [eval] at h
      simp only [erase, eval]
      cases hl : lookup s.env x with
      | none => simp [hl] at h
      | some u =>
        cases hi : incV s.heap u with
        | none => simp [hl, hi] at h
        | some h' =>
          simp only [hl, hi] at h ⊢
          refine ih k _ s' v t ?_ h
          exact hn
    | dec x k =>
      simp only [eval] at h
      simp only [erase, eval]
      cases htk : take s.env x with
      | none => simp [htk] at h
      | some q =>
        obtain ⟨u, env'⟩ := q
        cases hd : decV n s.heap u with
        | none => simp [htk, hd] at h
        | some h' =>
          simp only [htk, hd] at h ⊢
          refine ih k _ s' v t ?_ h
          exact hn
    | reset w x k =>
      simp only [eval, exclusive_false] at h
      simp only [erase, eval]
      cases htk : take s.env x with
      | none => simp [htk] at h
      | some q =>
        obtain ⟨u, env'⟩ := q
        cases hd : decV n s.heap u with
        | none => simp [htk, hd] at h
        | some h' =>
          simp only [htk, hd] at h ⊢
          have hn' : NullToks ((w, .null) :: s.toks) := by
            intro p hp
            rcases List.mem_cons.mp hp with hp | hp
            · rw [hp]
            · exact hn p hp
          refine ih k _ s' v t ?_ h
          exact hn'
    | reuse x w tg ys k =>
      simp only [eval] at h
      simp only [erase, eval]
      cases htk : take s.toks w with
      | none => simp [htk] at h
      | some q =>
        obtain ⟨tk, toks'⟩ := q
        obtain ⟨hmem, hsub⟩ := take_some w s.toks tk toks' htk
        have htn : tk = .null := hn _ hmem
        subst htn
        have hn' : NullToks toks' := fun p hp => hn p (hsub p hp)
        cases hm : takeMany s.env ys with
        | none => simp [htk, hm] at h
        | some q2 =>
          obtain ⟨vs, env'⟩ := q2
          simp only [htk, hm] at h ⊢
          refine ih k _ s' v t ?_ h
          exact hn'

/-- **Erasure soundness** (`EraseSoundness`): an in-place run is matched by the syntactically
    erased program (`reset` ↦ `dec`, `reuse` ↦ `ctor`) with the same observable value. -/
theorem eraseSoundness : EraseSoundness := by
  intro n e s s1 v1 hw htoks h1
  have key := resetReuseSoundness n e s hw htoks
  rw [h1] at key
  cases h2 : eval false n e s with
  | none =>
    rw [h2] at key
    simp [ORel] at key
  | some r2 =>
    rw [h2] at key
    obtain ⟨v2, s2⟩ := r2
    have hn : NullToks s.toks := by
      rw [htoks]
      intro p hp
      simp at hp
    exact ⟨(v2, { s2 with toks := s.toks }), eval_erase n e s s2 v2 s.toks hn h2, key⟩

/-! ## Witnesses -/

/-- A heap holding `cs` at addresses `0, 1, …`. -/
def mkHeap (cs : List HCell) : Heap :=
  { cells := fun a => cs.getD a .free, next := cs.length }

theorem mkHeap_free (cs : List HCell) (a : Addr) (ha : cs.length ≤ a) :
    (mkHeap cs).cells a = .free := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih =>
    cases a with
    | zero => simp at ha
    | succ a =>
      have ha' : cs.length ≤ a := by
        simp only [List.length_cons] at ha
        omega
      have h := ih a ha'
      simp only [mkHeap, List.getD_cons_succ] at h ⊢
      exact h

/-- A token-free state. -/
def mkSt (env : List (Var × Val)) (cs : List HCell) : St :=
  { env := env, toks := [], heap := mkHeap cs }

/-- `x3 := 42`, `w9 := reset x0`, `x2 := reuse w9 in ctor_1 [x3]`, `ret x2`. -/
def progReuse : Expr :=
  .lit 3 42 (.reset 9 0 (.reuse 2 9 1 [3] (.ret 2)))

/-- The same program, returning `x1` (an alias of the reset object, when there is one). -/
def progAlias : Expr :=
  .lit 3 42 (.reset 9 0 (.reuse 2 9 1 [3] (.ret 1)))

/-- `x0` owns cell 0 = `ctor_0 [cell 1]`, which owns cell 1 = `ctor_7 []`. -/
def exclSt : St :=
  mkSt [(0, .ptr 0)] [.obj 0 [.ptr 1] 1, .obj 7 [] 1]

/-- As `exclSt`, but cell 0 is shared by `x0` and `x1` (`rc = 2`). -/
def sharedSt : St :=
  mkSt [(0, .ptr 0), (1, .ptr 0)] [.obj 0 [.ptr 1] 2, .obj 7 [] 1]

/-- Ill-accounted: cell 0 is shared by `x0` and `x1` but claims `rc = 1`. -/
def badSt : St :=
  mkSt [(0, .ptr 0), (1, .ptr 0)] [.obj 0 [.ptr 1] 1, .obj 7 [] 1]

/-- Returned value. -/
def resVal (r : Option (Val × St)) : Option Val :=
  r.map (·.1)

/-- A cell of the final heap. -/
def resCell (r : Option (Val × St)) (a : Addr) : Option HCell :=
  r.map (·.2.heap.cells a)

/-- Next fresh address of the final heap. -/
def resNext (r : Option (Val × St)) : Option Addr :=
  r.map (·.2.heap.next)

/-- Observable value (read back to depth 4). -/
def resObs (r : Option (Val × St)) : Option (Option Tree) :=
  r.map fun q => denote 4 q.2.heap q.1

-- Exclusive (`rc = 1`): `reuse` writes the result into slot 0 in place, the child is released,
-- nothing is allocated; the pure run allocates a fresh cell 2 and frees cell 0.
#guard resVal (eval true 10 progReuse exclSt) == some (.ptr 0)
#guard resCell (eval true 10 progReuse exclSt) 0 == some (.obj 1 [.lit 42] 1)
#guard resCell (eval true 10 progReuse exclSt) 1 == some .free
#guard resNext (eval true 10 progReuse exclSt) == some 2
#guard resVal (eval false 10 progReuse exclSt) == some (.ptr 2)
#guard resCell (eval false 10 progReuse exclSt) 0 == some .free
#guard resNext (eval false 10 progReuse exclSt) == some 3
#guard resObs (eval true 10 progReuse exclSt) == some (some (.node 1 [.lit 42]))
#guard resObs (eval false 10 progReuse exclSt) == some (some (.node 1 [.lit 42]))

-- Shared (`rc = 2`): `reset` only decrements, `reuse` falls back to a fresh cell, and the alias
-- `x1` still denotes the original object in both modes.
#guard resVal (eval true 10 progReuse sharedSt) == some (.ptr 2)
#guard resCell (eval true 10 progReuse sharedSt) 0 == some (.obj 0 [.ptr 1] 1)
#guard resObs (eval true 10 progReuse sharedSt) == some (some (.node 1 [.lit 42]))
#guard resObs (eval true 10 progAlias sharedSt) == some (some (.node 0 [.node 7 []]))
#guard resObs (eval false 10 progAlias sharedSt) == some (some (.node 0 [.node 7 []]))

-- Negative: on the ill-accounted `badSt` (not `HeapWF`) the in-place run overwrites the object
-- still visible through `x1`, while the pure run frees it: the hypothesis cannot be dropped.
#guard resObs (eval true 10 progAlias badSt) == some (some (.node 1 [.lit 42]))
#guard resObs (eval false 10 progAlias badSt) == some none

-- Negative: an unbalanced program (two `dec`s of one credit) is stuck in both modes.
#guard (eval true 10 (.dec 0 (.dec 0 (.ret 0))) exclSt).isNone
#guard (eval false 10 (.dec 0 (.dec 0 (.ret 0))) exclSt).isNone

theorem exclSt_wf : HeapWF exclSt := by
  constructor
  · intro a ha
    exact mkHeap_free _ a ha
  · intro x a hx
    simp only [exclSt, mkSt, List.mem_singleton, Prod.mk.injEq, Val.ptr.injEq] at hx
    rw [hx.2]
    exact ⟨0, [.ptr 1], 1, rfl⟩
  · intro a ha
    simp at ha
  · intro b t fs rc a hb hm
    rcases b with _ | _ | b
    · simp only [exclSt, mkSt, mkHeap, List.getD_cons_zero, HCell.obj.injEq] at hb
      rw [← hb.2.1] at hm
      simp only [List.mem_singleton, Val.ptr.injEq] at hm
      rw [hm]
      exact ⟨7, [], 1, rfl⟩
    · simp only [exclSt, mkSt, mkHeap, List.getD_cons_succ, List.getD_cons_zero,
        HCell.obj.injEq] at hb
      rw [← hb.2.1] at hm
      simp at hm
    · simp [exclSt, mkSt, mkHeap] at hb
  · intro w a hw
    simp [exclSt, mkSt] at hw
  · intro a ha
    rcases a with _ | _ | a
    · simp [exclSt, mkSt, mkHeap] at ha
    · simp [exclSt, mkSt, mkHeap] at ha
    · simp [exclSt, mkSt, mkHeap] at ha
  · intro a t fs rc ha
    rcases a with _ | _ | a
    · simp only [exclSt, mkSt, mkHeap, List.getD_cons_zero, HCell.obj.injEq] at ha
      omega
    · simp only [exclSt, mkSt, mkHeap, List.getD_cons_succ, List.getD_cons_zero,
        HCell.obj.injEq] at ha
      omega
    · simp [exclSt, mkSt, mkHeap] at ha
  · intro a t fs rc ha
    rcases a with _ | _ | a
    · simp only [exclSt, mkSt, mkHeap, List.getD_cons_zero, HCell.obj.injEq] at ha
      rw [← ha.2.2]
      decide
    · simp only [exclSt, mkSt, mkHeap, List.getD_cons_succ, List.getD_cons_zero,
        HCell.obj.injEq] at ha
      rw [← ha.2.2]
      decide
    · simp [exclSt, mkSt, mkHeap] at ha

theorem sharedSt_wf : HeapWF sharedSt := by
  constructor
  · intro a ha
    exact mkHeap_free _ a ha
  · intro x a hx
    simp only [sharedSt, mkSt, List.mem_cons, Prod.mk.injEq, Val.ptr.injEq,
      List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [hx.2]
      exact ⟨0, [.ptr 1], 2, rfl⟩
    · rw [hx.2]
      exact ⟨0, [.ptr 1], 2, rfl⟩
  · intro a ha
    simp at ha
  · intro b t fs rc a hb hm
    rcases b with _ | _ | b
    · simp only [sharedSt, mkSt, mkHeap, List.getD_cons_zero, HCell.obj.injEq] at hb
      rw [← hb.2.1] at hm
      simp only [List.mem_singleton, Val.ptr.injEq] at hm
      rw [hm]
      exact ⟨7, [], 1, rfl⟩
    · simp only [sharedSt, mkSt, mkHeap, List.getD_cons_succ, List.getD_cons_zero,
        HCell.obj.injEq] at hb
      rw [← hb.2.1] at hm
      simp at hm
    · simp [sharedSt, mkSt, mkHeap] at hb
  · intro w a hw
    simp [sharedSt, mkSt] at hw
  · intro a ha
    rcases a with _ | _ | a
    · simp [sharedSt, mkSt, mkHeap] at ha
    · simp [sharedSt, mkSt, mkHeap] at ha
    · simp [sharedSt, mkSt, mkHeap] at ha
  · intro a t fs rc ha
    rcases a with _ | _ | a
    · simp only [sharedSt, mkSt, mkHeap, List.getD_cons_zero, HCell.obj.injEq] at ha
      omega
    · simp only [sharedSt, mkSt, mkHeap, List.getD_cons_succ, List.getD_cons_zero,
        HCell.obj.injEq] at ha
      omega
    · simp [sharedSt, mkSt, mkHeap] at ha
  · intro a t fs rc ha
    rcases a with _ | _ | a
    · simp only [sharedSt, mkSt, mkHeap, List.getD_cons_zero, HCell.obj.injEq] at ha
      rw [← ha.2.2]
      decide
    · simp only [sharedSt, mkSt, mkHeap, List.getD_cons_succ, List.getD_cons_zero,
        HCell.obj.injEq] at ha
      rw [← ha.2.2]
      decide
    · simp [sharedSt, mkSt, mkHeap] at ha

/-- The negative witness violates exact accounting (two owners, `rc = 1`). -/
theorem badSt_not_wf : ¬ HeapWF badSt := by
  intro hw
  have h := hw.rcExact 0 0 [.ptr 1] 1 rfl
  revert h
  decide

/-- Positive witness, as a theorem: the exclusive object is reused in place. -/
theorem exclSt_reuses_in_place : resVal (eval true 10 progReuse exclSt) = some (.ptr 0) := by
  decide

/-- Positive witness, as a theorem: the shared object is not reused. -/
theorem sharedSt_allocates_fresh :
    resVal (eval true 10 progReuse sharedSt) = some (.ptr 2) := by
  decide

end LeanNative.Proofs.H3.RcCore
