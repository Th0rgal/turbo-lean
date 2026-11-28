/-!
# H3.1 Step 1: a core calculus for reference counting with `reset`/`reuse` (`RcCore.lean`)

A self-contained first-order calculus in the style of λRC (Ullrich & de Moura, *Counting
Immutable Beans*), independent of the lowerer. It is the specification half of H3.1 Step 1;
the proofs are in `RcCoreReuse.lean`.

**Values and heap.** A value is a scalar `lit n` or a pointer `ptr a`. A heap cell is `free`, a
constructor object `obj tag fields rc`, or `resv`: a slot that `reset` reserved for a later
`reuse` (its fields already released, owned by exactly one token). Fresh cells are allocated at
`Heap.next`, so a freed address is never handed out again by `alloc`.

**Ownership is explicit.** The environment is a bag of owned references: each `(x, v)` entry is
one credit of `v` held under the name `x`, and `lookup` reads the first one. `inc x` pushes one
more credit, `dec x` and `ctor`/`reuse` arguments consume one, `proj` returns an owned (already
incremented) field. A program that consumes a credit it does not hold gets stuck (`none`), so
the semantics itself rejects unbalanced RC code. Tokens produced by `reset` live in a separate
bag, so they can only be consumed by `reuse`.

**`reset w x`** consumes `x`. If the evaluator runs in in-place mode (`inPlace = true`), `x`
points to an object and `rc = 1` (exclusive), its fields are released, the cell becomes `resv`
and `w` holds `slot a`. Otherwise `x` is decremented as by `dec` and `w` holds `null`.
**`reuse x w t ys`** consumes the token `w`: on `slot a` it writes `obj t ys 1` into `a` in
place, on `null` it allocates a fresh cell.

`eval false` is the pure-allocation semantics: `reset` is `dec` and every `reuse` allocates.
`erase` is the same thing syntactically (`reset` ↦ `dec`, `reuse` ↦ `ctor`).

**Heap well-formedness** (`HeapWF`) is the exact ownership accounting invariant: allocation is
bounded by `next`; every pointer held by the environment or a live object points to a live
object; every token slot is reserved and every reserved cell has exactly one token; every live
object has `rc ≥ 1`; and `rc` equals the number of environment credits plus the number of heap
fields that point to it. `HeapWFP s pend` is the same invariant with a list `pend` of
references that are still to be released (used inside the recursive `dec` cascade).

**Conjectures.** `WFPreservation` (balanced RC evaluation preserves `HeapWF`, in both modes) and
`ResetReuseSoundness` (from a well-formed state, in-place and pure-allocation evaluation both
get stuck or both return values with the same denotation) are stated at the end and proved in
`RcCoreReuse.lean`, together with `EraseSoundness` against the syntactic erasure.
-/

namespace LeanNative.Proofs.H3.RcCore

/-- Program variables. -/
abbrev Var := Nat

/-- Heap addresses. -/
abbrev Addr := Nat

/-- Runtime values: unboxed scalars and heap pointers. -/
inductive Val where
  | lit (n : Nat)
  | ptr (a : Addr)
  deriving DecidableEq, Repr

/-- `reset` tokens: a reserved slot, or `null` when the object was shared. -/
inductive Tok where
  | null
  | slot (a : Addr)
  deriving DecidableEq, Repr

/-- Heap cells. `resv` is a slot reserved by `reset` for a later `reuse`. -/
inductive HCell where
  | free
  | obj (tag : Nat) (fields : List Val) (rc : Nat)
  | resv
  deriving DecidableEq, Repr

/-- A heap: cells plus the next fresh address. -/
structure Heap where
  cells : Addr → HCell
  next : Addr

/-- Overwrite one cell. -/
def Heap.set (h : Heap) (a : Addr) (c : HCell) : Heap :=
  { h with cells := fun b => if b = a then c else h.cells b }

/-- Make room for one more cell (the new address `h.next` is still `free`). -/
def Heap.grow (h : Heap) : Heap :=
  { h with next := h.next + 1 }

/-- Fresh allocation at `h.next`. -/
def Heap.alloc (h : Heap) (c : HCell) : Addr × Heap :=
  (h.next, h.grow.set h.next c)

/-- The empty heap. -/
def Heap.empty : Heap :=
  { cells := fun _ => .free, next := 0 }

/-- Programs (first-order, administrative normal form). -/
inductive Expr where
  /-- Return the value of `x`. -/
  | ret (x : Var)
  /-- `x := n` (scalar). -/
  | lit (x : Var) (n : Nat) (k : Expr)
  /-- `x := ctor_t ys`: consumes one credit of each `y`, allocates with `rc = 1`. -/
  | ctor (x : Var) (t : Nat) (ys : List Var) (k : Expr)
  /-- `x := proj_i y; inc x`: borrows `y`, returns an owned field. -/
  | proj (x : Var) (y : Var) (i : Nat) (k : Expr)
  /-- Branch on the tag of an object (or on the value of a scalar); borrows `x`. -/
  | case (x : Var) (bs : List Expr)
  /-- Add one credit to `x`. -/
  | inc (x : Var) (k : Expr)
  /-- Consume one credit of `x`. -/
  | dec (x : Var) (k : Expr)
  /-- `w := reset x`: consumes `x`. -/
  | reset (w : Var) (x : Var) (k : Expr)
  /-- `x := reuse w in ctor_t ys`: consumes the token `w` and one credit of each `y`. -/
  | reuse (x : Var) (w : Var) (t : Nat) (ys : List Var) (k : Expr)
  deriving Repr

/-- Read the first entry for `x` in a bag. -/
def lookup {α : Type} : List (Var × α) → Var → Option α
  | [], _ => none
  | (y, v) :: rest, x => if y = x then some v else lookup rest x

/-- Remove the first entry for `x` from a bag, returning its value. -/
def take {α : Type} : List (Var × α) → Var → Option (α × List (Var × α))
  | [], _ => none
  | (y, v) :: rest, x =>
    if y = x then some (v, rest)
    else (take rest x).map fun p => (p.1, (y, v) :: p.2)

/-- Consume one credit of each variable, in order. -/
def takeMany : List (Var × Val) → List Var → Option (List Val × List (Var × Val))
  | env, [] => some ([], env)
  | env, y :: ys =>
    match take env y with
    | none => none
    | some (v, env') =>
      (takeMany env' ys).map fun p => (v :: p.1, p.2)

/-- Increment the count of a value (no-op on scalars). -/
def incV (h : Heap) : Val → Option Heap
  | .lit _ => some h
  | .ptr a =>
    match h.cells a with
    | .obj t fs rc => some (h.set a (.obj t fs (rc + 1)))
    | _ => none

/-- Release a list of references, in order, with a given single-reference release. -/
def decL (d : Heap → Val → Option Heap) : Heap → List Val → Option Heap
  | h, [] => some h
  | h, v :: vs => (d h v).bind fun h' => decL d h' vs

/-- Decrement the count of a value; at `rc = 1` free the cell and release its fields.
    The first argument is fuel for the release cascade. -/
def decV : Nat → Heap → Val → Option Heap
  | _, h, .lit _ => some h
  | 0, _, .ptr _ => none
  | n + 1, h, .ptr a =>
    match h.cells a with
    | .obj t fs (rc + 2) => some (h.set a (.obj t fs (rc + 1)))
    | .obj _ fs 1 => decL (decV n) (h.set a .free) fs
    | _ => none

/-- Exclusive `reset` of the object at `a` with fields `fs`: reserve the slot and release the
    fields (same fuel discipline as `decV`). -/
def resetV : Nat → Heap → Addr → List Val → Option Heap
  | 0, _, _, _ => none
  | n + 1, h, a, fs => decL (decV n) (h.set a .resv) fs

/-- The exclusivity test of `reset`: an object with `rc = 1`, and only in in-place mode. -/
def exclusive (inPlace : Bool) (h : Heap) : Val → Option (Addr × List Val)
  | .ptr a =>
    if inPlace then
      match h.cells a with
      | .obj _ fs 1 => some (a, fs)
      | _ => none
    else none
  | .lit _ => none

/-- Scrutinee of `case`: an object's tag, or a scalar's value. -/
def tagOf (h : Heap) : Val → Option Nat
  | .lit n => some n
  | .ptr a =>
    match h.cells a with
    | .obj t _ _ => some t
    | _ => none

/-- Machine state: owned environment credits, `reset` tokens, heap. -/
structure St where
  env : List (Var × Val)
  toks : List (Var × Tok)
  heap : Heap

/-- Fuel-indexed big-step evaluation. `inPlace = true` lets `reset`/`reuse` recycle exclusive
    cells; `inPlace = false` is the pure-allocation semantics. -/
def eval (inPlace : Bool) : Nat → Expr → St → Option (Val × St)
  | 0, _, _ => none
  | _ + 1, .ret x, s => (lookup s.env x).map fun v => (v, s)
  | n + 1, .lit x m k, s => eval inPlace n k { s with env := (x, .lit m) :: s.env }
  | n + 1, .ctor x t ys k, s =>
    match takeMany s.env ys with
    | none => none
    | some (vs, env') =>
      let p := s.heap.alloc (.obj t vs 1)
      eval inPlace n k { s with env := (x, .ptr p.1) :: env', heap := p.2 }
  | n + 1, .proj x y i k, s =>
    match lookup s.env y with
    | some (.ptr a) =>
      match s.heap.cells a with
      | .obj _ fs _ =>
        match fs[i]? with
        | none => none
        | some v =>
          match incV s.heap v with
          | none => none
          | some h' => eval inPlace n k { s with env := (x, v) :: s.env, heap := h' }
      | _ => none
    | _ => none
  | n + 1, .case x bs, s =>
    match lookup s.env x with
    | none => none
    | some v =>
      match tagOf s.heap v with
      | none => none
      | some t =>
        match bs[t]? with
        | none => none
        | some b => eval inPlace n b s
  | n + 1, .inc x k, s =>
    match lookup s.env x with
    | none => none
    | some v =>
      match incV s.heap v with
      | none => none
      | some h' => eval inPlace n k { s with env := (x, v) :: s.env, heap := h' }
  | n + 1, .dec x k, s =>
    match take s.env x with
    | none => none
    | some (v, env') =>
      match decV n s.heap v with
      | none => none
      | some h' => eval inPlace n k { s with env := env', heap := h' }
  | n + 1, .reset w x k, s =>
    match take s.env x with
    | none => none
    | some (v, env') =>
      match exclusive inPlace s.heap v with
      | some (a, fs) =>
        match resetV n s.heap a fs with
        | none => none
        | some h' =>
          eval inPlace n k { env := env', toks := (w, .slot a) :: s.toks, heap := h' }
      | none =>
        match decV n s.heap v with
        | none => none
        | some h' =>
          eval inPlace n k { env := env', toks := (w, .null) :: s.toks, heap := h' }
  | n + 1, .reuse x w t ys k, s =>
    match take s.toks w, takeMany s.env ys with
    | some (.slot a, toks'), some (vs, env') =>
      if s.heap.cells a = .resv then
        eval inPlace n k
          { env := (x, .ptr a) :: env', toks := toks', heap := s.heap.set a (.obj t vs 1) }
      else none
    | some (.null, toks'), some (vs, env') =>
      let p := s.heap.alloc (.obj t vs 1)
      eval inPlace n k { env := (x, .ptr p.1) :: env', toks := toks', heap := p.2 }
    | _, _ => none

/-- Syntactic erasure to the pure-allocation program: `reset` ↦ `dec`, `reuse` ↦ `ctor`. -/
def erase : Expr → Expr
  | .ret x => .ret x
  | .lit x n k => .lit x n (erase k)
  | .ctor x t ys k => .ctor x t ys (erase k)
  | .proj x y i k => .proj x y i (erase k)
  | .case x bs => .case x (bs.map erase)
  | .inc x k => .inc x (erase k)
  | .dec x k => .dec x (erase k)
  | .reset _ x k => .dec x (erase k)
  | .reuse x _ t ys k => .ctor x t ys (erase k)

/-! ## Ownership accounting -/

/-- `1` if the value points to `a`. -/
def valRef (a : Addr) : Val → Nat
  | .ptr b => if b = a then 1 else 0
  | .lit _ => 0

/-- Number of pointers to `a` in a list of values. -/
def cntV (a : Addr) : List Val → Nat
  | [] => 0
  | v :: vs => valRef a v + cntV a vs

/-- Number of environment credits pointing to `a`. -/
def envRefs (a : Addr) : List (Var × Val) → Nat
  | [] => 0
  | p :: r => valRef a p.2 + envRefs a r

/-- `1` if the token is the slot `a`. -/
def tokRef (a : Addr) : Tok → Nat
  | .slot b => if b = a then 1 else 0
  | .null => 0

/-- Number of tokens holding the slot `a`. -/
def tokRefs (a : Addr) : List (Var × Tok) → Nat
  | [] => 0
  | p :: r => tokRef a p.2 + tokRefs a r

/-- Number of fields of a cell pointing to `a` (non-objects have none). -/
def cellRefs (a : Addr) : HCell → Nat
  | .obj _ fs _ => cntV a fs
  | _ => 0

/-- `f 0 + ⋯ + f (n - 1)`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + f n

/-- Number of heap fields (over all allocated cells) pointing to `a`. -/
def heapRefs (h : Heap) (a : Addr) : Nat :=
  sumBelow (fun b => cellRefs a (h.cells b)) h.next

/-- `a` holds a live object. -/
def Live (h : Heap) (a : Addr) : Prop :=
  ∃ t fs rc, h.cells a = .obj t fs rc

/-- Every pointer in `v` is live. -/
def PtsLive (h : Heap) (v : Val) : Prop :=
  ∀ a, v = .ptr a → Live h a

/-- Heap well-formedness with a list `pend` of references still to be released. -/
structure HeapWFP (s : St) (pend : List Val) : Prop where
  /-- Allocation is bounded by `next`. -/
  bounded : ∀ a, s.heap.next ≤ a → s.heap.cells a = .free
  /-- Environment pointers are live. -/
  envLive : ∀ x a, (x, .ptr a) ∈ s.env → Live s.heap a
  /-- Pending pointers are live. -/
  pendLive : ∀ a, .ptr a ∈ pend → Live s.heap a
  /-- Child pointers of live objects are live. -/
  fieldLive : ∀ b t fs rc a, s.heap.cells b = .obj t fs rc → .ptr a ∈ fs → Live s.heap a
  /-- Token slots are reserved cells. -/
  tokResv : ∀ w a, (w, .slot a) ∈ s.toks → s.heap.cells a = .resv
  /-- Each reserved cell is owned by exactly one token. -/
  resvTok : ∀ a, s.heap.cells a = .resv → tokRefs a s.toks = 1
  /-- Live objects have a positive count. -/
  rcPos : ∀ a t fs rc, s.heap.cells a = .obj t fs rc → 1 ≤ rc
  /-- Exact ownership accounting. -/
  rcExact : ∀ a t fs rc, s.heap.cells a = .obj t fs rc →
    rc = envRefs a s.env + heapRefs s.heap a + cntV a pend

/-- Heap well-formedness: `HeapWFP` with nothing pending. -/
def HeapWF (s : St) : Prop :=
  HeapWFP s []

/-! ## Observables -/

/-- Heap-independent denotation of a value. -/
inductive Tree where
  | lit (n : Nat)
  | node (tag : Nat) (cs : List Tree)
  deriving Repr, BEq

/-- Read back a value as a tree (fuel bounds the depth). -/
def denote : Nat → Heap → Val → Option Tree
  | _, _, .lit n => some (.lit n)
  | 0, _, .ptr _ => none
  | k + 1, h, .ptr a =>
    match h.cells a with
    | .obj t fs _ => (fs.mapM (denote k h)).map (.node t)
    | _ => none

/-- Two optional results: both stuck, or both defined and related. -/
def ORel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

/-- Same observable value at every read-back depth. -/
def SameObs (r1 r2 : Val × St) : Prop :=
  ∀ k, denote k r1.2.heap r1.1 = denote k r2.2.heap r2.1

/-! ## Conjectures (proved in `RcCoreReuse.lean`) -/

/-- Balanced RC evaluation preserves heap well-formedness (either mode). -/
def WFPreservation : Prop :=
  ∀ (inPlace : Bool) (n : Nat) (e : Expr) (s s' : St) (v : Val),
    HeapWF s → eval inPlace n e s = some (v, s') → HeapWF s' ∧ PtsLive s'.heap v

/-- `reset`/`reuse` soundness: from a well-formed token-free state, in-place and
    pure-allocation evaluation both get stuck, or both return the same observable value. -/
def ResetReuseSoundness : Prop :=
  ∀ (n : Nat) (e : Expr) (s : St), HeapWF s → s.toks = [] →
    ORel SameObs (eval true n e s) (eval false n e s)

/-- An in-place run is matched by the syntactically erased (pure-allocation) program. -/
def EraseSoundness : Prop :=
  ∀ (n : Nat) (e : Expr) (s s1 : St) (v1 : Val), HeapWF s → s.toks = [] →
    eval true n e s = some (v1, s1) →
    ∃ r2, eval false n (erase e) s = some r2 ∧ SameObs (v1, s1) r2

end LeanNative.Proofs.H3.RcCore
