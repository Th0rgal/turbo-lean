import TurboLean.ConLeche

/-
  TurboLean.ElabAudit (Milestone M3):
  1. `HeaderPin` statement-spoofing prevention (`checkNoShadowedConsts`, `renderExplicitAST`,
     `verifyHeaderPin`) ensuring elaborated theorem statements match their pinned AST without
     binder-shadowed constants.
  2. `LNIR_EXPR_V1` Content-Addressable Storage (CAS) proof replay (`serializeExprV1`,
     `parseExprV1`, `replayCASProofBlob`) verifying deserialized binary proof terms directly
     through the `ConLeche` dependent CIC kernel (`inferType` + `isDefEq`).
-/

namespace TurboLean.ElabAudit

/-- Closed-context dependent CIC typing judgment alias (`ConLeche.HasType env prf ty`) in
    `TurboLean.ElabAudit` matching `Contract V4 M3`. -/
abbrev ConLeche.HasType (env : _root_.ConLeche.Env) (e ty : _root_.ConLeche.Expr) : Prop :=
  _root_.ConLeche.HasType env [] e ty

open _root_.ConLeche hiding HasType

/-- Recursively verify that every `.const name _` node in `e` is registered in `globalConsts`
    and is not shadowed by any local binder in `boundNames`. -/
def checkNoShadowedConsts (globalConsts boundNames : List String) : Expr → Bool
  | .bvar _ => true
  | .sort _ => true
  | .const name _ => !(boundNames.contains name) && globalConsts.contains name
  | .app fn arg =>
    checkNoShadowedConsts globalConsts boundNames fn &&
    checkNoShadowedConsts globalConsts boundNames arg
  | .lam dom body =>
    checkNoShadowedConsts globalConsts boundNames dom &&
    checkNoShadowedConsts globalConsts boundNames body
  | .forallE dom body =>
    checkNoShadowedConsts globalConsts boundNames dom &&
    checkNoShadowedConsts globalConsts boundNames body
  | .letE ty val body =>
    checkNoShadowedConsts globalConsts boundNames ty &&
    checkNoShadowedConsts globalConsts boundNames val &&
    checkNoShadowedConsts globalConsts boundNames body

/-- Render a `ConLeche.Level` into an explicit canonical S-expression string (`pp.all=true`). -/
def renderExplicitLevel : Level → String
  | .zero => "0"
  | .succ u => s!"(succ {renderExplicitLevel u})"
  | .max u v => s!"(max {renderExplicitLevel u} {renderExplicitLevel v})"
  | .imax u v => s!"(imax {renderExplicitLevel u} {renderExplicitLevel v})"
  | .param p => s!"(param {p})"

/-- Render a `ConLeche.Expr` into an explicit, fully-parenthesized canonical S-expression string
    with zero implicit argument elision (`pp.all=true`, `pp.universes=true`). -/
def renderExplicitAST : Expr → String
  | .bvar idx => s!"(bvar {idx})"
  | .sort u => s!"(sort {renderExplicitLevel u})"
  | .const name lvls =>
    let lvlStr := String.intercalate " " (lvls.map renderExplicitLevel)
    s!"(const {name} [{lvlStr}])"
  | .app fn arg => s!"(app {renderExplicitAST fn} {renderExplicitAST arg})"
  | .lam dom body => s!"(lam {renderExplicitAST dom} {renderExplicitAST body})"
  | .forallE dom body => s!"(forallE {renderExplicitAST dom} {renderExplicitAST body})"
  | .letE ty val body =>
    s!"(letE {renderExplicitAST ty} {renderExplicitAST val} {renderExplicitAST body})"

/-- Pinned theorem header specification (`specpin.lock` entry) for `HeaderPin`. -/
structure PinnedHeaderSpec where
  declName      : String
  pinnedTypeAst : Expr
  globalConsts  : List String
  boundNames    : List String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Surface header AST (`SurfaceSig`) produced by the Lean surface parser or `reparseExplicit`
    over an explicit `pp.all = true`, `pp.universes = true`, `pp.explicit = true` signature:
    - `declName`: pinned theorem name,
    - `coreAst`: parsed `ConLeche.Expr` core statement AST,
    - `explicitText`: canonical explicit surface rendering (`renderExplicitAST`),
    - `globalConsts`: in-scope global constant names,
    - `boundNames`: local binder names introduced in the surface header,
    - `annotationSpanCount`: surface syntax annotation/macro-expansion span count (erased by `eraseAnnotations`). -/
structure SurfaceSig where
  declName            : String
  coreAst             : Expr
  explicitText        : String
  globalConsts        : List String
  boundNames          : List String
  annotationSpanCount : Nat := 0
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Count how many constants referenced in `e` are either shadowed by a local binder in
    `boundNames` or absent from `globalConsts` (spoofed/unresolved constant reference). -/
def countShadowedOrUnresolvedConsts (globalConsts boundNames : List String) : Expr → Nat
  | .bvar _ => 0
  | .sort _ => 0
  | .const name _ =>
    if boundNames.contains name || !(globalConsts.contains name) then 1 else 0
  | .app fn arg =>
    countShadowedOrUnresolvedConsts globalConsts boundNames fn +
    countShadowedOrUnresolvedConsts globalConsts boundNames arg
  | .lam dom body =>
    countShadowedOrUnresolvedConsts globalConsts boundNames dom +
    countShadowedOrUnresolvedConsts globalConsts boundNames body
  | .forallE dom body =>
    countShadowedOrUnresolvedConsts globalConsts boundNames dom +
    countShadowedOrUnresolvedConsts globalConsts boundNames body
  | .letE ty val body =>
    countShadowedOrUnresolvedConsts globalConsts boundNames ty +
    countShadowedOrUnresolvedConsts globalConsts boundNames val +
    countShadowedOrUnresolvedConsts globalConsts boundNames body

/-- Count how many local binders in `surf.boundNames` shadow a global constant in `surf.globalConsts`
    or how many constant occurrences in `surf.coreAst` are shadowed/unresolved. -/
def shadowedBindersCount (surf : SurfaceSig) : Nat :=
  (surf.boundNames.filter (fun b => surf.globalConsts.contains b)).length +
  countShadowedOrUnresolvedConsts surf.globalConsts surf.boundNames surf.coreAst

/-- Collect all constant names referenced in a `ConLeche.Expr` AST. -/
def collectExprConsts : Expr → List String
  | .bvar _ => []
  | .sort _ => []
  | .const name _ => [name]
  | .app fn arg => collectExprConsts fn ++ collectExprConsts arg
  | .lam dom body => collectExprConsts dom ++ collectExprConsts body
  | .forallE dom body => collectExprConsts dom ++ collectExprConsts body
  | .letE ty val body => collectExprConsts ty ++ collectExprConsts val ++ collectExprConsts body

/-- Render a kernel `ConLeche.Expr` with full explicit universe levels and binder types
    (`pp.all = true`, `pp.universes = true`, `pp.explicit = true`). -/
def ppExplicit (kType : Expr) : String × Expr :=
  (renderExplicitAST kType, kType)

/-- Reparse an explicit `ppExplicit` rendering `(text, kType)` into a canonical `SurfaceSig`
    with `globalConsts := collectExprConsts kType`, `boundNames := []`, and `annotationSpanCount := 0`. -/
def reparseExplicit (rendered : String × Expr) : SurfaceSig :=
  { declName := ""
    coreAst := rendered.2
    explicitText := rendered.1
    globalConsts := collectExprConsts rendered.2
    boundNames := []
    annotationSpanCount := 0 }

/-- Erase surface-only syntax annotations, declaration labels, and binder lists from `surf`,
    projecting to the canonical `(coreAst, explicitText)` pair for statement-equivalence comparison. -/
def eraseAnnotations (surf : SurfaceSig) : SurfaceSig :=
  { declName := ""
    coreAst := surf.coreAst
    explicitText := surf.explicitText
    globalConsts := collectExprConsts surf.coreAst
    boundNames := []
    annotationSpanCount := 0 }

/-- Verify that a human-written surface signature `surf : SurfaceSig` matches the kernel-elaborated
    theorem type `kType : ConLeche.Expr` (`HeaderPin` Contract V4 M3):
    1. `!surf.declName.isEmpty`: non-empty declaration name,
    2. `shadowedBindersCount surf == 0`: zero binder shadowing or unresolved constant spoofing,
    3. `checkNoShadowedConsts surf.globalConsts surf.boundNames kType`: kernel type references only unshadowed globals,
    4. `decide (eraseAnnotations (reparseExplicit (ppExplicit kType)) = eraseAnnotations surf)`:
       explicit pretty-printing and reparsing of `kType` matches `surf` after annotation erasure. -/
def verifyHeaderPin (surf : SurfaceSig) (kType : Expr) : Bool :=
  !surf.declName.isEmpty &&
  decide (shadowedBindersCount surf = 0) &&
  checkNoShadowedConsts surf.globalConsts surf.boundNames kType &&
  decide (eraseAnnotations (reparseExplicit (ppExplicit kType)) = eraseAnnotations surf)

/-- Convert a `PinnedHeaderSpec` into its canonical `SurfaceSig`. -/
def PinnedHeaderSpec.toSurfaceSig (spec : PinnedHeaderSpec) : SurfaceSig :=
  { declName := spec.declName
    coreAst := spec.pinnedTypeAst
    explicitText := renderExplicitAST spec.pinnedTypeAst
    globalConsts := spec.globalConsts
    boundNames := spec.boundNames
    annotationSpanCount := 0 }

/-- Verify that an elaborated theorem statement `elaboratedTy` matches `spec : PinnedHeaderSpec`. -/
def verifyHeaderPinSpec (spec : PinnedHeaderSpec) (elaboratedTy : Expr) : Bool :=
  !spec.declName.isEmpty &&
  checkNoShadowedConsts spec.globalConsts spec.boundNames elaboratedTy &&
  decide (elaboratedTy = spec.pinnedTypeAst)

/-- Verify `HeaderPin` along with an explicit `pp.all=true` surface representation `surfaceAstStr`:
    rejects any macro/notation expansion or constant-shadowing spoof whose rendered explicit AST
    differs from `renderExplicitAST spec.pinnedTypeAst`. -/
def verifyHeaderPinSurface (spec : PinnedHeaderSpec) (elaboratedTy : Expr) (surfaceAstStr : String) : Bool :=
  verifyHeaderPinSpec spec elaboratedTy &&
  decide (surfaceAstStr = renderExplicitAST spec.pinnedTypeAst)

/-- A misleading macro expansion or shadowed constant spoofs `spec` whenever its elaborated
    expression `spoofedTy` either diverges from `spec.pinnedTypeAst` or references a constant outside
    the unshadowed `spec.globalConsts \ spec.boundNames` scope. -/
def IsStatementSpoof (spec : PinnedHeaderSpec) (spoofedTy : Expr) : Prop :=
  spoofedTy ≠ spec.pinnedTypeAst ∨
  checkNoShadowedConsts spec.globalConsts spec.boundNames spoofedTy = false

/-! ## `LNIR_EXPR_V1` Binary CAS Proof Term Serialization & Kernel Replay -/

/-- 4-byte magic prefix `"LNE1"` (`[0x4C, 0x4E, 0x45, 0x31]`) for `LNIR_EXPR_V1` CAS proof blobs. -/
def lnirExprV1Magic : List UInt8 := [0x4C, 0x4E, 0x45, 0x31]

/-- Serialize a `ConLeche.Expr` proof term into a binary `LNIR_EXPR_V1` CAS blob (`List UInt8`). -/
def serializeExprV1 (e : Expr) : List UInt8 :=
  lnirExprV1Magic ++ encodeOleanExpr e

/-- Serialize a `ConLeche.Expr` proof term into a binary `LNIR_EXPR_V1` CAS `ByteArray`. -/
def encodeExprBlob (e : Expr) : ByteArray :=
  ByteArray.mk (serializeExprV1 e).toArray

/-- Parse a binary `LNIR_EXPR_V1` CAS blob (`List UInt8`) into a `ConLeche.Expr` proof term,
    verifying the 4-byte `"LNE1"` magic header, decoding the binary AST, and verifying
    exact byte consumption (`offEnd == blob.length`). -/
def parseExprV1 (blob : List UInt8) : Option Expr :=
  match blob with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    if b0 == 0x4C && b1 == 0x4E && b2 == 0x45 && b3 == 0x31 then
      match decodeOleanExpr 64 (ByteArray.mk blob.toArray) 4 with
      | some (prf, offEnd) => if offEnd == blob.length then some prf else none
      | none => none
    else
      none
  | _ => none

/-- Decode a binary `LNIR_EXPR_V1` CAS `ByteArray` into a `ConLeche.Expr` proof term:
    1. Verifies minimum size (`blob.size ≥ 6`) and `"LNE1"` magic (`0x4C, 0x4E, 0x45, 0x31`),
    2. Decodes the binary expression starting at byte offset 4 via `decodeOleanExpr 64 blob 4`,
    3. Verifies exact byte consumption (`offEnd == blob.size`) with zero trailing garbage. -/
def decodeExprBlob (blob : ByteArray) : Except String Expr :=
  if blob.size < 6 then
    .error "decodeExprBlob: truncated LNIR_EXPR_V1 blob (< 6 bytes)"
  else if !(blob.get! 0 == 0x4C && blob.get! 1 == 0x4E && blob.get! 2 == 0x45 && blob.get! 3 == 0x31) then
    .error "decodeExprBlob: invalid LNIR_EXPR_V1 magic header (expected LNE1)"
  else
    match decodeOleanExpr 64 blob 4 with
    | some (prf, offEnd) =>
      if offEnd == blob.size then .ok prf
      else .error "decodeExprBlob: trailing unconsumed bytes in LNIR_EXPR_V1 blob"
    | none => .error "decodeExprBlob: malformed LNIR_EXPR_V1 expression stream"

/-- Verify a cached `LNIR_EXPR_V1` CAS proof `ByteArray` against `expectedType` inside the
    `ConLeche` dependent CIC kernel (`Contract V4 M3`):
    1. Decodes `proofTerm` via `decodeExprBlob blob`,
    2. Infers `expectedType : .sort u` and `proofTerm : prfTy` via `ConLeche.inferType 64 env []`,
    3. Checks definitional equality `ConLeche.isDefEq 64 env prfTy expectedType = true`. -/
def verifyCasProofBlob (env : Env) (expectedType : Expr) (blob : ByteArray) : Bool :=
  match decodeExprBlob blob with
  | .error _ => false
  | .ok proofTerm =>
    match inferType 64 env [] expectedType, inferType 64 env [] proofTerm with
    | some (.sort _), some prfTy => isDefEq 64 env prfTy expectedType
    | _, _ => false

/-- Replay a cached `LNIR_EXPR_V1` CAS proof blob (`List UInt8`) against `expectedTy` inside the
    `ConLeche` dependent CIC kernel. -/
def replayCASProofBlob (env : Env) (blob : List UInt8) (expectedTy : Expr) : Option Expr :=
  match parseExprV1 blob with
  | none => none
  | some prf =>
    match inferType 64 env [] expectedTy, inferType 64 env [] prf with
    | some (.sort _), some prfTy =>
      if isDefEq 64 env prfTy expectedTy then some prf else none
    | _, _ => none

/-- Milestone M3 (Item 1, Contract V4): Surface header round-trip gate (`header_pin_prevents_statement_spoofing`, `0 sorryAx`).
    Guarantees the elaborated `ConstantInfo.type` (`kType`) matches the human-written surface AST (`surf`)
    without macro spoofing or binder shadowing. -/
theorem header_pin_prevents_statement_spoofing (surf : SurfaceSig) (kType : ConLeche.Expr)
    (h_pin : verifyHeaderPin surf kType = true) :
    eraseAnnotations (reparseExplicit (ppExplicit kType)) = eraseAnnotations surf ∧
    shadowedBindersCount surf = 0 := by
  unfold verifyHeaderPin at h_pin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_pin
  rcases h_pin with ⟨⟨⟨_hne, hshadow⟩, _hconsts⟩, herase⟩
  exact ⟨herase, hshadow⟩

/-- Spec-record variant of `header_pin_prevents_statement_spoofing` over `PinnedHeaderSpec`. -/
theorem header_pin_spec_prevents_statement_spoofing (spec : PinnedHeaderSpec) (elaboratedTy : Expr)
    (h_pin : verifyHeaderPinSpec spec elaboratedTy = true) :
    elaboratedTy = spec.pinnedTypeAst ∧
    checkNoShadowedConsts spec.globalConsts spec.boundNames elaboratedTy = true ∧
    renderExplicitAST elaboratedTy = renderExplicitAST spec.pinnedTypeAst := by
  unfold verifyHeaderPinSpec at h_pin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_pin
  rcases h_pin with ⟨⟨_hne, hnoShadow⟩, heq⟩
  refine ⟨heq, hnoShadow, ?_⟩
  rw [heq]

/-- Any misleading macro or constant-shadowing spoof (`IsStatementSpoof spec spoofedTy`) is
    provably rejected by `verifyHeaderPinSpec` (`verifyHeaderPinSpec spec spoofedTy = false`). -/
theorem verifyHeaderPin_rejects_statement_spoof (spec : PinnedHeaderSpec) (spoofedTy : Expr)
    (h_spoof : IsStatementSpoof spec spoofedTy) :
    verifyHeaderPinSpec spec spoofedTy = false := by
  cases h_v : verifyHeaderPinSpec spec spoofedTy with
  | false => rfl
  | true =>
    have ⟨heq, hnoShadow, _⟩ := header_pin_spec_prevents_statement_spoofing spec spoofedTy h_v
    rcases h_spoof with hne | hshadow
    · exact False.elim (hne heq)
    · rw [hnoShadow] at hshadow
      contradiction

/-- Full surface + kernel AST `HeaderPin` soundness (`verifyHeaderPinSurface_sound`):
    when `verifyHeaderPinSurface spec elaboratedTy surfaceAstStr = true`, the elaborated type
    equals `spec.pinnedTypeAst`, no constant is shadowed, and the explicit `pp.all=true` surface
    string matches `renderExplicitAST elaboratedTy`. -/
theorem verifyHeaderPinSurface_sound (spec : PinnedHeaderSpec) (elaboratedTy : Expr)
    (surfaceAstStr : String)
    (h_surf : verifyHeaderPinSurface spec elaboratedTy surfaceAstStr = true) :
    elaboratedTy = spec.pinnedTypeAst ∧
    checkNoShadowedConsts spec.globalConsts spec.boundNames elaboratedTy = true ∧
    surfaceAstStr = renderExplicitAST elaboratedTy := by
  unfold verifyHeaderPinSurface at h_surf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_surf
  rcases h_surf with ⟨h_pin, h_str⟩
  have ⟨heq, hnoShadow, hrender⟩ := header_pin_spec_prevents_statement_spoofing spec elaboratedTy h_pin
  refine ⟨heq, hnoShadow, ?_⟩
  rw [h_str, hrender]

/-- Milestone M3 (Item 2, Contract V4): Replaying a cached `LNIR_EXPR_V1` proof witness through
    `con-leche` is sound regardless of how the untrusted elaborator originally found it
    (`cas_proof_replay_sound`, `0 sorryAx`). -/
theorem cas_proof_replay_sound (env : ConLeche.Env) (expectedType : ConLeche.Expr) (blob : ByteArray)
    (h_replay : verifyCasProofBlob env expectedType blob = true) :
    ∃ (proofTerm : ConLeche.Expr), decodeExprBlob blob = .ok proofTerm ∧
      ConLeche.HasType env proofTerm expectedType := by
  unfold verifyCasProofBlob at h_replay
  cases hdec : decodeExprBlob blob with
  | error _ => simp [hdec] at h_replay
  | ok proofTerm =>
    simp only [hdec] at h_replay
    cases hty : inferType 64 env [] expectedType with
    | none => simp [hty] at h_replay
    | some expSort =>
      cases expSort with
      | sort u =>
        cases hprf : inferType 64 env [] proofTerm with
        | none => simp [hty, hprf] at h_replay
        | some prfTy =>
          simp only [hty, hprf] at h_replay
          have hHasExp : _root_.ConLeche.HasType env [] expectedType (.sort u) :=
            inferType_sound 64 env [] expectedType (.sort u) hty
          have hHasPrf : _root_.ConLeche.HasType env [] proofTerm prfTy :=
            inferType_sound 64 env [] proofTerm prfTy hprf
          exact ⟨proofTerm, rfl, _root_.ConLeche.HasType.conv hHasPrf hHasExp h_replay⟩
      | _ => simp [hty] at h_replay

/-- List-based variant of `cas_proof_replay_sound` for `replayCASProofBlob`. -/
theorem replayCASProofBlob_sound (env : Env) (blob : List UInt8) (expectedTy prf : Expr)
    (h_replay : replayCASProofBlob env blob expectedTy = some prf) :
    parseExprV1 blob = some prf ∧
    _root_.ConLeche.HasType env [] prf expectedTy := by
  unfold replayCASProofBlob at h_replay
  cases hparse : parseExprV1 blob with
  | none => simp [hparse] at h_replay
  | some parsedPrf =>
    simp only [hparse] at h_replay
    cases hty : inferType 64 env [] expectedTy with
    | none => simp [hty] at h_replay
    | some expSort =>
      cases expSort with
      | sort u =>
        cases hprf : inferType 64 env [] parsedPrf with
        | none => simp [hty, hprf] at h_replay
        | some prfTy =>
          simp only [hty, hprf] at h_replay
          split at h_replay
          · rename_i hdefeq
            injection h_replay with heqPrf
            subst heqPrf
            have hHasExp : _root_.ConLeche.HasType env [] expectedTy (.sort u) :=
              inferType_sound 64 env [] expectedTy (.sort u) hty
            have hHasPrf : _root_.ConLeche.HasType env [] parsedPrf prfTy :=
              inferType_sound 64 env [] parsedPrf prfTy hprf
            exact ⟨rfl, _root_.ConLeche.HasType.conv hHasPrf hHasExp hdefeq⟩
          · contradiction
      | _ => simp [hty] at h_replay

/-- Replay a pinned theorem statement (`spec : PinnedHeaderSpec`) and a distilled `LNIR_EXPR_V1`
    CAS proof blob (`blob : List UInt8`) directly into a `ConLeche.Decl` inside `env`,
    bypassing `Lean.Elab` while enforcing both `HeaderPin` anti-spoofing and `ConLeche` kernel
    typechecking. -/
def replayPinnedCASDecl (env : Env) (spec : PinnedHeaderSpec) (elaboratedTy : Expr)
    (blob : List UInt8) : Option Decl :=
  if verifyHeaderPinSpec spec elaboratedTy then
    match replayCASProofBlob env blob elaboratedTy with
    | some prf =>
      some { name := spec.declName, ty := elaboratedTy, val := prf, wfTag := true }
    | none => none
  else
    none

/-- Machine-checked soundness of `replayPinnedCASDecl` (`replayPinnedCASDecl_sound`, `0 sorryAx`):
    any replayed declaration `d` satisfies `CICValid env d`, preserves `spec.pinnedTypeAst`
    with zero constant shadowing, and decodes `d.val` from `blob`. -/
theorem replayPinnedCASDecl_sound (env : Env) (spec : PinnedHeaderSpec) (elaboratedTy : Expr)
    (blob : List UInt8) (d : Decl)
    (h_rep : replayPinnedCASDecl env spec elaboratedTy blob = some d) :
    d.name = spec.declName ∧
    d.ty = spec.pinnedTypeAst ∧
    checkNoShadowedConsts spec.globalConsts spec.boundNames d.ty = true ∧
    parseExprV1 blob = some d.val ∧
    CICValid env d := by
  unfold replayPinnedCASDecl at h_rep
  split at h_rep
  · rename_i h_pin
    cases h_cas : replayCASProofBlob env blob elaboratedTy with
    | none => simp [h_cas] at h_rep
    | some prf =>
      simp only [h_cas, Option.some.injEq] at h_rep
      subst h_rep
      have ⟨heqTy, hnoShadow, _⟩ := header_pin_spec_prevents_statement_spoofing spec elaboratedTy h_pin
      have ⟨hparse, hHasType⟩ := replayCASProofBlob_sound env blob elaboratedTy prf h_cas
      unfold replayCASProofBlob at h_cas
      rw [hparse] at h_cas
      cases hty : inferType 64 env [] elaboratedTy with
      | none => simp [hty] at h_cas
      | some expSort =>
        cases expSort with
        | sort u =>
          have hSort : _root_.ConLeche.HasType env [] elaboratedTy (.sort u) :=
            inferType_sound 64 env [] elaboratedTy (.sort u) hty
          exact ⟨rfl, heqTy, hnoShadow, hparse, ⟨rfl, ⟨u, hSort⟩, hHasType⟩⟩
        | _ => simp [hty] at h_cas
  · contradiction

/-! ## Executable Mutant-Kill Conformance Guards (`>= 3` Mutants Killed) -/

/-- Valid reference surface header for `∀ (x : Sort 0), Sort 0`. -/
def validPinnedKernelType : Expr :=
  .forallE (.sort .zero) (.sort .zero)

def validPinnedSurfaceSig : SurfaceSig :=
  { declName := "thm_id_prop"
    coreAst := validPinnedKernelType
    explicitText := renderExplicitAST validPinnedKernelType
    globalConsts := []
    boundNames := []
    annotationSpanCount := 2 }

-- Positive sanity guard: `verifyHeaderPin` accepts the genuine unshadowed statement even when
-- surface syntax carries non-zero `annotationSpanCount`.
#guard verifyHeaderPin validPinnedSurfaceSig validPinnedKernelType == true

/-- Mutant 1 (Macro-Spoofing Mutant Killed): a misleading notation/macro expansion that rewrites
    the kernel type from `∀ (x : Sort 0), Sort 0` to `.sort .zero` (`True`-like triviality) is
    deterministically rejected by `verifyHeaderPin`. -/
def mutant1MacroSpoofedKernelType : Expr :=
  .sort .zero

#guard verifyHeaderPin validPinnedSurfaceSig mutant1MacroSpoofedKernelType == false

/-- Mutant 2 (Binder-Shadowing Mutant Killed): a surface signature where a local binder `"Nat.add"`
    shadows a global constant `"Nat.add"` (`shadowedBindersCount > 0`) is deterministically rejected
    by `verifyHeaderPin` even if the core AST matches `kType`. -/
def mutant2ShadowedBinderSurfaceSig : SurfaceSig :=
  { declName := "thm_shadowed"
    coreAst := .const "Nat.add" []
    explicitText := renderExplicitAST (.const "Nat.add" [])
    globalConsts := ["Nat.add"]
    boundNames := ["Nat.add"]
    annotationSpanCount := 0 }

#guard shadowedBindersCount mutant2ShadowedBinderSurfaceSig == 2
#guard verifyHeaderPin mutant2ShadowedBinderSurfaceSig (.const "Nat.add" []) == false

/-- Mutant 3 (Corrupted / Wrong-Type `LNIR_EXPR_V1` CAS Proof Blob Killed):
    - Valid proof term `.lam (.sort .zero) (.bvar 0)` has type `.forallE (.sort .zero) (.sort .zero)`
      and is accepted by `verifyCasProofBlob`.
    - A tampered `LNIR_EXPR_V1` blob whose proof term has type `.sort (.succ .zero)` instead of
      `.forallE (.sort .zero) (.sort .zero)` (or has trailing/corrupted bytes) is deterministically
      rejected by `verifyCasProofBlob`. -/
def validCasEnv : Env :=
  { decls := [], headerMagic := 0x4F4C454E }

def validCasProofBlob : ByteArray :=
  encodeExprBlob (.lam (.sort .zero) (.bvar 0))

def mutant3WrongTypeCasProofBlob : ByteArray :=
  encodeExprBlob (.sort .zero)

def mutant3TruncatedCasProofBlob : ByteArray :=
  ByteArray.mk #[0x4C, 0x4E, 0x45, 0x31, 0x04]

#guard verifyCasProofBlob validCasEnv validPinnedKernelType validCasProofBlob == true
#guard verifyCasProofBlob validCasEnv validPinnedKernelType mutant3WrongTypeCasProofBlob == false
#guard verifyCasProofBlob validCasEnv validPinnedKernelType mutant3TruncatedCasProofBlob == false

end TurboLean.ElabAudit
