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

open ConLeche

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

/-- Verify that an elaborated theorem statement `elaboratedTy` matches `spec : PinnedHeaderSpec`:
    1. `checkNoShadowedConsts` confirms no constant in `elaboratedTy` is shadowed by `spec.boundNames`
       or missing from `spec.globalConsts`.
    2. Structural AST equality (`decide (elaboratedTy = spec.pinnedTypeAst)`) holds. -/
def verifyHeaderPin (spec : PinnedHeaderSpec) (elaboratedTy : Expr) : Bool :=
  !spec.declName.isEmpty &&
  checkNoShadowedConsts spec.globalConsts spec.boundNames elaboratedTy &&
  decide (elaboratedTy = spec.pinnedTypeAst)

/-! ## `LNIR_EXPR_V1` Binary CAS Proof Term Serialization & Kernel Replay -/

/-- 4-byte magic prefix `"LNE1"` (`[0x4C, 0x4E, 0x45, 0x31]`) for `LNIR_EXPR_V1` CAS proof blobs. -/
def lnirExprV1Magic : List UInt8 := [0x4C, 0x4E, 0x45, 0x31]

/-- Serialize a `ConLeche.Expr` proof term into a binary `LNIR_EXPR_V1` CAS blob. -/
def serializeExprV1 (e : Expr) : List UInt8 :=
  lnirExprV1Magic ++ encodeOleanExpr e

/-- Parse a binary `LNIR_EXPR_V1` CAS blob into a `ConLeche.Expr` proof term,
    verifying the 4-byte `"LNE1"` magic header, decoding the self-delimiting binary AST, and
    verifying exact byte consumption (`rest == []`). -/
def parseExprV1 (blob : List UInt8) : Option Expr :=
  match blob with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    if b0 == 0x4C && b1 == 0x4E && b2 == 0x45 && b3 == 0x31 then
      match decodeOleanExprStream rest with
      | some (prf, []) => some prf
      | _ => none
    else
      none
  | _ => none

/-- Exact round-trip inversion for `LNIR_EXPR_V1` binary CAS proof term serialization. -/
theorem parseExprV1_serializeExprV1_roundtrip (e : Expr) :
    parseExprV1 (serializeExprV1 e) = some e := by
  have h := decodeOleanExprStream_encodeOleanExpr e []
  rw [List.append_nil] at h
  simp [parseExprV1, serializeExprV1, lnirExprV1Magic, h]

/-- Replay a cached `LNIR_EXPR_V1` CAS proof blob against `expectedTy` inside the `ConLeche`
    dependent CIC kernel:
    1. Deserializes `prf` via `parseExprV1 blob`.
    2. Infers `expectedTy : .sort u` and `prf : prfTy` via `ConLeche.inferType 64 env []`.
    3. Verifies definitional equality `ConLeche.isDefEq 64 env prfTy expectedTy = true`. -/
def replayCASProofBlob (env : Env) (blob : List UInt8) (expectedTy : Expr) : Option Expr :=
  match parseExprV1 blob with
  | none => none
  | some prf =>
    match inferType 64 env [] expectedTy, inferType 64 env [] prf with
    | some (.sort _), some prfTy =>
      if isDefEq 64 env prfTy expectedTy then some prf else none
    | _, _ => none

/-- Milestone M3 (Item 1): Machine-checked anti-spoofing soundness of `verifyHeaderPin`
    (`header_pin_prevents_statement_spoofing`, `0 sorryAx`). -/
theorem header_pin_prevents_statement_spoofing (spec : PinnedHeaderSpec) (elaboratedTy : Expr)
    (h_pin : verifyHeaderPin spec elaboratedTy = true) :
    elaboratedTy = spec.pinnedTypeAst ∧
    checkNoShadowedConsts spec.globalConsts spec.boundNames elaboratedTy = true ∧
    renderExplicitAST elaboratedTy = renderExplicitAST spec.pinnedTypeAst := by
  unfold verifyHeaderPin at h_pin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_pin
  rcases h_pin with ⟨⟨_hne, hnoShadow⟩, heq⟩
  refine ⟨heq, hnoShadow, ?_⟩
  rw [heq]

/-- Milestone M3 (Item 2): Machine-checked soundness of `LNIR_EXPR_V1` CAS proof replay
    (`cas_proof_replay_sound`, `0 sorryAx`). -/
theorem cas_proof_replay_sound (env : Env) (blob : List UInt8) (expectedTy prf : Expr)
    (h_replay : replayCASProofBlob env blob expectedTy = some prf) :
    parseExprV1 blob = some prf ∧
    HasType env [] prf expectedTy := by
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
            have hHasExp : HasType env [] expectedTy (.sort u) :=
              inferType_sound 64 env [] expectedTy (.sort u) hty
            have hHasPrf : HasType env [] parsedPrf prfTy :=
              inferType_sound 64 env [] parsedPrf prfTy hprf
            exact ⟨rfl, HasType.conv hHasPrf hHasExp hdefeq⟩
          · contradiction
      | _ => simp [hty] at h_replay

end TurboLean.ElabAudit
