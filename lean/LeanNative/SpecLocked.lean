import LeanNative.Proofs.RealLCNFBridgeProofs

/-!
# `H1.F` — Frozen Specification Lock for the H1 theorem (`SpecLocked.lean`)

**Why this file exists.** `roadmap/HORIZONS.md` leaf `H1.F`: "Statement of the H1 theorem frozen
and pinned" (accept: hash pin). The H1 theorem is `LeanNative.Proofs.lowerRealLCNFDecl_sound`
(`lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean`), the one proved `LCNF → LNIR` path — the
statement `docs/TRUSTED_BASE.md` §4 cites, and the fixed target rung `L2` builds against
(`HF → L2` in the work graph). This file is the Contract V1 lock
(`roadmap/VALIDATION_CONTRACTS.md`): workers never edit it; a change to the frozen statement is a
deliberate re-freeze, visible as a diff of this file plus a new pinned hash.

**What is frozen.** `h1_lowerRealLCNFDecl_sound_frozen` below restates the live theorem's
signature verbatim and proves it by delegation to the live theorem. The honest shape
(`roadmap/HORIZONS.md`, "Reliability measures"): forward simulation on successful runs — if the
lowering succeeds (`h_lower`) and the source evaluation succeeds at fuel `fuel` (`h_eval`), the
`LNIR` evaluation of the lowered body under the argument-bound environment gives the same result
at the same fuel. What it does **not** cover is recorded in `roadmap/HORIZONS.md` ("What the
review found"): no user calls, no recursion, and the `BridgeHelpers` context construction around
it is unproved until `L1`.

**How the pin enforces the freeze (dual level, Contract V1).**
1. *Kernel level (this file, every `lake build` of the `LeanNative` library)*: the `#eval` gate
   below re-reads both `ConstantInfo.type`s from the elaboration environment and fails the build
   unless (a) the live theorem's type is structurally equal (`Expr` `==`) to the frozen copy's
   after one measured normalization (below), and (b) the live type's in-kernel structural hash
   (`Expr.hash`) equals `pinnedH1StatementHash`. A weakening of the live theorem additionally
   breaks the delegation proof. The hash is a measured constant of the pinned toolchain
   (`lean/lean-toolchain`, `leanprover/lean4:v4.35.0`); a toolchain bump that changes `Expr`
   hashing is itself a re-freeze event and re-measures the pin.
2. *File level (review time)*: the SHA-256 of this file is recorded in the freezing commit
   (`spec_hash_before == spec_hash_after` in Contract V1/V5 review); `turbo-lean pr-verify
   --mode untrusted --disallow-statement-changes` is the Rust-side enforcement of the same lock.

**Matcher normalization (measured, 2026-11-26, v4.35.0).** The statement's pattern lambda
`fun acc (p, val) => …` elaborates to an auxiliary matcher constant named under its host
declaration (`LeanNative.Proofs.lowerRealLCNFDecl_sound.match_1` in the live type,
`….h1_lowerRealLCNFDecl_sound_frozen.match_1` in the frozen copy), so a cross-declaration verbatim
restatement is never raw-`==` to the live type. The gate therefore rewrites exactly that one
constant name in the frozen type before comparing; every other difference still fails the build.

**Known limits.** `Expr` `==` (`Expr.eqv`) and `Expr.hash` do not distinguish binder *names*, so
a pure binder rename does not trip the pin (not a semantic change). The pin compares the
elaborated statement, so a change beneath the statement (to `lowerRealLCNFDecl` itself, or the
semantics) is out of this file's scope — that is what the proof, `AxiomAudit` and the
differential gates guard.
-/

namespace LeanNative.SpecLocked

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- **Frozen H1 statement** (`H1.F`). Verbatim copy of the signature of
`LeanNative.Proofs.lowerRealLCNFDecl_sound` at freeze time (2026-11-26, graph state R0d of
`roadmap/HORIZONS.md`), proved by delegation. If the live theorem is weakened so that it no
longer discharges this statement, this file stops compiling. -/
theorem h1_lowerRealLCNFDecl_sound_frozen (fuel : Nat) (ctx : RealBridgeCtx)
    (decl : Lean.Compiler.LCNF.Decl .impure) (args : List Val) (hst hst' : HeapState) (v : Val)
    (d : LNIRDecl) (mangled : String)
    (h_lower : lowerRealLCNFDecl fuel ctx decl mangled = .ok d)
    (h_eval : evalRealLCNFDecl fuel ctx decl args hst = .ok (v, hst')) :
    evalCode fuel ((d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty) hst d.body =
      .ok (v, hst') :=
  LeanNative.Proofs.lowerRealLCNFDecl_sound fuel ctx decl args hst hst' v d mangled h_lower h_eval

/-- Pinned in-kernel structural hash (`Lean.Expr.hash`) of the `ConstantInfo.type` of
`LeanNative.Proofs.lowerRealLCNFDecl_sound`, measured on `leanprover/lean4:v4.35.0`.
Re-measure only as a deliberate re-freeze (the gate below prints the measured value on
mismatch). -/
def pinnedH1StatementHash : UInt64 := 306234630

/- `H1.F` hash-pin gate: runs at every elaboration of this module (`lake build`), so the
`LeanNative` library cannot build with a drifted H1 statement. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let some live := env.find? ``LeanNative.Proofs.lowerRealLCNFDecl_sound
    | throwError "[h1f-spec-lock] live H1 theorem LeanNative.Proofs.lowerRealLCNFDecl_sound is missing from the environment"
  let some frozen := env.find? ``h1_lowerRealLCNFDecl_sound_frozen
    | throwError "[h1f-spec-lock] frozen H1 statement LeanNative.SpecLocked.h1_lowerRealLCNFDecl_sound_frozen is missing from the environment"
  -- Measured normalization (see module docstring): the pattern-lambda matcher is named under its
  -- host declaration, so rewrite the frozen copy's matcher constant to the live theorem's name
  -- before comparing. Everything else must match structurally.
  let frozenMatcher := Name.str ``h1_lowerRealLCNFDecl_sound_frozen "match_1"
  let liveMatcher := Name.str ``LeanNative.Proofs.lowerRealLCNFDecl_sound "match_1"
  let normalized := frozen.type.replace fun e =>
    match e with
    | .const n us => if n == frozenMatcher then some (.const liveMatcher us) else none
    | _ => none
  unless live.type == normalized do
    throwError (s!"[h1f-spec-lock] DRIFT: the statement of LeanNative.Proofs.lowerRealLCNFDecl_sound no longer "
      ++ "structurally equals the frozen copy in lean/LeanNative/SpecLocked.lean (modulo the documented matcher "
      ++ "renaming). The H1 statement is frozen (roadmap/HORIZONS.md H1.F, roadmap/VALIDATION_CONTRACTS.md "
      ++ "Contract V1): revert the statement change, or re-freeze deliberately by updating the frozen copy AND "
      ++ "pinnedH1StatementHash in the same reviewed change.")
  let actual := live.type.hash
  unless actual == pinnedH1StatementHash do
    throwError (s!"[h1f-spec-lock] HASH PIN: Expr.hash of lowerRealLCNFDecl_sound's type is {actual}, "
      ++ s!"but pinnedH1StatementHash is {pinnedH1StatementHash}. The H1 statement is frozen (roadmap/HORIZONS.md "
      ++ "H1.F): revert the statement change, or re-freeze deliberately by updating the frozen copy and the pin "
      ++ "in lean/LeanNative/SpecLocked.lean in the same reviewed change.")
  IO.println s!"[h1f-spec-lock] OK: H1 statement frozen (structurally equal to the live theorem modulo matcher naming) and hash-pinned ({actual})"

end LeanNative.SpecLocked
