import TurboLean.ConLeche
import TurboLean.ElabAudit

/-
  LeanNative.Proofs.KernelElabProofs:
  Re-exports the Milestone M2 (`ConLeche`) and Milestone M3 (`TurboLean.ElabAudit`)
  soundness theorems into `LeanNative.Proofs` for `AxiomAudit.lean`.
-/

namespace LeanNative.Proofs

theorem conLeche_verify_decl_sound_bridge (env : ConLeche.Env) (d : ConLeche.Decl)
    (h_ver : ConLeche.verifyDecl env d = true) :
    ConLeche.CICValid env d :=
  ConLeche.con_leche_verify_decl_sound env d h_ver

theorem olean_mmap_bridge_sound_bridge (bytes : ByteArray) (env : ConLeche.Env)
    (h_parse : ConLeche.parseOleanShard bytes = .ok env) :
    bytes.size ≥ 5 ∧
    env.headerMagic = 0x4F4C454E ∧
    ConLeche.verifyDeclsPrefix [] env.decls = true ∧
    (∀ d ∈ env.decls, ConLeche.CICValid env d) ∧
    (∀ r ∈ env.recRules, ConLeche.RecRuleWF env r) :=
  ConLeche.olean_mmap_bridge_sound bytes env h_parse

theorem header_pin_prevents_statement_spoofing_bridge (spec : TurboLean.ElabAudit.PinnedHeaderSpec)
    (elaboratedTy : ConLeche.Expr)
    (h_pin : TurboLean.ElabAudit.verifyHeaderPin spec elaboratedTy = true) :
    elaboratedTy = spec.pinnedTypeAst ∧
    TurboLean.ElabAudit.checkNoShadowedConsts spec.globalConsts spec.boundNames elaboratedTy = true ∧
    TurboLean.ElabAudit.renderExplicitAST elaboratedTy = TurboLean.ElabAudit.renderExplicitAST spec.pinnedTypeAst :=
  TurboLean.ElabAudit.header_pin_prevents_statement_spoofing spec elaboratedTy h_pin

theorem cas_proof_replay_sound_bridge (env : ConLeche.Env) (blob : List UInt8)
    (expectedTy prf : ConLeche.Expr)
    (h_replay : TurboLean.ElabAudit.replayCASProofBlob env blob expectedTy = some prf) :
    TurboLean.ElabAudit.parseExprV1 blob = some prf ∧
    ConLeche.HasType env [] prf expectedTy :=
  TurboLean.ElabAudit.cas_proof_replay_sound env blob expectedTy prf h_replay

end LeanNative.Proofs
