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
    ConLeche.decodeOleanDecls (bytes.get! 4).toNat bytes 5 = some (env.decls, bytes.size) ∧
    ConLeche.verifyDeclsPrefix [] env.decls = true ∧
    (∀ d ∈ env.decls, ConLeche.CICValid env d) :=
  ConLeche.olean_mmap_bridge_sound bytes env h_parse

theorem kernel_conLeche_olean_mmap_bridge_sound_bridge (bytes : ByteArray) (env : ConLeche.Env)
    (h_parse : TurboLean.Kernel.ConLeche.parseOleanShard bytes = .ok env) :
    TurboLean.Kernel.ConLeche.EnvWellFormed env :=
  TurboLean.Kernel.ConLeche.olean_mmap_bridge_sound bytes env h_parse

theorem kernel_conLeche_verify_decl_sound_bridge (env env' : ConLeche.Env) (d : ConLeche.Decl)
    (h_wf : TurboLean.Kernel.ConLeche.EnvWellFormed env)
    (h_ok : TurboLean.Kernel.ConLeche.checkDecl env d = .ok env') :
    TurboLean.Kernel.ConLeche.EnvWellFormed env' ∧ TurboLean.Kernel.ConLeche.CICValid env d :=
  TurboLean.Kernel.ConLeche.con_leche_verify_decl_sound env env' d h_wf h_ok

theorem header_pin_prevents_statement_spoofing_bridge (surf : TurboLean.ElabAudit.SurfaceSig)
    (kType : ConLeche.Expr)
    (h_pin : TurboLean.ElabAudit.verifyHeaderPin surf kType = true) :
    TurboLean.ElabAudit.eraseAnnotations (TurboLean.ElabAudit.reparseExplicit (TurboLean.ElabAudit.ppExplicit kType)) =
      TurboLean.ElabAudit.eraseAnnotations surf ∧
    TurboLean.ElabAudit.shadowedBindersCount surf = 0 :=
  TurboLean.ElabAudit.header_pin_prevents_statement_spoofing surf kType h_pin

theorem cas_proof_replay_sound_bridge (env : ConLeche.Env) (expectedType : ConLeche.Expr)
    (blob : ByteArray)
    (h_replay : TurboLean.ElabAudit.verifyCasProofBlob env expectedType blob = true) :
    ∃ (proofTerm : ConLeche.Expr), TurboLean.ElabAudit.decodeExprBlob blob = .ok proofTerm ∧
      ConLeche.HasType env [] proofTerm expectedType :=
  TurboLean.ElabAudit.cas_proof_replay_sound env expectedType blob h_replay

end LeanNative.Proofs
