import B2.SpecCore
-- Signature-only imports: every name in `backend_correct_final_of_lower`'s statement, without the
-- proof cone of `FV.E2E.Final`/`FinalDirect` (365 modules). O7 is stated against these.
import FV.E2E.Statement
import FV.E2E.RegLevelCall
import FV.E2E.RegLevelTry
import FV.E2E.RegLevelTls
import FV.E2E.RegLevelDriverSem
import FV.E2E.RegLevelSim
import FV.E2E.RegLevelMachine
import FV.Backend.Proof.LowerDecide

/-!
# DRAFT — B2 specification, composition with clifv's backend theorem (statements only)

**DRAFT / CONJECTURE stage**, `:= by sorry` throughout. The composed claim:
LNIR `evalCode` returns `v` ⇒ the AArch64 run of clifv's compiled code (same pipeline objects
`vc vcp rf af fa fb` that `E2E.backend_correct_final_of_lower` quantifies over) reaches the return
address with `x0` holding `v`. All Arm-side premises are *copied* from
`backend_correct_final_of_lower` (clifv 5018b950, `FV/E2E/FinalDirect.lean:23`); none are
discharged here. The external/callee premises (`hC hX hXI hTls hCT`) are expected to be
dischargeable for F₆₄ code (no calls, no TLS, no `try_call`): `hCT`/`hTls` are vacuous by
`isTry = false`/`hasTls = false`, `hXI` by `xCallsIndOk_nil` once `indSigs f = []`, `hX` once
`f.externs = []`; `hC` quantifies over `vcp.CallSite`, which is empty for call-free code but still
needs the `pc`/`ext` fields — that discharge is open obligation O6, stated below.
-/

namespace B2

open LeanNative.IR LeanNative.Semantics
open E2E Backend Backend.Proof Backend.Proof.Driver

section
variable (lowerDecl : LNIRDecl → Except String Clif.Function)

/-- (O5) Lowered F₆₄ code satisfies the decidable input conditions of
`backend_correct_final_of_lower` (`InSubset` with an empty program of internal callees,
`dominatedB`, `lowerScopeB`). Expected to be provable once per lowering, or checked per
function by `decide`/`native_decide` (the latter violates turbo-lean's `0 native_decide` gate). -/
theorem lower_backend_scope (d : LNIRDecl) (f : Clif.Function)
    (hd : declF d = true) (hl : lowerDecl d = .ok f) (p : Clif.Program)
    (hp : ∀ n, p.func? n = none) :
    InSubset p f ∧ dominatedB f = true ∧ lowerScopeB f = true := by
  sorry

/-- (O6) The callee/extern premises are dischargeable for lowered F₆₄ code: no externs, no
indirect signatures, no `try_call`, no TLS, no call sites in the compiled VCode. -/
theorem lower_no_calls (d : LNIRDecl) (f : Clif.Function)
    (hd : declF d = true) (hl : lowerDecl d = .ok f) {vc vcp : VCode}
    (hlf : lowerFunction f = .ok vc) (hpr : Backend.prepare vc = .ok vcp) :
    f.externs = [] ∧ indSigs f = [] ∧ hasTls f = false ∧
    (∀ B ∈ f.blocks, B.term.isTry = false) ∧ (∀ info, ¬ vcp.CallSite info) := by
  sorry

/-- (O7) **End-to-end B2 statement**: LNIR → CLIF → AArch64, for one F₆₄ declaration.
Premises `hC … hslot`, `hent … hrel` are verbatim from `backend_correct_final_of_lower`
(FinalDirect.lean:23–49). Its `hsub`, `hd`, `hs` come from O5; its `htr : TrapsExplicit` is
*not* a premise here — it must follow from O4 (no traps at all on F₆₄ ∧ `DivGuarded`). -/
theorem lnir_to_arm_correct (DivGuarded : LNIRDecl → List Val → Prop)
    (d : LNIRDecl) (f : Clif.Function) (hd : declF d = true) (hlow : lowerDecl d = .ok f)
    {p : Clif.Program} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin}
    (hl : lowerFunction f = .ok vc) (hpr : Backend.prepare vc = .ok vcp)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {cs : Clif.State}
    (vs : List Val) (cvs : List Clif.Val) (hargsR : ArgsRel vs cvs) (hdiv : DivGuarded d vs)
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig cvs s) (hcs : ClifEntry f cvs cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpf : ∀ n, p.func? n = none)
    (fuel : Nat) (v : Val) (st : HeapState)
    (hev : evalCode fuel (entryEnv d vs) emptyHeap d.body = .ok (v, st)) :
    ∃ n rv, ArmRet ra s (runX (ArmStepX X H fa) n s) ∧ ValRel v rv ∧
      XHolds rv (xreg 0 (runX (ArmStepX X H fa) n s)) := by
  sorry

end

end B2
