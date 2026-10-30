-- DRAFT — NOT A RESULT. Every theorem ends in `:= by sorry`.
-- research/B2-spec-draft.lean: plan B2 (LNIR → CLIF, then clifv's CLIF → AArch64 theorem).
-- Elaborated (statements type-check) as module `B2.Draft` of the package in research/b2-proofs/
-- (Lean v4.34.1, clifv eth-act/clifv@5018b950, LNIR = turbo-lean@4966384 vendored verbatim).
import FV.Clif.Run
import FV.Compile.Subset
import LeanNative.Semantics.Eval
import FV.E2E.Statement
import FV.E2E.RegLevelCall
import FV.E2E.RegLevelTry
import FV.E2E.RegLevelTls
import FV.E2E.RegLevelDriverSem
import FV.E2E.RegLevelSim
import FV.E2E.RegLevelMachine
import FV.Backend.Proof.LowerDecide

/-!
# DRAFT — B2 specification (statements only)

**CONJECTURE stage.** Nothing here is proved. No semantics are defined: LNIR is
`LeanNative.Semantics.evalCode` (turbo-lean 4966384), CLIF is `Clif.runLoop`, AArch64 is clifv's
`ArmStepX`/`runX`, and the target composition is `E2E.backend_correct_final_of_lower`
(clifv 5018b950, `FV/E2E/FinalDirect.lean:23`). The lowering `lowerDecl` does not exist (turbo-lean
has no CLIF emitter); it is a section `variable`.

Obligations: O1 subset E · O2 signature · O3 forward simulation · O4 no trap/stuck ·
O5 backend input scope · O6 callee/extern premises vacuous · O7 end-to-end.
-/

namespace B2

open LeanNative.IR LeanNative.Semantics

/-! ## Fragment F₆₄ (syntactic, decidable) -/

/-- Binary operators admitted in F₆₄. `div`/`mod` are admitted only under `DivGuarded`
(LNIR returns 0 on `x/0` and `x%0`; CLIF `udiv`/`urem` trap `int_divz`). The `*Checked256`,
`clmul*`, `gf2Affine`, `eor3` operators are out of scope. -/
def binOpF : BinOp → Bool
  | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .bitXor
  | .shl | .shr | .sar | .eq | .lt | .le => true
  | _ => false

def unOpF : UnaryOp → Bool
  | .not | .neg => true
  | .clz256 => false

def scalarF : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => true
  | .binOp op a b => binOpF op && scalarF a && scalarF b
  | .unaryOp op a => unOpF op && scalarF a
  | .select c t e => scalarF c && scalarF t && scalarF e
  | .fma a b c => scalarF a && scalarF b && scalarF c

def tyF : LNIRType → Bool
  | .i1 | .i64 => true
  | _ => false

/-- F₆₄ code: `letBind` of scalar expressions at `i1`/`i64`, `ite`, `seqFor`, `ret`. No heap,
no RC, no `parFor`, no calls, no 256-bit. -/
def codeF : LNIRCode → Bool
  | .letBind _ ty (.scalar e) k => tyF ty && scalarF e && codeF k
  | .ite _ t e => codeF t && codeF e
  | .seqFor _ _ _ _ _ ty body k => tyF ty && codeF body && codeF k
  | .ret _ => true
  | _ => false

def declF (d : LNIRDecl) : Bool :=
  d.params.all (fun p => tyF p.ty) && tyF d.retTy && codeF d.body

/-! ## Value correspondence (no new semantics: both sides are the repos' own `Val`s) -/

/-- LNIR `u64` ↔ CLIF `i64`, LNIR `bool` ↔ CLIF `i8` 0/1 (CLIF `icmp` result). -/
def ValRel : Val → Clif.Val → Prop
  | .u64 n, v => v = ⟨.i64, n.toBitVec⟩
  | .bool b, v => v = ⟨.i8, if b then 1#8 else 0#8⟩
  | _, _ => False

/-- Pointwise `ValRel` on argument lists (core has no `List.Forall₂`). -/
def ArgsRel (vs : List Val) (cvs : List Clif.Val) : Prop :=
  vs.length = cvs.length ∧ ∀ (i : Nat) v cv, vs[i]? = some v → cvs[i]? = some cv → ValRel v cv

def clifTy : LNIRType → Clif.Ty
  | .i1 => .i8
  | _ => .i64

/-- The LNIR entry state of `d` on argument values `vs`. -/
def entryEnv (d : LNIRDecl) (vs : List Val) : VarEnv :=
  (d.params.zip vs).foldl (fun env (p, v) => env.bind p.id v) VarEnv.empty

/-- Empty LNIR heap (F₆₄ never touches it). -/
def emptyHeap : HeapState := ⟨[], 0, [], []⟩

/-! ## Obligations on the (future) lowering -/

section
-- The B2 front end to be written: LNIR declaration → CLIF function.
variable (lowerDecl : LNIRDecl → Except String Clif.Function)

/-- (O1) Scope: every F₆₄ function lands in clifv's verified emitter subset E and the
decidable side conditions of `E2E.backend_correct_final_of_lower`. Statement kept in
`B2/SpecE2E.lean` (needs `FV.E2E.*`); here only subset E. -/
theorem lower_in_subsetE (d : LNIRDecl) (f : Clif.Function)
    (hd : declF d = true) (hl : lowerDecl d = .ok f) :
    Compile.functionE f = true := by
  sorry

/-- (O2) Signature: one `i64`/`i8` parameter per LNIR parameter, one return. -/
theorem lower_sig (d : LNIRDecl) (f : Clif.Function)
    (hd : declF d = true) (hl : lowerDecl d = .ok f) :
    f.sig.params.map (·.ty) = d.params.map (clifTy ·.ty) ∧
    f.sig.returns.map (·.ty) = [clifTy d.retTy] := by
  sorry

/-- (O3) **Forward simulation, LNIR → CLIF** (the B2 core lemma). If LNIR evaluates `d` to a
value, the CLIF function returns a related value. `DivGuarded` is the explicit side condition
for the div/mod-by-zero mismatch: the run never divides by zero (otherwise CLIF traps
`int_divz` where LNIR returns 0; the alternative is to lower `div` to
`select(y==0, 0, udiv x y')` — then this hypothesis disappears, see feasibility §Q4). -/
theorem lower_forward (DivGuarded : LNIRDecl → List Val → Prop)
    (d : LNIRDecl) (f : Clif.Function) (hd : declF d = true) (hl : lowerDecl d = .ok f)
    (vs : List Val) (cvs : List Clif.Val) (hargs : ArgsRel vs cvs)
    (hdiv : DivGuarded d vs)
    (fuel : Nat) (v : Val) (st : HeapState)
    (hev : evalCode fuel (entryEnv d vs) emptyHeap d.body = .ok (v, st))
    (env : Clif.Env) (p : Clif.Program) (hp : p.func? f.name = some f)
    (m0 : Clif.Mem) (cs : Clif.State)
    (hinit : Clif.initState p f.name cvs m0 = .ok cs) :
    ∃ n rv m, Clif.runLoop env p n cs = .returned [rv] m ∧ ValRel v rv := by
  sorry

/-- (O4) No spurious traps: on F₆₄ (with `DivGuarded`) the CLIF run of the lowered function
never traps and never gets stuck. Needed because `ArmRefines` says nothing on `stuck`. -/
theorem lower_no_trap (DivGuarded : LNIRDecl → List Val → Prop)
    (d : LNIRDecl) (f : Clif.Function) (hd : declF d = true) (hl : lowerDecl d = .ok f)
    (vs : List Val) (cvs : List Clif.Val) (hargs : ArgsRel vs cvs)
    (hdiv : DivGuarded d vs)
    (env : Clif.Env) (p : Clif.Program) (hp : p.func? f.name = some f)
    (m0 : Clif.Mem) (cs : Clif.State) (hinit : Clif.initState p f.name cvs m0 = .ok cs)
    (n : Nat) :
    (∀ c, Clif.runLoop env p n cs ≠ .trapped c) ∧
    (∀ msg, Clif.runLoop env p n cs ≠ .stuck msg) := by
  sorry

end

/-! ## Composition with clifv (O5–O7) -/


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
