import LeanNative.Proofs.PTXLowerProofs

/-!
# Top-Level `LNIRDecl` -> `PTXAst` Lowering Soundness (`LeanNative.Proofs.PTXDeclProofs`)

Connects `PTXLower.lowerDeclToPTX` directly to `Semantics.evalCode` on top-level `LNIRDecl`s
(both `parFor ... ret` and `let len = sarrayLen arr; parFor ... ret`), discharging `.dotProduct`
reductions by `wfPTXKernel` and establishing genuine multi-CTA `evalPTXKernel` equivalence
plus a concrete `evalCode` non-vacuity witness (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.PTXDeclProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.PTXAst
open LeanNative.Backend.PTXLower
open LeanNative.Proofs.PTXScalarProofs
open LeanNative.Proofs.PTXLowerProofs

/-- Effective `VarEnv` after evaluating the optional `let lenVar = sarrayLen arrVar` prologue
extracted by `PTXLower.extractDeclParFor`. -/
def declRunEnv (env : VarEnv) (st : HeapState) : Option VarId → VarId → Option VarEnv
  | none, _ => some env
  | some arrVar, lenVar =>
    match env arrVar with
    | some (.sarrayId bid) =>
      match st.findBuffer bid with
      | some buf => some (env.bind lenVar (.u64 buf.data.size.toUInt64))
      | none => none
    | _ => none

private theorem evalVarList_of_packInputWordLists (env : VarEnv) (st : HeapState) (len : Nat) :
    ∀ (inputs : List VarId) (ws : List (List (BitVec 64))),
      packInputWordLists env st len inputs = some ws →
      ∃ vals, evalVarList env inputs = .ok vals
  | [], _, _ => ⟨[], rfl⟩
  | v :: rest, ws, h => by
    rw [packInputWordLists_cons] at h
    cases hp : packOneWordList env st len v with
    | none => simp [hp] at h
    | some w =>
      rw [hp] at h; dsimp only at h
      cases ht : packInputWordLists env st len rest with
      | none => simp [ht] at h
      | some tail =>
        unfold packOneWordList at hp
        cases hv : env v with
        | none => simp [hv] at hp
        | some val =>
          have hexists : (∃ bid, val = .sarrayId bid) ∨ (∃ bid, val = .rawPtrId bid) := by
            cases val <;> simp only [hv] at hp <;> try cases hp
            · left; exact ⟨_, rfl⟩
            · right; exact ⟨_, rfl⟩
          rcases hexists with ⟨_, _⟩ | ⟨_, _⟩ <;> {
            rcases evalVarList_of_packInputWordLists env st len rest tail ht with ⟨vs, hvs⟩
            exact ⟨val :: vs, by simp [evalVarList, hv, hvs]⟩
          }

private def outDataOfKind (k : ParallelKernelKind) (elems : List UInt64) : Array UInt64 :=
  match k with
  | .dotProduct => #[elems.foldl (· + ·) 0]
  | _ => elems.toArray

private theorem not_dotProduct_of_wf {k : ParallelKernelKind} (elems : List UInt64)
    (hwf : wfPTXKernel k = true) :
    outDataOfKind k elems = elems.toArray := by
  cases k <;> first | rfl | (simp [wfPTXKernel] at hwf)

private theorem extractDeclParFor_sound {code : LNIRCode}
    {arrOpt : Option VarId} {lenVar : VarId} {inputs : List VarId} {k : ParallelKernelKind}
    (hex : extractDeclParFor code = some (arrOpt, lenVar, inputs, k))
    (hwf : wfPTXKernel k = true)
    (fuel : Nat) (env env' : VarEnv) (st : HeapState) (n : UInt64)
    (henv' : declRunEnv env st arrOpt lenVar = some env')
    (hlen : env' lenVar = some (.u64 n))
    (hfuel : n.toNat ≤ fuel)
    (ws : List (List (BitVec 64)))
    (hpack : packInputWordLists env' st n.toNat inputs = some ws)
    (elems : List UInt64)
    (hloop : evalParKernelLoop env' st inputs n.toNat k (List.range n.toNat) = .ok elems) :
    ∃ (outId : Nat) (stOut : HeapState) (outBuf : ArrayBuffer),
      evalCode fuel env st code = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data = elems.toArray := by
  have hnotFuel : ¬ (n.toNat > fuel) := by omega
  rcases evalVarList_of_packInputWordLists env' st n.toNat inputs ws hpack with ⟨vals, hvals⟩
  have houtData : outDataOfKind k elems = elems.toArray := not_dotProduct_of_wf elems hwf
  cases code with
  | parFor outVar lv ins elemTy kern cont =>
    cases elemTy <;> try (unfold extractDeclParFor at hex; cases hex)
    cases cont <;> try (unfold extractDeclParFor at hex; cases hex)
    rename_i retVar
    simp only [extractDeclParFor] at hex
    split at hex <;> simp at hex
    rename_i houtEq
    rcases hex with ⟨rfl, rfl, rfl, rfl⟩
    simp only [declRunEnv, Option.some.injEq] at henv'
    subst henv'
    have heqOut : retVar = outVar := (beq_iff_eq.mp houtEq).symm
    subst heqOut
    refine ⟨st.nextId + 1, { st with
        buffers := { id := st.nextId + 1, exclusive := true, data := elems.toArray } :: st.buffers
        nextId := st.nextId + 1 },
      { id := st.nextId + 1, exclusive := true, data := elems.toArray }, ?_, ?_, rfl⟩
    · simp only [evalCode, evalParFor, hlen, hnotFuel, ite_false, hvals, hloop]
      simp only [VarEnv.bind, beq_self_eq_true, ite_true]
      change Except.ok (Val.sarrayId (st.nextId + 1),
        { st with
          buffers := { id := st.nextId + 1, exclusive := true, data := outDataOfKind kern elems } :: st.buffers
          nextId := st.nextId + 1 }) = _
      rw [houtData]
    · simp [HeapState.findBuffer]
  | letBind lv ty valExpr body =>
    cases ty <;> try (unfold extractDeclParFor at hex; cases hex)
    cases valExpr <;> try (unfold extractDeclParFor at hex; cases hex)
    cases body <;> try (unfold extractDeclParFor at hex; cases hex)
    rename_i arrVar outVar lv' ins elemTy kern cont
    cases elemTy <;> try (unfold extractDeclParFor at hex; cases hex)
    cases cont <;> try (unfold extractDeclParFor at hex; cases hex)
    rename_i retVar
    simp only [extractDeclParFor] at hex
    split at hex <;> simp at hex
    rename_i hcond
    rcases Bool.and_eq_true_iff.mp hcond with ⟨hlvEq, houtEq⟩
    rcases hex with ⟨rfl, rfl, rfl, rfl⟩
    have hlv : lv' = lv := (beq_iff_eq.mp hlvEq).symm
    have hout : retVar = outVar := (beq_iff_eq.mp houtEq).symm
    subst hlv; subst hout
    unfold declRunEnv at henv'
    cases harr : env arrVar with
    | none => simp [harr] at henv'
    | some aval =>
      cases aval <;> simp [harr] at henv'
      rename_i bid
      cases hbuf : st.findBuffer bid with
      | none => simp [hbuf] at henv'
      | some buf =>
        simp only [hbuf, Option.some.injEq] at henv'
        subst henv'
        refine ⟨st.nextId + 1, { st with
            buffers := { id := st.nextId + 1, exclusive := true, data := elems.toArray } :: st.buffers
            nextId := st.nextId + 1 },
          { id := st.nextId + 1, exclusive := true, data := elems.toArray }, ?_, ?_, rfl⟩
        · simp only [evalCode, evalExpr, harr, hbuf, evalParFor, hlen, hnotFuel, ite_false, hvals, hloop]
          simp only [VarEnv.bind, beq_self_eq_true, ite_true]
          change Except.ok (Val.sarrayId (st.nextId + 1),
            { st with
              buffers := { id := st.nextId + 1, exclusive := true, data := outDataOfKind kern elems } :: st.buffers
              nextId := st.nextId + 1 }) = _
          rw [houtData]
        · simp [HeapState.findBuffer]
  | _ => simp [extractDeclParFor] at hex

/-- Top-level `LNIRDecl` -> `PTXModule` soundness (`lowerToPTX_sound`):
whenever `lowerDeclToPTX d = some ptxMod`, evaluating `d.body` under `Semantics.evalCode`
produces an output `sarray` buffer `outBuf` and executing the emitted `PTXKernel` under
`PTXAst.evalPTXKernel` terminates race-free with every 64-bit output word matching `outBuf.data[i]`. -/
theorem lowerToPTX_sound
    (d : LNIRDecl) (ptxMod : PTXModule)
    (arrOpt : Option VarId) (lenVar : VarId) (inputs : List VarId) (k : ParallelKernelKind)
    (fuel : Nat) (env env' : VarEnv) (st : HeapState) (n : UInt64)
    (nBlocks blockSize : Nat) (inWords : List (List (BitVec 64)))
    (hlowDecl : lowerDeclToPTX d = some ptxMod)
    (hex : extractDeclParFor d.body = some (arrOpt, lenVar, inputs, k))
    (henv' : declRunEnv env st arrOpt lenVar = some env')
    (hlen : env' lenVar = some (.u64 n))
    (hfuel : n.toNat ≤ fuel)
    (hpack : packInputWordLists env' st n.toNat inputs = some inWords)
    (hlenCov : n.toNat ≤ nBlocks * blockSize)
    (hnBlk32 : nBlocks < 2 ^ 32) (hblk32 : blockSize < 2 ^ 32)
    (houn : (kernelArity k + 1) * n.toNat * 8 ≤ 2 ^ 64) :
    ∃ (outId : Nat) (stOut : HeapState) (outBuf : ArrayBuffer)
      (kern : PTXKernel) (gFinal : ByteMemory),
      ptxMod.kernels = [kern] ∧
      evalCode fuel env st d.body = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data.size = n.toNat ∧
      evalPTXKernel (ctaStepsForKind blockSize k) kern
        { x := nBlocks, y := 1, z := 1 } { x := blockSize, y := 1, z := 1 }
        (mkPTXGlobalMem inWords (kernelArity k) n.toNat)
        (mkPTXParamMem (kernelArity k) n.toNat) = .ok gFinal ∧
      (∀ (i : Nat) (hi : i < outBuf.data.size),
        gFinal.loadBits (kernelArity k * n.toNat * 8 + i * 8) 8 =
          some (outBuf.data[i]'hi).toBitVec) := by
  unfold lowerDeclToPTX at hlowDecl
  rw [hex] at hlowDecl
  cases hret : isSarrayI64 d.retTy with
  | false => rw [hret] at hlowDecl; cases hlowDecl
  | true =>
    rw [hret] at hlowDecl
    simp only [ite_true] at hlowDecl
    cases hcond : (wfPTXKernel k && inputs.length == kernelArity k) with
    | false => rw [hcond] at hlowDecl; cases hlowDecl
    | true =>
      rw [hcond] at hlowDecl
      simp only [ite_true, Option.some.injEq] at hlowDecl
      subst hlowDecl
      rcases Bool.and_eq_true_iff.mp hcond with ⟨hwf, harityBool⟩
      have harity : inputs.length = kernelArity k := beq_iff_eq.mp harityBool
      rcases lowerToPTX_evalPTXKernel_sound env' st inputs s!"lean_native_decl_{d.name}" k
          n.toNat nBlocks blockSize inWords hwf harity hpack hlenCov hnBlk32 hblk32 houn with
        ⟨elems, kern, gFinal, hkerns, hloop, helen, hptx, hwords⟩
      rcases extractDeclParFor_sound hex hwf fuel env env' st n henv' hlen hfuel inWords hpack elems hloop with
        ⟨outId, stOut, outBuf, hevalCode, hfindOut, houtData⟩
      refine ⟨outId, stOut, outBuf, kern, gFinal, hkerns, hevalCode, hfindOut, ?_, hptx, ?_⟩
      · simp [houtData, helen]
      · intro i hi
        have hiList : i < elems.length := by simpa [houtData] using hi
        have hw := hwords i hiList
        have hget : outBuf.data[i]'hi = elems[i]'hiList := by simp [houtData]
        rw [hget]
        exact hw

/-- Concrete `evalCode` non-vacuity witness for `lowerToPTX_sound` on a multi-CTA (`nBlocks = 2`,
`blockSize = 2`, `len = 3`) `let n = sarrayLen x; parFor out = saxpy 5 [x, y]; ret out` declaration. -/
theorem lowerToPTX_decl_nonvacuous :
    ∃ (d : LNIRDecl) (ptxMod : PTXModule) (env : VarEnv) (st stOut : HeapState)
      (outId : Nat) (outBuf : ArrayBuffer) (inWords : List (List (BitVec 64)))
      (kern : PTXKernel) (gFinal : ByteMemory),
      lowerDeclToPTX d = some ptxMod ∧
      ptxMod.kernels = [kern] ∧
      evalCode 8 env st d.body = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data = #[53, 107, 161] ∧
      evalPTXKernel (ctaStepsForKind 2 (.saxpy 5)) kern
        { x := 2, y := 1, z := 1 } { x := 2, y := 1, z := 1 }
        (mkPTXGlobalMem inWords 2 3) (mkPTXParamMem 2 3) = .ok gFinal ∧
      gFinal.loadBits (2 * 3 * 8 + 0 * 8) 8 = some 53#64 ∧
      gFinal.loadBits (2 * 3 * 8 + 1 * 8) 8 = some 107#64 ∧
      gFinal.loadBits (2 * 3 * 8 + 2 * 8) 8 = some 161#64 := by
  let d : LNIRDecl :=
    { name := "saxpy_decl"
      params := [{ id := 0, name := "x", ty := .sarray .i64 }, { id := 1, name := "y", ty := .sarray .i64 }]
      retTy := .sarray .i64
      body := .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 (.saxpy 5) (.ret 3)) }
  let env : VarEnv := (VarEnv.empty.bind 0 (.sarrayId 1)).bind 1 (.sarrayId 2)
  let st : HeapState :=
    { buffers :=
        [ { id := 1, exclusive := true, data := #[10, 20, 30] }
        , { id := 2, exclusive := true, data := #[3, 7, 11] } ]
      nextId := 2 }
  let ptxMod := lowerToPTX "lean_native_decl_saxpy_decl" (.saxpy 5)
  let env' := env.bind 2 (.u64 3)
  have hlow : lowerDeclToPTX d = some ptxMod := by
    simp [lowerDeclToPTX, isSarrayI64, d, ptxMod, extractDeclParFor, wfPTXKernel, kernelArity]
    rfl
  have hex : extractDeclParFor d.body = some (some 0, 2, [0, 1], .saxpy 5) := rfl
  have henv' : declRunEnv env st (some 0) 2 = some env' := rfl
  have hlen : env' 2 = some (.u64 3) := rfl
  cases hpack : packInputWordLists env' st 3 [0, 1] with
  | none =>
    exfalso; revert hpack
    simp [packInputWordLists, packOneWordList, env', env, st, VarEnv.bind, HeapState.findBuffer]
  | some inWords =>
    rcases lowerToPTX_sound d ptxMod (some 0) 2 [0, 1] (.saxpy 5) 8 env env' st 3 2 2 inWords
        hlow hex henv' hlen (by decide) hpack (by decide) (by decide) (by decide) (by decide) with
      ⟨outId, stOut, outBuf, kern, gFinal, hkerns, heval, hfind, hsize, hptx, hwords⟩
    have hdata : outBuf.data = #[53, 107, 161] := by
      have hevExplicit : evalCode 8 env st d.body =
          .ok (.sarrayId 3, { st with
            buffers := { id := 3, exclusive := true, data := #[53, 107, 161] } :: st.buffers
            nextId := 3 }) := by
        simp [d, env, st, evalCode, evalExpr, VarEnv.bind, HeapState.findBuffer,
          evalParFor, evalVarList, List.range, List.range.loop,
          evalParKernelLoop, evalParKernelElem, readParInput, HeapState.readElem]
      rw [hevExplicit] at heval
      rcases heval with ⟨rfl, rfl⟩
      simp [HeapState.findBuffer] at hfind
      exact congrArg ArrayBuffer.data hfind.symm
    have hw0 := hwords 0 (by rw [hdata]; decide)
    have hw1 := hwords 1 (by rw [hdata]; decide)
    have hw2 := hwords 2 (by rw [hdata]; decide)
    simp only [hdata] at hw0 hw1 hw2
    exact ⟨d, ptxMod, env, st, stOut, outId, outBuf, inWords, kern, gFinal,
      hlow, hkerns, heval, hfind, hdata, hptx, hw0, hw1, hw2⟩

end LeanNative.Proofs.PTXDeclProofs
