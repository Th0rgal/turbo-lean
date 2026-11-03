import LeanNative.Proofs.MetalLowerProofs

/-!
# Top-Level `LNIRDecl` -> `MetalAst` Lowering Soundness (`LeanNative.Proofs.MetalDeclProofs`)

Connects `MetalLower.lowerDeclToMetal` directly to `Semantics.evalCode` on top-level `LNIRDecl`s
(both `parFor ... ret` and `let len = sarrayLen arr; parFor ... ret`), discharging `.dotProduct`
reductions by `wfMetalKernel` and establishing multi-threadgroup `evalMSLKernel` equivalence
plus a concrete `evalCode` non-vacuity witness (`0 sorryAx`, `0 ofReduceBool`).
-/

namespace LeanNative.Proofs.MetalDeclProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend
open LeanNative.Backend.MetalAst
open LeanNative.Backend.MetalLower
open LeanNative.Proofs.MetalLowerSpec
open LeanNative.Proofs.MetalLowerProofs

/-- Effective `VarEnv` after evaluating the optional `let lenVar = sarrayLen arrVar` prologue
extracted by `MetalLower.extractDeclParFor`. -/
def declRunEnv (env : VarEnv) (st : HeapState) : Option VarId → VarId → Option VarEnv
  | none, _ => some env
  | some arrVar, lenVar =>
    match env arrVar with
    | some (.sarrayId bid) =>
      match st.findBuffer bid with
      | some buf => some (env.bind lenVar (.u64 buf.data.size.toUInt64))
      | none => none
    | _ => none

private theorem evalVarList_of_packInputDeviceBuffersGo (env : VarEnv) (st : HeapState) (len : Nat) :
    ∀ (inputs : List VarId) (idx : Nat) (bufs : List (Nat × ByteMemory)),
      packInputDeviceBuffersGo env st len idx inputs = some bufs →
      ∃ vals, evalVarList env inputs = .ok vals
  | [], _, _, _ => ⟨[], rfl⟩
  | v :: rest, idx, bufs, h => by
    rw [packInputDeviceBuffersGo_cons] at h
    cases hp : packOneDeviceBuffer env st len v with
    | none => simp [hp] at h
    | some m =>
      rw [hp] at h; dsimp only at h
      cases ht : packInputDeviceBuffersGo env st len (idx + 1) rest with
      | none => simp [ht] at h
      | some tail =>
        unfold packOneDeviceBuffer at hp
        cases hv : env v with
        | none => simp [hv] at hp
        | some val =>
          have hexists : (∃ bid, val = .sarrayId bid) ∨ (∃ bid, val = .rawPtrId bid) := by
            cases val <;> simp only [hv] at hp <;> try cases hp
            · left; exact ⟨_, rfl⟩
            · right; exact ⟨_, rfl⟩
          rcases hexists with ⟨_, _⟩ | ⟨_, _⟩ <;> {
            rcases evalVarList_of_packInputDeviceBuffersGo env st len rest (idx + 1) tail ht with ⟨vs, hvs⟩
            exact ⟨val :: vs, by simp [evalVarList, hv, hvs]⟩
          }

private def outDataOfKind (k : ParallelKernelKind) (elems : List UInt64) : Array UInt64 :=
  match k with
  | .dotProduct => #[elems.foldl (· + ·) 0]
  | _ => elems.toArray

private theorem not_dotProduct_of_wf {k : ParallelKernelKind} (elems : List UInt64)
    (hwf : wfMetalKernel k = true) :
    outDataOfKind k elems = elems.toArray := by
  cases k <;> first | rfl | (simp [wfMetalKernel] at hwf)

private theorem extractDeclParFor_sound {code : LNIRCode}
    {arrOpt : Option VarId} {lenVar : VarId} {inputs : List VarId} {k : ParallelKernelKind}
    (hex : extractDeclParFor code = some (arrOpt, lenVar, inputs, k))
    (hwf : wfMetalKernel k = true)
    (fuel : Nat) (env env' : VarEnv) (st : HeapState) (n : UInt64)
    (henv' : declRunEnv env st arrOpt lenVar = some env')
    (hlen : env' lenVar = some (.u64 n))
    (hfuel : n.toNat ≤ fuel)
    (inBufs : List (Nat × ByteMemory))
    (hpack : packInputDeviceBuffers env' st inputs n.toNat = some inBufs)
    (elems : List UInt64)
    (hloop : evalParKernelLoop env' st inputs n.toNat k (List.range n.toNat) = .ok elems) :
    ∃ (outId : Nat) (stOut : HeapState) (outBuf : ArrayBuffer),
      evalCode fuel env st code = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data = elems.toArray := by
  have hnotFuel : ¬ (n.toNat > fuel) := by omega
  rcases evalVarList_of_packInputDeviceBuffersGo env' st n.toNat inputs 0 inBufs hpack with ⟨vals, hvals⟩
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

/-- Top-level `LNIRDecl` -> `MSLModule` soundness (`lowerToMetal_sound`):
whenever `lowerDeclToMetal d = some mslMod`, evaluating `d.body` under `Semantics.evalCode`
produces an output `sarray` buffer `outBuf` and executing the emitted `MSLKernelDecl` under
`MetalAst.evalMSLKernel` terminates race-free with every 64-bit output word matching `outBuf.data[i]`. -/
theorem lowerToMetal_sound
    (d : LNIRDecl) (mslMod : MSLModule)
    (arrOpt : Option VarId) (lenVar : VarId) (inputs : List VarId) (k : ParallelKernelKind)
    (fuel : Nat) (env env' : VarEnv) (st : HeapState) (n : UInt64)
    (nGroups groupSize : Nat) (inBufs : List (Nat × ByteMemory))
    (hlowDecl : lowerDeclToMetal d = some mslMod)
    (hex : extractDeclParFor d.body = some (arrOpt, lenVar, inputs, k))
    (henv' : declRunEnv env st arrOpt lenVar = some env')
    (hlen : env' lenVar = some (.u64 n))
    (hfuel : n.toNat ≤ fuel)
    (hpack : packInputDeviceBuffers env' st inputs n.toNat = some inBufs)
    (hlenCov : n.toNat ≤ nGroups * groupSize)
    (hgrid32 : nGroups * groupSize < 2 ^ 32) :
    ∃ (outId : Nat) (stOut : HeapState) (outBuf : ArrayBuffer)
      (kern : MSLKernelDecl) (devBufsF : List (Nat × ByteMemory)) (outMemF : ByteMemory),
      mslMod.kernels = [kern] ∧
      evalCode fuel env st d.body = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data.size = n.toNat ∧
      evalMSLKernel (groupStepsForKind groupSize k) kern
        { x := nGroups, y := 1, z := 1 } { x := groupSize, y := 1, z := 1 }
        (mkDeviceBuffers inBufs (kernelArity k) n.toNat)
        (mkConstLenBuffers (kernelArity k) n.toNat) [] [] = .ok devBufsF ∧
      devBufsF.lookup (kernelArity k) = some outMemF ∧
      (∀ (i : Nat) (hi : i < outBuf.data.size),
        outMemF.readU64Word? i = some (outBuf.data[i]'hi).toBitVec) := by
  unfold lowerDeclToMetal at hlowDecl
  rw [hex] at hlowDecl
  cases hret : isSarrayI64 d.retTy with
  | false => rw [hret] at hlowDecl; cases hlowDecl
  | true =>
    rw [hret] at hlowDecl
    simp only [ite_true] at hlowDecl
    cases hcond : (wfMetalKernel k && inputs.length == kernelArity k) with
    | false => rw [hcond] at hlowDecl; cases hlowDecl
    | true =>
      rw [hcond] at hlowDecl
      simp only [ite_true, Option.some.injEq] at hlowDecl
      subst hlowDecl
      rcases Bool.and_eq_true_iff.mp hcond with ⟨hwf, harityBool⟩
      have harity : inputs.length = kernelArity k := beq_iff_eq.mp harityBool
      rcases lowerToMetal_evalMSLKernel_sound env' st inputs s!"lean_native_metal_decl_{d.name}" k
          n.toNat nGroups groupSize inBufs hwf harity hpack hlenCov hgrid32 with
        ⟨elems, kern, devBufsF, outMemF, hkerns, hloop, helen, hmsl, hlkOut, hwords⟩
      rcases extractDeclParFor_sound hex hwf fuel env env' st n henv' hlen hfuel inBufs hpack elems hloop with
        ⟨outId, stOut, outBuf, hevalCode, hfindOut, houtData⟩
      refine ⟨outId, stOut, outBuf, kern, devBufsF, outMemF, hkerns, hevalCode, hfindOut, ?_, hmsl, hlkOut, ?_⟩
      · simp [houtData, helen]
      · intro i hi
        have hiList : i < elems.length := by simpa [houtData] using hi
        have hw := hwords i hiList
        have hget : outBuf.data[i]'hi = elems[i]'hiList := by simp [houtData]
        rw [hget]
        exact hw

/-- Concrete `evalCode` non-vacuity witness for `lowerToMetal_sound` on a multi-threadgroup
(`nGroups = 2`, `groupSize = 2`, `len = 3`) `let n = sarrayLen x; parFor out = mapScaleAdd 3 7 [x]; ret out`
declaration. -/
theorem lowerToMetal_decl_nonvacuous :
    ∃ (d : LNIRDecl) (mslMod : MSLModule) (env : VarEnv) (st stOut : HeapState)
      (outId : Nat) (outBuf : ArrayBuffer)
      (inBufs devBufsF : List (Nat × ByteMemory)) (kern : MSLKernelDecl) (outMemF : ByteMemory),
      lowerDeclToMetal d = some mslMod ∧
      mslMod.kernels = [kern] ∧
      evalCode 8 env st d.body = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data = #[37, 67, 97] ∧
      evalMSLKernel (groupStepsForKind 2 (.mapScaleAdd 3 7)) kern
        { x := 2, y := 1, z := 1 } { x := 2, y := 1, z := 1 }
        (mkDeviceBuffers inBufs 1 3) (mkConstLenBuffers 1 3) [] [] = .ok devBufsF ∧
      devBufsF.lookup 1 = some outMemF ∧
      outMemF.readU64Word? 0 = some 37#64 ∧
      outMemF.readU64Word? 1 = some 67#64 ∧
      outMemF.readU64Word? 2 = some 97#64 := by
  let d : LNIRDecl :=
    { name := "msa_decl"
      params := [{ id := 0, name := "x", ty := .sarray .i64 }]
      retTy := .sarray .i64
      body := .letBind 1 .i64 (.sarrayLen 0) (.parFor 2 1 [0] .i64 (.mapScaleAdd 3 7) (.ret 2)) }
  let env : VarEnv := VarEnv.empty.bind 0 (.sarrayId 1)
  let st : HeapState :=
    { buffers := [{ id := 1, exclusive := true, data := #[10, 20, 30] }], nextId := 1 }
  let mslMod := lowerToMetal "lean_native_metal_decl_msa_decl" (.mapScaleAdd 3 7)
  let env' := env.bind 1 (.u64 3)
  have hlow : lowerDeclToMetal d = some mslMod := by
    simp [lowerDeclToMetal, isSarrayI64, d, mslMod, extractDeclParFor, wfMetalKernel, kernelArity]
    rfl
  have hex : extractDeclParFor d.body = some (some 0, 1, [0], .mapScaleAdd 3 7) := rfl
  have henv' : declRunEnv env st (some 0) 1 = some env' := rfl
  have hlen : env' 1 = some (.u64 3) := rfl
  cases hpack : packInputDeviceBuffers env' st [0] 3 with
  | none =>
    exfalso; revert hpack
    simp [packInputDeviceBuffers, packInputDeviceBuffersGo, packOneDeviceBuffer,
      env', env, st, VarEnv.bind, HeapState.findBuffer]
  | some inBufs =>
    rcases lowerToMetal_sound d mslMod (some 0) 1 [0] (.mapScaleAdd 3 7) 8 env env' st 3 2 2 inBufs
        hlow hex henv' hlen (by decide) hpack (by decide) (by decide) with
      ⟨outId, stOut, outBuf, kern, devBufsF, outMemF, hkerns, heval, hfind, _, hmsl, hlkOut, hwords⟩
    have hdata : outBuf.data = #[37, 67, 97] := by
      have hevExplicit : evalCode 8 env st d.body =
          .ok (.sarrayId 2, { st with
            buffers := { id := 2, exclusive := true, data := #[37, 67, 97] } :: st.buffers
            nextId := 2 }) := by
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
    exact ⟨d, mslMod, env, st, stOut, outId, outBuf, inBufs, devBufsF, kern, outMemF,
      hlow, hkerns, heval, hfind, hdata, hmsl, hlkOut, hw0, hw1, hw2⟩

end LeanNative.Proofs.MetalDeclProofs
