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

private theorem not_dotProduct_of_wf {k : ParallelKernelKind}
    (hwf : wfPTXKernel k = true) :
    k ≠ .dotProduct := by
  intro hEq
  subst hEq
  simp [wfPTXKernel] at hwf

private theorem extractDeclParFor_sound {code : LNIRCode}
    {arrOpt : Option VarId} {lenVar : VarId} {inputs : List VarId} {k : ParallelKernelKind}
    (hex : extractDeclParFor code = some (arrOpt, lenVar, inputs, k))
    (hwf : wfPTXKernel k = true)
    (fuel : Nat) (env env' : VarEnv) (st : HeapState) (n : UInt64)
    (henv' :
      (match (motive := Option VarId → Option VarEnv) arrOpt with
       | none => some env
       | some arrVar =>
         match env arrVar with
         | some (.sarrayId bid) =>
           match st.findBuffer bid with
           | some buf => some (env.bind lenVar (.u64 buf.data.size.toUInt64))
           | none => none
         | _ => none) = some env')
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
  have hNotDot : k ≠ .dotProduct := not_dotProduct_of_wf hwf
  cases code with
  | parFor outVar lv ins elemTy kern cont =>
    cases elemTy <;> try (unfold extractDeclParFor at hex; cases hex)
    cases cont <;> try (unfold extractDeclParFor at hex; cases hex)
    rename_i retVar
    simp only [extractDeclParFor] at hex
    split at hex <;> simp at hex
    rename_i houtEq
    rcases hex with ⟨rfl, rfl, rfl, rfl⟩
    simp only [Option.some.injEq] at henv'
    subst henv'
    have heqOut : retVar = outVar := (beq_iff_eq.mp houtEq).symm
    subst heqOut
    refine ⟨st.nextId + 1, { st with
        buffers := { id := st.nextId + 1, exclusive := true, data := elems.toArray } :: st.buffers
        nextId := st.nextId + 1 },
      { id := st.nextId + 1, exclusive := true, data := elems.toArray }, ?_, ?_, rfl⟩
    · cases kern with
      | dotProduct => exact False.elim (hNotDot rfl)
      | _ =>
        simp only [evalCode, evalParFor, hlen, hnotFuel, ite_false, hvals, hloop]
        simp only [VarEnv.bind, beq_self_eq_true, ite_true]
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
    dsimp only at henv'
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
        · cases kern with
          | dotProduct => exact False.elim (hNotDot rfl)
          | _ =>
            simp only [evalCode, evalExpr, harr, hbuf, evalParFor, hlen, hnotFuel, ite_false, hvals, hloop]
            simp only [VarEnv.bind, beq_self_eq_true, ite_true]
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
    (henv' :
      (match (motive := Option VarId → Option VarEnv) arrOpt with
       | none => some env
       | some arrVar =>
         match env arrVar with
         | some (.sarrayId bid) =>
           match st.findBuffer bid with
           | some buf => some (env.bind lenVar (.u64 buf.data.size.toUInt64))
           | none => none
         | _ => none) = some env')
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
  have henv' :
      (match (motive := Option VarId → Option VarEnv) some (0 : VarId) with
       | none => some env
       | some arrVar =>
         match env arrVar with
         | some (.sarrayId bid) =>
           match st.findBuffer bid with
           | some buf => some (env.bind (2 : VarId) (.u64 buf.data.size.toUInt64))
           | none => none
         | _ => none) = some env' := rfl
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

/-! ## Track `D6` — `.dotProduct` via `atom.add.global.u64` & sequential multi-kernel visibility -/

set_option maxRecDepth 65536

/-- Concrete LNIR `.dotProduct` reduction (`D6`):
    `evalParKernelElem` computes elementwise `x[i] * y[i]` (matching `evalParKernelElem` for
    `.zipMul`/`.dotProduct` at `Semantics/Eval.lean:465–469`) and `evalParFor` folds the sum into a
    length-1 `sarray` (`match k with | .dotProduct => ...` at `Semantics/Eval.lean:521`). The
    corresponding multi-CTA PTX kernel (`gridDim.x = 2`,
    `blockDim.x = 2`, `n = 3`) computes the same `UInt64` sum via cross-CTA `atom.add.global.u64` of
    `x[gid] * y[gid]`, with out-of-range thread `(ctaid.x = 1, tid.x = 1, gid = 3 >= n)` taking an
    early predicated `ret` before `bar.sync 0` while active threads synchronize on `bar.sync 0`,
    yielding `0` UB/race traps and final `.global` accumulator word `10*2 + 20*3 + 30*5 = 230`. -/
theorem ptx_dotProduct_atom_add_matches_lnir_fold :
    let d : LNIRDecl :=
      { name := "dot_decl"
      , params :=
          [ { id := 0, name := "x", ty := .sarray .i64 }
          , { id := 1, name := "y", ty := .sarray .i64 } ]
      , retTy := .sarray .i64
      , body := .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 .dotProduct (.ret 3)) }
    let env : VarEnv := (VarEnv.empty.bind 0 (.sarrayId 1)).bind 1 (.sarrayId 2)
    let st : HeapState :=
      { buffers :=
          [ { id := 1, exclusive := true, data := #[10, 20, 30] }
          , { id := 2, exclusive := true, data := #[2, 3, 5] } ]
      , nextId := 2 }
    let k : PTXKernel :=
      { name := "ptx_dot_product_atom"
      , params :=
          [ { ty := .u64, name := "x" }
          , { ty := .u64, name := "y" }
          , { ty := .u64, name := "acc" }
          , { ty := .u64, name := "n" } ]
      , regDecls :=
          [ { ty := .u32, prefixName := "%r", count := 3 }
          , { ty := .u64, prefixName := "%rd", count := 10 }
          , { ty := .pred, prefixName := "%p", count := 1 } ]
      , body :=
          [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
          , .instr none (.mov .u32 "%r1" (.sreg .ntidX))
          , .instr none (.mov .u32 "%r2" (.sreg .tidX))
          , .instr none (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
          , .instr none (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
          , .instr none (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
          , .instr none (.ldParam .u64 "%rd3" "n")
          , .instr none (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
          , .instr (some { predReg := "%p0" }) .ret
          , .instr none (.barSync 0)
          , .instr none (.shl .b64 "%rd4" (.reg "%rd2") (.immU64 3#64))
          , .instr none (.ldParam .u64 "%rd5" "x")
          , .instr none (.add .none .u64 "%rd5" (.reg "%rd5") (.reg "%rd4"))
          , .instr none (.ldGlobal .u64 "%rd5" (.regOffset "%rd5" 0))
          , .instr none (.ldParam .u64 "%rd6" "y")
          , .instr none (.add .none .u64 "%rd6" (.reg "%rd6") (.reg "%rd4"))
          , .instr none (.ldGlobal .u64 "%rd6" (.regOffset "%rd6" 0))
          , .instr none (.mul .lo .u64 "%rd7" (.reg "%rd5") (.reg "%rd6"))
          , .instr none (.ldParam .u64 "%rd8" "acc")
          , .instr none (.atomAdd .global .u64 "%rd9" (.regOffset "%rd8" 0) (.reg "%rd7"))
          , .instr none .ret ] }
    let g0 := ByteMemory.ofU64Words [ 10#64, 20#64, 30#64, 2#64, 3#64, 5#64, 0#64 ]
    let pm : ParamMemory := { params := [ ("x", 0#64), ("y", 24#64), ("acc", 48#64), ("n", 3#64) ] }
    (∃ (outId : Nat) (stOut : HeapState) (outBuf : ArrayBuffer),
      evalCode 8 env st d.body = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data = #[230]) ∧
    (∃ gFinal evs,
      evalPTXKernelWithOracle none 128 k { x := 2 } { x := 2 } g0 pm = .ok (gFinal, evs) ∧
      gFinal.loadBits 48 8 = some (230 : UInt64).toBitVec ∧
      sumAtomAddDeltas (evs.filter (fun e => e.isAtomic)) = 230#64 ∧
      (evs.filter (fun e => e.isAtomic)).length = 3) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · refine ⟨3,
      { buffers :=
          [ { id := 3, exclusive := true, data := #[230] }
          , { id := 1, exclusive := true, data := #[10, 20, 30] }
          , { id := 2, exclusive := true, data := #[2, 3, 5] } ]
        nextId := 3 },
      { id := 3, exclusive := true, data := #[230] }, ?_, ?_, rfl⟩
    · simp [evalCode, evalExpr, VarEnv.bind, HeapState.findBuffer,
        evalParFor, evalVarList, List.range, List.range.loop,
        evalParKernelLoop, evalParKernelElem, readParInput, HeapState.readElem]
    · simp [HeapState.findBuffer]
  · have hchk :
        (match evalPTXKernelWithOracle none 128
            { name := "ptx_dot_product_atom"
            , params :=
                [ { ty := .u64, name := "x" }
                , { ty := .u64, name := "y" }
                , { ty := .u64, name := "acc" }
                , { ty := .u64, name := "n" } ]
            , regDecls :=
                [ { ty := .u32, prefixName := "%r", count := 3 }
                , { ty := .u64, prefixName := "%rd", count := 10 }
                , { ty := .pred, prefixName := "%p", count := 1 } ]
            , body :=
                [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
                , .instr none (.mov .u32 "%r1" (.sreg .ntidX))
                , .instr none (.mov .u32 "%r2" (.sreg .tidX))
                , .instr none (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
                , .instr none (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
                , .instr none (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
                , .instr none (.ldParam .u64 "%rd3" "n")
                , .instr none (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
                , .instr (some { predReg := "%p0" }) .ret
                , .instr none (.barSync 0)
                , .instr none (.shl .b64 "%rd4" (.reg "%rd2") (.immU64 3#64))
                , .instr none (.ldParam .u64 "%rd5" "x")
                , .instr none (.add .none .u64 "%rd5" (.reg "%rd5") (.reg "%rd4"))
                , .instr none (.ldGlobal .u64 "%rd5" (.regOffset "%rd5" 0))
                , .instr none (.ldParam .u64 "%rd6" "y")
                , .instr none (.add .none .u64 "%rd6" (.reg "%rd6") (.reg "%rd4"))
                , .instr none (.ldGlobal .u64 "%rd6" (.regOffset "%rd6" 0))
                , .instr none (.mul .lo .u64 "%rd7" (.reg "%rd5") (.reg "%rd6"))
                , .instr none (.ldParam .u64 "%rd8" "acc")
                , .instr none (.atomAdd .global .u64 "%rd9" (.regOffset "%rd8" 0) (.reg "%rd7"))
                , .instr none .ret ] }
            { x := 2 } { x := 2 }
            (ByteMemory.ofU64Words [ 10#64, 20#64, 30#64, 2#64, 3#64, 5#64, 0#64 ])
            { params := [ ("x", 0#64), ("y", 24#64), ("acc", 48#64), ("n", 3#64) ] } with
         | .ok (gFinal, evs) =>
           gFinal.loadBits 48 8 == some (230 : UInt64).toBitVec &&
           sumAtomAddDeltas (evs.filter (fun e => e.isAtomic)) == 230#64 &&
           (evs.filter (fun e => e.isAtomic)).length == 3
         | _ => false) = true := rfl
    revert hchk
    generalize evalPTXKernelWithOracle none 128 _ { x := 2 } { x := 2 } _ _ = runRes
    intro hchk
    cases runRes <;> try contradiction
    rename_i res
    rcases res with ⟨gFinal, evs⟩
    dsimp only at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨h12, h3⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
    exact ⟨gFinal, evs, rfl, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3⟩

/-- Sequential multi-kernel host stream (`D6`):
    `k_0` (`lowerKind "lean_native_decl_dot_mul" .zipMul`, multi-CTA `gridDim.x = 2, blockDim.x = 2`)
    performs elementwise `zipMul` (`x[i] * y[i]`) into `.global` scratch words `[20, 60, 150]`, and
    `k_1` performs a multi-CTA `atom.add.global.u64` reduction (with early `ret` + `bar.sync 0` on
    the out-of-range lane) of those scratch words into `.global` accumulator address `72`. Inter-kernel
    host stream ordering threads `globalMem` from `k_0` into `k_1` without false cross-launch race
    traps, matching LNIR `.dotProduct` (`#[230]`) with `0` UB traps. -/
theorem ptx_seq_zipMul_then_atom_add_eq_dotProduct :
    let d : LNIRDecl :=
      { name := "dot_decl"
      , params :=
          [ { id := 0, name := "x", ty := .sarray .i64 }
          , { id := 1, name := "y", ty := .sarray .i64 } ]
      , retTy := .sarray .i64
      , body := .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 .dotProduct (.ret 3)) }
    let env : VarEnv := (VarEnv.empty.bind 0 (.sarrayId 1)).bind 1 (.sarrayId 2)
    let st : HeapState :=
      { buffers :=
          [ { id := 1, exclusive := true, data := #[10, 20, 30] }
          , { id := 2, exclusive := true, data := #[2, 3, 5] } ]
      , nextId := 2 }
    let kMul : PTXKernel := lowerKind "lean_native_decl_dot_mul" .zipMul
    let kAdd : PTXKernel :=
      { name := "ptx_atom_add_reduce"
      , params :=
          [ { ty := .u64, name := "scratch" }
          , { ty := .u64, name := "acc" }
          , { ty := .u64, name := "n" } ]
      , regDecls :=
          [ { ty := .u32, prefixName := "%r", count := 3 }
          , { ty := .u64, prefixName := "%rd", count := 8 }
          , { ty := .pred, prefixName := "%p", count := 1 } ]
      , body :=
          [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
          , .instr none (.mov .u32 "%r1" (.sreg .ntidX))
          , .instr none (.mov .u32 "%r2" (.sreg .tidX))
          , .instr none (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
          , .instr none (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
          , .instr none (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
          , .instr none (.ldParam .u64 "%rd3" "n")
          , .instr none (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
          , .instr (some { predReg := "%p0" }) .ret
          , .instr none (.barSync 0)
          , .instr none (.shl .b64 "%rd4" (.reg "%rd2") (.immU64 3#64))
          , .instr none (.ldParam .u64 "%rd5" "scratch")
          , .instr none (.add .none .u64 "%rd5" (.reg "%rd5") (.reg "%rd4"))
          , .instr none (.ldGlobal .u64 "%rd5" (.regOffset "%rd5" 0))
          , .instr none (.ldParam .u64 "%rd6" "acc")
          , .instr none (.atomAdd .global .u64 "%rd7" (.regOffset "%rd6" 0) (.reg "%rd5"))
          , .instr none .ret ] }
    let g0 := ByteMemory.ofU64Words
      [ 10#64, 20#64, 30#64, 2#64, 3#64, 5#64, 0#64, 0#64, 0#64, 0#64 ]
    let launches : List PTXKernelLaunchSpec :=
      [ { fuelPerCTA := 128
        , kernel := kMul
        , gridDim := { x := 2 }
        , blockDim := { x := 2 }
        , paramMem :=
            { params :=
                [ ("param_out", 48#64), ("param_in0", 0#64), ("param_in1", 24#64), ("param_n", 3#64) ] } }
      , { fuelPerCTA := 128
        , kernel := kAdd
        , gridDim := { x := 2 }
        , blockDim := { x := 2 }
        , paramMem := { params := [ ("scratch", 48#64), ("acc", 72#64), ("n", 3#64) ] } } ]
    (∃ (outId : Nat) (stOut : HeapState) (outBuf : ArrayBuffer),
      evalCode 8 env st d.body = .ok (.sarrayId outId, stOut) ∧
      stOut.findBuffer outId = some outBuf ∧
      outBuf.data = #[230]) ∧
    (∃ gFinal evs,
      evalPTXMultiKernelSeq launches g0 = .ok (gFinal, evs) ∧
      gFinal.loadBits 48 8 = some 20#64 ∧
      gFinal.loadBits 56 8 = some 60#64 ∧
      gFinal.loadBits 64 8 = some 150#64 ∧
      gFinal.loadBits 72 8 = some (230 : UInt64).toBitVec ∧
      (evs.filter (fun e => e.kernelIdx == 0 && e.isWrite)).length = 3 ∧
      (evs.filter (fun e => e.kernelIdx == 1 && e.isAtomic)).length = 3 ∧
      sumAtomAddDeltas (evs.filter (fun e => e.kernelIdx == 1 && e.isAtomic)) = 230#64) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · refine ⟨3,
      { buffers :=
          [ { id := 3, exclusive := true, data := #[230] }
          , { id := 1, exclusive := true, data := #[10, 20, 30] }
          , { id := 2, exclusive := true, data := #[2, 3, 5] } ]
        nextId := 3 },
      { id := 3, exclusive := true, data := #[230] }, ?_, ?_, rfl⟩
    · simp [evalCode, evalExpr, VarEnv.bind, HeapState.findBuffer,
        evalParFor, evalVarList, List.range, List.range.loop,
        evalParKernelLoop, evalParKernelElem, readParInput, HeapState.readElem]
    · simp [HeapState.findBuffer]
  · have hchk :
        (match evalPTXMultiKernelSeq
            [ { fuelPerCTA := 128
              , kernel := lowerKind "lean_native_decl_dot_mul" .zipMul
              , gridDim := { x := 2 }
              , blockDim := { x := 2 }
              , paramMem :=
                  { params :=
                      [ ("param_out", 48#64)
                      , ("param_in0", 0#64)
                      , ("param_in1", 24#64)
                      , ("param_n", 3#64) ] } }
            , { fuelPerCTA := 128
              , kernel :=
                  { name := "ptx_atom_add_reduce"
                  , params :=
                      [ { ty := .u64, name := "scratch" }
                      , { ty := .u64, name := "acc" }
                      , { ty := .u64, name := "n" } ]
                  , regDecls :=
                      [ { ty := .u32, prefixName := "%r", count := 3 }
                      , { ty := .u64, prefixName := "%rd", count := 8 }
                      , { ty := .pred, prefixName := "%p", count := 1 } ]
                  , body :=
                      [ .instr none (.mov .u32 "%r0" (.sreg .ctaidX))
                      , .instr none (.mov .u32 "%r1" (.sreg .ntidX))
                      , .instr none (.mov .u32 "%r2" (.sreg .tidX))
                      , .instr none (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
                      , .instr none (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
                      , .instr none (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
                      , .instr none (.ldParam .u64 "%rd3" "n")
                      , .instr none (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
                      , .instr (some { predReg := "%p0" }) .ret
                      , .instr none (.barSync 0)
                      , .instr none (.shl .b64 "%rd4" (.reg "%rd2") (.immU64 3#64))
                      , .instr none (.ldParam .u64 "%rd5" "scratch")
                      , .instr none (.add .none .u64 "%rd5" (.reg "%rd5") (.reg "%rd4"))
                      , .instr none (.ldGlobal .u64 "%rd5" (.regOffset "%rd5" 0))
                      , .instr none (.ldParam .u64 "%rd6" "acc")
                      , .instr none (.atomAdd .global .u64 "%rd7" (.regOffset "%rd6" 0) (.reg "%rd5"))
                      , .instr none .ret ] }
              , gridDim := { x := 2 }
              , blockDim := { x := 2 }
              , paramMem := { params := [ ("scratch", 48#64), ("acc", 72#64), ("n", 3#64) ] } } ]
            (ByteMemory.ofU64Words
              [ 10#64, 20#64, 30#64, 2#64, 3#64, 5#64, 0#64, 0#64, 0#64, 0#64 ]) with
         | .ok (gFinal, evs) =>
           gFinal.loadBits 48 8 == some 20#64 &&
           gFinal.loadBits 56 8 == some 60#64 &&
           gFinal.loadBits 64 8 == some 150#64 &&
           gFinal.loadBits 72 8 == some (230 : UInt64).toBitVec &&
           (evs.filter (fun e => e.kernelIdx == 0 && e.isWrite)).length == 3 &&
           (evs.filter (fun e => e.kernelIdx == 1 && e.isAtomic)).length == 3 &&
           sumAtomAddDeltas (evs.filter (fun e => e.kernelIdx == 1 && e.isAtomic)) == 230#64
         | _ => false) = true := rfl
    revert hchk
    generalize evalPTXMultiKernelSeq _ _ = rr
    intro hchk
    cases rr <;> try contradiction
    rename_i res
    rcases res with ⟨gFinal, evs⟩
    dsimp only at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨h16, h7⟩
    rcases Bool.and_eq_true_iff.mp h16 with ⟨h15, h6⟩
    rcases Bool.and_eq_true_iff.mp h15 with ⟨h14, h5⟩
    rcases Bool.and_eq_true_iff.mp h14 with ⟨h13, h4⟩
    rcases Bool.and_eq_true_iff.mp h13 with ⟨h12, h3⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
    exact ⟨gFinal, evs, rfl, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3,
      beq_iff_eq.mp h4, beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7⟩

end LeanNative.Proofs.PTXDeclProofs
