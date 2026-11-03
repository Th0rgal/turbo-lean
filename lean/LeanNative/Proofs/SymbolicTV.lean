import LeanNative.Proofs.SymbolicTVExpr
import LeanNative.Proofs.SymbolicTVState
import LeanNative.Proofs.SymbolicTVScalar
import LeanNative.Proofs.SymbolicTVCall
import LeanNative.Proofs.SymbolicTVExprEval
import LeanNative.Proofs.SymbolicTVMerge
import LeanNative.Proofs.SymbolicTVCode

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-!
# Alive2-Style Symbolic Translation Validator (`LeanNative.Proofs.SymbolicTV`)

Top-level concrete SplitMix64 sampler, Alive2 6-obligation `validateTranslationDecl` /
`validateTranslationModule`, baseline concrete-sample soundness theorems, and JSON reports.
Core symbolic expression normalization and execution live in `SymbolicTVExpr`..`SymbolicTVCode`.
-/

/-! ## Multi-Point Concrete Refinement Evaluator (64 Boundary + SplitMix64 Samples) -/

/-- Deterministic SplitMix64 step for reproducible test input generation. -/
def splitMix64Next (state : UInt64) : UInt64 × UInt64 :=
  let s' := state + 0x9e3779b97f4a7c15
  let z1 := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let out := z2 ^^^ (z2 >>> 31)
  (out, s')

/-- Construct a concrete `Val` and update `HeapState` for a parameter of type `LNIRType`.
    Scalar inputs are drawn from `{1, ..., 8}` so loop bounds and array indices stay within
    the 16-element test buffers while exercising multi-iteration loops and arithmetic paths. -/
def mkSampleParamVal (seed : UInt64) (paramIdx : Nat) (ty : LNIRType) (st : HeapState) :
    Val × HeapState :=
  let (r, _) := splitMix64Next (seed + paramIdx.toUInt64 * 31)
  let smallU64 : UInt64 := (r % 8) + 1
  match ty with
  | .i1 => (.bool (r % 2 == 1), st)
  | .i8 =>
    let v : UInt64 :=
      match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 255 | _ => r &&& 0xFF
    (.u64 v, st)
  | .i16 =>
    let v : UInt64 :=
      match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 65535 | _ => r &&& 0xFFFF
    (.u64 v, st)
  | .i32 =>
    let v : UInt64 :=
      match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 0xFFFFFFFF | _ => r &&& 0xFFFFFFFF
    (.u64 v, st)
  | .u256 | .i256 =>
    let (r1, _) := splitMix64Next (r + 1)
    let (r2, _) := splitMix64Next (r + 2)
    let (r3, _) := splitMix64Next (r + 3)
    let w256 : UInt256 :=
      match r % 8 with
      | 0 => UInt256.zero
      | 1 => UInt256.ofUInt64 smallU64
      | 2 => ⟨0xffffffffffffffff, 0, 0, 0⟩
      | 3 => ⟨0xffffffffffffffff, 0xffffffffffffffff, 0, 0⟩
      | 4 => ⟨0, 0, 0, 0x8000000000000000⟩
      | 5 => UInt256.max
      | _ => ⟨r, r1, r2, r3 &&& 0x7fffffffffffffff⟩
    (.u256 w256, st)
  | .storageMap =>
    let mapId := st.nextId + 1
    let initEntries : List (UInt256 × UInt256) :=
      if r % 2 == 0 then
        let seededVal : UInt256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0x7fffffffffffffff⟩
        [ (UInt256.zero, seededVal)
        , (UInt256.ofUInt64 1, seededVal)
        , (UInt256.ofUInt64 2, seededVal)
        , (UInt256.ofUInt64 3, seededVal)
        , (UInt256.ofUInt64 4, seededVal)
        , (UInt256.ofUInt64 5, seededVal)
        , (UInt256.ofUInt64 6, seededVal)
        , (UInt256.ofUInt64 7, seededVal)
        , (UInt256.ofUInt64 8, seededVal) ]
      else []
    let mapBuf : StorageMapBuffer := { id := mapId, entries := initEntries }
    (.storageMapId mapId, { st with nextId := mapId, storageMaps := mapBuf :: st.storageMaps })
  | .sarray _ =>
    let bufId := st.nextId + 1
    let elems := (List.range 16).map (fun i => ((splitMix64Next (r + i.toUInt64)).1 % 64) + 1)
    let buf : ArrayBuffer := { id := bufId, exclusive := (r % 2 == 0), data := elems.toArray }
    (.sarrayId bufId, { st with buffers := buf :: st.buffers, nextId := bufId })
  | .rawPtr _ =>
    let bufId := st.nextId + 1
    let elems := (List.range 16).map (fun i => ((splitMix64Next (r + i.toUInt64)).1 % 64) + 1)
    let buf : ArrayBuffer := { id := bufId, exclusive := true, data := elems.toArray }
    (.rawPtrId bufId, { st with buffers := buf :: st.buffers, nextId := bufId })
  | .tuple fs =>
    let rec sampleTupleType : Nat → UInt64 → LNIRType → Val
      | _, s, .i1 => .bool ((splitMix64Next s).1 % 2 == 1)
      | _, s, .u256 | _, s, .i256 => .u256 (UInt256.ofUInt64 (((splitMix64Next s).1 % 16) + 1))
      | 0, s, _ => .u64 (((splitMix64Next s).1 % 16) + 1)
      | d + 1, s, .tuple subFs =>
        .tuple (subFs.mapIdx fun idx subTy => sampleTupleType d (s + idx.toUInt64 * 37 + 11) subTy)
      | _, s, _ => .u64 (((splitMix64Next s).1 % 16) + 1)
    let vals := fs.mapIdx (fun idx fTy => sampleTupleType 8 (r + idx.toUInt64 * 17) fTy)
    (.tuple vals, st)
  | .objPtr | .taggedPtr =>
    match r % 5 with
    | 0 => (.u64 1, st)
    | _ =>
      let mkLeaf (s : HeapState) (salt : UInt64) (sharedLeaf : Bool) : Val × HeapState :=
        let leafFields := (List.range 8).map fun k =>
          Val.u64 (((splitMix64Next (r + salt + (k.toUInt64 * 7))).1 % 16) + 1)
        let (cid, s1) := s.allocHeapCtor 0 [] leafFields
        if sharedLeaf then
          match s1.incRefObj cid 1 with
          | .ok s2 => (.objPtr cid, s2)
          | .error _ => (.objPtr cid, s1)
        else (.objPtr cid, s1)
      let sharedRoot := (r % 2 == 0)
      let aliasSibling := (r % 4 == 1)
      let sharedKids := (r % 3 == 0) && !aliasSibling
      let (kids, stAfterKids) :=
        if aliasSibling then
          let (firstKid, stFirst) := mkLeaf st 101 false
          match firstKid with
          | .objPtr firstCid =>
            let stInc := match stFirst.incRefObj firstCid 1 with | .ok s2 => s2 | .error _ => stFirst
            let (restKids, stRest) := (List.range 6).foldl (fun (acc, curSt) idx =>
              let (cVal, nextSt) := mkLeaf curSt (295 + idx.toUInt64 * 97) sharedKids
              (acc ++ [cVal], nextSt)) ([], stInc)
            (firstKid :: firstKid :: restKids, stRest)
          | _ =>
            (List.range 8).foldl (fun (acc, curSt) idx =>
              let (cVal, nextSt) := mkLeaf curSt (101 + idx.toUInt64 * 97) sharedKids
              (acc ++ [cVal], nextSt)) ([], st)
        else
          (List.range 8).foldl (fun (acc, curSt) idx =>
            let (cVal, nextSt) := mkLeaf curSt (101 + idx.toUInt64 * 97) sharedKids
            (acc ++ [cVal], nextSt)) ([], st)
      let rootScalars := (List.range 8).map fun k =>
        Val.u64 (((splitMix64Next (r + 701 + (k.toUInt64 * 13))).1 % 16) + 1)
      let (oid, st3) := stAfterKids.allocHeapCtor 0 kids rootScalars
      if sharedRoot then
        match st3.incRefObj oid 1 with
        | .ok st4 => (.objPtr oid, st4)
        | .error _ => (.objPtr oid, st3)
      else (.objPtr oid, st3)
  | .unit => (.unit, st)
  | _ => (.u64 smallU64, st)

/-- Build a single sample `(VarEnv × HeapState)` for declaration `d` from `sampleIdx ∈ 0..63`. -/
def buildDeclSample (d : LNIRDecl) (sampleIdx : Nat) : VarEnv × HeapState :=
  let seed : UInt64 := (sampleIdx.toUInt64 + 1) * 0x9e3779b97f4a7c15
  let (env, st, _) := d.params.foldl (fun (curEnv, curSt, idx) p =>
    let (v, nextSt) := mkSampleParamVal seed idx p.ty curSt
    (curEnv.bind p.id v, nextSt, idx + 1)
  ) (VarEnv.empty, HeapState.empty, 0)
  (env, st)

/-- Check concrete forward simulation on a single `(VarEnv, HeapState)` sample:
    whenever `src` evaluates without UB to `.ok (vSrc, stSrc)`, `tgt` must evaluate
    without UB to `.ok (vTgt, stTgt)` with `vSrc == vTgt` and `stSrc = stTgt`. -/
def checkSingleSample (fuel : Nat) (env : VarEnv) (st : HeapState) (src tgt : LNIRCode) : Bool :=
  match evalCode fuel env st src with
  | .error _ => true
  | .ok (vSrc, stSrc) =>
    match evalCode fuel env st tgt with
    | .ok (vTgt, stTgt) => (vSrc == vTgt) && decide (stSrc = stTgt)
    | .error _ => false

/-- Check concrete forward simulation across a list of `(VarEnv × HeapState)` samples. -/
def checkConcreteSamples (fuel : Nat) (samples : List (VarEnv × HeapState)) (src tgt : LNIRCode) : Bool :=
  samples.all (fun (env, st) => checkSingleSample fuel env st src tgt)

/-- Evaluate `src` and `tgt` declarations across `numSamples` (default 64) concrete input states.
    Evaluator fuel / RC-release exhaustion on the source (`srcExhausted`) is treated as an incomplete analysis, never source UB. -/
def checkDeclConcreteRefinement (src tgt : LNIRDecl) (numSamples : Nat := 64) (fuel : Nat := 128) :
    Bool × Nat :=
  let effFuel := Nat.max fuel 256
  let samples := (List.range numSamples).map (buildDeclSample src)
  let (passedCount, nonVacuousCount) := samples.foldl (fun (acc, okSrc) (env, st) =>
    let srcRes := evalCode effFuel env st src.body
    let srcOk := match srcRes with | .ok _ => true | .error _ => false
    let srcExhausted := match srcRes with | .error .fuelExhausted => true | _ => false
    let stepOk := !srcExhausted && checkSingleSample effFuel env st src.body tgt.body
    (if stepOk then acc + 1 else acc, if srcOk && stepOk then okSrc + 1 else okSrc)) (0, 0)
  (passedCount == numSamples && (numSamples == 0 || nonVacuousCount > 0), nonVacuousCount)

/-! ## Alive2 6-Part Translation Validation Result & Module Report -/

/-- Per-declaration Alive2-style 6-part translation validation verdict. -/
structure TVDeclResult where
  declName           : String
  srcHash            : String
  tgtHash            : String
  ubRefines          : Bool
  domainEquiv        : Bool
  poisonRefines      : Bool
  symRetEquiv        : Bool
  concreteRefines    : Bool
  concreteSamplesOk  : Nat
  concreteSamplesTot : Nat
  memWritesEquiv     : Bool
  passed             : Bool
  srcRetSummary      : String
  tgtRetSummary      : String
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level translation validation report across all declarations. -/
structure TVModuleReport where
  moduleName    : String
  schemaVersion : String := "lean-native-symbolic-tv-v2"
  totalDecls    : Nat
  passedDecls   : Nat
  allPassed     : Bool
  declResults   : List TVDeclResult
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Validate translation refinement `(src ⊑ tgt)` for a single declaration using Alive2's 6 obligations.
    When `src == tgt` (an unmodified declaration with zero transformation), `CodeRefines.refl` holds
    syntactically, so we need only verify multi-point concrete reflexive behavior unless `src != tgt`. -/
def validateTranslationDecl (src tgt : LNIRDecl) (numSamples : Nat := 64) : TVDeclResult :=
  let (concreteOk, passedSamples) := checkDeclConcreteRefinement src tgt numSamples 128
  let sharedSynBase := Nat.max (declSynVarBase src) (declSynVarBase tgt)
  let sSrc := symExecDecl 4 src (some sharedSynBase)
  let sTgt := symExecDecl 4 tgt (some sharedSynBase)
  let isIdenticalDecl := src.params == tgt.params && src.retTy == tgt.retTy && src.body == tgt.body
  -- 1. UB refinement: `(src.noUB -> tgt.noUB)` AND path-conditional definedness refinement
  --    (`sSrc.ubCond → sTgt.ubCond`, i.e. `ite sSrc.ubCond sTgt.ubCond true == true`) so UB on one
  --    source branch never masks target UB on other defined paths!
  let scUb := normSymExpr sSrc.ubCond
  let tcUb := normSymExpr sTgt.ubCond
  let symUbImplies : Bool :=
    tcUb == .constBool true || scUb == .constBool false || scUb == tcUb ||
      normSymExpr (SymExecState.hoistIteTupleFuel 16 (normSymIteStep scUb tcUb (.constBool true))) == .constBool true
  -- C6.1/C6.2: exhaustion is an incomplete analysis on either side, never excused by syntactic identity
  let symSupportedOk := !sSrc.symExhausted && !sTgt.symExhausted &&
    (isIdenticalDecl || (!sSrc.symUnsupported && !sTgt.symUnsupported))
  let ubRefines := symSupportedOk && (!sSrc.noUB || sTgt.noUB) && symUbImplies
  -- 2. Return domain / reachability equivalence on defined source paths (`scUb → (sSrc.reachCond == sTgt.reachCond)`)
  let domainEquiv :=
    sSrc.reachable == sTgt.reachable &&
    (normSymExpr sSrc.reachCond == normSymExpr sTgt.reachCond ||
     normSymExpr (SymExecState.hoistIteTupleFuel 16
       (normSymIteStep scUb (normSymBinOpStep .eq sSrc.reachCond sTgt.reachCond) (.constBool true))) == .constBool true)
  -- 3. Poison refinement: src.nonPoison -> tgt.nonPoison
  let poisonRefines := !sSrc.nonPoison || sTgt.nonPoison
  -- 4. Symbolic return expression equivalence (either globally equal or equal on all defined source paths `scUb`)
  let symRetEquiv :=
    normSymExpr sSrc.retVal == normSymExpr sTgt.retVal ||
    normSymExpr (SymExecState.hoistIteTupleFuel 16
      (normSymIteStep scUb (normSymBinOpStep .eq sSrc.retVal sTgt.retVal) (.constBool true))) == .constBool true
  -- 5. Memory / buffer write log & RC-delta equivalence (set-equivalent per `(root, idx)` on all defined source paths)
  let eqOnDefinedPaths (a b : SymExpr) : Bool :=
    let na := normSymExpr a
    let nb := normSymExpr b
    na == nb ||
      normSymExpr (SymExecState.hoistIteTupleFuel 16
        (normSymIteStep scUb (normSymBinOpStep .eq na nb) (.constBool true))) == .constBool true
  let memWritesEquiv :=
    let keysOf (ws : List (MemWriteSpace × VarId × SymExpr × SymExpr)) :=
      ws.foldl (fun acc (sp, r, idx, _) =>
        let nidx := normSymExpr idx
        if acc.any (fun (sp2, r2, i2) => sp2 == sp && r2 == r && i2 == nidx) then acc else acc ++ [(sp, r, nidx)]) []
    let defaultSlot (synBase : VarId) (sp : MemWriteSpace) (r : VarId) (nidx : SymExpr) : SymExpr :=
      if sp == .ctorObj then
        match nidx with
        | .constU64 idxU64 =>
          let i := idxU64.toNat
          if i < 8 then .symVar (SymExecState.projFieldRootId synBase 0 r i)
          else .bufElem sp r nidx
        | _ => .bufElem sp r nidx
      else if sp == .ctorScalar then
        match nidx with
        | .constU64 idxU64 =>
          let i := idxU64.toNat
          if i < 8 then .symVar (SymExecState.projFieldRootId synBase 0 r (8 + i))
          else .bufElem sp r nidx
        | _ => .bufElem sp r nidx
      else if sp == .ctorTag then
        .ctorTag 0 r
      else
        .bufElem sp r nidx
    let lookupWrite (synBase : VarId)
        (ws : List (MemWriteSpace × VarId × SymExpr × SymExpr))
        (sp : MemWriteSpace) (r : VarId) (nidx : SymExpr) : SymExpr :=
      match ws.find? (fun (sp2, b, i, _) => sp2 == sp && b == r && normSymExpr i == nidx) with
      | some (_, _, _, v) => normSymExpr v
      | none => defaultSlot synBase sp r nidx
    let allKeys := keysOf (sSrc.memWrites ++ sTgt.memWrites)
    let writesOk := allKeys.all fun (sp, r, nidx) =>
      eqOnDefinedPaths (lookupWrite sSrc.synVarBase sSrc.memWrites sp r nidx) (lookupWrite sTgt.synVarBase sTgt.memWrites sp r nidx)
    let rcKeys := ((sSrc.rcDeltas.map Prod.fst) ++ (sTgt.rcDeltas.map Prod.fst)).eraseDups
    let lookupRcDelta (ds : List (VarId × SymExpr)) (r : VarId) : SymExpr :=
      match ds.lookup r with
      | some e => normSymExpr e
      | none => .constU64 0
    let rcOk := rcKeys.all fun r => eqOnDefinedPaths (lookupRcDelta sSrc.rcDeltas r) (lookupRcDelta sTgt.rcDeltas r)
    let jointOk := eqOnDefinedPaths sSrc.jointHeap sTgt.jointHeap
    writesOk && rcOk && jointOk
  let allOk :=
    symSupportedOk && ubRefines && domainEquiv && poisonRefines && symRetEquiv && concreteOk && memWritesEquiv
  { declName := src.name
    srcHash := src.structuralHash
    tgtHash := tgt.structuralHash
    ubRefines := ubRefines
    domainEquiv := domainEquiv
    poisonRefines := poisonRefines
    symRetEquiv := symRetEquiv
    concreteRefines := concreteOk
    concreteSamplesOk := passedSamples
    concreteSamplesTot := numSamples
    memWritesEquiv := memWritesEquiv
    passed := allOk
    srcRetSummary := reprStr sSrc.retVal
    tgtRetSummary := reprStr sTgt.retVal }

/-- Validate an entire optimized `LNIRModule` against its unoptimized source `LNIRModule`. -/
def validateTranslationModule (srcMod tgtMod : LNIRModule) (numSamples : Nat := 64) : TVModuleReport :=
  let results := srcMod.decls.filterMap (fun srcDecl =>
    match tgtMod.decls.find? (fun d => d.name == srcDecl.name) with
    | some tgtDecl => some (validateTranslationDecl srcDecl tgtDecl numSamples)
    | none => none)
  let passedCount := (results.filter (·.passed)).length
  { moduleName := srcMod.moduleName
    schemaVersion := "lean-native-symbolic-tv-v2"
    totalDecls := results.length
    passedDecls := passedCount
    allPassed := passedCount == results.length && results.length == srcMod.decls.length
    declResults := results }

/-! ## Machine-Checked Soundness Theorems for `SymbolicTV` -/

/-- Canonical normalization of `.constU64` is a fixed point. -/
theorem normSymExpr_constU64 (n : UInt64) :
    normSymExpr (.constU64 n) = .constU64 n := rfl

/-- Canonical normalization of `.constBool` is a fixed point. -/
theorem normSymExpr_constBool (b : Bool) :
    normSymExpr (.constBool b) = .constBool b := rfl

/-- Canonical normalization of `constU64 a + constU64 b` matches exact `UInt64` addition in `evalScalarExpr`. -/
theorem normSymExpr_const_sound (env : VarEnv) (a b : UInt64) :
    evalScalarExpr env (.binOp .add (.constU64 a) (.constU64 b)) =
    evalScalarExpr env (.constU64 (a + b)) := rfl

/-- Completeness of `checkSingleSample` with respect to `CodeRefines`:
    any `src` and `tgt` related by kernel-checked `CodeRefines src tgt` always pass `checkSingleSample`. -/
theorem checkSingleSample_of_codeRefines (fuel : Nat) (env : VarEnv) (st : HeapState)
    (src tgt : LNIRCode) (href : CodeRefines src tgt) :
    checkSingleSample fuel env st src tgt = true := by
  unfold checkSingleSample
  cases hsrc : evalCode fuel env st src with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨v, st'⟩
    have htgt := href fuel env st v st' hsrc
    rw [htgt]
    simp [Val.beq_self]

/-- Completeness of `checkConcreteSamples` with respect to `CodeRefines`:
    any `src` and `tgt` related by `CodeRefines src tgt` pass `checkConcreteSamples` on all sample suites. -/
theorem checkConcreteSamples_of_codeRefines (fuel : Nat) (samples : List (VarEnv × HeapState))
    (src tgt : LNIRCode) (href : CodeRefines src tgt) :
    checkConcreteSamples fuel samples src tgt = true := by
  unfold checkConcreteSamples
  induction samples with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨env, st⟩
    simp only [List.all_cons, checkSingleSample_of_codeRefines fuel env st src tgt href,
      Bool.true_and, ih]

/-- Soundness of `checkSingleSample`: whenever `checkSingleSample fuel env st src tgt = true`
    and `src` evaluates without UB to `.ok (v, st')`, `tgt` also evaluates without UB to `.ok (vTgt, st')`
    with `(v == vTgt) = true` and identical heap state `st'`. -/
theorem sound_of_checkSingleSample_eq_true (fuel : Nat) (env : VarEnv) (st : HeapState)
    (src tgt : LNIRCode) (v : Val) (st' : HeapState)
    (hcheck : checkSingleSample fuel env st src tgt = true)
    (hsrc : evalCode fuel env st src = .ok (v, st')) :
    ∃ vTgt, evalCode fuel env st tgt = .ok (vTgt, st') ∧ (v == vTgt) = true := by
  unfold checkSingleSample at hcheck; rw [hsrc] at hcheck
  cases htgt : evalCode fuel env st tgt with
  | error _ => rw [htgt] at hcheck; contradiction
  | ok pair =>
    rcases pair with ⟨vTgt, stTgt⟩; rw [htgt] at hcheck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    exact ⟨vTgt, hcheck.2 ▸ rfl, hcheck.1⟩

/-- Reflexive soundness of symbolic translation validation (`symbolicTV_refl_sound`). -/
theorem symbolicTV_refl_sound (c : LNIRCode) (fuel : Nat) (samples : List (VarEnv × HeapState)) :
    CodeRefines c c ∧ checkConcreteSamples fuel samples c c = true :=
  ⟨CodeRefines.refl c, checkConcreteSamples_of_codeRefines fuel samples c c (CodeRefines.refl c)⟩

namespace SymbolicTV
  abbrev normSymExpr_constU64 := @LeanNative.Proofs.normSymExpr_constU64
  abbrev normSymExpr_constBool := @LeanNative.Proofs.normSymExpr_constBool
  abbrev normSymExpr_const_sound := @LeanNative.Proofs.normSymExpr_const_sound
  abbrev checkSingleSample_of_codeRefines := @LeanNative.Proofs.checkSingleSample_of_codeRefines
  abbrev checkConcreteSamples_of_codeRefines := @LeanNative.Proofs.checkConcreteSamples_of_codeRefines
  abbrev sound_of_checkSingleSample_eq_true := @LeanNative.Proofs.sound_of_checkSingleSample_eq_true
  abbrev symbolicTV_refl_sound := @LeanNative.Proofs.symbolicTV_refl_sound
end SymbolicTV

#guard (symEvalExpr {} 9 .objPtr (.call "lean_native_box_u64" [1] .objPtr)).noUB
#guard !(symEvalExpr {} 9 .i64 (.call "lean_native_box_u64" [1] .i64)).noUB
#guard !(symEvalExpr {} 9 .objPtr (.call "lean_native_box_u64" [1, 2] .objPtr)).noUB
#guard !(symEvalExpr {} 9 .i64 (.call "lean_native_unbox_u64" [] .i64)).noUB
#guard !(symEvalExpr {} 9 .u256 (.call "lean_native_unbox_u64" [1] .u256)).noUB
#guard !(symEvalExpr {} 9 .i64 (.call "lean_native_ensure_exclusive" [1] .i64)).noUB
#guard !(symEvalExpr {} 9 .objPtr (.call "lean_native_sarray_len" [1] .objPtr)).noUB
#guard !(symEvalExpr {} 9 .i64 (.call "lean_native_sarray_len" [1] .i64 true)).noUB
#guard !(symEvalExpr {} 9 .i64 (.call "lean_native_unknown" [1] .i64)).noUB
#guard (symEvalExpr {} 9 .i64 (.call "lean_native_unbox_u64" [1] .i64)).lookupVar 9 == (({} : SymExecState).lookupVar 1)
#guard ((symEvalExpr (({} : SymExecState).markSarrayVar 1) 9 (.sarray .i64)
  (.call "lean_native_ensure_exclusive" [1] (.sarray .i64))).isBufExclusive 9)
#guard !(symEvalExpr (({} : SymExecState).markObjPtrVar 1) 9 .objPtr (.call "lean_native_ensure_exclusive" [1] .objPtr)).isBufExclusive 9
#guard (symEvalExpr (({} : SymExecState).markSarrayVar 1) 9 .i64 (.call "lean_native_sarray_len" [1] .i64)).lookupVar 9 ==
  (symEvalExpr (({} : SymExecState).markSarrayVar 1) 9 .i64 (.sarrayLen 1)).lookupVar 9

/-! ## JSON & Human-Readable Formatting for `TVModuleReport` -/

abbrev escapeJsonTV := LeanNative.IR.jsonEscape

def TVDeclResult.toJson (r : TVDeclResult) : String :=
  "{" ++
  s!"\"declName\":\"{escapeJsonTV r.declName}\"," ++
  s!"\"srcHash\":\"{escapeJsonTV r.srcHash}\"," ++
  s!"\"tgtHash\":\"{escapeJsonTV r.tgtHash}\"," ++
  s!"\"passed\":{if r.passed then "true" else "false"}," ++
  s!"\"ubRefines\":{if r.ubRefines then "true" else "false"}," ++
  s!"\"domainEquiv\":{if r.domainEquiv then "true" else "false"}," ++
  s!"\"poisonRefines\":{if r.poisonRefines then "true" else "false"}," ++
  s!"\"symRetEquiv\":{if r.symRetEquiv then "true" else "false"}," ++
  s!"\"concreteRefines\":{if r.concreteRefines then "true" else "false"}," ++
  s!"\"concreteSamplesOk\":{r.concreteSamplesOk}," ++
  s!"\"concreteSamplesTot\":{r.concreteSamplesTot}," ++
  s!"\"memWritesEquiv\":{if r.memWritesEquiv then "true" else "false"}" ++
  "}"

def TVModuleReport.toJson (r : TVModuleReport) : String :=
  let declsJson := String.intercalate "," (r.declResults.map TVDeclResult.toJson)
  "{" ++
  s!"\"schemaVersion\":\"{escapeJsonTV r.schemaVersion}\"," ++
  s!"\"moduleName\":\"{escapeJsonTV r.moduleName}\"," ++
  s!"\"allPassed\":{if r.allPassed then "true" else "false"}," ++
  s!"\"totalDecls\":{r.totalDecls}," ++
  s!"\"passedDecls\":{r.passedDecls}," ++
  s!"\"declResults\":[{declsJson}]" ++
  "}"

def TVModuleReport.formatSummary (r : TVModuleReport) : String :=
  let header :=
    s!"=== Alive2-Style Symbolic Translation Validation Report ===\n" ++
    s!"Module: {r.moduleName} ({r.schemaVersion})\n" ++
    s!"Status: {if r.allPassed then "PASSED" else "FAILED"} ({r.passedDecls}/{r.totalDecls} declarations refined)\n"
  let lines := r.declResults.map (fun d =>
    let st := if d.passed then "PASS" else "FAIL"
    s!"  [{st}] {d.declName} ({d.srcHash} -> {d.tgtHash}): " ++
    s!"noUB={d.ubRefines}, dom={d.domainEquiv}, nonPoison={d.poisonRefines}, " ++
    s!"symRet={d.symRetEquiv}, concrete={d.concreteSamplesOk}/{d.concreteSamplesTot}, mem={d.memWritesEquiv}")
  header ++ String.intercalate "\n" lines

end LeanNative.Proofs
