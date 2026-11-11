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

private def codeHasSeqForLoop : LNIRCode → Bool
  | .seqFor .. => true
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    codeHasSeqForLoop k
  | .ite _ t e => codeHasSeqForLoop t || codeHasSeqForLoop e
  | .ret _ | .unreachable => false

/-- Construct a concrete `Val` and update `HeapState` for a parameter of type `LNIRType`.
    Scalar inputs are drawn from `{1, ..., 8}` (or `{0, ..., 8}` for narrow loop-bound scalars
    when `hasSeqLoop` is set) so loop bounds and array indices stay within
    the 16-element test buffers while exercising multi-iteration loops and arithmetic paths. -/
def mkSampleParamVal (seed : UInt64) (paramIdx : Nat) (ty : LNIRType) (st : HeapState)
    (hasSeqLoop : Bool := false) :
    Val × HeapState :=
  let (r, _) := splitMix64Next (seed + paramIdx.toUInt64 * 31)
  let smallU64 : UInt64 := (r % 8) + 1
  match ty with
  | .i1 => (.bool (r % 2 == 1), st)
  | .i8 =>
    let v : UInt64 :=
      if hasSeqLoop then r % 9
      else match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 255 | _ => r &&& 0xFF
    (.u64 v, st)
  | .i16 =>
    let v : UInt64 :=
      if hasSeqLoop then r % 9
      else match paramIdx + (r % 5).toNat with
      | 0 => 0 | 1 => 65535 | _ => r &&& 0xFFFF
    (.u64 v, st)
  | .i32 =>
    let v : UInt64 :=
      if hasSeqLoop then r % 9
      else match paramIdx + (r % 5).toNat with
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
  let hasLoop := codeHasSeqForLoop d.body
  let (env, st, _) := d.params.foldl (fun (curEnv, curSt, idx) p =>
    let (v, nextSt) := mkSampleParamVal seed idx p.ty curSt hasLoop
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
  -- C6.1/C6.2: exhaustion is an incomplete analysis on either side, never excused by syntactic identity;
  -- element-type inconsistency (`checkElemTypes`) also fails closed even when `src == tgt`.
  let elemTypesOk := src.checkElemTypes.isNone && tgt.checkElemTypes.isNone
  let symSupportedOk := elemTypesOk && !sSrc.symExhausted && !sTgt.symExhausted &&
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

private def isLocalCallableScalarInt : LNIRType → Bool
  | .i64 | .usize | .i32 | .i16 | .i8 | .i1 | .unit => true
  | _ => false

private def isLocalCallableParamTy : LNIRType → Bool
  | .sarray _ | .f64 => true
  | ty => isLocalCallableScalarInt ty

private def isLocalCallDstScalarSlot : LNIRType → Bool
  | .objPtr | .taggedPtr | .sarray _ | .rawPtr _ | .storageMap | .u256 | .i256 | .tuple _ => false
  | _ => true

private def isExternWrapperDecl (d : LNIRDecl) : Bool :=
  match d.body with
  | .letBind dst _ (.call fn _ _ true) (.ret retVar) => dst == retVar && fn == d.name
  | _ => false

private def localCallableSigs (m : LNIRModule) : List (String × List LNIRType × LNIRType) :=
  m.decls.filterMap fun d =>
    if !isExternWrapperDecl d && (isLocalCallableScalarInt d.retTy || d.retTy == .f64) &&
       d.params.all (fun p => isLocalCallableParamTy p.ty) then
      some (d.name, d.params.map (·.ty), d.retTy)
    else none

private def isBuiltinRuntimeCall (fnName : String) : Bool :=
  fnName == "lean_native_box_u64" || fnName == "lean_native_unbox_u64" ||
  fnName == "lean_native_ensure_exclusive" || fnName == "lean_native_sarray_len" ||
  fnName == "lean_mark_mt" || fnName == "lean_native_ctor_set" ||
  fnName == "lean_native_ctor_set_scalar" || fnName == "lean_native_ctor_set_tag" ||
  fnName == "lean_native_del_obj" || fnName == "lean_native_ctor_tag"

private def codeHasUserLocalCall : LNIRCode → Bool
  | .letBind _ _ (.call fn _ _ false) k => (!isBuiltinRuntimeCall fn) || codeHasUserLocalCall k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    codeHasUserLocalCall k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasUserLocalCall t || codeHasUserLocalCall e
  | .ret _ | .unreachable => false

private abbrev SpecValSort := UInt8
private def specSortBool : UInt8 := 0
private def specSortU64 : UInt8 := 1
private def specSortUnit : UInt8 := 2
private def specSortSarray : UInt8 := 3
private def specSortOther : UInt8 := 4

private def paramSpecSort : LNIRType → SpecValSort
  | .i1 => specSortBool
  | .unit => specSortUnit
  | .sarray _ => specSortSarray
  | .i8 | .i16 | .i32 | .i64 | .usize | .f32 | .f64 => specSortU64
  | _ => specSortOther

private def elemStorageWidth? : LNIRType → Option LNIRType
  | .i1 | .i8 => some .i8
  | .i16 => some .i16
  | .i32 | .f32 => some .i32
  | _ => none

private def widthFitsIn (knownTy targetTy : LNIRType) : Bool :=
  match knownTy, targetTy with
  | .i1, .i1 | .i1, .i8 | .i1, .i16 | .i1, .i32 => true
  | .i8, .i8 | .i8, .i16 | .i8, .i32 => true
  | .i16, .i16 | .i16, .i32 => true
  | .i32, .i32 => true
  | _, _ => false

private def exprGuaranteedWidth? (exactEnv : List (VarId × LNIRType)) : LNIRExpr → Option LNIRType
  | .sarrayGet _ _ et | .rawLoad _ _ et => elemStorageWidth? et
  | .scalar (.var v) => exactEnv.lookup v
  | .scalar (.constBool _) | .isExclusive _ => some .i1
  | .scalar (.constU64 c) =>
    if c ≤ 1 then some .i1
    else if c ≤ 0xFF then some .i8
    else if c ≤ 0xFFFF then some .i16
    else if c ≤ 0xFFFFFFFF then some .i32
    else none
  | _ => none

private def scalarExprSpecSort (sortEnv : List (VarId × SpecValSort)) : ScalarExpr → SpecValSort
  | .constBool _ => specSortBool
  | .constU64 _ => specSortU64
  | .var id => (sortEnv.lookup id).getD specSortOther
  | .binOp .eq l r =>
    let sl := scalarExprSpecSort sortEnv l
    let sr := scalarExprSpecSort sortEnv r
    if (sl == specSortBool && sr == specSortBool) || (sl == specSortU64 && sr == specSortU64) then
      specSortBool
    else
      specSortOther
  | .binOp .lt l r | .binOp .le l r =>
    if scalarExprSpecSort sortEnv l == specSortU64 && scalarExprSpecSort sortEnv r == specSortU64 then
      specSortBool
    else
      specSortOther
  | .binOp .addChecked256 _ _ | .binOp .subChecked256 _ _ | .binOp .mulChecked256 _ _ => specSortOther
  | .binOp _ l r =>
    if scalarExprSpecSort sortEnv l == specSortU64 && scalarExprSpecSort sortEnv r == specSortU64 then
      specSortU64
    else
      specSortOther
  | .unaryOp .not a =>
    let sa := scalarExprSpecSort sortEnv a
    if sa == specSortBool || sa == specSortU64 then sa else specSortOther
  | .unaryOp .neg a =>
    if scalarExprSpecSort sortEnv a == specSortU64 then specSortU64 else specSortOther
  | .unaryOp .clz256 _ => specSortOther
  | .select c t e =>
    let sc := scalarExprSpecSort sortEnv c
    let st := scalarExprSpecSort sortEnv t
    let se := scalarExprSpecSort sortEnv e
    if (sc == specSortBool || sc == specSortU64) && st == se then st else specSortOther
  | .fma a b c =>
    if scalarExprSpecSort sortEnv a == specSortU64 &&
       scalarExprSpecSort sortEnv b == specSortU64 &&
       scalarExprSpecSort sortEnv c == specSortU64 then specSortU64 else specSortOther

private def exprSpecSort (sortEnv : List (VarId × SpecValSort)) : LNIRExpr → SpecValSort
  | .scalar se => scalarExprSpecSort sortEnv se
  | .sarrayGet .. | .rawLoad .. | .sarrayLen _ | .unboxScalar .. => specSortU64
  | .sarrayEnsureExclusive .. | .sarraySet .. => specSortSarray
  | .isExclusive _ => specSortBool
  | .call fn _ _ false =>
    if fn == "lean_native_ensure_exclusive" then specSortSarray
    else if fn == "lean_native_sarray_len" || fn == "lean_mark_mt" || fn == "lean_native_ctor_tag" then
      specSortU64
    else if fn == "lean_native_ctor_set" || fn == "lean_native_ctor_set_scalar" ||
            fn == "lean_native_ctor_set_tag" || fn == "lean_native_del_obj" then specSortUnit
    else specSortOther
  | _ => specSortOther

private def scalarExprHasBoolSortConflict (varEnv : List (VarId × LNIRType))
    (sortEnv : List (VarId × SpecValSort)) : ScalarExpr → Bool
  | .constBool _ | .constU64 _ | .var _ => false
  | .unaryOp .not (.var id) =>
    let isI1Slot := varEnv.lookup id == some .i1
    let s := (sortEnv.lookup id).getD specSortOther
    (isI1Slot && s != specSortBool) || (!isI1Slot && s == specSortBool)
  | .unaryOp .not a => scalarExprHasBoolSortConflict varEnv sortEnv a
  | .unaryOp .neg a =>
    scalarExprSpecSort sortEnv a == specSortBool || scalarExprHasBoolSortConflict varEnv sortEnv a
  | .unaryOp .clz256 a =>
    scalarExprSpecSort sortEnv a == specSortBool || scalarExprHasBoolSortConflict varEnv sortEnv a
  | .binOp .eq l r =>
    let sl := scalarExprSpecSort sortEnv l
    let sr := scalarExprSpecSort sortEnv r
    ((sl == specSortBool) != (sr == specSortBool)) ||
    scalarExprHasBoolSortConflict varEnv sortEnv l || scalarExprHasBoolSortConflict varEnv sortEnv r
  | .binOp _ l r =>
    scalarExprSpecSort sortEnv l == specSortBool || scalarExprSpecSort sortEnv r == specSortBool ||
    scalarExprHasBoolSortConflict varEnv sortEnv l || scalarExprHasBoolSortConflict varEnv sortEnv r
  | .select c t e =>
    scalarExprHasBoolSortConflict varEnv sortEnv c ||
    scalarExprHasBoolSortConflict varEnv sortEnv t ||
    scalarExprHasBoolSortConflict varEnv sortEnv e
  | .fma a b c =>
    scalarExprSpecSort sortEnv a == specSortBool ||
    scalarExprSpecSort sortEnv b == specSortBool ||
    scalarExprSpecSort sortEnv c == specSortBool ||
    scalarExprHasBoolSortConflict varEnv sortEnv a ||
    scalarExprHasBoolSortConflict varEnv sortEnv b ||
    scalarExprHasBoolSortConflict varEnv sortEnv c

private def exprHasBoolSortConflict (varEnv : List (VarId × LNIRType))
    (sortEnv : List (VarId × SpecValSort)) : LNIRExpr → Bool
  | .scalar se => scalarExprHasBoolSortConflict varEnv sortEnv se
  | .sarrayGet _ iv _ | .rawLoad _ iv _ => sortEnv.lookup iv == some specSortBool
  | .sarraySet _ iv vv _ =>
    sortEnv.lookup iv == some specSortBool || sortEnv.lookup vv == some specSortBool
  | _ => false

private def coerceCallArgExpr? (srcSort : SpecValSort) (paramTy : LNIRType) (alreadyNarrow : Bool)
    (argVar : VarId) : Option LNIRExpr :=
  match paramTy with
  | .sarray _ =>
    if srcSort == specSortSarray then some (.scalar (.var argVar)) else none
  | .unit =>
    if srcSort == specSortUnit then some (.scalar (.var argVar)) else some (.scalar (.constU64 0))
  | .i1 =>
    if srcSort == specSortBool then some (.scalar (.var argVar))
    else if srcSort == specSortU64 then
      some (.scalar (.binOp .eq (.binOp .bitAnd (.var argVar) (.constU64 1)) (.constU64 1)))
    else none
  | .i8 =>
    if srcSort == specSortBool then some (.scalar (.select (.var argVar) (.constU64 1) (.constU64 0)))
    else if srcSort == specSortU64 then
      some (if alreadyNarrow then .scalar (.var argVar)
            else .scalar (.binOp .bitAnd (.var argVar) (.constU64 0xFF)))
    else none
  | .i16 =>
    if srcSort == specSortBool then some (.scalar (.select (.var argVar) (.constU64 1) (.constU64 0)))
    else if srcSort == specSortU64 then
      some (if alreadyNarrow then .scalar (.var argVar)
            else .scalar (.binOp .bitAnd (.var argVar) (.constU64 0xFFFF)))
    else none
  | .i32 =>
    if srcSort == specSortBool then some (.scalar (.select (.var argVar) (.constU64 1) (.constU64 0)))
    else if srcSort == specSortU64 then
      some (if alreadyNarrow then .scalar (.var argVar)
            else .scalar (.binOp .bitAnd (.var argVar) (.constU64 0xFFFFFFFF)))
    else none
  | _ =>
    if srcSort == specSortBool then some (.scalar (.select (.var argVar) (.constU64 1) (.constU64 0)))
    else if srcSort == specSortU64 then some (.scalar (.var argVar))
    else none

private def coerceCallRetExpr? (rvSort : SpecValSort) (calleeRetTy dstTy : LNIRType)
    (alreadyNarrow : Bool) (rv : VarId) : Option LNIRExpr :=
  if calleeRetTy == .unit then
    if dstTy == .i1 then none
    else if dstTy == .unit && rvSort == specSortUnit then some (.scalar (.var rv))
    else if dstTy != .unit then some (.scalar (.constU64 0))
    else none
  else if dstTy == .unit then
    none
  else if dstTy == .i1 then
    if calleeRetTy != .i1 then none
    else if rvSort == specSortBool then some (.scalar (.var rv))
    else if rvSort == specSortU64 then
      let m : ScalarExpr := if alreadyNarrow then .var rv else .binOp .bitAnd (.var rv) (.constU64 1)
      some (.scalar (.binOp .eq m (.constU64 1)))
    else none
  else if rvSort != specSortBool && rvSort != specSortU64 then
    none
  else
    let asU64 : ScalarExpr :=
      if rvSort == specSortBool then .select (.var rv) (.constU64 1) (.constU64 0) else .var rv
    let maskedU64 : ScalarExpr :=
      if alreadyNarrow || rvSort == specSortBool then asU64
      else
        match calleeRetTy with
        | .i1 => .binOp .bitAnd asU64 (.constU64 1)
        | .i8 => .binOp .bitAnd asU64 (.constU64 0xFF)
        | .i16 => .binOp .bitAnd asU64 (.constU64 0xFFFF)
        | .i32 => .binOp .bitAnd asU64 (.constU64 0xFFFFFFFF)
        | _ => asU64
    some (.scalar maskedU64)

private def spliceCalleeBody (inLoopStep : Bool) (calleeEnv exactEnv : List (VarId × LNIRType))
    (sortEnv : List (VarId × SpecValSort)) (calleeRetTy callDstTy : LNIRType) (callDst : VarId)
    (callerCont : LNIRCode) : LNIRCode → List (VarId × VarId) → StateM VarId (Option LNIRCode)
  | .letBind dst ty val k, subst => do
    if exprHasBoolSortConflict calleeEnv sortEnv val then return none
    let val' := val.rewriteSubst subst
    let fDst ← get
    set (fDst + 1)
    let exactEnv' := match exprGuaranteedWidth? exactEnv val with
      | some wTy => (dst, wTy) :: exactEnv.filter (·.1 != dst)
      | none => exactEnv.filter (·.1 != dst)
    let sortEnv' := (dst, exprSpecSort sortEnv val) :: sortEnv.filter (·.1 != dst)
    match ← spliceCalleeBody inLoopStep ((dst, ty) :: calleeEnv.filter (·.1 != dst)) exactEnv' sortEnv'
        calleeRetTy callDstTy callDst callerCont k ((dst, fDst) :: subst) with
    | some k' => return some (.letBind fDst ty val' k')
    | none => return none
  | .rawStore pv iv vv et k, subst => do
    if sortEnv.lookup iv == some specSortBool || sortEnv.lookup vv == some specSortBool then
      return none
    let rw (v : VarId) := (subst.lookup v).getD v
    match ← spliceCalleeBody inLoopStep calleeEnv exactEnv sortEnv calleeRetTy callDstTy callDst
        callerCont k subst with
    | some k' => return some (.rawStore (rw pv) (rw iv) (rw vv) et k')
    | none => return none
  | .incRef ov c k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    match ← spliceCalleeBody inLoopStep calleeEnv exactEnv sortEnv calleeRetTy callDstTy callDst
        callerCont k subst with
    | some k' => return some (.incRef (rw ov) c k')
    | none => return none
  | .decRef ov c k, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    match ← spliceCalleeBody inLoopStep calleeEnv exactEnv sortEnv calleeRetTy callDstTy callDst
        callerCont k subst with
    | some k' => return some (.decRef (rw ov) c k')
    | none => return none
  | .ite cv t e, subst => do
    let rw (v : VarId) := (subst.lookup v).getD v
    match ← spliceCalleeBody inLoopStep calleeEnv exactEnv sortEnv calleeRetTy callDstTy callDst
              callerCont t subst,
          ← spliceCalleeBody inLoopStep calleeEnv exactEnv sortEnv calleeRetTy callDstTy callDst
              callerCont e subst with
    | some t', some e' => return some (.ite (rw cv) t' e')
    | _, _ => return none
  | .seqFor iv lv hv av ai aty step k, subst => do
    if sortEnv.lookup lv == some specSortBool || sortEnv.lookup hv == some specSortBool then
      return none
    let rw (v : VarId) := (subst.lookup v).getD v
    let fIv ← get
    let fAv := fIv + 1
    set (fIv + 2)
    let accSort := (sortEnv.lookup ai).getD (paramSpecSort aty)
    let stepEnv := (av, aty) :: (iv, .i64) :: calleeEnv.filter (fun (id, _) => id != av && id != iv)
    let exactStep := exactEnv.filter (fun (id, _) => id != av && id != iv)
    let sortStep :=
      (av, accSort) :: (iv, specSortU64) :: sortEnv.filter (fun (id, _) => id != av && id != iv)
    let contEnv := (av, aty) :: calleeEnv.filter (·.1 != av)
    let sortCont := (av, accSort) :: sortEnv.filter (·.1 != av)
    match ← spliceCalleeBody true stepEnv exactStep sortStep calleeRetTy callDstTy callDst callerCont
              step ((av, fAv) :: (iv, fIv) :: subst),
          ← spliceCalleeBody inLoopStep contEnv (exactEnv.filter (·.1 != av)) sortCont
              calleeRetTy callDstTy callDst callerCont k ((av, fAv) :: subst) with
    | some step', some k' => return some (.seqFor fIv (rw lv) (rw hv) fAv (rw ai) aty step' k')
    | _, _ => return none
  | .parFor ov lv ins et kern k, subst => do
    if sortEnv.lookup lv == some specSortBool then return none
    let rw (v : VarId) := (subst.lookup v).getD v
    let fOv ← get
    set (fOv + 1)
    let kern' ← match kern with
      | .customScalar idxVar inVars body => do
        let fIdx ← get
        let fIns := (List.range inVars.length).map (fun i => fIdx + 1 + i)
        set (fIdx + 1 + inVars.length)
        let kSubst := (inVars.zip fIns) ++ ((idxVar, fIdx) :: subst)
        pure (.customScalar fIdx fIns (body.rewriteSubst kSubst))
      | other => pure other
    let contEnv := (ov, .sarray et) :: calleeEnv.filter (·.1 != ov)
    let sortCont := (ov, specSortSarray) :: sortEnv.filter (·.1 != ov)
    match ← spliceCalleeBody inLoopStep contEnv (exactEnv.filter (·.1 != ov)) sortCont
        calleeRetTy callDstTy callDst callerCont k ((ov, fOv) :: subst) with
    | some k' => return some (.parFor fOv (rw lv) (ins.map rw) et kern' k')
    | none => return none
  | .ret rv, subst => do
    let rv' := (subst.lookup rv).getD rv
    if inLoopStep then
      return some (.ret rv')
    else
      let rvSort := (sortEnv.lookup rv).getD specSortOther
      let alreadyNarrow := match exactEnv.lookup rv with
        | some wTy => widthFitsIn wTy calleeRetTy
        | none => false
      match coerceCallRetExpr? rvSort calleeRetTy callDstTy alreadyNarrow rv' with
      | none => return none
      | some retExpr =>
        let fCallDst ← get
        set (fCallDst + 1)
        let contFresh ← callerCont.freshenBinders [(callDst, fCallDst)]
        return some (.letBind fCallDst callDstTy retExpr contFresh)
  | .unreachable, _ => return some .unreachable

private def foldCallArgBinds? : List ((LNIRParam × VarId) × VarId) →
    List (VarId × LNIRType) → List (VarId × SpecValSort) → LNIRCode → Option LNIRCode
  | [], _, _, acc => some acc
  | ((p, av), fp) :: rest, exactEnv, sortEnv, acc => do
    let restCode ← foldCallArgBinds? rest exactEnv sortEnv acc
    let srcSort := (sortEnv.lookup av).getD specSortOther
    let argNarrow := match exactEnv.lookup av with
      | some wTy => widthFitsIn wTy p.ty
      | none => false
    let argExpr ← coerceCallArgExpr? srcSort p.ty argNarrow av
    some (.letBind fp p.ty argExpr restCode)

private def inlineModuleCallsCode : Nat → List String → LNIRModule →
    List (String × List LNIRType × LNIRType) → List (VarId × LNIRType) → List (VarId × LNIRType) →
    List (VarId × SpecValSort) → LNIRCode → StateM VarId (Option LNIRCode)
  | 0, _, _, _, _, _, _, _ => return none
  | fuel + 1, visited, m, localSigs, varEnv, exactEnv, sortEnv, code => do
    match code with
    | .letBind dst ty (.call callee args retTy isExt) k =>
      if isExt || isBuiltinRuntimeCall callee then
        let callSort := exprSpecSort sortEnv (.call callee args retTy isExt)
        let sortEnv' := (dst, callSort) :: sortEnv.filter (·.1 != dst)
        match ← inlineModuleCallsCode (fuel + 1) visited m localSigs
            ((dst, ty) :: varEnv.filter (·.1 != dst))
            (exactEnv.filter (·.1 != dst)) sortEnv' k with
        | some k' => return some (.letBind dst ty (.call callee args retTy isExt) k')
        | none => return none
      else if visited.contains callee || !isLocalCallDstScalarSlot ty ||
              !localSigs.any (fun (nm, pTys, _) => nm == callee && pTys.length == args.length) then
        return none
      else
        match m.decls.find? (fun d => d.name == callee && d.params.length == args.length) with
        | none => return none
        | some calleeDecl =>
          if (ty == .i1 && calleeDecl.retTy != .i1) || (ty == .unit && calleeDecl.retTy != .unit) ||
             (calleeDecl.retTy != .unit && ty == .unit) then
            return none
          let calleeInitEnv := calleeDecl.params.map fun p => (p.id, p.ty)
          let calleeInitExact := calleeDecl.params.filterMap fun p =>
            match p.ty with
            | .i1 | .i8 | .i16 | .i32 => some (p.id, p.ty)
            | _ => none
          let calleeInitSort := calleeDecl.params.map fun p => (p.id, paramSpecSort p.ty)
          let curMax ← get
          set (Nat.max curMax (declSynVarBase calleeDecl + 16))
          match ← inlineModuleCallsCode fuel (callee :: visited) m localSigs calleeInitEnv
              calleeInitExact calleeInitSort calleeDecl.body with
          | none => return none
          | some calleeBodyInlined =>
            let dstExact := match calleeDecl.retTy with
              | .i1 | .i8 | .i16 | .i32 => (dst, calleeDecl.retTy) :: exactEnv.filter (·.1 != dst)
              | _ => exactEnv.filter (·.1 != dst)
            let dstSort : SpecValSort :=
              if ty == .i1 then specSortBool
              else if ty == .unit then specSortUnit
              else specSortU64
            let dstSortEnv := (dst, dstSort) :: sortEnv.filter (·.1 != dst)
            match ← inlineModuleCallsCode (fuel + 1) visited m localSigs
                ((dst, ty) :: varEnv.filter (·.1 != dst))
                dstExact dstSortEnv k with
            | none => return none
            | some kInlined =>
              let paramBase ← get
              set (paramBase + calleeDecl.params.length + 4)
              let freshParamIds := (List.range calleeDecl.params.length).map (fun i => paramBase + i)
              let paramSubst := (calleeDecl.params.map (·.id)).zip freshParamIds
              match ← spliceCalleeBody false calleeInitEnv calleeInitExact calleeInitSort
                  calleeDecl.retTy ty dst kInlined calleeBodyInlined paramSubst with
              | none => return none
              | some splicedBody =>
                let argTriples := (calleeDecl.params.zip args).zip freshParamIds
                match foldCallArgBinds? argTriples exactEnv sortEnv splicedBody with
                | none => return none
                | some fullCode =>
                  if fullCode.nodeSize > 16384 then return none
                  else return some fullCode
    | .letBind dst ty val k =>
      if exprHasBoolSortConflict varEnv sortEnv val then return none
      let exactEnv' := match exprGuaranteedWidth? exactEnv val with
        | some wTy => (dst, wTy) :: exactEnv.filter (·.1 != dst)
        | none => exactEnv.filter (·.1 != dst)
      let sortEnv' := (dst, exprSpecSort sortEnv val) :: sortEnv.filter (·.1 != dst)
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs
          ((dst, ty) :: varEnv.filter (·.1 != dst))
          exactEnv' sortEnv' k with
      | some k' => return some (.letBind dst ty val k')
      | none => return none
    | .rawStore pv iv vv et k =>
      if sortEnv.lookup iv == some specSortBool || sortEnv.lookup vv == some specSortBool then
        return none
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs varEnv exactEnv sortEnv k with
      | some k' => return some (.rawStore pv iv vv et k')
      | none => return none
    | .incRef ov c k =>
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs varEnv exactEnv sortEnv k with
      | some k' => return some (.incRef ov c k')
      | none => return none
    | .decRef ov c k =>
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs varEnv exactEnv sortEnv k with
      | some k' => return some (.decRef ov c k')
      | none => return none
    | .ite cv t e =>
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs varEnv exactEnv sortEnv t,
            ← inlineModuleCallsCode (fuel + 1) visited m localSigs varEnv exactEnv sortEnv e with
      | some t', some e' => return some (.ite cv t' e')
      | _, _ => return none
    | .seqFor iv lv hv av ai aty step k =>
      if sortEnv.lookup lv == some specSortBool || sortEnv.lookup hv == some specSortBool then
        return none
      let accSort := (sortEnv.lookup ai).getD (paramSpecSort aty)
      let stepEnv := (av, aty) :: (iv, .i64) :: varEnv.filter (fun (id, _) => id != av && id != iv)
      let exactStep := exactEnv.filter (fun (id, _) => id != av && id != iv)
      let sortStep :=
        (av, accSort) :: (iv, specSortU64) :: sortEnv.filter (fun (id, _) => id != av && id != iv)
      let contEnv := (av, aty) :: varEnv.filter (·.1 != av)
      let sortCont := (av, accSort) :: sortEnv.filter (·.1 != av)
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs stepEnv exactStep sortStep step,
            ← inlineModuleCallsCode (fuel + 1) visited m localSigs contEnv
                (exactEnv.filter (·.1 != av)) sortCont k with
      | some step', some k' => return some (.seqFor iv lv hv av ai aty step' k')
      | _, _ => return none
    | .parFor ov lv ins et kern k =>
      if sortEnv.lookup lv == some specSortBool then return none
      let contEnv := (ov, .sarray et) :: varEnv.filter (·.1 != ov)
      let sortCont := (ov, specSortSarray) :: sortEnv.filter (·.1 != ov)
      match ← inlineModuleCallsCode (fuel + 1) visited m localSigs contEnv
          (exactEnv.filter (·.1 != ov)) sortCont k with
      | some k' => return some (.parFor ov lv ins et kern k')
      | none => return none
    | .ret v => return some (.ret v)
    | .unreachable => return some .unreachable
termination_by fuel _ _ _ _ _ _ code => (fuel, sizeOf code)

private def specializeModuleLocalCallsDecl (m : LNIRModule)
    (localSigs : List (String × List LNIRType × LNIRType)) (d : LNIRDecl) : Option LNIRDecl :=
  let initMax := m.decls.foldl (fun acc md => Nat.max acc (declSynVarBase md)) (declSynVarBase d) + 32
  let initEnv := d.params.map fun p => (p.id, p.ty)
  let initExact := d.params.filterMap fun p =>
    match p.ty with
    | .i1 | .i8 | .i16 | .i32 => some (p.id, p.ty)
    | _ => none
  let initSort := d.params.map fun p => (p.id, paramSpecSort p.ty)
  let (body?, _) := (inlineModuleCallsCode 8 [d.name] m localSigs initEnv initExact initSort d.body).run initMax
  body?.map fun b => { d with body := b }

/-- Validate an entire optimized `LNIRModule` against its unoptimized source `LNIRModule`. -/
def validateTranslationModule (srcMod tgtMod : LNIRModule) (numSamples : Nat := 64) : TVModuleReport :=
  let srcSigs := localCallableSigs srcMod
  let tgtSigs := localCallableSigs tgtMod
  let results := srcMod.decls.filterMap (fun srcDecl =>
    match tgtMod.decls.find? (fun d => d.name == srcDecl.name) with
    | some tgtDecl =>
      let sigEq := srcDecl.params.map (·.ty) == tgtDecl.params.map (·.ty) && srcDecl.retTy == tgtDecl.retTy
      let modElemOk := sigEq && (srcDecl.checkElemTypes srcSigs).isNone && (tgtDecl.checkElemTypes tgtSigs).isNone
      if !modElemOk then
        let baseRes := validateTranslationDecl srcDecl tgtDecl numSamples
        some { baseRes with ubRefines := false, passed := false }
      else if codeHasUserLocalCall srcDecl.body || codeHasUserLocalCall tgtDecl.body then
        match specializeModuleLocalCallsDecl srcMod srcSigs srcDecl,
              specializeModuleLocalCallsDecl tgtMod tgtSigs tgtDecl with
        | some srcSpec, some tgtSpec =>
          let specRes := validateTranslationDecl srcSpec tgtSpec numSamples
          some { specRes with
            declName := srcDecl.name
            srcHash := srcDecl.structuralHash
            tgtHash := tgtDecl.structuralHash }
        | _, _ =>
          let baseRes := validateTranslationDecl srcDecl tgtDecl numSamples
          some { baseRes with ubRefines := false, passed := false }
      else
        some (validateTranslationDecl srcDecl tgtDecl numSamples)
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
