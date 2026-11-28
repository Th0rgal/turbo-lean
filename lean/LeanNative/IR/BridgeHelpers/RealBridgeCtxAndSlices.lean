import LeanNative.IR.BridgeHelpers.HeapAndConstructors

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-- Count AST nodes in `Lean.Compiler.LCNF.Code .impure` to size fuel generously for `RealLCNFBridge`. -/
partial def codeAstFuel (code : Lean.Compiler.LCNF.Code .impure) : Nat :=
  match code with
  | .let _ k | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeAstFuel k + 2
  | .fun d k _ => codeAstFuel d.value + codeAstFuel k + 4
  | .jp d k =>
    let dFuel := codeAstFuel d.value + 4
    let kFuel := codeAstFuel k + 4
    dFuel * kFuel + dFuel + kFuel + 8
  | .cases c =>
    c.alts.foldl (fun acc alt => acc + codeAstFuel alt.getCode + 4) (c.alts.size + 4)
  | .jmp _ _ | .return _ | .unreach _ => 4

private def collectArgFVarsImpure (acc : List Lean.FVarId) : Lean.Compiler.LCNF.Arg .impure → List Lean.FVarId
  | .fvar id => if acc.contains id then acc else acc ++ [id]
  | _ => acc

/-- Collect operand `FVarId`s referenced in `LetValue .impure` (for standalone `BridgeM` callers). -/
def collectLetValueFVarsImpure (acc : List Lean.FVarId) (lv : Lean.Compiler.LCNF.LetValue .impure) : List Lean.FVarId :=
  let add (xs : List Lean.FVarId) (id : Lean.FVarId) := if xs.contains id then xs else xs ++ [id]
  match lv with
  | .lit _ | .erased | .pap .. => acc
  | .fvar id args => args.foldl collectArgFVarsImpure (add acc id)
  | .ctor _ args _ | .fap _ args _ => args.foldl collectArgFVarsImpure acc
  | .reuse slot _ _ args _ => args.foldl collectArgFVarsImpure (add acc slot)
  | .oproj _ id _ | .uproj _ id _ | .sproj _ _ id _ | .box _ id _ | .unbox id _
  | .isShared id _ | .reset _ id _ => add acc id

/-- Collect free operand `FVarId`s in `Code .impure` (excluding `.jmp` join-point targets and locally bound vars). -/
partial def collectFreeCodeFVarsImpure (bound : Std.HashSet Lean.FVarId) (acc : List Lean.FVarId)
    (code : Lean.Compiler.LCNF.Code .impure) : List Lean.FVarId :=
  let addIfFree (xs : List Lean.FVarId) (id : Lean.FVarId) :=
    if bound.contains id || xs.contains id then xs else xs ++ [id]
  let addArg (xs : List Lean.FVarId) : Lean.Compiler.LCNF.Arg .impure → List Lean.FVarId
    | .fvar id => addIfFree xs id
    | _ => xs
  match code with
  | .let decl k =>
    let acc1 := (collectLetValueFVarsImpure [] decl.value).foldl addIfFree acc
    collectFreeCodeFVarsImpure (bound.insert decl.fvarId) acc1 k
  | .jp decl k =>
    let boundJp := decl.params.foldl (fun s p => s.insert p.fvarId) (bound.insert decl.fvarId)
    let acc1 := collectFreeCodeFVarsImpure boundJp acc decl.value
    collectFreeCodeFVarsImpure (bound.insert decl.fvarId) acc1 k
  | .fun decl k _ =>
    let boundFn := decl.params.foldl (fun s p => s.insert p.fvarId) (bound.insert decl.fvarId)
    let acc1 := collectFreeCodeFVarsImpure boundFn acc decl.value
    collectFreeCodeFVarsImpure (bound.insert decl.fvarId) acc1 k
  | .jmp _ args => args.foldl addArg acc
  | .inc id _ _ _ k _ | .dec id _ _ _ _ k _ | .del id k _ | .setTag id _ k _ =>
    collectFreeCodeFVarsImpure bound (addIfFree acc id) k
  | .oset id _ y k _ =>
    collectFreeCodeFVarsImpure bound (addArg (addIfFree acc id) y) k
  | .uset id _ y k _ | .sset id _ _ y _ k _ =>
    collectFreeCodeFVarsImpure bound (addIfFree (addIfFree acc id) y) k
  | .cases c =>
    let acc1 := addIfFree acc c.discr
    c.alts.foldl (fun a alt =>
      let bAlt := match alt with
        | .alt _ ps _ _ => ps.foldl (fun s p => s.insert p.fvarId) bound
        | _ => bound
      collectFreeCodeFVarsImpure bAlt a alt.getCode) acc1
  | .return id => addIfFree acc id
  | .unreach _ => acc

private partial def collectCodeTypeExprs (acc : List Lean.Expr) (code : Lean.Compiler.LCNF.Code .impure) : List Lean.Expr :=
  let addExpr (xs : List Lean.Expr) (e : Lean.Expr) := if xs.contains e then xs else xs ++ [e]
  match code with
  | .let decl k => collectCodeTypeExprs (addExpr acc decl.type) k
  | .jp decl k | .fun decl k _ =>
    let acc1 := decl.params.foldl (fun a p => addExpr a p.type) (addExpr acc decl.type)
    collectCodeTypeExprs (collectCodeTypeExprs acc1 decl.value) k
  | .cases c =>
    c.alts.foldl (fun a alt =>
      let a1 := match alt with
        | .alt _ ps _ _ => ps.foldl (fun s p => addExpr s p.type) a
        | _ => a
      collectCodeTypeExprs a1 alt.getCode) (addExpr acc c.resultType)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    collectCodeTypeExprs acc k
  | .jmp _ _ | .return _ | .unreach _ => acc

private def collectLetValueCtorAndCalleeNames (ctors callees : List Lean.Name)
    (lv : Lean.Compiler.LCNF.LetValue .impure) : List Lean.Name × List Lean.Name :=
  let add (xs : List Lean.Name) (n : Lean.Name) := if xs.contains n then xs else xs ++ [n]
  match lv with
  | .ctor info _ _ | .reuse _ info _ _ _ => (add ctors info.name, callees)
  | .fap fn _ _ | .pap fn _ _ => (ctors, add callees fn)
  | _ => (ctors, callees)

private partial def collectCodeCtorAndCalleeNames (ctors callees : List Lean.Name)
    (code : Lean.Compiler.LCNF.Code .impure) : List Lean.Name × List Lean.Name :=
  let add (xs : List Lean.Name) (n : Lean.Name) := if xs.contains n then xs else xs ++ [n]
  match code with
  | .let decl k =>
    let (c1, f1) := collectLetValueCtorAndCalleeNames ctors callees decl.value
    collectCodeCtorAndCalleeNames c1 f1 k
  | .jp decl k | .fun decl k _ =>
    let (c1, f1) := collectCodeCtorAndCalleeNames ctors callees decl.value
    collectCodeCtorAndCalleeNames c1 f1 k
  | .cases c =>
    c.alts.foldl (fun (cs, fs) alt =>
      let cs' := match alt with
        | .ctorAlt info _ _ => add cs info.name
        | .alt cname _ _ _ => add cs cname
        | .default _ => cs
      collectCodeCtorAndCalleeNames cs' fs alt.getCode) (ctors, callees)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    collectCodeCtorAndCalleeNames ctors callees k
  | .jmp _ _ | .return _ | .unreach _ => (ctors, callees)

private def mkFreshEmbFVarId : StateM Nat Lean.FVarId := do
  let idx ← get
  set (idx + 1)
  return ⟨Lean.Name.num `_ln_emb_getb idx⟩

/-- Collect `(getBangIdxUses, otherUses)` across `Code .impure` so `normalizeEmbeddedSliceGetBang`
    rewrites `USize.toNat` / `.lit (.nat m)` bindings iff their result `FVarId` is consumed
    exclusively as the index operand of `ByteArray.get!` (plus RC `inc`/`dec`/`del` cleanup). -/
private partial def collectGetBangIdxUsage
    (acc : Lean.FVarIdSet × Lean.FVarIdSet) :
    Lean.Compiler.LCNF.Code .impure → Lean.FVarIdSet × Lean.FVarIdSet
  | .let decl k =>
    let acc' := match decl.value with
      | .fap fn #[.fvar arrFVar, .fvar idxFVar] _ =>
        if fn == ``ByteArray.get! then
          (acc.1.insert idxFVar, acc.2.insert arrFVar)
        else
          (acc.1, (collectLetValueFVarsImpure [] decl.value).foldl (·.insert ·) acc.2)
      | lv =>
        (acc.1, (collectLetValueFVarsImpure [] lv).foldl (·.insert ·) acc.2)
    collectGetBangIdxUsage acc' k
  | .jp decl k =>
    collectGetBangIdxUsage (collectGetBangIdxUsage acc decl.value) k
  | .fun decl k _ =>
    collectGetBangIdxUsage (collectGetBangIdxUsage acc decl.value) k
  | .cases c =>
    let acc1 := (acc.1, acc.2.insert c.discr)
    c.alts.foldl (fun a alt => collectGetBangIdxUsage a alt.getCode) acc1
  | .jmp fvarId args =>
    let acc1 := (acc.1, acc.2.insert fvarId)
    args.foldl (fun a arg => match arg with | .fvar x => (a.1, a.2.insert x) | _ => a) acc1
  | .return fvarId => (acc.1, acc.2.insert fvarId)
  | .oset f _ y k _ =>
    let o2 := match y with | .fvar yf => (acc.2.insert f).insert yf | _ => acc.2.insert f
    collectGetBangIdxUsage (acc.1, o2) k
  | .uset f _ y k _ | .sset f _ _ y _ k _ =>
    collectGetBangIdxUsage (acc.1, (acc.2.insert f).insert y) k
  | .setTag f _ k _ =>
    collectGetBangIdxUsage (acc.1, acc.2.insert f) k
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ =>
    collectGetBangIdxUsage acc k
  | .unreach _ => acc

/-- On freestanding embedded targets (`arch.isFreestandingEmbedded`), rewrite impure LCNF
    `let n := USize.toNat i` / small `.lit (.nat m)` feeds into `ByteArray.get! arr n` so
    `ByteArray.get!` lowers to a bounds-guarded zero-copy `ByteArray.usize` + `ByteArray.uget`
    without heap `Nat` allocation or panicking runtime calls. -/
partial def normalizeEmbeddedSliceGetBangAux (eligibleNatIdx : Lean.FVarIdSet)
    (u2n : Std.HashMap Lean.FVarId Lean.FVarId)
    (natFVars : Lean.FVarIdSet) :
    Lean.Compiler.LCNF.Code .impure → StateM Nat (Lean.Compiler.LCNF.Code .impure)
  | .let decl k => do
    match decl.value with
    | .fap fn #[.fvar uFVar] _ =>
      if fn == ``USize.toNat && eligibleNatIdx.contains decl.fvarId then
        normalizeEmbeddedSliceGetBangAux eligibleNatIdx (u2n.insert decl.fvarId uFVar) (natFVars.insert decl.fvarId) k
      else
        return .let decl (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k)
    | .lit (.nat m) =>
      if (decl.type == ImpureType.tobject || decl.type == ImpureType.tagged) &&
         eligibleNatIdx.contains decl.fvarId && m < 0x100000000 then
        let uFVar ← mkFreshEmbFVarId
        let uDecl : Lean.Compiler.LCNF.LetDecl .impure := {
          fvarId := uFVar
          binderName := decl.binderName
          type := ImpureType.usize
          value := .lit (.usize m.toUInt64)
        }
        let k' ← normalizeEmbeddedSliceGetBangAux eligibleNatIdx (u2n.insert decl.fvarId uFVar) (natFVars.insert decl.fvarId) k
        return .let uDecl k'
      else
        return .let decl (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k)
    | .fap fn #[.fvar arrFVar, .fvar idxNatFVar] himp =>
      if fn == ``ByteArray.get! then
        match u2n[idxNatFVar]? with
        | some uIdxFVar =>
          let k' ← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k
          let lenFVar ← mkFreshEmbFVarId
          let cmpFVar ← mkFreshEmbFVarId
          let jpFVar ← mkFreshEmbFVarId
          let gotFVar ← mkFreshEmbFVarId
          let zeroFVar ← mkFreshEmbFVarId
          let jpParam : Lean.Compiler.LCNF.Param .impure := {
            fvarId := decl.fvarId, binderName := decl.binderName, type := ImpureType.uint8, borrow := false
          }
          let jpDecl : Lean.Compiler.LCNF.FunDecl .impure :=
            Lean.Compiler.LCNF.FunDecl.mk jpFVar `_jp_getb #[jpParam] ImpureType.uint8 k'
          let lenDecl : Lean.Compiler.LCNF.LetDecl .impure := {
            fvarId := lenFVar, binderName := `_len, type := ImpureType.usize,
            value := .fap ``ByteArray.usize #[.fvar arrFVar] himp
          }
          let cmpDecl : Lean.Compiler.LCNF.LetDecl .impure := {
            fvarId := cmpFVar, binderName := `_inb, type := ImpureType.uint8,
            value := .fap ``USize.decLt #[.fvar uIdxFVar, .fvar lenFVar] himp
          }
          let gotDecl : Lean.Compiler.LCNF.LetDecl .impure := {
            fvarId := gotFVar, binderName := `_b, type := ImpureType.uint8,
            value := .fap ``ByteArray.uget #[.fvar arrFVar, .fvar uIdxFVar, .erased] himp
          }
          let zeroDecl : Lean.Compiler.LCNF.LetDecl .impure := {
            fvarId := zeroFVar, binderName := `_z, type := ImpureType.uint8,
            value := .lit (.uint8 0)
          }
          let casesNode : Lean.Compiler.LCNF.Cases .impure :=
            Lean.Compiler.LCNF.Cases.mk ``Bool ImpureType.uint8 cmpFVar #[
              Alt.ctorAlt { name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 }
                (.let zeroDecl (.jmp jpFVar #[.fvar zeroFVar])) himp,
              Alt.ctorAlt { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 }
                (.let gotDecl (.jmp jpFVar #[.fvar gotFVar])) himp
            ]
          return .jp jpDecl (.let lenDecl (.let cmpDecl (.cases casesNode)))
        | none =>
          return .let decl (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k)
      else
        return .let decl (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k)
    | _ =>
      return .let decl (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k)
  | .jp decl k => do
    let val' ← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars decl.value
    let k' ← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k
    return .jp (Lean.Compiler.LCNF.FunDecl.mk decl.fvarId decl.binderName decl.params decl.type val') k'
  | .cases c => do
    let alts' : Array (Lean.Compiler.LCNF.Alt .impure) ← c.alts.mapM fun alt => do
      match alt with
      | .ctorAlt info code h => return Alt.ctorAlt info (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars code) h
      | .default code => return Alt.default (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars code)
      | .alt _ _ _ h => nomatch h
    return .cases (c.updateAlts alts')
  | .inc fvarId n check persistent k h => do
    if natFVars.contains fvarId then normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k
    else return .inc fvarId n check persistent (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .dec fvarId n check persistent del k h => do
    if natFVars.contains fvarId then normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k
    else return .dec fvarId n check persistent del (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .del fvarId k h => do
    if natFVars.contains fvarId then normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k
    else return .del fvarId (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .oset fvarId idx y k h => return .oset fvarId idx y (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .uset fvarId idx y k h => return .uset fvarId idx y (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .sset fvarId idx offset y ty k h => return .sset fvarId idx offset y ty (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .setTag fvarId cidx k h => return .setTag fvarId cidx (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | .fun d k h => return .fun d (← normalizeEmbeddedSliceGetBangAux eligibleNatIdx u2n natFVars k) h
  | code => return code

def normalizeEmbeddedSliceGetBang (u2n : Std.HashMap Lean.FVarId Lean.FVarId)
    (natFVars : Lean.FVarIdSet) (code : Lean.Compiler.LCNF.Code .impure) :
    Lean.CoreM (Lean.Compiler.LCNF.Code .impure) := do
  let (gbUses, otherUses) := collectGetBangIdxUsage ({}, {}) code
  let eligible := gbUses.foldl (fun acc f => if otherUses.contains f then acc else acc.insert f) ({} : Lean.FVarIdSet)
  return (normalizeEmbeddedSliceGetBangAux eligible u2n natFVars code).run' 0

/-- Pre-validate `LetDecl .impure` binder types recursively before delegating to `RealLCNFBridge`. -/
partial def checkImpureLetTypesM (code : Lean.Compiler.LCNF.Code .impure) : BridgeM Unit := do
  match code with
  | .let decl k =>
    let allowHeap := (← get).allowStage1DHeap
    let hasStage1DScalarLayout := match decl.value with
      | .ctor info _ _ => allowHeap && (info.usize > 0 || info.ssize > 0)
      | _ => false
    if !hasStage1DScalarLayout then
      let rawDeclTy ← lowerBridgeType decl.type
      if rawDeclTy != .unit then checkBridgeType s!"let binding `{decl.binderName}`" decl.type rawDeclTy true
    checkImpureLetTypesM k
  | .jp decl k =>
    let jpTy ← lowerBridgeType decl.type
    checkBridgeType "join-point result" decl.type jpTy true
    for p in decl.params do
      let pTy ← lowerBridgeType p.type
      checkBridgeType "parameter" p.type pTy true
    checkImpureLetTypesM decl.value
    checkImpureLetTypesM k
  | .cases c =>
    for alt in c.alts do
      checkImpureLetTypesM alt.getCode
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    checkImpureLetTypesM k
  | .fun _ _ _ | .jmp _ _ | .return _ | .unreach _ => pure ()

/-- Build a pure `RealBridgeCtx` from `Lean.Environment` and `BridgeState` for `RealLCNFBridge`. -/
def buildRealBridgeCtxM (typeExprs : List Lean.Expr) (ctorSeeds calleeSeeds : List Lean.Name)
    (paramTypeMap : List (Lean.FVarId × LNIRType) := [])
    (knownFVarCtors : List (Lean.FVarId × Lean.Name) := []) : BridgeM RealLCNFBridge.RealBridgeCtx := do
  let env ← getEnv
  let st ← get
  let mut allCtors : List Lean.Name := []
  let mut ctorSiblings : List (Lean.Name × Nat × Lean.Name) := []
  for seed in ctorSeeds do
    if !allCtors.contains seed then allCtors := allCtors ++ [seed]
    if let some (.ctorInfo cval) := env.find? seed then
      if let some (.inductInfo ival) := env.find? cval.induct then
        for sib in ival.ctors do
          if !allCtors.contains sib then allCtors := allCtors ++ [sib]
        for (sib, idx) in ival.ctors.zipIdx do
          if !ctorSiblings.any (fun (c, i, _) => c == seed && i == idx) then
            ctorSiblings := ctorSiblings ++ [(seed, idx, sib)]
  let mut ctorLayouts : List (Lean.Name × RcCtorLayoutSpec) := []
  let mut nullaryCtors : List (Lean.Name × Nat) := []
  let mut tupleStructCtors : List (Lean.Name × Nat) := []
  for cname in allCtors do
    if let some (.ctorInfo cval) := env.find? cname then
      if cval.numFields == 0 then
        nullaryCtors := nullaryCtors ++ [(cname, cval.cidx)]
      if let some (.inductInfo ival) := env.find? cval.induct then
        if ival.ctors.length == 1 && !ival.isRec && ival.numIndices == 0 && cval.numFields ≥ 1 && cval.numFields ≤ 8 then
          tupleStructCtors := tupleStructCtors ++ [(cname, cval.numFields)]
      if st.allowStage1DHeap && cval.numFields ≥ 1 && cval.numFields ≤ 8 then
        if let some spec ← (try some <$> getRcCtorLayoutSpecM cname catch _ => pure none) then
          ctorLayouts := ctorLayouts ++ [(cname, spec)]
  let mut typeOverrides : List (Lean.Expr × LNIRType) := []
  for e in typeExprs do
    let tyEnv := lowerImpureType e (some env)
    let tyPure := RealLCNFBridge.lowerGroundImpureType e
    if tyEnv != tyPure then
      typeOverrides := typeOverrides ++ [(e, tyEnv)]
  let localNames := (st.localDeclNames.push st.selfDeclName).toList.filter (· != .anonymous)
  let mut gfSimdIntrinsics : List (Lean.Name × BinOp) := []
  for fn in calleeSeeds do
    if let some op := trustedGfSimdIntrinsicOp env fn then
      if !gfSimdIntrinsics.any (fun (n, _) => n == fn) then
        gfSimdIntrinsics := gfSimdIntrinsics ++ [(fn, op)]
  let mut localCallees : List (Lean.Name × String) := []
  for fn in localNames do
    if !Lean.isExtern env fn &&
       (RealLCNFBridge.lowerCanonicalIntrinsicPure? fn [0, 1] .i64 [.i64, .i64] true st.arch gfSimdIntrinsics).isNone &&
       (trustedGfSimdIntrinsicOp env fn).isNone then
      if !localCallees.any (fun (n, _) => n == fn) then
        localCallees := localCallees ++ [(fn, mangleDeclNameInEnv env fn)]
  return {
    arch := st.arch
    allowStage1DHeap := st.allowStage1DHeap
    ctorLayouts := ctorLayouts
    nullaryCtors := nullaryCtors
    tupleStructCtors := tupleStructCtors
    ctorSiblings := ctorSiblings
    typeOverrides := typeOverrides
    paramTypeMap := paramTypeMap
    localCallees := localCallees
    gfSimdIntrinsics := gfSimdIntrinsics
    knownFVarCtors := knownFVarCtors
  }

partial def pureCodeAstFuel : Lean.Compiler.LCNF.Code .pure → Nat
  | .let _ k => 1 + pureCodeAstFuel k
  | .fun d k _ | .jp d k => 1 + pureCodeAstFuel d.value + pureCodeAstFuel k
  | .cases c => 1 + c.alts.foldl (fun acc a => acc + pureCodeAstFuel a.getCode) 0
  | .return _ | .jmp .. | .unreach _ => 1

def isWordFactTy : LNIRType → Bool
  | .i64 | .usize => true
  | _ => false

def isRawPtrFactTy : LNIRType → Bool
  | .rawPtr _ => true
  | _ => false

def isExclFactTy : LNIRType → Bool
  | .sarray _ | .objPtr => true
  | _ => false

def factVarsInScope (varTys : List (VarId × LNIRType)) : RetainedFact → Bool
  | .idxLt i n =>
    match varTys.lookup i, varTys.lookup n with
    | some ti, some tn => isWordFactTy ti && isWordFactTy tn
    | _, _ => false
  | .noOverflowAdd a b _ _ | .noOverflowSub a b _ _ | .noOverflowMul a b _ _ =>
    match varTys.lookup a, varTys.lookup b with
    | some ta, some tb => isWordFactTy ta && isWordFactTy tb
    | _, _ => false
  | .alignedPtr p _ =>
    match varTys.lookup p with
    | some tp => isRawPtrFactTy tp || isWordFactTy tp
    | none => false
  | .disjointSlices a b la lb =>
    match varTys.lookup a, varTys.lookup b, varTys.lookup la, varTys.lookup lb with
    | some ta, some tb, some tla, some tlb =>
      isRawPtrFactTy ta && isRawPtrFactTy tb && isWordFactTy tla && isWordFactTy tlb
    | _, _, _, _ => false
  | .exclusiveObj o =>
    match varTys.lookup o with
    | some to => isExclFactTy to
    | none => false

partial def collectDeclVarTys (acc : List (VarId × LNIRType)) : LNIRCode → List (VarId × LNIRType)
  | .letBind dst ty _ k => collectDeclVarTys ((dst, ty) :: acc) k
  | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k => collectDeclVarTys acc k
  | .ite _ t e => collectDeclVarTys (collectDeclVarTys acc t) e
  | .seqFor idx _ _ accV _ accTy body k =>
    collectDeclVarTys (collectDeclVarTys ((idx, .i64) :: (accV, accTy) :: acc) body) k
  | .parFor out _ _ elemTy _ k => collectDeclVarTys ((out, .sarray elemTy) :: acc) k
  | .ret _ | .unreachable => acc

def attachBaseDeclFactsM (declName : Lean.Name) (d : LNIRDecl) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let paramVars := d.params.map (·.id)
  let paramTys := d.params.map fun p => (p.id, p.ty)
  let nextVar := paramVars.foldl max 0 + 64
  let sigFacts := match env.find? declName with
    | none => []
    | some cinfo =>
      (LeanNative.Frontend.ProofRetention.retainedForallParamFacts paramVars nextVar cinfo.type).filter
        (factVarsInScope paramTys)
  let baseFacts ← match ← Lean.Compiler.LCNF.getBaseDecl? declName with
    | none => pure []
    | some baseDecl =>
      let paramSeed :=
        if baseDecl.params.size == d.params.length then
          (baseDecl.params.toList.zip d.params).map fun (bp, lp) => (bp.fvarId, lp.id)
        else []
      if paramSeed.isEmpty then pure []
      else
        let fuel := baseDecl.params.size +
          (match baseDecl.value with | .code c => pureCodeAstFuel c | .extern _ => 0) + 128
        let rawFacts := LeanNative.Frontend.ProofRetention.retainedPureDeclFactsWithSeed
          fuel paramSeed nextVar baseDecl
        pure (rawFacts.filter (factVarsInScope paramTys))
  let merged := (sigFacts ++ baseFacts).foldl LeanNative.IR.consFact d.retainedFacts
  return { d with retainedFacts := merged }

/-- Delegate `Decl .impure` lowering directly to `RealLCNFBridge.lowerRealLCNFDecl` (backed by `lowerRealLCNFDecl_sound`). -/
def ingestImpureDeclViaReal (decl : Lean.Compiler.LCNF.Decl .impure)
    (localDeclNames : Array Lean.Name := #[]) (arch : TargetArch := .x86_64)
    (allowRcAdt : Bool := false) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  if ← declUsesSignedScalarTransitively decl then
    Lean.throwError s!"[lean-native] Unsupported signed integer type (`Int*` / `ISize`) in `{decl.name}`"
  let metaInfo := getLCNFDeclMetadata env decl.name
  if metaInfo.isExtern then
    Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
  let isExported := (Lean.getExportNameFor? env decl.name).isSome
  checkEnvConstSignatureM env decl.name arch isExported
  let isStage1DHeap := allowRcAdt && !isExported && declQualifiesForStage1DHeap env decl.name arch
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol, isSimpleGround := metaInfo.isSimpleGround,
    selfDeclName := decl.name, localDeclNames := localDeclNames, arch := arch,
    allowStage1DHeap := isStage1DHeap }
  let action : BridgeM LNIRDecl := do
    let envParamTys ← collectDeclExplicitParamTypesM env decl.name
    let mut paramTypeMap : List (Lean.FVarId × LNIRType) := []
    let mut paramTypesList : List LNIRType := []
    let mut paramIds : List VarId := []
    let mut embeddedExportSliceFVars : Lean.FVarIdSet := {}
    let mut normParams : Array (Lean.Compiler.LCNF.Param .impure) := #[]
    let mut pIdx : Nat := 0
    for p in decl.params do
      let rawPTy ← lowerBridgeType p.type
      let pTy :=
        if !isStage1DHeap && (rawPTy == .objPtr || rawPTy == .taggedPtr) then
          match envParamTys[pIdx]? with
          | some (.tuple fs) => .tuple fs
          | some (.sarray .i8) => .sarray .i8
          | some (.sarray .f64) => .sarray .f64
          | _ => rawPTy
        else rawPTy
      let forceEmbeddedBorrow := isSupportedSliceType pTy && isExported && arch.isFreestandingEmbedded
      if isSupportedSliceType pTy && !p.borrow && !forceEmbeddedBorrow then
        Lean.throwError s!"[lean-native] Non-borrowed slice parameter `{p.binderName}` in `{decl.name}` requires borrow (@&)"
      if forceEmbeddedBorrow then
        embeddedExportSliceFVars := embeddedExportSliceFVars.insert p.fvarId
      normParams := normParams.push (if forceEmbeddedBorrow then { p with borrow := true } else p)
      checkBridgeType s!"parameter `{p.binderName}` of `{decl.name}`" p.type pTy true (!isExported || arch.isFreestandingEmbedded)
      let vid ← internFVar p.fvarId pTy true
      paramTypeMap := paramTypeMap ++ [(p.fvarId, pTy)]
      paramTypesList := paramTypesList ++ [pTy]
      paramIds := paramIds ++ [vid]
      pIdx := pIdx + 1
    let retTy ← lowerBridgeType decl.type
    checkBridgeType s!"return type of `{decl.name}`" decl.type retTy true
    match decl.value with
    | .extern _ =>
      Lean.throwError s!"[lean-native] Unsupported `@[extern]` declaration `{decl.name}` in Stage 1B"
    | .code rawC =>
      let c ← if arch.isFreestandingEmbedded then
        normalizeEmbeddedSliceGetBang {} embeddedExportSliceFVars rawC
      else pure rawC
      let decl : Lean.Compiler.LCNF.Decl .impure := { decl with params := normParams, value := .code c }
      if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name paramIds retTy paramTypesList then
        let retVar ← freshBridgeVar retTy
        let lnirParams := (decl.params.toList.zip (paramIds.zip paramTypesList)).map fun (p, (vid, pTy)) =>
          { id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow : LNIRParam }
        return {
          name := metaInfo.mangledSymbol, params := lnirParams, retTy := retTy,
          body := .letBind retVar retTy intrExpr (.ret retVar), assurance := .tested,
          isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible }
      if codeHasSelfTailCall decl.name c then
        Lean.throwError s!"[lean-native] unsupported self-tail recursion in {decl.name}: no qualified loop lowering"
      checkImpureLetTypesM c
      let knownCtors := collectFVarCtors c
      let typeExprs := decl.type :: (decl.params.toList.map (·.type) ++ collectCodeTypeExprs [] c)
      let (ctors, callees) := collectCodeCtorAndCalleeNames [] [] c
      let ctx ← buildRealBridgeCtxM typeExprs (ctors ++ knownCtors.toList.map Prod.snd)
        callees paramTypeMap knownCtors.toList
      let fuel := codeAstFuel c + decl.params.size + 64
      match RealLCNFBridge.lowerRealLCNFDecl fuel ctx decl metaInfo.mangledSymbol with
      | .ok d =>
        let rstAfter := (RealLCNFBridge.internRealParams ctx {} decl.params.toList).2
        let (nextAfter, endVarTypes) := match RealLCNFBridge.lowerRealLCNFCode fuel ctx rstAfter c with
          | .ok (_, rstEnd) => (rstEnd.nextVarId, rstEnd.varTypes)
          | .error _ => (d.params.length + 16, rstAfter.varTypes)
        modify fun s => {
          s with
          varTypes := endVarTypes.foldl (fun m (v, t) => m.insert v t) s.varTypes
          nextVarId := max s.nextVarId (nextAfter + 4) }
        let compressedCand ← compressScalarCode d.body
        let candRetTy := match inferReturnedType compressedCand with | some (.tuple fs) => .tuple fs | _ => d.retTy
        let baseRetTy := match inferReturnedType d.body with | some (.tuple fs) => .tuple fs | _ => d.retTy
        let baseDecl : LNIRDecl := { d with retTy := baseRetTy }
        let candDecl : LNIRDecl := { d with body := compressedCand, retTy := candRetTy }
        let useCompressed :=
          compressedCand != d.body && (LeanNative.Proofs.validateTranslationDecl baseDecl candDecl 64).passed
        let finalBody := if useCompressed then compressedCand else d.body
        let effRetTy := if useCompressed then candRetTy else baseRetTy
        let effAssurance :=
          if useCompressed then AssuranceLevel.combine d.assurance .translationValidated else d.assurance
        let dOut : LNIRDecl := { d with
          body := finalBody
          retTy := effRetTy
          assurance := effAssurance
          isGpuCand := d.params.all (fun p => p.ty.isGpuCompatible) && effRetTy.isGpuCompatible }
        attachBaseDeclFactsM decl.name dOut
      | .error msg => Lean.throwError msg
  Prod.fst <$> action.run initSt

end LeanNative.IR
