import LeanNative.IR.BridgeHelpers.RealBridgeCtxAndSlices

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

def isClosedConstHelperName : Lean.Name → Bool
  | .str p s =>
    s == "_boxed_const" || (s.splitOn "_boxed_const_").length > 1 ||
    s == "_closed" || (s.splitOn "_closed_").length > 1 ||
    isClosedConstHelperName p
  | .num p _ => isClosedConstHelperName p
  | .anonymous => false

def nameHasCompilerAuxComponent : Lean.Name → Bool
  | .str p s =>
    s == "_boxed" || s == "ctorIdx" || s == "ctorElim" || s == "ctorElimType" ||
    s == "noConfusion" || s == "noConfusionType" || s == "recOn" || s == "casesOn" ||
    s == "brecOn" || s == "below" || s == "ibelow" || s == "elim" ||
    (s.splitOn "___closed__").length > 1 || (s.splitOn "instRepr").length > 1 ||
    (s.splitOn "_cstage").length > 1 || (s.splitOn "_sparseCasesOn_").length > 1 ||
    (s.splitOn "_sizeOf_").length > 1 || s == "sizeOf_spec" ||
    nameHasCompilerAuxComponent p
  | .num p _ => nameHasCompilerAuxComponent p
  | .anonymous => false

def isCompilerGeneratedAuxDecl (env : Lean.Environment) (name : Lean.Name) : Bool :=
  if isClosedConstHelperName name then false
  else Lean.isAuxRecursor env name || Lean.isNoConfusion env name || nameHasCompilerAuxComponent name

private def isBuiltinLNIRRuntimeCall (fn : String) : Bool :=
  fn == "lean_native_ctor_tag" || fn == "lean_native_ctor_set" ||
  fn == "lean_native_ctor_set_scalar" || fn == "lean_native_ctor_set_tag" || fn == "lean_native_del_obj" ||
  fn == "lean_native_box_u64" || fn == "lean_native_unbox_u64" ||
  fn == "lean_native_ensure_exclusive" || fn == "lean_native_sarray_len"

private partial def collectDirectCallees : LNIRCode → List String
  | .letBind _ _ (.call fn _ _ isExt) k =>
    if isExt || isBuiltinLNIRRuntimeCall fn then collectDirectCallees k else fn :: collectDirectCallees k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k =>
    collectDirectCallees k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => collectDirectCallees t ++ collectDirectCallees e
  | .ret _ | .unreachable => []

private partial def reachesDeclInCallGraph (edges : List (String × List String))
    (target : String) (fuel : Nat) (visited : List String) (frontier : List String) : Bool :=
  match fuel, frontier with
  | 0, _ => true
  | _, [] => false
  | fuel + 1, cur :: rest =>
    if cur == target then true
    else if visited.contains cur then
      reachesDeclInCallGraph edges target (fuel + 1) visited rest
    else
      let nexts := ((edges.lookup cur).getD []).eraseDups
      reachesDeclInCallGraph edges target fuel (cur :: visited) (nexts ++ rest)

def validateIngestedModule (mod : LNIRModule) : Lean.CoreM Unit := do
  let knownNames := mod.decls.map (·.name)
  let edges := mod.decls.map fun d => (d.name, (collectDirectCallees d.body).eraseDups)
  for d in mod.decls do
    let callees := (edges.lookup d.name).getD []
    for c in callees do
      if !knownNames.contains c then
        Lean.throwError s!"[lean-native] Unsupported unresolved call `{c}` in `{d.name}`"
    if reachesDeclInCallGraph edges d.name (mod.decls.length + 2) [] callees then
      Lean.throwError s!"[lean-native] Unsupported self-tail recursion / mutual recursion involving `{d.name}`"

partial def codeHasResidualHeapOrTupleAbiOp : LNIRCode → Bool
  | .letBind _ ty val k =>
    (ty == .objPtr || ty == .taggedPtr) ||
    (match val with
      | .allocCtor .. | .ctorGetObj .. | .ctorGetScalar .. | .boxScalar .. | .unboxScalar .. | .isExclusive .. => true
      | .call "lean_native_ctor_set" .. | .call "lean_native_ctor_tag" .. => true
      | .call "lean_native_ctor_set_scalar" .. | .call "lean_native_ctor_set_tag" .. | .call "lean_native_del_obj" .. => true
      | _ => false) ||
    codeHasResidualHeapOrTupleAbiOp k
  | .incRef .. | .decRef .. => true
  | .rawStore _ _ _ _ k | .parFor _ _ _ _ _ k => codeHasResidualHeapOrTupleAbiOp k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasResidualHeapOrTupleAbiOp t || codeHasResidualHeapOrTupleAbiOp e
  | .ret _ | .unreachable => false

def filterNonInternalHelperDecls (env : Lean.Environment) (rawPairs : List (Lean.Name × String))
    (arch : TargetArch) (mod : LNIRModule) : Lean.CoreM LNIRModule := do
  let stage1DMangled : List String := rawPairs.filterMap fun (origName, mangled) =>
    if declQualifiesForStage1DHeap env origName arch then some mangled else none
  let isStage1DParamOrRet (ty : LNIRType) : Bool :=
    isSupportedStage1BScalarOrTuple ty arch || ty == .objPtr || ty == .taggedPtr
  let keepNames : List String ← rawPairs.filterMapM fun (origName, mangled) => do
    let isExported := (Lean.getExportNameFor? env origName).isSome
    let isUserConst := (env.find? origName).isSome && !origName.isInternalDetail && !isClosedConstHelperName origName
    if !(isExported || isUserConst) then
      return none
    match mod.decls.find? (·.name == mangled) with
    | none => return none
    | some d =>
      let hasExportedNonScalarSig :=
        d.params.any (fun p => !(isSupportedStage1BScalarType p.ty arch ||
          (arch.isFreestandingEmbedded && p.borrow && isSupportedSliceType p.ty))) ||
        !isSupportedStage1BScalarType d.retTy arch ||
        (inferReturnedType d.body |>.any (fun rt => !isSupportedStage1BScalarType rt arch))
      let hasUserUnsupportedSig :=
        d.params.any (fun p => !(isSupportedScalarOrFloat p.ty arch || (p.borrow && isSupportedSliceType p.ty))) ||
        !isSupportedScalarOrFloat d.retTy arch ||
        (inferReturnedType d.body |>.any (fun rt => !isSupportedScalarOrFloat rt arch))
      if isExported then
        if hasExportedNonScalarSig || codeHasResidualHeapOrTupleAbiOp d.body then
          Lean.throwError s!"[lean-native] Exported function `{origName}` has unsupported non-scalar signature or unlowered tuple/heap operations"
        return some mangled
      else if stage1DMangled.contains mangled then
        if d.params.any (fun p => !isStage1DParamOrRet p.ty) || !isStage1DParamOrRet d.retTy then
          Lean.throwError s!"[lean-native] Stage 1D helper `{origName}` has unsupported signature"
        return some mangled
      else if hasUserUnsupportedSig then
        return none
      else
        if codeHasResidualHeapOrTupleAbiOp d.body then
          Lean.throwError s!"[lean-native] Function `{origName}` contains unlowered heap/object operations after helper inlining"
        return some mangled
  let edges := mod.decls.map fun d => (d.name, collectDirectCallees d.body)
  let neededBy (roots : List String) : List String :=
    let step (acc : List String) : List String :=
      acc.foldl (fun cur nm =>
        let cs := (edges.lookup nm).getD []
        cs.foldl (fun a c => if a.contains c then a else c :: a) cur) acc
    (List.range (mod.decls.length + 1)).foldl (fun acc _ => step acc) roots
  let liveNames := neededBy keepNames
  if keepNames.isEmpty && !rawPairs.isEmpty then
    Lean.throwError "[lean-native] Module contains no Stage 1B scalar functions after filtering non-scalar helpers"
  let filteredDecls := mod.decls.filter (fun d => liveNames.contains d.name)
  for d in filteredDecls do
    if stage1DMangled.contains d.name then
      if d.params.any (fun p => !isStage1DParamOrRet p.ty) || !isStage1DParamOrRet d.retTy then
        Lean.throwError s!"[lean-native] Live Stage 1D declaration `{d.name}` has unsupported signature"
    else if d.params.any (fun p => !(isSupportedScalarOrFloat p.ty arch || (p.borrow && isSupportedSliceType p.ty))) ||
       !isSupportedScalarOrFloat d.retTy arch ||
       codeHasResidualHeapOrTupleAbiOp d.body then
      Lean.throwError s!"[lean-native] Live declaration `{d.name}` retains non-scalar signature or unlowered object operations"
  return { mod with decls := filteredDecls }

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

def extractPureDeclFactsWithBridgeState (decl : Lean.Compiler.LCNF.Decl .pure)
    (st : BridgeState) (d : LNIRDecl) : LNIRDecl :=
  let seedMap := st.fvarToVar.toList
  let fuel := decl.params.size +
    (match decl.value with | .code c => pureCodeAstFuel c | .extern _ => 0) + 128
  let liveVarTys := collectDeclVarTys (d.params.map fun p => (p.id, p.ty)) d.body
  let facts := (LeanNative.Frontend.ProofRetention.retainedPureDeclFactsWithSeed
    fuel seedMap st.nextVarId decl).filter (factVarsInScope liveVarTys)
  let merged := facts.foldl LeanNative.IR.consFact d.retainedFacts
  { d with retainedFacts := merged }

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

def expandCompilerAuxDecls (declNames : Array Lean.Name) : Lean.CoreM (Array Lean.Name) := do
  let mut out := declNames
  for name in declNames do
    let red := Lean.Name.str name "_redArg"
    if !out.contains red then
      if (← Lean.Compiler.LCNF.getLocalImpureDecl? red).isSome || (← Lean.Compiler.LCNF.getMonoDecl? red).isSome then
        out := out.push red
  return out

def ingestModuleDeclsWith (ingestImpure : Lean.Compiler.LCNF.Decl .impure → Array Lean.Name → TargetArch → Lean.CoreM LNIRDecl)
    (ingestMono : Lean.Compiler.LCNF.Decl .pure → Array Lean.Name → TargetArch → Lean.CoreM LNIRDecl)
    (rawDeclNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) : Lean.CoreM LNIRModule := do
  let declNames ← expandCompilerAuxDecls rawDeclNames
  let env ← getEnv
  let mut callGraph : Std.HashMap Lean.Name (List Lean.Name) := {}
  let mut decls : List LNIRDecl := []
  let mut rawPairs : List (Lean.Name × String) := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      if let .code c := impureDecl.value then
        callGraph := callGraph.insert name (collectCodeLocalCallees declNames c)
      let d ← ingestImpure impureDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      if let .code c := monoDecl.value then
        callGraph := callGraph.insert name (collectCodeLocalCallees declNames c)
      let d ← ingestMono monoDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
  if declsHaveMutualCycle callGraph then
    Lean.throwError s!"[lean-native] unsupported self-tail recursion / mutual recursion in {moduleName}: no qualified loop lowering"
  let rawMod : LNIRModule := { moduleName := moduleName, decls := decls }
  validateIngestedModule rawMod
  filterNonInternalHelperDecls env rawPairs arch (normalizeAndInlineLocalDefs rawMod)

private def diamondCallGraphRegMod : LNIRModule where
  moduleName := "diamond_call_graph_regression"
  decls := [
    { name := "f", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "g" [0] .i64)
          (.letBind 2 .i64 (.call "h" [0] .i64)
            (.letBind 3 .i64 (.call "g" [1] .i64)
              (.letBind 4 .i64 (.call "h" [2] .i64)
                (.ret 4)))) },
    { name := "g", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "k" [0] .i64)
          (.letBind 2 .i64 (.call "k" [1] .i64)
            (.ret 2)) },
    { name := "h", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "k" [0] .i64)
          (.letBind 2 .i64 (.call "k" [1] .i64)
            (.ret 2)) },
    { name := "k", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body := .ret 0 }
  ]

private def visitedFuelRegMod : LNIRModule where
  moduleName := "visited_fuel_regression"
  decls := [
    { name := "f", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "g" [0] .i64)
          (.letBind 2 .i64 (.call "h" [1] .i64)
            (.letBind 3 .i64 (.call "k" [2] .i64)
              (.ret 3))) },
    { name := "g", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body :=
        .letBind 1 .i64 (.call "h" [0] .i64)
          (.letBind 2 .i64 (.call "k" [1] .i64)
            (.ret 2)) },
    { name := "h", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body := .letBind 1 .i64 (.call "k" [0] .i64) (.ret 1) },
    { name := "k", params := [{ id := 0, name := "x", ty := .i64 }], retTy := .i64,
      body := .ret 0 }
  ]

#guard
  let edges := diamondCallGraphRegMod.decls.map fun d => (d.name, (collectDirectCallees d.body).eraseDups)
  !(reachesDeclInCallGraph edges "f" (diamondCallGraphRegMod.decls.length + 2) [] ["g", "h"])
#guard
  let edges := visitedFuelRegMod.decls.map fun d => (d.name, (collectDirectCallees d.body).eraseDups)
  !(reachesDeclInCallGraph edges "f" (visitedFuelRegMod.decls.length + 2) [] ((edges.lookup "f").getD []))
#eval validateIngestedModule diamondCallGraphRegMod
#eval validateIngestedModule visitedFuelRegMod

end LeanNative.IR
