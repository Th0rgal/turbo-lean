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

/-- Module gate before inlining: every direct callee is a module declaration and symbols are
    unique, the driver side of `H1.ModuleCallees`. Call cycles are accepted: self- and mutually
    recursive modules lower through `lowerRealLCNFModule` and are proved at every call depth by
    `H1.recRefinement` (W2-L3). -/
def validateIngestedModule (mod : LNIRModule) : Lean.CoreM Unit := do
  let knownNames := mod.decls.map (·.name)
  if knownNames.eraseDups.length != knownNames.length then
    Lean.throwError s!"[lean-native] Duplicate lowered symbol in `{mod.moduleName}`"
  for d in mod.decls do
    for c in (collectDirectCallees d.body).eraseDups do
      if !knownNames.contains c then
        Lean.throwError s!"[lean-native] Unsupported unresolved call `{c}` in `{d.name}`"

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

def expandCompilerAuxDecls (declNames : Array Lean.Name) : Lean.CoreM (Array Lean.Name) := do
  let mut out := declNames
  for name in declNames do
    let red := Lean.Name.str name "_redArg"
    if !out.contains red then
      if (← Lean.Compiler.LCNF.getLocalImpureDecl? red).isSome || (← Lean.Compiler.LCNF.getMonoDecl? red).isSome then
        out := out.push red
  return out

def ingestModuleDeclsWith (ingestImpure : Lean.Compiler.LCNF.Decl .impure → Array Lean.Name → TargetArch → Lean.CoreM LNIRDecl)
    (rawDeclNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested")
    (arch : TargetArch := .x86_64) : Lean.CoreM LNIRModule := do
  let declNames ← expandCompilerAuxDecls rawDeclNames
  let env ← getEnv
  let mut decls : List LNIRDecl := []
  let mut rawPairs : List (Lean.Name × String) := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      let d ← ingestImpure impureDecl declNames arch
      decls := decls ++ [d]
      rawPairs := rawPairs ++ [(name, d.name)]
    else if (← Lean.Compiler.LCNF.getMonoDecl? name).isSome then
      Lean.throwError s!"[lean-native] `{name}` has no local impure LCNF: only `Decl .impure` lowers (via the proved `lowerRealLCNFDecl`)"
  let rawMod : LNIRModule := { moduleName := moduleName, decls := decls }
  validateIngestedModule rawMod
  filterNonInternalHelperDecls env rawPairs arch (normalizeAndInlineLocalDefs rawMod)

private def u64Param : LNIRParam := { id := 0, name := "x", ty := .i64 }

/-- `f` calls itself and `g`, and `g` calls `f`: a recursive module passes the gate. -/
private def recCallGraphRegMod : LNIRModule where
  moduleName := "rec_call_graph_regression"
  decls := [
    { name := "f", params := [u64Param], retTy := .i64,
      body := .letBind 1 .i64 (.call "f" [0] .i64)
        (.letBind 2 .i64 (.call "g" [1] .i64) (.ret 2)) },
    { name := "g", params := [u64Param], retTy := .i64,
      body := .letBind 1 .i64 (.call "f" [0] .i64) (.ret 1) }
  ]

#eval validateIngestedModule recCallGraphRegMod

private def gateRejects (m : LNIRModule) : Lean.CoreM Bool :=
  tryCatch (validateIngestedModule m *> pure false) fun _ => pure true

-- An unresolved callee and a duplicated symbol still fail closed.
#eval show Lean.CoreM Unit from do
  let fOnly := { recCallGraphRegMod with decls := recCallGraphRegMod.decls.take 1 }
  let ds := recCallGraphRegMod.decls
  let dup := { recCallGraphRegMod with decls := ds ++ ds }
  unless (← gateRejects fOnly) && (← gateRejects dup) do
    Lean.throwError "validateIngestedModule accepted an unresolved call or a duplicate symbol"

end LeanNative.IR
