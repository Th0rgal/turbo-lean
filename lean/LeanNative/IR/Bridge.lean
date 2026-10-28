import LeanNative.IR.BridgeHelpers

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-- Canonical `Lean.Name` lookup table for scalar binary operations (Contract G3.1 / M4).
    Note: `Nat.sub` is intentionally excluded because `Nat` subtraction saturates at 0 whereas
    `BinOp.sub` is modular `UInt64` subtraction. Only exact-matching `Lean.Name` entries are
    lowered to scalar `BinOp` (no blind leaf-name fallback). -/
def canonicalScalarBinOpTable : List (Lean.Name × BinOp) := [
  (``UInt64.add, .add), (``UInt64.sub, .sub), (``UInt64.mul, .mul), (``UInt64.div, .div), (``UInt64.mod, .mod),
  (``UInt64.land, .bitAnd), (``UInt64.lor, .bitOr), (``UInt64.xor, .bitXor), (``UInt64.shiftLeft, .shl), (``UInt64.shiftRight, .shr),
  (``UInt64.decEq, .eq), (`UInt64.beq, .eq), (``UInt64.decLt, .lt), (`UInt64.blt, .lt), (``UInt64.decLe, .le), (`UInt64.ble, .le),
  (``UInt32.add, .add), (``UInt32.sub, .sub), (``UInt32.mul, .mul), (``UInt32.div, .div), (``UInt32.mod, .mod),
  (``UInt32.land, .bitAnd), (``UInt32.lor, .bitOr), (``UInt32.xor, .bitXor), (``UInt32.shiftLeft, .shl), (``UInt32.shiftRight, .shr),
  (``UInt32.decEq, .eq), (`UInt32.beq, .eq), (``UInt32.decLt, .lt), (``UInt32.decLe, .le),
  (``UInt16.add, .add), (``UInt16.sub, .sub), (``UInt16.mul, .mul), (``UInt16.div, .div), (``UInt16.mod, .mod),
  (``UInt16.land, .bitAnd), (``UInt16.lor, .bitOr), (``UInt16.xor, .bitXor), (``UInt16.shiftLeft, .shl), (``UInt16.shiftRight, .shr),
  (``UInt8.add, .add), (``UInt8.sub, .sub), (``UInt8.mul, .mul), (``UInt8.div, .div), (``UInt8.mod, .mod),
  (``UInt8.land, .bitAnd), (``UInt8.lor, .bitOr), (``UInt8.xor, .bitXor), (``UInt8.shiftLeft, .shl), (``UInt8.shiftRight, .shr),
  (``USize.add, .add), (``USize.sub, .sub), (``USize.mul, .mul), (``USize.div, .div), (``USize.mod, .mod),
  (``USize.land, .bitAnd), (``USize.lor, .bitOr), (``USize.xor, .bitXor), (``USize.shiftLeft, .shl), (``USize.shiftRight, .shr),
  (``USize.decEq, .eq), (`USize.beq, .eq), (``USize.decLt, .lt), (``USize.decLe, .le),
  (``Nat.add, .add), (``Nat.mul, .mul), (``Nat.div, .div), (``Nat.mod, .mod),
  (``Nat.land, .bitAnd), (``Nat.lor, .bitOr), (``Nat.xor, .bitXor), (``Nat.shiftLeft, .shl), (``Nat.shiftRight, .shr),
  (``Nat.decEq, .eq), (``Nat.beq, .eq), (``Nat.decLt, .lt), (``Nat.blt, .lt), (``Nat.decLe, .le), (``Nat.ble, .le)
]

def lookupCanonicalBinOp? (fnName : Lean.Name) : Option BinOp :=
  (canonicalScalarBinOpTable.find? (fun p => p.1 == fnName)).map Prod.snd

def isCanonicalArrayGetName (fnName : Lean.Name) : Bool :=
  [``Array.uget, `Array.fget, ``ByteArray.uget, ``ByteArray.get!].contains fnName

def isCanonicalArraySetName (fnName : Lean.Name) : Bool :=
  [``Array.uset, `Array.fset, ``ByteArray.uset, ``ByteArray.set!].contains fnName

def isCanonicalArrayLenName (fnName : Lean.Name) : Bool :=
  [``Array.size, ``Array.usize, ``ByteArray.size, ``ByteArray.usize, ``FloatArray.size, ``FloatArray.usize].contains fnName

def tryLowerIntrinsicCall (env : Lean.Environment) (fnName : Lean.Name) (argVars : List VarId)
    (retTy : LNIRType) (argTys : List LNIRType := []) (isLocal : Bool := false) : Option LNIRExpr :=
  match argVars with
  | [lhs, rhs] =>
    match tryLowerGfSimdIntrinsic env fnName argVars retTy argTys with
    | some intr => some intr
    | none =>
      if isLocal then none
      else match lookupCanonicalBinOp? fnName with
        | some op => some (.scalar (.binOp op (.var lhs) (.var rhs)))
        | none => if isCanonicalArrayGetName fnName then some (.sarrayGet lhs rhs retTy) else none
  | [arr] =>
    if !isLocal && isCanonicalArrayLenName fnName then some (.sarrayLen arr) else none
  | [arr, idx, val] =>
    if !isLocal && isCanonicalArraySetName fnName then
      some (.sarraySet arr idx val (match retTy with | .sarray elem => elem | _ => .i64))
    else none
  | _ => none

def lowerNamedCall (fnName : Lean.Name) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let argVars ← args.toList.mapM lowerArg
  let argTys ← argVars.mapM getVarType
  let env ← getEnv
  let st ← get
  let isLocal := st.localDeclNames.contains fnName || fnName == st.selfDeclName
  match tryLowerIntrinsicCall env fnName argVars retTy argTys isLocal with
  | some intrinsicExpr => return intrinsicExpr
  | none =>
    let isExt := !isLocal && Lean.isExtern env fnName
    if isExt then modify fun st => { st with hasExtern := true }
    return .call (mangleDeclNameInEnv env fnName) argVars retTy isExt

def lowerFVarCall (fvarId : Lean.FVarId) (args : Array (Lean.Compiler.LCNF.Arg pu)) (retTy : LNIRType) : BridgeM LNIRExpr := do
  let fnVar ← internFVar fvarId
  if args.isEmpty then
    return .scalar (.var fnVar)
  else
    return .call s!"fvar_{fnVar}" (← args.toList.mapM lowerArg) retTy false

def lowerCtorApp (ctorName : Lean.Name) (cidx size : Nat) (args : Array (Lean.Compiler.LCNF.Arg pu)) : BridgeM LNIRExpr := do
  let env ← getEnv
  let argVars ← args.toList.mapM lowerArg
  let isProd := ctorName == ``Prod.mk || ctorName == ``MProd.mk || ctorName == ``PProd.mk
  let isSingleCtorStruct := match env.find? ctorName with
    | some (.ctorInfo cval) =>
      match env.find? cval.induct with
      | some (.inductInfo ival) => ival.ctors.length == 1 && !ival.isRec
      | _ => false
    | _ => false
  if isProd || (isSingleCtorStruct && argVars.length ≤ 8) then
    return .mkTuple argVars
  else
    return .allocCtor cidx (argVars.take size) (argVars.drop size)

def lowerImpureLetValue (lv : Lean.Compiler.LCNF.LetValue .impure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => return lowerLitValue litVal
  | .erased => return .scalar (.constU64 0)
  | .fvar fvarId args => lowerFVarCall fvarId args retTy
  | .ctor ctorInfo args _ | .reuse _ ctorInfo _ args _ =>
    lowerCtorApp ctorInfo.name ctorInfo.cidx ctorInfo.size args
  | .oproj idx fvarId _ =>
    let v ← internFVar fvarId
    match (← getVarType v) with
    | .tuple _ => return .projTuple v idx
    | _ => return .ctorGetObj v idx
  | .uproj idx fvarId _ => return .ctorGetScalar (← internFVar fvarId) idx .usize
  | .sproj offset _ fvarId _ => return .ctorGetScalar (← internFVar fvarId) offset retTy
  | .fap fnName args _ | .pap fnName args _ => lowerNamedCall fnName args retTy
  | .reset _ fvarId _ => return .scalar (.var (← internFVar fvarId))
  | .box tyExpr fvarId _ => return .boxScalar (← internFVar fvarId) (lowerImpureType tyExpr)
  | .unbox fvarId _ => return .unboxScalar (← internFVar fvarId) retTy
  | .isShared fvarId _ => return .isExclusive (← internFVar fvarId)

mutual
partial def lowerImpureAlts (condVar : VarId) (alts : List (Lean.Compiler.LCNF.Alt .impure)) : BridgeM LNIRCode := do
  match alts with
  | [] => return .unreachable
  | [singleAlt] => lowerImpureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .ctorAlt info code _ =>
      let cmpVar ← freshBridgeVar .i64
      return .letBind cmpVar .i64 (.scalar (.binOp .eq (.var condVar) (.constU64 info.cidx.toUInt64)))
        (.ite cmpVar (← lowerImpureCode code) (← lowerImpureAlts condVar rest))
    | .default code => lowerImpureCode code
    | .alt _ params code _ =>
      internParams params
      return .ite condVar (← lowerImpureCode code) (← lowerImpureAlts condVar rest)

partial def lowerImpureCode (code : Lean.Compiler.LCNF.Code .impure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let st ← get
    match k, decl.value, st.selfLoopAccVar with
    | .return retFVar, .fap fnName args _, some accVar =>
      if retFVar == decl.fvarId && fnName == st.selfDeclName then
        spliceJoinPointJmp st.selfParams (.ret accVar) args
      else
        let ty := lowerImpureType decl.type
        return .letBind (← internFVar decl.fvarId ty) ty (← lowerImpureLetValue decl.value ty) (← lowerImpureCode k)
    | _, .isShared fvarId _, _ =>
      let refVar ← internFVar fvarId
      let exclVar ← freshBridgeVar .i1
      let dstVar ← internFVar decl.fvarId .i1
      let kCode ← lowerImpureCode k
      return .letBind exclVar .i1 (.isExclusive refVar)
        (.letBind dstVar .i1 (.scalar (.unaryOp .not (.var exclVar))) kCode)
    | _, _, _ =>
      let ty := lowerImpureType decl.type
      return .letBind (← internFVar decl.fvarId ty) ty (← lowerImpureLetValue decl.value ty) (← lowerImpureCode k)
  | .jp decl k => lowerJoinPoint decl k lowerImpureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .inc fvarId n _ _ k _ => return .incRef (← internFVar fvarId) n (← lowerImpureCode k)
  | .dec fvarId n _ _ _ k _ => return .decRef (← internFVar fvarId) n (← lowerImpureCode k)
  | .del fvarId k _ => return .decRef (← internFVar fvarId) 1 (← lowerImpureCode k)
  | .oset fvarId idx arg k _ => lowerIndexedSet fvarId idx (← lowerArg arg) .objPtr (← lowerImpureCode k)
  | .uset fvarId idx valFVar k _ => lowerIndexedSet fvarId idx (← internFVar valFVar .usize) .usize (← lowerImpureCode k)
  | .sset fvarId idx _ valFVar tyExpr k _ =>
    let elemTy := lowerImpureType tyExpr
    lowerIndexedSet fvarId idx (← internFVar valFVar elemTy) elemTy (← lowerImpureCode k)
  | .setTag _ _ k _ => lowerImpureCode k
  | .cases c => lowerImpureAlts (← internFVar c.discr) (orderAlts c.alts.toList)
  | .return fvarId => return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
end

def lowerPureLetValue (lv : Lean.Compiler.LCNF.LetValue .pure) (retTy : LNIRType) : BridgeM LNIRExpr := do
  match lv with
  | .lit litVal => return lowerLitValue litVal
  | .erased => return .scalar (.constU64 0)
  | .proj _ idx fvarId _ => return .projTuple (← internFVar fvarId) idx
  | .const declName _ args _ =>
    if declName == ``Prod.mk || declName == ``MProd.mk || declName == ``PProd.mk then
      return .mkTuple (← args.toList.mapM lowerArg)
    else
      lowerNamedCall declName args retTy
  | .fvar fvarId args => lowerFVarCall fvarId args retTy

def lookupCtorIdx (ctorName : Lean.Name) (fallbackIdx : Nat) : BridgeM Nat := do
  match (← getEnv).find? ctorName with
  | some (.ctorInfo cval) => return cval.cidx
  | _ => return fallbackIdx

mutual
partial def lowerPureAlts (condVar : VarId) (idx : Nat) (alts : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
  let emitTagBranch (cidx : Nat) (code : Lean.Compiler.LCNF.Code .pure) (rest : List (Lean.Compiler.LCNF.Alt .pure)) : BridgeM LNIRCode := do
    let cmpVar ← freshBridgeVar .i64
    return .letBind cmpVar .i64 (.scalar (.binOp .eq (.var condVar) (.constU64 cidx.toUInt64)))
      (.ite cmpVar (← lowerPureCode code) (← lowerPureAlts condVar (idx + 1) rest))
  match alts with
  | [] => return .unreachable
  | [singleAlt] =>
    if let .alt _ params _ _ := singleAlt then internParams params
    lowerPureCode singleAlt.getCode
  | alt :: rest =>
    match alt with
    | .alt ctorName params code _ =>
      internParams params
      emitTagBranch (← lookupCtorIdx ctorName idx) code rest
    | .ctorAlt info code _ => emitTagBranch info.cidx code rest
    | .default code => lowerPureCode code

partial def lowerPureCode (code : Lean.Compiler.LCNF.Code .pure) : BridgeM LNIRCode := do
  match code with
  | .let decl k =>
    let st ← get
    match k, decl.value, st.selfLoopAccVar with
    | .return retFVar, .const fnName _ args _, some accVar =>
      if retFVar == decl.fvarId && fnName == st.selfDeclName then
        spliceJoinPointJmp st.selfParams (.ret accVar) args
      else
        let ty := lowerImpureType decl.type
        return .letBind (← internFVar decl.fvarId ty) ty (← lowerPureLetValue decl.value ty) (← lowerPureCode k)
    | _, _, _ =>
      let ty := lowerImpureType decl.type
      return .letBind (← internFVar decl.fvarId ty) ty (← lowerPureLetValue decl.value ty) (← lowerPureCode k)
  | .fun decl k _ =>
    let _ ← internFVar decl.fvarId (lowerImpureType decl.type)
    internParams decl.params
    lowerPureCode k
  | .jp decl k => lowerJoinPoint decl k lowerPureCode
  | .jmp fvarId args => lowerJmpInstr fvarId args
  | .cases c => lowerPureAlts (← internFVar c.discr) 0 (orderAlts c.alts.toList)
  | .return fvarId => return .ret (← internFVar fvarId)
  | .unreach _ => return .unreachable
end

def ingestLCNFDeclGeneric {pu} (decl : Lean.Compiler.LCNF.Decl pu)
    (lowerCodeFn : Lean.Compiler.LCNF.Code pu → BridgeM LNIRCode)
    (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl := do
  let env ← getEnv
  let metaInfo := getLCNFDeclMetadata env decl.name
  let isDeclExtern := metaInfo.isExtern
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol
    isSimpleGround := metaInfo.isSimpleGround
    selfDeclName := decl.name
    localDeclNames := localDeclNames }
  let action : BridgeM LNIRDecl := do
    let mut lnirParams : List LNIRParam := []
    for p in decl.params do
      let pTy := lowerImpureType p.type
      let vid ← internFVar p.fvarId pTy
      lnirParams := lnirParams ++ [{ id := vid, name := p.binderName.toString, ty := pTy, borrow := p.borrow }]
    let retTy := lowerImpureType decl.type
    match decl.value with
    | .code c =>
      let env ← getEnv
      let body ←
        if let some intrExpr := tryLowerGfSimdIntrinsic env decl.name (lnirParams.map (·.id)) retTy (lnirParams.map (·.ty)) then do
          let retVar ← freshBridgeVar retTy
          pure (.letBind retVar retTy intrExpr (.ret retVar))
        else if codeHasSelfTailCall decl.name c then do
          let (idxVar, accVar, accTy) ← match lnirParams with
            | p0 :: p1 :: _ => pure (p0.id, p1.id, p1.ty)
            | [p0] => pure (← freshBridgeVar .i64, p0.id, p0.ty)
            | [] => pure (← freshBridgeVar .i64, ← freshBridgeVar retTy, retTy)
          modify fun st => { st with selfLoopAccVar := some accVar, selfParams := toImpureParams decl.params }
          let stepBody ← lowerCodeFn c
          let loVar ← freshBridgeVar .i64
          let hiVar ← freshBridgeVar .i64
          let accInit ← freshBridgeVar accTy
          pure (.letBind loVar .i64 (.scalar (.constU64 0))
            (.letBind hiVar .i64 (.scalar (.constU64 64))
              (.letBind accInit accTy (.scalar (.var accVar))
                (.seqFor idxVar loVar hiVar accVar accInit accTy stepBody (.ret accVar)))))
        else
          lowerCodeFn c
      let st ← get
      return {
        name := metaInfo.mangledSymbol
        params := lnirParams
        retTy := retTy
        body := body
        assurance := if isDeclExtern || st.hasExtern then .unverifiedFallback else .verifiedKernelProof
        isGpuCand := lnirParams.all (fun p => p.ty.isGpuCompatible) && retTy.isGpuCompatible }
    | .extern _ =>
      let retVar ← freshBridgeVar retTy
      return {
        name := metaInfo.mangledSymbol
        params := lnirParams
        retTy := retTy
        body := .letBind retVar retTy (.call metaInfo.mangledSymbol (lnirParams.map (·.id)) retTy true) (.ret retVar)
        assurance := .unverifiedFallback
        isGpuCand := false }
  Prod.fst <$> action.run initSt

def ingestLCNFImpureDecl (decl : Lean.Compiler.LCNF.Decl .impure) (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerImpureCode localDeclNames

def ingestLCNFMonoDecl (decl : Lean.Compiler.LCNF.Decl .pure) (localDeclNames : Array Lean.Name := #[]) : Lean.CoreM LNIRDecl :=
  ingestLCNFDeclGeneric decl lowerPureCode localDeclNames

def ingestModuleDecls (declNames : Array Lean.Name) (moduleName : String := "LeanNative.Ingested") : Lean.CoreM LNIRModule := do
  let mut decls : List LNIRDecl := []
  for name in declNames do
    if let some impureDecl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      decls := decls ++ [← ingestLCNFImpureDecl impureDecl declNames]
    else if let some monoDecl ← Lean.Compiler.LCNF.getMonoDecl? name then
      decls := decls ++ [← ingestLCNFMonoDecl monoDecl declNames]
  return { moduleName := moduleName, decls := decls }

def isInternalClosedOrReprAux (name : Lean.Name) : Bool :=
  ["___closed__", "instRepr", "_cstage", "ctorElim"].any fun pat => (name.toString.splitOn pat).length > 1

def ingestAllLocalDecls (moduleName : String := "LeanNative.Ingested") : Lean.CoreM LNIRModule := do
  let impureNames ← Lean.Compiler.LCNF.getLocalImpureDecls
  let env ← getEnv
  let extraNames := env.constants.map₂.foldl (fun acc name _ =>
    if impureNames.contains name || isInternalClosedOrReprAux name then acc else acc.push name) #[]
  let filteredImpure := impureNames.filter (fun n => !isInternalClosedOrReprAux n)
  ingestModuleDecls (if filteredImpure.isEmpty && extraNames.isEmpty then impureNames else (filteredImpure ++ extraNames)) moduleName

end LeanNative.IR
