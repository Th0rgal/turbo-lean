import Lean
import LeanNative.IR.Bridge
import LeanNative.IR.RealLCNFSemantics
import LeanNative.Driver.BuildExe

/-!
# H1.1 Differential Driver: `RealLCNFSemantics` vs. Stock Lean Evaluation

Evaluates real elaborated `Lean.Compiler.LCNF.Decl .impure` declarations with
`LeanNative.IR.RealLCNFSemantics.evalRealLCNFDecl` and compares each result directly
against stock Lean evaluation (`whnf` / `reduce` on the declaration in `MetaM`),
reporting:
- `compared_count`
- `skipped_count` and breakdown by reason (`unsupported_construct`, `non_computable`, `io`, etc.)
- `mismatch_count` (and detailed mismatch diagnostics if any)
- `constructs_covered`
-/

namespace LeanNative.Driver.EvalLCNFCLI

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-- Canonical skip categories for declarations outside `RealLCNFSemantics`'s executable domain. -/
inductive SkipReason where
  | io
  | nonComputable
  | externOrOpaque
  | higherOrderOrClosures
  | unsupportedType
  | unsupportedConstruct
  | internalCompilerAux
  deriving Repr, DecidableEq, Inhabited

namespace SkipReason

def toKey : SkipReason → String
  | .io => "io"
  | .nonComputable => "non_computable"
  | .externOrOpaque => "extern_or_opaque"
  | .higherOrderOrClosures => "higher_order_or_closures"
  | .unsupportedType => "unsupported_type"
  | .unsupportedConstruct => "unsupported_construct"
  | .internalCompilerAux => "internal_compiler_aux"

def all : List SkipReason :=
  [ .io
  , .nonComputable
  , .externOrOpaque
  , .higherOrderOrClosures
  , .unsupportedType
  , .unsupportedConstruct
  , .internalCompilerAux ]

end SkipReason

/-- Outcome of evaluating a single `(decl, inputVector)` test point. -/
structure VectorMismatch where
  declName : String
  argsRepr : String
  lcnfResult : String
  stockLeanResult : String
  deriving Repr, Inhabited

/-- Outcome of evaluating a single declaration across its test vectors. -/
inductive DeclEvalOutcome where
  | compared (declName : String) (vectorCount : Nat) (constructs : List String) (mismatches : List VectorMismatch)
  | skipped (declName : String) (reason : SkipReason) (detail : String)
  deriving Repr, Inhabited

/-- Summary statistics across a differential evaluation run. -/
structure DiffReport where
  schema : Nat := 1
  sourceDescription : String
  totalDecls : Nat
  comparedCount : Nat
  comparedVectors : Nat
  skippedCount : Nat
  skippedByReason : List (String × Nat)
  mismatchCount : Nat
  mismatches : List VectorMismatch
  constructsCovered : List (String × Nat)
  comparedDecls : List String
  skippedDecls : List (String × String × String)
  deriving Repr, Inhabited

/-! ## AST Inspection for Context Building & Construct Coverage -/

private def addUniqueExpr (xs : List Expr) (e : Expr) : List Expr :=
  if xs.contains e then xs else xs ++ [e]

private def addUniqueName (xs : List Name) (n : Name) : List Name :=
  if xs.contains n then xs else xs ++ [n]

private def addUniqueStr (xs : List String) (s : String) : List String :=
  if xs.contains s then xs else xs ++ [s]

partial def collectCodeTypeExprsLocal (acc : List Expr) (code : Code .impure) : List Expr :=
  match code with
  | .let decl k => collectCodeTypeExprsLocal (addUniqueExpr acc decl.type) k
  | .jp decl k | .fun decl k _ =>
    let acc1 := decl.params.foldl (fun a p => addUniqueExpr a p.type) (addUniqueExpr acc decl.type)
    collectCodeTypeExprsLocal (collectCodeTypeExprsLocal acc1 decl.value) k
  | .cases c =>
    c.alts.foldl (fun a alt =>
      let a1 := match alt with
        | .alt _ ps _ _ => ps.foldl (fun s p => addUniqueExpr s p.type) a
        | _ => a
      collectCodeTypeExprsLocal a1 alt.getCode) (addUniqueExpr acc c.resultType)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    collectCodeTypeExprsLocal acc k
  | .jmp _ _ | .return _ | .unreach _ => acc

def collectLetValueCtorAndCalleeNamesLocal (ctors callees : List Name)
    (lv : LetValue .impure) : List Name × List Name :=
  match lv with
  | .ctor info _ _ | .reuse _ info _ _ _ => (addUniqueName ctors info.name, callees)
  | .fap fn _ _ | .pap fn _ _ => (ctors, addUniqueName callees fn)
  | _ => (ctors, callees)

partial def collectCodeCtorAndCalleeNamesLocal (ctors callees : List Name)
    (code : Code .impure) : List Name × List Name :=
  match code with
  | .let decl k =>
    let (c1, f1) := collectLetValueCtorAndCalleeNamesLocal ctors callees decl.value
    collectCodeCtorAndCalleeNamesLocal c1 f1 k
  | .jp decl k | .fun decl k _ =>
    let (c1, f1) := collectCodeCtorAndCalleeNamesLocal ctors callees decl.value
    collectCodeCtorAndCalleeNamesLocal c1 f1 k
  | .cases c =>
    c.alts.foldl (fun (cs, fs) alt =>
      let cs' := match alt with
        | .ctorAlt info _ _ => addUniqueName cs info.name
        | .alt cname _ _ _ => addUniqueName cs cname
        | .default _ => cs
      collectCodeCtorAndCalleeNamesLocal cs' fs alt.getCode) (ctors, callees)
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    collectCodeCtorAndCalleeNamesLocal ctors callees k
  | .jmp _ _ | .return _ | .unreach _ => (ctors, callees)

/-- Record the LCNF constructs exercised by an impure declaration body. -/
def collectLetValueConstructs (acc : List String) (lv : LetValue .impure) : List String :=
  match lv with
  | .lit (.uint8 _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_uint8"
  | .lit (.uint16 _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_uint16"
  | .lit (.uint32 _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_uint32"
  | .lit (.uint64 _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_uint64"
  | .lit (.usize _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_usize"
  | .lit (.nat _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_nat"
  | .lit (.str _) => addUniqueStr (addUniqueStr acc "let_lit") "lit_str"
  | .erased => addUniqueStr acc "let_erased"
  | .fvar _ args =>
    if args.isEmpty then addUniqueStr acc "let_fvar" else addUniqueStr acc "let_fvar_app"
  | .ctor info args _ =>
    let base := addUniqueStr acc "let_ctor"
    if args.isEmpty then addUniqueStr base "ctor_nullary"
    else if info.usize > 0 || info.ssize > 0 then addUniqueStr base "ctor_scalar_slots"
    else addUniqueStr base "ctor_obj_fields"
  | .reuse _ _ _ _ _ => addUniqueStr acc "let_reuse"
  | .oproj _ _ _ => addUniqueStr acc "let_oproj"
  | .uproj _ _ _ => addUniqueStr acc "let_uproj"
  | .sproj _ _ _ _ => addUniqueStr acc "let_sproj"
  | .fap fn _ _ =>
    let base := addUniqueStr acc "let_fap"
    if (RealLCNFBridge.lookupCanonicalTypedBinOp? fn).isSome then addUniqueStr base "fap_scalar_binop"
    else if fn == ``Bool.and || fn == ``Bool.or || fn == ``Bool.xor || fn == `Bool.bne || fn == `bne || fn == ``Bool.beq then
      addUniqueStr base "fap_bool_binop"
    else if fn == ``Bool.not || fn == ``Bool.toUInt8 || fn == ``Bool.toUInt16 || fn == ``Bool.toUInt32 || fn == ``Bool.toUInt64 || fn == ``Bool.toUSize then
      addUniqueStr base "fap_bool_unary_or_cast"
    else if fn == ``UInt8.complement || fn == ``UInt16.complement || fn == ``UInt32.complement || fn == ``UInt64.complement || fn == ``USize.complement ||
            fn == ``UInt8.neg || fn == ``UInt16.neg || fn == ``UInt32.neg || fn == ``UInt64.neg || fn == ``USize.neg then
      addUniqueStr base "fap_uint_unary"
    else if fn == ``ByteArray.usize || fn == ``ByteArray.uget || fn == ``FloatArray.usize || fn == ``FloatArray.uget then
      addUniqueStr base "fap_slice_op"
    else addUniqueStr base "fap_cast_or_other"
  | .pap _ _ _ => addUniqueStr acc "let_pap"
  | .isShared _ _ => addUniqueStr acc "let_isShared"
  | .box _ _ _ => addUniqueStr acc "let_box"
  | .unbox _ _ => addUniqueStr acc "let_unbox"
  | .reset _ _ _ => addUniqueStr acc "let_reset"

partial def collectCodeConstructs (acc : List String) (code : Code .impure) : List String :=
  match code with
  | .let decl k =>
    collectCodeConstructs (collectLetValueConstructs acc decl.value) k
  | .jp decl k =>
    let a1 := addUniqueStr acc "jp"
    collectCodeConstructs (collectCodeConstructs a1 decl.value) k
  | .jmp _ _ => addUniqueStr acc "jmp"
  | .cases c =>
    let a1 := addUniqueStr acc (if c.typeName == ``Bool then "cases_bool" else "cases_adt")
    c.alts.foldl (fun a alt =>
      let a2 := match alt with
        | .ctorAlt _ _ _ => addUniqueStr a "alt_ctor"
        | .alt _ _ _ _ => addUniqueStr a "alt_pure"
        | .default _ => addUniqueStr a "alt_default"
      collectCodeConstructs a2 alt.getCode) a1
  | .return _ => addUniqueStr acc "return"
  | .unreach _ => addUniqueStr acc "unreach"
  | .inc _ _ _ _ k _ => collectCodeConstructs (addUniqueStr acc "rc_inc") k
  | .dec _ _ _ _ _ k _ => collectCodeConstructs (addUniqueStr acc "rc_dec") k
  | .del _ k _ => collectCodeConstructs (addUniqueStr acc "rc_del") k
  | .oset _ _ _ k _ => collectCodeConstructs (addUniqueStr acc "heap_oset") k
  | .uset _ _ _ k _ => collectCodeConstructs (addUniqueStr acc "heap_uset") k
  | .sset _ _ _ _ _ k _ => collectCodeConstructs (addUniqueStr acc "heap_sset") k
  | .setTag _ _ k _ => collectCodeConstructs (addUniqueStr acc "heap_setTag") k
  | .fun decl k _ =>
    collectCodeConstructs (collectCodeConstructs (addUniqueStr acc "local_fun") decl.value) k

/-! ## High-Level Elaborated Type Classification & Value Bridging -/

/-- Supported high-level ground types for differential evaluation between stock Lean and `RealLCNFSemantics`. -/
inductive GroundDomType where
  | bool
  | uint8
  | uint16
  | uint32
  | uint64
  | usize
  | unit
  | enumInduct (indName : Name) (ctors : List (Name × Nat))
  | tupleStruct (indName : Name) (ctorName : Name) (fields : List GroundDomType)
  | rcAdt (indName : Name) (ctors : List (Name × Nat × List GroundDomType))
  deriving Repr, Inhabited

namespace GroundDomType

partial def toLNIRType : GroundDomType → LNIRType
  | .bool => .i1
  | .uint8 => .i8
  | .uint16 => .i16
  | .uint32 => .i32
  | .uint64 => .i64
  | .usize => .usize
  | .unit => .unit
  | .enumInduct _ _ => .i64
  | .tupleStruct _ _ fs => .tuple (fs.map toLNIRType)
  | .rcAdt _ _ => .objPtr

partial def usesRcAdt : GroundDomType → Bool
  | .rcAdt _ _ => true
  | .tupleStruct _ _ fs => fs.any usesRcAdt
  | _ => false

def toExprType : GroundDomType → Expr
  | .bool => mkConst ``Bool
  | .uint8 => mkConst ``UInt8
  | .uint16 => mkConst ``UInt16
  | .uint32 => mkConst ``UInt32
  | .uint64 => mkConst ``UInt64
  | .usize => mkConst ``USize
  | .unit => mkConst ``Unit
  | .enumInduct nm _ => mkConst nm
  | .tupleStruct nm _ _ => mkConst nm
  | .rcAdt nm _ => mkConst nm

end GroundDomType

/-- Classify an elaborated Lean `Expr` type into a `GroundDomType` if supported. -/
partial def classifyGroundDomType (env : Environment) (depth : Nat) (tyExpr : Expr) : Option GroundDomType := do
  guard (depth > 0)
  let e := tyExpr.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const nm _ =>
    if nm == ``Bool && args.isEmpty then some .bool
    else if nm == ``UInt8 && args.isEmpty then some .uint8
    else if nm == ``UInt16 && args.isEmpty then some .uint16
    else if nm == ``UInt32 && args.isEmpty then some .uint32
    else if nm == ``UInt64 && args.isEmpty then some .uint64
    else if nm == ``USize && args.isEmpty then some .usize
    else if (nm == ``Unit || nm == ``PUnit) && args.isEmpty then some .unit
    else if nm == ``Prod && args.size == 2 then
      let tA ← classifyGroundDomType env (depth - 1) args[0]!
      let tB ← classifyGroundDomType env (depth - 1) args[1]!
      guard (!tA.usesRcAdt && !tB.usesRcAdt)
      some (.tupleStruct ``Prod ``Prod.mk [tA, tB])
    else if args.isEmpty then
      match env.find? nm with
      | some (.inductInfo ival) =>
        if ival.isRec || ival.numParams > 0 || ival.numIndices > 0 || ival.ctors.isEmpty then
          none
        else
          let ctorInfos ← ival.ctors.mapM fun cn =>
            match env.find? cn with
            | some (.ctorInfo cval) => some (cn, cval)
            | _ => none
          if ctorInfos.all (fun (_, cv) => cv.numFields == 0) then
            some (.enumInduct nm (ctorInfos.map fun (cn, cv) => (cn, cv.cidx)))
          else if ctorInfos.length == 1 then
            let (cn, cv) := ctorInfos.head!
            if cv.numFields ≥ 1 && cv.numFields ≤ 8 then
              let fieldTys ← extractForallFieldTypes env (depth - 1) cv.type
              if fieldTys.all (fun ft => !ft.usesRcAdt) then
                some (.tupleStruct nm cn fieldTys)
              else
                none
            else none
          else
            let specs ← ctorInfos.mapM fun (cn, cv) => do
              guard (cv.numFields ≤ 8)
              let fieldTys ← extractForallFieldTypes env (depth - 1) cv.type
              guard (!fieldTys.any GroundDomType.usesRcAdt)
              return (cn, cv.cidx, fieldTys)
            some (.rcAdt nm specs)
      | _ => none
    else none
  | _ => none
where
  extractForallFieldTypes (env : Environment) (d : Nat) (e : Expr) : Option (List GroundDomType) :=
    match e.consumeMData with
    | .forallE _ dom body _ => do
      let ft ← classifyGroundDomType env d dom
      let rest ← extractForallFieldTypes env d body
      some (ft :: rest)
    | _ => some []

/-- Check whether an `Expr` type is `IO ...` or `BaseIO ...` or `EIO ...`. -/
partial def isIoTypeExpr (e : Expr) : Bool :=
  let rec go (cur : Expr) : Bool :=
    match cur.consumeMData with
    | .forallE _ _ b _ => go b
    | other =>
      match other.getAppFn.consumeMData with
      | .const nm _ =>
        nm == ``IO || nm == ``BaseIO || nm == ``EIO || nm == ``EST ||
        nm.toString.startsWith "IO." || nm.toString == "Lean.CoreM" || nm.toString == "Lean.MetaM"
      | _ => false
  go e

/-- Extract the parameter types and return type from a constant's elaborated signature in `MetaM`. -/
def classifyDeclSignatureM (declName : Name) (expectedArity : Nat) :
    CoreM (Except (SkipReason × String) (List GroundDomType × GroundDomType)) := do
  let env ← getEnv
  let some ci := env.find? declName
    | return .error (.externOrOpaque, "declaration not found in kernel environment")
  if isIoTypeExpr ci.type then
    return .error (.io, "declaration has IO / effectful return type")
  if !ci.hasValue then
    return .error (.externOrOpaque, "declaration has no kernel value (axiom/opaque/extern)")
  let metaAction : MetaM (Except (SkipReason × String) (List GroundDomType × GroundDomType)) :=
    Meta.forallBoundedTelescope ci.type (some expectedArity) fun xs bodyTy => do
      if xs.size != expectedArity then
        return .error (.higherOrderOrClosures, s!"telescope arity {xs.size} != LCNF param arity {expectedArity}")
      if isIoTypeExpr bodyTy then
        return .error (.io, "body type is IO")
      if bodyTy.isForall then
        return .error (.higherOrderOrClosures, "return type is a function / forall")
      let mut paramDoms : List GroundDomType := []
      for x in xs do
        let xTy ← Meta.inferType x
        let xTyWhnf ← Meta.whnfD xTy
        if xTyWhnf.isForall then
          return .error (.higherOrderOrClosures, "higher-order function parameter")
        match classifyGroundDomType env 4 xTy |>.orElse (fun _ => classifyGroundDomType env 4 xTyWhnf) with
        | some .usize =>
          return .error (.unsupportedType, "USize depends on opaque System.Platform.numBits in kernel reduction")
        | some dom => paramDoms := paramDoms ++ [dom]
        | none =>
          return .error (.unsupportedType, s!"unsupported parameter type `{ ← Meta.ppExpr xTy }`")
      let bodyTyWhnf ← Meta.whnfD bodyTy
      match classifyGroundDomType env 4 bodyTy |>.orElse (fun _ => classifyGroundDomType env 4 bodyTyWhnf) with
      | some .usize =>
        return .error (.unsupportedType, "USize depends on opaque System.Platform.numBits in kernel reduction")
      | some retDom => return .ok (paramDoms, retDom)
      | none =>
        return .error (.unsupportedType, s!"unsupported return type `{ ← Meta.ppExpr bodyTy }`")
  Prod.fst <$> metaAction.run {} {}

/-- A paired test value represented both as a Lean `Expr` and as a `RealLCNFSemantics` `(Val, HeapState → Val × HeapState)`. -/
structure BridgedVal where
  expr : Expr
  reprStr : String
  mkVal : HeapState → Except String (Val × HeapState)
  deriving Inhabited

/-- Canonical semantic representation for exact comparison between stock Lean and `RealLCNFSemantics`. -/
inductive CanonicalVal where
  | bool (b : Bool)
  | uint8 (v : UInt8)
  | uint16 (v : UInt16)
  | uint32 (v : UInt32)
  | uint64 (v : UInt64)
  | usize (v : UInt64)
  | unit
  | enumTag (indName : Name) (cidx : Nat)
  | tuple (fields : List CanonicalVal)
  | adtCtor (indName : Name) (ctorName : Name) (cidx : Nat) (fields : List CanonicalVal)
  deriving Repr, BEq, Inhabited

namespace CanonicalVal

partial def toString : CanonicalVal → String
  | .bool b => s!"Bool({b})"
  | .uint8 v => s!"UInt8({v.toNat})"
  | .uint16 v => s!"UInt16({v.toNat})"
  | .uint32 v => s!"UInt32({v.toNat})"
  | .uint64 v => s!"UInt64({v.toNat})"
  | .usize v => s!"USize({v.toNat})"
  | .unit => "Unit"
  | .enumTag ind cidx => s!"Enum({ind}#{cidx})"
  | .tuple fs => s!"Tuple({String.intercalate ", " (fs.map toString)})"
  | .adtCtor _ cn cidx fs =>
    if fs.isEmpty then s!"{cn}(#{cidx})"
    else s!"{cn}(#{cidx}; {String.intercalate ", " (fs.map toString)})"

end CanonicalVal

/-- Generate sample `BridgedVal` values for a `GroundDomType`. -/
partial def sampleValuesForDom (ctx : RealBridgeCtx) (dom : GroundDomType) : List BridgedVal :=
  match dom with
  | .bool =>
    [ { expr := mkConst ``Bool.false
      , reprStr := "false"
      , mkVal := fun st => .ok (.bool false, st) }
    , { expr := mkConst ``Bool.true
      , reprStr := "true"
      , mkVal := fun st => .ok (.bool true, st) } ]
  | .uint8 =>
    ([0, 1, 7, 42, 127, 128, 255] : List UInt8).map fun n =>
      { expr := toExpr n
      , reprStr := s!"{n.toNat}u8"
      , mkVal := fun st => .ok (.u64 n.toUInt64, st) }
  | .uint16 =>
    ([0, 1, 42, 255, 256, 32767, 65535] : List UInt16).map fun n =>
      { expr := toExpr n
      , reprStr := s!"{n.toNat}u16"
      , mkVal := fun st => .ok (.u64 n.toUInt64, st) }
  | .uint32 =>
    ([0, 1, 7, 42, 255, 65536, 0x7FFFFFFF, 0xFFFFFFFF] : List UInt32).map fun n =>
      { expr := toExpr n
      , reprStr := s!"{n.toNat}u32"
      , mkVal := fun st => .ok (.u64 n.toUInt64, st) }
  | .uint64 =>
    ([0, 1, 2, 7, 42, 255, 0x10107, 0xFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF] : List UInt64).map fun n =>
      { expr := toExpr n
      , reprStr := s!"{n}"
      , mkVal := fun st => .ok (.u64 n, st) }
  | .usize =>
    ([0, 1, 7, 42, 255, 1024] : List UInt64).map fun n =>
      { expr := mkApp (mkConst ``USize.ofNat) (mkNatLit n.toNat)
      , reprStr := s!"{n}usize"
      , mkVal := fun st => .ok (.u64 n, st) }
  | .unit =>
    [ { expr := mkConst ``Unit.unit
      , reprStr := "()"
      , mkVal := fun st => .ok (.u64 0, st) } ]
  | .enumInduct _ ctors =>
    ctors.map fun (cn, cidx) =>
      { expr := mkConst cn
      , reprStr := cn.toString
      , mkVal := fun st => .ok (.u64 cidx.toUInt64, st) }
  | .tupleStruct indName ctorName fields =>
    let perField := fields.map (sampleValuesForDom ctx)
    let combos := buildFieldCombos perField 4
    combos.map fun fvals =>
      let appExpr :=
        if indName == ``Prod && fvals.length == 2 then
          mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
            (GroundDomType.toExprType fields[0]!) (GroundDomType.toExprType fields[1]!) fvals[0]!.expr fvals[1]!.expr
        else
          fvals.foldl (fun acc fv => mkApp acc fv.expr) (mkConst ctorName)
      { expr := appExpr
      , reprStr := s!"({String.intercalate ", " (fvals.map (·.reprStr))})"
      , mkVal := fun st => do
          let mut curSt := st
          let mut vs : List Val := []
          for fv in fvals do
            let (v, st') ← fv.mkVal curSt
            curSt := st'
            vs := vs ++ [v]
          return (.tuple vs, curSt) }
  | .rcAdt indName ctors =>
    ctors.flatMap fun (cn, cidx, fields) =>
      if fields.isEmpty then
        [ { expr := mkConst cn
          , reprStr := cn.toString
          , mkVal := fun st => .ok (.u64 cidx.toUInt64, st) } ]
      else
        let perField := fields.map (sampleValuesForDom ctx)
        let combos := buildFieldCombos perField 2
        combos.map fun fvals =>
          let appExpr :=
            if indName == ``Prod && fvals.length == 2 then
              mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
                (GroundDomType.toExprType fields[0]!) (GroundDomType.toExprType fields[1]!) fvals[0]!.expr fvals[1]!.expr
            else
              fvals.foldl (fun acc fv => mkApp acc fv.expr) (mkConst cn)
          { expr := appExpr
          , reprStr := s!"{cn}({String.intercalate ", " (fvals.map (·.reprStr))})"
          , mkVal := fun st => do
              let some spec := ctx.findLayout? cn
                | throw s!"missing layout spec for {cn}"
              let mut curSt := st
              let mut fvs : List Val := []
              for fv in fvals do
                let (v, st') ← fv.mkVal curSt
                curSt := st'
                fvs := fvs ++ [v]
              -- Place object fields and scalar fields according to `spec`
              let mut objFields : List Val := List.replicate spec.objSlots (.u64 0)
              let mut scalarFields : List Val := List.replicate spec.scalarSlots.length (.u64 0)
              let mut objIdx := 0
              let mut scalarIdx := 0
              for (_, fv) in fields.zip fvals.zipIdx do
                let (_, fieldPos) := fv
                let val := fvs[fieldPos]!
                if objIdx < spec.objSlots then
                  objFields := objFields.set objIdx val
                  objIdx := objIdx + 1
                else if scalarIdx < scalarFields.length then
                  scalarFields := scalarFields.set scalarIdx val
                  scalarIdx := scalarIdx + 1
              let (objId, st') := curSt.allocHeapCtor cidx objFields scalarFields
              return (.objPtr objId, st') }
where
  buildFieldCombos (lists : List (List BridgedVal)) (maxCount : Nat) : List (List BridgedVal) :=
    match lists with
    | [] => [[]]
    | [xs] => (xs.take maxCount).map fun x => [x]
    | xs :: rest =>
      let tailCombos := buildFieldCombos rest maxCount
      let headItems := xs.take maxCount
      (List.range maxCount).filterMap fun i =>
        match headItems[i % headItems.length]?, tailCombos[i % tailCombos.length]? with
        | some h, some t => some (h :: t)
        | _, _ => none

/-- Decode a `RealLCNFSemantics` `(Val, HeapState)` into a `CanonicalVal` according to `GroundDomType`. -/
partial def decodeLCNFVal (ctx : RealBridgeCtx) (dom : GroundDomType) (v : Val) (st : HeapState) :
    Except String CanonicalVal :=
  match dom with
  | .bool =>
    match v with
    | .bool b => .ok (.bool b)
    | .u64 n => .ok (.bool ((n &&& 1) != 0))
    | other => .error s!"expected Bool from LCNF, got {reprStr other}"
  | .uint8 =>
    match v with
    | .u64 n => .ok (.uint8 (UInt8.ofNat (n &&& 0xFF).toNat))
    | other => .error s!"expected UInt8 from LCNF, got {reprStr other}"
  | .uint16 =>
    match v with
    | .u64 n => .ok (.uint16 (UInt16.ofNat (n &&& 0xFFFF).toNat))
    | other => .error s!"expected UInt16 from LCNF, got {reprStr other}"
  | .uint32 =>
    match v with
    | .u64 n => .ok (.uint32 (UInt32.ofNat (n &&& 0xFFFFFFFF).toNat))
    | other => .error s!"expected UInt32 from LCNF, got {reprStr other}"
  | .uint64 =>
    match v with
    | .u64 n => .ok (.uint64 n)
    | other => .error s!"expected UInt64 from LCNF, got {reprStr other}"
  | .usize =>
    match v with
    | .u64 n =>
      let masked := if ctx.arch.isILP32 then n &&& 0xFFFFFFFF else n
      .ok (.usize masked)
    | other => .error s!"expected USize from LCNF, got {reprStr other}"
  | .unit =>
    match v with
    | .u64 0 => .ok .unit
    | other => .error s!"expected Unit (.u64 0) from LCNF, got {reprStr other}"
  | .enumInduct indName _ =>
    match v with
    | .u64 n => .ok (.enumTag indName n.toNat)
    | .bool b => .ok (.enumTag indName (if b then 1 else 0))
    | other => .error s!"expected Enum tag from LCNF, got {reprStr other}"
  | .tupleStruct _ _ fields =>
    match fields with
    | [singleDom] =>
      match v with
      | .tuple [ elemVal ] => do
        let c ← decodeLCNFVal ctx singleDom elemVal st
        .ok (.tuple [c])
      | scalarVal => do
        -- Single-field wrapper struct unboxed by LCNF
        let c ← decodeLCNFVal ctx singleDom scalarVal st
        .ok (.tuple [c])
    | _ =>
      match v with
      | .tuple vs =>
        if vs.length != fields.length then
          .error s!"tuple length mismatch: got {vs.length}, expected {fields.length}"
        else do
          let mut out : List CanonicalVal := []
          for (fdom, fv) in fields.zip vs do
            let c ← decodeLCNFVal ctx fdom fv st
            out := out ++ [c]
          .ok (.tuple out)
      | .objPtr objId =>
        match st.liveHeapObj objId with
        | .error e => .error s!"invalid heap object {objId}: {reprStr e}"
        | .ok obj =>
          let rawFields := obj.objFields ++ obj.scalarFields
          if rawFields.length < fields.length then
            .error s!"heap struct field count mismatch: got {rawFields.length}, expected {fields.length}"
          else do
            let mut out : List CanonicalVal := []
            for (fdom, fv) in fields.zip (rawFields.take fields.length) do
              let c ← decodeLCNFVal ctx fdom fv st
              out := out ++ [c]
            .ok (.tuple out)
      | other => .error s!"expected tuple from LCNF, got {reprStr other}"
  | .rcAdt indName ctors =>
    match v with
    | .u64 n =>
      match ctors.find? (fun (_, cidx, fs) => cidx == n.toNat && fs.isEmpty) with
      | some (cn, cidx, _) => .ok (.adtCtor indName cn cidx [])
      | none => .error s!"unknown nullary ctor tag {n} for {indName}"
    | .objPtr objId =>
      match st.liveHeapObj objId with
      | .error e => .error s!"invalid heap object {objId}: {reprStr e}"
      | .ok obj =>
        match ctors.find? (fun (_, cidx, _) => cidx == obj.tag) with
        | none => .error s!"unknown heap ctor tag {obj.tag} for {indName}"
        | some (cn, cidx, fieldDoms) => do
          let mut out : List CanonicalVal := []
          for (fdom, idx) in fieldDoms.zipIdx do
            let rawFieldVal := (obj.objFields ++ obj.scalarFields)[idx]?.getD (.u64 0)
            let cv ← decodeLCNFVal ctx fdom rawFieldVal st
            out := out ++ [cv]
          .ok (.adtCtor indName cn cidx out)
    | other => .error s!"expected ADT value from LCNF, got {reprStr other}"

/-- Evaluate an expression using stock Lean (`Meta.whnf` / `Meta.reduce`) and decode into `CanonicalVal`. -/
partial def evalAndDecodeStockLeanM (arch : TargetArch) (dom : GroundDomType) (e : Expr) :
    MetaM (Except String CanonicalVal) := do
  let decodeNatExpr (t : Expr) : MetaM (Option Nat) := do
    let t' ← Meta.whnf t
    if let some n := t'.rawNatLit? then return some n
    if let some n := evalClosedNatExpr? t' then return some n
    let tRed ← Meta.reduce t' (explicitOnly := false)
    if let some n := tRed.rawNatLit? then return some n
    return evalClosedNatExpr? tRed
  match dom with
  | .bool =>
    let e' ← Meta.whnf e
    if e'.isConstOf ``Bool.true then return .ok (.bool true)
    else if e'.isConstOf ``Bool.false then return .ok (.bool false)
    else
      let eRed ← Meta.reduce e' (explicitOnly := false)
      if eRed.isConstOf ``Bool.true then return .ok (.bool true)
      else if eRed.isConstOf ``Bool.false then return .ok (.bool false)
      else return .error s!"stock Lean did not reduce Bool expression to true/false: {← Meta.ppExpr eRed}"
  | .uint8 =>
    let toNatExpr := mkApp (mkConst ``UInt8.toNat) e
    match ← decodeNatExpr toNatExpr with
    | some n => return .ok (.uint8 (UInt8.ofNat (n % 256)))
    | none => return .error s!"stock Lean did not reduce UInt8.toNat: {← Meta.ppExpr e}"
  | .uint16 =>
    let toNatExpr := mkApp (mkConst ``UInt16.toNat) e
    match ← decodeNatExpr toNatExpr with
    | some n => return .ok (.uint16 (UInt16.ofNat (n % 65536)))
    | none => return .error s!"stock Lean did not reduce UInt16.toNat: {← Meta.ppExpr e}"
  | .uint32 =>
    let toNatExpr := mkApp (mkConst ``UInt32.toNat) e
    match ← decodeNatExpr toNatExpr with
    | some n => return .ok (.uint32 (UInt32.ofNat (n % 4294967296)))
    | none => return .error s!"stock Lean did not reduce UInt32.toNat: {← Meta.ppExpr e}"
  | .uint64 =>
    let toNatExpr := mkApp (mkConst ``UInt64.toNat) e
    match ← decodeNatExpr toNatExpr with
    | some n => return .ok (.uint64 (UInt64.ofNat (n % (2 ^ 64))))
    | none => return .error s!"stock Lean did not reduce UInt64.toNat: {← Meta.ppExpr e}"
  | .usize =>
    let toNatExpr := mkApp (mkConst ``USize.toNat) e
    match ← decodeNatExpr toNatExpr with
    | some n =>
      let modulus := if arch.isILP32 then 2 ^ 32 else 2 ^ 64
      return .ok (.usize (UInt64.ofNat (n % modulus)))
    | none => return .error s!"stock Lean did not reduce USize.toNat: {← Meta.ppExpr e}"
  | .unit =>
    let e' ← Meta.whnf e
    if e'.isConstOf ``Unit.unit || e'.isConstOf ``PUnit.unit then return .ok .unit
    else return .error s!"stock Lean did not reduce Unit expression: {← Meta.ppExpr e'}"
  | .enumInduct indName ctors =>
    let e' ← Meta.whnf e
    let fn := e'.getAppFn.consumeMData
    match fn with
    | .const cn _ =>
      match ctors.find? (fun (c, _) => c == cn) with
      | some (_, cidx) => return .ok (.enumTag indName cidx)
      | none => return .error s!"stock Lean reduced {indName} to unexpected constant {cn}"
    | _ => return .error s!"stock Lean did not reduce enum {indName}: {← Meta.ppExpr e'}"
  | .tupleStruct _ ctorName fieldDoms =>
    let e' ← Meta.whnf e
    let fn := e'.getAppFn.consumeMData
    let args := e'.getAppArgs.toList
    if !fn.isConstOf ctorName || args.length < fieldDoms.length then
      return .error s!"stock Lean did not reduce tuple struct {ctorName}: {← Meta.ppExpr e'}"
    else
      let fieldArgs := args.drop (args.length - fieldDoms.length)
      let mut out : List CanonicalVal := []
      for (fdom, fexpr) in fieldDoms.zip fieldArgs do
        match ← evalAndDecodeStockLeanM arch fdom fexpr with
        | .ok cv => out := out ++ [cv]
        | .error err => return .error err
      return .ok (.tuple out)
  | .rcAdt indName ctors =>
    let e' ← Meta.whnf e
    let fn := e'.getAppFn.consumeMData
    let args := e'.getAppArgs.toList
    match fn with
    | .const cn _ =>
      match ctors.find? (fun (c, _, _) => c == cn) with
      | none => return .error s!"stock Lean reduced {indName} to unknown ctor {cn}"
      | some (_, cidx, fieldDoms) =>
        if args.length < fieldDoms.length then
          return .error s!"stock Lean ctor {cn} has fewer args ({args.length}) than fields ({fieldDoms.length})"
        let fieldArgs := args.drop (args.length - fieldDoms.length)
        let mut out : List CanonicalVal := []
        for (fdom, fexpr) in fieldDoms.zip fieldArgs do
          match ← evalAndDecodeStockLeanM arch fdom fexpr with
          | .ok cv => out := out ++ [cv]
          | .error err => return .error err
        return .ok (.adtCtor indName cn cidx out)
    | _ => return .error s!"stock Lean did not reduce ADT {indName}: {← Meta.ppExpr e'}"
where
  evalClosedNatExpr? (e : Expr) : Option Nat :=
    let e := e.consumeMData
    if let some n := e.rawNatLit? then some n
    else
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs.toList
      if fn.isConstOf ``Nat.zero && args.isEmpty then some 0
      else if fn.isConstOf ``Nat.succ && args.length == 1 then (evalClosedNatExpr? args[0]!).map (· + 1)
      else if fn.isConstOf ``OfNat.ofNat && args.length ≥ 2 then args[1]!.rawNatLit?
      else none

/-! ## Declaration Pre-Check & Context Construction -/

/-- Inspect an impure LCNF declaration to see if it uses constructs outside `RealLCNFSemantics`'s domain. -/
partial def findUnsupportedImpureConstruct? (ctx : RealBridgeCtx) (selfName : Name) (code : Code .impure)
    (isSharedVars : List FVarId := []) : Option (SkipReason × String) :=
  match code with
  | .let decl k =>
    match checkLetValue decl.value with
    | some err => some err
    | none =>
      let isSharedVars' := match decl.value with
        | .isShared _ _ => decl.fvarId :: isSharedVars
        | _ => isSharedVars
      findUnsupportedImpureConstruct? ctx selfName k isSharedVars'
  | .jp decl k =>
    if hasJmpToPure (codeAstFuel decl.value + 16) decl.fvarId (.inl decl.value) then
      some (.unsupportedConstruct, s!"recursive join point `{decl.binderName}`")
    else
      match findUnsupportedImpureConstruct? ctx selfName decl.value isSharedVars with
      | some err => some err
      | none => findUnsupportedImpureConstruct? ctx selfName k isSharedVars
  | .fun decl _ _ =>
    some (.higherOrderOrClosures, s!"local function declaration `{decl.binderName}`")
  | .cases c =>
    if c.typeName == ``Bool && isSharedVars.contains c.discr then
      some (.unsupportedConstruct, "reset/reuse cases on UInt8 isShared with Bool typeName")
    else
      c.alts.foldl (fun acc alt =>
        match acc with
        | some err => some err
        | none => findUnsupportedImpureConstruct? ctx selfName alt.getCode isSharedVars) none
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ | .oset _ _ _ k _ =>
    findUnsupportedImpureConstruct? ctx selfName k isSharedVars
  | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    if !ctx.allowStage1DHeap then
      some (.unsupportedConstruct, "heap scalar/tag mutation requires Stage 1D heap mode")
    else
      findUnsupportedImpureConstruct? ctx selfName k isSharedVars
  | .jmp _ _ | .return _ => none
  | .unreach _ => none
where
  checkLetValue (lv : LetValue .impure) : Option (SkipReason × String) :=
    match lv with
    | .lit (.str _) => some (.unsupportedConstruct, "string literal")
    | .lit (.nat _) => none
    | .lit _ => none
    | .erased => none
    | .fvar _ args =>
      if args.isEmpty then none
      else some (.higherOrderOrClosures, "higher-order fvar application")
    | .pap fn _ _ =>
      some (.higherOrderOrClosures, s!"partial application `pap {fn}`")
    | .ctor info args _ | .reuse _ info _ args _ =>
      if args.isEmpty then none
      else if (ctx.findTupleArity? info.name).isSome then none
      else if ctx.allowStage1DHeap && (ctx.findLayout? info.name).isSome then none
      else some (.unsupportedConstruct, s!"constructor `{info.name}` requires unsupported heap layout")
    | .oproj _ _ _ | .uproj _ _ _ | .sproj _ _ _ _ => none
    | .isShared _ _ | .box _ _ _ | .unbox _ _ | .reset _ _ _ => none
    | .fap fn args _ =>
      if fn == selfName then
        some (.unsupportedConstruct, s!"recursive call to `{fn}`")
      else if (ctx.findLocalCallee? fn).isSome then
        some (.unsupportedConstruct, s!"inter-procedural call to local declaration `{fn}`")
      else if isSupportedFapIntrinsic ctx fn args.size then
        none
      else
        some (.unsupportedConstruct, s!"external/library call `{fn}` (arity {args.size})")
  isSupportedFapIntrinsic (ctx : RealBridgeCtx) (fn : Name) (arity : Nat) : Bool :=
    if arity == 2 then
      (ctx.findGfSimd? fn).isSome ||
      (RealLCNFBridge.lookupCanonicalTypedBinOp? fn).isSome ||
      fn == ``Bool.and || fn == ``Bool.or || fn == ``Bool.xor || fn == `Bool.bne || fn == `bne || fn == ``Bool.beq
    else if arity == 1 then
      fn == ``Bool.not ||
      fn == ``Bool.toUInt8 || fn == ``Bool.toUInt16 || fn == ``Bool.toUInt32 || fn == ``Bool.toUInt64 || fn == ``Bool.toUSize ||
      fn == ``UInt8.complement || fn == ``UInt16.complement || fn == ``UInt32.complement || fn == ``UInt64.complement || fn == ``USize.complement ||
      fn == ``UInt8.neg || fn == ``UInt16.neg || fn == ``UInt32.neg || fn == ``UInt64.neg || fn == ``USize.neg ||
      isSupportedUIntCastFn ctx.arch fn
    else false
  isSupportedUIntCastFn (arch : TargetArch) (fn : Name) : Bool :=
    let prims : List (Name × String) :=
      [(``UInt8, "toUInt8"), (``UInt16, "toUInt16"), (``UInt32, "toUInt32"), (``UInt64, "toUInt64")] ++
      (if archSupportsUSize arch then [(``USize, "toUSize")] else [])
    prims.any fun (src, _) =>
      prims.any fun (dst, suf) => src != dst && fn == Name.str src suf

/-- Check whether a declaration name is an internal compiler/elaborator auxiliary rather than a user declaration. -/
def isInternalCompilerAuxName (nm : Name) : Bool :=
  let s := nm.toString
  nm.isInternal ||
  s.endsWith "._cstage1" || s.endsWith "._cstage2" || s.endsWith "._closed_1" ||
  (s.splitOn "._closed_").length > 1 || (s.splitOn "._lambda_").length > 1 ||
  s.endsWith ".rec" || s.endsWith ".recOn" || s.endsWith ".casesOn" ||
  s.endsWith ".noConfusion" || s.endsWith ".noConfusionType" ||
  s.endsWith ".ctorIdx" || s.endsWith ".toCtorIdx" || s.endsWith ".elim" ||
  s.startsWith "instDecidableEq" || s.startsWith "instRepr" || s.startsWith "instInhabited" ||
  (s.splitOn ".instDecidableEq").length > 1 || (s.splitOn ".instRepr").length > 1 ||
  (s.splitOn ".instInhabited").length > 1 || (s.splitOn ".beq").length > 1 ||
  (s.splitOn ".repr").length > 1

/-- Check whether `code` performs `.cases` on a given `FVarId`. -/
partial def codeHasCasesOnFVar (target : FVarId) (code : Code .impure) : Bool :=
  match code with
  | .let _ k | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ =>
    codeHasCasesOnFVar target k
  | .jp decl k | .fun decl k _ =>
    codeHasCasesOnFVar target decl.value || codeHasCasesOnFVar target k
  | .cases c =>
    c.discr == target || c.alts.any (fun alt => codeHasCasesOnFVar target alt.getCode)
  | .jmp _ _ | .return _ | .unreach _ => false

/-- Check whether `code` performs heap-layout operations (`.sproj`, `.uproj`, `.uset`, `.sset`, `.setTag`, `.del`) on a given `FVarId`. -/
partial def codeUsesHeapLayoutOnFVar (target : FVarId) (code : Code .impure) : Bool :=
  match code with
  | .let decl k =>
    let hit := match decl.value with
      | .uproj _ x _ | .sproj _ _ x _ => x == target
      | _ => false
    hit || codeUsesHeapLayoutOnFVar target k
  | .uset x _ _ k _ | .sset x _ _ _ _ k _ | .setTag x _ k _ | .del x k _ =>
    x == target || codeUsesHeapLayoutOnFVar target k
  | .oset _ _ _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ =>
    codeUsesHeapLayoutOnFVar target k
  | .jp decl k | .fun decl k _ =>
    codeUsesHeapLayoutOnFVar target decl.value || codeUsesHeapLayoutOnFVar target k
  | .cases c =>
    c.alts.any (fun alt => codeUsesHeapLayoutOnFVar target alt.getCode)
  | .jmp _ _ | .return _ | .unreach _ => false

/-- Check whether `code` performs any heap-only mutation (`.oset`, `.uset`, `.sset`, `.setTag`) on any variable. -/
partial def codeHasAnyHeapMutation (code : Code .impure) : Bool :=
  match code with
  | .let decl k =>
    let hit := match decl.value with
      | .ctor info _ _ => info.usize > 0 || info.ssize > 0
      | _ => false
    hit || codeHasAnyHeapMutation k
  | .oset _ _ _ _ _ | .uset _ _ _ _ _ | .sset _ _ _ _ _ _ _ | .setTag _ _ _ _ => true
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ => codeHasAnyHeapMutation k
  | .jp decl k | .fun decl k _ => codeHasAnyHeapMutation decl.value || codeHasAnyHeapMutation k
  | .cases c => c.alts.any (fun alt => codeHasAnyHeapMutation alt.getCode)
  | .jmp _ _ | .return _ | .unreach _ => false

/-- Build a `RealBridgeCtx` for an elaborated `Decl .impure` using `BridgeHelpers.buildRealBridgeCtxM`. -/
def buildEvalBridgeCtxM (decl : Decl .impure) (paramDoms : List GroundDomType)
    (localDeclNames : Array Name) (arch : TargetArch) (allowStage1DHeap : Bool) :
    CoreM (RealBridgeCtx × List GroundDomType) := do
  let env ← getEnv
  let metaInfo := getLCNFDeclMetadata env decl.name
  let mut adjustedParamDoms : List GroundDomType := []
  let mut useHeap := allowStage1DHeap
  let mut paramTypeMap : List (FVarId × LNIRType) := []
  let mut extraKnownCtors : List (FVarId × Name) := []
  let mut extraCtorSeeds : List Name := []
  let bodyCode? := match decl.value with | .code c => some c | .extern _ => none
  for (p, dom) in decl.params.toList.zip paramDoms do
    match dom, bodyCode? with
    | .tupleStruct indName ctorName fields, some c =>
      if indName != ``Prod && (codeHasCasesOnFVar p.fvarId c || codeUsesHeapLayoutOnFVar p.fvarId c) then
        useHeap := true
        let rcDom := GroundDomType.rcAdt indName [(ctorName, 0, fields)]
        adjustedParamDoms := adjustedParamDoms ++ [rcDom]
        paramTypeMap := paramTypeMap ++ [(p.fvarId, .objPtr)]
        extraKnownCtors := extraKnownCtors ++ [(p.fvarId, ctorName)]
        extraCtorSeeds := extraCtorSeeds ++ [ctorName]
      else
        adjustedParamDoms := adjustedParamDoms ++ [dom]
        paramTypeMap := paramTypeMap ++ [(p.fvarId, dom.toLNIRType)]
    | .rcAdt _ ctors, _ =>
      useHeap := true
      adjustedParamDoms := adjustedParamDoms ++ [dom]
      paramTypeMap := paramTypeMap ++ [(p.fvarId, .objPtr)]
      for (cn, _, _) in ctors do
        extraCtorSeeds := extraCtorSeeds ++ [cn]
      if ctors.length == 1 then
        extraKnownCtors := extraKnownCtors ++ [(p.fvarId, ctors[0]!.1)]
    | _, _ =>
      adjustedParamDoms := adjustedParamDoms ++ [dom]
      paramTypeMap := paramTypeMap ++ [(p.fvarId, dom.toLNIRType)]
  let initSt : BridgeState := {
    mangledSymbol := metaInfo.mangledSymbol
    isSimpleGround := metaInfo.isSimpleGround
    selfDeclName := decl.name
    localDeclNames := localDeclNames
    arch := arch
    allowStage1DHeap := useHeap
  }
  let action : BridgeM RealBridgeCtx := do
    match decl.value with
    | .extern _ => return { arch := arch, allowStage1DHeap := useHeap }
    | .code c =>
      let knownCtors := collectFVarCtors c
      let allKnown := knownCtors.toList ++ extraKnownCtors
      let typeExprs := decl.type :: (decl.params.toList.map (·.type) ++ collectCodeTypeExprsLocal [] c)
      let (ctors, callees) := collectCodeCtorAndCalleeNamesLocal [] [] c
      buildRealBridgeCtxM typeExprs (ctors ++ allKnown.map Prod.snd ++ extraCtorSeeds)
        callees paramTypeMap allKnown
  let ctx ← Prod.fst <$> action.run initSt
  return (ctx, adjustedParamDoms)

/-- Build input test vectors across all parameters of a declaration. -/
def buildInputVectors (ctx : RealBridgeCtx) (paramDoms : List GroundDomType) (maxVectors : Nat := 12) :
    List (List BridgedVal) :=
  match paramDoms with
  | [] => [[]]
  | [d0] => (sampleValuesForDom ctx d0).take maxVectors |>.map (fun v => [v])
  | [d0, d1] =>
    let s0 := sampleValuesForDom ctx d0
    let s1 := sampleValuesForDom ctx d1
    let pairs := (s0.take 4).flatMap fun a => (s1.take 3).map fun b => [a, b]
    pairs.take maxVectors
  | d0 :: rest =>
    let s0 := sampleValuesForDom ctx d0
    let restVecs := buildInputVectors ctx rest maxVectors
    let total := max s0.length restVecs.length
    (List.range (min maxVectors total)).filterMap fun i =>
      match s0[i % s0.length]?, restVecs[i % restVecs.length]? with
      | some h, some t => some (h :: t)
      | _, _ => none

/-- Differential evaluation of a single elaborated `Decl .impure` against stock Lean. -/
def evaluateDeclDifferentialM (decl : Decl .impure) (localDeclNames : Array Name)
    (arch : TargetArch := .x86_64) (fuel : Nat := 4096) : CoreM DeclEvalOutcome := do
  let env ← getEnv
  if isInternalCompilerAuxName decl.name then
    return .skipped decl.name.toString .internalCompilerAux "compiler/elaborator auxiliary declaration"
  let metaInfo := getLCNFDeclMetadata env decl.name
  if metaInfo.isExtern then
    return .skipped decl.name.toString .externOrOpaque "@[extern] declaration"
  match decl.value with
  | .extern _ =>
    return .skipped decl.name.toString .externOrOpaque "extern LCNF declaration body"
  | .code code =>
    if ← declUsesSignedScalarTransitively decl then
      return .skipped decl.name.toString .unsupportedType "uses signed integer type (Int* / ISize)"
    match ← classifyDeclSignatureM decl.name decl.params.size with
    | .error (reason, detail) =>
      return .skipped decl.name.toString reason detail
    | .ok (paramDoms, retDom) =>
      let needHeap := paramDoms.any GroundDomType.usesRcAdt || retDom.usesRcAdt
      let (ctx, effParamDoms) ← buildEvalBridgeCtxM decl paramDoms localDeclNames arch needHeap
      if let some (reason, detail) := findUnsupportedImpureConstruct? ctx decl.name code then
        return .skipped decl.name.toString reason detail
      let constructs := collectCodeConstructs [] code
      let vectors := buildInputVectors ctx effParamDoms 12
      if vectors.isEmpty then
        return .skipped decl.name.toString .unsupportedType "no test vectors generated for parameter types"
      let mut mismatches : List VectorMismatch := []
      let mut comparedVecs : Nat := 0
      for vec in vectors do
        let argsRepr := "[" ++ String.intercalate ", " (vec.map (·.reprStr)) ++ "]"
        -- Build initial heap and Val list for RealLCNFSemantics
        let mut initSt := HeapState.empty
        let mut argVals : List Val := []
        let mut argBuildErr? : Option String := none
        for bv in vec do
          match bv.mkVal initSt with
          | .ok (v, st') =>
            initSt := st'
            argVals := argVals ++ [v]
          | .error err =>
            argBuildErr? := some err
        match argBuildErr? with
        | some err =>
          mismatches := mismatches ++ [{
            declName := decl.name.toString
            argsRepr := argsRepr
            lcnfResult := s!"arg_build_error({err})"
            stockLeanResult := "n/a"
          }]
        | none =>
          let lcnfRes := evalRealLCNFDecl fuel ctx decl argVals initSt
          let appExpr := vec.foldl (fun acc bv => mkApp acc bv.expr) (mkConst decl.name)
          let stockRes ← Prod.fst <$> (evalAndDecodeStockLeanM arch retDom appExpr).run {} {}
          comparedVecs := comparedVecs + 1
          let mkMismatch (lStr sStr : String) : VectorMismatch :=
            { declName := decl.name.toString, argsRepr := argsRepr, lcnfResult := lStr, stockLeanResult := sStr }
          match lcnfRes, stockRes with
          | .ok (vOut, stOut), .ok stockCanon =>
            match decodeLCNFVal ctx retDom vOut stOut with
            | .ok lcnfCanon =>
              if lcnfCanon != stockCanon then
                mismatches := mismatches ++ [mkMismatch lcnfCanon.toString stockCanon.toString]
            | .error decodeErr =>
              mismatches := mismatches ++ [mkMismatch s!"decode_error({decodeErr}; raw={reprStr vOut})" stockCanon.toString]
          | .error ubErr, .ok stockCanon =>
            mismatches := mismatches ++ [mkMismatch s!"lcnf_error({reprStr ubErr})" stockCanon.toString]
          | .ok (vOut, stOut), .error stockErr =>
            let lcnfStr := match decodeLCNFVal ctx retDom vOut stOut with
              | .ok c => c.toString
              | .error e => s!"decode_error({e})"
            mismatches := mismatches ++ [mkMismatch lcnfStr s!"stock_lean_error({stockErr})"]
          | .error ubErr, .error stockErr =>
            mismatches := mismatches ++ [mkMismatch s!"lcnf_error({reprStr ubErr})" s!"stock_lean_error({stockErr})"]
      return .compared decl.name.toString comparedVecs constructs mismatches

/-- Aggregate a list of `DeclEvalOutcome`s into a `DiffReport`. -/
def summarizeOutcomes (sourceDescription : String) (outcomes : List DeclEvalOutcome) : DiffReport := Id.run do
  let mut comparedCount := 0
  let mut comparedVectors := 0
  let mut skippedCount := 0
  let mut reasonCounts : List (String × Nat) := SkipReason.all.map (fun r => (r.toKey, 0))
  let mut mismatches : List VectorMismatch := []
  let mut constructCounts : List (String × Nat) := []
  let mut comparedDecls : List String := []
  let mut skippedDecls : List (String × String × String) := []
  for o in outcomes do
    match o with
    | .compared dName vecCnt constructs ms =>
      comparedCount := comparedCount + 1
      comparedVectors := comparedVectors + vecCnt
      comparedDecls := comparedDecls ++ [dName]
      mismatches := mismatches ++ ms
      for c in constructs do
        if constructCounts.any (fun (k, _) => k == c) then
          constructCounts := constructCounts.map fun (k, n) => if k == c then (k, n + 1) else (k, n)
        else
          constructCounts := constructCounts ++ [(c, 1)]
    | .skipped dName reason detail =>
      skippedCount := skippedCount + 1
      let rKey := reason.toKey
      reasonCounts := reasonCounts.map fun (k, n) => if k == rKey then (k, n + 1) else (k, n)
      skippedDecls := skippedDecls ++ [(dName, rKey, detail)]
  return {
    schema := 1
    sourceDescription := sourceDescription
    totalDecls := outcomes.length
    comparedCount := comparedCount
    comparedVectors := comparedVectors
    skippedCount := skippedCount
    skippedByReason := reasonCounts.filter (fun (_, n) => n > 0)
    mismatchCount := mismatches.length
    mismatches := mismatches
    constructsCovered := constructCounts
    comparedDecls := comparedDecls
    skippedDecls := skippedDecls
  }

/-- Render a `DiffReport` as JSON. -/
def DiffReport.toJson (r : DiffReport) : Json :=
  Json.mkObj [
    ("schema", Lean.toJson r.schema),
    ("source", Json.str r.sourceDescription),
    ("total_decls", Lean.toJson r.totalDecls),
    ("compared_count", Lean.toJson r.comparedCount),
    ("compared_vectors", Lean.toJson r.comparedVectors),
    ("skipped_count", Lean.toJson r.skippedCount),
    ("skipped_by_reason", Json.mkObj (r.skippedByReason.map fun (k, v) => (k, Lean.toJson v))),
    ("mismatch_count", Lean.toJson r.mismatchCount),
    ("mismatches", Json.arr (r.mismatches.map fun m =>
      Json.mkObj [
        ("decl", Json.str m.declName),
        ("args", Json.str m.argsRepr),
        ("lcnf_result", Json.str m.lcnfResult),
        ("stock_lean_result", Json.str m.stockLeanResult)
      ]).toArray),
    ("constructs_covered", Json.mkObj (r.constructsCovered.map fun (k, v) => (k, Lean.toJson v))),
    ("compared_decls", Json.arr (r.comparedDecls.map Json.str).toArray),
    ("skipped_decls", Json.arr (r.skippedDecls.map fun (d, rsn, det) =>
      Json.mkObj [
        ("decl", Json.str d),
        ("reason", Json.str rsn),
        ("detail", Json.str det)
      ]).toArray)
  ]

/-- Format a human-readable summary of a `DiffReport`. -/
def DiffReport.formatSummary (r : DiffReport) : String := Id.run do
  let skipParts := r.skippedByReason.map fun (k, v) => s!"{k}={v}"
  let constructParts := r.constructsCovered.map fun (k, v) => s!"{k}:{v}"
  let mut lines : List String := [
    s!"[eval-lcnf] source: {r.sourceDescription}",
    s!"[eval-lcnf] total_decls={r.totalDecls} compared_count={r.comparedCount} compared_vectors={r.comparedVectors} skipped_count={r.skippedCount} mismatch_count={r.mismatchCount}",
    s!"[eval-lcnf] skipped_by_reason: {if skipParts.isEmpty then "none" else String.intercalate ", " skipParts}",
    s!"[eval-lcnf] constructs_covered ({r.constructsCovered.length}): {String.intercalate ", " constructParts}"
  ]
  for m in r.mismatches do
    lines := lines ++ [
      s!"[eval-lcnf] MISMATCH in {m.declName}{m.argsRepr}: lcnf={m.lcnfResult} vs stock_lean={m.stockLeanResult}"
    ]
  return String.intercalate "\n" lines

/-! ## Built-in Corpus of Real Elaborated LCNF Declarations -/

namespace BuiltinCorpus

/-- Multi-constructor enum inductive for `cases` / nullary constructor testing. -/
inductive TrafficLight where
  | red
  | yellow
  | green
  deriving DecidableEq, Repr

/-- Single-constructor product structure for tuple allocation and `.oproj`/`.uproj`/`.sproj` testing. -/
structure WordPair where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, Repr

/-- 1. 64-bit arithmetic, bitwise, shift, division-by-zero, and modulo-by-zero semantics. -/
@[noinline] def u64ArithMix (a b : UInt64) : UInt64 :=
  let sum := a + b
  let diff := sum - (a &&& b)
  let prod := diff * (b ||| 1)
  let xored := prod ^^^ (a <<< (b &&& 7))
  let shifted := xored + (a >>> (b &&& 3))
  let q := a / b
  let r := a % b
  shifted ^^^ q ^^^ r

/-- 2. Narrow unsigned widths (`UInt8`, `UInt16`, `UInt32`) with overflow masking and shifts. -/
@[noinline] def u8OverflowAndShift (a b : UInt8) : UInt8 :=
  let s := a + b
  let m := s * (b ||| 3)
  let sh := (a <<< (b &&& 3)) ^^^ (b >>> 1)
  (m - sh) ^^^ (a / b) ^^^ (a % b)

@[noinline] def u16BitwiseMix (a b : UInt16) : UInt16 :=
  ((a + b) &&& (0xFF0F : UInt16)) ||| ((a ^^^ b) >>> 2)

@[noinline] def u32ArithDivMod (a b : UInt32) : UInt32 :=
  (a * b) + (a / b) - (a % b)

/-- 3. Cross-width unsigned casts (`toUInt8`, `toUInt16`, `toUInt32`, `toUInt64`, `toUSize`) and unary ops (`complement`, `neg`). -/
@[noinline] def uintCastAndUnaryRoundtrip (x : UInt64) : UInt64 :=
  let b8 : UInt8 := ~~~(x.toUInt8)
  let b16 : UInt16 := -(b8.toUInt16 + x.toUInt16)
  let b32 : UInt32 := ~~~(b16.toUInt32 ^^^ x.toUInt32)
  let b64 : UInt64 := -(b32.toUInt64)
  b64 + b8.toUInt64

/-- 4. 32/64-bit aligned address calculation with cross-width casts and shifts. -/
@[noinline] def usizeAddressCalc (base : UInt64) (offset : UInt32) : UInt64 :=
  let ext := offset.toUInt64
  let aligned := (base + ext) &&& (0xFFFFFFFFFFFFFFF8 : UInt64)
  aligned ^^^ (ext >>> 2)

/-- 5. Boolean operations, comparisons (`==`, `<`, `≤`), `Bool.not`, and `Bool.toUInt64`. -/
@[noinline] def boolLogicAndCmp (a b : UInt64) (flag : Bool) : UInt64 :=
  let c1 := a < b
  let c2 := a ≤ b
  let c3 := a == b
  let comb := (c1 && !flag) || (c2 != c3)
  if comb then
    comb.toUInt64 + a
  else
    (!comb).toUInt64 + b

/-- 6. Join points (`jp` / `jmp`) via multi-branch conditionals sharing a continuation. -/
@[noinline] def multiBranchJoinPoint (x y : UInt64) : UInt64 :=
  let step1 :=
    if x < 10 then
      y + 100
    else if x < 100 then
      y * 3 + x
    else
      y ^^^ x
  let step2 :=
    if step1 &&& 1 == 0 then
      step1 >>> 1
    else
      step1 * 3 + 1
  step2 + x

/-- 7. Enum inductive pattern matching (`cases` on multi-constructor enum & nullary constructors). -/
@[noinline] def nextTrafficLight (t : TrafficLight) : TrafficLight :=
  match t with
  | .red => .green
  | .green => .yellow
  | .yellow => .red

@[noinline] def trafficLightWaitSeconds (t : TrafficLight) (rushHour : Bool) : UInt64 :=
  match t with
  | .red => if rushHour then 90 else 60
  | .yellow => 5
  | .green => if rushHour then 75 else 45

/-- 8. Tuple / `Prod` construction and projection. -/
@[noinline] def swapAndCombinePair (p : @& (UInt64 × UInt64)) : UInt64 × UInt64 :=
  (p.2 + p.1, p.1 ^^^ p.2)

@[noinline] def wordPairChecksum (w : WordPair) : UInt64 :=
  (w.lo + w.hi) ^^^ (w.lo >>> 3)

/-- 9. Deliberately skipped declarations to verify skip-reason accounting (`non_computable`, `io`, `higher_order_or_closures`, `unsupported_construct`). -/
noncomputable def skippedNonComputableWitness (x : UInt64) : UInt64 :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : UInt64, y = x)

def skippedIoActionWitness (x : UInt64) : IO UInt64 :=
  pure (x + 1)

@[noinline] def skippedHigherOrderWitness (f : UInt64 → UInt64) (x : UInt64) : UInt64 :=
  f (x + 1)

@[noinline] def skippedUnsupportedCallWitness (x : UInt64) : UInt64 :=
  (toString x).length.toUInt64

def builtinComparedDeclNames : Array Name := #[
  ``u64ArithMix,
  ``u8OverflowAndShift,
  ``u16BitwiseMix,
  ``u32ArithDivMod,
  ``uintCastAndUnaryRoundtrip,
  ``usizeAddressCalc,
  ``boolLogicAndCmp,
  ``multiBranchJoinPoint,
  ``nextTrafficLight,
  ``trafficLightWaitSeconds,
  ``swapAndCombinePair,
  ``wordPairChecksum
]

def builtinSkippedDeclNames : Array Name := #[
  ``skippedIoActionWitness,
  ``skippedHigherOrderWitness,
  ``skippedUnsupportedCallWitness
]

def builtinAllDeclNames : Array Name :=
  builtinComparedDeclNames ++ builtinSkippedDeclNames

end BuiltinCorpus

/-! ## Running on Built-in Corpus or External `.lean` Source Files -/

/-- Run differential evaluation over an explicit list of declaration names in the current `CoreM` environment. -/
def runDifferentialOnDeclNamesM (sourceDesc : String) (declNames : Array Name)
    (arch : TargetArch := .x86_64) (fuel : Nat := 4096) : CoreM DiffReport := do
  let env ← getEnv
  let mut outcomes : List DeclEvalOutcome := []
  for nm in declNames do
    match ← getLocalImpureDecl? nm with
    | some impDecl =>
      let o ← evaluateDeclDifferentialM impDecl declNames arch fuel
      outcomes := outcomes ++ [o]
    | none =>
      let redName := Name.str nm "_redArg"
      match ← getLocalImpureDecl? redName with
      | some redDecl =>
        -- If `_redArg` has the same parameter arity as the user declaration, evaluate it under the user declaration name
        let o ← evaluateDeclDifferentialM { redDecl with name := nm } declNames arch fuel
        outcomes := outcomes ++ [o]
      | none =>
        match env.find? nm with
        | none =>
          outcomes := outcomes ++ [.skipped nm.toString .externOrOpaque "declaration not found in environment"]
        | some ci =>
          if isIoTypeExpr ci.type then
            outcomes := outcomes ++ [.skipped nm.toString .io "IO declaration"]
          else if !ci.hasValue then
            outcomes := outcomes ++ [.skipped nm.toString .externOrOpaque "axiom/opaque declaration"]
          else
            outcomes := outcomes ++ [.skipped nm.toString .nonComputable "no impure LCNF code (noncomputable or type/proof declaration)"]
  return summarizeOutcomes sourceDesc outcomes

/-- Elaborate an in-memory Lean 4 snippet and run `act` inside `CoreM`. -/
def withElaboratedSnippet {α : Type} (snippetName : String) (sourceText : String)
    (modName : Lean.Name) (act : Lean.CoreM α) : IO α := do
  unsafe Lean.enableInitializersExecution
  let mut extraPaths : Lean.SearchPath := []
  for cand in [
    ".lake/build/lib/lean",
    ".lake/packages/lean-sys/.lake/build/lib/lean",
    "lean/.lake/build/lib/lean",
    "lean/.lake/packages/lean-sys/.lake/build/lib/lean",
    "build/olean"
  ] do
    let p := System.FilePath.mk cand
    if ← p.pathExists then
      extraPaths := extraPaths ++ [p]
  Lean.initSearchPath (← LeanNative.IR.resolveLeanSysroot) extraPaths
  let opts : Lean.Options := {}
  let some env ← Lean.Elab.runFrontend sourceText opts snippetName modName
    | throw <| IO.userError s!"Elaboration failed for {snippetName}"
  let coreCtx : Lean.Core.Context := { fileName := snippetName, fileMap := sourceText.toFileMap, options := opts }
  Prod.fst <$> act.toIO coreCtx { env := env }

/-- Run differential evaluation on a `.lean` source file by elaborating it through the Lean frontend. -/
def runDifferentialOnSourceFile (sourcePath : String) (onlyDecl? : Option String := none)
    (arch : TargetArch := .x86_64) (fuel : Nat := 4096) : IO DiffReport := do
  let sourceText ← IO.FS.readFile sourcePath
  withElaboratedSnippet sourcePath sourceText `EvalLCNFInput do
    let impureNames ← getLocalImpureDecls
    let env ← getEnv
    let filteredImpure := impureNames.filter (fun n => !isCompilerGeneratedAuxDecl env n && !isInternalCompilerAuxName n)
    let extraNames := env.constants.map₂.foldl (fun acc name ci =>
      if impureNames.contains name || isCompilerGeneratedAuxDecl env name || isInternalCompilerAuxName name then acc
      else if ci matches .defnInfo _ || ci matches .opaqueInfo _ || ci matches .axiomInfo _ then acc.push name
      else acc) #[]
    let allNames := (filteredImpure ++ extraNames).filter fun nm =>
      match onlyDecl? with
      | none => true
      | some target => nm.toString == target || nm.toString.endsWith ("." ++ target)
    runDifferentialOnDeclNamesM sourcePath allNames arch fuel

/-- Run the built-in differential corpus inside `CoreM` by elaborating a self-contained Lean 4 source module. -/
def builtinCorpusLeanSource : String :=
"namespace LeanNative.Driver.EvalLCNFCLI.BuiltinCorpus

inductive TrafficLight where
  | red
  | yellow
  | green
  deriving DecidableEq, Repr

structure WordPair where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, Repr

@[noinline] def u64ArithMix (a b : UInt64) : UInt64 :=
  let sum := a + b
  let diff := sum - (a &&& b)
  let prod := diff * (b ||| 1)
  let xored := prod ^^^ (a <<< (b &&& 7))
  let shifted := xored + (a >>> (b &&& 3))
  let q := a / b
  let r := a % b
  shifted ^^^ q ^^^ r

@[noinline] def u8OverflowAndShift (a b : UInt8) : UInt8 :=
  let s := a + b
  let m := s * (b ||| 3)
  let sh := (a <<< (b &&& 3)) ^^^ (b >>> 1)
  (m - sh) ^^^ (a / b) ^^^ (a % b)

@[noinline] def u16BitwiseMix (a b : UInt16) : UInt16 :=
  ((a + b) &&& (0xFF0F : UInt16)) ||| ((a ^^^ b) >>> 2)

@[noinline] def u32ArithDivMod (a b : UInt32) : UInt32 :=
  (a * b) + (a / b) - (a % b)

@[noinline] def uintCastAndUnaryRoundtrip (x : UInt64) : UInt64 :=
  let b8 : UInt8 := ~~~(x.toUInt8)
  let b16 : UInt16 := -(b8.toUInt16 + x.toUInt16)
  let b32 : UInt32 := ~~~(b16.toUInt32 ^^^ x.toUInt32)
  let b64 : UInt64 := -(b32.toUInt64)
  b64 + b8.toUInt64

@[noinline] def usizeAddressCalc (base : UInt64) (offset : UInt32) : UInt64 :=
  let ext := offset.toUInt64
  let aligned := (base + ext) &&& (0xFFFFFFFFFFFFFFF8 : UInt64)
  aligned ^^^ (ext >>> 2)

@[noinline] def boolLogicAndCmp (a b : UInt64) (flag : Bool) : UInt64 :=
  let c1 := a < b
  let c2 := a ≤ b
  let c3 := a == b
  let comb := (c1 && !flag) || (c2 != c3)
  if comb then
    comb.toUInt64 + a
  else
    (!comb).toUInt64 + b

@[noinline] def multiBranchJoinPoint (x y : UInt64) : UInt64 :=
  let step1 :=
    if x < 10 then
      y + 100
    else if x < 100 then
      y * 3 + x
    else
      y ^^^ x
  let step2 :=
    if step1 &&& 1 == 0 then
      step1 >>> 1
    else
      step1 * 3 + 1
  step2 + x

@[noinline] def nextTrafficLight (t : TrafficLight) : TrafficLight :=
  match t with
  | .red => .green
  | .green => .yellow
  | .yellow => .red

@[noinline] def trafficLightWaitSeconds (t : TrafficLight) (rushHour : Bool) : UInt64 :=
  match t with
  | .red => if rushHour then 90 else 60
  | .yellow => 5
  | .green => if rushHour then 75 else 45

@[noinline] def swapAndCombinePair (p : @& (UInt64 × UInt64)) : UInt64 × UInt64 :=
  (p.2 + p.1, p.1 ^^^ p.2)

@[noinline] def wordPairChecksum (w : WordPair) : UInt64 :=
  (w.lo + w.hi) ^^^ (w.lo >>> 3)

noncomputable def skippedNonComputableWitness (x : UInt64) : UInt64 :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : UInt64, y = x)

def skippedIoActionWitness (x : UInt64) : IO UInt64 :=
  pure (x + 1)

@[noinline] def skippedHigherOrderWitness (f : UInt64 → UInt64) (x : UInt64) : UInt64 :=
  f (x + 1)

@[noinline] def skippedUnsupportedCallWitness (x : UInt64) : UInt64 :=
  (toString x).length.toUInt64

end LeanNative.Driver.EvalLCNFCLI.BuiltinCorpus
"

/-- Run the built-in differential corpus inside `CoreM`. -/
def runBuiltinCorpusM (arch : TargetArch := .x86_64) (fuel : Nat := 4096) : CoreM DiffReport := do
  runDifferentialOnDeclNamesM "BuiltinCorpus"
    (BuiltinCorpus.builtinAllDeclNames.push ``BuiltinCorpus.skippedNonComputableWitness) arch fuel

/-- Execute `runBuiltinCorpusM` inside `IO` by elaborating `builtinCorpusLeanSource`. -/
def runBuiltinCorpusIO (arch : TargetArch := .x86_64) (fuel : Nat := 4096) : IO DiffReport := do
  withElaboratedSnippet "<BuiltinCorpus>" builtinCorpusLeanSource `BuiltinCorpus do
    runBuiltinCorpusM arch fuel

/-! ## CLI Entrypoint -/

private def hasFlag (args : List String) (flag : String) : Bool :=
  args.contains flag

private def findFlagValue? (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | f :: v :: rest => if f == flag then some v else findFlagValue? (v :: rest) flag
  | _ :: rest => findFlagValue? rest flag

private def positionalSourceFiles (args : List String) : List String :=
  let rec go : List String → List String
    | [] => []
    | "--decl" :: _ :: rest => go rest
    | "--fuel" :: _ :: rest => go rest
    | "--arch" :: _ :: rest => go rest
    | a :: rest =>
      if a.startsWith "-" then go rest
      else a :: go rest
  go args

def printUsage : IO Unit := do
  IO.println "Usage: lean-native eval-lcnf [--json] [--self-test] [--decl <name>] [--fuel <n>] [<file.lean> ...]"
  IO.println "  Evaluates LCNF (.impure) declarations with RealLCNFSemantics and compares each result"
  IO.println "  against stock Lean evaluation, reporting compared_count, skipped_count (by reason),"
  IO.println "  mismatch_count, and constructs_covered."

def run (args : List String) : IO UInt32 := do
  if hasFlag args "--help" || hasFlag args "-h" then
    printUsage
    return 0
  let jsonOut := hasFlag args "--json"
  let onlyDecl? := findFlagValue? args "--decl"
  let fuel := (findFlagValue? args "--fuel" >>= String.toNat?).getD 4096
  let files := positionalSourceFiles args
  let reports ←
    if files.isEmpty then
      let rep ← runBuiltinCorpusIO .x86_64 fuel
      pure [rep]
    else
      files.mapM fun f => runDifferentialOnSourceFile f onlyDecl? .x86_64 fuel
  let totalMismatchCount := reports.foldl (fun acc r => acc + r.mismatchCount) 0
  let totalComparedCount := reports.foldl (fun acc r => acc + r.comparedCount) 0
  if jsonOut then
    match reports with
    | [single] => IO.println (Json.compress single.toJson)
    | many =>
      let merged := Json.mkObj [
        ("schema", Lean.toJson (1 : Nat)),
        ("mismatch_count", Lean.toJson totalMismatchCount),
        ("compared_count", Lean.toJson totalComparedCount),
        ("reports", Json.arr (many.map DiffReport.toJson).toArray)
      ]
      IO.println (Json.compress merged)
  else
    for rep in reports do
      IO.println rep.formatSummary
  return if totalMismatchCount == 0 && totalComparedCount > 0 then 0 else 1

end LeanNative.Driver.EvalLCNFCLI
