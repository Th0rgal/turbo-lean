import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.ToImpureType
import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFSemantics
import LeanNative.IR.BridgeHelpers
import LeanNative.IR.Bridge
import LeanNative.Transform.EqSat
import LeanNative.Semantics.Eval
import LeanNative.Proofs.RealLCNFBridgeProofs
import LeanNative.Proofs.SymbolicTV

namespace LeanNative.Tests.RealLCNFBridgeTests

open Lean
open Lean.Compiler.LCNF
open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

private def fv (n : Nat) : FVarId := { name := .num `x n }

private def mkParam (n : Nat) (ty : Expr) (borrow : Bool := false) : Param .impure :=
  { fvarId := fv n, binderName := .num `p n, type := ty, borrow := borrow }

private def mkLet (n : Nat) (ty : Expr) (val : LetValue .impure) : LetDecl .impure :=
  { fvarId := fv n, binderName := .num `v n, type := ty, value := val }

private def mkDecl (name : Name) (params : Array (Param .impure)) (retTy : Expr)
    (body : Code .impure) : Decl .impure :=
  { name := name
    levelParams := []
    type := retTy
    params := params
    value := .code body
    inlineAttr? := none }

private def evalLoweredDecl (fuel : Nat) (d : LNIRDecl) (args : List Val)
    (hst : HeapState := HeapState.empty) : Except UBError (Val × HeapState) :=
  let venv := (d.params.zip args).foldl (fun acc (p, val) => acc.bind p.id val) VarEnv.empty
  evalCode fuel venv hst d.body

private def checkDeclParity (fuel : Nat) (ctx : RealBridgeCtx) (decl : Decl .impure)
    (args : List Val) (expected : Val) : Bool :=
  match lowerRealLCNFDecl fuel ctx decl, evalRealLCNFDecl fuel ctx decl args with
  | .ok lnir, .ok (vSrc, hstSrc) =>
    match evalLoweredDecl fuel lnir args with
    | .ok (vTgt, hstTgt) => vSrc == expected && vTgt == expected && hstSrc == hstTgt
    | .error _ => false
  | _, _ => false

/-- Test 1: 8-bit arithmetic wraparound, division-by-zero total semantics, and narrow cast. -/
private def u8ArithDecl : Decl .impure :=
  let u8 := ImpureType.uint8
  let u32 := ImpureType.uint32
  mkDecl `test_u8_arith #[mkParam 1 u8, mkParam 2 u8] u32 <|
    .let (mkLet 3 u8 (.fap ``UInt8.add #[.fvar (fv 1), .fvar (fv 2)] rfl)) <|
    .let (mkLet 4 u8 (.lit (.uint8 0))) <|
    .let (mkLet 5 u8 (.fap ``UInt8.div #[.fvar (fv 3), .fvar (fv 4)] rfl)) <|
    .let (mkLet 6 u8 (.fap ``UInt8.add #[.fvar (fv 3), .fvar (fv 5)] rfl)) <|
    .let (mkLet 7 u32 (.fap ``UInt8.toUInt32 #[.fvar (fv 6)] rfl)) <|
    .return (fv 7)

#guard checkDeclParity 32 { arch := .x86_64 } u8ArithDecl [.u64 250, .u64 10] (.u64 4)

/-- Test 2: Boolean `cases` branch ordering (`Bool` tag 0 = false, tag 1 = true) + non-recursive `jp`/`jmp`. -/
private def boolJpDecl : Decl .impure :=
  let u64 := ImpureType.uint64
  let bTy := mkConst ``Bool
  let jpDecl : FunDecl .impure :=
    FunDecl.mk (fv 10) `jp_merge #[mkParam 11 u64] u64 <|
      .let (mkLet 12 u64 (.lit (.uint64 7))) <|
      .let (mkLet 13 u64 (.fap ``UInt64.add #[.fvar (fv 11), .fvar (fv 12)] rfl)) <|
      .return (fv 13)
  let falseBr : Code .impure :=
    .let (mkLet 20 u64 (.lit (.uint64 100))) <|
    .jmp (fv 10) #[.fvar (fv 20)]
  let trueBr : Code .impure :=
    .let (mkLet 21 u64 (.lit (.uint64 200))) <|
    .jmp (fv 10) #[.fvar (fv 21)]
  mkDecl `test_bool_jp #[mkParam 1 u64, mkParam 2 u64] u64 <|
    .jp jpDecl <|
    .let (mkLet 3 bTy (.fap `UInt64.blt #[.fvar (fv 1), .fvar (fv 2)] rfl)) <|
    .cases (Cases.mk ``Bool u64 (fv 3) #[
      .ctorAlt { name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 } falseBr rfl,
      .ctorAlt { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 } trueBr rfl
    ])

#guard checkDeclParity 32 { arch := .x86_64 } boolJpDecl [.u64 3, .u64 9] (.u64 207)
#guard checkDeclParity 32 { arch := .x86_64 } boolJpDecl [.u64 9, .u64 3] (.u64 107)

/-- Test 3: Stage 1D heap ADT constructor allocation, `oset`, `setTag`, `cases` tag dispatch, and `dec` cleanup. -/
private def objBoxSpec0 : RealLCNFBridge.RcCtorLayoutSpec :=
  { ctorName := `ObjBox.left, cidx := 0, objSlots := 1, usizeSlots := 0, scalarSlots := [] }

private def objBoxSpec1 : RealLCNFBridge.RcCtorLayoutSpec :=
  { ctorName := `ObjBox.right, cidx := 1, objSlots := 1, usizeSlots := 0, scalarSlots := [] }

private def objHeapCtx : RealBridgeCtx :=
  { arch := .x86_64
    allowStage1DHeap := true
    ctorLayouts := [(`ObjBox.left, objBoxSpec0), (`ObjBox.right, objBoxSpec1)] }

private def objHeapLifecycleDecl : Decl .impure :=
  let obj := ImpureType.object
  let u64 := ImpureType.uint64
  let ci0 : CtorInfo := { name := `ObjBox.left, cidx := 0, size := 1, usize := 0, ssize := 0 }
  let ci1 : CtorInfo := { name := `ObjBox.right, cidx := 1, size := 1, usize := 0, ssize := 0 }
  let branch0 : Code .impure :=
    .let (mkLet 10 u64 (.lit (.uint64 11))) <|
    .dec (fv 4) 1 true false none (.return (fv 10)) rfl
  let branch1 : Code .impure :=
    .let (mkLet 11 obj (.oproj 0 (fv 4) rfl)) <|
    .let (mkLet 12 u64 (.unbox (fv 11) rfl)) <|
    .dec (fv 4) 1 true false none (.return (fv 12)) rfl
  mkDecl `test_obj_heap_lifecycle #[mkParam 1 u64, mkParam 2 u64] u64 <|
    .let (mkLet 3 obj (.box u64 (fv 1) rfl)) <|
    .let (mkLet 4 obj (.ctor ci0 #[.fvar (fv 3)] rfl)) <|
    .let (mkLet 5 obj (.box u64 (fv 2) rfl)) <|
    .oset (fv 4) 0 (.fvar (fv 5))
      (.setTag (fv 4) 1
        (.cases (Cases.mk `ObjBox u64 (fv 4) #[
          .ctorAlt ci0 branch0 rfl,
          .ctorAlt ci1 branch1 rfl,
          .default branch0
        ])) rfl) rfl

#guard checkDeclParity 32 objHeapCtx objHeapLifecycleDecl [.u64 42, .u64 99] (.u64 99)

/-- Test 4: Flat tuple (`Prod UInt64 UInt64`) construction and projection parity. -/
private def prodDecl : Decl .impure :=
  let u64 := ImpureType.uint64
  let prodTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``UInt64) (mkConst ``UInt64)
  let prodCi : CtorInfo := { name := ``Prod.mk, cidx := 0, size := 2, usize := 0, ssize := 0 }
  mkDecl `test_prod_tuple #[mkParam 1 u64, mkParam 2 u64] u64 <|
    .let (mkLet 3 prodTy (.ctor prodCi #[.erased, .erased, .fvar (fv 1), .fvar (fv 2)] rfl)) <|
    .let (mkLet 4 u64 (.oproj 0 (fv 3) rfl)) <|
    .let (mkLet 5 u64 (.oproj 1 (fv 3) rfl)) <|
    .let (mkLet 6 u64 (.fap ``UInt64.sub #[.fvar (fv 4), .fvar (fv 5)] rfl)) <|
    .return (fv 6)

#guard checkDeclParity 32 { arch := .x86_64 } prodDecl [.u64 55, .u64 13] (.u64 42)

/-- Test 5: Fail-closed rejection on recursive join points and unsupported `@[extern]` declarations. -/
private def recJpDecl : Decl .impure :=
  let u64 := ImpureType.uint64
  let jpDecl : FunDecl .impure :=
    FunDecl.mk (fv 10) `jp_loop #[mkParam 11 u64] u64 (.jmp (fv 10) #[.fvar (fv 11)])
  mkDecl `test_rec_jp #[mkParam 1 u64] u64 <|
    .jp jpDecl (.jmp (fv 10) #[.fvar (fv 1)])

#guard (lowerRealLCNFDecl 32 { arch := .x86_64 } recJpDecl).isOk == false

/-! ### L1: explicit requests fail closed

An explicitly requested declaration whose constant kind carries compiled code (a computable
`defnInfo`/`opaqueInfo`) but that the Stage 1B ingest cannot lower raises a named
`Unsupported` error instead of being dropped silently — the "imported declarations are
outside" wording for an imported name, "no impure LCNF form" for a local one; a constant
with no compiled code (here: a theorem) is skipped silently. Red evidence, both recorded in
the PR's commit history: one earlier revision accepted `UInt64.add` as an EMPTY module;
a later one accepted the LOCAL type-alias case below as an empty module too. -/

private theorem l1NonCodeProbe : True := trivial

/-- A local `def` with a compiled-code kind but no runtime code: `defnInfo`, computable,
    and the LCNF pipeline compiles no impure form for a `Type`-valued definition
    (measured on this branch). -/
private def l1TypeAliasProbe : Type := UInt64

private def expectIngestThrows (names : Array Lean.Name) (tag expected : String) :
    Lean.CoreM Unit := do
  let threw ← try
    let _ ← ingestModuleDecls names tag .x86_64 false
    pure false
  catch e =>
    let msg ← e.toMessageData.toString
    unless (msg.splitOn expected).length > 1 do
      Lean.throwError s!"wrong rejection ({tag}): {msg}"
    pure true
  unless threw do
    Lean.throwError s!"ingestModuleDecls accepted an explicit request it must refuse ({tag})"

#eval show Lean.CoreM Unit from do
  -- imported computable def: its home module may well have an impure form; this ingest
  -- sees only the current module's, so the request fails closed with the real reason
  expectIngestThrows #[``UInt64.add] "l1_f4_imported" "imported declarations are outside"
  -- local declaration with a compiled-code kind but no impure LCNF form
  expectIngestThrows #[``l1TypeAliasProbe] "l1_f4_local" "no impure LCNF form"
  -- a constant with no compiled code stays silently skipped
  let m ← ingestModuleDecls #[``l1NonCodeProbe] "l1_f4_noncode" .x86_64 false
  unless m.decls.isEmpty do
    Lean.throwError "non-code constant unexpectedly lowered"

private def evalDeclProduces (fuel : Nat) (d : LNIRDecl) (args : List Val) (expected : Val) : Bool :=
  match evalLoweredDecl fuel d args with
  | .ok (v, hst) => v == expected && hst == HeapState.empty
  | .error _ => false

/-- Test 6: Regression against branch-local `letBind` shadowing outer parameters in
    `flattenInlinedHelperBody` and `normalizeAndInlineLocalDefs`. -/
private def shadowedIteDecl : LNIRDecl :=
  { name := "test_shadowed_ite"
    params := [{ id := 0, name := "cond", ty := .i1 }, { id := 1, name := "x", ty := .i64 }]
    retTy := .i64
    body := .ite 0 (.letBind 1 .i64 (.scalar (.constU64 999)) (.ret 1)) (.ret 1) }

#guard evalDeclProduces 16 shadowedIteDecl [.bool false, .u64 42] (.u64 42)
#guard evalDeclProduces 16 (flattenInlinedHelperBody shadowedIteDecl) [.bool false, .u64 42] (.u64 42)
#guard evalDeclProduces 16 (flattenInlinedHelperBody shadowedIteDecl) [.bool true, .u64 42] (.u64 999)

private def shadowedTupleIteDecl : LNIRDecl :=
  { name := "test_shadowed_tuple_ite"
    params := [{ id := 0, name := "cond", ty := .i1 }, { id := 1, name := "x", ty := .i64 }]
    retTy := .tuple [.i64, .i64]
    body := .ite 0
      (.letBind 1 .i64 (.scalar (.constU64 999))
        (.letBind 2 (.tuple [.i64, .i64]) (.mkTuple [1, 1]) (.ret 2)))
      (.letBind 3 (.tuple [.i64, .i64]) (.mkTuple [1, 1]) (.ret 3)) }

#guard evalDeclProduces 16 (flattenInlinedHelperBody shadowedTupleIteDecl) [.bool false, .u64 42]
  (.tuple [.u64 42, .u64 42])
#guard evalDeclProduces 16 (flattenInlinedHelperBody shadowedTupleIteDecl) [.bool true, .u64 42]
  (.tuple [.u64 999, .u64 999])

private def shadowedInlineMod : LNIRModule :=
  normalizeAndInlineLocalDefs
    { moduleName := "shadowed_inline_mod"
      decls := [
        shadowedIteDecl,
        { name := "caller"
          params := [{ id := 0, name := "c", ty := .i1 }, { id := 1, name := "y", ty := .i64 }]
          retTy := .i64
          body := .letBind 2 .i64 (.call "test_shadowed_ite" [0, 1] .i64 false) (.ret 2) }
      ] }

#guard
  match shadowedInlineMod.decls.find? (·.name == "caller") with
  | some d =>
    evalDeclProduces 16 d [.bool false, .u64 42] (.u64 42) &&
    evalDeclProduces 16 d [.bool true, .u64 42] (.u64 999)
  | none => false

end LeanNative.Tests.RealLCNFBridgeTests
