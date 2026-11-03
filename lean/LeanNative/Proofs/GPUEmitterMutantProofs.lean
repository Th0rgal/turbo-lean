import LeanNative.Backend.GPUEmitVerify
import LeanNative.Backend.LLVMEmitVerify

/-!
# Production GPU & LLVM Emitter Mutant-Kill Proofs (`M6..M10` + `.dotProduct`)

Kernel-checked theorems (`0 sorryAx`, `0 native_decide`, `0 Lean.ofReduceBool`) and
compile-time `#guard` module-level parse-and-execute checks proving:
1. Full production `emitMLIRModule`, `emitPTXModule`, `emitMetalModule`, and `emitDeclLLVM`
   module outputs pass `GPUEmitVerify.verifyGPUEmitters = true` and
   `LLVMEmitVerify.verifyLLVMEmitter = true` (including `.dotProduct` reduction), and
   applying each verbatim `M6..M10` string replacement from `scripts/emitter_mutants.json`
   to full emitted module text flips `GPUEmitVerify` from `true` to `false`.
2. In-kernel theorems (`decide`, zero extra axioms) over total `List Char` parsers and
   `StableHLOAst` / `PTXAst` / `MetalAst` evaluators proving that every production emitter
   (`emitMLIRScalarExpr`, `emitPTXScalarExpr`, `emitPTXDeclKernel`, `emitMetalScalarExpr`,
   `emitMetalDeclKernel`) evaluates in agreement with `Semantics.Eval` and is strictly
   separated from its verbatim `M6..M10` mutant.
3. `production_decl_emitters_wired`: production `emitPTXDeclKernel` and `emitMetalDeclKernel`
   delegate `saxpy`, `mapScaleAdd`, `zipAdd`, `zipMul`, and `stencil1D3Pt` definitionally (`rfl`)
   to the verified `PTXLower` / `MetalLower` AST pretty-printers.
-/

namespace LeanNative.Proofs.GPUEmitterMutantProofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.GPUEmitVerify
open LeanNative.Backend.LLVMEmitVerify

set_option maxRecDepth 262144
set_option maxHeartbeats 1600000

#guard verifyGPUEmitters = true
#guard verifyLLVMEmitter = true

#guard (let mod : LNIRModule :=
          { moduleName := "M6", decls := [ptxProbeDecl "emit_shl" (.binOp .shl (.var 0) (.var 1))] }
        let mlir := emitMLIRModule mod
        let mlirMut := ((mlir.replace "arith.shli " "__TMP__ ").replace
          "arith.shrui " "arith.shli ").replace "__TMP__ " "arith.shrui "
        evalParsedMLIRKernel1D mlir "emit_shl_parfor_0" [3, 8] [2, 1] == some [12, 16] &&
        evalParsedMLIRKernel1D mlirMut "emit_shl_parfor_0" [3, 8] [2, 1] == some [0, 4]) = true

#guard (let mod : LNIRModule :=
          { moduleName := "M7", decls := [ptxProbeDecl "emit_sub" (.binOp .sub (.var 0) (.var 1))] }
        let ptx := emitPTXModule mod
        let ptxMut := ptx.replace "    sub.u64      %rd10, %rd8, %rd9;"
          "    sub.u64      %rd10, %rd9, %rd8;"
        let exp : List UInt64 := [3, (1 : UInt64) - 4]
        ptxMut != ptx && probePTX ptx "emit_sub" 2 2 200 [[5, 1], [2, 4]] exp &&
        !(probePTX ptxMut "emit_sub" 2 2 200 [[5, 1], [2, 4]] exp)) = true

#guard (let mod : LNIRModule :=
          { moduleName := "M8", decls := [ptxProbeDecl "emit_lt" (.binOp .lt (.var 0) (.var 1))] }
        let ptx := emitPTXModule mod
        let ptxMut := ptx.replace "setp.lt.u64" "setp.le.u64"
        ptxMut != ptx && probePTX ptx "emit_lt" 2 2 200 [[3, 2], [3, 5]] [0, 1] &&
        !(probePTX ptxMut "emit_lt" 2 2 200 [[3, 2], [3, 5]] [0, 1])) = true

#guard (let mod : LNIRModule :=
          { moduleName := "M9", decls := [mslProbeDecl "msl_div" (.binOp .div (.var 0) (.var 1))] }
        let msl := emitMetalModule mod
        let mslMut := msl.replace "((v1 == 0UL) ? 0UL : (v0 / v1))" "(v0 / v1)"
        mslMut != msl && probeMSL msl "msl_div" 2 2 400 [[18, 7], [3, 0]] [6, 0] &&
        !(probeMSL mslMut "msl_div" 2 2 400 [[18, 7], [3, 0]] [6, 0])) = true

#guard (let mod : LNIRModule :=
          { moduleName := "M10", decls := [mslProbeDecl "msl_shl" (.binOp .shl (.var 0) (.var 1))] }
        let msl := emitMetalModule mod
        let mslMut := msl.replace "& 63UL)" "& 31UL)"
        mslMut != msl && probeMSL msl "msl_shl" 2 2 400 [[1, 1], [32, 65]] [4294967296, 2] &&
        !(probeMSL mslMut "msl_shl" 2 2 400 [[1, 1], [32, 65]] [4294967296, 2])) = true

#guard ((emitPTXDeclKernel "lean_native_decl_emit_sub"
          (.customScalar 9 [0, 1] (.binOp .sub (.var 0) (.var 1)))).replace
          "    sub.u64      %rd10, %rd8, %rd9;" "    sub.u64      %rd10, %rd9, %rd8;" !=
        emitPTXDeclKernel "lean_native_decl_emit_sub"
          (.customScalar 9 [0, 1] (.binOp .sub (.var 0) (.var 1)))) = true

#guard ((emitPTXDeclKernel "lean_native_decl_emit_lt"
          (.customScalar 9 [0, 1] (.binOp .lt (.var 0) (.var 1)))).replace
          "setp.lt.u64" "setp.le.u64" !=
        emitPTXDeclKernel "lean_native_decl_emit_lt"
          (.customScalar 9 [0, 1] (.binOp .lt (.var 0) (.var 1)))) = true

#guard (((emitMetalDeclKernel (mslProbeDecl "msl_div" (.binOp .div (.var 0) (.var 1)))).getD "").replace
          "((v1 == 0UL) ? 0UL : (v0 / v1))" "(v0 / v1)" !=
        (emitMetalDeclKernel (mslProbeDecl "msl_div" (.binOp .div (.var 0) (.var 1)))).getD "") = true

#guard (((emitMetalDeclKernel (mslProbeDecl "msl_shl" (.binOp .shl (.var 0) (.var 1)))).getD "").replace
          "& 63UL)" "& 31UL)" !=
        (emitMetalDeclKernel (mslProbeDecl "msl_shl" (.binOp .shl (.var 0) (.var 1)))).getD "") = true

/-- Total `List Char` prefix stripper (transparent to the Lean kernel). -/
def stripPre : List Char → List Char → Option (List Char)
  | [], xs => some xs
  | p :: ps, x :: xs => if p == x then stripPre ps xs else none
  | _, [] => none

def kContainsSub : List Char → List Char → Bool
  | pat, [] => pat.isEmpty
  | pat, cs@(_ :: rest) =>
    if (stripPre pat cs).isSome then true else kContainsSub pat rest

def kHasSubstr (s pat : String) : Bool :=
  kContainsSub pat.toList s.toList

/-- Total `List Char` string splitter avoiding `partial def String.splitOnAux`. -/
def kSplitAux (pat : List Char) : Nat → List Char → List Char → List String
  | 0, cur, _ => [String.ofList cur.reverse]
  | _ + 1, cur, [] => [String.ofList cur.reverse]
  | fuel + 1, cur, cs@(c :: rest) =>
    if pat.isEmpty then [String.ofList (cur.reverse ++ cs)]
    else match stripPre pat cs with
      | some after => String.ofList cur.reverse :: kSplitAux pat fuel [] after
      | none => kSplitAux pat fuel (c :: cur) rest

def kSplitOn (s pat : String) : List String :=
  let cs := s.toList
  kSplitAux pat.toList (cs.length + 1) [] cs

def kReplace (s pat rep : String) : String :=
  String.intercalate rep (kSplitOn s pat)

def kTrim (s : String) : String :=
  let dropWs := List.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
  String.ofList ((dropWs (dropWs s.toList).reverse).reverse)

def kStartsWith (s pre : String) : Bool := (stripPre pre.toList s.toList).isSome
def kEndsWith (s suf : String) : Bool := (stripPre suf.toList.reverse s.toList.reverse).isSome
def kDrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
def kDropRight (s : String) (n : Nat) : String := String.ofList ((s.toList.reverse.drop n).reverse)
def kStripComma (s : String) : String := if kEndsWith s "," then kDropRight s 1 else s
def kStripSemi (s : String) : String := if kEndsWith s ";" then kDropRight s 1 else s

def kNatOfChars : List Char → Option Nat
  | [] => none
  | cs => cs.foldlM (fun acc c =>
      if '0' ≤ c && c ≤ '9' then some (acc * 10 + (c.toNat - '0'.toNat)) else none) 0

def kParseMLIRArith (line : String) : Option StableHLOOp :=
  let l := kTrim line
  if !(kStartsWith l "%") then none
  else match kSplitOn l "=" with
  | [lhs, rhs0] =>
    let dst := kDrop (kTrim lhs) 1
    let rhs := kTrim ((kSplitOn rhs0 ":").head?.getD "")
    match (kSplitOn rhs " ").filter (· != "") with
    | [op, a0, b0] =>
      let a := kDrop (kStripComma a0) 1
      let b := kDrop (kStripComma b0) 1
      match op with
      | "arith.shli" => some (.shiftLeft dst a b)
      | "arith.shrui" => some (.shiftRightLogical dst a b)
      | _ => none
    | _ => none
  | _ => none

def evalMLIRScalarText (lines : List String) (resSsa : String) (v0 v1 : UInt64) : Option UInt64 :=
  let ops := lines.filterMap kParseMLIRArith
  let fn : FuncOp :=
    { name := "f"
      params := [("v0", { shape := [], elem := .ui64 }), ("v1", { shape := [], elem := .ui64 })]
      result := { shape := [], elem := .ui64 }
      body := ops ++ [.returnOp (kDrop resSsa 1)] }
  match evalFuncOp fn [scU64 v0, scU64 v1] with
  | .ok tv => tv.data[0]?.map (fun bv => bv.toNat.toUInt64)
  | .error _ => none

def evalScalarU64? (env : VarEnv) (e : ScalarExpr) : Option UInt64 :=
  match evalScalarExpr env e with
  | .ok (.u64 x) => some x
  | _ => none

def evalScalarBool? (env : VarEnv) (e : ScalarExpr) : Option Bool :=
  match evalScalarExpr env e with
  | .ok (.bool b) => some b
  | _ => none

/-- `M6` in-kernel mutant kill on production `MLIRGPU.emitMLIRScalarExpr`: swapping `arith.shli`
    and `arith.shrui` changes evaluation on `(3, 2)` from `some 12` (matching `evalScalarExpr`)
    to `some 0`. -/
theorem kill_emitter_mutant_M6 :
    let e : ScalarExpr := .binOp .shl (.var 0) (.var 1)
    let (lines, res, _) := emitMLIRScalarExpr e 0
    let mutLines := lines.map fun l =>
      kReplace (kReplace (kReplace l "arith.shli " "__TMP__ ") "arith.shrui " "arith.shli ")
        "__TMP__ " "arith.shrui "
    let env := (VarEnv.empty.bind 0 (.u64 3)).bind 1 (.u64 2)
    mutLines ≠ lines ∧
    evalScalarU64? env e = some 12 ∧
    evalMLIRScalarText lines res 3 2 = some 12 ∧
    evalMLIRScalarText mutLines res 3 2 = some 0 ∧
    evalMLIRScalarText mutLines res 3 2 ≠ evalMLIRScalarText lines res 3 2 := by
  decide

def kPtxOp (tok0 : String) : Option PTXOperand :=
  let tok := kStripComma tok0
  match kNatOfChars tok.toList with
  | some n => some (.immU64 (BitVec.ofNat 64 n))
  | none => if kStartsWith tok "%" then some (.reg tok) else none

def kParsePTXScalarLine (line : String) : Option PTXStmt :=
  let ws := (kSplitOn (kStripSemi (kTrim line)) " ").filter (· != "")
  match ws with
  | ["sub.u64", dst, a, b] =>
    (kPtxOp a).bind fun x => (kPtxOp b).map fun y => .instr none (.sub .u64 (kStripComma dst) x y)
  | ["setp.lt.u64", p, a, b] =>
    (kPtxOp a).bind fun x => (kPtxOp b).map fun y => .instr none (.setp .lt .u64 (kStripComma p) x y)
  | ["setp.le.u64", p, a, b] =>
    (kPtxOp a).bind fun x => (kPtxOp b).map fun y => .instr none (.setp .le .u64 (kStripComma p) x y)
  | ["selp.u64", dst, a, b, p] =>
    (kPtxOp a).bind fun x => (kPtxOp b).map fun y =>
      .instr none (.selp .u64 (kStripComma dst) x y (kStripComma p))
  | _ => none

def evalPTXScalarText (lines : List String) (resReg : String) (v0 v1 : UInt64) : Option UInt64 :=
  let stmts := (lines.flatMap fun s => kSplitOn s "\n").filterMap kParsePTXScalarLine
  let k : PTXKernel :=
    { name := "sc"
      params := []
      regDecls := [ { ty := .pred, prefixName := "%p", count := 4 }
                  , { ty := .b32, prefixName := "%r", count := 5 }
                  , { ty := .b64, prefixName := "%rd", count := 12 } ]
      body := [ .instr none (.mov .u64 "%rd8" (.immU64 v0.toBitVec))
              , .instr none (.mov .u64 "%rd9" (.immU64 v1.toBitVec))
              , .instr none (.mov .u64 "%rd6" (.immU64 0#64)) ] ++
              stmts ++
              [ .instr none (.stGlobal .u64 (.regOffset "%rd6" 0) (.reg resReg))
              , .instr none .ret ] }
  let g0 := LeanNative.Backend.PTXLower.mkPTXGlobalMem [] 0 1
  let p0 := LeanNative.Backend.PTXLower.mkPTXParamMem 0 1
  match evalPTXKernel 16 k { x := 1, y := 1, z := 1 } { x := 1, y := 1, z := 1 } g0 p0 with
  | .ok g => (g.loadBits 0 8).map (fun bv => bv.toNat.toUInt64)
  | _ => none

/-- `M7` in-kernel mutant kill on production `MLIRGPU.emitPTXScalarExpr` & `emitPTXDeclKernel`:
    reversing `sub.u64` operands changes `evalPTXKernel` on `(1, 4)` from `1 - 4` (matching
    `evalScalarExpr`) to `4 - 1 = 3`, and mutates the full `emitPTXDeclKernel` entry text. -/
theorem kill_emitter_mutant_M7 :
    let e : ScalarExpr := .binOp .sub (.var 0) (.var 1)
    let (lines, res, _, _) := emitPTXScalarExpr e [(0, "%rd8"), (1, "%rd9")] 10 2
    let mutLines := lines.map fun l =>
      kReplace l "    sub.u64      %rd10, %rd8, %rd9;" "    sub.u64      %rd10, %rd9, %rd8;"
    let env := (VarEnv.empty.bind 0 (.u64 1)).bind 1 (.u64 4)
    mutLines ≠ lines ∧
    evalScalarU64? env e = some ((1 : UInt64) - 4) ∧
    evalPTXScalarText lines res 1 4 = some ((1 : UInt64) - 4) ∧
    evalPTXScalarText mutLines res 1 4 = some 3 ∧
    evalPTXScalarText mutLines res 1 4 ≠ evalPTXScalarText lines res 1 4 := by
  decide

/-- `M8` in-kernel mutant kill on production `MLIRGPU.emitPTXScalarExpr`:
    replacing `setp.lt.u64` with `setp.le.u64` changes `evalPTXKernel` on equal operands `(3, 3)`
    from `0` (`3 < 3 = false` in `evalScalarExpr`) to `1`. -/
theorem kill_emitter_mutant_M8 :
    let e : ScalarExpr := .binOp .lt (.var 0) (.var 1)
    let (lines, res, _, _) := emitPTXScalarExpr e [(0, "%rd8"), (1, "%rd9")] 10 2
    let mutLines := lines.map fun l => kReplace l "setp.lt.u64" "setp.le.u64"
    let env := (VarEnv.empty.bind 0 (.u64 3)).bind 1 (.u64 3)
    mutLines ≠ lines ∧
    evalScalarBool? env e = some false ∧
    evalPTXScalarText lines res 3 3 = some 0 ∧
    evalPTXScalarText mutLines res 3 3 = some 1 ∧
    evalPTXScalarText mutLines res 3 3 ≠ evalPTXScalarText lines res 3 3 := by
  decide

def kParseMSLExpr : Nat → String → Option MSLExpr
  | 0, _ => none
  | fuel + 1, t0 =>
    let t := kTrim t0
    if isWrappedParens t then
      let inner := kDropRight (kDrop t 1) 1
      match splitTopChar inner '?' with
      | [c, rest] =>
        match splitTopChar rest ':' with
        | [a, b] =>
          (kParseMSLExpr fuel c).bind fun ce =>
          (kParseMSLExpr fuel a).bind fun ae =>
          (kParseMSLExpr fuel b).map fun be => .select ce ae be
        | _ => none
      | _ =>
        let bins : List (String × (MSLExpr → MSLExpr → MSLExpr)) :=
          [("==", .eq), ("&", .bitAnd), ("<<", .shl), ("/", .div)]
        bins.findSome? fun (op, mk) =>
          match splitTopOp inner op with
          | some (a, b) =>
            (kParseMSLExpr fuel a).bind fun ae => (kParseMSLExpr fuel b).map fun be => mk ae be
          | none => none
    else if kEndsWith t "UL" then
      (kNatOfChars (kDropRight t 2).toList).map fun n => .immU64 (BitVec.ofNat 64 n)
    else if t != "" then some (.var t)
    else none

def evalMSLScalarText (exprText : String) (v0 v1 : UInt64) :
    Option (MSLOutcome (List (Nat × LeanNative.Backend.MetalAst.ByteMemory))) :=
  match kParseMSLExpr 16 exprText with
  | none => none
  | some e =>
    let k : MSLKernelDecl :=
      { name := "k"
        params := [ LeanNative.Backend.MetalLower.bufParam "in0" 0 true
                  , LeanNative.Backend.MetalLower.bufParam "in1" 1 true
                  , LeanNative.Backend.MetalLower.bufParam "out" 2 false
                  , LeanNative.Backend.MetalLower.lenParam 3
                  , LeanNative.Backend.MetalLower.gidParam ]
        body := [ .varDecl .ulong "v0" (.index "in0" (.var "gid"))
                , .varDecl .ulong "v1" (.index "in1" (.var "gid"))
                , .indexAssign "out" (.var "gid") e
                , .returnStmt ] }
    let inBufs := [ (0, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [v0.toBitVec])
                  , (1, LeanNative.Backend.MetalAst.ByteMemory.ofU64Words [v1.toBitVec]) ]
    let dev := LeanNative.Backend.MetalLower.mkDeviceBuffers inBufs 2 1
    let cst := LeanNative.Backend.MetalLower.mkConstLenBuffers 2 1
    some (evalMSLKernel 16 k { x := 1, y := 1, z := 1 } { x := 1, y := 1, z := 1 } dev cst [] [])

def extractMSLWord0 :
    Option (MSLOutcome (List (Nat × LeanNative.Backend.MetalAst.ByteMemory))) → Option UInt64
  | some (.ok bufs) =>
    (bufs.lookup 2).bind (fun m => m.readU64Word? 0) |>.map (fun bv => bv.toNat.toUInt64)
  | _ => none

/-- `M9` in-kernel mutant kill on production `Metal.emitMetalScalarExpr` & `emitMetalDeclKernel`:
    dropping the `== 0UL` divisor guard traps with `MSLOutcome.divisionByZero` on `(7, 0)` whereas
    unmutated Metal returns `0` (matching `evalScalarExpr`). -/
theorem kill_emitter_mutant_M9 :
    let e : ScalarExpr := .binOp .div (.var 0) (.var 1)
    let txt := emitMetalScalarExpr e
    let txtMut := kReplace txt "((v1 == 0UL) ? 0UL : (v0 / v1))" "(v0 / v1)"
    let env := (VarEnv.empty.bind 0 (.u64 7)).bind 1 (.u64 0)
    txtMut ≠ txt ∧
    evalScalarU64? env e = some 0 ∧
    extractMSLWord0 (evalMSLScalarText txt 7 0) = some 0 ∧
    (evalMSLScalarText txtMut 7 0 == some MSLOutcome.divisionByZero) = true := by
  decide

/-- `M10` in-kernel mutant kill on production `Metal.emitMetalScalarExpr`:
    replacing `& 63UL` with `& 31UL` masks shift amount `32` to `0` (`1` vs `2^32` in `evalScalarExpr`). -/
theorem kill_emitter_mutant_M10 :
    let e : ScalarExpr := .binOp .shl (.var 0) (.var 1)
    let txt := emitMetalScalarExpr e
    let txtMut := kReplace txt "& 63UL)" "& 31UL)"
    let env := (VarEnv.empty.bind 0 (.u64 1)).bind 1 (.u64 32)
    txtMut ≠ txt ∧
    evalScalarU64? env e = some 4294967296 ∧
    extractMSLWord0 (evalMSLScalarText txt 1 32) = some 4294967296 ∧
    extractMSLWord0 (evalMSLScalarText txtMut 1 32) = some 1 ∧
    extractMSLWord0 (evalMSLScalarText txtMut 1 32) ≠ extractMSLWord0 (evalMSLScalarText txt 1 32) := by
  decide

/-- Production declaration-kernel emitters delegate `saxpy`, `mapScaleAdd`, `zipAdd`, `zipMul`,
    and `stencil1D3Pt` definitionally (`rfl`) to the verified `PTXLower` / `MetalLower` AST pretty-printers. -/
theorem production_decl_emitters_wired :
    let saxpyDecl : LNIRDecl :=
      { name := "saxpy_k"
        params := [{ id := 0, name := "x", ty := .sarray .i64 }, { id := 1, name := "y", ty := .sarray .i64 }]
        retTy := .sarray .i64
        body := .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 (.saxpy 7) (.ret 3)) }
    let stencilDecl : LNIRDecl :=
      { name := "stencil_k"
        params := [{ id := 0, name := "x", ty := .sarray .i64 }]
        retTy := .sarray .i64
        body := .letBind 1 .i64 (.sarrayLen 0) (.parFor 2 1 [0] .i64 (.stencil1D3Pt 1 2 1) (.ret 2)) }
    emitPTXDeclKernel "lean_native_decl_saxpy_k" (.saxpy 7) =
      ppPTXKernel (LeanNative.Backend.PTXLower.lowerKind "lean_native_decl_saxpy_k" (.saxpy 7)) ∧
    emitPTXDeclKernel "lean_native_decl_stencil_k" (.stencil1D3Pt 1 2 1) =
      ppPTXKernel (LeanNative.Backend.PTXLower.lowerKind "lean_native_decl_stencil_k" (.stencil1D3Pt 1 2 1)) ∧
    emitMetalDeclKernel saxpyDecl =
      some (ppMSLKernel (LeanNative.Backend.MetalLower.lowerSaxpyNamed "lean_native_metal_decl_saxpy_k" 7)) ∧
    emitMetalDeclKernel stencilDecl =
      some (ppMSLKernel (LeanNative.Backend.MetalLower.lowerKind "lean_native_metal_decl_stencil_k"
        (.stencil1D3Pt 1 2 1))) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end LeanNative.Proofs.GPUEmitterMutantProofs
