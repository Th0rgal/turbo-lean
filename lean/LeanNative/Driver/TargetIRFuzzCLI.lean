import Lean.Data.Json
import LeanNative.IR.Codec
import LeanNative.Backend.LLVMAst
import LeanNative.Backend.PTXAst
import LeanNative.Backend.StableHLOAst
import LeanNative.Backend.MetalAst

/-!
# Stage 4 Multi-Backend Target-IR Differential Fuzzer CLI (`LeanNative.Driver.TargetIRFuzzCLI`)

Seeded deterministic Target-IR generator, in-Lean `parse ∘ pp = some` roundtrip verifier, and
evaluator oracle across all four typed backend ASTs (`LLVMAst`, `PTXAst`, `StableHLOAst`, `MetalAst`):

- **Valid well-typed cases**: multi-width integer arithmetic/bitwise/shift/comparison/select,
  `alloca`+`store`+`getelementptr`+`load`, `condBr`+`phi` diamonds, PTX SIMT lane-guarded kernels
  plus `.shared` + `bar.sync` swap kernels, OpenXLA StableHLO integer/boolean tensor DAGs
  (including `INT_MIN / -1` and `dynamic_slice` OOB start-index clamping), and Metal MSL 3.0
  scalar + `threadgroup_barrier` kernels.
- **Intentional UB / trap cases (two-sided trap agreement)**: `LLVMAst` `udiv`/`sdiv`/`urem`/`srem`
  by `0`, `sdiv`/`srem` `INT_MIN / -1`, `null` dereference, and stack `alloca` OOB `getelementptr`;
  `PTXAst` `div`/`rem` by `0`, `div.s64` `INT64_MIN / -1`, OOB `.global` access, misaligned `.global`
  access, `.shared` data race without `bar.sync`, and divergent `bar.sync`; `StableHLOAst`
  `divide`/`remainder` by `0` and static shape/type mismatch; `MetalAst` `div`/`rem` by `0`,
  signed `long` `INT64_MIN / -1`, shift out-of-range (`≥ 64`), OOB `device` access, and
  `threadgroup` data race without `threadgroup_barrier`.
- **Negative semantic mutants**: emitted per seed across all 4 backends to prove the external
  executors catch semantic drift rather than rubber-stamping syntax.
-/

namespace LeanNative.Driver.TargetIRFuzzCLI

open Lean
open LeanNative.IR
open LeanNative.Backend.TargetIR
open LeanNative.Backend
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.PTXAst
open LeanNative.Backend.StableHLOAst
open LeanNative.Backend.MetalAst

/-! ## 1. Deterministic SplitMix64 PRNG -/

structure Rng where
  state : UInt64
  deriving Repr, Inhabited

namespace Rng

def ofSeed (seed : Nat) : Rng :=
  { state := seed.toUInt64 ^^^ 0x9e3779b97f4a7c15 }

def nextU64 (r : Rng) : UInt64 × Rng :=
  let s' := r.state + 0x9e3779b97f4a7c15
  let z1 := (s' ^^^ (s' >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  (z2 ^^^ (z2 >>> 31), { state := s' })

def nextNat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (w, r') := r.nextU64
  if bound == 0 then (0, r') else (w.toNat % bound, r')

def pick {α : Type} [Inhabited α] (r : Rng) (xs : List α) : α × Rng :=
  let (idx, r') := r.nextNat xs.length
  (xs[idx]?.getD default, r')

end Rng

private def u64ArrJson (xs : List UInt64) : Json :=
  Json.arr (xs.map (fun w => toJson w.toNat)).toArray

private def natArrJson (xs : List Nat) : Json :=
  Json.arr (xs.map toJson).toArray

/-! ## 2. Covered `LLVMFn` Roundtrip Parser (`parseFuzzLLVMFn ∘ PP.ppFn = some`) -/

private def dropStr (s : String) (n : Nat) : String :=
  (s.drop n).toString

private def dropEndStr (s : String) (n : Nat) : String :=
  (s.dropEnd n).toString

private def trimStr (s : String) : String :=
  s.trimAscii.toString

private def parseIntWidthStr : String → Option IntWidth
  | "i1" => some .i1 | "i8" => some .i8 | "i16" => some .i16
  | "i32" => some .i32 | "i64" => some .i64 | "i128" => some .i128 | "i256" => some .i256
  | _ => none

private def parseLLVMTypeExact (s : String) : Option LLVMType :=
  match PP.parseType (s.length + 8) s.toList with
  | some (ty, []) => some ty
  | _ => none

private def parseRegTok (s : String) : Option RegName :=
  if s.startsWith "%" && s.length > 1 then some (dropStr s 1) else none

private def parseOperandWithWidth (w : IntWidth) (s : String) : Option Operand :=
  let t := trimStr s
  if t == "null" then some .constNull
  else if t == "undef" then some .constUndef
  else if t == "poison" then some .poison
  else if t == "zeroinitializer" then some .constZero
  else if let some r := parseRegTok t then some (.reg r)
  else if t.startsWith "@" && t.length > 1 then some (.global (dropStr t 1))
  else t.toNat?.map fun n => .constInt w (BitVec.ofNat w.bits n)

private def parseOperandForType (ty : LLVMType) (s : String) : Option Operand :=
  match ty with
  | .int w => parseOperandWithWidth w s
  | .ptr _ => parseOperandWithWidth .i64 s
  | _ => none

private def parseICmpPredStr : String → Option ICmpPred
  | "eq" => some .eq | "ne" => some .ne
  | "ult" => some .ult | "ule" => some .ule | "ugt" => some .ugt | "uge" => some .uge
  | "slt" => some .slt | "sle" => some .sle | "sgt" => some .sgt | "sge" => some .sge
  | _ => none

private def stripAlignSuffix (s : String) : Option (String × Nat) :=
  match s.splitOn ", align " with
  | [head] => some (head, 0)
  | [head, alStr] => alStr.toNat?.map fun a => (head, a)
  | _ => none

private def parseOverflowPrefix (op : String) (rhs : String) : Option (OverflowFlags × String) :=
  if rhs.startsWith (op ++ " nsw nuw ") then some (.nswNuw, dropStr rhs (op.length + 9))
  else if rhs.startsWith (op ++ " nsw ") then some (.nsw, dropStr rhs (op.length + 5))
  else if rhs.startsWith (op ++ " nuw ") then some (.nuw, dropStr rhs (op.length + 5))
  else if rhs.startsWith (op ++ " ") then some (.none, dropStr rhs (op.length + 1))
  else none

private def parseExactPrefix (op : String) (rhs : String) : Option (Bool × String) :=
  if rhs.startsWith (op ++ " exact ") then some (true, dropStr rhs (op.length + 7))
  else if rhs.startsWith (op ++ " ") then some (false, dropStr rhs (op.length + 1))
  else none

private def parseWidthPairArgs (rest : String) : Option (IntWidth × Operand × Operand) := do
  let [wAndA, bStr] := rest.splitOn ", " | none
  let [wStr, aStr] := wAndA.splitOn " " | none
  let w ← parseIntWidthStr wStr
  let a ← parseOperandWithWidth w aStr
  let b ← parseOperandWithWidth w bStr
  pure (w, a, b)

private def parseCastTail (rest : String) : Option (IntWidth × Operand × IntWidth) := do
  let [lhs, dstStr] := rest.splitOn " to " | none
  let [srcStr, opStr] := lhs.splitOn " " | none
  let srcW ← parseIntWidthStr srcStr
  let dstW ← parseIntWidthStr dstStr
  let op ← parseOperandWithWidth srcW opStr
  pure (srcW, op, dstW)

private def parsePhiArms (ty : LLVMType) (s : String) : Option (List (Operand × BlockLabel)) := do
  let rawArms := s.splitOn "], ["
  rawArms.mapM fun raw => do
    let r1 := if raw.startsWith "[" then dropStr raw 1 else raw
    let r2 := if r1.endsWith "]" then dropEndStr r1 1 else r1
    let clean := trimStr r2
    let [vStr, lblStr] := clean.splitOn ", " | none
    let op ← parseOperandForType ty (trimStr vStr)
    let lbl ← parseRegTok (trimStr lblStr)
    pure (op, lbl)

private def parseFuzzPhi (line : String) : Option PhiNode := do
  let [dstTok, rhs] := line.splitOn " = phi " | none
  let dst ← parseRegTok dstTok
  let pieces := rhs.splitOn "["
  let tyPart :: armParts := pieces | none
  if armParts.isEmpty then none
  else
    let tyStr := trimStr tyPart
    let armsStr := "[" ++ String.intercalate "[" armParts
    let ty ← parseLLVMTypeExact tyStr
    let arms ← parsePhiArms ty armsStr
    pure { dst, ty, incomings := arms }

private def parseGEPIdxs (parts : List String) : Option (List (IntWidth × Operand)) :=
  parts.mapM fun item => do
    let [wStr, opStr] := (trimStr item).splitOn " " | none
    let w ← parseIntWidthStr wStr
    let op ← parseOperandWithWidth w opStr
    pure (w, op)

private def parseFuzzInstr (line : String) : Option LLVMInstr := do
  if line.startsWith "store " then
    let (core, align) ← stripAlignSuffix (dropStr line 6)
    let [valPart, ptrPart] := core.splitOn ", " | none
    let [tyStr, valStr] := valPart.splitOn " " | none
    let ty ← parseLLVMTypeExact tyStr
    let valOp ← parseOperandForType ty valStr
    let [ptrTyStr, ptrStr] := ptrPart.splitOn " " | none
    let .ptr as_ ← parseLLVMTypeExact ptrTyStr | none
    let ptrOp ← parseOperandWithWidth .i64 ptrStr
    pure (.store false ty valOp ptrOp align as_)
  else
    let [dstTok, rhs] := line.splitOn " = " | none
    let dst ← parseRegTok dstTok
    if rhs.startsWith "alloca " then
      let (tyStr, align) ← stripAlignSuffix (dropStr rhs 7)
      let ty ← parseLLVMTypeExact tyStr
      pure (.alloca dst ty align)
    else if rhs.startsWith "load " then
      let (core, align) ← stripAlignSuffix (dropStr rhs 5)
      let [tyStr, ptrPart] := core.splitOn ", " | none
      let ty ← parseLLVMTypeExact tyStr
      let [ptrTyStr, ptrStr] := ptrPart.splitOn " " | none
      let .ptr as_ ← parseLLVMTypeExact ptrTyStr | none
      let ptrOp ← parseOperandWithWidth .i64 ptrStr
      pure (.load dst false ty ptrOp align as_)
    else if rhs.startsWith "getelementptr " then
      let rest := dropStr rhs 14
      let (ib, afterIb) :=
        if rest.startsWith "inbounds " then (true, dropStr rest 9) else (false, rest)
      let segs := afterIb.splitOn ", "
      let tyStr :: ptrSeg :: idxSegs := segs | none
      let ty ← parseLLVMTypeExact tyStr
      let [ptrTyStr, baseStr] := ptrSeg.splitOn " " | none
      let .ptr as_ ← parseLLVMTypeExact ptrTyStr | none
      let baseOp ← parseOperandWithWidth .i64 baseStr
      let idxs ← parseGEPIdxs idxSegs
      pure (.getelementptr dst ib ty baseOp idxs as_)
    else if let some (fl, rest) := parseOverflowPrefix "add" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.add dst fl w a b)
    else if let some (fl, rest) := parseOverflowPrefix "sub" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.sub dst fl w a b)
    else if let some (fl, rest) := parseOverflowPrefix "mul" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.mul dst fl w a b)
    else if let some (fl, rest) := parseOverflowPrefix "shl" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.shl dst fl w a b)
    else if let some (ex, rest) := parseExactPrefix "udiv" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.udiv dst ex w a b)
    else if let some (ex, rest) := parseExactPrefix "sdiv" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.sdiv dst ex w a b)
    else if let some (ex, rest) := parseExactPrefix "lshr" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.lshr dst ex w a b)
    else if let some (ex, rest) := parseExactPrefix "ashr" rhs then
      let (w, a, b) ← parseWidthPairArgs rest
      pure (.ashr dst ex w a b)
    else if rhs.startsWith "urem " then
      let (w, a, b) ← parseWidthPairArgs (dropStr rhs 5)
      pure (.urem dst w a b)
    else if rhs.startsWith "srem " then
      let (w, a, b) ← parseWidthPairArgs (dropStr rhs 5)
      pure (.srem dst w a b)
    else if rhs.startsWith "and " then
      let (w, a, b) ← parseWidthPairArgs (dropStr rhs 4)
      pure (.and_ dst w a b)
    else if rhs.startsWith "or " then
      let (w, a, b) ← parseWidthPairArgs (dropStr rhs 3)
      pure (.or_ dst w a b)
    else if rhs.startsWith "xor " then
      let (w, a, b) ← parseWidthPairArgs (dropStr rhs 4)
      pure (.xor dst w a b)
    else if rhs.startsWith "icmp " then
      let rest := dropStr rhs 5
      let [predAndTyAndA, bStr] := rest.splitOn ", " | none
      let [predStr, tyStr, aStr] := predAndTyAndA.splitOn " " | none
      let pred ← parseICmpPredStr predStr
      let ty ← parseLLVMTypeExact tyStr
      let a ← parseOperandForType ty aStr
      let b ← parseOperandForType ty bStr
      pure (.icmp dst pred ty a b)
    else if rhs.startsWith "select i1 " then
      let rest := dropStr rhs 10
      let [condStr, tPart, ePart] := rest.splitOn ", " | none
      let condOp ← parseOperandWithWidth .i1 condStr
      let [tTyStr, tValStr] := tPart.splitOn " " | none
      let [eTyStr, eValStr] := ePart.splitOn " " | none
      let ty ← parseLLVMTypeExact tTyStr
      let ty2 ← parseLLVMTypeExact eTyStr
      if ty != ty2 then none
      else
        let tOp ← parseOperandForType ty tValStr
        let eOp ← parseOperandForType ty eValStr
        pure (.select dst condOp ty tOp eOp)
    else if rhs.startsWith "zext " then
      let (srcW, op, dstW) ← parseCastTail (dropStr rhs 5)
      pure (.zext dst srcW op dstW)
    else if rhs.startsWith "sext " then
      let (srcW, op, dstW) ← parseCastTail (dropStr rhs 5)
      pure (.sext dst srcW op dstW)
    else if rhs.startsWith "trunc " then
      let (srcW, op, dstW) ← parseCastTail (dropStr rhs 6)
      pure (.trunc dst srcW op dstW)
    else none

private def parseFuzzTerm (line : String) : Option Terminator := do
  if line == "ret void" then pure (.ret none)
  else if line == "unreachable" then pure .unreachable
  else if line.startsWith "ret " then
    let [tyStr, valStr] := (dropStr line 4).splitOn " " | none
    let ty ← parseLLVMTypeExact tyStr
    let op ← parseOperandForType ty valStr
    pure (.ret (some (ty, op)))
  else if line.startsWith "br label " then
    let lbl ← parseRegTok (dropStr line 9)
    pure (.br lbl)
  else if line.startsWith "br i1 " then
    let [condStr, tPart, ePart] := (dropStr line 6).splitOn ", " | none
    let condOp ← parseOperandWithWidth .i1 condStr
    if !(tPart.startsWith "label " && ePart.startsWith "label ") then none
    else
      let tLbl ← parseRegTok (dropStr tPart 6)
      let eLbl ← parseRegTok (dropStr ePart 6)
      pure (.condBr condOp tLbl eLbl)
  else none

private def parseFuzzParam (s : String) : Option LLVMParam := do
  let [tyStr, nameTok] := (trimStr s).splitOn " " | none
  let ty ← parseLLVMTypeExact tyStr
  let name ← parseRegTok nameTok
  pure { name, ty, attrs := [] }

private def parseCCStr : String → Option CallingConv
  | "ccc" => some .ccc | "fastcc" => some .fastcc | "coldcc" => some .coldcc | _ => none

private def parseFuzzBlocks : Nat → List String → Option (List LLVMBlock)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, hdr :: rest => do
    if !hdr.endsWith ":" then none
    else
      let lbl := dropEndStr hdr 1
      let stmtLines := rest.takeWhile (fun l => l.startsWith "  ")
      let rem := rest.drop stmtLines.length
      let trimmed := stmtLines.map (fun l => dropStr l 2)
      let termLine ← trimmed.getLast?
      let preTerm := trimmed.dropLast
      let phiLines := preTerm.takeWhile (fun l => (l.splitOn " = phi ").length == 2)
      let bodyLines := preTerm.drop phiLines.length
      let phis ← phiLines.mapM parseFuzzPhi
      let body ← bodyLines.mapM parseFuzzInstr
      let term ← parseFuzzTerm termLine
      let tailBlocks ← parseFuzzBlocks fuel rem
      pure ({ label := lbl, phis, body, term } :: tailBlocks)

/-- Structural parser for the covered `LLVMFn` fragment (`parseFuzzLLVMFn (PP.ppFn fn) == some fn`). -/
def parseFuzzLLVMFn (text : String) : Option LLVMFn := do
  let header :: rest := text.splitOn "\n" | none
  if !(header.startsWith "define " && header.endsWith ") {") then none
  else
    let sig := dropEndStr (dropStr header 7) 3
    let [beforeAt, afterAt] := sig.splitOn " @" | none
    let [ccStr, retTyStr] := beforeAt.splitOn " " | none
    let cc ← parseCCStr ccStr
    let retTy ← parseLLVMTypeExact retTyStr
    let [fnName, paramsStr] := afterAt.splitOn "(" | none
    let params ←
      if paramsStr.isEmpty then some []
      else (paramsStr.splitOn ", ").mapM parseFuzzParam
    let "}" :: revBlocks := rest.reverse | none
    let blockLines := revBlocks.reverse
    let blocks ← parseFuzzBlocks (blockLines.length + 1) blockLines
    pure { name := fnName, retTy, params, cc, blocks }

/-! ## 3. Backend 1: `LLVMAst` Seeded Generator, Roundtrip Gate & Evaluator -/

private def mkLLVMMod (fn : LLVMFn) : LLVMModule :=
  { dataLayout := TargetArch.x86_64.dataLayout
  , triple := TargetArch.x86_64.llvmTriple
  , fns := [fn] }

private def genLLVMValidFn (seed : Nat) : LLVMFn × LLVMFn × String × List (List UInt64) :=
  let r0 := Rng.ofSeed (seed * 4 + 1)
  let fnName := s!"llvm_fuzz_valid_{seed}"
  let params : List LLVMParam := [{ name := "a", ty := .int .i64 }, { name := "b", ty := .int .i64 }]
  let (kind, r1) := r0.nextNat 4
  let (k1, r2) := r1.nextU64
  let (k2, r3) := r2.nextU64
  let (shAmt, r4) := r3.nextNat 31
  let c1 := Operand.constInt .i64 ((k1 &&& 0xFFFF).toBitVec)
  let c2 := Operand.constInt .i64 (((k2 &&& 0xFF) ||| 1).toBitVec)
  let (v1a, r5) := r4.nextU64
  let (v1b, r6) := r5.nextU64
  let (v2a, r7) := r6.nextU64
  let (v2b, _) := r7.nextU64
  let vecs : List (List UInt64) :=
    [ [v1a, v1b], [v2a, v2b], [0, 1], [0x8000000000000000, 7] ]
  let fn : LLVMFn :=
    match kind with
    | 0 =>
      -- Multi-width trunc/sext/zext + guarded udiv/urem + select
      let body : List LLVMInstr :=
        [ .trunc "a32" .i64 (.reg "a") .i32
        , .trunc "b32" .i64 (.reg "b") .i32
        , .or_ "b32nz" .i32 (.reg "b32") (.constInt .i32 1#32)
        , .udiv "q32" false .i32 (.reg "a32") (.reg "b32nz")
        , .urem "r32" .i32 (.reg "a32") (.reg "b32nz")
        , .zext "q64" .i32 (.reg "q32") .i64
        , .sext "r64" .i32 (.reg "r32") .i64
        , .xor "mix" .i64 (.reg "q64") (.reg "r64")
        , .shl "sh" .none .i64 (.reg "mix") (.constInt .i64 (BitVec.ofNat 64 (shAmt + 1)))
        , .icmp "cmp" .ult (.int .i64) (.reg "a") (.reg "b")
        , .add "alt" .none .i64 (.reg "sh") c1
        , .select "res" (.reg "cmp") (.int .i64) (.reg "alt") (.reg "sh") ]
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry", body, term := .ret (some (.int .i64, .reg "res")) } ] }
    | 1 =>
      -- Stack alloca [4 x i64], inbounds GEP stores & loads
      let arrTy : LLVMType := .array 4 (.int .i64)
      let body : List LLVMInstr :=
        [ .alloca "buf" arrTy 8
        , .getelementptr "p0" true arrTy (.reg "buf") [(.i64, .constInt .i64 0#64), (.i64, .constInt .i64 0#64)] 0
        , .getelementptr "p1" true arrTy (.reg "buf") [(.i64, .constInt .i64 0#64), (.i64, .constInt .i64 1#64)] 0
        , .getelementptr "p2" true arrTy (.reg "buf") [(.i64, .constInt .i64 0#64), (.i64, .constInt .i64 2#64)] 0
        , .add "s0" .none .i64 (.reg "a") c1
        , .mul "s1" .none .i64 (.reg "b") c2
        , .xor "s2" .i64 (.reg "s0") (.reg "s1")
        , .store false (.int .i64) (.reg "s0") (.reg "p0") 8 0
        , .store false (.int .i64) (.reg "s1") (.reg "p1") 8 0
        , .store false (.int .i64) (.reg "s2") (.reg "p2") 8 0
        , .load "l1" false (.int .i64) (.reg "p1") 8 0
        , .load "l2" false (.int .i64) (.reg "p2") 8 0
        , .sub "res" .none .i64 (.reg "l2") (.reg "l1") ]
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry", body, term := .ret (some (.int .i64, .reg "res")) } ] }
    | 2 =>
      -- Diamond CFG (`condBr` + `phi`) with arithmetic/logical shifts
      let shOp := Operand.constInt .i64 (BitVec.ofNat 64 ((shAmt % 15) + 1))
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body := [ .icmp "c" .slt (.int .i64) (.reg "a") (.reg "b") ]
          , term := .condBr (.reg "c") "then_bb" "else_bb" },
          { label := "then_bb"
          , body :=
              [ .ashr "t0" false .i64 (.reg "a") shOp
              , .add "t1" .none .i64 (.reg "t0") c1 ]
          , term := .br "merge_bb" },
          { label := "else_bb"
          , body :=
              [ .lshr "e0" false .i64 (.reg "b") shOp
              , .sub "e1" .none .i64 (.reg "e0") c2 ]
          , term := .br "merge_bb" },
          { label := "merge_bb"
          , phis := [{ dst := "m", ty := .int .i64, incomings := [(.reg "t1", "then_bb"), (.reg "e1", "else_bb")] }]
          , body := [ .xor "res" .i64 (.reg "m") c1 ]
          , term := .ret (some (.int .i64, .reg "res")) } ] }
    | _ =>
      -- 16-bit / 8-bit arithmetic + bitwise + guarded sdiv
      let body : List LLVMInstr :=
        [ .trunc "a16" .i64 (.reg "a") .i16
        , .trunc "b8" .i64 (.reg "b") .i8
        , .zext "b16" .i8 (.reg "b8") .i16
        , .or_ "bnz" .i16 (.reg "b16") (.constInt .i16 3#16)
        , .sdiv "q16" false .i16 (.reg "a16") (.reg "bnz")
        , .sext "q64" .i16 (.reg "q16") .i64
        , .and_ "m64" .i64 (.reg "a") c1
        , .add "res" .none .i64 (.reg "q64") (.reg "m64") ]
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry", body, term := .ret (some (.int .i64, .reg "res")) } ] }
  -- Negative mutant flips final result by `add res, 1` so every input vector diverges
  let mutFn : LLVMFn :=
    { fn with blocks := fn.blocks.map fun blk =>
        match blk.term with
        | .ret (some (.int .i64, op)) =>
          { blk with
            body := blk.body ++ [.add "mut_flip" .none .i64 op (.constInt .i64 1#64)]
            term := .ret (some (.int .i64, .reg "mut_flip")) }
        | _ => blk }
  (fn, mutFn, "appended +1 result perturbation", vecs)

private def genLLVMTrapFn (seed : Nat) : String × LLVMFn × List UInt64 :=
  let fnName := s!"llvm_fuzz_trap_{seed}"
  let params : List LLVMParam := [{ name := "a", ty := .int .i64 }, { name := "b", ty := .int .i64 }]
  match seed % 6 with
  | 0 =>
    ("udiv_zero",
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body := [.udiv "r" false .i64 (.reg "a") (.reg "b")]
          , term := .ret (some (.int .i64, .reg "r")) } ] },
      [42 + seed.toUInt64, 0])
  | 1 =>
    ("sdiv_int64_min_neg1",
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body := [.sdiv "r" false .i64 (.reg "a") (.reg "b")]
          , term := .ret (some (.int .i64, .reg "r")) } ] },
      [0x8000000000000000, 0xFFFFFFFFFFFFFFFF])
  | 2 =>
    ("srem_int64_min_neg1",
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body := [.srem "r" .i64 (.reg "a") (.reg "b")]
          , term := .ret (some (.int .i64, .reg "r")) } ] },
      [0x8000000000000000, 0xFFFFFFFFFFFFFFFF])
  | 3 =>
    ("null_load",
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body := [.load "r" false (.int .i64) .constNull 8 0]
          , term := .ret (some (.int .i64, .reg "r")) } ] },
      [seed.toUInt64 + 1, 7])
  | 4 =>
    ("null_store",
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body := [.store false (.int .i64) (.reg "a") .constNull 8 0]
          , term := .ret (some (.int .i64, .reg "b")) } ] },
      [seed.toUInt64 + 3, 9])
  | _ =>
    ("oob_alloca_gep_load",
      { name := fnName, retTy := .int .i64, params, blocks := [
          { label := "entry"
          , body :=
              [ .alloca "slot" (.int .i64) 8
              , .store false (.int .i64) (.reg "a") (.reg "slot") 8 0
              , .getelementptr "oob" true (.int .i64) (.reg "slot") [(.i64, .constInt .i64 2#64)] 0
              , .load "r" false (.int .i64) (.reg "oob") 8 0 ]
          , term := .ret (some (.int .i64, .reg "r")) } ] },
      [seed.toUInt64 + 11, 2])

private def buildLLVMSeedCases (seed : Nat) : Except String (List Json) := do
  let (validFn, mutFn, mutReason, vecs) := genLLVMValidFn seed
  let fnText := PP.ppFn validFn
  if parseFuzzLLVMFn fnText != some validFn then
    throw s!"[LLVMAst] roundtrip failed on valid seed {seed}:\n{fnText}"
  if parseFuzzLLVMFn (PP.ppFn mutFn) != some mutFn then
    throw s!"[LLVMAst] roundtrip failed on mutant seed {seed}"
  let modValid := mkLLVMMod validFn
  let modMut := mkLLVMMod mutFn
  let vecJson ← vecs.mapM fun ins => do
    let argVals := ins.map fun w => LLVMVal.bits .i64 w.toBitVec
    match execFn modValid validFn argVals 64 with
    | .returned (some (.bits .i64 bv)) =>
      let expected := bv.toNat.toUInt64
      match execFn modMut mutFn argVals 64 with
      | .returned (some (.bits .i64 mbv)) =>
        if mbv.toNat.toUInt64 == expected then
          throw s!"[LLVMAst] mutant failed to diverge on seed {seed}"
        pure (Json.mkObj [
          ("inputs", u64ArrJson ins),
          ("expectedTag", Json.str "val"),
          ("expectedWord", toJson expected.toNat)
        ])
      | _ => throw s!"[LLVMAst] mutant unexpectedly trapped on seed {seed}"
    | other => throw s!"[LLVMAst] valid seed {seed} did not return concrete i64: {reprStr other}"
  let validObj := Json.mkObj [
    ("id", Json.str s!"llvm_seed_{seed}_valid"),
    ("seed", toJson seed),
    ("kind", Json.str "valid"),
    ("fnName", Json.str validFn.name),
    ("roundtripVerified", Json.bool true),
    ("irText", Json.str (PP.ppModule modValid)),
    ("negativeMutantIr", Json.str (PP.ppModule modMut)),
    ("negativeMutantReason", Json.str mutReason),
    ("vectors", Json.arr vecJson.toArray)
  ]

  let (trapClass, trapFn, trapInputs) := genLLVMTrapFn seed
  let trapFnText := PP.ppFn trapFn
  if parseFuzzLLVMFn trapFnText != some trapFn then
    throw s!"[LLVMAst] roundtrip failed on trap seed {seed} ({trapClass}):\n{trapFnText}"
  let modTrap := mkLLVMMod trapFn
  let trapArgs := trapInputs.map fun w => LLVMVal.bits .i64 w.toBitVec
  let ubMsg ← match execFn modTrap trapFn trapArgs 64 with
    | .ub msg => pure msg
    | other => throw s!"[LLVMAst] trap seed {seed} ({trapClass}) failed to trap in Lean: {reprStr other}"
  let trapObj := Json.mkObj [
    ("id", Json.str s!"llvm_seed_{seed}_trap_{trapClass}"),
    ("seed", toJson seed),
    ("kind", Json.str "trap"),
    ("trapClass", Json.str trapClass),
    ("fnName", Json.str trapFn.name),
    ("roundtripVerified", Json.bool true),
    ("irText", Json.str (PP.ppModule modTrap)),
    ("inputs", u64ArrJson trapInputs),
    ("leanUbReason", Json.str ubMsg)
  ]
  pure [validObj, trapObj]

/-! ## 4. Backend 2: `PTXAst` Seeded Generator, Roundtrip Gate & Evaluator -/

private def ptxIns (i : PTXInstr) : PTXStmt := .instr none i

private def mkPTXMemFromInputs (inputs : List (List UInt64)) (len : Nat) :
    PTXAst.ByteMemory × ParamMemory :=
  let nIn := inputs.length
  let inBufs := inputs.map fun ws => PTXAst.ByteMemory.ofU64Words (ws.map UInt64.toBitVec)
  let outBuf := PTXAst.ByteMemory.zeros (len * 8)
  let allBytes := (inBufs ++ [outBuf]).foldl (fun acc m => acc ++ m.bytes) #[]
  let params :=
    ("param_out", BitVec.ofNat 64 (nIn * len * 8)) ::
    (List.range nIn).map (fun j => (s!"param_in{j}", BitVec.ofNat 64 (j * len * 8))) ++
    [("param_n", BitVec.ofNat 64 len)]
  ({ bytes := allBytes }, { params })

private def readPTXOutputs (g : PTXAst.ByteMemory) (nIn len : Nat) : List UInt64 :=
  (List.range len).map fun i =>
    ((g.loadBits (nIn * len * 8 + i * 8) 8).getD 0#64).toNat.toUInt64

private def ptxOutcomeTag {α : Type} : PTXOutcome α → Option String
  | .ok _ => none
  | .divisionByZero => some "divisionByZero"
  | .signedDivOverflow => some "signedDivOverflow"
  | .misalignedAccess .. => some "misalignedAccess"
  | .readOnlyWrite .. => some "readOnlyWrite"
  | .dataRace .. => some "dataRace"
  | .unsupportedFloatOp _ => some "unsupportedFloatOp"
  | .barrierDivergence _ => some "barrierDivergence"
  | .outOfBoundsLoad .. => some "outOfBoundsLoad"
  | .outOfBoundsStore .. => some "outOfBoundsStore"
  | .unboundParam _ => some "unboundParam"
  | .unboundPred _ => some "unboundPred"
  | .unboundReg _ => some "unboundReg"
  | .typeMismatch _ => some "typeMismatch"
  | .unboundLabel _ => some "unboundLabel"
  | .invalidOperand _ => some "invalidOperand"
  | .fuelExhausted => some "fuelExhausted"

private def genPTXValidKernel (seed : Nat) :
    PTXKernel × PTXKernel × String × Nat × Nat × List (List UInt64) :=
  let r0 := Rng.ofSeed (seed * 4 + 2)
  let kName := s!"ptx_fuzz_valid_{seed}"
  let doneLbl := s!"$L_done_{seed}"
  let (c1, r1) := r0.nextU64
  let (c2, r2) := r1.nextU64
  let imm1 := (c1 &&& 0xFF) + 3
  let imm2 := (c2 &&& 0xFF) + 5
  let (w0, r3) := r2.nextU64
  let (w1, r4) := r3.nextU64
  let (w2, r5) := r4.nextU64
  let (w3, _) := r5.nextU64
  let in0 : List UInt64 := [w0 &&& 0xFFFFFFFF, w1 &&& 0xFFFFFFFF, 0, 42]
  let in1 : List UInt64 := [w2 &&& 0xFFFFFFFF, w3 &&& 0xFFFFFFFF, 7, 42]
  match seed % 3 with
  | 0 =>
    -- Scalar lane-guarded mad + xor + selp
    let headerStmts : List PTXStmt :=
      [ ptxIns (.mov .u32 "%r0" (.sreg .ctaidX))
      , ptxIns (.mov .u32 "%r1" (.sreg .ntidX))
      , ptxIns (.mov .u32 "%r2" (.sreg .tidX))
      , ptxIns (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
      , ptxIns (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
      , ptxIns (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
      , ptxIns (.ldParam .u64 "%rd3" "param_n")
      , ptxIns (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
      , .instr (some { predReg := "%p0" }) (.bra doneLbl)
      , ptxIns (.shl .b64 "%rd4" (.reg "%rd2") (.immU64 3#64))
      , ptxIns (.ldParam .u64 "%rd5" "param_in0")
      , ptxIns (.cvtaToGlobal .u64 "%rd5" (.reg "%rd5"))
      , ptxIns (.add .none .u64 "%rd5" (.reg "%rd5") (.reg "%rd4"))
      , ptxIns (.ldGlobal .u64 "%rd6" (.regOffset "%rd5" 0))
      , ptxIns (.ldParam .u64 "%rd7" "param_in1")
      , ptxIns (.cvtaToGlobal .u64 "%rd7" (.reg "%rd7"))
      , ptxIns (.add .none .u64 "%rd7" (.reg "%rd7") (.reg "%rd4"))
      , ptxIns (.ldGlobal .u64 "%rd8" (.regOffset "%rd7" 0))
      , ptxIns (.mad .lo .u64 "%rd9" (.reg "%rd6") (.immU64 imm1.toBitVec) (.immU64 imm2.toBitVec))
      , ptxIns (.bitXor .b64 "%rd9" (.reg "%rd9") (.reg "%rd8"))
      , ptxIns (.setp .lt .u64 "%p1" (.reg "%rd6") (.reg "%rd8"))
      , ptxIns (.add .none .u64 "%rd10" (.reg "%rd9") (.immU64 9#64))
      , ptxIns (.selp .b64 "%rd11" (.reg "%rd10") (.reg "%rd9") "%p1")
      , ptxIns (.ldParam .u64 "%rd12" "param_out")
      , ptxIns (.cvtaToGlobal .u64 "%rd12" (.reg "%rd12"))
      , ptxIns (.add .none .u64 "%rd12" (.reg "%rd12") (.reg "%rd4")) ]
    let kValid : PTXKernel :=
      { name := kName
      , params := [ { ty := .u64, name := "param_out" }
                  , { ty := .u64, name := "param_in0" }
                  , { ty := .u64, name := "param_in1" }
                  , { ty := .u64, name := "param_n" } ]
      , regDecls := [ { ty := .pred, prefixName := "%p", count := 2 }
                    , { ty := .u32, prefixName := "%r", count := 4 }
                    , { ty := .u64, prefixName := "%rd", count := 14 } ]
      , body := headerStmts ++
          [ ptxIns (.stGlobal .u64 (.regOffset "%rd12" 0) (.reg "%rd11"))
          , .label doneLbl
          , ptxIns .ret ] }
    let kMut : PTXKernel :=
      { kValid with
        body := headerStmts ++
          [ ptxIns (.add .none .u64 "%rd13" (.reg "%rd11") (.immU64 1#64))
          , ptxIns (.stGlobal .u64 (.regOffset "%rd12" 0) (.reg "%rd13"))
          , .label doneLbl
          , ptxIns .ret ] }
    (kValid, kMut, "perturbed output store by +1", 1, 4, [in0, in1])
  | 1 =>
    -- `.shared` + `bar.sync 0` cross-lane neighbor swap (1 CTA x 4 threads)
    let baseStmts : List PTXStmt :=
      [ ptxIns (.mov .u32 "%r0" (.sreg .tidX))
      , ptxIns (.cvt .none .u64 .u32 "%rd0" (.reg "%r0"))
      , ptxIns (.shl .b64 "%rd1" (.reg "%rd0") (.immU64 3#64))
      , ptxIns (.ldParam .u64 "%rd2" "param_in0")
      , ptxIns (.cvtaToGlobal .u64 "%rd2" (.reg "%rd2"))
      , ptxIns (.add .none .u64 "%rd2" (.reg "%rd2") (.reg "%rd1"))
      , ptxIns (.ldGlobal .u64 "%rd3" (.regOffset "%rd2" 0))
      , ptxIns (.mov .u64 "%rd4" (.sym "sh_tile"))
      , ptxIns (.add .none .u64 "%rd5" (.reg "%rd4") (.reg "%rd1"))
      , ptxIns (.stShared .u64 (.regOffset "%rd5" 0) (.reg "%rd3"))
      , ptxIns (.barSync 0)
      , ptxIns (.bitXor .b32 "%r1" (.reg "%r0") (.immU64 1#64))
      , ptxIns (.cvt .none .u64 .u32 "%rd6" (.reg "%r1"))
      , ptxIns (.shl .b64 "%rd7" (.reg "%rd6") (.immU64 3#64))
      , ptxIns (.add .none .u64 "%rd8" (.reg "%rd4") (.reg "%rd7"))
      , ptxIns (.ldShared .u64 "%rd9" (.regOffset "%rd8" 0))
      , ptxIns (.add .none .u64 "%rd9" (.reg "%rd9") (.immU64 imm1.toBitVec))
      , ptxIns (.ldParam .u64 "%rd10" "param_out")
      , ptxIns (.cvtaToGlobal .u64 "%rd10" (.reg "%rd10"))
      , ptxIns (.add .none .u64 "%rd10" (.reg "%rd10") (.reg "%rd1")) ]
    let kValid : PTXKernel :=
      { name := kName
      , params := [ { ty := .u64, name := "param_out" }
                  , { ty := .u64, name := "param_in0" }
                  , { ty := .u64, name := "param_in1" }
                  , { ty := .u64, name := "param_n" } ]
      , regDecls := [ { ty := .u32, prefixName := "%r", count := 3 }
                    , { ty := .u64, prefixName := "%rd", count := 12 } ]
      , sharedDecls := [ { name := "sh_tile", elemTy := .u64, align := 8, count := 4 } ]
      , body := baseStmts ++
          [ ptxIns (.stGlobal .u64 (.regOffset "%rd10" 0) (.reg "%rd9"))
          , ptxIns .ret ] }
    let kMut : PTXKernel :=
      { kValid with
        body := baseStmts ++
          [ ptxIns (.bitXor .b64 "%rd11" (.reg "%rd9") (.immU64 0x55#64))
          , ptxIns (.stGlobal .u64 (.regOffset "%rd10" 0) (.reg "%rd11"))
          , ptxIns .ret ] }
    (kValid, kMut, "perturbed shared-memory neighbor swap output by ^0x55", 1, 4, [in0, in1])
  | _ =>
    -- Guarded unsigned div/rem + shift-right across 2 CTAs x 2 threads
    let baseStmts : List PTXStmt :=
      [ ptxIns (.mov .u32 "%r0" (.sreg .ctaidX))
      , ptxIns (.mov .u32 "%r1" (.sreg .ntidX))
      , ptxIns (.mov .u32 "%r2" (.sreg .tidX))
      , ptxIns (.mul .wide .u32 "%rd0" (.reg "%r0") (.reg "%r1"))
      , ptxIns (.cvt .none .u64 .u32 "%rd1" (.reg "%r2"))
      , ptxIns (.add .none .u64 "%rd2" (.reg "%rd0") (.reg "%rd1"))
      , ptxIns (.ldParam .u64 "%rd3" "param_n")
      , ptxIns (.setp .ge .u64 "%p0" (.reg "%rd2") (.reg "%rd3"))
      , .instr (some { predReg := "%p0" }) (.bra doneLbl)
      , ptxIns (.shl .b64 "%rd4" (.reg "%rd2") (.immU64 3#64))
      , ptxIns (.ldParam .u64 "%rd5" "param_in0")
      , ptxIns (.cvtaToGlobal .u64 "%rd5" (.reg "%rd5"))
      , ptxIns (.add .none .u64 "%rd5" (.reg "%rd5") (.reg "%rd4"))
      , ptxIns (.ldGlobal .u64 "%rd6" (.regOffset "%rd5" 0))
      , ptxIns (.ldParam .u64 "%rd7" "param_in1")
      , ptxIns (.cvtaToGlobal .u64 "%rd7" (.reg "%rd7"))
      , ptxIns (.add .none .u64 "%rd7" (.reg "%rd7") (.reg "%rd4"))
      , ptxIns (.ldGlobal .u64 "%rd8" (.regOffset "%rd7" 0))
      , ptxIns (.bitOr .b64 "%rd8" (.reg "%rd8") (.immU64 1#64))
      , ptxIns (.div .u64 "%rd9" (.reg "%rd6") (.reg "%rd8"))
      , ptxIns (.rem .u64 "%rd10" (.reg "%rd6") (.reg "%rd8"))
      , ptxIns (.shr .u64 "%rd9" (.reg "%rd9") (.immU64 1#64))
      , ptxIns (.add .none .u64 "%rd11" (.reg "%rd9") (.reg "%rd10"))
      , ptxIns (.ldParam .u64 "%rd12" "param_out")
      , ptxIns (.cvtaToGlobal .u64 "%rd12" (.reg "%rd12"))
      , ptxIns (.add .none .u64 "%rd12" (.reg "%rd12") (.reg "%rd4")) ]
    let kValid : PTXKernel :=
      { name := kName
      , params := [ { ty := .u64, name := "param_out" }
                  , { ty := .u64, name := "param_in0" }
                  , { ty := .u64, name := "param_in1" }
                  , { ty := .u64, name := "param_n" } ]
      , regDecls := [ { ty := .pred, prefixName := "%p", count := 2 }
                    , { ty := .u32, prefixName := "%r", count := 4 }
                    , { ty := .u64, prefixName := "%rd", count := 14 } ]
      , body := baseStmts ++
          [ ptxIns (.stGlobal .u64 (.regOffset "%rd12" 0) (.reg "%rd11"))
          , .label doneLbl
          , ptxIns .ret ] }
    let kMut : PTXKernel :=
      { kValid with
        body := baseStmts ++
          [ ptxIns (.sub .u64 "%rd13" (.reg "%rd11") (.immU64 3#64))
          , ptxIns (.stGlobal .u64 (.regOffset "%rd12" 0) (.reg "%rd13"))
          , .label doneLbl
          , ptxIns .ret ] }
    (kValid, kMut, "subtracted 3 from div+rem output", 2, 2, [in0, in1])

private def genPTXTrapKernel (seed : Nat) :
    String × Bool × PTXKernel × Nat × Nat × List (List UInt64) :=
  let kName := s!"ptx_fuzz_trap_{seed}"
  let params : List PTXParamDecl :=
    [ { ty := .u64, name := "param_out" }
    , { ty := .u64, name := "param_in0" }
    , { ty := .u64, name := "param_in1" }
    , { ty := .u64, name := "param_n" } ]
  match seed % 7 with
  | 0 =>
    -- Unsigned division by zero
    ("divisionByZero", false,
      { name := kName, params
      , regDecls := [{ ty := .u64, prefixName := "%rd", count := 6 }]
      , body :=
          [ ptxIns (.ldParam .u64 "%rd0" "param_in0")
          , ptxIns (.cvtaToGlobal .u64 "%rd0" (.reg "%rd0"))
          , ptxIns (.ldGlobal .u64 "%rd1" (.regOffset "%rd0" 0))
          , ptxIns (.ldParam .u64 "%rd2" "param_in1")
          , ptxIns (.cvtaToGlobal .u64 "%rd2" (.reg "%rd2"))
          , ptxIns (.ldGlobal .u64 "%rd3" (.regOffset "%rd2" 0))
          , ptxIns (.div .u64 "%rd4" (.reg "%rd1") (.reg "%rd3"))
          , ptxIns (.ldParam .u64 "%rd5" "param_out")
          , ptxIns (.cvtaToGlobal .u64 "%rd5" (.reg "%rd5"))
          , ptxIns (.stGlobal .u64 (.regOffset "%rd5" 0) (.reg "%rd4"))
          , ptxIns .ret ] },
      1, 1, [[99], [0]])
  | 1 =>
    -- Signed 64-bit INT64_MIN / -1 overflow
    ("signedDivOverflow", false,
      { name := kName, params
      , regDecls := [{ ty := .s64, prefixName := "%rd", count := 6 }]
      , body :=
          [ ptxIns (.ldParam .u64 "%rd0" "param_in0")
          , ptxIns (.cvtaToGlobal .u64 "%rd0" (.reg "%rd0"))
          , ptxIns (.ldGlobal .s64 "%rd1" (.regOffset "%rd0" 0))
          , ptxIns (.ldParam .u64 "%rd2" "param_in1")
          , ptxIns (.cvtaToGlobal .u64 "%rd2" (.reg "%rd2"))
          , ptxIns (.ldGlobal .s64 "%rd3" (.regOffset "%rd2" 0))
          , ptxIns (.div .s64 "%rd4" (.reg "%rd1") (.reg "%rd3"))
          , ptxIns (.ldParam .u64 "%rd5" "param_out")
          , ptxIns (.cvtaToGlobal .u64 "%rd5" (.reg "%rd5"))
          , ptxIns (.stGlobal .s64 (.regOffset "%rd5" 0) (.reg "%rd4"))
          , ptxIns .ret ] },
      1, 1, [[0x8000000000000000], [0xFFFFFFFFFFFFFFFF]])
  | 2 =>
    -- Out-of-bounds global load
    ("outOfBoundsLoad", false,
      { name := kName, params
      , regDecls := [{ ty := .u64, prefixName := "%rd", count := 4 }]
      , body :=
          [ ptxIns (.ldParam .u64 "%rd0" "param_in0")
          , ptxIns (.cvtaToGlobal .u64 "%rd0" (.reg "%rd0"))
          , ptxIns (.ldGlobal .u64 "%rd1" (.regOffset "%rd0" 512))
          , ptxIns (.ldParam .u64 "%rd2" "param_out")
          , ptxIns (.cvtaToGlobal .u64 "%rd2" (.reg "%rd2"))
          , ptxIns (.stGlobal .u64 (.regOffset "%rd2" 0) (.reg "%rd1"))
          , ptxIns .ret ] },
      1, 1, [[11, 22], [33, 44]])
  | 3 =>
    -- Misaligned 8-byte global load (`+4`)
    ("misalignedAccess", false,
      { name := kName, params
      , regDecls := [{ ty := .u64, prefixName := "%rd", count := 4 }]
      , body :=
          [ ptxIns (.ldParam .u64 "%rd0" "param_in0")
          , ptxIns (.cvtaToGlobal .u64 "%rd0" (.reg "%rd0"))
          , ptxIns (.ldGlobal .u64 "%rd1" (.regOffset "%rd0" 4))
          , ptxIns (.ldParam .u64 "%rd2" "param_out")
          , ptxIns (.cvtaToGlobal .u64 "%rd2" (.reg "%rd2"))
          , ptxIns (.stGlobal .u64 (.regOffset "%rd2" 0) (.reg "%rd1"))
          , ptxIns .ret ] },
      1, 1, [[11, 22], [33, 44]])
  | 4 =>
    -- Unsynchronized `.shared` write-write race across 2 lanes without `bar.sync`
    ("dataRace", false,
      { name := kName, params
      , regDecls := [{ ty := .u32, prefixName := "%r", count := 2 },
                     { ty := .u64, prefixName := "%rd", count := 4 }]
      , sharedDecls := [{ name := "sh_race", elemTy := .u64, align := 8, count := 2 }]
      , body :=
          [ ptxIns (.mov .u32 "%r0" (.sreg .tidX))
          , ptxIns (.cvt .none .u64 .u32 "%rd0" (.reg "%r0"))
          , ptxIns (.mov .u64 "%rd1" (.sym "sh_race"))
          , ptxIns (.stShared .u64 (.regOffset "%rd1" 0) (.reg "%rd0"))
          , ptxIns .ret ] },
      1, 2, [[11, 22], [33, 44]])
  | 5 =>
    -- Divergent barrier IDs (`bar.sync 0` vs `bar.sync 1`) across active CTA lanes
    ("barrierDivergence", false,
      { name := kName, params
      , regDecls := [{ ty := .pred, prefixName := "%p", count := 2 },
                     { ty := .u32, prefixName := "%r", count := 2 }]
      , body :=
          [ ptxIns (.mov .u32 "%r0" (.sreg .tidX))
          , ptxIns (.setp .eq .u32 "%p0" (.reg "%r0") (.immU64 0#64))
          , .instr (some { predReg := "%p0", negated := true }) (.bra "$L_b1")
          , ptxIns (.barSync 0)
          , ptxIns (.bra "$L_done")
          , .label "$L_b1"
          , ptxIns (.barSync 1)
          , .label "$L_done"
          , ptxIns .ret ] },
      1, 2, [[11, 22], [33, 44]])
  | _ =>
    -- Static register-width mismatch rejected by both `evalPTXKernel` (`typeMismatch`) and `ptxas -Werror`
    ("typeMismatch", true,
      { name := kName, params
      , regDecls := [{ ty := .u32, prefixName := "%r", count := 2 },
                     { ty := .u64, prefixName := "%rd", count := 2 }]
      , body :=
          [ ptxIns (.ldParam .u64 "%rd0" "param_in0")
          , ptxIns (.add .none .u64 "%r0" (.reg "%rd0") (.immU64 1#64))
          , ptxIns .ret ] },
      1, 1, [[11], [22]])

private def buildPTXSeedCases (seed : Nat) : Except String (List Json) := do
  let (kValid, kMut, mutReason, gridX, blockX, inputs) := genPTXValidKernel seed
  let kText := ppPTXKernel kValid
  let fuelParse := kText.length + 64
  if parsePTXKernel fuelParse kText != some kValid then
    throw s!"[PTXAst] roundtrip failed on valid seed {seed}:\n{kText}"
  let kMutText := ppPTXKernel kMut
  if parsePTXKernel (kMutText.length + 64) kMutText != some kMut then
    throw s!"[PTXAst] roundtrip failed on mutant seed {seed}"
  let len := (inputs[0]?.getD []).length
  let (gMem0, pMem) := mkPTXMemFromInputs inputs len
  let expected ← match evalPTXKernel 4096 kValid { x := gridX, y := 1, z := 1 } { x := blockX, y := 1, z := 1 } gMem0 pMem with
    | .ok gFinal => pure (readPTXOutputs gFinal inputs.length len)
    | other => throw s!"[PTXAst] valid seed {seed} trapped: {reprStr (ptxOutcomeTag other)}"
  let mutOut ← match evalPTXKernel 4096 kMut { x := gridX, y := 1, z := 1 } { x := blockX, y := 1, z := 1 } gMem0 pMem with
    | .ok gMut => pure (readPTXOutputs gMut inputs.length len)
    | other => throw s!"[PTXAst] mutant seed {seed} trapped: {reprStr (ptxOutcomeTag other)}"
  if mutOut == expected then
    throw s!"[PTXAst] mutant failed to diverge on seed {seed}"
  let validObj := Json.mkObj [
    ("id", Json.str s!"ptx_seed_{seed}_valid"),
    ("seed", toJson seed),
    ("kind", Json.str "valid"),
    ("kernelName", Json.str kValid.name),
    ("roundtripVerified", Json.bool true),
    ("gridX", toJson gridX),
    ("blockX", toJson blockX),
    ("arity", toJson inputs.length),
    ("ptxText", Json.str (ppPTXModule { kernels := [kValid] })),
    ("negativeMutantPtx", Json.str (ppPTXModule { kernels := [kMut] })),
    ("negativeMutantReason", Json.str mutReason),
    ("inputs", Json.arr (inputs.map u64ArrJson).toArray),
    ("expected", u64ArrJson expected)
  ]

  let (trapClass, staticReject, kTrap, tGridX, tBlockX, tInputs) := genPTXTrapKernel seed
  let trapText := ppPTXKernel kTrap
  if parsePTXKernel (trapText.length + 64) trapText != some kTrap then
    throw s!"[PTXAst] roundtrip failed on trap seed {seed} ({trapClass}):\n{trapText}"
  let tLen := (tInputs[0]?.getD []).length
  let (tgMem0, tpMem) := mkPTXMemFromInputs tInputs tLen
  let gotTag ← match ptxOutcomeTag (evalPTXKernel 4096 kTrap { x := tGridX, y := 1, z := 1 } { x := tBlockX, y := 1, z := 1 } tgMem0 tpMem) with
    | some tag => pure tag
    | none => throw s!"[PTXAst] trap seed {seed} ({trapClass}) failed to trap in Lean"
  if gotTag != trapClass then
    throw s!"[PTXAst] trap seed {seed} expected {trapClass}, got {gotTag}"
  let trapObj := Json.mkObj [
    ("id", Json.str s!"ptx_seed_{seed}_trap_{trapClass}"),
    ("seed", toJson seed),
    ("kind", Json.str "trap"),
    ("trapClass", Json.str trapClass),
    ("staticReject", Json.bool staticReject),
    ("kernelName", Json.str kTrap.name),
    ("roundtripVerified", Json.bool true),
    ("gridX", toJson tGridX),
    ("blockX", toJson tBlockX),
    ("arity", toJson tInputs.length),
    ("ptxText", Json.str (ppPTXModule { kernels := [kTrap] })),
    ("inputs", Json.arr (tInputs.map u64ArrJson).toArray)
  ]
  pure [validObj, trapObj]

/-! ## 5. Backend 3: `StableHLOAst` Seeded Generator, Roundtrip Gate & Evaluator -/

private def ppElemStr : ElemType → String
  | .i1 => "i1" | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .ui8 => "ui8" | .ui16 => "ui16" | .ui32 => "ui32" | .ui64 => "ui64"
  | .f32 => "f32" | .f64 => "f64" | .bf16 => "bf16"

private def tensorValJson (tv : TensorVal) : Json :=
  Json.mkObj [
    ("shape", natArrJson tv.ty.shape),
    ("elem", Json.str (ppElemStr tv.ty.elem)),
    ("words", u64ArrJson (tv.data.toList.map (fun bv => bv.toNat.toUInt64)))
  ]

private def maskElemWord (e : ElemType) (w : UInt64) : BitVec 64 :=
  match intBitWidth? e with
  | some 1 => if (w &&& 1) == 1 then 1#64 else 0#64
  | some 8 => (w &&& 0xFF).toBitVec
  | some 16 => (w &&& 0xFFFF).toBitVec
  | some 32 => (w &&& 0xFFFFFFFF).toBitVec
  | _ => w.toBitVec

private def mkTensor (shape : List Nat) (elem : ElemType) (raw : List UInt64) : TensorVal :=
  let n := shape.foldl (· * ·) 1
  let padded := (List.range n).map fun i => maskElemWord elem (raw[i]?.getD (i.toUInt64 + 1))
  { ty := { shape, elem }, data := padded.toArray }

private def shapeErrTag : ShapeError → String
  | .unbound s => s!"unbound:{s}"
  | .typeMismatch .. => "typeMismatch"
  | .shapeMismatch s => s!"shapeMismatch:{s}"
  | .rankMismatch .. => "rankMismatch"
  | .volumeMismatch .. => "volumeMismatch"
  | .divisionByZero => "divisionByZero"

private def genStableHLOValidCase (seed : Nat) :
    FuncOp × FuncOp × String × Bool × List TensorVal :=
  let r0 := Rng.ofSeed (seed * 4 + 3)
  let fnName := s!"hlo_fuzz_valid_{seed}"
  let (w0, r1) := r0.nextU64
  let (w1, r2) := r1.nextU64
  let (w2, r3) := r2.nextU64
  let (w3, _) := r3.nextU64
  match seed % 5 with
  | 0 =>
    -- Multi-width arithmetic + compare + select across i8/ui8/i16/ui16/i32/ui32/i64/ui64
    let elems : List ElemType := [.i8, .ui8, .i16, .ui16, .i32, .ui32, .i64, .ui64]
    let elem := elems[(seed / 5) % elems.length]?.getD .i64
    let ty : TensorType := { shape := [4], elem }
    let fn : FuncOp :=
      { name := fnName
      , params := [("a", ty), ("b", ty)]
      , result := ty
      , body :=
          [ .add "t0" "a" "b"
          , .multiply "t1" "a" "b"
          , .xor "t2" "t0" "t1"
          , .compare "p" "a" "b" .lt
          , .select "r" "p" "t2" "t0"
          , .returnOp "r" ] }
    let mutFn : FuncOp :=
      { fn with body :=
          [ .add "t0" "a" "b"
          , .multiply "t1" "a" "b"
          , .xor "t2" "t0" "t1"
          , .compare "p" "a" "b" .ge
          , .select "r" "p" "t2" "t0"
          , .returnOp "r" ] }
    let a := mkTensor [4] elem [w0, w1 ||| 2, 1, 7]
    let b := mkTensor [4] elem [w2 ||| 1, w3, 5, 3]
    (fn, mutFn, "flipped compare direction LT -> GE", true, [a, b])
  | 1 =>
    -- OpenXLA signed INT64_MIN / -1 and INT64_MIN % -1 edge-case agreement (`i64`)
    let ty : TensorType := { shape := [4], elem := .i64 }
    let fn : FuncOp :=
      { name := fnName
      , params := [("a", ty), ("b", ty)]
      , result := ty
      , body :=
          [ .divide "q" "a" "b"
          , .remainder "rm" "a" "b"
          , .add "r" "q" "rm"
          , .returnOp "r" ] }
    let mutFn : FuncOp :=
      { fn with body :=
          [ .divide "q" "a" "b"
          , .remainder "rm" "a" "b"
          , .subtract "r" "q" "b"
          , .returnOp "r" ] }
    let a := mkTensor [4] .i64 [0x8000000000000000, w0, 0xFFFFFFFFFFFFFF9C, 42]
    let b := mkTensor [4] .i64 [0xFFFFFFFFFFFFFFFF, (w1 &&& 0xFF) ||| 3, 7, 0xFFFFFFFFFFFFFFFB]
    (fn, mutFn, "replaced q + rem with q - b", true, [a, b])
  | 2 =>
    -- `reshape` + `slice` + `broadcast_in_dim` + `convert` (`ui32` -> `i64`)
    let inTy : TensorType := { shape := [2, 2], elem := .ui32 }
    let scTy : TensorType := { shape := [], elem := .i64 }
    let outTy : TensorType := { shape := [2], elem := .i64 }
    let fn : FuncOp :=
      { name := fnName
      , params := [("m", inTy), ("s", scTy)]
      , result := outTy
      , body :=
          [ .reshape "v4" "m" [4]
          , .slice "v2" "v4" [1] [4] [2]
          , .convert "v2_64" "v2" .i64
          , .broadcastInDim "sb" "s" [2] []
          , .add "r" "v2_64" "sb"
          , .returnOp "r" ] }
    let mutFn : FuncOp :=
      { fn with body :=
          [ .reshape "v4" "m" [4]
          , .slice "v2" "v4" [0] [3] [2]
          , .convert "v2_64" "v2" .i64
          , .broadcastInDim "sb" "s" [2] []
          , .add "r" "v2_64" "sb"
          , .returnOp "r" ] }
    let m := mkTensor [2, 2] .ui32 [w0 + 1, w1 + 2, w2 + 3, w3 + 4]
    let s := mkTensor [] .i64 [(w0 &&& 0xFF) + 9]
    (fn, mutFn, "shifted slice start 1:4:2 -> 0:3:2", true, [m, s])
  | 3 =>
    -- `dot_general` [2, 3] x [3, 2] -> [2, 2] (`i32`)
    let ta : TensorType := { shape := [2, 3], elem := .i32 }
    let tb : TensorType := { shape := [3, 2], elem := .i32 }
    let tout : TensorType := { shape := [2, 2], elem := .i32 }
    let fn : FuncOp :=
      { name := fnName
      , params := [("a", ta), ("b", tb)]
      , result := tout
      , body :=
          [ .dotGeneral "d" "a" "b" [] [] [1] [0] [2, 2]
          , .maximum "r" "d" "d"
          , .returnOp "r" ] }
    let mutFn : FuncOp :=
      { fn with body :=
          [ .dotGeneral "d" "a" "b" [] [] [1] [0] [2, 2]
          , .add "r" "d" "d"
          , .returnOp "r" ] }
    let a := mkTensor [2, 3] .i32 [1, 2, 3, 4, 5, (w0 &&& 0xF) + 1]
    let b := mkTensor [3, 2] .i32 [2, 1, 0, 3, (w1 &&& 0xF) + 2, 4]
    (fn, mutFn, "doubled dot_general output via add d, d", true, [a, b])
  | _ =>
    -- `dynamic_slice` with negative / OOB signed `i64` start index clamping (OpenXLA clamp semantics)
    let srcTy : TensorType := { shape := [6], elem := .i64 }
    let idxTy : TensorType := { shape := [], elem := .i64 }
    let outTy : TensorType := { shape := [3], elem := .i64 }
    let fn : FuncOp :=
      { name := fnName
      , params := [("x", srcTy), ("idx", idxTy)]
      , result := outTy
      , body :=
          [ .dynamicSlice "ds" "x" ["idx"] [3]
          , .returnOp "ds" ] }
    let mutFn : FuncOp :=
      { fn with body :=
          [ .slice "ds" "x" [0] [3] [1]
          , .returnOp "ds" ] }
    -- Pass OOB positive index `99` so `clampStart 6 3 99 = 3` (`x[3..6]`), diverging from `x[0..3]`
    let x := mkTensor [6] .i64 [10, 20, 30, 40 + (w0 &&& 0xFF), 50 + (w1 &&& 0xFF), 60]
    let idx := mkTensor [] .i64 [99]
    (fn, mutFn, "replaced clamped dynamic_slice with fixed slice 0:3:1", false, [x, idx])

private def genStableHLOTrapCase (seed : Nat) :
    String × Bool × FuncOp × List TensorVal :=
  let fnName := s!"hlo_fuzz_trap_{seed}"
  match seed % 3 with
  | 0 =>
    -- Signed i64 division by zero
    let ty : TensorType := { shape := [2], elem := .i64 }
    ("divisionByZero", false,
      { name := fnName
      , params := [("a", ty), ("b", ty)]
      , result := ty
      , body := [.divide "q" "a" "b", .returnOp "q"] },
      [mkTensor [2] .i64 [42, 99], mkTensor [2] .i64 [1, 0]])
  | 1 =>
    -- Unsigned ui32 remainder by zero
    let ty : TensorType := { shape := [2], elem := .ui32 }
    ("divisionByZero", false,
      { name := fnName
      , params := [("a", ty), ("b", ty)]
      , result := ty
      , body := [.remainder "r" "a" "b", .returnOp "r"] },
      [mkTensor [2] .ui32 [17, 29], mkTensor [2] .ui32 [0, 3]])
  | _ =>
    -- Static shape mismatch on `reshape` (`[4] -> [3]`): rejected by both `evalFuncOp` (`volumeMismatch`)
    -- and OpenXLA MLIR `Module.parse` / `operation.verify()`.
    let inTy : TensorType := { shape := [4], elem := .i64 }
    let badOut : TensorType := { shape := [3], elem := .i64 }
    let badMlirFn : FuncOp :=
      { name := fnName
      , params := [("a", inTy)]
      , result := badOut
      , body := [.reshape "bad" "a" [3], .returnOp "bad"] }
    ("volumeMismatch", true, badMlirFn, [mkTensor [4] .i64 [1, 2, 3, 4]])

private def buildStableHLOSeedCases (seed : Nat) : Except String (List Json) := do
  let (validFn, mutFn, mutReason, checkRoundtrip, args) := genStableHLOValidCase seed
  if checkRoundtrip then
    let fnText := ppFuncOp validFn
    if parseFuncOp fnText != some validFn then
      throw s!"[StableHLOAst] roundtrip failed on valid seed {seed}:\n{fnText}"
  let expected ← match evalFuncOp validFn args with
    | .ok tv => pure tv
    | .error err => throw s!"[StableHLOAst] valid seed {seed} failed in Lean: {shapeErrTag err}"
  let mutTv ← match evalFuncOp mutFn args with
    | .ok tv => pure tv
    | .error err => throw s!"[StableHLOAst] mutant seed {seed} failed in Lean: {shapeErrTag err}"
  if mutTv.data == expected.data then
    throw s!"[StableHLOAst] mutant failed to diverge on seed {seed}"
  let modValid : ModuleOp := { name := s!"hlo_mod_{seed}", funcs := [validFn] }
  let modMut : ModuleOp := { name := s!"hlo_mod_{seed}", funcs := [mutFn] }
  let validObj := Json.mkObj [
    ("id", Json.str s!"stablehlo_seed_{seed}_valid"),
    ("seed", toJson seed),
    ("kind", Json.str "valid"),
    ("funcName", Json.str validFn.name),
    ("roundtripVerified", Json.bool checkRoundtrip),
    ("mlirText", Json.str (ppModuleOp modValid)),
    ("negativeMutantMlir", Json.str (ppModuleOp modMut)),
    ("negativeMutantReason", Json.str mutReason),
    ("args", Json.arr (args.map tensorValJson).toArray),
    ("expected", tensorValJson expected)
  ]

  let (trapClass, staticReject, trapFn, trapArgs) := genStableHLOTrapCase seed
  let gotErr ← match evalFuncOp trapFn trapArgs with
    | .error err => pure (shapeErrTag err)
    | .ok _ => throw s!"[StableHLOAst] trap seed {seed} ({trapClass}) failed to trap in Lean"
  if !(gotErr.startsWith trapClass) then
    throw s!"[StableHLOAst] trap seed {seed} expected {trapClass}, got {gotErr}"
  -- For staticReject (`reshape` volume mismatch), emit explicit MLIR with mismatched tensor volume
  -- so OpenXLA `Module.parse` / `verify()` sees the exact ill-typed operation.
  let trapMlir :=
    if staticReject then
      s!"module @hlo_trap_mod_{seed} \{\n  func.func @{trapFn.name}(%a: tensor<4xi64>) -> tensor<3xi64> \{\n    %bad = stablehlo.reshape %a : (tensor<4xi64>) -> tensor<3xi64>\n    return %bad : tensor<3xi64>\n  }\n}"
    else
      ppModuleOp { name := s!"hlo_trap_mod_{seed}", funcs := [trapFn] }
  let trapObj := Json.mkObj [
    ("id", Json.str s!"stablehlo_seed_{seed}_trap_{trapClass}"),
    ("seed", toJson seed),
    ("kind", Json.str "trap"),
    ("trapClass", Json.str trapClass),
    ("staticReject", Json.bool staticReject),
    ("funcName", Json.str trapFn.name),
    ("mlirText", Json.str trapMlir),
    ("args", Json.arr (trapArgs.map tensorValJson).toArray)
  ]
  pure [validObj, trapObj]

/-! ## 6. Backend 4: `MetalAst` Seeded Generator, Roundtrip Gate & Evaluator -/

private def mslOutcomeTag {α : Type} : MSLOutcome α → Option String
  | .ok _ => none
  | .readOnlyViolation .. => some "readOnlyViolation"
  | .barrierDivergence => some "barrierDivergence"
  | .divisionByZero => some "divisionByZero"
  | .signedDivOverflow => some "signedDivOverflow"
  | .shiftOutOfRange => some "shiftOutOfRange"
  | .dataRace .. => some "dataRace"
  | .unsupportedFloatOp _ => some "unsupportedFloatOp"
  | .outOfBoundsLoad .. => some "outOfBoundsLoad"
  | .outOfBoundsWrite .. => some "outOfBoundsWrite"
  | .unboundIdentifier _ => some "unboundIdentifier"
  | .fuelExhausted => some "fuelExhausted"

private def mkMetalBuffers (inputs : List (List UInt64)) (len : Nat) :
    List (Nat × MetalAst.ByteMemory) × List (Nat × MetalAst.ByteMemory) :=
  let nIn := inputs.length
  let dev :=
    (List.range nIn).map (fun j =>
      (j, MetalAst.ByteMemory.ofU64Words ((inputs[j]?.getD []).map UInt64.toBitVec))) ++
    [(nIn, MetalAst.ByteMemory.zeros (len * 8))]
  let cst := [(nIn + 1, MetalAst.ByteMemory.ofU64Words [BitVec.ofNat 64 len])]
  (dev, cst)

private def readMetalOut (bufs : List (Nat × MetalAst.ByteMemory)) (nIn len : Nat) :
    Option (List UInt64) := do
  let m ← bufs.lookup nIn
  pure ((List.range len).map fun i => ((m.readU64Word? i).getD 0#64).toNat.toUInt64)

private def stdMetalParams (kName : String) : List MSLParamDecl :=
  let _ := kName
  [ { ty := .pointer .device true .ulong, name := "in0", attr := some (.buffer 0) }
  , { ty := .pointer .device true .ulong, name := "in1", attr := some (.buffer 1) }
  , { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer 2) }
  , { ty := .ref .constant .ulong, name := "n", attr := some (.buffer 3) }
  , { ty := .uint, name := "gid", attr := some .threadPositionInGrid } ]

private def genMetalValidKernel (seed : Nat) :
    MSLKernelDecl × MSLKernelDecl × String × Bool × Nat × Nat × List (List UInt64) :=
  let r0 := Rng.ofSeed (seed * 4 + 4)
  let kName := s!"msl_fuzz_valid_{seed}"
  let (w0, r1) := r0.nextU64
  let (w1, r2) := r1.nextU64
  let (w2, r3) := r2.nextU64
  let (w3, _) := r3.nextU64
  let c1 := (w0 &&& 0xFF) + 5
  let in0 : List UInt64 := [w0 &&& 0xFFFFFFFF, w1 &&& 0xFFFFFFFF, 19, 88]
  let in1 : List UInt64 := [w2 &&& 0xFFFFFFFF, w3 &&& 0xFFFFFFFF, 23, 88]
  match seed % 3 with
  | 0 =>
    -- Scalar guarded kernel with clz, masked shift, ternary select
    let rhsValid : MSLExpr :=
      .select (.lt (.index "in0" (.var "gid")) (.index "in1" (.var "gid")))
        (.add (.shl (.index "in0" (.var "gid")) (.bitAnd (.index "in1" (.var "gid")) (.immU64 15#64)))
              (.immU64 c1.toBitVec))
        (.bitXor (.clz (.index "in0" (.var "gid"))) (.index "in1" (.var "gid")))
    let rhsMut : MSLExpr := .add rhsValid (.immU64 1#64)
    let kValid : MSLKernelDecl :=
      { name := kName
      , params := stdMetalParams kName
      , body :=
          [ .ifElse (.lt (.cast .ulong (.var "gid")) (.var "n"))
              (.cons (.indexAssign "out" (.var "gid") rhsValid) .nil) .nil
          , .returnStmt ] }
    let kMut : MSLKernelDecl :=
      { kValid with
        body :=
          [ .ifElse (.lt (.cast .ulong (.var "gid")) (.var "n"))
              (.cons (.indexAssign "out" (.var "gid") rhsMut) .nil) .nil
          , .returnStmt ] }
    (kValid, kMut, "perturbed scalar Metal kernel output by +1", true, 1, 4, [in0, in1])
  | 1 =>
    -- Scalar guarded kernel with varDecl, ifElse branch, and guarded division
    let kValid : MSLKernelDecl :=
      { name := kName
      , params := stdMetalParams kName
      , body :=
          [ .ifElse (.lt (.cast .ulong (.var "gid")) (.var "n"))
              (.cons (.varDecl .ulong "va" (.index "in0" (.var "gid")))
                (.cons (.varDecl .ulong "vb" (.bitOr (.index "in1" (.var "gid")) (.immU64 1#64)))
                  (.cons (.varDecl .ulong "q" (.div (.var "va") (.var "vb")))
                    (.cons (.indexAssign "out" (.var "gid")
                      (.add (.mul (.var "q") (.immU64 c1.toBitVec)) (.rem (.var "va") (.var "vb")))) .nil))))
              .nil
          , .returnStmt ] }
    let kMut : MSLKernelDecl :=
      { kValid with
        body :=
          [ .ifElse (.lt (.cast .ulong (.var "gid")) (.var "n"))
              (.cons (.varDecl .ulong "va" (.index "in0" (.var "gid")))
                (.cons (.varDecl .ulong "vb" (.bitOr (.index "in1" (.var "gid")) (.immU64 1#64)))
                  (.cons (.varDecl .ulong "q" (.div (.var "va") (.var "vb")))
                    (.cons (.indexAssign "out" (.var "gid")
                      (.sub (.mul (.var "q") (.immU64 c1.toBitVec)) (.immU64 7#64))) .nil))))
              .nil
          , .returnStmt ] }
    (kValid, kMut, "replaced + rem(va,vb) with - 7", true, 2, 2, [in0, in1])
  | _ =>
    -- `threadgroup` shared-array + `threadgroup_barrier` neighbor swap (1 group x 4 threads)
    let kValid : MSLKernelDecl :=
      { name := kName
      , params := stdMetalParams kName
      , sharedDecls := [{ elemTy := .ulong, name := "sh_tile", count := 4 }]
      , body :=
          [ .indexAssign "sh_tile" (.var "gid") (.index "in0" (.var "gid"))
          , .threadgroupBarrier
          , .varDecl .ulong "mate" (.bitXor (.cast .ulong (.var "gid")) (.immU64 1#64))
          , .indexAssign "out" (.var "gid")
              (.add (.index "sh_tile" (.var "mate")) (.index "in1" (.var "gid")))
          , .returnStmt ] }
    let kMut : MSLKernelDecl :=
      { kValid with
        body :=
          [ .indexAssign "sh_tile" (.var "gid") (.index "in0" (.var "gid"))
          , .threadgroupBarrier
          , .varDecl .ulong "mate" (.bitXor (.cast .ulong (.var "gid")) (.immU64 1#64))
          , .indexAssign "out" (.var "gid")
              (.bitXor (.index "sh_tile" (.var "mate")) (.immU64 0xAA#64))
          , .returnStmt ] }
    (kValid, kMut, "replaced + in1[gid] with ^ 0xAA on threadgroup swap", false, 1, 4, [in0, in1])

private def genMetalTrapKernel (seed : Nat) :
    String × Bool × MSLKernelDecl × Nat × Nat × List (List UInt64) :=
  let kName := s!"msl_fuzz_trap_{seed}"
  let params := stdMetalParams kName
  match seed % 5 with
  | 0 =>
    -- Unsigned division by zero
    ("divisionByZero", true,
      { name := kName, params
      , body := [ .indexAssign "out" (.var "gid")
                    (.div (.index "in0" (.var "gid")) (.index "in1" (.var "gid")))
                , .returnStmt ] },
      1, 1, [[77], [0]])
  | 1 =>
    -- Signed 64-bit `long` `INT64_MIN / -1` overflow
    ("signedDivOverflow", true,
      { name := kName, params
      , body :=
          [ .varDecl .long "sa" (.cast .long (.index "in0" (.var "gid")))
          , .varDecl .long "sb" (.cast .long (.index "in1" (.var "gid")))
          , .indexAssign "out" (.var "gid") (.cast .ulong (.div (.var "sa") (.var "sb")))
          , .returnStmt ] },
      1, 1, [[0x8000000000000000], [0xFFFFFFFFFFFFFFFF]])
  | 2 =>
    -- Shift out of range (`>= 64`)
    ("shiftOutOfRange", true,
      { name := kName, params
      , body :=
          [ .varDecl .ulong "sh" (.index "in1" (.var "gid"))
          , .indexAssign "out" (.var "gid") (.shl (.index "in0" (.var "gid")) (.var "sh"))
          , .returnStmt ] },
      1, 1, [[13], [64]])
  | 3 =>
    -- Immediate post-buffer out-of-bounds `device` buffer read (`gid + 2`, inside ASan 16B redzone)
    ("outOfBoundsLoad", true,
      { name := kName, params
      , body :=
          [ .indexAssign "out" (.var "gid")
              (.index "in0" (.add (.cast .ulong (.var "gid")) (.immU64 2#64)))
          , .returnStmt ] },
      1, 2, [[11, 22], [33, 44]])
  | _ =>
    -- Unsynchronized `threadgroup` shared-array write-write data race across 2 threads
    ("dataRace", false,
      { name := kName, params
      , sharedDecls := [{ elemTy := .ulong, name := "sh_race", count := 2 }]
      , body :=
          [ .indexAssign "sh_race" (.immU64 0#64) (.index "in0" (.var "gid"))
          , .indexAssign "out" (.var "gid") (.index "sh_race" (.immU64 0#64))
          , .returnStmt ] },
      1, 2, [[101, 202], [1, 2]])

private def verifyMSLBodyRoundtrip (stmts : List MSLStmt) : Bool :=
  let blk := MSLBlock.ofList stmts
  let txt := ppMSLBlock "    " blk
  parseMSLBlock (txt.length + 128) "    " txt.toList == some (blk, [])

private def buildMetalSeedCases (seed : Nat) : Except String (List Json) := do
  let (kValid, kMut, mutReason, scalarKernelRt, gridX, groupX, inputs) := genMetalValidKernel seed
  if scalarKernelRt then
    let kText := ppMSLKernel kValid
    if parseMSLKernel (kText.length + 128) kText != some kValid then
      throw s!"[MetalAst] kernel roundtrip failed on valid seed {seed}:\n{kText}"
  else if !verifyMSLBodyRoundtrip kValid.body then
    throw s!"[MetalAst] block roundtrip failed on threadgroup valid seed {seed}"
  let len := (inputs[0]?.getD []).length
  let (dev0, cst0) := mkMetalBuffers inputs len
  let expected ← match evalMSLKernel 4096 kValid { x := gridX, y := 1, z := 1 } { x := groupX, y := 1, z := 1 } dev0 cst0 with
    | .ok bufs =>
      match readMetalOut bufs inputs.length len with
      | some ws => pure ws
      | none => throw s!"[MetalAst] missing output buffer on valid seed {seed}"
    | other => throw s!"[MetalAst] valid seed {seed} trapped: {reprStr (mslOutcomeTag other)}"
  let mutOut ← match evalMSLKernel 4096 kMut { x := gridX, y := 1, z := 1 } { x := groupX, y := 1, z := 1 } dev0 cst0 with
    | .ok bufs =>
      match readMetalOut bufs inputs.length len with
      | some ws => pure ws
      | none => throw s!"[MetalAst] missing output buffer on mutant seed {seed}"
    | other => throw s!"[MetalAst] mutant seed {seed} trapped: {reprStr (mslOutcomeTag other)}"
  if mutOut == expected then
    throw s!"[MetalAst] mutant failed to diverge on seed {seed}"
  let validObj := Json.mkObj [
    ("id", Json.str s!"metal_seed_{seed}_valid"),
    ("seed", toJson seed),
    ("kind", Json.str "valid"),
    ("kernelName", Json.str kValid.name),
    ("usesThreadgroup", Json.bool (!kValid.sharedDecls.isEmpty)),
    ("roundtripVerified", Json.bool true),
    ("gridX", toJson gridX),
    ("groupX", toJson groupX),
    ("arity", toJson inputs.length),
    ("mslText", Json.str (ppMSLModule { kernels := [kValid] })),
    ("negativeMutantMsl", Json.str (ppMSLModule { kernels := [kMut] })),
    ("negativeMutantReason", Json.str mutReason),
    ("inputs", Json.arr (inputs.map u64ArrJson).toArray),
    ("expected", u64ArrJson expected)
  ]

  let (trapClass, scalarTrapRt, kTrap, tGridX, tGroupX, tInputs) := genMetalTrapKernel seed
  if scalarTrapRt then
    let trapText := ppMSLKernel kTrap
    if parseMSLKernel (trapText.length + 128) trapText != some kTrap then
      throw s!"[MetalAst] kernel roundtrip failed on trap seed {seed} ({trapClass}):\n{trapText}"
  else if !verifyMSLBodyRoundtrip kTrap.body then
    throw s!"[MetalAst] block roundtrip failed on threadgroup trap seed {seed}"
  let tLen := (tInputs[0]?.getD []).length
  let (tDev0, tCst0) := mkMetalBuffers tInputs tLen
  let gotTag ← match mslOutcomeTag (evalMSLKernel 4096 kTrap { x := tGridX, y := 1, z := 1 } { x := tGroupX, y := 1, z := 1 } tDev0 tCst0) with
    | some tag => pure tag
    | none => throw s!"[MetalAst] trap seed {seed} ({trapClass}) failed to trap in Lean"
  if gotTag != trapClass then
    throw s!"[MetalAst] trap seed {seed} expected {trapClass}, got {gotTag}"
  let trapObj := Json.mkObj [
    ("id", Json.str s!"metal_seed_{seed}_trap_{trapClass}"),
    ("seed", toJson seed),
    ("kind", Json.str "trap"),
    ("trapClass", Json.str trapClass),
    ("usesThreadgroup", Json.bool (!kTrap.sharedDecls.isEmpty)),
    ("kernelName", Json.str kTrap.name),
    ("roundtripVerified", Json.bool true),
    ("gridX", toJson tGridX),
    ("groupX", toJson tGroupX),
    ("arity", toJson tInputs.length),
    ("mslText", Json.str (ppMSLModule { kernels := [kTrap] })),
    ("inputs", Json.arr (tInputs.map u64ArrJson).toArray)
  ]
  pure [validObj, trapObj]

/-! ## 7. CLI Entrypoint (`target-ir-fuzz-suite`) -/

private def findOptVal (args : List String) (flag : String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | k :: v :: rest => if k == flag then some v else go (v :: rest)
    | [_] => none
  go args

def buildSuiteJson (seedStart numSeeds : Nat) (backends : List String) : Except String Json := do
  let seedRange := (List.range numSeeds).map (seedStart + ·)
  let want (b : String) : Bool := backends.isEmpty || backends.contains b
  let llvmCases ←
    if want "llvm" then
      (seedRange.mapM buildLLVMSeedCases).map List.flatten
    else pure []
  let ptxCases ←
    if want "ptx" then
      (seedRange.mapM buildPTXSeedCases).map List.flatten
    else pure []
  let hloCases ←
    if want "stablehlo" then
      (seedRange.mapM buildStableHLOSeedCases).map List.flatten
    else pure []
  let metalCases ←
    if want "metal" then
      (seedRange.mapM buildMetalSeedCases).map List.flatten
    else pure []
  pure <| Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("seedStart", toJson seedStart),
    ("seeds", toJson numSeeds),
    ("llvmCases", Json.arr llvmCases.toArray),
    ("ptxCases", Json.arr ptxCases.toArray),
    ("stablehloCases", Json.arr hloCases.toArray),
    ("metalCases", Json.arr metalCases.toArray)
  ]

def run (args : List String) : IO UInt32 := do
  if args.contains "--self-test" then
    match buildSuiteJson 0 12 ["llvm", "ptx", "stablehlo", "metal"] with
    | .ok _ =>
      IO.println "[target-ir-fuzz-suite] self-test: 12 seeds x 4 backends (roundtrip + valid + trap + mutant) PASSED"
      return 0
    | .error err =>
      IO.eprintln s!"[target-ir-fuzz-suite] self-test FAILED: {err}"
      return 1
  let seedStart := (findOptVal args "--seed-start" >>= String.toNat?).getD 0
  let numSeeds := (findOptVal args "--seeds" >>= String.toNat?).getD 16
  let backends :=
    match findOptVal args "--backends" with
    | some csv => (csv.splitOn ",").map trimStr |>.filter (!·.isEmpty)
    | none => ["llvm", "ptx", "stablehlo", "metal"]
  match buildSuiteJson seedStart numSeeds backends with
  | .ok j =>
    IO.println (Json.compress j)
    return 0
  | .error err =>
    IO.eprintln s!"[target-ir-fuzz-suite] error: {err}"
    return 1

end LeanNative.Driver.TargetIRFuzzCLI
