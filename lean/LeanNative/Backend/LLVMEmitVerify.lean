import LeanNative.IR.AST
import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVM
import LeanNative.Backend.LLVMAst

/-!
# LLVM Text Emitter Parse-and-Execute Verification (`LeanNative.Backend.LLVMEmitVerify`)

Parses the LLVM 18 text emitted by `LeanNative.Backend.LLVM.emitDeclLLVM` into
`LeanNative.Backend.LLVMAst.LLVMFn` and executes it on `LeanNative.Backend.LLVMAst.Eval`
(`execBlockWith` + `ByteMem`) against `LeanNative.Semantics.evalCode` across scalar ALU
(`sub`, `shl`, `shr`, `lt`, `div`, `mod` including zero divisors) and `parFor` array
bounds probes.
-/

namespace LeanNative.Backend.LLVMEmitVerify

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVM
open LeanNative.Backend.LLVMAst

def dropStr (s : String) (n : Nat) : String :=
  (s.drop n).toString

def dropEndStr (s : String) (n : Nat) : String :=
  (s.dropEnd n).toString

def stripComma (s : String) : String :=
  if s.endsWith "," then dropEndStr s 1 else s

def stripComment (s : String) : String :=
  match s.splitOn ";" with
  | [] => ""
  | h :: _ => h.trimAscii.toString

def toks (s : String) : List String :=
  (s.splitOn " ").filter (· != "")

def parseIntW : String → Option IntWidth
  | "i1" => some .i1 | "i8" => some .i8 | "i16" => some .i16
  | "i32" => some .i32 | "i64" => some .i64 | "i128" => some .i128
  | "i256" => some .i256 | _ => none

def parseSimpleTy (s0 : String) : Option LLVMType :=
  let s := stripComma s0
  if s == "ptr" then some (.ptr 0)
  else if s == "void" then some .void
  else (parseIntW s).map .int

def parseOp (w? : Option IntWidth) (tok0 : String) : Option Operand :=
  let tok := stripComma tok0
  if tok.startsWith "%" then some (.reg (dropStr tok 1))
  else if tok.startsWith "@" then some (.global (dropStr tok 1))
  else if tok == "null" then some .constNull
  else if tok == "zeroinitializer" then some .constZero
  else if tok == "poison" then some .poison
  else if tok == "true" then some (.constInt .i1 1#1)
  else if tok == "false" then some (.constInt .i1 0#1)
  else
    let w := w?.getD .i64
    (tok.toNat?).map fun n => .constInt w (BitVec.ofNat w.bits n)

def parseTypedOp (tyTok valTok : String) : Option (LLVMType × Operand) := do
  let ty ← parseSimpleTy tyTok
  let w? := match ty with | .int w => some w | _ => none
  let op ← parseOp w? valTok
  some (ty, op)

def parseICmpPred : String → Option ICmpPred
  | "eq" => some .eq | "ne" => some .ne | "ult" => some .ult | "ule" => some .ule
  | "ugt" => some .ugt | "uge" => some .uge | "slt" => some .slt | "sle" => some .sle
  | "sgt" => some .sgt | "sge" => some .sge | _ => none

def parseAlignTail : List String → Nat
  | ["align", nStr] => nStr.toNat?.getD 0
  | _ => 0

def parsePhiArms (ty : LLVMType) (rhs : String) : Option (List (Operand × BlockLabel)) :=
  let w? := match ty with | .int w => some w | _ => none
  let parts := (rhs.splitOn "[").drop 1
  parts.mapM fun p => do
    let inner := ((p.splitOn "]").headD "").trimAscii.toString
    match inner.splitOn "," with
    | [vPart, lPart] =>
      let op ← parseOp w? vPart.trimAscii.toString
      let lt := lPart.trimAscii.toString
      if lt.startsWith "%" then some (op, dropStr lt 1) else none
    | _ => none

def parsePhiLine (line : String) : Option PhiNode := do
  let ws := toks line
  match ws with
  | dstTok :: "=" :: "phi" :: tyTok :: _ =>
    if !dstTok.startsWith "%" then none
    else
      let ty ← parseSimpleTy tyTok
      let arms ← parsePhiArms ty line
      some { dst := dropStr dstTok 1, ty := ty, incomings := arms }
  | _ => none

def parseFlags : List String → OverflowFlags × List String
  | "nuw" :: "nsw" :: rest | "nsw" :: "nuw" :: rest => (.nswNuw, rest)
  | "nuw" :: rest => (.nuw, rest)
  | "nsw" :: rest => (.nsw, rest)
  | rest => (.none, rest)

def parseCallLine (dst? : Option RegName) (afterCall : List String) : Option LLVMInstr := do
  let joined := String.intercalate " " afterCall
  let (headPart, restParts) := match joined.splitOn "(" with
    | h :: t => (h.trimAscii.toString, String.intercalate "(" t)
    | [] => ("", "")
  let argBody := (restParts.splitOn ")").headD ""
  let hToks := toks headPart
  let (retTok, symTok) ← match hToks.reverse with
    | sym :: ret :: _ => some (ret, sym)
    | _ => none
  if !symTok.startsWith "@" then none
  else
    let retTy ← parseSimpleTy retTok
    let args ← if argBody.trimAscii.toString == "" then some []
      else (argBody.splitOn ",").mapM fun seg =>
        match toks seg.trimAscii.toString with
        | [tTok, vTok] => parseTypedOp tTok vTok
        | _ => none
    some (.call dst? retTy (dropStr symTok 1) args .ccc)

def parseBinOps (dst opName : String) (flags : OverflowFlags) (w : IntWidth)
    (a b : Operand) : Option LLVMInstr :=
  match opName with
  | "add" => some (.add dst flags w a b)
  | "sub" => some (.sub dst flags w a b)
  | "mul" => some (.mul dst flags w a b)
  | "udiv" => some (.udiv dst false w a b)
  | "urem" => some (.urem dst w a b)
  | "and" => some (.and_ dst w a b)
  | "or" => some (.or_ dst w a b)
  | "xor" => some (.xor dst w a b)
  | "shl" => some (.shl dst flags w a b)
  | "lshr" => some (.lshr dst false w a b)
  | "ashr" => some (.ashr dst false w a b)
  | _ => none

def parseInstrLine (line : String) : Option LLVMInstr := do
  let ws := toks line
  match ws with
  | "store" :: tyTok :: valTok :: "ptr" :: ptrTok :: tail =>
    let (ty, valOp) ← parseTypedOp tyTok valTok
    let ptrOp ← parseOp none ptrTok
    some (.store false ty valOp ptrOp (parseAlignTail tail))
  | "call" :: afterCall =>
    parseCallLine none afterCall
  | dstTok :: "=" :: rhs =>
    if !dstTok.startsWith "%" then none
    else
      let dst := dropStr dstTok 1
      match rhs with
      | "alloca" :: tyTok :: tail =>
        let ty ← parseSimpleTy tyTok
        some (.alloca dst ty (parseAlignTail tail))
      | "load" :: tyTok :: "ptr" :: ptrTok :: tail =>
        let ty ← parseSimpleTy tyTok
        let ptrOp ← parseOp none ptrTok
        some (.load dst false ty ptrOp (parseAlignTail tail))
      | "icmp" :: predTok :: tyTok :: aTok :: bTok :: _ =>
        let pred ← parseICmpPred predTok
        let ty ← parseSimpleTy tyTok
        let w? := match ty with | .int w => some w | _ => none
        let a ← parseOp w? aTok
        let b ← parseOp w? bTok
        some (.icmp dst pred ty a b)
      | "select" :: "i1" :: cTok :: tTyTok :: tValTok :: eTyTok :: eValTok :: _ =>
        let cOp ← parseOp (some .i1) cTok
        let (tTy, tOp) ← parseTypedOp tTyTok tValTok
        let (_, eOp) ← parseTypedOp eTyTok eValTok
        some (.select dst cOp tTy tOp eOp)
      | "zext" :: sTok :: vTok :: "to" :: dTok :: _ =>
        let sw ← parseIntW sTok
        let dw ← parseIntW dTok
        let op ← parseOp (some sw) vTok
        some (.zext dst sw op dw)
      | "trunc" :: sTok :: vTok :: "to" :: dTok :: _ =>
        let sw ← parseIntW sTok
        let dw ← parseIntW dTok
        let op ← parseOp (some sw) vTok
        some (.trunc dst sw op dw)
      | "inttoptr" :: sTok :: vTok :: "to" :: "ptr" :: _ =>
        let sw ← parseIntW sTok
        let op ← parseOp (some sw) vTok
        some (.inttoptr dst sw op 0)
      | "ptrtoint" :: "ptr" :: vTok :: "to" :: dTok :: _ =>
        let dw ← parseIntW dTok
        let op ← parseOp none vTok
        some (.ptrtoint dst 0 op dw)
      | "getelementptr" :: restGep =>
        let (inb, gTail) := match restGep with
          | "inbounds" :: t => (true, t)
          | t => (false, t)
        match gTail with
        | tyTok :: "ptr" :: baseTok :: idxTyTok :: idxValTok :: _ =>
          let ty ← parseSimpleTy tyTok
          let baseOp ← parseOp none baseTok
          let iw ← parseIntW idxTyTok
          let idxOp ← parseOp (some iw) idxValTok
          some (.getelementptr dst inb ty baseOp [(iw, idxOp)])
        | _ => none
      | "call" :: afterCall =>
        parseCallLine (some dst) afterCall
      | opName :: afterOp =>
        let (flags, remToks) := parseFlags afterOp
        match remToks with
        | wTok :: aTok :: bTok :: _ =>
          let w ← parseIntW wTok
          let a ← parseOp (some w) aTok
          let b ← parseOp (some w) bTok
          parseBinOps dst opName flags w a b
        | _ => none
      | [] => none
  | _ => none

def stripTrailingMd (ws : List String) : List String :=
  match ws.findIdx? (fun t => t.startsWith "!") with
  | some idx =>
    let pre := ws.take idx
    match pre.reverse with
    | last :: revInit => (stripComma last :: revInit).reverse
    | [] => []
  | none => ws

def parseTermLine (line : String) : Option Terminator := do
  let ws := stripTrailingMd (toks line)
  match ws with
  | ["ret", "void"] => some (.ret none)
  | ["ret", tyTok, valTok] =>
    let tv ← parseTypedOp tyTok valTok
    some (.ret (some tv))
  | ["br", "label", lblTok] =>
    let l := stripComma lblTok
    if l.startsWith "%" then some (.br (dropStr l 1)) else none
  | ["br", "i1", cTok, "label", tTok, "label", eTok] =>
    let c ← parseOp (some .i1) cTok
    let tl := stripComma tTok
    let el := stripComma eTok
    if tl.startsWith "%" && el.startsWith "%" then
      some (.condBr c (dropStr tl 1) (dropStr el 1))
    else none
  | ["unreachable"] => some .unreachable
  | _ => none

def parseParamSeg (seg : String) : Option LLVMParam := do
  let ws := toks seg.trimAscii.toString
  match ws, ws.reverse with
  | tyTok :: _, nameTok :: _ =>
    if !nameTok.startsWith "%" then none
    else
      let ty ← parseSimpleTy tyTok
      some { name := dropStr nameTok 1, ty := ty }
  | _, _ => none

def parseHeader (line : String) : Option (GlobalSym × LLVMType × List LLVMParam) := do
  let (beforeParen, restParen) := match line.splitOn "(" with
    | h :: t => (h.trimAscii.toString, String.intercalate "(" t)
    | [] => ("", "")
  let paramPart := (restParen.splitOn ")").headD ""
  let hToks := toks beforeParen
  let (retTok, symTok) ← match hToks.reverse with
    | sym :: ret :: _ => some (ret, sym)
    | _ => none
  if !symTok.startsWith "@" then none
  else
    let retTy ← parseSimpleTy retTok
    let params ← if paramPart.trimAscii.toString == "" then some []
      else (paramPart.splitOn ",").mapM parseParamSeg
    some (dropStr symTok 1, retTy, params)

structure BlockBuilder where
  label : BlockLabel
  phis  : List PhiNode := []
  body  : List LLVMInstr := []

def parseBlocksAux : List String → Option BlockBuilder → List LLVMBlock → Option (List LLVMBlock)
  | [], none, acc => some acc.reverse
  | [], some _, _ => none
  | line :: rest, cur?, acc =>
    if line.endsWith ":" then
      match cur? with
      | some _ => none
      | none => parseBlocksAux rest (some { label := dropEndStr line 1 }) acc
    else
      match cur? with
      | none => none
      | some b =>
        match parseTermLine line with
        | some term =>
          let blk : LLVMBlock := { label := b.label, phis := b.phis.reverse, body := b.body.reverse, term := term }
          parseBlocksAux rest none (blk :: acc)
        | none =>
          if b.body.isEmpty then
            match parsePhiLine line with
            | some phi => parseBlocksAux rest (some { b with phis := phi :: b.phis }) acc
            | none =>
              match parseInstrLine line with
              | some ins => parseBlocksAux rest (some { b with body := ins :: b.body }) acc
              | none => none
          else
            match parseInstrLine line with
            | some ins => parseBlocksAux rest (some { b with body := ins :: b.body }) acc
            | none => none

def parseEmittedFn (irText : String) : Option LLVMFn := do
  let rawLines := (irText.splitOn "\n").map stripComment |>.filter (· != "")
  let defIdx ← rawLines.findIdx? (fun l => l.startsWith "define ")
  let fromDef := rawLines.drop defIdx
  match fromDef with
  | hdrLine :: tail =>
    let endIdx ← tail.findIdx? (· == "}")
    let bodyLines := tail.take endIdx
    let (name, retTy, params) ← parseHeader hdrLine
    let blocks ← parseBlocksAux bodyLines none []
    some { name := name, retTy := retTy, params := params, blocks := blocks }
  | [] => none

/-! ## Runtime SArray Allocator & Call Handler for `parFor` Execution -/

/-- Allocate a Lean-shaped `sarray` object `[rc=1 : i32, pad=0 : i32, sz : i64, cap : i64, elems...]`
    of exact byte size `24 + 8 * elems.length` so out-of-bounds loop writes (`M4`) hit `.ub`. -/
def allocSArray (m : ByteMem) (elems : List UInt64) : Option (BitVec 64 × ByteMem) := do
  let len := elems.length
  let byteLen := 24 + 8 * len
  let (ptr, m0) ← m.allocAligned byteLen 8 true
  let base := ptr.toNat
  let m1 := m0.storeInt (BitVec.ofNat 64 base) .i32 1#32
  let m2 := m1.storeInt (BitVec.ofNat 64 (base + 8)) .i64 (BitVec.ofNat 64 len)
  let m3 := m2.storeInt (BitVec.ofNat 64 (base + 16)) .i64 (BitVec.ofNat 64 len)
  let mFinal := (List.range len).foldl (fun acc i =>
    let w := (elems[i]?.getD 0).toBitVec
    acc.storeInt (BitVec.ofNat 64 (base + 24 + 8 * i)) .i64 w) m3
  some (ptr, mFinal)

def readSArrayWords (m : ByteMem) (ptr : BitVec 64) (len : Nat) : Option (List UInt64) :=
  let base := ptr.toNat
  (List.range len).mapM fun i =>
    let addr := BitVec.ofNat 64 (base + 24 + 8 * i)
    if m.accessOk addr 8 8 false then
      (m.loadInt? addr .i64).map fun bv => bv.toNat.toUInt64
    else none

def runEmitCall (st : ExecState) (dst? : Option RegName) (_cc : CallingConv)
    (_retTy : LLVMType) (callee : GlobalSym) (argVals : List LLVMVal) : ExecOutcome ⊕ ExecState :=
  if callee == "lean_native_ensure_exclusive" || callee == "lean_native_ensure_exclusive_uninit" then
    match argVals with
    | [.ptr inPtr] =>
      let lenOpt := st.mem.loadInt? (BitVec.ofNat 64 (inPtr.toNat + 8)) .i64
      match lenOpt with
      | none => .inl (.ub "ensure_exclusive invalid sarray header")
      | some lenBv =>
        let zeros := List.replicate lenBv.toNat (0 : UInt64)
        match allocSArray st.mem zeros with
        | none => .inl (.ub "ensure_exclusive alloc failed")
        | some (outPtr, mem') =>
          let st' := { st with mem := mem' }
          match dst? with
          | some dst => .inr (bindReg st' dst (.ptr outPtr))
          | none => .inr st'
    | _ => .inl (.ub "ensure_exclusive bad args")
  else if callee == "malloc" then
    match argVals with
    | [.bits .i64 byteLen] =>
      match st.mem.allocAligned byteLen.toNat 8 true with
      | none => .inl (.ub "malloc failed")
      | some (outPtr, mem') =>
        let st' := { st with mem := mem' }
        match dst? with
        | some dst => .inr (bindReg st' dst (.ptr outPtr))
        | none => .inr st'
    | _ => .inl (.ub "malloc bad args")
  else
    runCallWith {} 0 st dst? .ccc .void callee argVals

def execParsedScalar2 (fn : LLVMFn) (a b : UInt64) (fuel : Nat := 64) : Option UInt64 :=
  match fn.blocks with
  | [] => none
  | entry :: _ =>
    match bindArgs {} fn.params [.bits .i64 a.toBitVec, .bits .i64 b.toBitVec] with
    | none => none
    | some st0 =>
      match execBlockWith runEmitCall fn fuel st0 entry with
      | .returned (some (.bits .i64 v)) _ => some v.toNat.toUInt64
      | _ => none

def evalLNIRScalar2 (d : LNIRDecl) (a b : UInt64) : Option UInt64 :=
  let env := (VarEnv.empty.bind 0 (.u64 a)).bind 1 (.u64 b)
  match evalCode 64 env HeapState.empty d.body with
  | .ok (.u64 v, _) => some v
  | .ok (.bool flag, _) => some (if flag then 1 else 0)
  | _ => none

def mkScalarProbe (name : String) (op : BinOp) : LNIRDecl :=
  { name := name
    params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    retTy := .i64
    body := .letBind 2 .i64 (.scalar (.binOp op (.var 0) (.var 1))) (.ret 2) }

def checkScalarDecl (opt : Bool) (d : LNIRDecl) (cases : List (UInt64 × UInt64)) : Bool :=
  match parseEmittedFn (emitDeclLLVM opt d .x86_64) with
  | none => false
  | some fn =>
    cases.all fun (a, b) =>
      let exp := evalLNIRScalar2 d a b
      exp.isSome && execParsedScalar2 fn a b == exp

def parForProbeDecl : LNIRDecl :=
  { name := "llvm_emit_parfor_msa"
    params := [{ id := 0, name := "n", ty := .i64 }, { id := 1, name := "xs", ty := .sarray .i64 }]
    retTy := .sarray .i64
    body := .parFor 2 0 [1] .i64 (.mapScaleAdd 3 5) (.ret 2) }

def checkParForDecl (opt : Bool) (elems : List UInt64) : Bool :=
  let d := parForProbeDecl
  match parseEmittedFn (emitDeclLLVM opt d .x86_64) with
  | none => false
  | some fn =>
    match fn.blocks, allocSArray {} elems with
    | entry :: _, some (inPtr, mem0) =>
      let len := elems.length
      let args : List LLVMVal := [.bits .i64 (BitVec.ofNat 64 len), .ptr inPtr]
      match bindArgs { mem := mem0 } fn.params args with
      | none => false
      | some st0 =>
        match execBlockWith runEmitCall fn 128 st0 entry with
        | .returned (some (.ptr outPtr)) memOut =>
          let env := (VarEnv.empty.bind 0 (.u64 len.toUInt64)).bind 1 (.sarrayId 1)
          let heap : HeapState :=
            { buffers := [{ id := 1, exclusive := true, data := elems.toArray }], nextId := 2 }
          let lnirExp : Option (List UInt64) :=
            match evalCode 128 env heap d.body with
            | .ok (.sarrayId bid, hOut) =>
              (hOut.buffers.find? (·.id == bid)).map (·.data.toList)
            | _ => none
          lnirExp.isSome && readSArrayWords memOut outPtr len == lnirExp
        | _ => false
    | _, _ => false

def dotProdProbeDecl : LNIRDecl :=
  { name := "llvm_emit_parfor_dot"
    params :=
      [ { id := 0, name := "n", ty := .i64 }
      , { id := 1, name := "xs", ty := .sarray .i64 }
      , { id := 2, name := "ys", ty := .sarray .i64 } ]
    retTy := .sarray .i64
    body := .parFor 3 0 [1, 2] .i64 .dotProduct (.ret 3) }

def checkDotProdDecl (opt : Bool) (xs ys : List UInt64) : Bool :=
  let d := dotProdProbeDecl
  match parseEmittedFn (emitDeclLLVM opt d .x86_64) with
  | none => false
  | some fn =>
    match fn.blocks, allocSArray {} xs with
    | entry :: _, some (xPtr, mem1) =>
      match allocSArray mem1 ys with
      | some (yPtr, mem2) =>
        let len := xs.length
        let args : List LLVMVal := [.bits .i64 (BitVec.ofNat 64 len), .ptr xPtr, .ptr yPtr]
        match bindArgs { mem := mem2 } fn.params args with
        | none => false
        | some st0 =>
          match execBlockWith runEmitCall fn 128 st0 entry with
          | .returned (some (.ptr outPtr)) memOut =>
            let env := ((VarEnv.empty.bind 0 (.u64 len.toUInt64)).bind 1 (.sarrayId 1)).bind 2 (.sarrayId 2)
            let heap : HeapState :=
              { buffers :=
                  [ { id := 1, exclusive := true, data := xs.toArray }
                  , { id := 2, exclusive := true, data := ys.toArray } ]
                nextId := 3 }
            let lnirExp : Option (List UInt64) :=
              match evalCode 128 env heap d.body with
              | .ok (.sarrayId bid, hOut) =>
                (hOut.buffers.find? (·.id == bid)).map (·.data.toList)
              | _ => none
            lnirExp.isSome && readSArrayWords memOut outPtr 1 == lnirExp
          | _ => false
      | none => false
    | _, _ => false

/-- End-to-end LLVM text emitter verification across baseline and optimized modes (`M1..M5` + `.dotProduct`). -/
def verifyLLVMEmitter : Bool :=
  let subDecl := mkScalarProbe "llvm_emit_sub" .sub
  let shlDecl := mkScalarProbe "llvm_emit_shl" .shl
  let shrDecl := mkScalarProbe "llvm_emit_shr" .shr
  let ltDecl  := mkScalarProbe "llvm_emit_lt"  .lt
  let divDecl := mkScalarProbe "llvm_emit_div" .div
  let modDecl := mkScalarProbe "llvm_emit_mod" .mod
  [false, true].all fun opt =>
    checkScalarDecl opt subDecl [(10, 3), (3, 10), (0, 1)] &&
    checkScalarDecl opt shlDecl [(3, 2), (1, 32), (5, 65)] &&
    checkScalarDecl opt shrDecl [(16, 2), (4294967296, 32), (8, 64)] &&
    checkScalarDecl opt ltDecl  [(3, 3), (0, 0), (2, 5), (5, 2)] &&
    checkScalarDecl opt divDecl [(18, 3), (7, 0), (0, 0)] &&
    checkScalarDecl opt modDecl [(19, 4), (7, 0), (0, 0)] &&
    checkParForDecl opt [11, 22, 33] &&
    checkParForDecl opt [] &&
    checkDotProdDecl opt [2, 3, 5] [7, 11, 13] &&
    checkDotProdDecl opt [] []

#guard verifyLLVMEmitter = true

end LeanNative.Backend.LLVMEmitVerify
