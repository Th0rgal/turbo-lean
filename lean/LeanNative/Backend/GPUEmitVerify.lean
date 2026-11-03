import LeanNative.IR.AST
import LeanNative.Semantics.Eval
import LeanNative.Backend.GPUIR
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Metal
import LeanNative.Backend.PTXAst
import LeanNative.Backend.MetalAst
import LeanNative.Backend.PTXLower
import LeanNative.Backend.MetalLower
import LeanNative.Backend.StableHLOAst

namespace LeanNative.Backend.GPUEmitVerify

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.GPUIR
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanNative.Backend.PTXAst
open LeanNative.Backend.MetalAst
open LeanNative.Backend.StableHLOAst

def natOf : String → Option Nat
  | "" => none
  | s => s.toNat?

def dropStr (s : String) (n : Nat) : String :=
  (s.drop n).toString

def dropRightStr (s : String) (n : Nat) : String :=
  (s.dropEnd n).toString

def linesOf (s : String) : List String :=
  (s.splitOn "\n").map (·.trimAscii.toString)

def stripSemi (s : String) : String :=
  if s.endsWith ";" then dropRightStr s 1 else s

def stripComma (s : String) : String :=
  if s.endsWith "," then dropRightStr s 1 else s

def toks (s : String) : List String :=
  ((stripSemi s).splitOn " ").filter (· != "")

def immNat (tok : String) : Option Nat :=
  if tok.endsWith "UL" || tok.endsWith "ul" then natOf (dropRightStr tok 2)
  else natOf tok

def ptxTy : String → Option PTXType
  | ".u64" => some .u64 | ".b64" => some .b64 | ".s64" => some .s64
  | ".u32" => some .u32 | ".b32" => some .b32 | ".s32" => some .s32
  | ".pred" => some .pred | _ => none

def ptxOp (tok0 : String) : Option PTXOperand :=
  let tok := stripComma tok0
  match immNat tok with
  | some n => some (.immU64 (BitVec.ofNat 64 n))
  | none =>
    if tok == "%ctaid.x" then some (.sreg .ctaidX)
    else if tok == "%ntid.x" then some (.sreg .ntidX)
    else if tok == "%tid.x" then some (.sreg .tidX)
    else if tok.startsWith "%" then some (.reg tok) else none

def ptxAddr (tok0 : String) : Option PTXAddr :=
  let tok := stripComma tok0
  if tok.startsWith "[" && tok.endsWith "]" then
    let inner := dropRightStr (dropStr tok 1) 1
    if inner.startsWith "%" then
      match inner.splitOn "+" with
      | [r] => some (.regOffset r 0)
      | [r, off] =>
        if off.startsWith "-" then
          (immNat (dropStr off 1)).map fun n => .regOffset r (-(Int.ofNat n))
        else (immNat off).map fun n => .regOffset r (Int.ofNat n)
      | _ => none
    else some (.paramSym inner)
  else none

def guardOf (tok : String) : Option (Option PTXPredGuard) :=
  if tok.startsWith "@!" then some (some { predReg := dropStr tok 2, negated := true })
  else if tok.startsWith "@" then some (some { predReg := dropStr tok 1, negated := false })
  else some none

def ptxCmp : String → Option PTXCmpOp
  | "eq" => some .eq | "ne" => some .ne | "lt" => some .lt | "le" => some .le
  | "gt" => some .gt | "ge" => some .ge | _ => none

def parsePTXLine (line : String) : Option PTXStmt :=
  let ws := toks line
  match ws with
  | [] => none
  | w :: rest =>
    if w.endsWith ":" then some (.label (dropRightStr w 1))
    else match guardOf w with
    | none => none
    | some g? =>
      let body := match g? with | some _ => rest | none => ws
      match body with
      | op :: args =>
        let instr? : Option PTXInstr :=
          if op.startsWith "mov." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, src] => (ptxOp src).map fun s => .mov ty (stripComma dst) s
            | _, _ => none
          else if op.startsWith "ld.param." then
            match ptxTy (dropStr op 8), args with
            | some ty, [dst, addr] => (ptxAddr addr).bind fun a =>
              match a with | .paramSym n => some (.ldParam ty (stripComma dst) n) | _ => none
            | _, _ => none
          else if op.startsWith "ld.global." then
            match ptxTy (dropStr op 9), args with
            | some ty, [dst, addr] => (ptxAddr addr).map fun a => .ldGlobal ty (stripComma dst) a
            | _, _ => none
          else if op.startsWith "st.global." then
            match ptxTy (dropStr op 9), args with
            | some ty, [addr, src] =>
              (ptxAddr addr).bind fun a => (ptxOp src).map fun s => .stGlobal ty a s
            | _, _ => none
          else if op.startsWith "cvta.to.global." then
            match ptxTy (dropStr op 14), args with
            | some ty, [dst, src] => (ptxOp src).map fun s => .cvtaToGlobal ty (stripComma dst) s
            | _, _ => none
          else if op.startsWith "cvt." then
            match op.splitOn ".", args with
            | ["cvt", dt, st], [dst, src] =>
              (ptxTy ("." ++ dt)).bind fun d => (ptxTy ("." ++ st)).bind fun s =>
                (ptxOp src).map fun o => .cvt .none d s (stripComma dst) o
            | _, _ => none
          else if op.startsWith "add." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .add .none ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "sub." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .sub ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "mul.lo." then
            match ptxTy (dropStr op 6), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .mul .lo ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "mul.wide." then
            match ptxTy (dropStr op 8), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .mul .wide ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "mad.lo." then
            match ptxTy (dropStr op 6), args with
            | some ty, [dst, a, b, c] =>
              (ptxOp a).bind fun x => (ptxOp b).bind fun y => (ptxOp c).map fun z =>
                .mad .lo ty (stripComma dst) x y z
            | _, _ => none
          else if op.startsWith "div." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .div ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "and." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .bitAnd ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "or." then
            match ptxTy (dropStr op 2), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .bitOr ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "xor." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .bitXor ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "shl." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .shl ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "shr." then
            match ptxTy (dropStr op 3), args with
            | some ty, [dst, a, b] =>
              (ptxOp a).bind fun x => (ptxOp b).map fun y => .shr ty (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "setp." then
            match op.splitOn ".", args with
            | ["setp", cmp, ty], [dst, a, b] =>
              (ptxCmp cmp).bind fun c => (ptxTy ("." ++ ty)).bind fun t =>
                (ptxOp a).bind fun x => (ptxOp b).map fun y => .setp c t (stripComma dst) x y
            | _, _ => none
          else if op.startsWith "selp." then
            match ptxTy (dropStr op 4), args with
            | some ty, [dst, t, f, p] =>
              (ptxOp t).bind fun x => (ptxOp f).map fun y => .selp ty (stripComma dst) x y (stripComma p)
            | _, _ => none
          else if op == "bra" then match args with | [lbl] => some (.bra (stripComma lbl)) | _ => none
          else if op == "ret" then some .ret
          else none
        instr?.map fun i => .instr g? i
      | [] => none

def parseRegCount (l : String) : Nat :=
  let tail := (l.splitOn "<").getLast?.getD "0"
  (natOf ((tail.splitOn ">").head?.getD "0")).getD 0

def parsePTXKernel (text : String) : Option PTXKernel :=
  let ls := (linesOf text).filter (· != "")
  match ls with
  | head :: rest =>
    if !(head.startsWith ".visible .entry ") then none
    else
      let name := ((dropStr head 16).splitOn "(").head?.getD ""
      let rec takeParams : List String → List PTXParamDecl × List String
        | [] => ([], [])
        | l :: ls =>
          if l == ")" then
            match ls with
            | "{" :: ls2 => ([], ls2)
            | _ => ([], ls)
          else if l == ") {" || l == "{" then ([], ls)
          else
            let (ps, tail) := takeParams ls
            let cleaned := stripComma l
            match toks cleaned with
            | [".param", ty, nm] =>
              match ptxTy ty with
              | some t => ({ ty := t, name := nm } :: ps, tail)
              | none => (ps, tail)
            | _ => (ps, tail)
      let (params, after) := takeParams rest
      let rec takeBody : List String → List PTXStmt × Nat × Nat × Nat
        | [] => ([], 0, 0, 0)
        | l :: ls =>
          if l == "}" then ([], 0, 0, 0)
          else if l.startsWith ".reg .pred" then
            let (b, p, r, rd) := takeBody ls
            (b, Nat.max p (parseRegCount l), r, rd)
          else if l.startsWith ".reg .b32" then
            let (b, p, r, rd) := takeBody ls
            (b, p, Nat.max r (parseRegCount l), rd)
          else if l.startsWith ".reg .b64" then
            let (b, p, r, rd) := takeBody ls
            (b, p, r, Nat.max rd (parseRegCount l))
          else
            let (b, p, r, rd) := takeBody ls
            match parsePTXLine l with
            | some st => (st :: b, p, r, rd)
            | none => (b, p, r, rd)
      let (body, np, nr, nrd) := takeBody after
      if body.isEmpty then none
      else some {
        name := name
        params := params
        body := body
        regDecls := [ { ty := .pred, prefixName := "%p", count := np }
                    , { ty := .b32, prefixName := "%r", count := nr }
                    , { ty := .b64, prefixName := "%rd", count := nrd } ] }
  | [] => none

def splitEntries (text : String) : List String :=
  let rec go : List String → List String → List String
    | [], acc => if acc.isEmpty then [] else [String.intercalate "\n" acc.reverse]
    | l :: ls, acc =>
      if l.startsWith ".visible .entry " && !acc.isEmpty then
        String.intercalate "\n" acc.reverse :: go ls [l]
      else go ls (l :: acc)
  go (text.splitOn "\n") []

def findPTXKernel (moduleText name : String) : Option PTXKernel :=
  (splitEntries moduleText).findSome? fun chunk =>
    (parsePTXKernel chunk).filter fun k => k.name == name

def mslTy : String → Option MSLType
  | "ulong" => some .ulong | "uint" => some .uint | "long" => some .long
  | "int" => some .int | "bool" => some .bool | _ => none

def splitTopChar (s : String) (sep : Char) : List String :=
  let rec go (depth : Nat) (cur : List Char) : List Char → List String
    | [] => [String.ofList cur.reverse]
    | c :: cs =>
      if c == sep && depth == 0 then String.ofList cur.reverse :: go 0 [] cs
      else
        let d := if c == '(' || c == '{' || c == '[' then depth + 1
                 else if (c == ')' || c == '}' || c == ']') && depth > 0 then depth - 1 else depth
        go d (c :: cur) cs
  go 0 [] s.toList

def splitTopOp (s : String) (op : String) : Option (String × String) :=
  let opChars := op.toList
  let rec matchPre : List Char → List Char → Option (List Char)
    | [], xs => some xs
    | p :: ps, x :: xs => if p == x then matchPre ps xs else none
    | _, [] => none
  let rec go (depth : Nat) (cur : List Char) : List Char → Option (String × String)
    | [] => none
    | c :: cs =>
      if depth == 0 then
        match matchPre opChars (c :: cs) with
        | some rest => some (String.ofList cur.reverse, String.ofList rest)
        | none =>
          let d := if c == '(' || c == '{' || c == '[' then 1 else 0
          go d (c :: cur) cs
      else
        let d := if c == '(' || c == '{' || c == '[' then depth + 1
                 else if (c == ')' || c == '}' || c == ']') && depth > 0 then depth - 1 else depth
        go d (c :: cur) cs
  go 0 [] s.toList

def isWrappedParens (s : String) : Bool :=
  let cs := s.toList
  match cs with
  | '(' :: rest =>
    let rec chk (depth : Nat) : List Char → Bool
      | [] => false
      | [')'] => depth == 0
      | c :: tail =>
        let d := if c == '(' then depth + 1
                 else if c == ')' then depth - 1 else depth
        if d < 0 then false else chk d tail
    let rec chkNat (depth : Nat) : List Char → Bool
      | [] => false
      | [')'] => depth == 0
      | '(' :: tail => chkNat (depth + 1) tail
      | ')' :: tail => if depth == 0 then false else chkNat (depth - 1) tail
      | _ :: tail => chkNat depth tail
    chkNat 0 rest
  | _ => false

def parseMSLExpr (s0 : String) : Option MSLExpr :=
  let rec go (fuel : Nat) (t0 : String) : Option MSLExpr :=
    match fuel with
    | 0 => none
    | n + 1 =>
      let t := t0.trimAscii.toString
      if isWrappedParens t then
        let inner := dropRightStr (dropStr t 1) 1
        match splitTopChar inner '?' with
        | [c, rest] =>
          match splitTopChar rest ':' with
          | [a, b] =>
            (go n c).bind fun ce => (go n a).bind fun ae => (go n b).map fun be => .select ce ae be
          | _ => go n inner
        | _ =>
          let bins : List (String × (MSLExpr → MSLExpr → MSLExpr)) :=
            [ ("==", .eq), ("!=", .ne), ("<=", .le), (">=", .ge)
            , ("|", .bitOr), ("^", .bitXor), ("&", .bitAnd)
            , ("<<", .shl), (">>", .shr), ("<", .lt), (">", .gt)
            , ("+", .add), ("-", .sub), ("*", .mul), ("/", .div), ("%", .rem) ]
          match bins.findSome? fun (op, mk) =>
            match splitTopOp inner op with
            | some (a, b) => (go n a).bind fun ae => (go n b).map fun be => mk ae be
            | none => none with
          | some e => some e
          | none => go n inner
      else
        let bins : List (String × (MSLExpr → MSLExpr → MSLExpr)) :=
          [ ("==", .eq), ("!=", .ne), ("<=", .le), (">=", .ge)
          , ("|", .bitOr), ("^", .bitXor), ("&", .bitAnd)
          , ("<<", .shl), (">>", .shr), ("<", .lt), (">", .gt)
          , ("+", .add), ("-", .sub), ("*", .mul), ("/", .div), ("%", .rem) ]
        match bins.findSome? fun (op, mk) =>
          match splitTopOp t op with
          | some (a, b) => (go n a).bind fun ae => (go n b).map fun be => mk ae be
          | none => none with
        | some e => some e
        | none =>
          if t.startsWith "(" && t.contains ')' then
            match t.splitOn ")" with
            | head :: tail =>
              let tyName := (dropStr head 1).trimAscii.toString
              match mslTy tyName with
              | some ty => (go n (String.intercalate ")" tail)).map fun e => .cast ty e
              | none => none
            | [] => none
          else match immNat t with
          | some k => some (.immU64 (BitVec.ofNat 64 k))
          | none =>
            if t.endsWith ")" && t.contains '(' then
              match t.splitOn "(" with
              | fn :: rest =>
                let argBody := dropRightStr (String.intercalate "(" rest) 1
                let rawArgs := if argBody.trimAscii.toString == "" then [] else splitTopChar argBody ','
                let es := rawArgs.filterMap fun a => go n a
                if es.length == rawArgs.length then
                  some (.call fn.trimAscii.toString (MSLExprList.ofList es))
                else none
              | [] => none
            else if t.endsWith "]" && t.contains '[' then
              match t.splitOn "[" with
              | [arr, idx] => (go n (dropRightStr idx 1)).map fun i => .index arr.trimAscii.toString i
              | _ => none
            else if !t.isEmpty && t.all (fun c => c.isAlphanum || c == '_') then some (.var t)
            else none
  go 48 s0

def parseMSLSimpleLine (line : String) : Option MSLStmt :=
  let l := stripSemi line.trimAscii.toString
  if l.startsWith "return " then (parseMSLExpr (dropStr l 7)).map .returnVal
  else if l.startsWith "ulong " || l.startsWith "uint " || l.startsWith "long " then
    match l.splitOn "=" with
    | lhs :: rhsParts =>
      match (lhs.trimAscii.toString.splitOn " ").filter (· != "") with
      | [ty, nm] =>
        (mslTy ty).bind fun t =>
          (parseMSLExpr (String.intercalate "=" rhsParts)).map fun e => .varDecl t nm e
      | _ => none
    | [] => none
  else if l.contains '=' && l.contains '[' then
    match splitTopOp l "=" with
    | some (lhs, rhs) =>
      let lt := lhs.trimAscii.toString
      if lt.endsWith "]" then
        match lt.splitOn "[" with
        | [arr, idx] =>
          (parseMSLExpr (dropRightStr idx 1)).bind fun i =>
            (parseMSLExpr rhs).map fun e => .indexAssign arr.trimAscii.toString i e
        | _ => none
      else none
    | none => none
  else none

def takeUntilCloseBrace : List String → List String × List String
  | [] => ([], [])
  | l :: ls =>
    if l == "}" then ([], ls)
    else
      let (b, rest) := takeUntilCloseBrace ls
      (l :: b, rest)

def parseMSLBodyLines : Nat → List String → List MSLStmt
  | 0, _ => []
  | _, [] => []
  | f + 1, l :: ls =>
    if l == "}" || l == "{" || l == "" then parseMSLBodyLines f ls
    else if l.startsWith "if (" && l.endsWith ") {" then
      let condStr := dropRightStr (dropStr l 4) 3
      let (inner, after) := takeUntilCloseBrace ls
      let rest := parseMSLBodyLines f after
      match parseMSLExpr condStr with
      | some c => .ifElse c (MSLBlock.ofList (parseMSLBodyLines f inner)) .nil :: rest
      | none => rest
    else
      match parseMSLSimpleLine l with
      | some st => st :: parseMSLBodyLines f ls
      | none => parseMSLBodyLines f ls

def parseMSLKernel (text : String) : Option MSLKernelDecl :=
  let ls := linesOf text
  match ls with
  | head :: rest =>
    if !(head.startsWith "kernel void ") then none
    else
      let name := (((dropStr head 12).splitOn "(").head?.getD "").trimAscii.toString
      let rec params : List String → List MSLParamDecl × List String
        | [] => ([], [])
        | l :: ls =>
          if l.startsWith ") {" || l == "{" then ([], ls)
          else
            let (ps, tail) := params ls
            let cleaned := (stripComma l).trimAscii.toString
            let p? :=
              if cleaned.contains "[[buffer(" then
                let tailIdx := ((cleaned.splitOn "[[buffer(").getLast?.getD "")
                let idx := (natOf (String.ofList (tailIdx.toList.takeWhile Char.isDigit))).getD 0
                if cleaned.startsWith "device const ulong*" then
                  some { ty := .pointer .device true .ulong
                       , name := (((dropStr cleaned 19).trimAscii.toString.splitOn " ").head?.getD "")
                       , attr := some (.buffer idx) }
                else if cleaned.startsWith "device ulong*" then
                  some { ty := .pointer .device false .ulong
                       , name := (((dropStr cleaned 13).trimAscii.toString.splitOn " ").head?.getD "")
                       , attr := some (.buffer idx) }
                else if cleaned.startsWith "constant ulong&" then
                  some { ty := .ref .constant .ulong
                       , name := (((dropStr cleaned 15).trimAscii.toString.splitOn " ").head?.getD "")
                       , attr := some (.buffer idx) }
                else none
              else if cleaned.startsWith "uint " && cleaned.contains "thread_position_in_grid" then
                some { ty := .uint
                     , name := (((dropStr cleaned 5).trimAscii.toString.splitOn " ").head?.getD "")
                     , attr := some .threadPositionInGrid }
              else none
            match p? with | some p => (p :: ps, tail) | none => (ps, tail)
      let (ps, after) := params rest
      let (bodyRaw, _) := takeUntilCloseBrace after
      let body := parseMSLBodyLines 32 bodyRaw
      if body.isEmpty then none else some { name := name, params := ps, body := body }
  | [] => none

def findMSLKernel (moduleText name : String) : Option MSLKernelDecl :=
  let chunks := moduleText.splitOn "kernel void "
  (chunks.drop 1).findSome? fun c =>
    (parseMSLKernel ("kernel void " ++ c)).filter fun k => k.name == name

def parseMSLFunc (text : String) : Option MSLFuncDecl :=
  let ls := linesOf text
  match ls with
  | head :: rest =>
    if !(head.startsWith "inline ulong ") then none
    else
      let name := (((dropStr head 13).splitOn "(").head?.getD "").trimAscii.toString
      let afterParen := String.intercalate "(" (((dropStr head 13).splitOn "(").drop 1)
      let sig := ((afterParen.splitOn ")").head?.getD "").trimAscii.toString
      let ps := (if sig == "" then [] else sig.splitOn ",").filterMap fun raw =>
        match (raw.trimAscii.toString.splitOn " ").filter (· != "") with
        | [ty, nm] => (mslTy ty).map fun t => { ty := t, name := nm : MSLParamDecl }
        | _ => none
      let (bodyRaw, _) := takeUntilCloseBrace rest
      let body := parseMSLBodyLines 32 bodyRaw
      if body.isEmpty then none
      else some { retTy := .ulong, name := name, params := ps, body := MSLBlock.ofList body }
  | [] => none

def findMSLFuncs (moduleText : String) : List MSLFuncDecl :=
  let chunks := moduleText.splitOn "inline ulong "
  (chunks.drop 1).filterMap fun c => parseMSLFunc ("inline ulong " ++ c)

def scU64 (n : UInt64) : TensorVal :=
  { ty := { shape := [], elem := .ui64 }, data := #[n.toBitVec] }

def parseMLIRArithLine (line : String) : Option (StableHLOOp × String) :=
  let l := line.trimAscii.toString
  if !(l.startsWith "%") || !(l.contains '=') then none
  else
    match l.splitOn "=" with
    | [lhs, rhs0] =>
      let dst := dropStr lhs.trimAscii.toString 1
      let rhs := ((rhs0.splitOn ":").head?.getD "").trimAscii.toString
      match (rhs.splitOn " ").filter (· != "") with
      | ["arith.constant", v] =>
        (natOf v).map fun n => (.constant dst (scU64 n.toUInt64), dst)
      | [op, a0, b0] =>
        let a := dropStr (stripComma a0) 1
        let b := dropStr (stripComma b0) 1
        match op with
        | "arith.addi" => some (.add dst a b, dst)
        | "arith.subi" => some (.subtract dst a b, dst)
        | "arith.muli" => some (.multiply dst a b, dst)
        | "arith.shli" => some (.shiftLeft dst a b, dst)
        | "arith.shrui" => some (.shiftRightLogical dst a b, dst)
        | "arith.andi" => some (.and dst a b, dst)
        | "arith.ori" => some (.or dst a b, dst)
        | "arith.xori" => some (.xor dst a b, dst)
        | _ => none
      | _ => none
    | _ => none

def evalParsedMLIRKernel1D (mlirText funcName : String) (in0 in1 : List UInt64) : Option (List UInt64) :=
  let chunks := mlirText.splitOn s!"gpu.func @{funcName}("
  match chunks.drop 1 with
  | bodyChunk :: _ =>
    let afterPar := ((bodyChunk.splitOn "scf.parallel ").drop 1).head?.getD ""
    let body := ((afterPar.splitOn "scf.reduce").head?.getD "")
    let ls := linesOf body
    let storeDst? := ls.findSome? fun l =>
      if l.startsWith "memref.store " then
        match (dropStr l 13).splitOn "," with
        | v :: _ => some (dropStr v.trimAscii.toString 1)
        | [] => none
      else none
    let inLoads : List (String × Nat) := ls.filterMap fun l =>
      if l.contains "memref.load %in0[" then
        some (dropStr ((l.splitOn "=").head?.getD "").trimAscii.toString 1, 0)
      else if l.contains "memref.load %in1[" then
        some (dropStr ((l.splitOn "=").head?.getD "").trimAscii.toString 1, 1)
      else none
    let ops := (ls.filterMap parseMLIRArithLine).map (·.1)
    match storeDst? with
    | none => none
    | some retVar =>
      let len := in0.length
      let laneOut (i : Nat) : Option UInt64 :=
        let env0 := inLoads.foldl (fun e (nm, bufIdx) =>
          let w := if bufIdx == 0 then in0[i]?.getD 0 else in1[i]?.getD 0
          e.bind nm (scU64 w)) Env.empty
        match evalOps env0 ops with
        | .ok envF =>
          match envF retVar with
          | some tv => tv.data[0]?.map (fun bv => bv.toNat.toUInt64)
          | none => none
        | .error _ => none
      let outs := (List.range len).filterMap laneOut
      if outs.length == len then some outs else none
  | [] => none

def wordEnv (inputs : List (List UInt64)) : VarEnv :=
  (List.range inputs.length).foldl (fun e j => e.bind (100 + j) (.sarrayId (j + 1))) VarEnv.empty

def wordHeap (inputs : List (List UInt64)) : HeapState :=
  { buffers := (List.range inputs.length).map fun j =>
      { id := j + 1, exclusive := true, data := (inputs[j]?.getD []).toArray }
    , nextId := inputs.length + 1 }

def lnirOut (k : ParallelKernelKind) (inputs : List (List UInt64)) (len : Nat) : Option (List UInt64) :=
  match evalParKernelLoop (wordEnv inputs) (wordHeap inputs)
      ((List.range inputs.length).map (100 + ·)) len k (List.range len) with
  | .ok xs => some xs
  | _ => none

def runParsedPTX (k : PTXKernel) (nIn len : Nat) (inputs : List (List UInt64)) (fuel : Nat) :
    Option (List UInt64) :=
  let words := inputs.map (·.map UInt64.toBitVec)
  let gMem := LeanNative.Backend.PTXLower.mkPTXGlobalMem words nIn len
  let pMem := LeanNative.Backend.PTXLower.mkPTXParamMem nIn len
  match evalPTXKernel fuel k { x := 1, y := 1, z := 1 } { x := Nat.max 1 len, y := 1, z := 1 } gMem pMem with
  | .ok g => some ((List.range len).map fun i =>
      ((g.loadBits (nIn * len * 8 + i * 8) 8).getD 0#64).toNat.toUInt64)
  | _ => none

def runParsedMSL (k : MSLKernelDecl) (funcs : List MSLFuncDecl) (nIn len : Nat)
    (inputs : List (List UInt64)) (fuel : Nat) : Option (List UInt64) :=
  let inBufs : List (Nat × MetalAst.ByteMemory) := (List.range inputs.length).map fun j =>
    (j, MetalAst.ByteMemory.ofU64Words ((inputs[j]?.getD []).map UInt64.toBitVec))
  let dev := LeanNative.Backend.MetalLower.mkDeviceBuffers inBufs nIn len
  let cst := LeanNative.Backend.MetalLower.mkConstLenBuffers nIn len
  match evalMSLKernel fuel k { x := 1, y := 1, z := 1 } { x := Nat.max 1 len, y := 1, z := 1 } dev cst funcs with
  | .ok bufs =>
    match bufs.lookup nIn with
    | some m => some ((List.range len).map fun i => ((m.readU64Word? i).getD 0#64).toNat.toUInt64)
    | none => none
  | _ => none

def probePTX (modText : String) (decl : String) (nIn len fuel : Nat) (inputs : List (List UInt64))
    (expect : List UInt64) : Bool :=
  match findPTXKernel modText s!"lean_native_decl_{decl}" with
  | none => false
  | some k => runParsedPTX k nIn len inputs fuel == some expect

def probeMSL (modText : String) (decl : String) (nIn len fuel : Nat) (inputs : List (List UInt64))
    (expect : List UInt64) : Bool :=
  match findMSLKernel modText s!"lean_native_metal_decl_{decl}" with
  | none => false
  | some k => runParsedMSL k (findMSLFuncs modText) nIn len inputs fuel == some expect

def ptxProbeDecl (name : String) (body : ScalarExpr) : LNIRDecl :=
  { name := name, params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    retTy := .i64
    body := .parFor 2 0 [0, 1] .i64 (.customScalar 9 [0, 1] body) (.ret 2)
    isGpuCand := true }

def mslProbeDecl (name : String) (body : ScalarExpr) : LNIRDecl :=
  { name := name, params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    retTy := .i64
    body := .letBind 2 .i64 (.scalar body) (.ret 2)
    isGpuCand := true }

def probeMod : LNIRModule :=
  { moduleName := "GPUEmitVerify"
    decls := [ ptxProbeDecl "emit_sub" (.binOp .sub (.var 0) (.var 1))
             , ptxProbeDecl "emit_lt" (.binOp .lt (.var 0) (.var 1))
             , ptxProbeDecl "emit_shl" (.binOp .shl (.var 0) (.var 1))
             , ptxProbeDecl "emit_shr" (.binOp .shr (.var 0) (.var 1))
             , mslProbeDecl "msl_div" (.binOp .div (.var 0) (.var 1))
             , mslProbeDecl "msl_shl" (.binOp .shl (.var 0) (.var 1)) ] }

def verifyGPUEmitters : Bool :=
  let mlir := emitMLIRModule probeMod
  let ptx := emitPTXModule probeMod
  let msl := emitMetalModule probeMod
  let subIn := [[5, 1], [2, 4]]
  let ltIn := [[3, 2], [3, 5]]
  let divIn := [[18, 7], [3, 0]]
  let shlIn := [[1, 1], [32, 65]]
  let mlirShlIn0 : List UInt64 := [3, 8]
  let mlirShlIn1 : List UInt64 := [2, 1]
  let subExp := (lnirOut (.customScalar 9 [0, 1] (.binOp .sub (.var 0) (.var 1))) subIn 2).getD []
  let ltExp := (lnirOut (.customScalar 9 [0, 1] (.binOp .lt (.var 0) (.var 1))) ltIn 2).getD []
  let divExp := (lnirOut (.customScalar 9 [0, 1] (.binOp .div (.var 0) (.var 1))) divIn 2).getD []
  let shlExp := (lnirOut (.customScalar 9 [0, 1] (.binOp .shl (.var 0) (.var 1))) shlIn 2).getD []
  let mlirShlExp := (lnirOut (.customScalar 9 [0, 1] (.binOp .shl (.var 0) (.var 1)))
    [mlirShlIn0, mlirShlIn1] 2).getD []
  let mlirShrExp := (lnirOut (.customScalar 9 [0, 1] (.binOp .shr (.var 0) (.var 1)))
    [mlirShlIn0, mlirShlIn1] 2).getD []
  probePTX ptx "emit_sub" 2 2 200 subIn subExp &&
    probePTX ptx "emit_lt" 2 2 200 ltIn ltExp &&
    probeMSL msl "msl_div" 2 2 400 divIn divExp &&
    probeMSL msl "msl_shl" 2 2 400 shlIn shlExp &&
    evalParsedMLIRKernel1D mlir "emit_shl_parfor_0" mlirShlIn0 mlirShlIn1 == some mlirShlExp &&
    evalParsedMLIRKernel1D mlir "emit_shr_parfor_0" mlirShlIn0 mlirShlIn1 == some mlirShrExp &&
    subExp == [3, (1 : UInt64) - 4] && ltExp == [0, 1] && divExp == [6, 0] &&
    shlExp == [4294967296, 2] && mlirShlExp == [12, 16] && mlirShrExp == [0, 4]

end LeanNative.Backend.GPUEmitVerify
