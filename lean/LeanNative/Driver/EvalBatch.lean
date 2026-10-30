import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanSys.Posix
import LeanSys.Codec

namespace LeanNative.Driver.CoreCLI

open LeanNative.IR
open LeanNative.Semantics
open LeanSys.Posix
open LeanSys.Codec

def evalScalarMask? (arch : TargetArch) : LNIRType → Option UInt64
  | .unit => some 0
  | .i1 => some 1
  | .i8 => some 0xFF
  | .i16 => some 0xFFFF
  | .i32 => some 0xFFFFFFFF
  | .usize =>
    if arch.isWasm then some 0xFFFFFFFF
    else if arch == .nvptx64 || arch == .hybridCpuGpu then none
    else some 0xFFFFFFFFFFFFFFFF
  | .i64 => some 0xFFFFFFFFFFFFFFFF
  | _ => none

def parseU64Token? (tok : String) : Option UInt64 :=
  let s := tok.trimAscii.toString
  let s' :=
    if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
      ((s.drop 1).dropEnd 1).trimAscii.toString
    else s
  match s'.toNat? with
  | some n => if n < 2^64 then some (UInt64.ofNat n) else none
  | none => none

def parseU64ArgsCsv (aStr : String) : IO (List UInt64) :=
  if aStr.trimAscii.toString.isEmpty then pure []
  else (aStr.splitOn ",").mapM fun tok => do
    match parseU64Token? tok with
    | some v => pure v
    | none => throw <| IO.userError s!"[lean-native] Invalid or out-of-range u64 argument '{tok}' in --args"

def evalDeclWithU64Args (fuel : Nat) (d : LNIRDecl) (dArgs : List UInt64) (arch : TargetArch := .x86_64) : String × Bool :=
  let paramMasks? := d.params.mapM (fun p => evalScalarMask? arch p.ty)
  let retMask? := evalScalarMask? arch d.retTy
  match paramMasks?, retMask? with
  | some pMasks, some rMask =>
    if d.assurance == .unsupported || d.params.length != dArgs.length then
      (s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape d.name}\",\"error\":\"unsupported_u64_signature_or_arity\"}", false)
    else
      let env := ((d.params.zip pMasks).zip dArgs).foldl (fun acc ((p, m), u) =>
        let masked := u &&& m
        let val := if p.ty == .unit then Val.unit else if p.ty == .i1 then Val.bool (masked != 0) else Val.u64 masked
        acc.bind p.id val) VarEnv.empty
      match evalCode fuel env HeapState.empty d.body with
      | Except.ok (retVal, finalHeap) =>
        let retU64? := match retVal, d.retTy with
          | .unit, .unit => some 0
          | .u64 _, .unit => some 0
          | .bool b, .i1 => some (if b then 1 else 0)
          | .u64 v, .i1 => some (if (v &&& 1) != 0 then 1 else 0)
          | .u64 v, _ => some (v &&& rMask)
          | .bool b, _ => some ((if b then 1 else 0) &&& rMask)
          | _, _ => none
        match retU64? with
        | none =>
          (s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape d.name}\",\"error\":\"return_type_mismatch\"}", false)
        | some retU64 =>
          let liveObjs := finalHeap.buffers.length + (finalHeap.refCounts.filter (fun (_, _, rc) => rc > 0)).length
          (s!"\{\"ok\":true,\"decl\":\"{LeanNative.IR.jsonEscape d.name}\",\"assurance\":\"{d.assurance}\",\"value_u64\":\"{retU64}\",\"live_objects\":{liveObjs}}", true)
      | Except.error ub =>
        (s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape d.name}\",\"error\":\"{LeanNative.IR.jsonEscape (toString (repr ub))}\"}", false)
  | _, _ =>
    (s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape d.name}\",\"error\":\"unsupported_u64_signature_or_arity\"}", false)

private def splitTopLevelJsonObjects (raw : String) : Option (List String) := Id.run do
  let t := raw.trimAscii.toString
  if t.isEmpty then return some []
  if !(t.startsWith "[") then
    return some ((raw.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))
  if !(t.endsWith "]") then return none
  let inner := ((t.drop 1).dropEnd 1).trimAscii.toString
  if inner.isEmpty then return some []
  let chars := inner.toList
  let mut objs : List String := []
  let mut cur : List Char := []
  let mut depth : Nat := 0
  let mut inStr : Bool := false
  let mut escaped : Bool := false
  for c in chars do
    if inStr then
      cur := c :: cur
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inStr := false
    else
      if c == '"' then
        inStr := true
        cur := c :: cur
      else if c == '{' then
        depth := depth + 1
        cur := c :: cur
      else if c == '}' then
        if depth == 0 then return none
        depth := depth - 1
        cur := c :: cur
        if depth == 0 then
          objs := objs ++ [String.ofList cur.reverse]
          cur := []
      else if depth > 0 then
        cur := c :: cur
      else if c != ',' && c != ' ' && c != '\t' && c != '\r' && c != '\n' then
        return none
  if depth != 0 || inStr || !cur.isEmpty then return none
  return some objs

private def parseJsonArgsSlice? (s : String) (isStr : Bool) : Option (List UInt64) :=
  let t := s.trimAscii.toString
  if isStr then
    if t.isEmpty then some []
    else (t.splitOn ",").mapM parseU64Token?
  else if t.startsWith "[" && t.endsWith "]" && t.length ≥ 2 then
    let body := ((t.drop 1).dropEnd 1).trimAscii.toString
    if body.isEmpty then some []
    else (body.splitOn ",").mapM parseU64Token?
  else none

private def findUniqueDeclPure (mod : LNIRModule) (name : String) : Option LNIRDecl :=
  match mod.decls.filter (fun d => d.name == name) with
  | [d] => some d
  | [] =>
    match mod.decls.filter (fun d => d.name.endsWith ("." ++ name)) with
    | [d] => some d
    | _ => none
  | _ => none

private def isValidJsonScalarAtom (s : String) : Bool :=
  let t := s.trimAscii.toString
  t == "null" || t == "true" || t == "false" || t.toNat?.isSome ||
    (t.startsWith "-" && (t.drop 1).toString.toNat?.isSome)

private def skipCharsWs : List Char → List Char
  | ' ' :: cs | '\t' :: cs | '\r' :: cs | '\n' :: cs => skipCharsWs cs
  | cs => cs

private def hex4? : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest =>
    [a, b, c, d].foldlM (fun (acc : Nat) (ch : Char) =>
      if ch.isDigit then some (acc * 16 + (ch.toNat - '0'.toNat))
      else if 'a' ≤ ch && ch ≤ 'f' then some (acc * 16 + (ch.toNat - 'a'.toNat + 10))
      else if 'A' ≤ ch && ch ≤ 'F' then some (acc * 16 + (ch.toNat - 'A'.toNat + 10))
      else none) 0 |>.map (fun n => (n, rest))
  | _ => none

private def unescapeJsonRawContent? (cs : List Char) : Option String := Id.run do
  let mut out : List Char := []
  let mut rem := cs
  while !rem.isEmpty do
    match rem with
    | '\\' :: 'u' :: rest =>
      let some (hi, r1) := hex4? rest | return none
      if 0xDC00 ≤ hi && hi < 0xE000 then return none
      if 0xD800 ≤ hi && hi < 0xDC00 then
        let '\\' :: 'u' :: r2 := r1 | return none
        let some (lo, r3) := hex4? r2 | return none
        if !(0xDC00 ≤ lo && lo < 0xE000) then return none
        out := Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :: out; rem := r3
      else
        out := Char.ofNat hi :: out; rem := r1
    | '\\' :: '"' :: rest => out := '"' :: out; rem := rest
    | '\\' :: '\\' :: rest => out := '\\' :: out; rem := rest
    | '\\' :: '/' :: rest => out := '/' :: out; rem := rest
    | '\\' :: 'b' :: rest => out := '\x08' :: out; rem := rest
    | '\\' :: 'f' :: rest => out := '\x0c' :: out; rem := rest
    | '\\' :: 'n' :: rest => out := '\n' :: out; rem := rest
    | '\\' :: 'r' :: rest => out := '\r' :: out; rem := rest
    | '\\' :: 't' :: rest => out := '\t' :: out; rem := rest
    | '\\' :: _ => return none
    | '"' :: _ => return none
    | c :: rest => if c.toNat < 0x20 then return none else out := c :: out; rem := rest
    | [] => break
  return some (String.ofList out.reverse)

#guard unescapeJsonRawContent? "a\\u0041\\u00e9".toList == some "aAé"
#guard unescapeJsonRawContent? "\\uD83D\\uDE00".toList == some "😀"
#guard unescapeJsonRawContent? "\\uD83D".toList == none
#guard unescapeJsonRawContent? "\\uDE00".toList == none
#guard unescapeJsonRawContent? "\\uD83Dx".toList == none
#guard unescapeJsonRawContent? "\\u00G1".toList == none
#guard unescapeJsonRawContent? "\\u004".toList == none
#guard unescapeJsonRawContent? "a\nb".toList == none
#guard unescapeJsonRawContent? "a\x01b".toList == none
#guard unescapeJsonRawContent? "\\u0001".toList == some "\x01"

private partial def parseStrictJsonValue (cs : List Char) : Option (String × Bool × List Char) :=
  match skipCharsWs cs with
  | '"' :: rest => Id.run do
    let mut raw : List Char := []
    let mut rem := rest
    let mut esc := false
    while !rem.isEmpty do
      let c := rem.head!
      rem := rem.tail!
      if esc then
        raw := c :: raw
        esc := false
      else if c == '\\' then
        raw := c :: raw
        esc := true
      else if c == '"' then
        return some (String.ofList raw.reverse, true, rem)
      else
        raw := c :: raw
    return none
  | '[' :: rest =>
    let rec parseElems (acc : List String) (r : List Char) : Option (String × Bool × List Char) := do
      let (v, isStr, r1) ← parseStrictJsonValue r
      let vLit := if isStr then "\"" ++ v ++ "\"" else v
      match skipCharsWs r1 with
      | ',' :: r2 => parseElems (vLit :: acc) r2
      | ']' :: r2 => some ("[" ++ String.intercalate "," (vLit :: acc).reverse ++ "]", false, r2)
      | _ => none
    match skipCharsWs rest with
    | ']' :: r2 => some ("[]", false, r2)
    | r => parseElems [] r
  | c :: rest =>
    let isAtomChar (ch : Char) := ch != ',' && ch != '}' && ch != ']' && ch != ' ' && ch != '\t' && ch != '\r' && ch != '\n' && ch != '"' && ch != ':' && ch != '{' && ch != '['
    if !isAtomChar c then none
    else
      let atom := String.ofList (c :: rest.takeWhile isAtomChar)
      let after := rest.dropWhile isAtomChar
      if isValidJsonScalarAtom atom then some (atom, false, after) else none
  | [] => none

private partial def parseStrictJsonObject (s : String) : Option (List (String × String × Bool)) :=
  let rec parsePairs (acc : List (String × String × Bool)) (r : List Char) : Option (List (String × String × Bool)) := do
    let (rawKey, isKeyStr, r1) ← parseStrictJsonValue r
    guard isKeyStr
    let key ← unescapeJsonRawContent? rawKey.toList
    match skipCharsWs r1 with
    | ':' :: r2 =>
      let (val, isStr, r3) ← parseStrictJsonValue r2
      if isStr then guard (unescapeJsonRawContent? val.toList).isSome
      match skipCharsWs r3 with
      | ',' :: r4 => parsePairs ((key, val, isStr) :: acc) r4
      | '}' :: r4 => if (skipCharsWs r4).isEmpty then some ((key, val, isStr) :: acc).reverse else none
      | _ => none
    | _ => none
  match skipCharsWs s.toList with
  | '{' :: r =>
    match skipCharsWs r with
    | '}' :: r2 => if (skipCharsWs r2).isEmpty then some [] else none
    | _ => parsePairs [] r
  | _ => none

#guard (parseStrictJsonObject "{\"decl\":\"f\\u0041\",\"id\":\"\\uD83D\\uDE00\"}").isSome
#guard (parseStrictJsonObject "{\"decl\":\"a\nb\"}").isNone
#guard (parseStrictJsonObject "{\"de\x01cl\":\"f\"}").isNone
#guard (parseStrictJsonObject "{\"decl\":\"\\uD800\"}").isNone

private def evalSingleBatchCaseObj (fuel : Nat) (arch : TargetArch) (mod : LNIRModule) (objStr : String) : String × Bool :=
  match parseStrictJsonObject objStr with
  | none =>
    ("{\"ok\":false,\"decl\":\"\",\"error\":\"malformed_case_json\"}", false)
  | some fields =>
    let lookupField? (k : String) : Option (String × Bool) :=
      (fields.find? (fun (fk, _, _) => fk == k)).map Prod.snd
    let caseId? := lookupField? "case_id" <|> lookupField? "id"
    let attachId (row : String) : String :=
      match caseId? with
      | none => row
      | some (rawId, isStr) =>
        let idJson :=
          if isStr then jsonStr ((unescapeJsonRawContent? rawId.toList).getD "")
          else rawId.trimAscii.toString
        if row.startsWith "{" then s!"\{\"case_id\":{idJson},\"id\":{idJson}," ++ (row.drop 1).toString else row
    let fuelOpt : Option Nat :=
      match lookupField? "fuel" with
      | none => some fuel
      | some (fRaw, fIsStr) =>
        if fIsStr then (unescapeJsonRawContent? fRaw.toList).bind (fun s => s.trimAscii.toString.toNat?)
        else fRaw.trimAscii.toString.toNat?
    let declOpt : Option String :=
      match lookupField? "decl" with
      | some (dRaw, true) => unescapeJsonRawContent? dRaw.toList
      | _ => none
    match declOpt with
    | none =>
      (attachId "{\"ok\":false,\"decl\":\"\",\"error\":\"missing_decl_field\"}", false)
    | some declName =>
      match fuelOpt with
      | none =>
        (attachId s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape declName}\",\"error\":\"invalid_case_fuel\"}", false)
      | some caseFuel =>
        let argsOpt : Option (List UInt64) :=
          match lookupField? "args" with
          | none => some []
          | some (argRaw, isStr) =>
            if isStr then (unescapeJsonRawContent? argRaw.toList).bind (parseJsonArgsSlice? · true)
            else parseJsonArgsSlice? argRaw false
        match argsOpt with
        | none =>
          (attachId s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape declName}\",\"error\":\"invalid_case_args\"}", false)
        | some parsedArgs =>
          match findUniqueDeclPure mod declName with
          | none =>
            (attachId s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape declName}\",\"error\":\"decl_missing_or_ambiguous\"}", false)
          | some d =>
            if parsedArgs.length != d.params.length then
              (attachId s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape d.name}\",\"error\":\"arity_mismatch\"}", false)
            else
              let (row, ok) := evalDeclWithU64Args caseFuel d parsedArgs arch
              (attachId row, ok)

def runEvalCasesFile (fuel : Nat) (arch : TargetArch) (mod : LNIRModule) (casesPath : String) : IO UInt32 := do
  if !(← System.FilePath.pathExists casesPath) then
    throw <| IO.userError s!"[lean-native] Cases file '{casesPath}' does not exist"
  let raw ← IO.FS.readFile casesPath
  let some objs := splitTopLevelJsonObjects raw
    | throw <| IO.userError s!"[lean-native] Malformed JSON cases container in '{casesPath}'"
  let mut rows : List String := []
  let mut allOk := true
  for objStr in objs do
    let (row, ok) := evalSingleBatchCaseObj fuel arch mod objStr
    if !ok then allOk := false
    rows := rows ++ [row]
  IO.println s!"[{String.intercalate "," rows}]"
  return if allOk then 0 else 1

end LeanNative.Driver.CoreCLI
