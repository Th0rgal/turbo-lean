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

private def evalSingleBatchCaseObj (fuel : Nat) (arch : TargetArch) (mod : LNIRModule) (objStr : String) : String × Bool :=
  let trimmed := objStr.trimAscii.toString
  if !(trimmed.startsWith "{") || !(trimmed.endsWith "}") then
    ("{\"ok\":false,\"decl\":\"\",\"error\":\"malformed_case_json\"}", false)
  else
    let tape := JsonTape.indexJsonObject (ByteSlice.ofString trimmed)
    let caseId? := JsonTape.lookupSlice? tape "case_id" <|> JsonTape.lookupSlice? tape "id"
    let attachId (row : String) : String :=
      match caseId? with
      | none => row
      | some (idSlice, isStr) =>
        let rawId := idSlice.toStringLossy
        let idJson :=
          if isStr || !(isValidJsonScalarAtom rawId) then
            s!"\"{LeanNative.IR.jsonEscape rawId}\""
          else rawId.trimAscii.toString
        if row.startsWith "{" then s!"\{\"case_id\":{idJson},\"id\":{idJson}," ++ (row.drop 1).toString else row
    let fuelOpt : Option Nat :=
      match JsonTape.lookupSlice? tape "fuel" with
      | none => some fuel
      | some (fSlice, fIsStr) =>
        let ft := fSlice.toStringLossy.trimAscii.toString
        if fIsStr then ft.toNat? else ft.toNat?
    match JsonTape.lookupString? tape "decl" with
    | none =>
      (attachId "{\"ok\":false,\"decl\":\"\",\"error\":\"missing_decl_field\"}", false)
    | some declName =>
      match fuelOpt with
      | none =>
        (attachId s!"\{\"ok\":false,\"decl\":\"{LeanNative.IR.jsonEscape declName}\",\"error\":\"invalid_case_fuel\"}", false)
      | some caseFuel =>
        let argsOpt : Option (List UInt64) :=
          match JsonTape.lookupSlice? tape "args" with
          | none => some []
          | some (argSlice, isStr) => parseJsonArgsSlice? argSlice.toStringLossy isStr
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
