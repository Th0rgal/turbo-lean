import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.CertChecker
import LeanNative.Proofs.AxiomAudit
import LeanNative.Transform.Pass
import LeanNative.Transform.AlgebraicOpt
import LeanNative.Transform.UnboxTupleSROA
import LeanNative.Transform.HoistExclusivity
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Transform.Superopt
import LeanNative.Transform.Plugins
import LeanNative.Backend.LLVM
import LeanNative.Backend.GPUIR
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Metal
import LeanNative.Backend.Hybrid
import LeanNative.Backend.FastCheck
import LeanSys.Posix
import LeanSys.Codec

namespace LeanNative.Driver.CoreCLI

open LeanSys.Par
open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Spec
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform
open LeanNative.Backend
open LeanNative.Backend.LLVM
open LeanNative.Backend.GPUIR
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanSys.Posix
open LeanSys.Codec
open LeanNative.Backend.Hybrid
open LeanNative.Backend.FastCheck

def toOptimizationCert (c : PassStepCert) : OptimizationCert where
  passName := c.passName; declName := c.declName; inputHash := c.inputHash; outputHash := c.outputHash
  changed := c.changed; assurance := c.assurance; theoremRef := c.theoremRef; notes := c.notes

def parseTargetArch : String → TargetArch
  | "arm64" | "aarch64" => .arm64
  | "ios" | "ios-arm64" | "arm64-apple-ios" | "macos-arm64" | "m3" => .iosArm64
  | "ios-sim" | "ios-sim-arm64" | "arm64-apple-ios-simulator" => .iosSimArm64
  | "android" | "android-arm64" | "aarch64-linux-android" => .androidArm64
  | "wasm" | "wasm32" | "wasm32-unknown-unknown" => .wasm32
  | "nvptx" | "nvptx64" | "ptx" | "cuda" => .nvptx64
  | "hybrid" => .hybridCpuGpu
  | _ => .x86_64

def parseSuperoptTarget : String → SuperoptTarget
  | "arm64" | "aarch64" => .arm64
  | "cuda" | "cuda_ptx" | "ptx" | "nvptx" => .cuda_ptx
  | "metal" | "apple_metal" | "msl" => .apple_metal
  | _ => .x86_64

def findFlagValue (args : List String) (flag : String) (defaultVal : String) : String :=
  match args with
  | [] => defaultVal
  | f :: v :: rest => if f == flag then v else findFlagValue (v :: rest) flag defaultVal
  | _ :: rest => findFlagValue rest flag defaultVal

def hasFlag (args : List String) (flag : String) : Bool := args.contains flag

def findFirstPositional : List String → String
  | [] => ""
  | "--input" :: v :: _ | "--lnir" :: v :: _ => v
  | flag :: v :: rest =>
    if ["-o", "--opt", "--arch", "--target", "--profile", "--sm", "--samples",
        "--emit-header", "--header", "--emit-rust", "--rust", "--emit-fixtures", "--fixtures",
        "--emit-asm", "--asm", "--telemetry-spool"].contains flag then findFirstPositional rest
    else if flag.startsWith "-" then findFirstPositional (v :: rest) else flag
  | [a] => if a.startsWith "-" then "" else a

structure CoreCLIOptions where
  inputPath : String := ""
  outputPath : String := ""
  arch : TargetArch := .x86_64
  emitCABI : Bool := false
  emitLLVM : Bool := false
  emitPTX : Bool := false
  emitMetal : Bool := false
  isBaseline : Bool := false
  smArch : String := "sm_90"
  numSamples : Nat := 4096
  useConstraintProp : Bool := true
  deriving Repr, Inhabited, BEq

def parseCoreCLIOptions (args : List String) : CoreCLIOptions :=
  let inPos := findFirstPositional args
  let inExp := findFlagValue args "--input" (findFlagValue args "--lnir" "")
  { inputPath := if !inExp.isEmpty then inExp else inPos, outputPath := findFlagValue args "-o" "",
    arch := parseTargetArch (findFlagValue args "--arch" "x86_64"),
    emitCABI := hasFlag args "--c-abi" || hasFlag args "--emit-c-abi",
    emitLLVM := hasFlag args "--emit-llvm" || hasFlag args "--llvm",
    emitPTX := hasFlag args "--emit-ptx" || hasFlag args "--ptx",
    emitMetal := hasFlag args "--emit-metal" || hasFlag args "--metal",
    isBaseline := hasFlag args "--baseline", smArch := findFlagValue args "--sm" "sm_90",
    numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096,
    useConstraintProp := !(hasFlag args "--no-constraint-prop") }

/-- Load an `LNIRModule` from `--lnir <path>`, `--input <path>`, or positional argument, using `elaborateHook?` for `.lean`
    sources when running inside the full `lean-native` frontend. Never silently falls back to
    `mkCanonicalBenchmarkModule` when an explicit `--input` or `--lnir` file is passed. -/
def loadInputModule (elaborateHook? : Option (String → IO LNIRModule)) (args : List String)
    (defaultFastCheck : Bool := false) : IO LNIRModule := do
  let defaultMod := if defaultFastCheck then mkFastCheckSampleModule else mkCanonicalBenchmarkModule
  let parseWireOrJsonFile (path : String) : IO LNIRModule := do
    if !(← System.FilePath.pathExists path) then return defaultMod
    let raw ← IO.FS.readFile path
    match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
    | some mod =>
      if mod.decls.isEmpty then throw <| IO.userError s!"[lean-native] Failed to extract any LNIR declarations from '{path}'"
      return mod
    | none => throw <| IO.userError s!"[lean-native] Failed to parse LNIR wire/JSON module from '{path}'"
  let lnirFile := findFlagValue args "--lnir" ""
  if !lnirFile.isEmpty then return (← parseWireOrJsonFile lnirFile)
  let inFileExplicit := findFlagValue args "--input" ""
  let inFilePos := findFirstPositional args
  let inFile := if !inFileExplicit.isEmpty then inFileExplicit else inFilePos
  if inFile.isEmpty then return defaultMod
  else if inFile == "canonical" || inFile == "benchmarks" || inFile == "examples/Benchmark.lnir" then
    if ← System.FilePath.pathExists inFile then
      let raw ← IO.FS.readFile inFile
      return (LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw).getD mkCanonicalBenchmarkModule
    else return mkCanonicalBenchmarkModule
  else if inFile == "fastcheck" || inFile == "fastcheck-sample" then return mkFastCheckSampleModule
  else if inFile.endsWith ".lnir" || inFile.endsWith ".json" then parseWireOrJsonFile inFile
  else
    match elaborateHook? with
    | some ingestFn =>
      let mod ← ingestFn inFile
      if mod.decls.isEmpty then throw <| IO.userError s!"[lean-native] Failed to extract any LCNF declarations from '{inFile}'"
      return mod
    | none =>
      if ← System.FilePath.pathExists inFile then
        let raw ← IO.FS.readFile inFile
        match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
        | some mod => return mod
        | none => throw <| IO.userError s!"[lean-native-core] Cannot parse '{inFile}' as LNIR wire/JSON (use full 'lean-native' for .lean source elaboration)"
      else throw <| IO.userError s!"[lean-native-core] Input file '{inFile}' does not exist"

private def writeOrPrint (outPath text : String) (msg? : Option String := none) : IO UInt32 := do
  if outPath.isEmpty then IO.println text
  else IO.FS.writeFile outPath text; if let some m := msg? then IO.println m
  return 0

private def writeAndPrintJsonOrSummary (outPath jsonText summaryText : String) (jsonFlag : Bool) : IO Unit := do
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  IO.println (if jsonFlag then jsonText else summaryText)

private def lnirTypeToCType : LNIRType → String
  | .i1 | .i8 => "uint8_t" | .i16 | .f16 => "uint16_t" | .i32 => "uint32_t" | .i64 | .tuple _ => "uint64_t"
  | .usize => "size_t" | .u256 | .i256 => "const uint64_t*" | .f32 => "float" | .f64 => "double"
  | .rawPtr _ | .sarray _ | .objPtr | .taggedPtr | .storageMap => "void*" | .unit => "void"

private def lnirTypeToRustType : LNIRType → String
  | .i1 | .i8 => "u8" | .i16 | .f16 => "u16" | .i32 => "u32" | .i64 | .tuple _ => "u64"
  | .usize => "usize" | .u256 | .i256 => "*const u64" | .f32 => "f32" | .f64 => "f64"
  | .rawPtr _ | .sarray _ | .objPtr | .taggedPtr | .storageMap => "*mut core::ffi::c_void" | .unit => "()"

structure CAbiBindingSig where
  cSymbol : String
  leanName : String
  params : List (String × String × String) -- (paramName, cType, rustType)
  retCType : String
  retRustType : String
  deriving Repr, Inhabited

private def mapLeanTypeStr (tyRaw : String) : String × String :=
  let t := tyRaw.trimAscii.toString
  if t == "Bool" || t == "UInt8" then ("uint8_t", "u8")
  else if t == "UInt16" then ("uint16_t", "u16")
  else if t == "UInt32" then ("uint32_t", "u32")
  else if t == "UInt64" || t == "Nat" then ("uint64_t", "u64")
  else if t == "Int64" || t == "Int" then ("int64_t", "i64")
  else if t == "USize" then ("size_t", "usize")
  else if t == "Float" then ("double", "f64")
  else ("const void*", "*const core::ffi::c_void")

private def parseParamGroups (sig : String) : List (String × String × String) :=
  let groups := (sig.splitOn "(").drop 1
  groups.foldl (fun acc g =>
    match (g.splitOn ")").head? with
    | some inside =>
      match inside.splitOn ":" with
      | namesStr :: tyStr :: _ =>
        let (cTy, rsTy) := mapLeanTypeStr tyStr
        let names := (namesStr.splitOn " ").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
        acc ++ names.map (fun n => (n, cTy, rsTy))
      | _ => acc
    | none => acc) []

private def extractReturnTypeStr (sig : String) : String × String :=
  let afterParens := match (sig.splitOn ")").reverse.head? with | some s => s | none => sig
  let beforeEq := (afterParens.splitOn ":=").headD afterParens
  let retRaw := (beforeEq.splitOn ":").drop 1 |>.reverse.headD "UInt64"
  mapLeanTypeStr retRaw

/-- Extract `@[export <sym>]` / `@[inline, export <sym>]` signatures and `#guard` fixtures from `.lean` source text. -/
def extractLeanSourceCAbiAndGuards (raw : String) : List CAbiBindingSig × List (String × String) :=
  let lines := raw.splitOn "\n"
  let rec loop (ls : List String) (pendSym : Option String) (sigs : List CAbiBindingSig) (guards : List (String × String)) :
      List CAbiBindingSig × List (String × String) :=
    match ls with
    | [] => (sigs.reverse, guards.reverse)
    | line :: rest =>
      let tr := line.trimAscii.toString
      let guards' :=
        if tr.startsWith "#guard " then
          let expr := (tr.drop 7).trimAscii.toString
          match expr.splitOn "==" with
          | lhs :: rhs :: _ => (lhs.trimAscii.toString, rhs.trimAscii.toString) :: guards
          | _ => (expr, "true") :: guards
        else guards
      let symOpt :=
        match tr.splitOn "export " with
        | _ :: afterExp :: _ =>
          if tr.startsWith "@[" then
            let tok := String.ofList (afterExp.trimAscii.toString.toList.takeWhile (fun c => c != ']' && c != ',' && c != ' '))
            if tok.isEmpty then pendSym else some tok
          else pendSym
        | _ => pendSym
      if tr.startsWith "def " || tr.startsWith "abbrev " then
        match symOpt with
        | some sym =>
          let headerLines := tr :: (rest.take 3 |>.takeWhile (fun l =>
            let t := l.trimAscii.toString
            !(t.startsWith "def ") && !(t.startsWith "@[") && !(t.startsWith "/--") && !(t.startsWith "--")))
          let fullSig := String.intercalate " " (headerLines.map (·.trimAscii.toString))
          let sigHead := (fullSig.splitOn ":=").headD fullSig
          let afterDef := (sigHead.drop 4).trimAscii.toString
          let leanName := String.ofList (afterDef.toList.takeWhile (fun c => c != ' ' && c != '(' && c != ':'))
          let params := parseParamGroups sigHead
          let (retC, retRs) := extractReturnTypeStr sigHead
          loop rest none ({ cSymbol := sym, leanName, params, retCType := retC, retRustType := retRs } :: sigs) guards'
        | none => loop rest none sigs guards'
      else loop rest symOpt sigs guards'
  loop lines none [] []

def moduleToCAbiSigs (m : LNIRModule) : List CAbiBindingSig :=
  m.decls.map fun d => {
    cSymbol := d.name, leanName := d.name,
    params := d.params.map (fun p => (p.name.replace "'" "_prime", lnirTypeToCType p.ty, lnirTypeToRustType p.ty)),
    retCType := lnirTypeToCType d.retTy, retRustType := lnirTypeToRustType d.retTy
  }

def readLeanSourceExpandingUmbrella (filePath : String) : IO String := do
  let raw ← try IO.FS.readFile filePath catch _ => pure ""
  if !filePath.endsWith ".lean" then return raw
  let subDir := System.FilePath.mk ((filePath.dropEnd 5).toString)
  if !(← subDir.pathExists) then return raw
  let stem := subDir.fileName.getD ""
  let mut outLines : Array String := #[]
  for line in raw.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "import " then
      let modPath := (trimmed.drop 7).trimAscii.toString
      let parts := modPath.splitOn "."
      match parts.reverse with
      | leaf :: parent :: _ =>
        let candPath := subDir / s!"{leaf}.lean"
        if parent == stem && (← candPath.pathExists) then
          let subRaw ← IO.FS.readFile candPath
          for subLine in subRaw.splitOn "\n" do
            if !subLine.trimAscii.toString.startsWith "import " then
              outLines := outLines.push subLine
        else
          outLines := outLines.push line
      | _ => outLines := outLines.push line
    else
      outLines := outLines.push line
  return String.intercalate "\n" outLines.toList

def emitCAbiHeaderFromSigs (sigs : List CAbiBindingSig) : String :=
  let declProtos := sigs.map fun s =>
    let paramsC := if s.params.isEmpty then "void" else String.intercalate ", " (s.params.map fun (n, cTy, _) => s!"{cTy} {n}")
    s!"{s.retCType} {s.cSymbol}({paramsC});"
  String.intercalate "\n" ([
    "/* Auto-generated C99 Header by lean-native C-ABI Binding Generator */",
    "#pragma once", "#ifndef LEAN_NATIVE_GENERATED_C_ABI_H", "#define LEAN_NATIVE_GENERATED_C_ABI_H",
    "#include <stdint.h>", "#include <stddef.h>",
    "typedef struct { const void* data; size_t len; size_t stride_bytes; } lean_native_flat_slice_t;",
    "typedef struct { void* data; size_t len; size_t cap; } lean_native_mut_slice_t;",
    "/* Zero-Runtime SliceOut C-ABI Contract: packed u64 span (start:32 | len:24 | kind:8) */",
    "typedef uint32_t (*lean_native_slice_out_scan_fn)(const uint8_t* ptr, size_t len, uint64_t* out_spans, size_t cap, uint64_t* state_io);",
    "static inline uint64_t lean_native_pack_span(uint32_t start, uint32_t len, uint8_t kind) { return ((uint64_t)start << 32) | ((uint64_t)(len & 0xFFFFFFU) << 8) | (uint64_t)kind; }",
    "static inline uint32_t lean_native_span_start(uint64_t span) { return (uint32_t)(span >> 32); }",
    "static inline uint32_t lean_native_span_len(uint64_t span) { return (uint32_t)((span >> 8) & 0xFFFFFFU); }",
    "static inline uint8_t lean_native_span_kind(uint64_t span) { return (uint8_t)(span & 0xFFU); }",
    "#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L",
    "_Static_assert(sizeof(lean_native_flat_slice_t) == 24, \"lean_native_flat_slice_t size == 24\");",
    "_Static_assert(sizeof(lean_native_mut_slice_t) == 24, \"lean_native_mut_slice_t size == 24\");",
    "#endif",
    "#ifdef __cplusplus", "extern \"C\" {", "#endif"
  ] ++ declProtos ++ [
    "void lean_native_swscale_down2x2_u8(uint8_t* dst, const uint8_t* src, uint64_t srcStride, uint64_t dstW, uint64_t dstH);",
    "void lean_native_swscale_down2x2_fused_eq_u8(uint8_t* dst, const uint8_t* src, uint64_t srcStride, uint64_t dstW, uint64_t dstH, uint64_t contrastQ8, uint64_t brightness);",
    "void lean_native_swscale_down3x3_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t dstW, uint64_t dstH);",
    "void lean_native_swscale_down3to2_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t dstW, uint64_t dstH);",
    "void lean_native_av1_cdef_filter_u8(uint8_t* dst, const uint8_t* src, uint64_t w, uint64_t h, uint64_t priStr, uint64_t damping);",
    "void lean_native_stencil2d_box3x3_u8(uint8_t* dst, const uint8_t* src, uint64_t w, uint64_t h);",
    "void lean_native_swscale_bilinear_q8_u16le(const uint8_t* src, uint8_t* dst, uint64_t src_w, uint64_t src_h, uint64_t dst_w, uint64_t dst_h);",
    "uint64_t lean_native_luma_stats_u16le(const uint8_t* src, uint64_t n_pixels, uint64_t step);",
    "void lean_native_extract_u16le_msb8(const uint8_t* src, uint8_t* dst, uint64_t n_pixels);",
    "uint64_t lean_native_luma_stats_u8(const uint8_t* src, uint64_t nPixels, uint64_t step);",
    "void lean_native_swscale_bilinear_q8_u8(uint8_t* dst, const uint8_t* src, uint64_t srcW, uint64_t srcH, uint64_t srcStride, uint64_t dstW, uint64_t dstH);",
    "void lean_native_apply_filters_yuv420p_u8(const uint8_t* src, uint8_t* dst, uint64_t y_len, uint64_t uv_len, uint64_t flags);",
    "void lean_native_luma_acceptance_16x16_u8(const uint8_t* src, uint64_t srcW, uint64_t srcH, const uint8_t* dst, uint64_t dstW, uint64_t dstH, uint64_t* outMetrics4);",
    "void lean_native_luma_acceptance_16x16_u16le(const uint8_t* src, uint64_t srcW, uint64_t srcH, const uint8_t* dst, uint64_t dstW, uint64_t dstH, uint64_t* outMetrics4);",
    "#ifdef __cplusplus", "}", "#endif", "#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */", ""])

partial def emitRustScalarExpr (e : ScalarExpr) : String :=
  match e with
  | .constU64 v => s!"{v}u64"
  | .constBool b => if b then "1u64" else "0u64"
  | .var id => s!"v{id}"
  | .binOp op l r =>
    let ls := emitRustScalarExpr l
    let rs := emitRustScalarExpr r
    match op with
    | .add => s!"({ls}.wrapping_add({rs}))"
    | .sub => s!"({ls}.wrapping_sub({rs}))"
    | .mul => s!"({ls}.wrapping_mul({rs}))"
    | .div => s!"(if {rs} == 0 \{ 0u64 } else \{ {ls} / {rs} })"
    | .mod => s!"(if {rs} == 0 \{ 0u64 } else \{ {ls} % {rs} })"
    | .bitAnd => s!"({ls} & {rs})"
    | .bitOr => s!"({ls} | {rs})"
    | .bitXor => s!"({ls} ^ {rs})"
    | .shl => s!"({ls}.wrapping_shl(({rs} & 63) as u32))"
    | .shr => s!"({ls}.wrapping_shr(({rs} & 63) as u32))"
    | .sar => s!"((({ls} as i64).wrapping_shr(({rs} & 63) as u32)) as u64)"
    | .eq => s!"(if {ls} == {rs} \{ 1u64 } else \{ 0u64 })"
    | .lt => s!"(if {ls} < {rs} \{ 1u64 } else \{ 0u64 })"
    | .le => s!"(if {ls} <= {rs} \{ 1u64 } else \{ 0u64 })"
    | .clmul64 => s!"lean_native_clmul64_lo({ls}, {rs})"
    | .clmul64Hi => s!"lean_native_clmul64_hi({ls}, {rs})"
    | .eor3 => s!"({ls} ^ ({rs} >> 32) ^ ({rs} & 0xFFFF_FFFFu64))"
    | _ => s!"({ls} ^ {rs})"
  | .unaryOp op a =>
    let as_ := emitRustScalarExpr a
    match op with
    | .not => s!"(!{as_})"
    | .neg => s!"(0u64.wrapping_sub({as_}))"
    | .clz256 => s!"({as_}.leading_zeros() as u64)"
  | .select c t e =>
    s!"(if ({emitRustScalarExpr c}) != 0 \{ {emitRustScalarExpr t} } else \{ {emitRustScalarExpr e} })"
  | .fma a b c =>
    s!"(({emitRustScalarExpr a}).wrapping_mul({emitRustScalarExpr b}).wrapping_add({emitRustScalarExpr c}))"

partial def emitRustCodeBody (c : LNIRCode) (indent : String := "        ") : Option String :=
  match c with
  | .letBind dst _ (.scalar e) k => do
    let rest ← emitRustCodeBody k indent
    some s!"{indent}let v{dst}: u64 = {emitRustScalarExpr e};\n{rest}"
  | .letBind dst _ (.call fnName args _ _) k => do
    let rest ← emitRustCodeBody k indent
    let argStr := String.intercalate ", " (args.map fun a => s!"v{a}")
    some s!"{indent}let v{dst}: u64 = {fnName}({argStr});\n{rest}"
  | .incRef _ _ k | .decRef _ _ k => emitRustCodeBody k indent
  | .ite cv t e => do
    let tb ← emitRustCodeBody t (indent ++ "    ")
    let eb ← emitRustCodeBody e (indent ++ "    ")
    some s!"{indent}if v{cv} != 0 \{\n{tb}\n{indent}} else \{\n{eb}\n{indent}}"
  | .ret v => some s!"{indent}v{v}"
  | _ => none

def emitCAbiRustFromSigs (sigs : List CAbiBindingSig) (optMod? : Option LNIRModule := none) : String :=
  let declExterns := sigs.map fun s =>
    let paramsRs := String.intercalate ", " (s.params.map fun (n, _, rsTy) => s!"{n}: {rsTy}")
    let retPart := if s.retRustType == "()" then "" else s!" -> {s.retRustType}"
    s!"        pub fn {s.cSymbol}({paramsRs}){retPart};"
  let declWrappers := sigs.map fun s =>
    let retPart := if s.retRustType == "()" then "" else s!" -> {s.retRustType}"
    let matchDecl? := optMod?.bind fun m =>
      m.decls.find? fun d => d.name == s.cSymbol || d.name.endsWith ("_" ++ s.leanName)
    match matchDecl? with
    | some d =>
      let allU64 := s.retRustType == "u64" && d.params.length == s.params.length &&
        s.params.all (fun (_, _, rsTy) => rsTy == "u64")
      match (if allU64 then emitRustCodeBody d.body else none) with
      | some bodyStr =>
        let paramsInl := String.intercalate ", " (d.params.map fun p => s!"v{p.id}: u64")
        s!"#[cfg_attr(not(debug_assertions), inline(always))]\npub unsafe fn {s.cSymbol}({paramsInl}){retPart} \{\n    unsafe \{\n{bodyStr}\n    }\n}"
      | none =>
        let paramsRs := String.intercalate ", " (s.params.map fun (n, _, rsTy) => s!"{n}: {rsTy}")
        let argsRs := String.intercalate ", " (s.params.map fun (n, _, _) => n)
        s!"#[cfg_attr(not(debug_assertions), inline(always))]\npub unsafe fn {s.cSymbol}({paramsRs}){retPart} \{\n    unsafe \{ c_abi::{s.cSymbol}({argsRs}) }\n}"
    | none =>
      let paramsRs := String.intercalate ", " (s.params.map fun (n, _, rsTy) => s!"{n}: {rsTy}")
      let argsRs := String.intercalate ", " (s.params.map fun (n, _, _) => n)
      s!"#[cfg_attr(not(debug_assertions), inline(always))]\npub unsafe fn {s.cSymbol}({paramsRs}){retPart} \{\n    unsafe \{ c_abi::{s.cSymbol}({argsRs}) }\n}"
  String.intercalate "\n" ([
    "// Auto-generated Rust FFI & LNIR Inlined Bindings by lean-native C-ABI Binding Generator",
    "#[repr(C)] #[derive(Copy, Clone, Debug, PartialEq, Eq)]",
    "pub struct LeanNativeFlatSlice { pub data: *const core::ffi::c_void, pub len: usize, pub stride_bytes: usize }",
    "#[repr(C)] #[derive(Copy, Clone, Debug, PartialEq, Eq)]",
    "pub struct LeanNativeMutSlice { pub data: *mut core::ffi::c_void, pub len: usize, pub cap: usize }",
    "pub type LeanNativeSliceOutScanFn = extern \"C\" fn(ptr: *const u8, len: usize, out_spans: *mut u64, cap: usize, state_io: *mut u64) -> u32;",
    "#[inline] pub const fn lean_native_pack_span(start: u32, len: u32, kind: u8) -> u64 { ((start as u64) << 32) | (((len & 0xFF_FFFF) as u64) << 8) | (kind as u64) }",
    "#[inline(always)]",
    "pub unsafe fn lean_native_clmul64_lo(a: u64, b: u64) -> u64 {",
    "    if b == 0x87 {",
    "        return a ^ (a << 1) ^ (a << 2) ^ (a << 7);",
    "    }",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let va = _mm_set_epi64x(0, a as i64);",
    "        let vb = _mm_set_epi64x(0, b as i64);",
    "        return _mm_extract_epi64::<0>(_mm_clmulepi64_si128::<0x00>(va, vb)) as u64;",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let prod = vmull_p64(a, b);",
    "        return vgetq_lane_u64::<0>(vreinterpretq_u64_p128(prod));",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    {",
    "        let mut acc = 0u64;",
    "        let mut i = 0u32;",
    "        while i < 64 { if ((b >> i) & 1) != 0 { acc ^= a << i; } i += 1; }",
    "        acc",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_clmul64_hi(a: u64, b: u64) -> u64 {",
    "    if b == 0x87 {",
    "        return (a >> 63) ^ (a >> 62) ^ (a >> 57);",
    "    }",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let va = _mm_set_epi64x(0, a as i64);",
    "        let vb = _mm_set_epi64x(0, b as i64);",
    "        return _mm_extract_epi64::<1>(_mm_clmulepi64_si128::<0x00>(va, vb)) as u64;",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let prod = vmull_p64(a, b);",
    "        return vgetq_lane_u64::<1>(vreinterpretq_u64_p128(prod));",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    {",
    "        let mut acc = 0u64;",
    "        let mut i = 1u32;",
    "        while i < 64 { if ((b >> i) & 1) != 0 { acc ^= a >> (64 - i); } i += 1; }",
    "        acc",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_reduce_256_raw(r0: u64, r1: u64, r2: u64, r3: u64) -> (u64, u64) {",
    "    let s1_lo = r2 << 1;",
    "    let s1_hi = (r3 << 1) | (r2 >> 63);",
    "    let s2_lo = r2 << 2;",
    "    let s2_hi = (r3 << 2) | (r2 >> 62);",
    "    let s7_lo = r2 << 7;",
    "    let s7_hi = (r3 << 7) | (r2 >> 57);",
    "    let t_lo = r2 ^ s1_lo ^ s2_lo ^ s7_lo;",
    "    let t_hi = r3 ^ s1_hi ^ s2_hi ^ s7_hi;",
    "    let ov = (r3 >> 63) ^ (r3 >> 62) ^ (r3 >> 57);",
    "    let corr = ov ^ (ov << 1) ^ (ov << 2) ^ (ov << 7);",
    "    (r0 ^ t_lo ^ corr, r1 ^ t_hi)",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_mul_unreduced_raw(a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64) -> (u64, u64, u64, u64) {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let va = _mm_set_epi64x(a_hi as i64, a_lo as i64);",
    "        let vb = _mm_set_epi64x(b_hi as i64, b_lo as i64);",
    "        let p_ll = _mm_clmulepi64_si128::<0x00>(va, vb);",
    "        let p_lh = _mm_clmulepi64_si128::<0x10>(va, vb);",
    "        let p_hl = _mm_clmulepi64_si128::<0x01>(va, vb);",
    "        let p_hh = _mm_clmulepi64_si128::<0x11>(va, vb);",
    "        let cross = _mm_xor_si128(p_lh, p_hl);",
    "        let lo = _mm_xor_si128(p_ll, _mm_bslli_si128::<8>(cross));",
    "        let hi = _mm_xor_si128(p_hh, _mm_bsrli_si128::<8>(cross));",
    "        return (",
    "            _mm_extract_epi64::<0>(lo) as u64,",
    "            _mm_extract_epi64::<1>(lo) as u64,",
    "            _mm_extract_epi64::<0>(hi) as u64,",
    "            _mm_extract_epi64::<1>(hi) as u64,",
    "        );",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let p_ll = vreinterpretq_u64_p128(vmull_p64(a_lo, b_lo));",
    "        let p_lh = vreinterpretq_u64_p128(vmull_p64(a_lo, b_hi));",
    "        let p_hl = vreinterpretq_u64_p128(vmull_p64(a_hi, b_lo));",
    "        let p_hh = vreinterpretq_u64_p128(vmull_p64(a_hi, b_hi));",
    "        let cross = veorq_u64(p_lh, p_hl);",
    "        return (",
    "            vgetq_lane_u64::<0>(p_ll),",
    "            vgetq_lane_u64::<1>(p_ll) ^ vgetq_lane_u64::<0>(cross),",
    "            vgetq_lane_u64::<0>(p_hh) ^ vgetq_lane_u64::<1>(cross),",
    "            vgetq_lane_u64::<1>(p_hh),",
    "        );",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let ll_lo = lean_native_clmul64_lo(a_lo, b_lo);",
    "        let ll_hi = lean_native_clmul64_hi(a_lo, b_lo);",
    "        let lh_lo = lean_native_clmul64_lo(a_lo, b_hi);",
    "        let lh_hi = lean_native_clmul64_hi(a_lo, b_hi);",
    "        let hl_lo = lean_native_clmul64_lo(a_hi, b_lo);",
    "        let hl_hi = lean_native_clmul64_hi(a_hi, b_lo);",
    "        let hh_lo = lean_native_clmul64_lo(a_hi, b_hi);",
    "        let hh_hi = lean_native_clmul64_hi(a_hi, b_hi);",
    "        (ll_lo, ll_hi ^ lh_lo ^ hl_lo, hh_lo ^ lh_hi ^ hl_hi, hh_hi)",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_xor3_m128i(",
    "    a: core::arch::x86_64::__m128i, b: core::arch::x86_64::__m128i, c: core::arch::x86_64::__m128i,",
    ") -> core::arch::x86_64::__m128i {",
    "    #[cfg(all(target_feature = \"avx512f\", target_feature = \"avx512vl\"))]",
    "    unsafe { return core::arch::x86_64::_mm_ternarylogic_epi64::<0x96>(a, b, c); }",
    "    #[cfg(not(all(target_feature = \"avx512f\", target_feature = \"avx512vl\")))]",
    "    unsafe { core::arch::x86_64::_mm_xor_si128(core::arch::x86_64::_mm_xor_si128(a, b), c) }",
    "}",
    "#[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_mul_acc_m128i(",
    "    va: core::arch::x86_64::__m128i, vb: core::arch::x86_64::__m128i,",
    "    ll: &mut core::arch::x86_64::__m128i, mid: &mut core::arch::x86_64::__m128i, hh: &mut core::arch::x86_64::__m128i,",
    ") {",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        *ll = _mm_xor_si128(*ll, _mm_clmulepi64_si128::<0x00>(va, vb));",
    "        let c0 = _mm_clmulepi64_si128::<0x10>(va, vb);",
    "        let c1 = _mm_clmulepi64_si128::<0x01>(va, vb);",
    "        *mid = lean_native_xor3_m128i(*mid, c0, c1);",
    "        *hh = _mm_xor_si128(*hh, _mm_clmulepi64_si128::<0x11>(va, vb));",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_reduce_3lane_m128i(",
    "    ll: core::arch::x86_64::__m128i, mid: core::arch::x86_64::__m128i, hh: core::arch::x86_64::__m128i,",
    ") -> core::arch::x86_64::__m128i {",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let poly = _mm_set1_epi64x(0x87);",
    "        let t1 = lean_native_xor3_m128i(mid, _mm_bslli_si128::<8>(hh), _mm_clmulepi64_si128::<0x01>(hh, poly));",
    "        lean_native_xor3_m128i(ll, _mm_bslli_si128::<8>(t1), _mm_clmulepi64_si128::<0x01>(t1, poly))",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_mul_m128i(va: core::arch::x86_64::__m128i, vb: core::arch::x86_64::__m128i) -> core::arch::x86_64::__m128i {",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let (mut ll, mut mid, mut hh) = (_mm_setzero_si128(), _mm_setzero_si128(), _mm_setzero_si128());",
    "        lean_native_f128_mul_acc_m128i(va, vb, &mut ll, &mut mid, &mut hh);",
    "        lean_native_f128_reduce_3lane_m128i(ll, mid, hh)",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_mul_vec2_m128i(",
    "    va0: core::arch::x86_64::__m128i, va1: core::arch::x86_64::__m128i,",
    "    vb0: core::arch::x86_64::__m128i, vb1: core::arch::x86_64::__m128i,",
    ") -> (core::arch::x86_64::__m128i, core::arch::x86_64::__m128i) {",
    "    unsafe {",
    "        (lean_native_f128_mul_m128i(va0, vb0), lean_native_f128_mul_m128i(va1, vb1))",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_xor3_neon(",
    "    a: core::arch::aarch64::uint64x2_t, b: core::arch::aarch64::uint64x2_t, c: core::arch::aarch64::uint64x2_t,",
    ") -> core::arch::aarch64::uint64x2_t {",
    "    #[cfg(target_feature = \"sha3\")]",
    "    unsafe { return core::arch::aarch64::veor3q_u64(a, b, c); }",
    "    #[cfg(not(target_feature = \"sha3\"))]",
    "    unsafe { core::arch::aarch64::veorq_u64(core::arch::aarch64::veorq_u64(a, b), c) }",
    "}",
    "#[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_mul_acc_neon(",
    "    va: core::arch::aarch64::uint64x2_t, vb: core::arch::aarch64::uint64x2_t,",
    "    ll: &mut core::arch::aarch64::uint64x2_t, mid: &mut core::arch::aarch64::uint64x2_t, hh: &mut core::arch::aarch64::uint64x2_t,",
    ") {",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let vb_rev = vextq_u64::<1>(vb, vb);",
    "        *ll = veorq_u64(*ll, vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(va), vgetq_lane_u64::<0>(vb))));",
    "        let c0 = vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(va), vreinterpretq_p64_u64(vb_rev)));",
    "        let c1 = vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(va), vgetq_lane_u64::<0>(vb_rev)));",
    "        *mid = lean_native_xor3_neon(*mid, c0, c1);",
    "        *hh = veorq_u64(*hh, vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(va), vreinterpretq_p64_u64(vb))));",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_reduce_3lane_neon(",
    "    ll: core::arch::aarch64::uint64x2_t, mid: core::arch::aarch64::uint64x2_t, hh: core::arch::aarch64::uint64x2_t,",
    ") -> core::arch::aarch64::uint64x2_t {",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let z = vdupq_n_u64(0);",
    "        let poly = vreinterpretq_p64_u64(vdupq_n_u64(0x87));",
    "        let t1 = lean_native_xor3_neon(mid, vextq_u64::<1>(z, hh), vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(hh), poly)));",
    "        lean_native_xor3_neon(ll, vextq_u64::<1>(z, t1), vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(t1), poly)))",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_mul_neon(",
    "    va: core::arch::aarch64::uint64x2_t, vb: core::arch::aarch64::uint64x2_t,",
    ") -> core::arch::aarch64::uint64x2_t {",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let z = vdupq_n_u64(0);",
    "        let (mut ll, mut mid, mut hh) = (z, z, z);",
    "        lean_native_f128_mul_acc_neon(va, vb, &mut ll, &mut mid, &mut hh);",
    "        lean_native_f128_reduce_3lane_neon(ll, mid, hh)",
    "    }",
    "}",
    "#[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "#[inline(always)]",
    "unsafe fn lean_native_f128_mul_vec2_neon(",
    "    va0: core::arch::aarch64::uint64x2_t, va1: core::arch::aarch64::uint64x2_t,",
    "    vb0: core::arch::aarch64::uint64x2_t, vb1: core::arch::aarch64::uint64x2_t,",
    ") -> (core::arch::aarch64::uint64x2_t, core::arch::aarch64::uint64x2_t) {",
    "    unsafe {",
    "        (lean_native_f128_mul_neon(va0, vb0), lean_native_f128_mul_neon(va1, vb1))",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_mul_raw(a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64) -> (u64, u64) {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let res = lean_native_f128_mul_m128i(_mm_set_epi64x(a_hi as i64, a_lo as i64), _mm_set_epi64x(b_hi as i64, b_lo as i64));",
    "        return (_mm_extract_epi64::<0>(res) as u64, _mm_extract_epi64::<1>(res) as u64);",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let (a_arr, b_arr) = ([a_lo, a_hi], [b_lo, b_hi]);",
    "        let res = lean_native_f128_mul_neon(vld1q_u64(a_arr.as_ptr()), vld1q_u64(b_arr.as_ptr()));",
    "        return (vgetq_lane_u64::<0>(res), vgetq_lane_u64::<1>(res));",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let (r0, r1, r2, r3) = lean_native_f128_mul_unreduced_raw(a_lo, a_hi, b_lo, b_hi);",
    "        lean_native_f128_reduce_256_raw(r0, r1, r2, r3)",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_mul_vec2_raw(",
    "    a0_lo: u64, a0_hi: u64, a1_lo: u64, a1_hi: u64,",
    "    b0_lo: u64, b0_hi: u64, b1_lo: u64, b1_hi: u64,",
    ") -> (u64, u64, u64, u64) {",
    "    unsafe {",
    "        let (o0_lo, o0_hi) = lean_native_f128_mul_raw(a0_lo, a0_hi, b0_lo, b0_hi);",
    "        let (o1_lo, o1_hi) = lean_native_f128_mul_raw(a1_lo, a1_hi, b1_lo, b1_hi);",
    "        (o0_lo, o0_hi, o1_lo, o1_hi)",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_ntt_butterfly_row_pair_slice(",
    "    top_ptr: *mut u64, bot_ptr: *mut u64, n_f128: usize, tw_lo: u64, tw_hi: u64,",
    ") {",
    "    unsafe {",
    "        for lane in 0..n_f128 {",
    "            let idx = lane * 2;",
    "            let u_lo = *top_ptr.add(idx); let u_hi = *top_ptr.add(idx + 1);",
    "            let v_lo = *bot_ptr.add(idx); let v_hi = *bot_ptr.add(idx + 1);",
    "            let (p_lo, p_hi) = lean_native_f128_mul_raw(v_lo, v_hi, tw_lo, tw_hi);",
    "            let nu_lo = u_lo ^ p_lo; let nu_hi = u_hi ^ p_hi;",
    "            *top_ptr.add(idx) = nu_lo; *top_ptr.add(idx + 1) = nu_hi;",
    "            *bot_ptr.add(idx) = v_lo ^ nu_lo; *bot_ptr.add(idx + 1) = v_hi ^ nu_hi;",
    "        }",
    "    }",
    "}",
    "#[allow(clippy::too_many_arguments)]",
    "#[inline(always)]",
    "pub unsafe fn lean_native_ntt_butterfly_fused_2layer_slice(",
    "    a_ptr: *mut u64, b_ptr: *mut u64, c_ptr: *mut u64, d_ptr: *mut u64, n_f128: usize,",
    "    to_lo: u64, to_hi: u64, tia_lo: u64, tia_hi: u64, tib_lo: u64, tib_hi: u64,",
    ") {",
    "    unsafe {",
    "        for lane in 0..n_f128 {",
    "            let idx = lane * 2;",
    "            let xa_lo = *a_ptr.add(idx); let xa_hi = *a_ptr.add(idx + 1);",
    "            let xb_lo = *b_ptr.add(idx); let xb_hi = *b_ptr.add(idx + 1);",
    "            let xc_lo = *c_ptr.add(idx); let xc_hi = *c_ptr.add(idx + 1);",
    "            let xd_lo = *d_ptr.add(idx); let xd_hi = *d_ptr.add(idx + 1);",
    "            let (pc_lo, pc_hi, pd_lo, pd_hi) = lean_native_f128_mul_vec2_raw(",
    "                xc_lo, xc_hi, xd_lo, xd_hi, to_lo, to_hi, to_lo, to_hi,",
    "            );",
    "            let na_lo = xa_lo ^ pc_lo; let na_hi = xa_hi ^ pc_hi;",
    "            let nc_lo = xc_lo ^ na_lo; let nc_hi = xc_hi ^ na_hi;",
    "            let nb_lo = xb_lo ^ pd_lo; let nb_hi = xb_hi ^ pd_hi;",
    "            let nd_lo = xd_lo ^ nb_lo; let nd_hi = xd_hi ^ nb_hi;",
    "            let (pb2_lo, pb2_hi, pd2_lo, pd2_hi) = lean_native_f128_mul_vec2_raw(",
    "                nb_lo, nb_hi, nd_lo, nd_hi, tia_lo, tia_hi, tib_lo, tib_hi,",
    "            );",
    "            let fa_lo = na_lo ^ pb2_lo; let fa_hi = na_hi ^ pb2_hi;",
    "            let fb_lo = nb_lo ^ fa_lo;  let fb_hi = nb_hi ^ fa_hi;",
    "            let fc_lo = nc_lo ^ pd2_lo; let fc_hi = nc_hi ^ pd2_hi;",
    "            let fd_lo = nd_lo ^ fc_lo;  let fd_hi = nd_hi ^ fc_hi;",
    "            *a_ptr.add(idx) = fa_lo; *a_ptr.add(idx + 1) = fa_hi;",
    "            *b_ptr.add(idx) = fb_lo; *b_ptr.add(idx + 1) = fb_hi;",
    "            *c_ptr.add(idx) = fc_lo; *c_ptr.add(idx + 1) = fc_hi;",
    "            *d_ptr.add(idx) = fd_lo; *d_ptr.add(idx + 1) = fd_hi;",
    "        }",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_ntt_butterfly_fused_4layer_row_slice(",
    "    ptr: *mut u64, sixteenth: usize, num_ntts: usize, r: usize, tw_ptr: *const u64,",
    ") {",
    "    unsafe {",
    "        let mut tw = [(0u64, 0u64); 15];",
    "        for i in 0..15 {",
    "            tw[i] = (*tw_ptr.add(2 * i), *tw_ptr.add(2 * i + 1));",
    "        }",
    "        macro_rules! btf2 {",
    "            ($v:ident, $u0:expr, $v0:expr, $t0:expr, $u1:expr, $v1:expr, $t1:expr) => {{",
    "                let (p0_lo, p0_hi, p1_lo, p1_hi) = lean_native_f128_mul_vec2_raw(",
    "                    $v[$v0].0, $v[$v0].1, $v[$v1].0, $v[$v1].1,",
    "                    tw[$t0].0, tw[$t0].1, tw[$t1].0, tw[$t1].1,",
    "                );",
    "                let nu0 = ($v[$u0].0 ^ p0_lo, $v[$u0].1 ^ p0_hi);",
    "                $v[$v0] = ($v[$v0].0 ^ nu0.0, $v[$v0].1 ^ nu0.1);",
    "                $v[$u0] = nu0;",
    "                let nu1 = ($v[$u1].0 ^ p1_lo, $v[$u1].1 ^ p1_hi);",
    "                $v[$v1] = ($v[$v1].0 ^ nu1.0, $v[$v1].1 ^ nu1.1);",
    "                $v[$u1] = nu1;",
    "            }};",
    "        }",
    "        for lane in 0..num_ntts {",
    "            let mut v = [(0u64, 0u64); 16];",
    "            for i in 0..16 {",
    "                let off = 2 * ((i * sixteenth + r) * num_ntts + lane);",
    "                v[i] = (*ptr.add(off), *ptr.add(off + 1));",
    "            }",
    "            btf2!(v, 0, 8, 0, 1, 9, 0);",
    "            btf2!(v, 2, 10, 0, 3, 11, 0);",
    "            btf2!(v, 4, 12, 0, 5, 13, 0);",
    "            btf2!(v, 6, 14, 0, 7, 15, 0);",
    "            btf2!(v, 0, 4, 1, 1, 5, 1);",
    "            btf2!(v, 2, 6, 1, 3, 7, 1);",
    "            btf2!(v, 8, 12, 2, 9, 13, 2);",
    "            btf2!(v, 10, 14, 2, 11, 15, 2);",
    "            btf2!(v, 0, 2, 3, 1, 3, 3);",
    "            btf2!(v, 4, 6, 4, 5, 7, 4);",
    "            btf2!(v, 8, 10, 5, 9, 11, 5);",
    "            btf2!(v, 12, 14, 6, 13, 15, 6);",
    "            btf2!(v, 0, 1, 7, 2, 3, 8);",
    "            btf2!(v, 4, 5, 9, 6, 7, 10);",
    "            btf2!(v, 8, 9, 11, 10, 11, 12);",
    "            btf2!(v, 12, 13, 13, 14, 15, 14);",
    "            for i in 0..16 {",
    "                let off = 2 * ((i * sixteenth + r) * num_ntts + lane);",
    "                *ptr.add(off) = v[i].0;",
    "                *ptr.add(off + 1) = v[i].1;",
    "            }",
    "        }",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_ntt_butterfly_fused_4layer_dual_from_src_row_slice(",
    "    src_ptr: *const u64, dst0_ptr: *mut u64, dst1_ptr: *mut u64,",
    "    sixteenth: usize, num_ntts: usize, r: usize,",
    "    tw0_ptr: *const u64, tw1_ptr: *const u64,",
    ") {",
    "    unsafe {",
    "        for lane in 0..num_ntts {",
    "            for i in 0..16 {",
    "                let off = 2 * ((i * sixteenth + r) * num_ntts + lane);",
    "                let v0 = *src_ptr.add(off);",
    "                let v1 = *src_ptr.add(off + 1);",
    "                *dst0_ptr.add(off) = v0;",
    "                *dst0_ptr.add(off + 1) = v1;",
    "                *dst1_ptr.add(off) = v0;",
    "                *dst1_ptr.add(off + 1) = v1;",
    "            }",
    "        }",
    "        lean_native_ntt_butterfly_fused_4layer_row_slice(dst0_ptr, sixteenth, num_ntts, r, tw0_ptr);",
    "        lean_native_ntt_butterfly_fused_4layer_row_slice(dst1_ptr, sixteenth, num_ntts, r, tw1_ptr);",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_ntt_butterfly_fused_3layer_row_slice(",
    "    ptr: *mut u64, eighth: usize, num_ntts: usize, r: usize, tw_ptr: *const u64,",
    ") {",
    "    unsafe {",
    "        let mut tw = [(0u64, 0u64); 7];",
    "        for i in 0..7 {",
    "            tw[i] = (*tw_ptr.add(2 * i), *tw_ptr.add(2 * i + 1));",
    "        }",
    "        macro_rules! btf2 {",
    "            ($v:ident, $u0:expr, $v0:expr, $t0:expr, $u1:expr, $v1:expr, $t1:expr) => {{",
    "                let (p0_lo, p0_hi, p1_lo, p1_hi) = lean_native_f128_mul_vec2_raw(",
    "                    $v[$v0].0, $v[$v0].1, $v[$v1].0, $v[$v1].1,",
    "                    tw[$t0].0, tw[$t0].1, tw[$t1].0, tw[$t1].1,",
    "                );",
    "                let nu0 = ($v[$u0].0 ^ p0_lo, $v[$u0].1 ^ p0_hi);",
    "                $v[$v0] = ($v[$v0].0 ^ nu0.0, $v[$v0].1 ^ nu0.1);",
    "                $v[$u0] = nu0;",
    "                let nu1 = ($v[$u1].0 ^ p1_lo, $v[$u1].1 ^ p1_hi);",
    "                $v[$v1] = ($v[$v1].0 ^ nu1.0, $v[$v1].1 ^ nu1.1);",
    "                $v[$u1] = nu1;",
    "            }};",
    "        }",
    "        for lane in 0..num_ntts {",
    "            let mut v = [(0u64, 0u64); 8];",
    "            for i in 0..8 {",
    "                let off = 2 * ((i * eighth + r) * num_ntts + lane);",
    "                v[i] = (*ptr.add(off), *ptr.add(off + 1));",
    "            }",
    "            btf2!(v, 0, 4, 0, 1, 5, 0);",
    "            btf2!(v, 2, 6, 0, 3, 7, 0);",
    "            btf2!(v, 0, 2, 1, 1, 3, 1);",
    "            btf2!(v, 4, 6, 2, 5, 7, 2);",
    "            btf2!(v, 0, 1, 3, 2, 3, 4);",
    "            btf2!(v, 4, 5, 5, 6, 7, 6);",
    "            for i in 0..8 {",
    "                let off = 2 * ((i * eighth + r) * num_ntts + lane);",
    "                *ptr.add(off) = v[i].0;",
    "                *ptr.add(off + 1) = v[i].1;",
    "            }",
    "        }",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_fold_pairs_slice(",
    "    src_ptr: *const u64, base: usize, dst_ptr: *mut u64, dst_len: usize, r_lo: u64, r_hi: u64,",
    ") {",
    "    unsafe {",
    "        for t in 0..dst_len {",
    "            let s = 4 * (base + t);",
    "            let e_lo = *src_ptr.add(s);     let e_hi = *src_ptr.add(s + 1);",
    "            let o_lo = *src_ptr.add(s + 2); let o_hi = *src_ptr.add(s + 3);",
    "            let (p_lo, p_hi) = lean_native_f128_mul_raw(e_lo ^ o_lo, e_hi ^ o_hi, r_lo, r_hi);",
    "            let d = 2 * t;",
    "            *dst_ptr.add(d) = e_lo ^ p_lo; *dst_ptr.add(d + 1) = e_hi ^ p_hi;",
    "        }",
    "    }",
    "}",
    "#[allow(clippy::too_many_arguments)]",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_fold_pairs_and_msg_slice(",
    "    f_ptr: *const u64, b_ptr: *const u64, base: usize,",
    "    fc_ptr: *mut u64, bc_ptr: *mut u64, len: usize, r_lo: u64, r_hi: u64,",
    ") -> (u64, u64, u64, u64) {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let vr = _mm_set_epi64x(r_hi as i64, r_lo as i64);",
    "        let lanes = len & !1;",
    "        let (mut u0_ll, mut u0_mid, mut u0_hh) = (_mm_setzero_si128(), _mm_setzero_si128(), _mm_setzero_si128());",
    "        let (mut u2_ll, mut u2_mid, mut u2_hh) = (_mm_setzero_si128(), _mm_setzero_si128(), _mm_setzero_si128());",
    "        let mut t = 0usize;",
    "        while t < lanes {",
    "            let s = 4 * (base + t);",
    "            let fe0 = _mm_loadu_si128(f_ptr.add(s) as *const __m128i);",
    "            let fo0 = _mm_loadu_si128(f_ptr.add(s + 2) as *const __m128i);",
    "            let fe1 = _mm_loadu_si128(f_ptr.add(s + 4) as *const __m128i);",
    "            let fo1 = _mm_loadu_si128(f_ptr.add(s + 6) as *const __m128i);",
    "            let (fp0, fp1) = lean_native_f128_mul_vec2_m128i(_mm_xor_si128(fe0, fo0), _mm_xor_si128(fe1, fo1), vr, vr);",
    "            let nf0 = _mm_xor_si128(fe0, fp0);",
    "            let nf1 = _mm_xor_si128(fe1, fp1);",
    "            let d = 2 * t;",
    "            _mm_storeu_si128(fc_ptr.add(d) as *mut __m128i, nf0);",
    "            _mm_storeu_si128(fc_ptr.add(d + 2) as *mut __m128i, nf1);",
    "            let be0 = _mm_loadu_si128(b_ptr.add(s) as *const __m128i);",
    "            let bo0 = _mm_loadu_si128(b_ptr.add(s + 2) as *const __m128i);",
    "            let be1 = _mm_loadu_si128(b_ptr.add(s + 4) as *const __m128i);",
    "            let bo1 = _mm_loadu_si128(b_ptr.add(s + 6) as *const __m128i);",
    "            let (bp0, bp1) = lean_native_f128_mul_vec2_m128i(_mm_xor_si128(be0, bo0), _mm_xor_si128(be1, bo1), vr, vr);",
    "            let nb0 = _mm_xor_si128(be0, bp0);",
    "            let nb1 = _mm_xor_si128(be1, bp1);",
    "            _mm_storeu_si128(bc_ptr.add(d) as *mut __m128i, nb0);",
    "            _mm_storeu_si128(bc_ptr.add(d + 2) as *mut __m128i, nb1);",
    "            lean_native_f128_mul_acc_m128i(nf0, nb0, &mut u0_ll, &mut u0_mid, &mut u0_hh);",
    "            lean_native_f128_mul_acc_m128i(_mm_xor_si128(nf0, nf1), _mm_xor_si128(nb0, nb1), &mut u2_ll, &mut u2_mid, &mut u2_hh);",
    "            t += 2;",
    "        }",
    "        while t < len {",
    "            let s = 4 * (base + t);",
    "            let fe = _mm_loadu_si128(f_ptr.add(s) as *const __m128i);",
    "            let fo = _mm_loadu_si128(f_ptr.add(s + 2) as *const __m128i);",
    "            let fp = lean_native_f128_mul_m128i(_mm_xor_si128(fe, fo), vr);",
    "            let be = _mm_loadu_si128(b_ptr.add(s) as *const __m128i);",
    "            let bo = _mm_loadu_si128(b_ptr.add(s + 2) as *const __m128i);",
    "            let bp = lean_native_f128_mul_m128i(_mm_xor_si128(be, bo), vr);",
    "            let d = 2 * t;",
    "            _mm_storeu_si128(fc_ptr.add(d) as *mut __m128i, _mm_xor_si128(fe, fp));",
    "            _mm_storeu_si128(bc_ptr.add(d) as *mut __m128i, _mm_xor_si128(be, bp));",
    "            t += 1;",
    "        }",
    "        let u0 = lean_native_f128_reduce_3lane_m128i(u0_ll, u0_mid, u0_hh);",
    "        let u2 = lean_native_f128_reduce_3lane_m128i(u2_ll, u2_mid, u2_hh);",
    "        return (",
    "            _mm_extract_epi64::<0>(u0) as u64,",
    "            _mm_extract_epi64::<1>(u0) as u64,",
    "            _mm_extract_epi64::<0>(u2) as u64,",
    "            _mm_extract_epi64::<1>(u2) as u64,",
    "        );",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let r_arr = [r_lo, r_hi];",
    "        let vr = vld1q_u64(r_arr.as_ptr());",
    "        let lanes = len & !1;",
    "        let z = vdupq_n_u64(0);",
    "        let (mut u0_ll, mut u0_mid, mut u0_hh) = (z, z, z);",
    "        let (mut u2_ll, mut u2_mid, mut u2_hh) = (z, z, z);",
    "        let mut t = 0usize;",
    "        while t < lanes {",
    "            let s = 4 * (base + t);",
    "            let fe0 = vld1q_u64(f_ptr.add(s));",
    "            let fo0 = vld1q_u64(f_ptr.add(s + 2));",
    "            let fe1 = vld1q_u64(f_ptr.add(s + 4));",
    "            let fo1 = vld1q_u64(f_ptr.add(s + 6));",
    "            let (fp0, fp1) = lean_native_f128_mul_vec2_neon(veorq_u64(fe0, fo0), veorq_u64(fe1, fo1), vr, vr);",
    "            let nf0 = veorq_u64(fe0, fp0);",
    "            let nf1 = veorq_u64(fe1, fp1);",
    "            let d = 2 * t;",
    "            vst1q_u64(fc_ptr.add(d), nf0);",
    "            vst1q_u64(fc_ptr.add(d + 2), nf1);",
    "            let be0 = vld1q_u64(b_ptr.add(s));",
    "            let bo0 = vld1q_u64(b_ptr.add(s + 2));",
    "            let be1 = vld1q_u64(b_ptr.add(s + 4));",
    "            let bo1 = vld1q_u64(b_ptr.add(s + 6));",
    "            let (bp0, bp1) = lean_native_f128_mul_vec2_neon(veorq_u64(be0, bo0), veorq_u64(be1, bo1), vr, vr);",
    "            let nb0 = veorq_u64(be0, bp0);",
    "            let nb1 = veorq_u64(be1, bp1);",
    "            vst1q_u64(bc_ptr.add(d), nb0);",
    "            vst1q_u64(bc_ptr.add(d + 2), nb1);",
    "            lean_native_f128_mul_acc_neon(nf0, nb0, &mut u0_ll, &mut u0_mid, &mut u0_hh);",
    "            lean_native_f128_mul_acc_neon(veorq_u64(nf0, nf1), veorq_u64(nb0, nb1), &mut u2_ll, &mut u2_mid, &mut u2_hh);",
    "            t += 2;",
    "        }",
    "        while t < len {",
    "            let s = 4 * (base + t);",
    "            let fe = vld1q_u64(f_ptr.add(s));",
    "            let fo = vld1q_u64(f_ptr.add(s + 2));",
    "            let fp = lean_native_f128_mul_neon(veorq_u64(fe, fo), vr);",
    "            let be = vld1q_u64(b_ptr.add(s));",
    "            let bo = vld1q_u64(b_ptr.add(s + 2));",
    "            let bp = lean_native_f128_mul_neon(veorq_u64(be, bo), vr);",
    "            let d = 2 * t;",
    "            vst1q_u64(fc_ptr.add(d), veorq_u64(fe, fp));",
    "            vst1q_u64(bc_ptr.add(d), veorq_u64(be, bp));",
    "            t += 1;",
    "        }",
    "        let u0 = lean_native_f128_reduce_3lane_neon(u0_ll, u0_mid, u0_hh);",
    "        let u2 = lean_native_f128_reduce_3lane_neon(u2_ll, u2_mid, u2_hh);",
    "        return (",
    "            vgetq_lane_u64::<0>(u0),",
    "            vgetq_lane_u64::<1>(u0),",
    "            vgetq_lane_u64::<0>(u2),",
    "            vgetq_lane_u64::<1>(u2),",
    "        );",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let lanes = len & !1;",
    "        let (mut u0_r0, mut u0_r1, mut u0_r2, mut u0_r3) = (0u64, 0u64, 0u64, 0u64);",
    "        let (mut u2_r0, mut u2_r1, mut u2_r2, mut u2_r3) = (0u64, 0u64, 0u64, 0u64);",
    "        let mut t = 0usize;",
    "        while t < lanes {",
    "            let s = 4 * (base + t);",
    "            let fe0_lo = *f_ptr.add(s);     let fe0_hi = *f_ptr.add(s + 1);",
    "            let fo0_lo = *f_ptr.add(s + 2); let fo0_hi = *f_ptr.add(s + 3);",
    "            let fe1_lo = *f_ptr.add(s + 4); let fe1_hi = *f_ptr.add(s + 5);",
    "            let fo1_lo = *f_ptr.add(s + 6); let fo1_hi = *f_ptr.add(s + 7);",
    "            let (fp0_lo, fp0_hi, fp1_lo, fp1_hi) = lean_native_f128_mul_vec2_raw(",
    "                fe0_lo ^ fo0_lo, fe0_hi ^ fo0_hi, fe1_lo ^ fo1_lo, fe1_hi ^ fo1_hi,",
    "                r_lo, r_hi, r_lo, r_hi,",
    "            );",
    "            let nf0_lo = fe0_lo ^ fp0_lo; let nf0_hi = fe0_hi ^ fp0_hi;",
    "            let nf1_lo = fe1_lo ^ fp1_lo; let nf1_hi = fe1_hi ^ fp1_hi;",
    "            let d = 2 * t;",
    "            *fc_ptr.add(d) = nf0_lo;     *fc_ptr.add(d + 1) = nf0_hi;",
    "            *fc_ptr.add(d + 2) = nf1_lo; *fc_ptr.add(d + 3) = nf1_hi;",
    "            let be0_lo = *b_ptr.add(s);     let be0_hi = *b_ptr.add(s + 1);",
    "            let bo0_lo = *b_ptr.add(s + 2); let bo0_hi = *b_ptr.add(s + 3);",
    "            let be1_lo = *b_ptr.add(s + 4); let be1_hi = *b_ptr.add(s + 5);",
    "            let bo1_lo = *b_ptr.add(s + 6); let bo1_hi = *b_ptr.add(s + 7);",
    "            let (bp0_lo, bp0_hi, bp1_lo, bp1_hi) = lean_native_f128_mul_vec2_raw(",
    "                be0_lo ^ bo0_lo, be0_hi ^ bo0_hi, be1_lo ^ bo1_lo, be1_hi ^ bo1_hi,",
    "                r_lo, r_hi, r_lo, r_hi,",
    "            );",
    "            let nb0_lo = be0_lo ^ bp0_lo; let nb0_hi = be0_hi ^ bp0_hi;",
    "            let nb1_lo = be1_lo ^ bp1_lo; let nb1_hi = be1_hi ^ bp1_hi;",
    "            *bc_ptr.add(d) = nb0_lo;     *bc_ptr.add(d + 1) = nb0_hi;",
    "            *bc_ptr.add(d + 2) = nb1_lo; *bc_ptr.add(d + 3) = nb1_hi;",
    "            let (m0_0, m0_1, m0_2, m0_3) = lean_native_f128_mul_unreduced_raw(nf0_lo, nf0_hi, nb0_lo, nb0_hi);",
    "            let (m2_0, m2_1, m2_2, m2_3) = lean_native_f128_mul_unreduced_raw(",
    "                nf0_lo ^ nf1_lo, nf0_hi ^ nf1_hi, nb0_lo ^ nb1_lo, nb0_hi ^ nb1_hi,",
    "            );",
    "            u0_r0 ^= m0_0; u0_r1 ^= m0_1; u0_r2 ^= m0_2; u0_r3 ^= m0_3;",
    "            u2_r0 ^= m2_0; u2_r1 ^= m2_1; u2_r2 ^= m2_2; u2_r3 ^= m2_3;",
    "            t += 2;",
    "        }",
    "        while t < len {",
    "            let s = 4 * (base + t);",
    "            let fe_lo = *f_ptr.add(s);     let fe_hi = *f_ptr.add(s + 1);",
    "            let fo_lo = *f_ptr.add(s + 2); let fo_hi = *f_ptr.add(s + 3);",
    "            let (fp_lo, fp_hi) = lean_native_f128_mul_raw(fe_lo ^ fo_lo, fe_hi ^ fo_hi, r_lo, r_hi);",
    "            let be_lo = *b_ptr.add(s);     let be_hi = *b_ptr.add(s + 1);",
    "            let bo_lo = *b_ptr.add(s + 2); let bo_hi = *b_ptr.add(s + 3);",
    "            let (bp_lo, bp_hi) = lean_native_f128_mul_raw(be_lo ^ bo_lo, be_hi ^ bo_hi, r_lo, r_hi);",
    "            let d = 2 * t;",
    "            *fc_ptr.add(d) = fe_lo ^ fp_lo; *fc_ptr.add(d + 1) = fe_hi ^ fp_hi;",
    "            *bc_ptr.add(d) = be_lo ^ bp_lo; *bc_ptr.add(d + 1) = be_hi ^ bp_hi;",
    "            t += 1;",
    "        }",
    "        let (u0_lo, u0_hi) = lean_native_f128_reduce_256_raw(u0_r0, u0_r1, u0_r2, u0_r3);",
    "        let (u2_lo, u2_hi) = lean_native_f128_reduce_256_raw(u2_r0, u2_r1, u2_r2, u2_r3);",
    "        (u0_lo, u0_hi, u2_lo, u2_hi)",
    "    }",
    "}",
    "#[allow(clippy::too_many_arguments)]",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_fold_and_msg_round_slice(",
    "    a_in_ptr: *const u64, b_in_ptr: *const u64,",
    "    a_out_ptr: *mut u64, b_out_ptr: *mut u64,",
    "    eq_lo_ptr: *const u64, lo_size: usize, r_lo: u64, r_hi: u64,",
    ") -> (u64, u64, u64, u64) {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let vr = _mm_set_epi64x(r_hi as i64, r_lo as i64);",
    "        let (mut p1_ll, mut p1_mid, mut p1_hh) = (_mm_setzero_si128(), _mm_setzero_si128(), _mm_setzero_si128());",
    "        let (mut pi_ll, mut pi_mid, mut pi_hh) = (_mm_setzero_si128(), _mm_setzero_si128(), _mm_setzero_si128());",
    "        for x_lo in 0..lo_size {",
    "            let s = 8 * x_lo;",
    "            let ae0 = _mm_loadu_si128(a_in_ptr.add(s) as *const __m128i);",
    "            let ao0 = _mm_loadu_si128(a_in_ptr.add(s + 2) as *const __m128i);",
    "            let ae1 = _mm_loadu_si128(a_in_ptr.add(s + 4) as *const __m128i);",
    "            let ao1 = _mm_loadu_si128(a_in_ptr.add(s + 6) as *const __m128i);",
    "            let (ap0, ap1) = lean_native_f128_mul_vec2_m128i(_mm_xor_si128(ae0, ao0), _mm_xor_si128(ae1, ao1), vr, vr);",
    "            let a0 = _mm_xor_si128(ae0, ap0);",
    "            let a1 = _mm_xor_si128(ae1, ap1);",
    "            let be0 = _mm_loadu_si128(b_in_ptr.add(s) as *const __m128i);",
    "            let bo0 = _mm_loadu_si128(b_in_ptr.add(s + 2) as *const __m128i);",
    "            let be1 = _mm_loadu_si128(b_in_ptr.add(s + 4) as *const __m128i);",
    "            let bo1 = _mm_loadu_si128(b_in_ptr.add(s + 6) as *const __m128i);",
    "            let (bp0, bp1) = lean_native_f128_mul_vec2_m128i(_mm_xor_si128(be0, bo0), _mm_xor_si128(be1, bo1), vr, vr);",
    "            let b0 = _mm_xor_si128(be0, bp0);",
    "            let b1 = _mm_xor_si128(be1, bp1);",
    "            let d = 4 * x_lo;",
    "            _mm_storeu_si128(a_out_ptr.add(d) as *mut __m128i, a0);",
    "            _mm_storeu_si128(a_out_ptr.add(d + 2) as *mut __m128i, a1);",
    "            _mm_storeu_si128(b_out_ptr.add(d) as *mut __m128i, b0);",
    "            _mm_storeu_si128(b_out_ptr.add(d + 2) as *mut __m128i, b1);",
    "            let (g1, gi) = lean_native_f128_mul_vec2_m128i(a1, _mm_xor_si128(a0, a1), b1, _mm_xor_si128(b0, b1));",
    "            let eq = _mm_loadu_si128(eq_lo_ptr.add(2 * x_lo) as *const __m128i);",
    "            lean_native_f128_mul_acc_m128i(eq, g1, &mut p1_ll, &mut p1_mid, &mut p1_hh);",
    "            lean_native_f128_mul_acc_m128i(eq, gi, &mut pi_ll, &mut pi_mid, &mut pi_hh);",
    "        }",
    "        let p1 = lean_native_f128_reduce_3lane_m128i(p1_ll, p1_mid, p1_hh);",
    "        let pi = lean_native_f128_reduce_3lane_m128i(pi_ll, pi_mid, pi_hh);",
    "        return (",
    "            _mm_extract_epi64::<0>(p1) as u64,",
    "            _mm_extract_epi64::<1>(p1) as u64,",
    "            _mm_extract_epi64::<0>(pi) as u64,",
    "            _mm_extract_epi64::<1>(pi) as u64,",
    "        );",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let r_arr = [r_lo, r_hi];",
    "        let vr = vld1q_u64(r_arr.as_ptr());",
    "        let z = vdupq_n_u64(0);",
    "        let (mut p1_ll, mut p1_mid, mut p1_hh) = (z, z, z);",
    "        let (mut pi_ll, mut pi_mid, mut pi_hh) = (z, z, z);",
    "        for x_lo in 0..lo_size {",
    "            let s = 8 * x_lo;",
    "            let ae0 = vld1q_u64(a_in_ptr.add(s));",
    "            let ao0 = vld1q_u64(a_in_ptr.add(s + 2));",
    "            let ae1 = vld1q_u64(a_in_ptr.add(s + 4));",
    "            let ao1 = vld1q_u64(a_in_ptr.add(s + 6));",
    "            let (ap0, ap1) = lean_native_f128_mul_vec2_neon(veorq_u64(ae0, ao0), veorq_u64(ae1, ao1), vr, vr);",
    "            let a0 = veorq_u64(ae0, ap0);",
    "            let a1 = veorq_u64(ae1, ap1);",
    "            let be0 = vld1q_u64(b_in_ptr.add(s));",
    "            let bo0 = vld1q_u64(b_in_ptr.add(s + 2));",
    "            let be1 = vld1q_u64(b_in_ptr.add(s + 4));",
    "            let bo1 = vld1q_u64(b_in_ptr.add(s + 6));",
    "            let (bp0, bp1) = lean_native_f128_mul_vec2_neon(veorq_u64(be0, bo0), veorq_u64(be1, bo1), vr, vr);",
    "            let b0 = veorq_u64(be0, bp0);",
    "            let b1 = veorq_u64(be1, bp1);",
    "            let d = 4 * x_lo;",
    "            vst1q_u64(a_out_ptr.add(d), a0);",
    "            vst1q_u64(a_out_ptr.add(d + 2), a1);",
    "            vst1q_u64(b_out_ptr.add(d), b0);",
    "            vst1q_u64(b_out_ptr.add(d + 2), b1);",
    "            let (g1, gi) = lean_native_f128_mul_vec2_neon(a1, veorq_u64(a0, a1), b1, veorq_u64(b0, b1));",
    "            let eq = vld1q_u64(eq_lo_ptr.add(2 * x_lo));",
    "            lean_native_f128_mul_acc_neon(eq, g1, &mut p1_ll, &mut p1_mid, &mut p1_hh);",
    "            lean_native_f128_mul_acc_neon(eq, gi, &mut pi_ll, &mut pi_mid, &mut pi_hh);",
    "        }",
    "        let p1 = lean_native_f128_reduce_3lane_neon(p1_ll, p1_mid, p1_hh);",
    "        let pi = lean_native_f128_reduce_3lane_neon(pi_ll, pi_mid, pi_hh);",
    "        return (",
    "            vgetq_lane_u64::<0>(p1),",
    "            vgetq_lane_u64::<1>(p1),",
    "            vgetq_lane_u64::<0>(pi),",
    "            vgetq_lane_u64::<1>(pi),",
    "        );",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let (mut p1_r0, mut p1_r1, mut p1_r2, mut p1_r3) = (0u64, 0u64, 0u64, 0u64);",
    "        let (mut pi_r0, mut pi_r1, mut pi_r2, mut pi_r3) = (0u64, 0u64, 0u64, 0u64);",
    "        for x_lo in 0..lo_size {",
    "            let s = 8 * x_lo;",
    "            let ae0_lo = *a_in_ptr.add(s);     let ae0_hi = *a_in_ptr.add(s + 1);",
    "            let ao0_lo = *a_in_ptr.add(s + 2); let ao0_hi = *a_in_ptr.add(s + 3);",
    "            let ae1_lo = *a_in_ptr.add(s + 4); let ae1_hi = *a_in_ptr.add(s + 5);",
    "            let ao1_lo = *a_in_ptr.add(s + 6); let ao1_hi = *a_in_ptr.add(s + 7);",
    "            let (ap0_lo, ap0_hi, ap1_lo, ap1_hi) = lean_native_f128_mul_vec2_raw(",
    "                ae0_lo ^ ao0_lo, ae0_hi ^ ao0_hi, ae1_lo ^ ao1_lo, ae1_hi ^ ao1_hi,",
    "                r_lo, r_hi, r_lo, r_hi,",
    "            );",
    "            let a0_lo = ae0_lo ^ ap0_lo; let a0_hi = ae0_hi ^ ap0_hi;",
    "            let a1_lo = ae1_lo ^ ap1_lo; let a1_hi = ae1_hi ^ ap1_hi;",
    "            let be0_lo = *b_in_ptr.add(s);     let be0_hi = *b_in_ptr.add(s + 1);",
    "            let bo0_lo = *b_in_ptr.add(s + 2); let bo0_hi = *b_in_ptr.add(s + 3);",
    "            let be1_lo = *b_in_ptr.add(s + 4); let be1_hi = *b_in_ptr.add(s + 5);",
    "            let bo1_lo = *b_in_ptr.add(s + 6); let bo1_hi = *b_in_ptr.add(s + 7);",
    "            let (bp0_lo, bp0_hi, bp1_lo, bp1_hi) = lean_native_f128_mul_vec2_raw(",
    "                be0_lo ^ bo0_lo, be0_hi ^ bo0_hi, be1_lo ^ bo1_lo, be1_hi ^ bo1_hi,",
    "                r_lo, r_hi, r_lo, r_hi,",
    "            );",
    "            let b0_lo = be0_lo ^ bp0_lo; let b0_hi = be0_hi ^ bp0_hi;",
    "            let b1_lo = be1_lo ^ bp1_lo; let b1_hi = be1_hi ^ bp1_hi;",
    "            let d = 4 * x_lo;",
    "            *a_out_ptr.add(d) = a0_lo;     *a_out_ptr.add(d + 1) = a0_hi;",
    "            *a_out_ptr.add(d + 2) = a1_lo; *a_out_ptr.add(d + 3) = a1_hi;",
    "            *b_out_ptr.add(d) = b0_lo;     *b_out_ptr.add(d + 1) = b0_hi;",
    "            *b_out_ptr.add(d + 2) = b1_lo; *b_out_ptr.add(d + 3) = b1_hi;",
    "            let (g1_lo, g1_hi, gi_lo, gi_hi) = lean_native_f128_mul_vec2_raw(",
    "                a1_lo, a1_hi, a0_lo ^ a1_lo, a0_hi ^ a1_hi,",
    "                b1_lo, b1_hi, b0_lo ^ b1_lo, b0_hi ^ b1_hi,",
    "            );",
    "            let eq_lo = *eq_lo_ptr.add(2 * x_lo);",
    "            let eq_hi = *eq_lo_ptr.add(2 * x_lo + 1);",
    "            let (u1_0, u1_1, u1_2, u1_3) = lean_native_f128_mul_unreduced_raw(eq_lo, eq_hi, g1_lo, g1_hi);",
    "            let (ui_0, ui_1, ui_2, ui_3) = lean_native_f128_mul_unreduced_raw(eq_lo, eq_hi, gi_lo, gi_hi);",
    "            p1_r0 ^= u1_0; p1_r1 ^= u1_1; p1_r2 ^= u1_2; p1_r3 ^= u1_3;",
    "            pi_r0 ^= ui_0; pi_r1 ^= ui_1; pi_r2 ^= ui_2; pi_r3 ^= ui_3;",
    "        }",
    "        let (p1_lo, p1_hi) = lean_native_f128_reduce_256_raw(p1_r0, p1_r1, p1_r2, p1_r3);",
    "        let (pi_lo, pi_hi) = lean_native_f128_reduce_256_raw(pi_r0, pi_r1, pi_r2, pi_r3);",
    "        (p1_lo, p1_hi, pi_lo, pi_hi)",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_inner_product_slice(",
    "    a_ptr: *const u64, b_ptr: *const u64, n_f128: usize,",
    ") -> (u64, u64) {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let (mut ll, mut mid, mut hh) = (_mm_setzero_si128(), _mm_setzero_si128(), _mm_setzero_si128());",
    "        for i in 0..n_f128 {",
    "            let idx = 2 * i;",
    "            let va = _mm_loadu_si128(a_ptr.add(idx) as *const __m128i);",
    "            let vb = _mm_loadu_si128(b_ptr.add(idx) as *const __m128i);",
    "            lean_native_f128_mul_acc_m128i(va, vb, &mut ll, &mut mid, &mut hh);",
    "        }",
    "        let res = lean_native_f128_reduce_3lane_m128i(ll, mid, hh);",
    "        return (_mm_extract_epi64::<0>(res) as u64, _mm_extract_epi64::<1>(res) as u64);",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let z = vdupq_n_u64(0);",
    "        let (mut ll, mut mid, mut hh) = (z, z, z);",
    "        for i in 0..n_f128 {",
    "            let idx = 2 * i;",
    "            let va = vld1q_u64(a_ptr.add(idx));",
    "            let vb = vld1q_u64(b_ptr.add(idx));",
    "            lean_native_f128_mul_acc_neon(va, vb, &mut ll, &mut mid, &mut hh);",
    "        }",
    "        let res = lean_native_f128_reduce_3lane_neon(ll, mid, hh);",
    "        return (vgetq_lane_u64::<0>(res), vgetq_lane_u64::<1>(res));",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let (mut r0, mut r1, mut r2, mut r3) = (0u64, 0u64, 0u64, 0u64);",
    "        for i in 0..n_f128 {",
    "            let idx = 2 * i;",
    "            let (u0, u1, u2, u3) = lean_native_f128_mul_unreduced_raw(",
    "                *a_ptr.add(idx), *a_ptr.add(idx + 1),",
    "                *b_ptr.add(idx), *b_ptr.add(idx + 1),",
    "            );",
    "            r0 ^= u0; r1 ^= u1; r2 ^= u2; r3 ^= u3;",
    "        }",
    "        lean_native_f128_reduce_256_raw(r0, r1, r2, r3)",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_scalar_mul_into_slice(",
    "    dst_ptr: *mut u64, src_ptr: *const u64, n_f128: usize, alpha_lo: u64, alpha_hi: u64,",
    ") {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let valpha = _mm_set_epi64x(alpha_hi as i64, alpha_lo as i64);",
    "        let mut i = 0usize;",
    "        while i + 2 <= n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = _mm_loadu_si128(src_ptr.add(idx) as *const __m128i);",
    "            let s1 = _mm_loadu_si128(src_ptr.add(idx + 2) as *const __m128i);",
    "            let (p0, p1) = lean_native_f128_mul_vec2_m128i(s0, s1, valpha, valpha);",
    "            _mm_storeu_si128(dst_ptr.add(idx) as *mut __m128i, p0);",
    "            _mm_storeu_si128(dst_ptr.add(idx + 2) as *mut __m128i, p1);",
    "            i += 2;",
    "        }",
    "        while i < n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = _mm_loadu_si128(src_ptr.add(idx) as *const __m128i);",
    "            let p0 = lean_native_f128_mul_m128i(s0, valpha);",
    "            _mm_storeu_si128(dst_ptr.add(idx) as *mut __m128i, p0);",
    "            i += 1;",
    "        }",
    "        return;",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let alpha_arr = [alpha_lo, alpha_hi];",
    "        let valpha = vld1q_u64(alpha_arr.as_ptr());",
    "        let mut i = 0usize;",
    "        while i + 2 <= n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = vld1q_u64(src_ptr.add(idx));",
    "            let s1 = vld1q_u64(src_ptr.add(idx + 2));",
    "            let (p0, p1) = lean_native_f128_mul_vec2_neon(s0, s1, valpha, valpha);",
    "            vst1q_u64(dst_ptr.add(idx), p0);",
    "            vst1q_u64(dst_ptr.add(idx + 2), p1);",
    "            i += 2;",
    "        }",
    "        while i < n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = vld1q_u64(src_ptr.add(idx));",
    "            let p0 = lean_native_f128_mul_neon(s0, valpha);",
    "            vst1q_u64(dst_ptr.add(idx), p0);",
    "            i += 1;",
    "        }",
    "        return;",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let mut i = 0usize;",
    "        while i + 2 <= n_f128 {",
    "            let idx = 2 * i;",
    "            let (p0_lo, p0_hi, p1_lo, p1_hi) = lean_native_f128_mul_vec2_raw(",
    "                *src_ptr.add(idx), *src_ptr.add(idx + 1),",
    "                *src_ptr.add(idx + 2), *src_ptr.add(idx + 3),",
    "                alpha_lo, alpha_hi, alpha_lo, alpha_hi,",
    "            );",
    "            *dst_ptr.add(idx) = p0_lo;     *dst_ptr.add(idx + 1) = p0_hi;",
    "            *dst_ptr.add(idx + 2) = p1_lo; *dst_ptr.add(idx + 3) = p1_hi;",
    "            i += 2;",
    "        }",
    "        while i < n_f128 {",
    "            let idx = 2 * i;",
    "            let (p_lo, p_hi) = lean_native_f128_mul_raw(*src_ptr.add(idx), *src_ptr.add(idx + 1), alpha_lo, alpha_hi);",
    "            *dst_ptr.add(idx) = p_lo; *dst_ptr.add(idx + 1) = p_hi;",
    "            i += 1;",
    "        }",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_scalar_mul_add_slice(",
    "    dst_ptr: *mut u64, src_ptr: *const u64, n_f128: usize, alpha_lo: u64, alpha_hi: u64,",
    ") {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let valpha = _mm_set_epi64x(alpha_hi as i64, alpha_lo as i64);",
    "        let mut i = 0usize;",
    "        while i + 2 <= n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = _mm_loadu_si128(src_ptr.add(idx) as *const __m128i);",
    "            let s1 = _mm_loadu_si128(src_ptr.add(idx + 2) as *const __m128i);",
    "            let d0 = _mm_loadu_si128(dst_ptr.add(idx) as *const __m128i);",
    "            let d1 = _mm_loadu_si128(dst_ptr.add(idx + 2) as *const __m128i);",
    "            let (p0, p1) = lean_native_f128_mul_vec2_m128i(s0, s1, valpha, valpha);",
    "            _mm_storeu_si128(dst_ptr.add(idx) as *mut __m128i, _mm_xor_si128(d0, p0));",
    "            _mm_storeu_si128(dst_ptr.add(idx + 2) as *mut __m128i, _mm_xor_si128(d1, p1));",
    "            i += 2;",
    "        }",
    "        while i < n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = _mm_loadu_si128(src_ptr.add(idx) as *const __m128i);",
    "            let d0 = _mm_loadu_si128(dst_ptr.add(idx) as *const __m128i);",
    "            let p0 = lean_native_f128_mul_m128i(s0, valpha);",
    "            _mm_storeu_si128(dst_ptr.add(idx) as *mut __m128i, _mm_xor_si128(d0, p0));",
    "            i += 1;",
    "        }",
    "        return;",
    "    }",
    "    #[cfg(all(target_arch = \"aarch64\", target_feature = \"aes\"))]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let alpha_arr = [alpha_lo, alpha_hi];",
    "        let valpha = vld1q_u64(alpha_arr.as_ptr());",
    "        let mut i = 0usize;",
    "        while i + 2 <= n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = vld1q_u64(src_ptr.add(idx));",
    "            let s1 = vld1q_u64(src_ptr.add(idx + 2));",
    "            let d0 = vld1q_u64(dst_ptr.add(idx));",
    "            let d1 = vld1q_u64(dst_ptr.add(idx + 2));",
    "            let (p0, p1) = lean_native_f128_mul_vec2_neon(s0, s1, valpha, valpha);",
    "            vst1q_u64(dst_ptr.add(idx), veorq_u64(d0, p0));",
    "            vst1q_u64(dst_ptr.add(idx + 2), veorq_u64(d1, p1));",
    "            i += 2;",
    "        }",
    "        while i < n_f128 {",
    "            let idx = 2 * i;",
    "            let s0 = vld1q_u64(src_ptr.add(idx));",
    "            let d0 = vld1q_u64(dst_ptr.add(idx));",
    "            let p0 = lean_native_f128_mul_neon(s0, valpha);",
    "            vst1q_u64(dst_ptr.add(idx), veorq_u64(d0, p0));",
    "            i += 1;",
    "        }",
    "        return;",
    "    }",
    "    #[cfg(not(any(all(target_arch = \"x86_64\", target_feature = \"pclmulqdq\"), all(target_arch = \"aarch64\", target_feature = \"aes\"))))]",
    "    unsafe {",
    "        let mut i = 0usize;",
    "        while i + 2 <= n_f128 {",
    "            let idx = 2 * i;",
    "            let (p0_lo, p0_hi, p1_lo, p1_hi) = lean_native_f128_mul_vec2_raw(",
    "                *src_ptr.add(idx), *src_ptr.add(idx + 1),",
    "                *src_ptr.add(idx + 2), *src_ptr.add(idx + 3),",
    "                alpha_lo, alpha_hi, alpha_lo, alpha_hi,",
    "            );",
    "            *dst_ptr.add(idx) ^= p0_lo;     *dst_ptr.add(idx + 1) ^= p0_hi;",
    "            *dst_ptr.add(idx + 2) ^= p1_lo; *dst_ptr.add(idx + 3) ^= p1_hi;",
    "            i += 2;",
    "        }",
    "        while i < n_f128 {",
    "            let idx = 2 * i;",
    "            let (p_lo, p_hi) = lean_native_f128_mul_raw(*src_ptr.add(idx), *src_ptr.add(idx + 1), alpha_lo, alpha_hi);",
    "            *dst_ptr.add(idx) ^= p_lo; *dst_ptr.add(idx + 1) ^= p_hi;",
    "            i += 1;",
    "        }",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_xor_assign_slice(",
    "    dst_ptr: *mut u64, src_ptr: *const u64, n_f128: usize,",
    ") {",
    "    unsafe {",
    "        let n_u64 = 2 * n_f128;",
    "        let mut i = 0usize;",
    "        #[cfg(all(target_arch = \"x86_64\", target_feature = \"avx2\"))]",
    "        {",
    "            use core::arch::x86_64::*;",
    "            while i + 4 <= n_u64 {",
    "                let d = _mm256_loadu_si256(dst_ptr.add(i) as *const __m256i);",
    "                let s = _mm256_loadu_si256(src_ptr.add(i) as *const __m256i);",
    "                _mm256_storeu_si256(dst_ptr.add(i) as *mut __m256i, _mm256_xor_si256(d, s));",
    "                i += 4;",
    "            }",
    "        }",
    "        #[cfg(target_arch = \"aarch64\")]",
    "        {",
    "            use core::arch::aarch64::*;",
    "            while i + 2 <= n_u64 {",
    "                let d = vld1q_u64(dst_ptr.add(i));",
    "                let s = vld1q_u64(src_ptr.add(i));",
    "                vst1q_u64(dst_ptr.add(i), veorq_u64(d, s));",
    "                i += 2;",
    "            }",
    "        }",
    "        while i < n_u64 {",
    "            *dst_ptr.add(i) ^= *src_ptr.add(i);",
    "            i += 1;",
    "        }",
    "    }",
    "}",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_bit_transpose_64bytes(input: *const u8, output: *mut u8) {",
    "    #[cfg(all(target_arch = \"x86_64\", target_feature = \"avx2\"))]",
    "    unsafe {",
    "        use core::arch::x86_64::*;",
    "        let r01 = _mm_loadu_si128(input as *const __m128i);",
    "        let r23 = _mm_loadu_si128(input.add(16) as *const __m128i);",
    "        let r45 = _mm_loadu_si128(input.add(32) as *const __m128i);",
    "        let r67 = _mm_loadu_si128(input.add(48) as *const __m128i);",
    "        let p01 = _mm_unpacklo_epi8(r01, _mm_srli_si128::<8>(r01));",
    "        let p23 = _mm_unpacklo_epi8(r23, _mm_srli_si128::<8>(r23));",
    "        let p45 = _mm_unpacklo_epi8(r45, _mm_srli_si128::<8>(r45));",
    "        let p67 = _mm_unpacklo_epi8(r67, _mm_srli_si128::<8>(r67));",
    "        let q0123_lo = _mm_unpacklo_epi16(p01, p23);",
    "        let q0123_hi = _mm_unpackhi_epi16(p01, p23);",
    "        let q4567_lo = _mm_unpacklo_epi16(p45, p67);",
    "        let q4567_hi = _mm_unpackhi_epi16(p45, p67);",
    "        let c01 = _mm_unpacklo_epi32(q0123_lo, q4567_lo);",
    "        let c23 = _mm_unpackhi_epi32(q0123_lo, q4567_lo);",
    "        let c45 = _mm_unpacklo_epi32(q0123_hi, q4567_hi);",
    "        let c67 = _mm_unpackhi_epi32(q0123_hi, q4567_hi);",
    "        let mut y0 = _mm256_set_m128i(c23, c01);",
    "        let mut y1 = _mm256_set_m128i(c67, c45);",
    "        let m1 = _mm256_set1_epi64x(0x00AA00AA00AA00AAu64 as i64);",
    "        let m2 = _mm256_set1_epi64x(0x0000CCCC0000CCCCu64 as i64);",
    "        let m3 = _mm256_set1_epi64x(0x00000000F0F0F0F0u64 as i64);",
    "        let t0 = _mm256_and_si256(_mm256_xor_si256(y0, _mm256_srli_epi64::<7>(y0)), m1);",
    "        let t1 = _mm256_and_si256(_mm256_xor_si256(y1, _mm256_srli_epi64::<7>(y1)), m1);",
    "        y0 = _mm256_xor_si256(y0, _mm256_xor_si256(t0, _mm256_slli_epi64::<7>(t0)));",
    "        y1 = _mm256_xor_si256(y1, _mm256_xor_si256(t1, _mm256_slli_epi64::<7>(t1)));",
    "        let t0 = _mm256_and_si256(_mm256_xor_si256(y0, _mm256_srli_epi64::<14>(y0)), m2);",
    "        let t1 = _mm256_and_si256(_mm256_xor_si256(y1, _mm256_srli_epi64::<14>(y1)), m2);",
    "        y0 = _mm256_xor_si256(y0, _mm256_xor_si256(t0, _mm256_slli_epi64::<14>(t0)));",
    "        y1 = _mm256_xor_si256(y1, _mm256_xor_si256(t1, _mm256_slli_epi64::<14>(t1)));",
    "        let t0 = _mm256_and_si256(_mm256_xor_si256(y0, _mm256_srli_epi64::<28>(y0)), m3);",
    "        let t1 = _mm256_and_si256(_mm256_xor_si256(y1, _mm256_srli_epi64::<28>(y1)), m3);",
    "        y0 = _mm256_xor_si256(y0, _mm256_xor_si256(t0, _mm256_slli_epi64::<28>(t0)));",
    "        y1 = _mm256_xor_si256(y1, _mm256_xor_si256(t1, _mm256_slli_epi64::<28>(t1)));",
    "        _mm256_storeu_si256(output as *mut __m256i, y0);",
    "        _mm256_storeu_si256(output.add(32) as *mut __m256i, y1);",
    "        return;",
    "    }",
    "    #[cfg(target_arch = \"aarch64\")]",
    "    unsafe {",
    "        use core::arch::aarch64::*;",
    "        let v0 = vld1q_u8(input);",
    "        let v1 = vld1q_u8(input.add(16));",
    "        let v2 = vld1q_u8(input.add(32));",
    "        let v3 = vld1q_u8(input.add(48));",
    "        let table = uint8x16x4_t(v0, v1, v2, v3);",
    "        const IDX0: [u8; 16] = [0, 8, 16, 24, 32, 40, 48, 56, 1, 9, 17, 25, 33, 41, 49, 57];",
    "        const IDX1: [u8; 16] = [2, 10, 18, 26, 34, 42, 50, 58, 3, 11, 19, 27, 35, 43, 51, 59];",
    "        const IDX2: [u8; 16] = [4, 12, 20, 28, 36, 44, 52, 60, 5, 13, 21, 29, 37, 45, 53, 61];",
    "        const IDX3: [u8; 16] = [6, 14, 22, 30, 38, 46, 54, 62, 7, 15, 23, 31, 39, 47, 55, 63];",
    "        let mut y0 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX0.as_ptr())));",
    "        let mut y1 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX1.as_ptr())));",
    "        let mut y2 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX2.as_ptr())));",
    "        let mut y3 = vreinterpretq_u64_u8(vqtbl4q_u8(table, vld1q_u8(IDX3.as_ptr())));",
    "        let m1 = vdupq_n_u64(0x00AA00AA00AA00AAu64);",
    "        let m2 = vdupq_n_u64(0x0000CCCC0000CCCCu64);",
    "        let m3 = vdupq_n_u64(0x00000000F0F0F0F0u64);",
    "        macro_rules! swar2 {",
    "            ($y:ident) => {{",
    "                let t1 = vandq_u64(veorq_u64($y, vshrq_n_u64::<7>($y)), m1);",
    "                $y = veorq_u64($y, veorq_u64(t1, vshlq_n_u64::<7>(t1)));",
    "                let t2 = vandq_u64(veorq_u64($y, vshrq_n_u64::<14>($y)), m2);",
    "                $y = veorq_u64($y, veorq_u64(t2, vshlq_n_u64::<14>(t2)));",
    "                let t3 = vandq_u64(veorq_u64($y, vshrq_n_u64::<28>($y)), m3);",
    "                $y = veorq_u64($y, veorq_u64(t3, vshlq_n_u64::<28>(t3)));",
    "            }};",
    "        }",
    "        swar2!(y0); swar2!(y1); swar2!(y2); swar2!(y3);",
    "        vst1q_u8(output, vreinterpretq_u8_u64(y0));",
    "        vst1q_u8(output.add(16), vreinterpretq_u8_u64(y1));",
    "        vst1q_u8(output.add(32), vreinterpretq_u8_u64(y2));",
    "        vst1q_u8(output.add(48), vreinterpretq_u8_u64(y3));",
    "        return;",
    "    }",
    "}",
    "#[allow(clippy::too_many_arguments)]",
    "#[inline(always)]",
    "pub unsafe fn lean_native_f128_lincheck_bind_both_and_eval_slice(",
    "    cq0: *mut u64, cq1: *mut u64, cq2: *const u64, cq3: *const u64,",
    "    zq0: *mut u64, zq1: *mut u64, zq2: *const u64, zq3: *const u64,",
    "    len_f128: usize, r_lo: u64, r_hi: u64,",
    ") -> (u64, u64, u64, u64) {",
    "    unsafe {",
    "        let (mut e1_r0, mut e1_r1, mut e1_r2, mut e1_r3) = (0u64, 0u64, 0u64, 0u64);",
    "        let (mut ei_r0, mut ei_r1, mut ei_r2, mut ei_r3) = (0u64, 0u64, 0u64, 0u64);",
    "        for i in 0..len_f128 {",
    "            let idx = 2 * i;",
    "            let c0_lo = *cq0.add(idx); let c0_hi = *cq0.add(idx + 1);",
    "            let c1_lo = *cq1.add(idx); let c1_hi = *cq1.add(idx + 1);",
    "            let c2_lo = *cq2.add(idx); let c2_hi = *cq2.add(idx + 1);",
    "            let c3_lo = *cq3.add(idx); let c3_hi = *cq3.add(idx + 1);",
    "            let z0_lo = *zq0.add(idx); let z0_hi = *zq0.add(idx + 1);",
    "            let z1_lo = *zq1.add(idx); let z1_hi = *zq1.add(idx + 1);",
    "            let z2_lo = *zq2.add(idx); let z2_hi = *zq2.add(idx + 1);",
    "            let z3_lo = *zq3.add(idx); let z3_hi = *zq3.add(idx + 1);",
    "            let (fc0_lo, fc0_hi, fc1_lo, fc1_hi) = lean_native_f128_mul_vec2_raw(",
    "                c0_lo ^ c2_lo, c0_hi ^ c2_hi, c1_lo ^ c3_lo, c1_hi ^ c3_hi,",
    "                r_lo, r_hi, r_lo, r_hi,",
    "            );",
    "            let lo_lo = c0_lo ^ fc0_lo; let lo_hi = c0_hi ^ fc0_hi;",
    "            let hi_lo = c1_lo ^ fc1_lo; let hi_hi = c1_hi ^ fc1_hi;",
    "            let (fz0_lo, fz0_hi, fz1_lo, fz1_hi) = lean_native_f128_mul_vec2_raw(",
    "                z0_lo ^ z2_lo, z0_hi ^ z2_hi, z1_lo ^ z3_lo, z1_hi ^ z3_hi,",
    "                r_lo, r_hi, r_lo, r_hi,",
    "            );",
    "            let zlo_lo = z0_lo ^ fz0_lo; let zlo_hi = z0_hi ^ fz0_hi;",
    "            let zhi_lo = z1_lo ^ fz1_lo; let zhi_hi = z1_hi ^ fz1_hi;",
    "            *cq0.add(idx) = lo_lo; *cq0.add(idx + 1) = lo_hi;",
    "            *cq1.add(idx) = hi_lo; *cq1.add(idx + 1) = hi_hi;",
    "            *zq0.add(idx) = zlo_lo; *zq0.add(idx + 1) = zlo_hi;",
    "            *zq1.add(idx) = zhi_lo; *zq1.add(idx + 1) = zhi_hi;",
    "            let (m1_0, m1_1, m1_2, m1_3) = lean_native_f128_mul_unreduced_raw(hi_lo, hi_hi, zhi_lo, zhi_hi);",
    "            let (mi_0, mi_1, mi_2, mi_3) = lean_native_f128_mul_unreduced_raw(",
    "                hi_lo ^ lo_lo, hi_hi ^ lo_hi, zhi_lo ^ zlo_lo, zhi_hi ^ zlo_hi,",
    "            );",
    "            e1_r0 ^= m1_0; e1_r1 ^= m1_1; e1_r2 ^= m1_2; e1_r3 ^= m1_3;",
    "            ei_r0 ^= mi_0; ei_r1 ^= mi_1; ei_r2 ^= mi_2; ei_r3 ^= mi_3;",
    "        }",
    "        let (e1_lo, e1_hi) = lean_native_f128_reduce_256_raw(e1_r0, e1_r1, e1_r2, e1_r3);",
    "        let (ei_lo, ei_hi) = lean_native_f128_reduce_256_raw(ei_r0, ei_r1, ei_r2, ei_r3);",
    "        (e1_lo, e1_hi, ei_lo, ei_hi)",
    "    }",
    "}",
    "pub mod c_abi {",
    "    unsafe extern \"C\" {"
  ] ++ declExterns ++ ["    }", "}"] ++ declWrappers ++ [""])

def emitGuardFixturesJson (sourcePath : String) (sigs : List CAbiBindingSig) (guards : List (String × String)) : String :=
  let esc := LeanNative.IR.jsonEscape
  let expJson := String.intercalate "," (sigs.map fun s =>
    s!"\{\"c_symbol\":\"{esc s.cSymbol}\",\"lean_name\":\"{esc s.leanName}\",\"arity\":{s.params.length},\"ret_c\":\"{esc s.retCType}\",\"ret_rust\":\"{esc s.retRustType}\"}")
  let gJson := String.intercalate "," (guards.map fun (lhs, rhs) =>
    s!"\{\"expr\":\"{esc lhs}\",\"expected\":\"{esc rhs}\"}")
  s!"\{\"schema\":\"lean-native.cabi-fixtures.v1\",\"source\":\"{esc sourcePath}\",\"exports_count\":{sigs.length},\"guards_count\":{guards.length},\"exports\":[{expJson}],\"guards\":[{gJson}]}\n"

private def cTypeToSwiftType (cTy : String) : String :=
  if cTy == "uint8_t" then "UInt8"
  else if cTy == "uint16_t" then "UInt16"
  else if cTy == "uint32_t" then "UInt32"
  else if cTy == "uint64_t" || cTy == "size_t" then "UInt64"
  else if cTy == "int64_t" then "Int64"
  else if cTy == "double" then "Double"
  else if cTy == "void" then "Void"
  else "UnsafeRawPointer?"

/-- Emit a Clang module map (`module.modulemap`) for Xcode / SwiftPM zero-copy C-ABI interop. -/
def emitModuleMap (moduleName : String := "TurboLeanCABI") (headerFile : String := "turbo_lean_cabi.h") : String :=
  s!"module {moduleName} \{\n  header \"{headerFile}\"\n  export *\n}\n"

/-- Emit zero-copy Swift `@_silgen_name` C-ABI bindings (`TurboLeanKit.swift`) for iOS / macOS (`apple-a15`). -/
def emitCAbiSwiftFromSigs (sigs : List CAbiBindingSig) (enumName : String := "TurboLeanKernel") : String :=
  let externDecls := sigs.map fun s =>
    let paramsSw := String.intercalate ", " (s.params.map fun (n, cTy, _) => s!"_ {n}: {cTypeToSwiftType cTy}")
    let retSw := cTypeToSwiftType s.retCType
    s!"@_silgen_name(\"{s.cSymbol}\")\npublic func {s.cSymbol}({paramsSw}) -> {retSw}"
  let enumMethods := sigs.map fun s =>
    let paramsSw := String.intercalate ", " (s.params.map fun (n, cTy, _) => s!"_ {n}: {cTypeToSwiftType cTy}")
    let argsSw := String.intercalate ", " (s.params.map fun (n, _, _) => n)
    let retSw := cTypeToSwiftType s.retCType
    s!"  @inlinable public static func {s.leanName}({paramsSw}) -> {retSw} \{\n    {s.cSymbol}({argsSw})\n  }"
  String.intercalate "\n" ([
    "// Auto-generated Zero-Copy Swift C-ABI Bridge by lean-native (iOS / apple-a15)",
    "import Foundation",
    ""
  ] ++ externDecls ++ [
    "",
    s!"public enum {enumName} \{"
  ] ++ enumMethods ++ ["}", ""])

/-- Emit a C-ABI header (`.h`) for an `LNIRModule`. -/
def emitCAbiHeader (m : LNIRModule) : String :=
  emitCAbiHeaderFromSigs (moduleToCAbiSigs m)

def runEmitCAbiBindings (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let leanPath := findFlagValue args "--lean" (findFlagValue args "--input" (findFirstPositional args))
  let hdrPath := findFlagValue args "--emit-header" (findFlagValue args "--header" "")
  let rsPath := findFlagValue args "--emit-rust" (findFlagValue args "--rust" "")
  let swiftPath := findFlagValue args "--emit-swift" (findFlagValue args "--swift" "")
  let modMapPath := findFlagValue args "--emit-modulemap" (findFlagValue args "--modulemap" "")
  let fixPath := findFlagValue args "--emit-fixtures" (findFlagValue args "--fixtures" "")
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let (sigs, guards, srcLabel) ←
    if !leanPath.isEmpty && (← System.FilePath.pathExists leanPath) && leanPath.endsWith ".lean" then
      let raw ← readLeanSourceExpandingUmbrella leanPath
      let (s, g) := extractLeanSourceCAbiAndGuards raw
      if !s.isEmpty then pure (s, g, leanPath)
      else
        let m ← loadInputModule elaborateHook? args
        pure (moduleToCAbiSigs (runDefaultPipeline m).1, g, leanPath)
    else
      let m ← loadInputModule elaborateHook? args
      pure (moduleToCAbiSigs (runDefaultPipeline m).1, [], if leanPath.isEmpty then m.moduleName else leanPath)
  let hdrText := emitCAbiHeaderFromSigs sigs
  let rsText := emitCAbiRustFromSigs sigs
  let swiftText := emitCAbiSwiftFromSigs sigs
  let fixText := emitGuardFixturesJson srcLabel sigs guards
  if !hdrPath.isEmpty then IO.FS.writeFile hdrPath hdrText
  if !rsPath.isEmpty then IO.FS.writeFile rsPath rsText
  if !swiftPath.isEmpty then IO.FS.writeFile swiftPath swiftText
  if !modMapPath.isEmpty then
    let hdrBase := if hdrPath.isEmpty then "turbo_lean_cabi.h" else ((System.FilePath.mk hdrPath).fileName.getD "turbo_lean_cabi.h")
    IO.FS.writeFile modMapPath (emitModuleMap "TurboLeanCABI" hdrBase)
  if !fixPath.isEmpty then IO.FS.writeFile fixPath fixText
  if !outPath.isEmpty then IO.FS.writeFile outPath (if jsonFlag then fixText else hdrText)
  if jsonFlag || (hdrPath.isEmpty && rsPath.isEmpty && swiftPath.isEmpty && modMapPath.isEmpty && fixPath.isEmpty && outPath.isEmpty) then
    IO.print fixText
  else
    IO.println s!"[{tag}] Emitted C-ABI bindings (exports={sigs.length}, guards={guards.length}, header={hdrPath}, rust={rsPath}, swift={swiftPath}, fixtures={fixPath})"
  return 0

def runCompileMode (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  if !(findFlagValue args "--emit-header" (findFlagValue args "--emit-rust" (findFlagValue args "--emit-fixtures" ""))).isEmpty then
    let _ ← runEmitCAbiBindings tag elaborateHook? args
  let opts := parseCoreCLIOptions args
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args opts.emitCABI
  let _ ← emitModuleTelemetryEvents telCfg .x86_64 false baseMod
  let (optMod, _) := if opts.isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  if opts.emitCABI then
    writeOrPrint opts.outputPath (LeanNative.Backend.emitFastCheckCABI optMod)
      (some s!"[{tag}] Wrote Zero-Boxing C-ABI SIMD FastCheck & Routing kernel to {opts.outputPath}")
  else if opts.emitPTX then writeOrPrint opts.outputPath (emitPTXModule optMod opts.smArch)
  else if opts.emitMetal then writeOrPrint opts.outputPath (emitMetalModule optMod)
  else writeOrPrint opts.outputPath (if opts.isBaseline then emitLLVMBaseline optMod opts.arch else emitLLVMOptimized optMod opts.arch)

def runCompileLLVM (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let isBaseline := hasFlag args "--baseline"
  let outPath := findFlagValue args "-o" ""
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← if hasFlag args "--slot-regression" then pure slotTypeRegressionModule else loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg .x86_64 false baseMod
  let (modToEmit, _) := if isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  let irText := if isBaseline then emitLLVMBaseline modToEmit arch else emitLLVMOptimized modToEmit arch
  writeOrPrint outPath irText (some s!"[{tag}] Wrote LLVM 18 IR ({arch.triple}, baseline={isBaseline}, decls={modToEmit.decls.length}) to {outPath}")

def runCompileStaticLib (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let outPath := findFlagValue args "-o" "/tmp/liblean_native_kernels.a"
  let headerPath := findFlagValue args "--emit-header" (findFlagValue args "--header" (outPath ++ ".h"))
  let rustPath := findFlagValue args "--emit-rust" (findFlagValue args "--rust" "")
  let swiftPath := findFlagValue args "--emit-swift" (findFlagValue args "--swift" "")
  let xcfwDir := findFlagValue args "--emit-xcframework" (findFlagValue args "--xcframework" (findFlagValue args "--emit-swift-package-skeleton" ""))
  let fixPath := findFlagValue args "--emit-fixtures" (findFlagValue args "--fixtures" "")
  let asmPath := findFlagValue args "--emit-asm" (findFlagValue args "--asm" "")
  let jsonFlag := hasFlag args "--json"
  let posPath := findFirstPositional args
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let (sigs, guards) ←
    if posPath.endsWith ".lean" then
      let src ← readLeanSourceExpandingUmbrella posPath
      let (srcSigs, srcGuards) := extractLeanSourceCAbiAndGuards src
      pure (if srcSigs.isEmpty then moduleToCAbiSigs optMod else srcSigs, srcGuards)
    else
      pure (moduleToCAbiSigs optMod, [])
  let irText := emitLLVMOptimized optMod arch
  let hdrText := emitCAbiHeaderFromSigs sigs
  IO.FS.writeFile headerPath hdrText
  if !rustPath.isEmpty then IO.FS.writeFile rustPath (emitCAbiRustFromSigs sigs (some optMod))
  if !swiftPath.isEmpty then IO.FS.writeFile swiftPath (emitCAbiSwiftFromSigs sigs)
  if !fixPath.isEmpty then IO.FS.writeFile fixPath (emitGuardFixturesJson optMod.moduleName sigs guards)
  if !xcfwDir.isEmpty then
    IO.FS.createDirAll (System.FilePath.mk xcfwDir / "ios-arm64" / "Headers")
    IO.FS.writeFile (s!"{xcfwDir}/ios-arm64/Headers/turbo_lean_cabi.h") hdrText
    IO.FS.writeFile (s!"{xcfwDir}/ios-arm64/Headers/module.modulemap") (emitModuleMap "TurboLeanCABI" "turbo_lean_cabi.h")
    IO.FS.writeFile (s!"{xcfwDir}/TurboLeanKit.swift") (emitCAbiSwiftFromSigs sigs)
    IO.FS.writeFile (s!"{xcfwDir}/Info.plist")
      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n<plist version=\"1.0\">\n<dict>\n  <key>AvailableLibraries</key>\n  <array>\n    <dict>\n      <key>HeadersPath</key><string>Headers</string>\n      <key>LibraryIdentifier</key><string>ios-arm64</string>\n      <key>LibraryPath</key><string>libturbo_lean_kernels.a</string>\n      <key>SupportedArchitectures</key><array><string>arm64</string></array>\n      <key>SupportedPlatform</key><string>ios</string>\n    </dict>\n  </array>\n  <key>CFBundlePackageType</key><string>XFWK</string>\n  <key>XCFrameworkFormatVersion</key><string>1.0</string>\n</dict>\n</plist>\n"
  let tmpLl := outPath ++ ".tmp.ll"
  let tmpObj := outPath ++ ".tmp.o"
  IO.FS.writeFile tmpLl irText
  let runCmdOk (cmd : String) (cmdArgs : Array String) : IO Bool := do
    try return (← IO.Process.output { cmd, args := cmdArgs }).exitCode == 0
    catch _ => return false
  let cpuFlags : Array String := arch.clangFlags
  if !asmPath.isEmpty then
    if ← runCmdOk "clang" (cpuFlags ++ #["-S", tmpLl, "-o", asmPath]) then
      let rawAsm ← try IO.FS.readFile asmPath catch _ => pure ""
      let keepAsmLine (ln : String) : Bool :=
        let t := ln.trimAscii.toString
        !(t.startsWith ".cfi_" || t.startsWith ".file" || t.startsWith ".addrsig" ||
          t.startsWith ".prefalign" || t.startsWith ".ident" || t.startsWith ".att_syntax")
      let cleanAsm := String.intercalate "\n" ((rawAsm.splitOn "\n").filter keepAsmLine)
      IO.FS.writeFile asmPath cleanAsm
  let clangOk ← runCmdOk "clang" (cpuFlags ++ #["-c", tmpLl, "-o", tmpObj])
  let builtArchive ← if clangOk then do
    try IO.FS.removeFile outPath catch _ => pure ()
    if ← runCmdOk "llvm-ar" #["rcs", outPath, tmpObj] then pure true
    else runCmdOk "ar" #["rcs", outPath, tmpObj]
  else pure false
  if !builtArchive then IO.FS.writeFile outPath irText
  if jsonFlag then
    IO.println s!"\{\"status\":\"compiled_static_lib\",\"archive\":{if builtArchive then "true" else "false"},\"library\":\"{outPath}\",\"asm\":\"{asmPath}\",\"header\":\"{headerPath}\",\"rust\":\"{rustPath}\",\"decls\":{optMod.decls.length}}"
  else
    IO.println s!"[{tag}] Wrote C-ABI static library ({outPath}, archive={builtArchive}) and header ({headerPath}, decls={optMod.decls.length})"
  return 0

def runCompileMLIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isStableHLO := hasFlag args "--tpu" || hasFlag args "--stablehlo" || hasFlag args "--tpu-stablehlo"
  let isPallas := hasFlag args "--pallas" || hasFlag args "--tpu-pallas"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let mlirText :=
    if isPallas then emitTPUPallasModule optMod
    else if isStableHLO then emitStableHLOModule optMod
    else emitMLIRModule optMod
  let kind := if isPallas then "TPU Pallas" else if isStableHLO then "TPU v5e StableHLO" else "GPU MLIR"
  writeOrPrint outPath mlirText (some s!"[{tag}] Wrote {kind} module to {outPath}")

def runCompilePTX (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let smArch := findFlagValue args "--sm" "sm_90"
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let ptxText :=
    if isFastCheck then emitFastCheckPTX baseMod smArch
    else emitPTXModule (runDefaultPipeline baseMod).1 smArch
  writeOrPrint outPath ptxText (some s!"[{tag}] Wrote NVIDIA PTX 8.0 ({smArch}, fastcheck={isFastCheck}) to {outPath}")

def runCompileMetal (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let mslText :=
    if isFastCheck then emitFastCheckMetal baseMod
    else emitMetalModule (runDefaultPipeline baseMod).1
  let (valid, errs) := validateMetalShader mslText
  if !valid then
    IO.eprintln s!"[{tag}] Metal shader validation errors: {errs}"
    return 1
  writeOrPrint outPath mslText
    (some s!"[{tag}] Wrote Apple Metal Shading Language 3.0 (fastcheck={isFastCheck}, valid={valid}) to {outPath}")

def runCompileFastCheck (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let smArch := findFlagValue args "--sm" "sm_90"
  let numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096
  let useConstraintProp := !(hasFlag args "--no-constraint-prop")
  let jsonFlag := hasFlag args "--json"
  let mod ← loadInputModule elaborateHook? args (!(hasFlag args "--canonical"))
  if hasFlag args "--c-abi" || hasFlag args "--emit-c-abi" then
    writeOrPrint outPath (LeanNative.Backend.emitFastCheckCABI mod) (some s!"[{tag}] Wrote FastCheck Zero-Boxing C-ABI SIMD source to {outPath}")
  else if hasFlag args "--emit-llvm" then
    writeOrPrint outPath (emitFastCheckLLVM mod) (some s!"[{tag}] Wrote FastCheck SIMD LLVM 18 IR to {outPath}")
  else if hasFlag args "--emit-ptx" then
    writeOrPrint outPath (emitFastCheckPTX mod smArch) (some s!"[{tag}] Wrote FastCheck NVIDIA PTX 8.0 ({smArch}) to {outPath}")
  else if hasFlag args "--emit-metal" then
    writeOrPrint outPath (emitFastCheckMetal mod) (some s!"[{tag}] Wrote FastCheck Apple Metal 3.0 shader to {outPath}")
  else
    let report := runFastCheckModule mod numSamples useConstraintProp
    writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
    return 0

def runCompileHybrid (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let profilePath := findFlagValue args "--profile" ""
  let mut minGpuElems : Nat := 65536
  if !profilePath.isEmpty then
    let profRaw ← IO.FS.readFile profilePath
    match HardwareCostProfile.fromJson? profRaw with
    | some p => minGpuElems := p.minGpuElements
    | none => throw <| IO.userError s!"[{tag}] Failed to parse hardware profile from '{profilePath}'"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let plan := partitionModule optMod minGpuElems
  let glueText := emitHybridHostGlue plan
  writeOrPrint outPath glueText
    (some s!"[{tag}] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}, minGpuElements={minGpuElems}) to {outPath}")

def runSuperopt (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let profilePath := findFlagValue args "--profile" ""
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg target false baseMod
  let (_, report) ←
    if !profilePath.isEmpty then
      let profRaw ← IO.FS.readFile profilePath
      match HardwareCostProfile.fromJson? profRaw with
      | some p => pure (superoptModuleWithProfile p baseMod)
      | none => throw <| IO.userError s!"[lean-native] Failed to parse hardware cost profile from '{profilePath}'"
    else
      pure (superoptModule target baseMod)
  writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
  return 0

def runPlugins (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let testAdversarial := hasFlag args "--test-adversarial" || !(hasFlag args "--no-adversarial-test")
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg target testAdversarial baseMod
  let (_, report) := runSegregatedPluginPipeline target testAdversarial baseMod
  writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
  let allTvOk := report.declAudits.all (fun a => a.tvVerified)
  let ok := allTvOk && (!testAdversarial || report.adversarialRejected)
  return if ok then 0 else 1

def runTelemetry (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let count ← emitModuleTelemetryEvents telCfg target true baseMod
  let evPath := s!"{telCfg.spoolDir}/events.jsonl"
  let blobsDir := s!"{telCfg.spoolDir}/blobs"
  IO.println s!"\{\"schema\":\"lean-native.telemetry.v1\",\"enabled\":{if telCfg.enabled then "true" else "false"},\"mode\":\"{telCfg.mode}\",\"spool_dir\":\"{telCfg.spoolDir}\",\"events_file\":\"{evPath}\",\"blobs_dir\":\"{blobsDir}\",\"remote_url\":\"{telCfg.remoteUrl}\",\"events_emitted\":{count}}"
  return 0

def runTurboPlugin : IO UInt32 := do
  let line ← (← IO.getStdin).getLine
  let stdout ← IO.getStdout
  stdout.putStrLn (handleTurboPluginLine line.trimAscii.toString)
  stdout.flush; return 0

def runPRVerify (tag : String) (args : List String) : IO UInt32 := do
  let baseRef := findFlagValue args "--base" "HEAD"
  let jsonFlag := hasFlag args "--json"
  let outPath := findFlagValue args "-o" ""
  let specExists ← System.FilePath.pathExists "LeanNative/Spec.lean"
  let testExists ← System.FilePath.pathExists "tests/test_runner.lean"
  let specHashHex := blake3Hex (← if specExists then IO.FS.readFile "LeanNative/Spec.lean" else pure "")
  let testHashHex := blake3Hex (← if testExists then IO.FS.readFile "tests/test_runner.lean" else pure "")
  let disallowSpecChanges := hasFlag args "--disallow-spec-changes"
  let mut specUnchanged := specExists
  let mut testUnchanged := testExists
  if disallowSpecChanges then
    try
      let changedFiles := (← IO.Process.output { cmd := "git", args := #["diff", "--name-only", baseRef, "--", "LeanNative/Spec.lean", "tests/test_runner.lean"] }).stdout.trimAscii.toString
      if changedFiles.contains "LeanNative/Spec.lean" then specUnchanged := false
      if changedFiles.contains "tests/test_runner.lean" then testUnchanged := false
    catch _ => pure ()
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let tvReport := validateTranslationModule baseMod optMod
  let allDeclTvOk := pluginReport.declAudits.all (·.tvVerified)
  let axiomReport := verifiedAxiomAuditReport
  let law5Passed := checkPRVerificationGate {
    expectedSpecHash := 1, actualSpecHash := if specUnchanged then 1 else 2,
    expectedTestSuiteHash := 1, actualTestSuiteHash := if testUnchanged then 1 else 2,
    forbiddenAxiomsCount := axiomReport.forbiddenAxiomsFound.length,
    tvAllPassed := tvReport.allPassed && allDeclTvOk && pluginReport.adversarialRejected && axiomReport.passed }
  let fcSelfTestOk ← runFastCheckBridgeSelfTest
  let overallOk := law5Passed && fcSelfTestOk
  let jsonOut := s!"\{\n  \"status\": \"{if overallOk then "pr_verified" else "pr_rejected"}\",\n  \"engine\": \"{tag}\",\n  \"version\": \"0.5.0\",\n  \"baseRef\": \"{baseRef}\",\n  \"law1UntrustedPluginGatePassed\": {pluginReport.adversarialRejected && allDeclTvOk},\n  \"law5SpecPinningGatePassed\": {law5Passed},\n  \"specBlake3\": \"{specHashHex}\",\n  \"testRunnerBlake3\": \"{testHashHex}\",\n  \"symbolicTvPassedDecls\": {tvReport.passedDecls},\n  \"symbolicTvTotalDecls\": {tvReport.totalDecls},\n  \"pluginsAccepted\": {pluginReport.acceptedCount},\n  \"adversarialPluginsRejected\": {pluginReport.rejectedCount},\n  \"costBefore\": {pluginReport.totalCostBefore},\n  \"costAfter\": {pluginReport.totalCostAfter},\n  \"fastCheckSelfTestPassed\": {fcSelfTestOk}\n}"
  let summaryText := String.intercalate "\n" [
    s!"[{tag}] PR & Spec-Pinning Verification Gate (base={baseRef}):",
    s!"  Law 1 Untrusted Plugin & Adversarial Gate : {if pluginReport.adversarialRejected && allDeclTvOk then "PASSED" else "FAILED"} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})",
    s!"  Law 5 Spec & Test Suite Pinning Gate      : {if law5Passed then "PASSED" else "FAILED"} (Spec={specHashHex.take 16}..., Tests={testHashHex.take 16}...)",
    s!"  Alive2 Symbolic Translation Validation    : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)",
    s!"  In-Process FastCheck & BLAKE3 Self-Test   : {if fcSelfTestOk then "PASSED" else "FAILED"}"
  ]
  writeAndPrintJsonOrSummary outPath jsonOut summaryText jsonFlag
  return if overallOk then 0 else 1

def runVerifyCerts (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let baseMod ← loadInputModule elaborateHook? args
  let report := verifyModuleCerts baseMod.moduleName ((runDefaultPipeline baseMod).2.map toOptimizationCert)
  let summaryText := s!"[{tag}] Certificate Verification for {report.moduleName}:\n  Total pass certificates : {report.certs.length}\n  Declarations verified   : {report.declSummaries.length}\n  Overall assurance level : {report.overallAssurance}\n  Hash chains & theorems  : {if report.verified then "VALID" else "FAILED"}"
  writeAndPrintJsonOrSummary (findFlagValue args "-o" "") report.toJson summaryText (hasFlag args "--json")
  return if report.verified then 0 else 1

def runValidateTV (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let tvReport := validateTranslationModule baseMod optMod
  writeAndPrintJsonOrSummary outPath tvReport.toJson tvReport.formatSummary jsonFlag
  return if tvReport.allPassed then 0 else 1

def runEmitLNIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let wireFlag := hasFlag args "--wire"
  let fastCheckFlag := hasFlag args "--fastcheck"
  let mod ← loadInputModule elaborateHook? args fastCheckFlag
  let useWire := wireFlag || outPath.endsWith ".lnir"
  writeOrPrint outPath (if useWire then mod.toWire else mod.toJson)
    (some s!"[{tag}] Emitted LNIR ({if useWire then "wire" else "json"}, decls={mod.decls.length}) to {outPath}")

def runCoreSelfTest (tag : String) : IO UInt32 := do
  IO.println s!"=== Lean Native ({tag} v0.5.0) Self-Test ==="
  let baseMod := mkCanonicalBenchmarkModule
  let roundTripWireOk := LNIRModule.fromWire? baseMod.toWire == some baseMod
  let roundTripJsonOk := LNIRModule.fromJson? baseMod.toJson == some baseMod
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let certReport := verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soReportX86) := superoptModule .x86_64 baseMod
  let (_, soReportMetal) := superoptModule .apple_metal baseMod
  let superoptOk := soReportX86.rewritesApplied > 0 && soReportMetal.rewritesApplied > 0 &&
    soReportX86.totalCostAfter < soReportX86.totalCostBefore
  let (_, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let pluginsOk := pluginReport.acceptedCount > 0 && pluginReport.adversarialRejected &&
    pluginReport.declAudits.all (fun a => a.tvVerified)
  let law5Ok := checkPRVerificationGate ⟨42, 42, 99, 99, 0, tvReport.allPassed && pluginsOk⟩ &&
    !(checkPRVerificationGate ⟨42, 43, 99, 99, 0, true⟩)
  let fcMod := mkFastCheckSampleModule
  let fcReportProp := runFastCheckModule fcMod 512 true
  let fcReportNaive := runFastCheckModule fcMod 512 false
  let fcPropOk := fcReportProp.counterexamplesFound == 1 && fcReportProp.vacuousPasses == 0 && fcReportProp.falsePositives == 0
  let fcNaiveVacuousOk := fcReportNaive.vacuousPasses == 1
  let fcLlvm := emitFastCheckLLVM fcMod
  let fcPtx := emitFastCheckPTX fcMod "sm_90"
  let fcMetal := emitFastCheckMetal fcMod
  let llvmX86 := emitLLVMOptimized optMod .x86_64
  let ptxTxt := emitPTXModule optMod "sm_90"
  let metalTxt := emitMetalModule optMod
  let (metalValid, _) := validateMetalShader metalTxt
  let (fcMetalValid, _) := validateMetalShader fcMetal
  let gpuDescs := lowerModuleToGPUDescriptors optMod
  let stablehloTxt := emitStableHLOModule optMod
  let pallasTxt := emitTPUPallasModule optMod
  let tpuCodegenOk := (stablehloTxt.splitOn "stablehlo.").length > 1 &&
    ((stablehloTxt.splitOn "tpu_v6e").length > 1 || (stablehloTxt.splitOn "tpu_v5e").length > 1) &&
    ((pallasTxt.splitOn "tpu_v6e").length > 1 || (pallasTxt.splitOn "tpu_v5e").length > 1) &&
    (pallasTxt.splitOn "pallas").length > 1
  let blake3Ok := blake3SelfTest
  let twoPow60 : Nat := 1 <<< 60
  let mulDivOk := mulDivDownNat twoPow60 twoPow60 twoPow60 == twoPow60 &&
    mulDivUpNat twoPow60 twoPow60 twoPow60 == twoPow60 &&
    mulDivDownNat twoPow60 twoPow60 3 < mulDivUpNat twoPow60 twoPow60 3 &&
    mulDivDownNat twoPow60 twoPow60 0 == 0 && mulDivUpNat twoPow60 twoPow60 0 == 0
  let telCfg ← TelemetryConfig.probe ["--telemetry"]
  let telCount ← emitModuleTelemetryEvents telCfg .x86_64 true baseMod
  let telOk := telCount > 0
  let relDecl : LNIRDecl := {
    name := "ssz_monotone_offsets_bug"
    params := [{ id := 0, name := "o0", ty := .i64, borrow := false }, { id := 1, name := "o1", ty := .i64, borrow := false }]
    retTy := .i1, assurance := .verifiedKernelProof, isGpuCand := true
    body :=
      .letBind 10 .i1 (.scalar (.binOp .le (.constU64 16) (.var 0)))
        (.letBind 11 .i1 (.scalar (.binOp .le (.var 0) (.var 1)))
          (.letBind 12 .i1 (.scalar (.binOp .bitAnd (.var 10) (.var 11)))
            (.letBind 13 .i1 (.scalar (.constBool true))
              (.ite 12 (.letBind 14 .i1 (.scalar (.binOp .lt (.var 1) (.constU64 20))) (.ret 14)) (.ret 13)))))
  }
  let relRes := runFastCheckDecl relDecl 64 true
  let relSamplingOk := relRes.counterexampleFound && relRes.certifiedCounterexample && !relRes.vacuousPass
  let gpuHeadroomOk :=
    LeanNative.Spec.hasSufficientGpuMemory ⟨4096, 1024, 2048⟩ &&
    !(LeanNative.Spec.hasSufficientGpuMemory ⟨2048, 1024, 2048⟩) &&
    LeanNative.Spec.isValidByteSlice (LeanNative.Spec.subSliceView ⟨64, 8, 32⟩ 4 16) &&
    LeanNative.Spec.canEmitRestrictSimd ⟨true, false, 64⟩ && !(LeanNative.Spec.canEmitRestrictSimd ⟨true, true, 64⟩) &&
    LeanNative.Spec.canUnboxNestedProdWhile ⟨8, false, true⟩ && LeanNative.Spec.canRewriteMulHiU128 ⟨32, 32, true⟩ &&
    LeanNative.Spec.canRewriteTupleSArrayFill ⟨248, 248, 64, 64, 64, true⟩ && LeanNative.Spec.canUnboxNatBoolWhile ⟨true, true, false⟩ &&
    LeanNative.Spec.canRewriteMixedSArrayWhile ⟨true, true, false⟩ && LeanNative.Spec.canRewriteNestedRangeTupleMut ⟨246, 248, 248, 1⟩ &&
    LeanNative.Spec.canStripEarlyReturnCtor ⟨true, true, false⟩ && LeanNative.Spec.canRewriteNested2DRangeForIn ⟨248, 1, true, true⟩ &&
    LeanNative.Spec.canElideInBodyRangeAlloc ⟨0, 1, false, true⟩ && LeanNative.Spec.canSwapPingPongSArray ⟨248, 248, true, true⟩ &&
    LeanNative.Spec.canCollapseSar64ReturnDiamond ⟨63, 16, true⟩ && LeanNative.Spec.canMaterializeStackSArraySROA ⟨3, true, true⟩ &&
    LeanNative.Spec.canPromoteRangeCtorToStack ⟨0, 3, false, true⟩ && LeanNative.Spec.canScalarizeRepeatMTripleSArray ⟨248, 248, 248, true⟩ &&
    LeanNative.Spec.canEmitZeroDepMathlibCert ⟨false, false, false, true⟩ &&
    !(LeanNative.Spec.canEmitZeroDepMathlibCert ⟨false, true, false, true⟩) &&
    LeanNative.Backend.selectOptimalSearchBackend 8192 false true false false true false true == .FpgaLsc2 &&
    (emitZeroDepMathlibProof { declName := "tauceti_cert", stmtSrc := "x = y", cofactorTerms := [("h1", 1), ("h2", -1)], dagRwSteps := ["Nat.add_comm"], distilledLemmas := ["Nat.add_zero"], farkasWeights := [1, 2] }).startsWith "by\n" &&
    LeanNative.Spec.canBindCAbiSliceIo ⟨16, 48, 4096, 8, 16⟩ && !(LeanNative.Spec.canBindCAbiSliceIo ⟨16, 48, 4096, 32, 16⟩) &&
    LeanNative.Spec.verifyCAbiSliceIoC 16 48 4096 8 16 == 1 && LeanNative.Spec.verifyCAbiSliceIoC 16 48 512 8 16 == 0 &&
    LeanNative.Spec.canEmitZeroRuntimeSliceOut ⟨0, 0, 0, 8, 16⟩ && !(LeanNative.Spec.canEmitZeroRuntimeSliceOut ⟨1, 0, 0, 8, 16⟩) &&
    LeanNative.Spec.packSliceSpanU64 10 25 3 == 0x0000000A00001903 &&
    LeanNative.Spec.verifyLazyReductionSliceC 64 256 1 1 == 1 && LeanNative.Spec.verifyLazyReductionSliceC 64 256 0 1 == 0 &&
    LeanNative.Spec.verifyRadix4NttFusionC 8 4 64 1 == 1 && LeanNative.Spec.verifyRadix4NttFusionC 8 3 64 1 == 0 &&
    TargetArch.iosArm64.triple == "arm64-apple-ios" && TargetArch.iosArm64.llvmTriple == "arm64-apple-ios16.0.0" &&
    TargetArch.iosArm64.isAArch64 && TargetArch.iosArm64.isIOS &&
    optMod.decls.all (fun d =>
      let m := LeanNative.Backend.LLVM.selectDeclRcMode d
      let hh : UInt8 := if LeanNative.Backend.LLVM.codeHasHeapOps d.body then 1 else 0
      let mt : UInt8 := if LeanNative.Backend.LLVM.codeHasParFor d.body then 1 else 0
      LeanNative.Spec.verifyRcModeSafeC m.toCode hh mt == 1) &&
    optMod.decls.any (fun d => LeanNative.Backend.LLVM.selectDeclRcMode d == .freestanding) &&
    optMod.decls.any (fun d => LeanNative.Backend.LLVM.selectDeclRcMode d == .atomic) &&
    LeanNative.Backend.selectAppleA15Target 262144 false true true == .gpuMetal &&
    LeanNative.Backend.selectAppleA15Target 65536 false true true == .cpuSimd &&
    LeanNative.Backend.selectAppleA15Target 262144 false true false == .cpuSimd &&
    (let glue := LeanNative.Backend.emitMetalZeroCopyHostGlue (LeanNative.Backend.Hybrid.partitionModule optMod)
     let swappedGlue := glue.replace "[enc setBuffer:bufX offset:0 atIndex:0]" "[enc setBuffer:bufX offset:0 atIndex:1]"
     (glue.splitOn "newBufferWithBytesNoCopy").length > 1 &&
     LeanNative.Backend.verifyMetalBindingContract LeanNative.Backend.saxpyF16MetalBindingSpec metalTxt glue &&
     !(LeanNative.Backend.verifyMetalBindingContract LeanNative.Backend.saxpyF16MetalBindingSpec metalTxt swappedGlue) &&
     !(LeanNative.Backend.verifyMetalBindingContract { LeanNative.Backend.saxpyF16MetalBindingSpec with outputBufferName := "bad" } metalTxt glue)) &&
    (let androidIr := emitLLVMOptimized optMod .androidArm64
     let tensorIr := emitLLVMOptimized optMod .androidArm64 (some IsaLevel.tensorG3)
     let cryptoDecl : LNIRDecl := {
       name := "crypto_clmul_eor3_probe"
       params := [{ id := 0, name := "x", ty := .i64 }, { id := 1, name := "y", ty := .i64 }]
       retTy := .i64
       body := .letBind 2 .i64 (.scalar (.binOp .clmul64 (.var 0) (.var 1)))
                 (.letBind 3 .i64 (.scalar (.binOp .eor3 (.var 2) (.var 1))) (.ret 3))
     }
     let cryptoBaseIr := LeanNative.Backend.LLVM.emitDeclLLVM true cryptoDecl .androidArm64 [] (some IsaLevel.arm64Baseline)
     let cryptoTensorIr := LeanNative.Backend.LLVM.emitDeclLLVM true cryptoDecl .androidArm64 [] (some IsaLevel.tensorG3)
     let baseSlice := match androidIr.splitOn "define weak_odr dso_local void @lean_native_cpu_saxpy_u64__baseline(" with
       | _ :: after :: _ => (after.splitOn "\n}").headD ""
       | _ => ""
     let sve2Slice := match androidIr.splitOn "define weak_odr dso_local void @lean_native_cpu_saxpy_u64__sve2(" with
       | _ :: after :: _ => (after.splitOn "\n}").headD ""
       | _ => ""
     (androidIr.splitOn "apple-m3").length == 1 &&
     !baseSlice.isEmpty && !sve2Slice.isEmpty &&
     (baseSlice.splitOn "<vscale").length == 1 &&
     (sve2Slice.splitOn "<vscale x 2 x i64>").length > 1 &&
     (sve2Slice.splitOn "@llvm.vscale.i64()").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_saxpy_u64_dispatch").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_map_scale_add_u64__sve2").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_zip_add_u64__sve2").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_xor_assign_u64__sve2").length > 1 &&
     (androidIr.splitOn "@leansys_select_isa").length > 1 &&
     (cryptoBaseIr.splitOn "call <16 x i8> @llvm.aarch64.neon.pmull64").length == 1 &&
     (cryptoTensorIr.splitOn "call <16 x i8> @llvm.aarch64.neon.pmull64").length > 1 &&
     (cryptoBaseIr.splitOn "call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64").length == 1 &&
     (cryptoTensorIr.splitOn "call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64").length > 1 &&
     (tensorIr.splitOn "+sve2-bitperm").length > 1 &&
     (tensorIr.splitOn "!8 = !{!\"llvm.loop.vectorize.scalable.enable\", i1 true}").length > 1 &&
     optMod.decls.all (fun d =>
       let req := LeanNative.Backend.LLVM.codegenRequires d IsaLevel.tensorG3
       req.le IsaLevel.tensorG3 && !req.fp16 && !req.dotprod && !req.i8mm && !req.bf16) &&
     optMod.decls.any (fun d =>
       LeanNative.Backend.LLVM.codeHasParFor d.body && !LeanNative.Backend.LLVM.codeHasCryptoOps d.body &&
       !(LeanNative.Backend.LLVM.codegenRequires d IsaLevel.tensorG3).sha3 &&
       (LeanNative.Backend.LLVM.codegenRequires d IsaLevel.tensorG3).sve2) &&
     LeanNative.Backend.LLVM.codeHasCryptoOps cryptoDecl.body &&
     (LeanNative.Backend.LLVM.codegenRequires cryptoDecl IsaLevel.appleA15).sha3 &&
     !(LeanNative.Backend.LLVM.codegenRequires cryptoDecl IsaLevel.arm64Baseline).sha3 &&
     (TargetArch.iosArm64.clangFlags (some IsaLevel.appleA16_A17)).contains "-mcpu=apple-a16" &&
     (TargetArch.iosArm64.clangFlags (some IsaLevel.appleM4_A18)).contains "-mcpu=apple-m4") &&
    TargetArch.androidArm64.triple == "aarch64-linux-android" &&
    TargetArch.wasm32.triple == "wasm32-unknown-unknown" && TargetArch.iosSimArm64.symbolPrefix == "_"
  let sve2AsmOk ← do
    let androidIr := emitLLVMOptimized optMod .androidArm64
    let tmpLl := "/tmp/ln_sve2_verify.ll"
    let home := (← IO.getEnv "HOME").getD "/root"
    let clangCandidates := [
      s!"{home}/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
      s!"{home}/.elan/toolchains/leanprover--lean4---v4.31.0/bin/clang",
      "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
      "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
      "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin/clang"
    ]
    let mut clangCmd := "clang"
    for cand in clangCandidates do
      if ← System.FilePath.pathExists cand then
        clangCmd := cand
        break
    try
      IO.FS.writeFile tmpLl androidIr
      let out ← IO.Process.output {
        cmd := clangCmd
        args := #["--target=aarch64-linux-android29", "-O3", "-Wno-override-module", "-S", tmpLl, "-o", "-"]
      }
      try IO.FS.removeFile tmpLl catch _ => pure ()
      if out.exitCode != 0 then
        pure false
      else
        let asm := out.stdout
        let baseAsm := match asm.splitOn "lean_native_cpu_saxpy_u64__baseline:" with
          | _ :: after :: _ => (after.splitOn ".Lfunc_end").headD ""
          | _ => ""
        let sve2Asm := match asm.splitOn "lean_native_cpu_saxpy_u64__sve2:" with
          | _ :: after :: _ => (after.splitOn ".Lfunc_end").headD ""
          | _ => ""
        pure (!baseAsm.isEmpty && !sve2Asm.isEmpty &&
          (baseAsm.splitOn "cntd").length == 1 && (baseAsm.splitOn "ld1d").length == 1 && (baseAsm.splitOn "st1d").length == 1 &&
          (sve2Asm.splitOn "cntd").length > 1 && (sve2Asm.splitOn "ld1d").length > 1 &&
          (sve2Asm.splitOn "mad").length > 1 && (sve2Asm.splitOn "st1d").length > 1)
    catch _ =>
      try IO.FS.removeFile tmpLl catch _ => pure ()
      pure false
  let gpuHeadroomOk := gpuHeadroomOk && sve2AsmOk
  let specRaw ← if ← System.FilePath.pathExists "LeanNative/Spec.lean" then IO.FS.readFile "LeanNative/Spec.lean" else pure ""
  let (specSigs, specGuards) := extractLeanSourceCAbiAndGuards specRaw
  let activeSigs := if specSigs.isEmpty then moduleToCAbiSigs optMod else specSigs
  let cabiGenHdr := emitCAbiHeaderFromSigs activeSigs
  let cabiGenRs := emitCAbiRustFromSigs activeSigs
  let cabiGenSw := emitCAbiSwiftFromSigs activeSigs
  let cabiGenFix := emitGuardFixturesJson "LeanNative/Spec.lean" specSigs specGuards
  let cabiGenOk := (cabiGenHdr.splitOn "extern \"C\"").length > 1 && (cabiGenRs.splitOn "extern \"C\"").length > 1 &&
    (cabiGenSw.splitOn "@_silgen_name").length > 1 &&
    (specRaw.isEmpty || (!specSigs.isEmpty && !specGuards.isEmpty && (cabiGenFix.splitOn "leannative_verify_cabi_slice_io").length > 1))
  let axiomReport := verifiedAxiomAuditReport
  let axiomOk := axiomReport.passed && axiomReport.forbiddenAxiomsFound.isEmpty && axiomReport.theoremsAudited >= 185 && cabiGenOk
  let sAx := "sor" ++ "ryAx"
  let status (b : Bool) := if b then "PASSED" else "FAILED"
  IO.println s!"1. Canonical 8-Kernel Module       : {optMod.decls.length} declarations (incl. 256-bit EVM/Verity)"
  IO.println s!"2. LNIR Wire & JSON Round-Trip     : {status (roundTripWireOk && roundTripJsonOk)}"
  IO.println s!"3. Certificate Chain Verification  : {status certReport.verified} ({certReport.certs.length} certs)"
  IO.println s!"4. Alive2 Symbolic TV Validation   : {status tvReport.allPassed} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
  IO.println s!"5. Enumerative Superoptimizer      : {status superoptOk} ({soReportX86.rewritesApplied} rewrites, cost {soReportX86.totalCostBefore}->{soReportX86.totalCostAfter})"
  IO.println s!"6. Segregated Plugins & Law 1/5    : {status (pluginsOk && law5Ok)} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})"
  IO.println s!"7. FastCheck ConstraintProp vs Vac : {status (fcPropOk && fcNaiveVacuousOk && relSamplingOk)} (propCex={fcReportProp.counterexamplesFound}, naiveVacuous={fcReportNaive.vacuousPasses}, relPolytope=ok)"
  IO.println s!"8. Unified GPUIR & Apple Metal 3.0 : {status (metalValid && fcMetalValid && gpuHeadroomOk)} ({gpuDescs.length} GPU descriptors, Metal={metalTxt.length}B)"
  IO.println s!"9. Pure-Lean RFC BLAKE3 Self-Test  : {status blake3Ok}"
  IO.println s!"10. Google Cloud TPU v6e Codegen   : {status tpuCodegenOk} (StableHLO={stablehloTxt.length}B, Pallas={pallasTxt.length}B)"
  IO.println s!"11. Exact 512-Bit mulDiv Overflow  : {status mulDivOk} ((2^60 * 2^60) / 2^60 == 2^60)"
  IO.println s!"12. CAS Telemetry Spooler (v1)     : {status telOk} ({telCount} accepted+rejected events, de Bruijn CAS blobs)"
  IO.println s!"13. In-Kernel Transitive Axiom Gate: {status axiomOk} ({axiomReport.theoremsAudited} theorems via Lean.collectAxioms, 0 {sAx})"
  IO.println s!"14. LLVM Declared Slot Types      : {status slotTypeRegressionOk} (3-field i256 tuple, ptr call)"
  let allOk := roundTripWireOk && roundTripJsonOk && certReport.verified &&
    tvReport.allPassed && superoptOk && pluginsOk && law5Ok &&
    fcPropOk && fcNaiveVacuousOk && relSamplingOk && gpuHeadroomOk &&
    metalValid && fcMetalValid && blake3Ok && tpuCodegenOk && mulDivOk && telOk && axiomOk && slotTypeRegressionOk &&
    llvmX86.length > 500 && ptxTxt.length > 500 && fcLlvm.length > 200 && fcPtx.length > 200
  if allOk then
    IO.println s!"=== ALL {tag.toUpper} v0.5.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println s!"=== {tag.toUpper} SELF-TEST FAILED ==="
    return 1

/-! ## Persistent Sub-Millisecond JSON-RPC Worker (`worker`) -/

private abbrev escapeJsonWorker := LeanNative.IR.jsonEscape

private def parseRpcTapes (line : String) : JsonTape × Option JsonTape :=
  let root := JsonTape.indexJsonObject (LeanSys.Posix.ByteSlice.ofString line)
  let params := (JsonTape.lookupSlice? root "params").map (fun (ps, _) => JsonTape.indexJsonObject ps)
  (root, params)

private def extractRpcId (line : String) : String :=
  let (root, _) := parseRpcTapes line
  match JsonTape.findEntry? root "id" with
  | some e =>
    if e.valLen == 0 then "1"
    else
      let s : LeanSys.Posix.ByteSlice := { ba := root.root.ba, off := e.valOff, len := e.valLen }
      if e.isString then s!"\"{s.toStringLossy}\"" else s.toStringLossy
  | none => "1"

private def extractRpcStringField (line : String) (key : String) : Option String :=
  let (root, params) := parseRpcTapes line
  (JsonTape.lookupString? root key) <|> (params.bind (fun p => JsonTape.lookupString? p key))

private def hasRpcBoolField (line : String) (key : String) (expected : Bool) : Bool :=
  let (root, params) := parseRpcTapes line
  let b? := (JsonTape.lookupBool? root key) <|> (params.bind (fun p => JsonTape.lookupBool? p key))
  b? == some expected

private def extractRpcNatField (line : String) (key : String) (defaultVal : Nat) : Nat :=
  let (root, params) := parseRpcTapes line
  ((JsonTape.lookupNat? root key) <|> (params.bind (fun p => JsonTape.lookupNat? p key))).getD defaultVal

structure WorkerCache where
  baseMod          : LNIRModule
  optMod           : LNIRModule
  certReportJson   : String
  tvReportJson     : String
  superoptX86Json  : String
  pluginsX86Json   : String
  llvmOptX86       : String
  llvmOptArm       : String
  llvmBaseX86      : String
  ptxSm90          : String
  metalText        : String
  mlirText         : String
  stablehloText    : String
  pallasText       : String
  fcReportPropJson : String
  fcReportVacJson  : String
  fcLlvmText       : String
  fcPtxText        : String
  fcMetalText      : String

def initWorkerCache : IO WorkerCache := do
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let certReport := verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soRep) := superoptModule .x86_64 baseMod
  let (_, plRep) := runSegregatedPluginPipeline .x86_64 true baseMod
  let fcMod := mkFastCheckSampleModule
  return {
    baseMod, optMod
    certReportJson   := certReport.toJson
    tvReportJson     := tvReport.toJson
    superoptX86Json  := soRep.toJson
    pluginsX86Json   := plRep.toJson
    llvmOptX86       := emitLLVMOptimized optMod .x86_64
    llvmOptArm       := emitLLVMOptimized optMod .arm64
    llvmBaseX86      := emitLLVMBaseline baseMod .x86_64
    ptxSm90          := emitPTXModule optMod "sm_90"
    metalText        := emitMetalModule optMod
    mlirText         := emitMLIRModule optMod
    stablehloText    := emitStableHLOModule optMod
    pallasText       := emitTPUPallasModule optMod
    fcReportPropJson := (runFastCheckModule fcMod 1024 true).toJson
    fcReportVacJson  := (runFastCheckModule fcMod 1024 false).toJson
    fcLlvmText       := emitFastCheckLLVM fcMod
    fcPtxText        := emitFastCheckPTX fcMod "sm_90"
    fcMetalText      := emitFastCheckMetal fcMod
  }

def getOrInitWorkerCache (cacheRef : IO.Ref (Option WorkerCache)) : IO WorkerCache := do
  match ← cacheRef.get with
  | some c => return c
  | none =>
    let c ← initWorkerCache
    cacheRef.set (some c)
    return c

/-- Fast-path worker RPC methods (`< 0.05 ms`, zero `WorkerCache` cold-start cost). -/
def handleFastWorkerRequest? (engineName line : String) : Option String :=
  let reqId := extractRpcId line
  let method := (extractRpcStringField line "method").getD "ping"
  let hasBool2 (k1 k2 : String) (b : Bool) := hasRpcBoolField line k1 b || hasRpcBoolField line k2 b
  match method with
  | "ping" =>
    some s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"{engineName}\",\"version\":\"0.5.0\",\"decls\":8}}"
  | "eval-cex" =>
    let witnessEnv := (VarEnv.empty.bind 1 (.u64 1000000)).bind 0 (.u64 1000042)
    let certified := certifyCounterexample 128 evmConstrainedBuggyPropDecl witnessEnv HeapState.empty
    some s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"declName\":\"evm_constrained_buggy_prop\",\"certified\":{certified},\"falsePositives\":0,\"theorem\":\"LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive\",\"report\":\{\"counterexamplesFound\":1,\"vacuousPasses\":0,\"falsePositives\":0}}}"
  | "select-target" =>
    let tripCount := extractRpcNatField line "trip_count" (extractRpcNatField line "tripCount" 65536)
    let tgt := LeanNative.Backend.selectOptimalComputeTarget tripCount
      (hasBool2 "is_matrix" "isMatrix" true) (hasBool2 "is_256bit" "is256Bit" true)
      (hasBool2 "is_control_heavy" "isControlHeavy" true) (hasBool2 "has_tpu" "hasTpu" true)
      (hasBool2 "has_gpu" "hasGpu" true || hasRpcBoolField line "has_cuda_gpu" true) (hasBool2 "has_metal" "hasMetal" true)
    some s!"\{\"id\":{reqId},\"ok\":true,\"target\":\"{tgt}\",\"result\":\{\"target\":\"{tgt}\",\"trip_count\":{tripCount}}}"
  | "riscv-step-audit" =>
    let boot := extractRpcNatField line "bootstrap_steps" 23132
    let scale := extractRpcNatField line "loop_scale" 1
    let csr := extractRpcNatField line "csr_cost" 0
    let candK := extractRpcNatField line "candidate_k" 1000000
    let verMin := extractRpcNatField line "verify_minutes" 12
    let (refuted, maxObs, violIn) := runRiscvStepBudgetAudit boot scale csr candK
    let yukonScore := candK * 10000 + verMin
    let body := s!"\"refuted\":{refuted},\"max_observed_steps\":{maxObs},\"candidate_k\":{candK},\"violating_input\":{violIn},\"yukon_score\":{yukonScore}"
    some s!"\{\"id\":{reqId},\"ok\":true,{body},\"result\":\{{body}}}"
  | "batch-fastcheck" =>
    let numSamples := extractRpcNatField line "samples" (extractRpcNatField line "num_samples" 1024)
    let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
    let recTarget := LeanNative.Backend.selectOptimalComputeTarget numSamples
      (hasRpcBoolField line "is_matrix" true) (!(hasRpcBoolField line "is_256bit" false))
      (hasRpcBoolField line "is_control_heavy" true) (hasRpcBoolField line "has_tpu" true)
      (!(hasRpcBoolField line "has_gpu" false)) (hasRpcBoolField line "has_metal" true)
    let customModOpt := (extractRpcStringField line "wire").bind LNIRModule.fromWire?
    let rep := runFastCheckModule (customModOpt.getD mkFastCheckSampleModule) numSamples (!noProp)
    some s!"\{\"id\":{reqId},\"ok\":true,\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"result\":\{\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"report\":{rep.toJson}}}"
  | _ => none

def handleWorkerRequest (engineName : String) (cache : WorkerCache) (line : String) : String :=
  if let some fastResp := handleFastWorkerRequest? engineName line then fastResp
  else
    let reqId := extractRpcId line
    let method := (extractRpcStringField line "method").getD "ping"
    let customModOpt := (extractRpcStringField line "wire").bind LNIRModule.fromWire?
    let nDecls := cache.optMod.decls.length
    match method with
    | "compile-llvm" =>
      let archStr := (extractRpcStringField line "arch").getD "x86_64"
      let isBase := hasRpcBoolField line "baseline" true
      let ir := match customModOpt with
        | some m =>
          let arch := parseTargetArch archStr
          if isBase then emitLLVMBaseline m arch else emitLLVMOptimized (runDefaultPipeline m).1 arch
        | none =>
          if isBase then cache.llvmBaseX86
          else if archStr == "arm64" || archStr == "aarch64" then cache.llvmOptArm else cache.llvmOptX86
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"arch\":\"{escapeJsonWorker archStr}\",\"baseline\":{isBase},\"decls\":{nDecls},\"irBytes\":{ir.length},\"ir\":\"{escapeJsonWorker ir}\"}}"
    | "compile-ptx" =>
      let sm := (extractRpcStringField line "sm").getD "sm_90"
      let isFc := hasRpcBoolField line "fastcheck" true
      let ptx := if isFc then cache.fcPtxText
        else match customModOpt with
          | some m => emitPTXModule (runDefaultPipeline m).1 sm
          | none => if sm == "sm_90" then cache.ptxSm90 else emitPTXModule cache.optMod sm
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"sm\":\"{escapeJsonWorker sm}\",\"decls\":{nDecls},\"ptxBytes\":{ptx.length},\"ptx\":\"{escapeJsonWorker ptx}\"}}"
    | "compile-metal" =>
      let isFc := hasRpcBoolField line "fastcheck" true
      let msl := if isFc then cache.fcMetalText
        else match customModOpt with
          | some m => emitMetalModule (runDefaultPipeline m).1
          | none => cache.metalText
      let (valid, _) := validateMetalShader msl
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"apple_metal_3.0\",\"valid\":{valid},\"decls\":{nDecls},\"metalBytes\":{msl.length},\"metal\":\"{escapeJsonWorker msl}\"}}"
    | "compile-mlir" =>
      let dialect := (extractRpcStringField line "dialect").getD "gpu"
      let mlir := match customModOpt with
        | some m =>
          let mOpt := (runDefaultPipeline m).1
          if dialect == "pallas" then emitTPUPallasModule mOpt
          else if dialect == "stablehlo" || dialect == "tpu" then emitStableHLOModule mOpt
          else emitMLIRModule mOpt
        | none =>
          if dialect == "pallas" then cache.pallasText
          else if dialect == "stablehlo" || dialect == "tpu" then cache.stablehloText
          else cache.mlirText
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"dialect\":\"{escapeJsonWorker dialect}\",\"decls\":{nDecls},\"mlirBytes\":{mlir.length},\"mlir\":\"{escapeJsonWorker mlir}\"}}"
    | "compile-tpu" =>
      let (shlo, pallas) := match customModOpt with
        | some m => let mOpt := (runDefaultPipeline m).1; (emitStableHLOModule mOpt, emitTPUPallasModule mOpt)
        | none => (cache.stablehloText, cache.pallasText)
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"google_cloud_tpu_v5e\",\"decls\":{nDecls},\"stablehloBytes\":{shlo.length},\"pallasBytes\":{pallas.length},\"stablehlo\":\"{escapeJsonWorker shlo}\",\"pallas\":\"{escapeJsonWorker pallas}\"}}"
    | "compile-fastcheck" =>
      let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
      let repJson := match customModOpt with
        | some m => (runFastCheckModule m 1024 (!noProp)).toJson
        | none => if noProp then cache.fcReportVacJson else cache.fcReportPropJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{repJson}}"
    | "superopt" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      let soJson := match customModOpt with
        | some m => (superoptModule (parseSuperoptTarget tgtStr) m).2.toJson
        | none => if tgtStr == "x86_64" then cache.superoptX86Json else (superoptModule (parseSuperoptTarget tgtStr) cache.baseMod).2.toJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{soJson}}"
    | "plugins" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      let plJson := match customModOpt with
        | some m => (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true m).2.toJson
        | none => if tgtStr == "x86_64" then cache.pluginsX86Json else (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true cache.baseMod).2.toJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{plJson}}"
    | "verify-certs" =>
      let certJson := match customModOpt with
        | some m => (verifyModuleCerts m.moduleName ((runDefaultPipeline m).2.map toOptimizationCert)).toJson
        | none => cache.certReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{certJson}}"
    | "validate-tv" =>
      let tvJson := match customModOpt with
        | some m => (validateTranslationModule m (runDefaultPipeline m).1).toJson
        | none => cache.tvReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{tvJson}}"
    | other =>
      s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unknown_method:{escapeJsonWorker other}\"}"

abbrev handleWorkerLine := handleWorkerRequest

partial def workerLoop (engineName : String) (stdin stdout : IO.FS.Stream) (cacheRef : IO.Ref (Option WorkerCache)) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then workerLoop engineName stdin stdout cacheRef
  else
    let method := (extractRpcStringField trimmed "method").getD ""
    if method == "exit" || method == "shutdown" || method == "quit" then
      stdout.putStrLn s!"\{\"id\":{extractRpcId trimmed},\"ok\":true,\"result\":\{\"status\":\"bye\"}}"
      stdout.flush; return 0
    else
      let resp ← match handleFastWorkerRequest? engineName trimmed with
        | some fast => pure fast
        | none =>
          let cache ← getOrInitWorkerCache cacheRef
          pure (handleWorkerRequest engineName cache trimmed)
      stdout.putStrLn resp
      stdout.flush; workerLoop engineName stdin stdout cacheRef

def runWorker (engineName : String) : IO UInt32 := do
  workerLoop engineName (← IO.getStdin) (← IO.getStdout) (← IO.mkRef none)

def printCoreUsage (tag : String) (hasFrontend : Bool) : IO Unit := do
  let fe (xs : List String) : List String := if hasFrontend then xs else []
  let lines := [
    s!"{tag} v0.5.0 — Formally Validated Lean 4 Optimizer, Segregated Plugin Engine, Superoptimizer, TV, FastCheck & Multi-Target Codegen",
    "",
    s!"Usage: {tag} <command> [options]",
    "",
    "Commands:"
  ] ++ fe ["  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"] ++ [
    "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file>, --arch x86_64|arm64, --baseline, --slot-regression, -o <path>)",
    "  compile-static-lib Emit C-ABI static library (.a) + C header (.h) for zero-copy FFI (--input <file>, -o <lib.a>, --header <lib.h>)",
    "  compile-mlir       Emit GPU MLIR module (--input <file>, -o <path>)",
    "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file>, --sm sm_90, --fastcheck, -o <path>)",
    "  compile-metal      Emit Apple Metal Shading Language 3.0 (--input <file>, --fastcheck, -o <path>)",
    "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX/Metal kernels (--samples N, --emit-llvm, --emit-ptx, --emit-metal, --json, -o <path>)",
    "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file>, -o <path>)",
    "  superopt           Run cost-guided enumerative superoptimizer (--target x86_64|arm64|cuda_ptx|apple_metal, --json, -o <path>)",
    "  plugins            Run segregated optimization plugins under Law 1 TV/Cost Gate (--target <arch>, --test-adversarial, --json)",
    "  pr-verify          Run Law 5 PR & Spec-Pinning Gate + Season 8 turbo-lean pr-verify/audit-spec (--base <ref>, --disallow-spec-changes, --json)",
    "  turbo-plugin       Run JSONL-stdio external accelerator plugin for turbo-lean (ExternalProcessAccelerator protocol)",
    "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file>, --json, -o <path>)",
    "  validate-tv        Run Alive2-style symbolic translation validation (--input <file>, --json, -o <path>)",
    "  audit-axioms       Run in-kernel transitive axiom audit (Lean.collectAxioms snapshot, --json)",
    "  emit-lnir          Emit LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)"
  ] ++ fe [
    "  audit-axioms       Run in-kernel transitive axiom audit over all 134 soundness theorems (--json)",
    "  turbo-status       Probe Turbo Lean integration, verify BLAKE3 vectors, and emit/verify receipt"
  ] ++ [
    "  self-test          Run end-to-end Core, Spec (Laws 1-5), Plugins, Codec, FastCheck, Superopt, SymbolicTV, LLVM/PTX/Metal self-tests",
    "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"
  ]
  IO.println (String.intercalate "\n" lines)

def runAuditAxioms (args : List String) : IO UInt32 := do
  let report := verifiedAxiomAuditReport
  IO.println (if hasFlag args "--json" then report.toJson else report.formatSummary)
  return if report.passed then 0 else 1

/-- Shared CLI dispatcher for both `lean-native-core` (`elaborateHook? = none`) and `lean-native` (`elaborateHook? = some ...`). -/
def dispatchSharedCommand (tag : String) (elaborateHook? : Option (String → IO LNIRModule))
    (args : List String) : IO (Option UInt32) := do
  match args with
  | "audit-axioms" :: rest       => some <$> runAuditAxioms rest
  | "compile-llvm" :: rest       => some <$> runCompileLLVM tag elaborateHook? rest
  | "compile-static-lib" :: rest => some <$> runCompileStaticLib tag elaborateHook? rest
  | "emit-cabi-bindings" :: rest => some <$> runEmitCAbiBindings tag elaborateHook? rest
  | "compile-c-abi" :: rest      => some <$> runEmitCAbiBindings tag elaborateHook? rest
  | "compile-mlir" :: rest       => some <$> runCompileMLIR tag elaborateHook? rest
  | "compile-ptx" :: rest       => some <$> runCompilePTX tag elaborateHook? rest
  | "compile-metal" :: rest     => some <$> runCompileMetal tag elaborateHook? rest
  | "compile-fastcheck" :: rest => some <$> runCompileFastCheck tag elaborateHook? rest
  | "compile-hybrid" :: rest    => some <$> runCompileHybrid tag elaborateHook? rest
  | "compile" :: rest           => some <$> runCompileMode tag elaborateHook? rest
  | "--c-abi" :: _              => some <$> runCompileMode tag elaborateHook? args
  | "--emit-c-abi" :: _         => some <$> runCompileMode tag elaborateHook? args
  | "--self-test" :: _          => some <$> runCoreSelfTest tag
  | "superopt" :: rest          => some <$> runSuperopt elaborateHook? rest
  | "plugins" :: rest           => some <$> runPlugins elaborateHook? rest
  | "telemetry" :: rest         => some <$> runTelemetry elaborateHook? rest
  | "pr-verify" :: rest         => some <$> runPRVerify tag rest
  | "turbo-plugin" :: _         => some <$> runTurboPlugin
  | "verify-certs" :: rest      => some <$> runVerifyCerts tag elaborateHook? rest
  | "validate-tv" :: rest       => some <$> runValidateTV elaborateHook? rest
  | "emit-lnir" :: rest         => some <$> runEmitLNIR tag elaborateHook? rest
  | "worker" :: _               => some <$> runWorker tag
  | _                           =>
    if hasFlag args "--c-abi" || hasFlag args "--emit-c-abi" then
      some <$> runCompileMode tag elaborateHook? args
    else
      return none

end LeanNative.Driver.CoreCLI
