import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec

namespace LeanNative.Driver.CoreCLI

open LeanNative.IR
open LeanNative.IR.Codec

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
    | .gf2Affine => s!"lean_native_gf2_affine({ls}, {rs})"
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

partial def emitRustCodeBody (c : LNIRCode) (indent : String := "        ") (loopAcc? : Option VarId := none) : Option String :=
  match c with
  | .letBind dst _ (.scalar e) k => do
    let rest ← emitRustCodeBody k indent loopAcc?
    some s!"{indent}let v{dst}: u64 = {emitRustScalarExpr e};\n{rest}"
  | .letBind dst _ (.call fnName args _ _) k => do
    let rest ← emitRustCodeBody k indent loopAcc?
    let argStr := String.intercalate ", " (args.map fun a => s!"v{a}")
    some s!"{indent}let v{dst}: u64 = {fnName}({argStr});\n{rest}"
  | .incRef _ _ k | .decRef _ _ k => emitRustCodeBody k indent loopAcc?
  | .ite cv t e => do
    let tb ← emitRustCodeBody t (indent ++ "    ") loopAcc?
    let eb ← emitRustCodeBody e (indent ++ "    ") loopAcc?
    some s!"{indent}if v{cv} != 0 \{\n{tb}\n{indent}} else \{\n{eb}\n{indent}}"
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k => do
    let stepStr ← emitRustCodeBody stepBody (indent ++ "    ") (some accVar)
    let rest ← emitRustCodeBody k indent loopAcc?
    some s!"{indent}let mut v{accVar}: u64 = v{accInit};\n{indent}let mut v{idxVar}: u64 = v{loVar};\n{indent}while v{idxVar} < v{hiVar} \{\n{stepStr}\n{indent}    v{idxVar} = v{idxVar}.wrapping_add(1);\n{indent}}\n{rest}"
  | .ret v =>
    match loopAcc? with
    | some accVar => some s!"{indent}v{accVar} = v{v};"
    | none => some s!"{indent}v{v}"
  | _ => none


/-- Canonical LNIR declarations for the SNARK / Binius kernels, lowered programmatically
    via `emitRustCodeBody` instead of hardcoded string blocks. -/
def canonicalSnarkKernelDecls : List LNIRDecl :=
  let mkBinDecl (name : String) (op : BinOp) : LNIRDecl :=
    { name := name
      params := [{ id := 0, name := "v0", ty := .i64 }, { id := 1, name := "v1", ty := .i64 }]
      retTy := .i64
      body := .letBind 2 .i64 (.scalar (.binOp op (.var 0) (.var 1))) (.ret 2) }
  let mkButterflyDecl (name : String) (op1 op2 : BinOp) : LNIRDecl :=
    { name := name
      params := [{ id := 0, name := "v0", ty := .i64 }, { id := 1, name := "v1", ty := .i64 }, { id := 2, name := "v2", ty := .i64 }]
      retTy := .i64
      body :=
        .letBind 3 .i64 (.scalar (.binOp op1 (.var 0) (.var 1)))
          (.letBind 4 .i64 (.scalar (.binOp op2 (.var 3) (.var 2)))
            (.ret 4)) }
  [ mkBinDecl "binius_tower_xor64" .bitXor
  , mkBinDecl "binius_tower_and64" .bitAnd
  , mkBinDecl "binius_gf128_clmul_low" .clmul64
  , mkBinDecl "binius_gf128_clmul_high" .clmul64Hi
  , mkButterflyDecl "lean_native_f128_mul_const_zmm" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_f128_mul_low_const_m128i" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_f128_tri_acc_neon" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_f128_mul_unreduced_neon" .clmul64 .clmul64Hi
  , mkButterflyDecl "lean_native_f128_fold_alpha_four_slice" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_f128_pre_reduce_eq_lo_slice" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_gf8_inv_ntt_avx2_pair_composite_u32" .gf2Affine .bitXor
  , mkButterflyDecl "lean_native_gf8_shift_reduce_inner_ab_slice" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_gf8_shift_reduce_inner_ab_gfni_avx512_slice" .gf2Affine .bitXor
  , mkButterflyDecl "lean_native_gf8_urm_convert_ab_nomul_gfni_slice" .gf2Affine .bitXor
  , mkButterflyDecl "lean_native_gf2_fold_64_rows_gfni_c4_slice" .gf2Affine .bitXor
  , mkButterflyDecl "lean_native_f128_plane_bank_to_f128_slice" .bitXor .shl
  , mkButterflyDecl "lean_native_f128_fold64_banked_nested_slice" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_f128_transpose_butterfly_fused_2layer_slice" .bitXor .clmul64
  , mkButterflyDecl "lean_native_f128_partial_fold_tile8_slice" .clmul64 .bitXor
  , mkButterflyDecl "lean_native_f128_adjoint_inject_and_sweep_slice" .bitXor .clmul64
  , mkButterflyDecl "lean_native_f128_urm_accumulate_convert_batch_ab_slice" .clmul64 .bitXor
  , { name := "binius_gf128_reduce_0x87"
      params := [{ id := 0, name := "v0", ty := .i64 }, { id := 1, name := "v1", ty := .i64 }]
      retTy := .i64
      body :=
        .letBind 2 .i64 (.scalar (.binOp .clmul64 (.var 1) (.constU64 0x87)))
          (.letBind 3 .i64 (.scalar (.binOp .bitXor (.var 0) (.var 2)))
            (.ret 3)) }
  ]

def emitProgrammaticSnarkRust (decls : List LNIRDecl := canonicalSnarkKernelDecls) : String :=
  let fns := decls.map fun d =>
    let paramsStr := String.intercalate ", " (d.params.map fun p => s!"v{p.id}: {lnirTypeToRustType p.ty}")
    let bodyStr := (emitRustCodeBody d.body "    " none).getD "    0"
    s!"#[inline(always)]\npub fn {d.name}({paramsStr}) -> {lnirTypeToRustType d.retTy} \{\n{bodyStr}\n}"
  String.intercalate "\n\n" (
    [ "// Auto-generated by lean-native programmatic LNIR -> Rust emitter (0 hardcoded string blobs)"
    , "#![allow(unused_variables, unused_mut, non_snake_case, clippy::all)]" ] ++ fns)


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
  String.intercalate "\n" ([emitProgrammaticSnarkRust canonicalSnarkKernelDecls, "pub mod c_abi {", "    extern \"C\" {"] ++ declExterns ++ ["    }", "}"] ++ declWrappers ++ [""])

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

/-- Atomic file write (`P0` Fail-Closed Output Publication):
    Writes `bytes` to a unique monotonic timestamped staging sibling `<path>.tmp.<nanos>.stage`
    and renames it over `path`, avoiding fixed-filename races and preserving any previous valid output at `path`. -/
def writeBinaryAtomic (path : String) (bytes : ByteArray) : IO Unit := do
  let nonce ← IO.monoNanosNow
  let tmpPath := s!"{path}.tmp.{nonce}.stage"
  IO.FS.writeBinFile tmpPath bytes
  IO.FS.rename tmpPath path

def writeTextAtomic (path : String) (text : String) : IO Unit := do
  let nonce ← IO.monoNanosNow
  let tmpPath := s!"{path}.tmp.{nonce}.stage"
  IO.FS.writeFile tmpPath text
  IO.FS.rename tmpPath path

private def readU16LE (b : ByteArray) (off : Nat) : UInt16 :=
  if off + 1 < b.size then
    let b0 := (b.get! off).toUInt16
    let b1 := (b.get! (off + 1)).toUInt16
    b0 ||| (b1 <<< 8)
  else 0

private def readU32LE (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 3 < b.size then
    let b0 := (b.get! off).toUInt32
    let b1 := (b.get! (off + 1)).toUInt32
    let b2 := (b.get! (off + 2)).toUInt32
    let b3 := (b.get! (off + 3)).toUInt32
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
  else 0

private def checkMachOLoadCmds (b : ByteArray) (limit : Nat) : Nat → Nat → Option UInt32 → Option UInt32
  | 0, off, foundPlat => if off == limit then foundPlat else none
  | f + 1, off, foundPlat =>
    if off + 8 > limit then none
    else
      let cmd := readU32LE b off
      let cmdsize := (readU32LE b (off + 4)).toNat
      if cmdsize < 8 || cmdsize % 8 != 0 || off + cmdsize > limit then none
      else if cmd == 0x32 then
        if cmdsize < 24 || foundPlat.isSome then none
        else checkMachOLoadCmds b limit f (off + cmdsize) (some (readU32LE b (off + 8)))
      else
        checkMachOLoadCmds b limit f (off + cmdsize) foundPlat

/-- Check object format and CPU headers, plus Apple's platform load command.
    ELF headers do not distinguish Linux from Android or establish runtime ABI compatibility.
    These checks are not a complete object/linker or runtime validation.
    - `.x86_64` -> ELF64 (`\x7fELF\x02\x01`, `>= 64` bytes), `e_type == 1` (`ET_REL`), `e_machine == 0x3E` (`EM_X86_64`)
    - `.arm64` / `.androidArm64` -> ELF64 (`\x7fELF\x02\x01`, `>= 64` bytes), `e_type == 1` (`ET_REL`), `e_machine == 0xB7` (`EM_AARCH64`)
    - `.macosArm64` -> Mach-O 64-bit (`0xFEEDFACF`, `>= 32` bytes), `cputype == 0x0100000C` (`CPU_TYPE_ARM64`),
      `filetype == 1` (`MH_OBJECT`), `LC_BUILD_VERSION` (`cmd == 0x32`) with `platform == 1` (`PLATFORM_MACOS`)
    - `.iosArm64` -> Mach-O 64-bit (`0xFEEDFACF`, `>= 32` bytes), `cputype == 0x0100000C`, `filetype == 1` (`MH_OBJECT`),
      `LC_BUILD_VERSION` (`cmd == 0x32`) with `platform == 2` (`PLATFORM_IOS`)
    - `.iosSimArm64` -> Mach-O 64-bit (`0xFEEDFACF`, `>= 32` bytes), `cputype == 0x0100000C`, `filetype == 1` (`MH_OBJECT`),
      `LC_BUILD_VERSION` (`cmd == 0x32`) with `platform == 7` (`PLATFORM_IOSSIMULATOR`)
    - `.wasm32` -> WebAssembly binary magic (`\x00asm\x01\x00\x00\x00`, `> 8` bytes)
    - All other targets fail closed (`false`). -/
def verifyObjectBytesForTarget (arch : TargetArch) (b : ByteArray) : Bool × String :=
  if b.size < 32 then (false, s!"artifact too small ({b.size} bytes < 32)")
  else
    match arch with
    | .x86_64 =>
      let isElf64 := b.size >= 64 && b.get! 0 == 0x7F && b.get! 1 == 0x45 && b.get! 2 == 0x4C && b.get! 3 == 0x46 && b.get! 4 == 2 && b.get! 5 == 1
      let etype := readU16LE b 16
      let mach := readU16LE b 18
      if !isElf64 then (false, "expected ELF64 little-endian header (>= 64 bytes)")
      else if etype != 1 then (false, s!"expected ELF relocatable object e_type=1 (ET_REL), got {etype}")
      else if mach != 0x3E then (false, s!"expected ELF e_machine=0x3E (EM_X86_64), got {mach}")
      else (true, "ELF64 ET_REL EM_X86_64; OS/ABI not verified")
    | .arm64 | .androidArm64 =>
      let isElf64 := b.size >= 64 && b.get! 0 == 0x7F && b.get! 1 == 0x45 && b.get! 2 == 0x4C && b.get! 3 == 0x46 && b.get! 4 == 2 && b.get! 5 == 1
      let etype := readU16LE b 16
      let mach := readU16LE b 18
      if !isElf64 then (false, "expected ELF64 little-endian header (>= 64 bytes)")
      else if etype != 1 then (false, s!"expected ELF relocatable object e_type=1 (ET_REL), got {etype}")
      else if mach != 0xB7 then (false, s!"expected ELF e_machine=0xB7 (EM_AARCH64), got {mach}")
      else (true, "ELF64 ET_REL EM_AARCH64; OS/ABI not verified")
    | .macosArm64 | .iosArm64 | .iosSimArm64 =>
      let magic := readU32LE b 0
      let cputype := readU32LE b 4
      let filetype := readU32LE b 12
      let ncmds := (readU32LE b 16).toNat
      let sizeofcmds := (readU32LE b 20).toNat
      let expectedPlat : UInt32 :=
        match arch with
        | .macosArm64  => 1
        | .iosArm64    => 2
        | .iosSimArm64 => 7
        | _            => 0
      if magic != 0xFEEDFACF then (false, s!"expected Mach-O 64-bit magic 0xFEEDFACF, got {magic}")
      else if cputype != 0x0100000C then (false, s!"expected Mach-O CPU_TYPE_ARM64 (0x0100000C), got {cputype}")
      else if filetype != 1 then (false, s!"expected Mach-O MH_OBJECT (filetype=1), got {filetype}")
      else if 32 + sizeofcmds > b.size then (false, s!"Mach-O load commands exceed object size ({32 + sizeofcmds} > {b.size})")
      else
        match checkMachOLoadCmds b (32 + sizeofcmds) ncmds 32 none with
        | some plat =>
          if plat == expectedPlat then (true, s!"Mach-O ARM64 platform={plat}")
          else (false, s!"Mach-O platform mismatch: expected platform={expectedPlat} for {arch.triple}, got platform={plat}")
        | none => (false, "Mach-O missing LC_BUILD_VERSION (0x32) platform load command")
    | .wasm32 =>
      let isWasm := b.size > 8 && b.get! 0 == 0x00 && b.get! 1 == 0x61 && b.get! 2 == 0x73 && b.get! 3 == 0x6D &&
                    b.get! 4 == 0x01 && b.get! 5 == 0x00 && b.get! 6 == 0x00 && b.get! 7 == 0x00
      if isWasm then (true, "WASM32 v1")
      else (false, "expected WebAssembly binary magic (\\x00asm\\x01\\x00\\x00\\x00)")
    | _ => (false, s!"unsupported binary object verification target: {arch.triple}")

/-- Require exactly one complete non-index member equal to the compiled object.
    Parse the whole archive: substrings, trailing junk and extra objects fail. -/
def verifyStaticArchiveBytes (b expectedObj : ByteArray) : Bool :=
  if expectedObj.size == 0 || String.fromUTF8! (b.extract 0 8) != "!<arch>\n" then false
  else
    let rec members (off count fuel : Nat) : Bool :=
      if off == b.size then count == 1
      else match fuel with
      | 0 => false
      | fuel + 1 =>
        if off + 60 > b.size || b.get! (off + 58) != 0x60 || b.get! (off + 59) != 0x0A then false
        else
          let sizeText := (String.fromUTF8! (b.extract (off + 48) (off + 58))).trimAscii.toString
          match sizeText.toNat? with
          | none => false
          | some size =>
            let start := off + 60
            let stop := start + size
            let next := stop + size % 2
            if stop > b.size || next > b.size || (size % 2 == 1 && b.get! stop != 10) then false
            else
              let rawName := (String.fromUTF8! (b.extract off (off + 16))).trimAscii.toString
              let nameLen := if rawName.startsWith "#1/" then (rawName.drop 3).toString.toNat? else some 0
              match nameLen with
              | none => false
              | some n =>
                if n > size then false
                else
                  let name :=
                    if n == 0 then rawName
                    else ((String.fromUTF8! (b.extract start (start + n))).splitOn (String.singleton (Char.ofNat 0))).headD "" |>.trimAscii.toString
                  let isIndex := name == "/" || name == "//" || name == "/SYM64/" ||
                    name == "__.SYMDEF" || name == "__.SYMDEF SORTED"
                  if isIndex then members next count fuel
                  else if count != 0 || b.extract (start + n) stop != expectedObj then false
                  else members next (count + 1) fuel
    members 8 0 b.size

def verifyStaticArchiveFile (path : String) (expectedObj : ByteArray) : IO (Bool × String) := do
  if !(← System.FilePath.pathExists path) then
    return (false, s!"archive '{path}' does not exist")
  let b ← IO.FS.readBinFile path
  return if verifyStaticArchiveBytes b expectedObj then
    (true, "parsed archive with exactly one byte-identical object member")
  else (false, s!"archive '{path}' is malformed or does not bind exactly the expected object")

end LeanNative.Driver.CoreCLI
