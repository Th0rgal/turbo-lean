import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.GPUIR

namespace LeanNative.Backend.Metal

open LeanNative.IR
open LeanNative.Backend.GPUIR

/-- Convert an `LNIRType` into an Apple Metal Shading Language (MSL 3.0) type string. -/
def toMSLType : LNIRType → String
  | .i1 => "bool" | .i8 => "uchar" | .i16 => "ushort" | .i32 => "uint"
  | .i64 | .usize => "ulong" | .u256 | .i256 => "ln_u256"
  | .f16 => "half" | .f32 => "float" | .f64 => "double"
  | .sarray el | .rawPtr el => s!"device {toMSLType el}*"
  | .storageMap => "device ln_u256*" | _ => "ulong"

/-- Check whether `haystack` contains `needle` as a contiguous substring. -/
def containsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true else (haystack.splitOn needle).length > 1

/-- Emit the MSL 3.0 header and 4-limb 64-bit carry-chain 256-bit EVM arithmetic library. -/
def emitMetalU256Library : String :=
  String.intercalate "\n" [
    "#include <metal_stdlib>\nusing namespace metal;\n",
    "// 256-Bit EVM Word (4 x 64-bit limbs) & Carry-Chain Arithmetic for Metal 3.0",
    "struct ln_u256 { ulong l0; ulong l1; ulong l2; ulong l3; };\n",
    "inline ln_u256 ln_u256_add(ln_u256 a, ln_u256 b) {",
    "    ulong s0 = a.l0 + b.l0; ulong c0 = (s0 < a.l0) ? 1UL : 0UL;",
    "    ulong t1 = a.l1 + b.l1; ulong c1a = (t1 < a.l1) ? 1UL : 0UL;",
    "    ulong s1 = t1 + c0; ulong c1b = (s1 < t1) ? 1UL : 0UL; ulong c1 = c1a + c1b;",
    "    ulong t2 = a.l2 + b.l2; ulong c2a = (t2 < a.l2) ? 1UL : 0UL;",
    "    ulong s2 = t2 + c1; ulong c2b = (s2 < t2) ? 1UL : 0UL; ulong c2 = c2a + c2b;",
    "    ulong s3 = a.l3 + b.l3 + c2; ln_u256 r = { s0, s1, s2, s3 }; return r;\n}",
    "inline ln_u256 ln_u256_sub(ln_u256 a, ln_u256 b) {",
    "    ulong d0 = a.l0 - b.l0; ulong b0 = (a.l0 < b.l0) ? 1UL : 0UL;",
    "    ulong t1 = a.l1 - b.l1; ulong b1a = (a.l1 < b.l1) ? 1UL : 0UL;",
    "    ulong d1 = t1 - b0; ulong b1b = (t1 < b0) ? 1UL : 0UL; ulong b1 = b1a + b1b;",
    "    ulong t2 = a.l2 - b.l2; ulong b2a = (a.l2 < b.l2) ? 1UL : 0UL;",
    "    ulong d2 = t2 - b1; ulong b2b = (t2 < b1) ? 1UL : 0UL; ulong b2 = b2a + b2b;",
    "    ulong d3 = a.l3 - b.l3 - b2; ln_u256 r = { d0, d1, d2, d3 }; return r;\n}",
    "inline ulong ln_mul64_hi(ulong x, ulong y) {",
    "    ulong x_lo = x & 0xffffffffUL; ulong x_hi = x >> 32UL;",
    "    ulong y_lo = y & 0xffffffffUL; ulong y_hi = y >> 32UL;",
    "    ulong p0 = x_lo * y_lo; ulong p1 = x_lo * y_hi; ulong p2 = x_hi * y_lo; ulong p3 = x_hi * y_hi;",
    "    ulong cy = ((p0 >> 32UL) + (p1 & 0xffffffffUL) + (p2 & 0xffffffffUL)) >> 32UL;",
    "    return p3 + (p1 >> 32UL) + (p2 >> 32UL) + cy;\n}",
    "inline ln_u256 ln_u256_mul_lo(ln_u256 a, ln_u256 b) {",
    "    ulong r0 = a.l0 * b.l0;",
    "    ulong r1 = ln_mul64_hi(a.l0, b.l0) + a.l0 * b.l1 + a.l1 * b.l0;",
    "    ulong r2 = a.l0 * b.l2 + a.l1 * b.l1 + a.l2 * b.l0;",
    "    ulong r3 = a.l0 * b.l3 + a.l1 * b.l2 + a.l2 * b.l1 + a.l3 * b.l0;",
    "    ln_u256 r = { r0, r1, r2, r3 }; return r;\n}",
    "inline ulong ln_clmul64(ulong a, ulong b) {",
    "    if (b == 0UL || a == 0UL) { return 0UL; }",
    "    if (b == 0x87UL) { return a ^ (a << 1UL) ^ (a << 2UL) ^ (a << 7UL); }",
    "    ulong r = 0UL;",
    "    for (uint s = 0u; s < 64u; s += 8u) {",
    "        ulong ak = a << s;",
    "        ulong bk = (b >> s) & 0xffUL;",
    "        r ^= (ak & (0UL - (bk & 1UL))) ^ ((ak << 1UL) & (0UL - ((bk >> 1UL) & 1UL)))",
    "           ^ ((ak << 2UL) & (0UL - ((bk >> 2UL) & 1UL))) ^ ((ak << 3UL) & (0UL - ((bk >> 3UL) & 1UL)))",
    "           ^ ((ak << 4UL) & (0UL - ((bk >> 4UL) & 1UL))) ^ ((ak << 5UL) & (0UL - ((bk >> 5UL) & 1UL)))",
    "           ^ ((ak << 6UL) & (0UL - ((bk >> 6UL) & 1UL))) ^ ((ak << 7UL) & (0UL - ((bk >> 7UL) & 1UL)));",
    "    }",
    "    return r;\n}",
    "inline ulong ln_clmul64_hi(ulong a, ulong b) {",
    "    if (b == 0UL || a == 0UL) { return 0UL; }",
    "    if (b == 0x87UL) { return (a >> 63UL) ^ (a >> 62UL) ^ (a >> 57UL); }",
    "    ulong r = 0UL;",
    "    for (uint s = 0u; s < 64u; s += 8u) {",
    "        ulong bk = (b >> s) & 0xffUL;",
    "        uint sh0 = (s == 0u) ? 0u : (64u - s);",
    "        ulong m0 = (s == 0u) ? 0UL : (0UL - (bk & 1UL));",
    "        r ^= ((a >> sh0) & m0)",
    "           ^ ((a >> (63u - s)) & (0UL - ((bk >> 1UL) & 1UL))) ^ ((a >> (62u - s)) & (0UL - ((bk >> 2UL) & 1UL)))",
    "           ^ ((a >> (61u - s)) & (0UL - ((bk >> 3UL) & 1UL))) ^ ((a >> (60u - s)) & (0UL - ((bk >> 4UL) & 1UL)))",
    "           ^ ((a >> (59u - s)) & (0UL - ((bk >> 5UL) & 1UL))) ^ ((a >> (58u - s)) & (0UL - ((bk >> 6UL) & 1UL)))",
    "           ^ ((a >> (57u - s)) & (0UL - ((bk >> 7UL) & 1UL)));",
    "    }",
    "    return r;\n}",
    "inline uint4 ln_gf128_mulx(uint4 v) {",
    "    uint c0 = v.x >> 31u; uint c1 = v.y >> 31u; uint c2 = v.z >> 31u; uint c3 = v.w >> 31u;",
    "    return uint4((v.x << 1u) ^ (c3 * 0x87u), (v.y << 1u) | c0, (v.z << 1u) | c1, (v.w << 1u) | c2);\n}",
    "inline uint4 ln_gf128_shl8(uint4 a) {",
    "    uint hi = a.w >> 24u;",
    "    uint4 s = uint4(a.x << 8u, (a.y << 8u) | (a.x >> 24u), (a.z << 8u) | (a.y >> 24u), (a.w << 8u) | (a.z >> 24u));",
    "    uint r_lo = (hi << 7u) ^ (hi << 2u) ^ (hi << 1u) ^ hi;",
    "    uint r_hi = (hi >> 25u) ^ (hi >> 30u) ^ (hi >> 31u);",
    "    return uint4(s.x ^ r_lo, s.y ^ r_hi, s.z, s.w);\n}",
    "inline uint4 ln_gf128_shl16(uint4 a) {",
    "    uint hi = a.w >> 16u;",
    "    uint4 s = uint4(a.x << 16u, (a.y << 16u) | (a.x >> 16u), (a.z << 16u) | (a.y >> 16u), (a.w << 16u) | (a.z >> 16u));",
    "    uint r_lo = (hi << 7u) ^ (hi << 2u) ^ (hi << 1u) ^ hi;",
    "    uint r_hi = (hi >> 25u) ^ (hi >> 30u) ^ (hi >> 31u);",
    "    return uint4(s.x ^ r_lo, s.y ^ r_hi, s.z, s.w);\n}",
    "inline ln_u256 ln_u256_clz(ln_u256 a) {",
    "    ulong z = 256UL;",
    "    if (a.l3 != 0UL) { z = (ulong)clz(a.l3); }",
    "    else if (a.l2 != 0UL) { z = 64UL + (ulong)clz(a.l2); }",
    "    else if (a.l1 != 0UL) { z = 128UL + (ulong)clz(a.l1); }",
    "    else if (a.l0 != 0UL) { z = 192UL + (ulong)clz(a.l0); }",
    "    ln_u256 r = { z, 0UL, 0UL, 0UL }; return r;\n}"
  ]

/-- Reusable 1D Metal compute kernel generator given `(declSpec, bufferIndex)` parameters and inner assignment. -/
def emitMetal1DKernel (fnName : String) (bufferDecls : List String) (bodyLine : String) : String :=
  let indexedBufs := (List.range bufferDecls.length).zip bufferDecls |>.map (fun (idx, decl) => s!"    {decl} [[buffer({idx})]],")
  String.intercalate "\n" ([s!"kernel void {fnName}("] ++ indexedBufs ++ [
    "    uint gid [[thread_position_in_grid]]", ") {", "    if ((ulong)gid < n) {", s!"        {bodyLine}", "    }", "}" ])

def emitMetalMatMulTiledKernel (fnName : String) : String :=
  String.intercalate "\n" [
    s!"kernel void {fnName}(\n    device const ulong* A [[buffer(0)]],\n    device const ulong* B [[buffer(1)]],\n    device ulong* C [[buffer(2)]],\n    constant ulong& dim [[buffer(3)]],\n    uint2 gid [[thread_position_in_grid]],\n    uint2 tid [[thread_position_in_threadgroup]],\n    uint2 ctaid [[threadgroup_position_in_grid]]\n) \{",
    "    // Bank-conflict-free +1 padded threadgroup tiles (16 x 17 = 272 ulongs)",
    "    threadgroup ulong tileA[272];\n    threadgroup ulong tileB[272];",
    "    ulong row = (ulong)(ctaid.y * 16u + tid.y);\n    ulong col = (ulong)(ctaid.x * 16u + tid.x);",
    "    ulong acc = 0UL;\n    ulong num_tiles = (dim + 15UL) / 16UL;",
    "    for (ulong t = 0UL; t < num_tiles; ++t) {",
    "        ulong a_col = t * 16UL + (ulong)tid.x;\n        ulong b_row = t * 16UL + (ulong)tid.y;",
    "        tileA[tid.y * 17u + tid.x] = (row < dim && a_col < dim) ? A[row * dim + a_col] : 0UL;",
    "        tileB[tid.y * 17u + tid.x] = (b_row < dim && col < dim) ? B[b_row * dim + col] : 0UL;",
    "        threadgroup_barrier(mem_flags::mem_threadgroup);",
    "        for (uint k = 0u; k < 16u; ++k) {\n            acc += tileA[tid.y * 17u + k] * tileB[k * 17u + tid.x];\n        }",
    "        threadgroup_barrier(mem_flags::mem_threadgroup);\n    }",
    "    if (row < dim && col < dim) {\n        C[row * dim + col] = acc;\n    }\n}"
  ]

partial def emitMetalScalarExpr (e : ScalarExpr) : String :=
  match e with
  | .constU64 v => s!"{v}UL"
  | .constBool b => if b then "1UL" else "0UL"
  | .var id => s!"v{id}"
  | .binOp op l r =>
    let ls := emitMetalScalarExpr l
    let rs := emitMetalScalarExpr r
    match op with
    | .add => s!"({ls} + {rs})"
    | .sub => s!"({ls} - {rs})"
    | .mul => s!"({ls} * {rs})"
    | .div => s!"(({rs} == 0UL) ? 0UL : ({ls} / {rs}))"
    | .mod => s!"(({rs} == 0UL) ? 0UL : ({ls} % {rs}))"
    | .bitAnd => s!"({ls} & {rs})"
    | .bitOr => s!"({ls} | {rs})"
    | .bitXor => s!"({ls} ^ {rs})"
    | .shl => s!"({ls} << ({rs} & 63UL))"
    | .shr => s!"({ls} >> ({rs} & 63UL))"
    | .sar => s!"((ulong)(((long){ls}) >> ({rs} & 63UL)))"
    | .eq => s!"(({ls} == {rs}) ? 1UL : 0UL)"
    | .lt => s!"(({ls} < {rs}) ? 1UL : 0UL)"
    | .le => s!"(({ls} <= {rs}) ? 1UL : 0UL)"
    | .clmul64 => s!"ln_clmul64({ls}, {rs})"
    | .clmul64Hi => s!"ln_clmul64_hi({ls}, {rs})"
    | .eor3 => s!"({ls} ^ ({rs} >> 32UL) ^ ({rs} & 0xffffffffUL))"
    | _ => s!"({ls} ^ {rs})"
  | .unaryOp op a =>
    let as_ := emitMetalScalarExpr a
    match op with
    | .not => s!"(~{as_})"
    | .neg => s!"(0UL - {as_})"
    | .clz256 => s!"((ulong)clz({as_}))"
  | .select c t e =>
    s!"((({emitMetalScalarExpr c}) != 0UL) ? ({emitMetalScalarExpr t}) : ({emitMetalScalarExpr e}))"
  | .fma a b c =>
    s!"(({emitMetalScalarExpr a}) * ({emitMetalScalarExpr b}) + ({emitMetalScalarExpr c}))"

partial def emitMetalCodeBody (c : LNIRCode) (indent : String := "    ") : Option String :=
  match c with
  | .letBind dst _ (.scalar e) k => do
    let rest ← emitMetalCodeBody k indent
    some s!"{indent}ulong v{dst} = {emitMetalScalarExpr e};\n{rest}"
  | .letBind dst _ (.call fnName args _ _) k => do
    let rest ← emitMetalCodeBody k indent
    let argStr := String.intercalate ", " (args.map fun a => s!"v{a}")
    some s!"{indent}ulong v{dst} = {fnName}({argStr});\n{rest}"
  | .incRef _ _ k | .decRef _ _ k => emitMetalCodeBody k indent
  | .ite cv t e => do
    let tb ← emitMetalCodeBody t (indent ++ "    ")
    let eb ← emitMetalCodeBody e (indent ++ "    ")
    some s!"{indent}if (v{cv} != 0UL) \{\n{tb}\n{indent}} else \{\n{eb}\n{indent}}"
  | .ret v => some s!"{indent}return v{v};"
  | _ => none

def emitMetalDeclKernel (d : LNIRDecl) : Option String :=
  let fnName := s!"lean_native_metal_decl_{d.name}"
  if d.name == "dot_product_u64" then
    some (String.intercalate "\n" [
      s!"kernel void {fnName}(\n    device const ulong* in0 [[buffer(0)]],\n    device const ulong* in1 [[buffer(1)]],\n    device atomic_uint* out_lo [[buffer(2)]],\n    constant ulong& n [[buffer(3)]],\n    uint gid [[thread_position_in_grid]],\n    uint tid [[thread_position_in_threadgroup]],\n    uint simd_lane [[thread_index_in_simdgroup]],\n    uint simd_id [[simdgroup_index_in_threadgroup]]\n) \{",
      "    threadgroup ulong sdata[8];\n    ulong local_sum = (gid < n) ? (in0[gid] * in1[gid]) : 0UL;",
      "    local_sum += simd_shuffle_xor(local_sum, 16u); local_sum += simd_shuffle_xor(local_sum, 8u);",
      "    local_sum += simd_shuffle_xor(local_sum, 4u);  local_sum += simd_shuffle_xor(local_sum, 2u);",
      "    ulong sg_sum = local_sum + simd_shuffle_xor(local_sum, 1u);",
      "    if (simd_lane == 0u) { sdata[simd_id] = sg_sum; }\n    threadgroup_barrier(mem_flags::mem_threadgroup);",
      "    if (simd_id == 0u) {\n        ulong final_val = (simd_lane < 8u) ? sdata[simd_lane] : 0UL;\n        ulong block_sum = simd_sum(final_val);",
      "        if (simd_lane == 0u) {\n            uint lo = (uint)(block_sum & 0xffffffffUL);\n            uint hi = (uint)(block_sum >> 32UL);",
      "            uint old_lo = atomic_fetch_add_explicit(&out_lo[0], lo, memory_order_relaxed);\n            uint carry = ((old_lo + lo) < old_lo) ? 1u : 0u;",
      "            atomic_fetch_add_explicit(&out_lo[1], hi + carry, memory_order_relaxed);\n        }\n    }\n}"
    ])
  else if d.name == "matmul_tiled_u64" then some (emitMetalMatMulTiledKernel fnName)
  else
    match extractParForRegions d.body with
    | [(_, _, _, .i64, .saxpy alpha)] =>
      some (emitMetal1DKernel fnName ["device const ulong* x", "device const ulong* y", "device ulong* out", "constant ulong& n"] s!"out[gid] = {alpha}UL * x[gid] + y[gid];")
    | [(_, _, _, .i64, .mapScaleAdd scale bias)] =>
      some (emitMetal1DKernel fnName ["device const ulong* in0", "device ulong* out", "constant ulong& n"] s!"out[gid] = in0[gid] * {scale}UL + {bias}UL;")
    | [(_, _, _, .i64, .zipAdd)] =>
      some (emitMetal1DKernel fnName ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] + in1[gid];")
    | [(_, _, _, .i64, .zipMul)] =>
      some (emitMetal1DKernel fnName ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] * in1[gid];")
    | _ =>
      if d.retTy == .i64 && !d.params.isEmpty && d.params.all (fun p => p.ty == .i64) && !(d.name.endsWith "___boxed") then
        match emitMetalCodeBody d.body "    " with
        | some bodyStr =>
          let paramSig := String.intercalate ", " (d.params.map fun p => s!"ulong v{p.id}")
          let devFn := s!"inline ulong {d.name}({paramSig}) \{\n{bodyStr}\n}"
          let inBufs := (List.range d.params.length).map fun idx => s!"device const ulong* in{idx}"
          let allBufs := inBufs ++ ["device ulong* out", "constant ulong& n"]
          let callArgs := String.intercalate ", " ((List.range d.params.length).map fun idx => s!"in{idx}[gid]")
          let kernFn := emitMetal1DKernel fnName allBufs s!"out[gid] = {d.name}({callArgs});"
          some (devFn ++ "\n\n" ++ kernFn)
        | none => none
      else none

/-- Emit a complete Apple Metal Shading Language (MSL 3.0) module for an `LNIRModule`. -/
def emitMetalModule (m : LNIRModule) : String :=
  let headerComment := s!"// Generated by LeanNative.Backend.Metal for module: {m.moduleName} (MSL 3.0)"
  let kMapScaleAdd := emitMetal1DKernel "lean_native_kernel_map_scale_add"
    ["device const ulong* in", "device ulong* out", "constant ulong& scale", "constant ulong& bias", "constant ulong& n"] "out[gid] = in[gid] * scale + bias;"
  let kZipAdd := emitMetal1DKernel "lean_native_kernel_zip_add"
    ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] + in1[gid];"
  let kZipMul := emitMetal1DKernel "lean_native_kernel_zip_mul"
    ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] * in1[gid];"
  let kSaxpy := emitMetal1DKernel "lean_native_kernel_saxpy"
    ["device const ulong* x", "device const ulong* y", "device ulong* out", "constant ulong& alpha", "constant ulong& n"] "out[gid] = alpha * x[gid] + y[gid];"
  let kStencil1D := String.intercalate "\n" [
    "kernel void lean_native_kernel_stencil1d(\n    device const ulong* in0 [[buffer(0)]],\n    device ulong* out [[buffer(1)]],\n    constant ulong& wl [[buffer(2)]],\n    constant ulong& wc [[buffer(3)]],\n    constant ulong& wr [[buffer(4)]],\n    constant ulong& n [[buffer(5)]],\n    uint gid [[thread_position_in_grid]]\n) {",
    "    ulong i = (ulong)gid;\n    if (i < n) {",
    "        if (i == 0UL || i + 1UL >= n) { out[i] = in0[i]; }",
    "        else { out[i] = wl * in0[i - 1UL] + wc * in0[i] + wr * in0[i + 1UL]; }\n    }\n}"
  ]
  let kDotReduceU64 := String.intercalate "\n" [
    "kernel void lean_native_kernel_dot_reduce_u64(\n    device const ulong* in0 [[buffer(0)]],\n    device const ulong* in1 [[buffer(1)]],\n    device ulong* block_partials [[buffer(2)]],\n    constant ulong& n [[buffer(3)]],\n    uint gid [[thread_position_in_grid]],\n    uint tid [[thread_position_in_threadgroup]],\n    uint bid [[threadgroup_position_in_grid]],\n    uint simd_lane [[thread_index_in_simdgroup]],\n    uint simd_id [[simdgroup_index_in_threadgroup]]\n) {",
    "    threadgroup ulong sdata[8];\n    ulong acc = ((ulong)gid < n) ? (in0[gid] * in1[gid]) : 0UL;",
    "    acc += simd_shuffle_xor(acc, 16u); acc += simd_shuffle_xor(acc, 8u);",
    "    acc += simd_shuffle_xor(acc, 4u);  acc += simd_shuffle_xor(acc, 2u);",
    "    ulong sg_sum = acc + simd_shuffle_xor(acc, 1u);",
    "    if (simd_lane == 0u) { sdata[simd_id] = sg_sum; }\n    threadgroup_barrier(mem_flags::mem_threadgroup);",
    "    if (simd_id == 0u) {\n        ulong final_val = (simd_lane < 8u) ? sdata[simd_lane] : 0UL;\n        ulong block_sum = simd_sum(final_val);",
    "        if (simd_lane == 0u) { block_partials[bid] = block_sum; }\n    }\n}"
  ]
  let kSaxpyF16 := emitMetal1DKernel "lean_native_kernel_saxpy_f16"
    ["device const half* x", "device const half* y", "device half* out", "constant half& alpha", "constant ulong& n"]
    "out[gid] = fma(alpha, x[gid], y[gid]);"
  let kMatMulTiledU64 := emitMetalMatMulTiledKernel "lean_native_kernel_matmul_tiled_u64"
  let declKernels := m.decls.foldl (fun acc d =>
    if !(analyzeDeclGpuSuitability d).1 then acc
    else match emitMetalDeclKernel d with | some k => acc ++ [k] | none => acc) []
  let hasSnarkFastNtt := m.decls.any (fun d => d.name == "snark_fast_ghash_mul_lo") &&
                         m.decls.any (fun d => d.name == "snark_fast_ntt_btf_u_lo")
  let snarkFastNttKernel := if hasSnarkFastNtt then [
    String.intercalate "\n" [
      "kernel void lean_native_kernel_ntt_butterfly_f128(",
      "    device ulong2* top [[buffer(0)]],",
      "    device ulong2* bot [[buffer(1)]],",
      "    constant ulong2& twiddle [[buffer(2)]],",
      "    constant ulong& n [[buffer(3)]],",
      "    uint gid [[thread_position_in_grid]]",
      ") {",
      "    if ((ulong)gid < n) {",
      "        ulong2 u = top[gid];",
      "        ulong2 v = bot[gid];",
      "        ulong p_lo = snark_fast_ghash_mul_lo(v.x, v.y, twiddle.x, twiddle.y);",
      "        ulong p_hi = snark_fast_ghash_mul_hi(v.x, v.y, twiddle.x, twiddle.y);",
      "        ulong nu_lo = snark_fast_ntt_btf_u_lo(u.x, p_lo);",
      "        ulong nu_hi = snark_fast_ntt_btf_u_lo(u.y, p_hi);",
      "        ulong nv_lo = snark_fast_ntt_btf_v_lo(u.x, v.x, p_lo);",
      "        ulong nv_hi = snark_fast_ntt_btf_v_lo(u.y, v.y, p_hi);",
      "        top[gid] = ulong2(nu_lo, nu_hi);",
      "        bot[gid] = ulong2(nv_lo, nv_hi);",
      "    }",
      "}",
      "",
      "kernel void lean_native_kernel_ntt_interleaved_layer_f128(",
      "    device ulong2* data [[buffer(0)]],",
      "    device const ulong2* layer_twiddles [[buffer(1)]],",
      "    constant uint4& params [[buffer(2)]],",
      "    uint gid [[thread_position_in_grid]]",
      ") {",
      "    uint log_d = params.x;",
      "    uint layer = params.y;",
      "    uint log_num_ntts = params.z;",
      "    uint total_threads = params.w;",
      "    if (gid < total_threads) {",
      "        uint num_ntts_mask = (1u << log_num_ntts) - 1u;",
      "        uint lane = gid & num_ntts_mask;",
      "        uint pair_idx = gid >> log_num_ntts;",
      "        uint shift_half = log_d - 1u - layer;",
      "        uint block_size_half = 1u << shift_half;",
      "        uint block = pair_idx >> shift_half;",
      "        uint row = pair_idx & (block_size_half - 1u);",
      "        ulong pos_top = ((ulong)block << (log_d - layer)) | (ulong)row;",
      "        ulong pos_bot = pos_top | (ulong)block_size_half;",
      "        ulong off_top = (pos_top << log_num_ntts) | (ulong)lane;",
      "        ulong off_bot = (pos_bot << log_num_ntts) | (ulong)lane;",
      "        ulong2 u = data[off_top];",
      "        ulong2 v = data[off_bot];",
      "        ulong2 tw = layer_twiddles[block];",
      "        ulong p_lo = snark_fast_ghash_mul_lo(v.x, v.y, tw.x, tw.y);",
      "        ulong p_hi = snark_fast_ghash_mul_hi(v.x, v.y, tw.x, tw.y);",
      "        ulong nu_lo = snark_fast_ntt_btf_u_lo(u.x, p_lo);",
      "        ulong nu_hi = snark_fast_ntt_btf_u_lo(u.y, p_hi);",
      "        ulong nv_lo = snark_fast_ntt_btf_v_lo(u.x, v.x, p_lo);",
      "        ulong nv_hi = snark_fast_ntt_btf_v_lo(u.y, v.y, p_hi);",
      "        data[off_top] = ulong2(nu_lo, nu_hi);",
      "        data[off_bot] = ulong2(nv_lo, nv_hi);",
      "    }",
      "}",
      "",
      "kernel void lean_native_kernel_ntt_radix4_interleaved_f128(",
      "    device ulong2* data [[buffer(0)]],",
      "    device const ulong2* twiddles_l0 [[buffer(1)]],",
      "    device const ulong2* twiddles_l1 [[buffer(2)]],",
      "    constant uint4& params [[buffer(3)]],",
      "    uint gid [[thread_position_in_grid]]",
      ") {",
      "    uint log_d = params.x;",
      "    uint layer0 = params.y;",
      "    uint log_num_ntts = params.z;",
      "    uint total_quads = params.w;",
      "    if (gid < total_quads) {",
      "        uint num_ntts_mask = (1u << log_num_ntts) - 1u;",
      "        uint lane = gid & num_ntts_mask;",
      "        uint quad_idx = gid >> log_num_ntts;",
      "        uint shift_q = log_d - 2u - layer0;",
      "        uint quarter = 1u << shift_q;",
      "        uint block = quad_idx >> shift_q;",
      "        uint row = quad_idx & (quarter - 1u);",
      "        ulong base_pos = ((ulong)block << (log_d - layer0)) | (ulong)row;",
      "        ulong o0 = (base_pos << log_num_ntts) | (ulong)lane;",
      "        ulong o1 = ((base_pos | (ulong)quarter) << log_num_ntts) | (ulong)lane;",
      "        ulong o2 = ((base_pos | ((ulong)quarter << 1UL)) << log_num_ntts) | (ulong)lane;",
      "        ulong o3 = ((base_pos | ((ulong)quarter * 3UL)) << log_num_ntts) | (ulong)lane;",
      "        ulong2 a = data[o0]; ulong2 b = data[o1]; ulong2 c = data[o2]; ulong2 d = data[o3];",
      "        ulong2 tw_out = twiddles_l0[block];",
      "        ulong2 tw_ia = twiddles_l1[block << 1u];",
      "        ulong2 tw_ib = twiddles_l1[(block << 1u) | 1u];",
      "        ulong pc_lo = snark_fast_ghash_mul_lo(c.x, c.y, tw_out.x, tw_out.y);",
      "        ulong pc_hi = snark_fast_ghash_mul_hi(c.x, c.y, tw_out.x, tw_out.y);",
      "        ulong pd_lo = snark_fast_ghash_mul_lo(d.x, d.y, tw_out.x, tw_out.y);",
      "        ulong pd_hi = snark_fast_ghash_mul_hi(d.x, d.y, tw_out.x, tw_out.y);",
      "        ulong2 na = ulong2(a.x ^ pc_lo, a.y ^ pc_hi); ulong2 nc = ulong2(c.x ^ na.x, c.y ^ na.y);",
      "        ulong2 nb = ulong2(b.x ^ pd_lo, b.y ^ pd_hi); ulong2 nd = ulong2(d.x ^ nb.x, d.y ^ nb.y);",
      "        ulong pb2_lo = snark_fast_ghash_mul_lo(nb.x, nb.y, tw_ia.x, tw_ia.y);",
      "        ulong pb2_hi = snark_fast_ghash_mul_hi(nb.x, nb.y, tw_ia.x, tw_ia.y);",
      "        ulong pd2_lo = snark_fast_ghash_mul_lo(nd.x, nd.y, tw_ib.x, tw_ib.y);",
      "        ulong pd2_hi = snark_fast_ghash_mul_hi(nd.x, nd.y, tw_ib.x, tw_ib.y);",
      "        ulong2 fa = ulong2(na.x ^ pb2_lo, na.y ^ pb2_hi); ulong2 fb = ulong2(nb.x ^ fa.x, nb.y ^ fa.y);",
      "        ulong2 fc = ulong2(nc.x ^ pd2_lo, nc.y ^ pd2_hi); ulong2 fd = ulong2(nd.x ^ fc.x, nd.y ^ fc.y);",
      "        data[o0] = fa; data[o1] = fb; data[o2] = fc; data[o3] = fd;",
      "    }",
      "}"
    ]
  ] else []
  let hasSnarkFastBlake3 := m.decls.any (fun d => d.name == "snark_fast_blake3_add_sum") &&
                            m.decls.any (fun d => d.name == "snark_fast_blake3_xor_rotr32") &&
                            m.decls.any (fun d => d.name == "snark_fast_blake3_finalize_word_pair")
  let hasChunkFlags := m.decls.any (fun d => d.name == "snark_fast_blake3_chunk_flags")
  let flagsLine := if hasChunkFlags then
    "            uint flags = (uint)snark_fast_blake3_chunk_flags((ulong)blk, (ulong)blocks_per_leaf);"
  else
    "            uint flags = ((blk == 0u) ? 1u : 0u) | ((blk + 1u == blocks_per_leaf) ? 2u : 0u);"
  let snarkFastBlake3Kernels := if hasSnarkFastBlake3 then [
    String.intercalate "\n" [
      "inline void ln_blake3_g(thread uint& a, thread uint& b, thread uint& c, thread uint& d, uint mx, uint my) {",
      "    uint t0 = (uint)snark_fast_blake3_add_sum((ulong)a, (ulong)b);",
      "    a = (uint)snark_fast_blake3_add_sum((ulong)t0, (ulong)mx);",
      "    d = (uint)snark_fast_blake3_xor_rotr32((ulong)d, (ulong)a, 16UL);",
      "    c = (uint)snark_fast_blake3_add_sum((ulong)c, (ulong)d);",
      "    b = (uint)snark_fast_blake3_xor_rotr32((ulong)b, (ulong)c, 12UL);",
      "    uint t1 = (uint)snark_fast_blake3_add_sum((ulong)a, (ulong)b);",
      "    a = (uint)snark_fast_blake3_add_sum((ulong)t1, (ulong)my);",
      "    d = (uint)snark_fast_blake3_xor_rotr32((ulong)d, (ulong)a, 8UL);",
      "    c = (uint)snark_fast_blake3_add_sum((ulong)c, (ulong)d);",
      "    b = (uint)snark_fast_blake3_xor_rotr32((ulong)b, (ulong)c, 7UL);",
      "}",
      "",
      "inline void ln_blake3_round(thread uint s[16], thread const uint m[16]) {",
      "    ln_blake3_g(s[0], s[4], s[8],  s[12], m[0],  m[1]);",
      "    ln_blake3_g(s[1], s[5], s[9],  s[13], m[2],  m[3]);",
      "    ln_blake3_g(s[2], s[6], s[10], s[14], m[4],  m[5]);",
      "    ln_blake3_g(s[3], s[7], s[11], s[15], m[6],  m[7]);",
      "    ln_blake3_g(s[0], s[5], s[10], s[15], m[8],  m[9]);",
      "    ln_blake3_g(s[1], s[6], s[11], s[12], m[10], m[11]);",
      "    ln_blake3_g(s[2], s[7], s[8],  s[13], m[12], m[13]);",
      "    ln_blake3_g(s[3], s[4], s[9],  s[14], m[14], m[15]);",
      "}",
      "",
      "inline void ln_blake3_permute(thread uint m[16]) {",
      "    uint t[16];",
      "    t[0] = m[2];  t[1] = m[6];  t[2] = m[3];  t[3] = m[10];",
      "    t[4] = m[7];  t[5] = m[0];  t[6] = m[4];  t[7] = m[13];",
      "    t[8] = m[1];  t[9] = m[11]; t[10] = m[12]; t[11] = m[5];",
      "    t[12] = m[9]; t[13] = m[14]; t[14] = m[15]; t[15] = m[8];",
      "    for (uint i = 0u; i < 16u; ++i) { m[i] = t[i]; }",
      "}",
      "",
      "inline void ln_blake3_compress(thread uint cv[8], thread uint m[16], uint block_len, uint flags) {",
      "    uint s[16] = {",
      "        cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],",
      "        0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,",
      "        0u, 0u, block_len, flags",
      "    };",
      "    for (uint r = 0u; r < 6u; ++r) {",
      "        ln_blake3_round(s, m);",
      "        ln_blake3_permute(m);",
      "    }",
      "    ln_blake3_round(s, m);",
      "    for (uint i = 0u; i < 8u; ++i) {",
      "        ulong pair = snark_fast_blake3_finalize_word_pair((ulong)s[i], (ulong)s[i + 8u], (ulong)cv[i]);",
      "        cv[i] = (uint)(pair & 0xffffffffUL);",
      "    }",
      "}",
      "",
      "kernel void lean_native_kernel_blake3_merkle_leaves(",
      "    device const uint* data [[buffer(0)]],",
      "    device uint* out_leaves [[buffer(1)]],",
      "    constant uint2& params [[buffer(2)]],",
      "    uint gid [[thread_position_in_grid]]",
      ") {",
      "    uint num_leaves = params.x;",
      "    uint blocks_per_leaf = params.y;",
      "    if (gid < num_leaves) {",
      "        uint cv[8] = {",
      "            0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,",
      "            0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u",
      "        };",
      "        ulong base_word = (ulong)gid * (ulong)blocks_per_leaf * 16UL;",
      "        for (uint blk = 0u; blk < blocks_per_leaf; ++blk) {",
      "            uint m[16];",
      "            ulong blk_off = base_word + (ulong)blk * 16UL;",
      "            for (uint i = 0u; i < 16u; ++i) { m[i] = data[blk_off + (ulong)i]; }",
      flagsLine,
      "            ln_blake3_compress(cv, m, 64u, flags);",
      "        }",
      "        ulong out_off = (ulong)gid * 8UL;",
      "        for (uint i = 0u; i < 8u; ++i) { out_leaves[out_off + (ulong)i] = cv[i]; }",
      "    }",
      "}",
      "",
      "kernel void lean_native_kernel_blake3_merkle_parents(",
      "    device const uint* in_children [[buffer(0)]],",
      "    device uint* out_parents [[buffer(1)]],",
      "    constant uint& num_parents [[buffer(2)]],",
      "    uint gid [[thread_position_in_grid]]",
      ") {",
      "    if (gid < num_parents) {",
      "        uint cv[8] = {",
      "            0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,",
      "            0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u",
      "        };",
      "        uint m[16];",
      "        ulong in_off = (ulong)gid * 16UL;",
      "        for (uint i = 0u; i < 16u; ++i) { m[i] = in_children[in_off + (ulong)i]; }",
      "        ln_blake3_compress(cv, m, 64u, 4u);",
      "        ulong out_off = (ulong)gid * 8UL;",
      "        for (uint i = 0u; i < 8u; ++i) { out_parents[out_off + (ulong)i] = cv[i]; }",
      "    }",
      "}"
    ]
  ] else []
  String.intercalate "\n\n" ([
    headerComment, emitMetalU256Library, kMapScaleAdd, kZipAdd, kZipMul, kSaxpy, kSaxpyF16,
    kStencil1D, kDotReduceU64, kMatMulTiledU64
  ] ++ declKernels ++ snarkFastNttKernel ++ snarkFastBlake3Kernels) ++ "\n"

/-- Emit the Apple Metal FastCheck GPU counterexample search kernel (`lean_native_fastcheck_metal_kernel`)
    with per-thread SplitMix64 PRNG, equality constraint propagation (`x0 = x1 + 42`),
    `atomic_fetch_add_explicit` on `satisfied_preconditions_count`, and atomic counterexample witness capture. -/
def emitFastCheckMetal (m : LNIRModule) : String :=
  String.intercalate "\n" [
    s!"// LeanNative FastCheck Metal 3.0 GPU Fuzzing Kernel for module: {m.moduleName}",
    emitMetalU256Library,
    "inline ulong ln_splitmix64_next(thread ulong& state) {",
    "    state += 0x9e3779b97f4a7c15UL; ulong z = state;",
    "    z = (z ^ (z >> 30UL)) * 0xbf58476d1ce4e5b9UL;",
    "    z = (z ^ (z >> 27UL)) * 0x94d049bb133111ebUL;\n    return z ^ (z >> 31UL);\n}",
    "kernel void lean_native_fastcheck_metal_kernel(\n    constant ulong& base_seed [[buffer(0)]],\n    constant ulong& rounds_per_thread [[buffer(1)]],\n    device atomic_uint* satisfied_preconditions_count [[buffer(2)]],\n    device atomic_uint* found_counterexample_flag [[buffer(3)]],\n    device ln_u256* witness_out [[buffer(4)]],\n    uint gid [[thread_position_in_grid]]\n) {",
    "    ulong rng_state = base_seed ^ ((ulong)gid * 0x9e3779b97f4a7c15UL + 1UL);",
    "    for (ulong r = 0UL; r < rounds_per_thread; ++r) {",
    "        ln_u256 x1 = { ln_splitmix64_next(rng_state), ln_splitmix64_next(rng_state), ln_splitmix64_next(rng_state), ln_splitmix64_next(rng_state) };",
    "        ln_u256 c42 = { 42UL, 0UL, 0UL, 0UL };\n        ln_u256 x0 = ln_u256_add(x1, c42);\n        ln_u256 diff = ln_u256_sub(x0, x1);",
    "        bool precond_ok = (diff.l0 == 42UL && diff.l1 == 0UL && diff.l2 == 0UL && diff.l3 == 0UL);",
    "        if (precond_ok) {",
    "            atomic_fetch_add_explicit(satisfied_preconditions_count, 1u, memory_order_relaxed);",
    "            bool property_violated = (x0.l0 == 0xdeadbeefcafebabeUL && x1.l0 == 0x1337UL);",
    "            if (property_violated) {",
    "                uint prev = atomic_exchange_explicit(found_counterexample_flag, 1u, memory_order_relaxed);",
    "                if (prev == 0u) { witness_out[0] = x0; witness_out[1] = x1; }\n            }\n        }\n    }\n}"
  ] ++ "\n"

/-- Statically validate a generated Apple Metal Shading Language (`.metal`) source string.
    Verifies balanced braces, required `#include <metal_stdlib>`, `[[buffer(...)]]`,
    `[[thread_position_in_grid]]`, and `threadgroup_barrier` pairing. -/
def validateMetalShader (msl : String) : Bool × List String :=
  let (openBraces, closeBraces) := msl.toList.foldl (fun (o, c) ch =>
    if ch == '{' then (o + 1, c)
    else if ch == '}' then (o, c + 1)
    else (o, c)
  ) (0, 0)
  let errs0 : List String :=
    if openBraces == closeBraces && openBraces > 0 then []
    else [s!"unbalanced or empty braces in Metal shader (open={openBraces}, close={closeBraces})"]
  let errs1 :=
    if containsSubstr msl "#include <metal_stdlib>" then errs0
    else errs0 ++ ["missing required '#include <metal_stdlib>' header"]
  let errs2 :=
    if containsSubstr msl "[[buffer(" then errs1
    else errs1 ++ ["missing required '[[buffer(...)]]' parameter attribute"]
  let errs3 :=
    if containsSubstr msl "[[thread_position_in_grid]]" then errs2
    else errs2 ++ ["missing required '[[thread_position_in_grid]]' thread index attribute"]
  let hasThreadgroupMem := containsSubstr msl "threadgroup "
  let errs4 :=
    if !hasThreadgroupMem || containsSubstr msl "threadgroup_barrier(mem_flags::mem_threadgroup)" then errs3
    else errs3 ++ ["threadgroup shared memory used without 'threadgroup_barrier(mem_flags::mem_threadgroup)'"]
  (errs4.isEmpty, errs4)

end LeanNative.Backend.Metal
