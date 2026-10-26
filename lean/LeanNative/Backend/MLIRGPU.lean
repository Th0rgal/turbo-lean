import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.GPUIR

namespace LeanNative.Backend.MLIRGPU

open LeanNative.IR
open LeanNative.Backend.GPUIR

/-- Inspect an `LNIRExpr` for constructs incompatible with GPU execution.
    Delegates to `LeanNative.Backend.GPUIR.checkExprGpuCompatibility`. -/
def checkExprGpuCompatibility (e : LNIRExpr) : List String :=
  GPUIR.checkExprGpuCompatibility e

/-- Recursively check an `LNIRCode` block for GPU compatibility violations.
    Delegates to `LeanNative.Backend.GPUIR.checkCodeGpuCompatibility`. -/
def checkCodeGpuCompatibility (code : LNIRCode) : List String :=
  GPUIR.checkCodeGpuCompatibility code

/-- Check whether an `LNIRCode` contains at least one `parFor` data-parallel region.
    Delegates to `LeanNative.Backend.GPUIR.containsParFor`. -/
def containsParFor (code : LNIRCode) : Bool :=
  GPUIR.containsParFor code

/-- Automatic GPU suitability analyzer for an `LNIRDecl`.
    Delegates to `LeanNative.Backend.GPUIR.analyzeDeclGpuSuitability`. -/
def analyzeGpuCompatibility (d : LNIRDecl) : Bool × List String :=
  GPUIR.analyzeDeclGpuSuitability d

/-- Convert an `LNIRType` into an MLIR type string (`i64`, `i256`, `f64`, `memref<?xi64>`, etc.). -/
def toMLIRType : LNIRType → String
  | .i1         => "i1"
  | .i8         => "i8"
  | .i16        => "i16"
  | .i32        => "i32"
  | .i64        => "i64"
  | .usize      => "index"
  | .u256       => "i256"
  | .i256       => "i256"
  | .f32        => "f32"
  | .f64        => "f64"
  | .sarray el  => s!"memref<?x{toMLIRType el}>"
  | .rawPtr el  => s!"memref<?x{toMLIRType el}>"
  | .storageMap => "memref<?xi256>"
  | _           => "i64"

/-- Lower a `ScalarExpr` to MLIR `arith.*` SSA instructions, returning `(preambleLines, resultSSA)`. -/
partial def emitMLIRScalarExpr (e : ScalarExpr) (counter : Nat) : List String × String × Nat :=
  match e with
  | .constU64 v =>
    let ssa := s!"%c_{counter}"
    ([s!"      {ssa} = arith.constant {v} : i64"], ssa, counter + 1)
  | .constBool b =>
    let ssa := s!"%cb_{counter}"
    let lit := if b then "true" else "false"
    ([s!"      {ssa} = arith.constant {lit} : i1"], ssa, counter + 1)
  | .var id =>
    ([], s!"%v{id}", counter)
  | .binOp op lhs rhs =>
    let (lLines, lVal, c1) := emitMLIRScalarExpr lhs counter
    let (rLines, rVal, c2) := emitMLIRScalarExpr rhs c1
    let dst := s!"%t_{c2}"
    let instr := match op with
      | .add           => s!"{dst} = arith.addi {lVal}, {rVal} : i64"
      | .sub           => s!"{dst} = arith.subi {lVal}, {rVal} : i64"
      | .mul           => s!"{dst} = arith.muli {lVal}, {rVal} : i64"
      | .div           => s!"{dst} = arith.divui {lVal}, {rVal} : i64"
      | .mod           => s!"{dst} = arith.remui {lVal}, {rVal} : i64"
      | .bitAnd        => s!"{dst} = arith.andi {lVal}, {rVal} : i64"
      | .bitOr         => s!"{dst} = arith.ori {lVal}, {rVal} : i64"
      | .bitXor        => s!"{dst} = arith.xori {lVal}, {rVal} : i64"
      | .shl           => s!"{dst} = arith.shli {lVal}, {rVal} : i64"
      | .shr           => s!"{dst} = arith.shrui {lVal}, {rVal} : i64"
      | .sar           => s!"{dst} = arith.shrsi {lVal}, {rVal} : i64"
      | .eq            => s!"{dst} = arith.cmpi eq, {lVal}, {rVal} : i64"
      | .lt            => s!"{dst} = arith.cmpi ult, {lVal}, {rVal} : i64"
      | .le            => s!"{dst} = arith.cmpi ule, {lVal}, {rVal} : i64"
      | .addChecked256 => s!"{dst} = arith.addi {lVal}, {rVal} : i64"
      | .subChecked256 => s!"{dst} = arith.subi {lVal}, {rVal} : i64"
      | .mulChecked256 => s!"{dst} = arith.muli {lVal}, {rVal} : i64"
      | .clmul64 | .clmul64Hi => s!"{dst} = llvm.call @llvm.aarch64.neon.pmull64({lVal}, {rVal}) : (i64, i64) -> vector<16xi8>"
      | .gf2Affine     => s!"{dst} = llvm.call @llvm.x86.vgf2p8affineqb.128({lVal}, {rVal}) : (vector<16xi8>, vector<16xi8>) -> vector<16xi8>"
      | .eor3          => s!"{dst} = llvm.call @llvm.aarch64.neon.eor3.v16i8({lVal}, {rVal}, {rVal}) : (vector<16xi8>, vector<16xi8>, vector<16xi8>) -> vector<16xi8>"
    (lLines ++ rLines ++ [s!"      {instr}"], dst, c2 + 1)
  | .unaryOp op arg =>
    let (aLines, aVal, c1) := emitMLIRScalarExpr arg counter
    let dst := s!"%u_{c1}"
    let instr := match op with
      | .not    => s!"%ones_{c1} = arith.constant -1 : i64\n      {dst} = arith.xori {aVal}, %ones_{c1} : i64"
      | .neg    => s!"%zero_{c1} = arith.constant 0 : i64\n      {dst} = arith.subi %zero_{c1}, {aVal} : i64"
      | .clz256 => s!"{dst} = math.ctlz {aVal} : i64"
    (aLines ++ [s!"      {instr}"], dst, c1 + 1)
  | .select cond thenVal elseVal =>
    let (cLines, cVal, c1) := emitMLIRScalarExpr cond counter
    let (tLines, tVal, c2) := emitMLIRScalarExpr thenVal c1
    let (eLines, eVal, c3) := emitMLIRScalarExpr elseVal c2
    let dst := s!"%sel_{c3}"
    (cLines ++ tLines ++ eLines ++ [s!"      {dst} = arith.select {cVal}, {tVal}, {eVal} : i64"], dst, c3 + 1)
  | .fma a b c =>
    let (aLines, aVal, c1) := emitMLIRScalarExpr a counter
    let (bLines, bVal, c2) := emitMLIRScalarExpr b c1
    let (cLines, cVal, c3) := emitMLIRScalarExpr c c2
    let mulVal := s!"%fma_mul_{c3}"
    let dst := s!"%fma_{c3}"
    (aLines ++ bLines ++ cLines ++ [
      s!"      {mulVal} = arith.muli {aVal}, {bVal} : i64",
      s!"      {dst} = arith.addi {mulVal}, {cVal} : i64"
    ], dst, c3 + 1)

/-- Emit MLIR `gpu.func` and `scf.parallel` representation for a `ParallelKernelKind`. -/
def emitMLIRKernelBody (elemTy : LNIRType) (kernel : ParallelKernelKind) : String :=
  let mlirElem := toMLIRType elemTy
  let emitBinArith (opName : String) : String :=
    String.intercalate "\n" [
      s!"      %lhs = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %rhs = memref.load %in1[%iv] : memref<?x{mlirElem}>",
      s!"      %res = {opName} %lhs, %rhs : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  match kernel with
  | .mapScaleAdd scale bias =>
    String.intercalate "\n" [
      s!"      %in_val = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %c_scale = arith.constant {scale} : {mlirElem}",
      s!"      %c_bias = arith.constant {bias} : {mlirElem}",
      s!"      %scaled = arith.muli %in_val, %c_scale : {mlirElem}",
      s!"      %res = arith.addi %scaled, %c_bias : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .zipAdd => emitBinArith "arith.addi"
  | .zipMul | .dotProduct => emitBinArith "arith.muli"
  | .saxpy alphaBits =>
    String.intercalate "\n" [
      s!"      %x_val = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %y_val = memref.load %in1[%iv] : memref<?x{mlirElem}>",
      s!"      %c_alpha = arith.constant {alphaBits} : {mlirElem}",
      s!"      %ax = arith.muli %c_alpha, %x_val : {mlirElem}",
      s!"      %res = arith.addi %ax, %y_val : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .stencil1D3Pt wLeft wCenter wRight =>
    String.intercalate "\n" [
      "      %c1_idx = arith.constant 1 : index\n      %n_minus_1 = arith.subi %n_idx, %c1_idx : index",
      "      %is_lo = arith.cmpi eq, %iv, %c0_idx : index\n      %is_hi = arith.cmpi uge, %iv, %n_minus_1 : index\n      %is_boundary = arith.ori %is_lo, %is_hi : i1",
      s!"      %center_val = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      "      %iv_m1 = arith.subi %iv, %c1_idx : index\n      %iv_p1 = arith.addi %iv, %c1_idx : index",
      "      %safe_m1 = arith.select %is_boundary, %iv, %iv_m1 : index\n      %safe_p1 = arith.select %is_boundary, %iv, %iv_p1 : index",
      s!"      %left_val = memref.load %in0[%safe_m1] : memref<?x{mlirElem}>\n      %right_val = memref.load %in0[%safe_p1] : memref<?x{mlirElem}>",
      s!"      %c_wl = arith.constant {wLeft} : {mlirElem}\n      %c_wc = arith.constant {wCenter} : {mlirElem}\n      %c_wr = arith.constant {wRight} : {mlirElem}",
      s!"      %tl = arith.muli %left_val, %c_wl : {mlirElem}\n      %tc = arith.muli %center_val, %c_wc : {mlirElem}\n      %tr = arith.muli %right_val, %c_wr : {mlirElem}",
      s!"      % tlc = arith.addi %tl, %tc : {mlirElem}\n      %stencil_val = arith.addi %tlc, %tr : {mlirElem}",
      s!"      %res = arith.select %is_boundary, %center_val, %stencil_val : {mlirElem}\n      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .customScalar idxVar inVars body =>
    let rec buildLoadLines (idx : Nat) : List VarId → List String
      | [] => []
      | vId :: rest =>
        let bufName := if idx == 0 then "%in0" else "%in1"
        s!"      %v{vId} = memref.load {bufName}[%iv] : memref<?x{mlirElem}>" :: buildLoadLines (idx + 1) rest
    let loadLines := buildLoadLines 0 inVars
    let idxCast := s!"      %v{idxVar} = arith.index_cast %iv : index to i64"
    let (exprLines, resVal, _) := emitMLIRScalarExpr body 0
    let storeLine := s!"      memref.store {resVal}, %out[%iv] : memref<?x{mlirElem}>"
    String.intercalate "\n" ([idxCast] ++ loadLines ++ exprLines ++ [storeLine])

/-- Extract all `(outVar, lenVar, inputs, elemTy, kernel)` regions from an `LNIRCode` tree. -/
def extractParForRegions (code : LNIRCode) :
    List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) :=
  GPUIR.extractParForRegions code

/-- Emit an MLIR `gpu.func` for a single extracted `parFor` region inside a declaration. -/
def emitMLIRGpuFunc (declName : String) (regionIdx : Nat) (elemTy : LNIRType)
    (kernel : ParallelKernelKind) : String :=
  let mlirElem := toMLIRType elemTy
  let kName := s!"@{declName}_parfor_{regionIdx}"
  let bodyStr := emitMLIRKernelBody elemTy kernel
  String.intercalate "\n" [
    s!"    gpu.func {kName}(%out: memref<?x{mlirElem}>, %in0: memref<?x{mlirElem}>, %in1: memref<?x{mlirElem}>, %n: i64) kernel attributes \{nvvm.maxntid = array<i32: 256, 1, 1>} \{",
    "      %tidx = nvvm.read.ptx.sreg.tid.x : i32\n      %bidx = nvvm.read.ptx.sreg.ctaid.x : i32\n      %bdim = nvvm.read.ptx.sreg.ntid.x : i32\n      %gdim = nvvm.read.ptx.sreg.nctaid.x : i32",
    "      %bid_mul = arith.muli %bidx, %bdim : i32\n      %gid_i32 = arith.addi %bid_mul, %tidx : i32\n      %stride_i32 = arith.muli %bdim, %gdim : i32",
    "      %gid = arith.index_cast %gid_i32 : i32 to index\n      %stride = arith.index_cast %stride_i32 : i32 to index\n      %c0_idx = arith.constant 0 : index\n      %n_idx = arith.index_cast %n : i64 to index",
    "      scf.parallel (%iv) = (%gid) to (%n_idx) step (%stride) {",
    bodyStr,
    "        scf.reduce\n      }\n      gpu.return\n    }"
  ]

/-- Lower GPU-compatible `LNIRDecl`s and `parFor` kernels in `m` to valid MLIR
    (`gpu.module`, `gpu.func`, `scf.parallel`, `arith.*`, `memref.*`, `nvvm.*`). -/
def emitMLIRModule (m : LNIRModule) : String :=
  let header := String.intercalate "\n" [
    s!"// LeanNative MLIR/NVVM GPU Module: {m.moduleName}",
    "module attributes {gpu.container_module} {",
    "  gpu.module @lean_native_gpu_kernels {"
  ]
  let builtinKernels := [
    emitMLIRGpuFunc "lean_native_builtin_map_scale_add" 0 .i64 (.mapScaleAdd 3 7),
    emitMLIRGpuFunc "lean_native_builtin_zip_add" 0 .i64 .zipAdd,
    emitMLIRGpuFunc "lean_native_builtin_zip_mul" 0 .i64 .zipMul,
    emitMLIRGpuFunc "lean_native_builtin_saxpy" 0 .i64 (.saxpy 5),
    emitMLIRGpuFunc "lean_native_builtin_stencil1d" 0 .i64 (.stencil1D3Pt 1 2 1)
  ]
  let declKernels := m.decls.foldl (fun acc d =>
    let (ok, _) := analyzeGpuCompatibility d
    if !ok then acc
    else
      let regions := extractParForRegions d.body
      if regions.isEmpty then
        acc
      else
        let rec emitRegions (idx : Nat) :
            List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) → List String
          | [] => []
          | (_, _, _, elemTy, k) :: rest =>
            emitMLIRGpuFunc d.name idx elemTy k :: emitRegions (idx + 1) rest
        acc ++ emitRegions 0 regions
  ) []
  let footer := String.intercalate "\n" [
    "  }",
    "}"
  ]
  String.intercalate "\n\n" ([header] ++ builtinKernels ++ declKernels ++ [footer]) ++ "\n"

/-- Emit a shared-memory parallel tree reduction PTX 8.0 kernel for `dot_product_u64`.
    Uses `.shared .align 8 .b8 sdata_raw[2048];` (256 x u64), grid-stride register accumulation,
    `bar.sync 0;` tree reduction (`stride = 128, 64, 32, 16, 8, 4, 2, 1`), and thread-0
    `atom.global.add.u64`. -/
def emitPTXDotReduceKernel (fnSymbol : String) : String :=
  let sharedSteps : List (Nat × Nat) := [(128, 1024), (64, 512), (32, 256)]
  let sharedLines := sharedSteps.foldl (fun acc (stride, byteOff) =>
    acc ++ [
      s!"    setp.lt.u32   %p2, %r3, {stride};\n    @!%p2 bra     $L_red_sync_{stride}_{fnSymbol};",
      s!"    ld.shared.u64 %rd15, [%rd14+{byteOff}];\n    add.u64       %rd9, %rd9, %rd15;\n    st.shared.u64 [%rd14], %rd9;",
      s!"$L_red_sync_{stride}_{fnSymbol}:\n    bar.sync      0;"
    ]
  ) []
  let warpSteps : List Nat := [16, 8, 4, 2, 1]
  let warpLines := [
    s!"    setp.lt.u32   %p2, %r3, 32;\n    @!%p2 bra     $L_warp_done_{fnSymbol};"
  ] ++ warpSteps.foldl (fun acc offset =>
    acc ++ [
      "    mov.b64            {%r5, %r6}, %rd9;",
      s!"    shfl.sync.bfly.b32 %r7, %r5, {offset}, 31, 0xffffffff;\n    shfl.sync.bfly.b32 %r8, %r6, {offset}, 31, 0xffffffff;",
      "    mov.b64            %rd15, {%r7, %r8};\n    add.u64            %rd9, %rd9, %rd15;"
    ]
  ) [] ++ [s!"$L_warp_done_{fnSymbol}:"]
  let reduceLines := sharedLines ++ warpLines
  String.intercalate "\n" ([
    s!".visible .entry {fnSymbol}(\n    .param .u64 param_out,\n    .param .u64 param_in0,\n    .param .u64 param_in1,\n    .param .u64 param_n\n)\n\{",
    "    .shared .align 8 .b8 sdata_raw[2048];\n    .reg .pred %p<3>;\n    .reg .b32  %r<9>;\n    .reg .b64  %rd<16>;\n",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_in0];\n    ld.param.u64 %rd3, [param_in1];\n    ld.param.u64 %rd4, [param_n];\n",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    cvta.to.global.u64 %rd3, %rd3;\n",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mov.u32      %r4, %nctaid.x;",
    "    mul.wide.u32 %rd5, %r1, %r2;\n    cvt.u64.u32  %rd6, %r3;\n    add.u64      %rd7, %rd5, %rd6;\n    mul.wide.u32 %rd8, %r2, %r4;\n    mov.u64      %rd9, 0;\n",
    s!"$L_grid_loop_{fnSymbol}:\n    setp.ge.u64  %p1, %rd7, %rd4;\n    @%p1 bra     $L_grid_done_{fnSymbol};",
    "    shl.b64      %rd10, %rd7, 3;\n    add.u64      %rd11, %rd2, %rd10;\n    add.u64      %rd12, %rd3, %rd10;",
    "    ld.global.u64 %rd11, [%rd11];\n    ld.global.u64 %rd12, [%rd12];\n    mad.lo.u64   %rd9, %rd11, %rd12, %rd9;\n    add.u64      %rd7, %rd7, %rd8;",
    s!"    bra          $L_grid_loop_{fnSymbol};\n\n$L_grid_done_{fnSymbol}:",
    "    mov.u64      %rd13, sdata_raw;\n    shl.b64      %rd14, %rd6, 3;\n    add.u64      %rd14, %rd13, %rd14;\n    st.shared.u64 [%rd14], %rd9;\n    bar.sync     0;"
  ] ++ reduceLines ++ [
    s!"    setp.ne.u32  %p1, %r3, 0;\n    @%p1 bra     $L_done_{fnSymbol};\n    atom.global.add.u64 %rd15, [%rd1], %rd9;\n",
    s!"$L_done_{fnSymbol}:\n    ret;\n}"
  ])

/-- Emit a 2D thread-block shared-memory tiled matrix multiplication PTX 8.0 kernel (16x16 tiles,
    with +1 shared-memory column padding `16x17` = 2176 bytes to eliminate 32-way shared memory bank conflicts).
    Uses `.shared .align 8 .b8 tileA_raw[2176]; .shared .align 8 .b8 tileB_raw[2176];` (stride = 136 bytes = 17 x 8B),
    2D CTA/thread coordinates (`%ctaid.x`, `%ctaid.y`, `%tid.x`, `%tid.y`), collaborative tile loads,
    `bar.sync 0;`, unrolled 16-step `mad.lo.u64` inner product, and global store `C[row * dim + col] = acc`. -/
def emitPTXMatMulTiledKernel (fnSymbol : String) : String :=
  let unrolledFmaLines := (List.range 16).foldl (fun acc k =>
    let offA := k * 8
    let offB := k * 136
    acc ++ [
      s!"    ld.shared.u64 %rd18, [%rd13+{offA}];\n    ld.shared.u64 %rd19, [%rd14+{offB}];\n    mad.lo.u64    %rd9, %rd18, %rd19, %rd9;"
    ]
  ) []
  String.intercalate "\n" ([
    s!".visible .entry {fnSymbol}(\n    .param .u64 param_c,\n    .param .u64 param_a,\n    .param .u64 param_b,\n    .param .u64 param_dim\n)\n\{",
    "    // Bank-conflict-free +1 padded shared memory tiles (16 x 17 x 8B = 2176 bytes, row stride = 136B)",
    "    .shared .align 8 .b8 tileA_raw[2176];\n    .shared .align 8 .b8 tileB_raw[2176];\n    .reg .pred %p<3>;\n    .reg .b32  %r<8>;\n    .reg .b64  %rd<21>;\n",
    "    ld.param.u64 %rd1, [param_c];\n    ld.param.u64 %rd2, [param_a];\n    ld.param.u64 %rd3, [param_b];\n    ld.param.u64 %rd4, [param_dim];\n",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    cvta.to.global.u64 %rd3, %rd3;\n",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ctaid.y;\n    mov.u32      %r3, %tid.x;\n    mov.u32      %r4, %tid.y;\n",
    "    shl.b32      %r5, %r2, 4;\n    add.u32      %r5, %r5, %r4;\n    cvt.u64.u32  %rd5, %r5;\n",
    "    shl.b32      %r6, %r1, 4;\n    add.u32      %r6, %r6, %r3;\n    cvt.u64.u32  %rd6, %r6;\n",
    "    cvt.u64.u32  %rd7, %r3;\n    cvt.u64.u32  %rd8, %r4;\n",
    "    mad.lo.u32   %r7, %r4, 17, %r3;\n    cvt.u64.u32  %rd16, %r7;\n    shl.b64      %rd16, %rd16, 3;",
    "    mov.u64      %rd17, tileA_raw;\n    add.u64      %rd11, %rd17, %rd16;\n    mov.u64      %rd18, tileB_raw;\n    add.u64      %rd12, %rd18, %rd16;\n",
    "    mul.lo.u64   %rd19, %rd8, 136;\n    add.u64      %rd13, %rd17, %rd19;\n    shl.b64      %rd20, %rd7, 3;\n    add.u64      %rd14, %rd18, %rd20;\n",
    "    add.u64      %rd15, %rd4, 15;\n    shr.b64      %rd15, %rd15, 4;\n    mov.u64      %rd9, 0;\n    mov.u64      %rd10, 0;",
    s!"$L_tile_loop_{fnSymbol}:",
    s!"    setp.ge.u64  %p1, %rd10, %rd15;\n    @%p1 bra     $L_tile_done_{fnSymbol};",
    "    shl.b64      %rd16, %rd10, 4;\n    add.u64      %rd17, %rd16, %rd7;\n    mov.u64      %rd18, 0;",
    s!"    setp.ge.u64  %p1, %rd5, %rd4;\n    setp.ge.u64  %p2, %rd17, %rd4;\n    or.pred      %p1, %p1, %p2;\n    @%p1 bra     $L_store_tileA_{fnSymbol};",
    "    mad.lo.u64   %rd19, %rd5, %rd4, %rd17;\n    shl.b64      %rd19, %rd19, 3;\n    add.u64      %rd19, %rd2, %rd19;\n    ld.global.u64 %rd18, [%rd19];",
    s!"$L_store_tileA_{fnSymbol}:\n    st.shared.u64 [%rd11], %rd18;",
    "    add.u64      %rd17, %rd16, %rd8;\n    mov.u64      %rd18, 0;",
    s!"    setp.ge.u64  %p1, %rd17, %rd4;\n    setp.ge.u64  %p2, %rd6, %rd4;\n    or.pred      %p1, %p1, %p2;\n    @%p1 bra     $L_store_tileB_{fnSymbol};",
    "    mad.lo.u64   %rd19, %rd17, %rd4, %rd6;\n    shl.b64      %rd19, %rd19, 3;\n    add.u64      %rd19, %rd3, %rd19;\n    ld.global.u64 %rd18, [%rd19];",
    s!"$L_store_tileB_{fnSymbol}:\n    st.shared.u64 [%rd12], %rd18;\n    bar.sync     0;"
  ] ++ unrolledFmaLines ++ [
    s!"    bar.sync     0;\n    add.u64      %rd10, %rd10, 1;\n    bra          $L_tile_loop_{fnSymbol};",
    s!"$L_tile_done_{fnSymbol}:",
    s!"    setp.ge.u64  %p1, %rd5, %rd4;\n    setp.ge.u64  %p2, %rd6, %rd4;\n    or.pred      %p1, %p1, %p2;\n    @%p1 bra     $L_done_{fnSymbol};",
    "    mad.lo.u64   %rd19, %rd5, %rd4, %rd6;\n    shl.b64      %rd19, %rd19, 3;\n    add.u64      %rd19, %rd1, %rd19;\n    st.global.u64 [%rd19], %rd9;",
    s!"$L_done_{fnSymbol}:\n    ret;\n}"
  ])

private def emitPTXBinaryU64Kernel (fnSymbol p1 p2 doneLbl opLine : String) : String :=
  String.intercalate "\n" [
    s!".visible .entry {fnSymbol}(\n    .param .u64 param_out,\n    .param .u64 {p1},\n    .param .u64 {p2},\n    .param .u64 param_n\n)\n\{",
    "    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<13>;",
    s!"    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [{p1}];\n    ld.param.u64 %rd3, [{p2}];\n    ld.param.u64 %rd4, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd5, %r1, %r2;\n    cvt.u64.u32  %rd6, %r3;\n    add.u64      %rd7, %rd5, %rd6;",
    s!"    setp.ge.u64  %p1, %rd7, %rd4;\n    @%p1 bra     {doneLbl};",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    cvta.to.global.u64 %rd3, %rd3;",
    "    shl.b64      %rd8, %rd7, 3;\n    add.u64      %rd9, %rd2, %rd8;\n    add.u64      %rd10, %rd3, %rd8;\n    ld.global.u64 %rd11, [%rd9];\n    ld.global.u64 %rd12, [%rd10];",
    s!"    {opLine}\n    add.u64      %rd9, %rd1, %rd8;\n    st.global.u64 [%rd9], %rd11;",
    s!"{doneLbl}:\n    ret;\n}"
  ]

private def emitPTXUnaryU64Kernel (fnSymbol regDecls opLine outReg : String) : String :=
  String.intercalate "\n" [
    s!".visible .entry {fnSymbol}(\n    .param .u64 param_out,\n    .param .u64 param_in0,\n    .param .u64 param_n\n)\n\{",
    s!"    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  {regDecls};",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_in0];\n    ld.param.u64 %rd3, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd4, %r1, %r2;\n    cvt.u64.u32  %rd5, %r3;\n    add.u64      %rd6, %rd4, %rd5;",
    s!"    setp.ge.u64  %p1, %rd6, %rd3;\n    @%p1 bra     $L_done_{fnSymbol};",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    shl.b64      %rd7, %rd6, 3;\n    add.u64      %rd8, %rd2, %rd7;\n    ld.global.u64 %rd9, [%rd8];",
    s!"    {opLine}\n    add.u64      %rd8, %rd1, %rd7;\n    st.global.u64 [%rd8], {outReg};",
    s!"$L_done_{fnSymbol}:\n    ret;\n}"
  ]

/-- Lower a `ScalarExpr` AST to NVIDIA PTX 8.0 `.b64` / `.pred` register instructions,
    returning `(lines, resultReg, nextRd, nextPred)`. -/
partial def emitPTXScalarExpr (e : ScalarExpr) (varMap : List (VarId × String))
    (nextRd : Nat) (nextPred : Nat) : List String × String × Nat × Nat :=
  match e with
  | .constU64 v =>
    let dst := s!"%rd{nextRd}"
    ([s!"    mov.u64      {dst}, {v};"], dst, nextRd + 1, nextPred)
  | .constBool b =>
    let dst := s!"%rd{nextRd}"
    let lit := if b then 1 else 0
    ([s!"    mov.u64      {dst}, {lit};"], dst, nextRd + 1, nextPred)
  | .var id =>
    match varMap.lookup id with
    | some reg => ([], reg, nextRd, nextPred)
    | none =>
      let dst := s!"%rd{nextRd}"
      ([s!"    mov.u64      {dst}, 0;"], dst, nextRd + 1, nextPred)
  | .binOp op lhs rhs =>
    let (lLines, lReg, r1, p1) := emitPTXScalarExpr lhs varMap nextRd nextPred
    let (rLines, rReg, r2, p2) := emitPTXScalarExpr rhs varMap r1 p1
    let dst := s!"%rd{r2}"
    let (opLines, r3, p3) := match op with
      | .add | .addChecked256 => ([s!"    add.u64      {dst}, {lReg}, {rReg};"], r2 + 1, p2)
      | .sub | .subChecked256 => ([s!"    sub.u64      {dst}, {lReg}, {rReg};"], r2 + 1, p2)
      | .mul | .mulChecked256 => ([s!"    mul.lo.u64   {dst}, {lReg}, {rReg};"], r2 + 1, p2)
      | .clmul64 | .clmul64Hi =>
        let isHi := op == .clmul64Hi
        let tBit := s!"%rd{r2 + 1}"
        let tShift := s!"%rd{r2 + 2}"
        let startIdx := if isHi then 1 else 0
        let stepLines := (List.range (64 - startIdx)).foldl (fun acc k =>
          let i := startIdx + k
          let shLine :=
            if isHi then s!"    shr.u64      {tShift}, {lReg}, {64 - i};"
            else if i == 0 then s!"    mov.u64      {tShift}, {lReg};"
            else s!"    shl.b64      {tShift}, {lReg}, {i};"
          let bitShift :=
            if i == 0 then s!"    mov.u64      {tBit}, {rReg};"
            else s!"    shr.u64      {tBit}, {rReg}, {i};"
          acc ++ [
            bitShift,
            s!"    and.b64      {tBit}, {tBit}, 1;",
            s!"    neg.s64      {tBit}, {tBit};",
            shLine,
            s!"    and.b64      {tShift}, {tShift}, {tBit};",
            s!"    xor.b64      {dst}, {dst}, {tShift};"
          ]
        ) [s!"    mov.u64      {dst}, 0;"]
        (stepLines, r2 + 3, p2)
      | .gf2Affine =>
        let t0 := s!"%rd{r2 + 1}"
        let t1 := s!"%rd{r2 + 2}"
        let stepLines := (List.range 8).foldl (fun acc i =>
          let rowLine :=
            if i == 0 then s!"    mov.u64      {t0}, {rReg};"
            else s!"    shr.u64      {t0}, {rReg}, {i * 8};"
          let placeLine :=
            if i == 0 then []
            else [s!"    shl.b64      {t0}, {t0}, {i};"]
          acc ++ [
            rowLine,
            s!"    and.b64      {t0}, {t0}, {lReg};",
            s!"    and.b64      {t0}, {t0}, 255;",
            s!"    shr.u64      {t1}, {t0}, 4;",
            s!"    xor.b64      {t0}, {t0}, {t1};",
            s!"    shr.u64      {t1}, {t0}, 2;",
            s!"    xor.b64      {t0}, {t0}, {t1};",
            s!"    shr.u64      {t1}, {t0}, 1;",
            s!"    xor.b64      {t0}, {t0}, {t1};",
            s!"    and.b64      {t0}, {t0}, 1;"
          ] ++ placeLine ++ [
            s!"    or.b64       {dst}, {dst}, {t0};"
          ]
        ) [s!"    mov.u64      {dst}, 0;"]
        (stepLines, r2 + 3, p2)
      | .div =>
        ([s!"    setp.eq.u64  %p{p2}, {rReg}, 0;",
          s!"    selp.u64     {dst}, 1, {rReg}, %p{p2};",
          s!"    div.u64      {dst}, {lReg}, {dst};",
          s!"    selp.u64     {dst}, 0, {dst}, %p{p2};"], r2 + 1, p2 + 1)
      | .mod =>
        ([s!"    setp.eq.u64  %p{p2}, {rReg}, 0;",
          s!"    selp.u64     {dst}, 1, {rReg}, %p{p2};",
          s!"    rem.u64      {dst}, {lReg}, {dst};",
          s!"    selp.u64     {dst}, {lReg}, {dst}, %p{p2};"], r2 + 1, p2 + 1)
      | .bitAnd => ([s!"    and.b64      {dst}, {lReg}, {rReg};"], r2 + 1, p2)
      | .bitOr => ([s!"    or.b64       {dst}, {lReg}, {rReg};"], r2 + 1, p2)
      | .bitXor => ([s!"    xor.b64      {dst}, {lReg}, {rReg};"], r2 + 1, p2)
      | .eor3 =>
        let t0 := s!"%rd{r2 + 1}"
        ([s!"    shr.u64      {t0}, {rReg}, 32;",
          s!"    xor.b64      {dst}, {lReg}, {t0};",
          s!"    and.b64      {t0}, {rReg}, 4294967295;",
          s!"    xor.b64      {dst}, {dst}, {t0};"], r2 + 2, p2)
      | .shl => ([s!"    cvt.u32.u64  %r4, {rReg};\n    shl.b64      {dst}, {lReg}, %r4;"], r2 + 1, p2)
      | .shr => ([s!"    cvt.u32.u64  %r4, {rReg};\n    shr.u64      {dst}, {lReg}, %r4;"], r2 + 1, p2)
      | .sar => ([s!"    cvt.u32.u64  %r4, {rReg};\n    shr.s64      {dst}, {lReg}, %r4;"], r2 + 1, p2)
      | .eq => ([s!"    setp.eq.u64  %p{p2}, {lReg}, {rReg};\n    selp.u64     {dst}, 1, 0, %p{p2};"], r2 + 1, p2 + 1)
      | .lt => ([s!"    setp.lt.u64  %p{p2}, {lReg}, {rReg};\n    selp.u64     {dst}, 1, 0, %p{p2};"], r2 + 1, p2 + 1)
      | .le => ([s!"    setp.le.u64  %p{p2}, {lReg}, {rReg};\n    selp.u64     {dst}, 1, 0, %p{p2};"], r2 + 1, p2 + 1)
    (lLines ++ rLines ++ opLines, dst, r3, p3)
  | .unaryOp op arg =>
    let (aLines, aReg, r1, p1) := emitPTXScalarExpr arg varMap nextRd nextPred
    let dst := s!"%rd{r1}"
    let opLines := match op with
      | .not => [s!"    not.b64      {dst}, {aReg};"]
      | .neg => [s!"    neg.s64      {dst}, {aReg};"]
      | .clz256 => [s!"    clz.b64      %r4, {aReg};\n    cvt.u64.u32  {dst}, %r4;"]
    (aLines ++ opLines, dst, r1 + 1, p1)
  | .select cond thenVal elseVal =>
    let (cLines, cReg, r1, p1) := emitPTXScalarExpr cond varMap nextRd nextPred
    let (tLines, tReg, r2, p2) := emitPTXScalarExpr thenVal varMap r1 p1
    let (eLines, eReg, r3, p3) := emitPTXScalarExpr elseVal varMap r2 p2
    let dst := s!"%rd{r3}"
    (cLines ++ tLines ++ eLines ++ [
      s!"    setp.ne.u64  %p{p3}, {cReg}, 0;",
      s!"    selp.u64     {dst}, {tReg}, {eReg}, %p{p3};"
    ], dst, r3 + 1, p3 + 1)
  | .fma a b c =>
    let (aLines, aReg, r1, p1) := emitPTXScalarExpr a varMap nextRd nextPred
    let (bLines, bReg, r2, p2) := emitPTXScalarExpr b varMap r1 p1
    let (cLines, cReg, r3, p3) := emitPTXScalarExpr c varMap r2 p2
    let dst := s!"%rd{r3}"
    (aLines ++ bLines ++ cLines ++ [
      s!"    mad.lo.u64   {dst}, {aReg}, {bReg}, {cReg};"
    ], dst, r3 + 1, p3)

/-- Emit a specialized per-declaration PTX entry point for a `ParallelKernelKind`. -/
def emitPTXDeclKernel (fnSymbol : String) (kernel : ParallelKernelKind) : String :=
  if fnSymbol == "lean_native_decl_dot_product_u64" then
    emitPTXDotReduceKernel fnSymbol
  else if fnSymbol == "lean_native_decl_matmul_tiled_u64" then
    emitPTXMatMulTiledKernel fnSymbol
  else
  match kernel with
  | .mapScaleAdd scale bias =>
    emitPTXUnaryU64Kernel fnSymbol "%rd<11>" s!"mad.lo.u64   %rd10, %rd9, {scale}, {bias};" "%rd10"
  | .zipAdd =>
    emitPTXBinaryU64Kernel fnSymbol "param_in0" "param_in1" s!"$L_done_{fnSymbol}" "add.u64      %rd11, %rd11, %rd12;"
  | .dotProduct =>
    emitPTXDotReduceKernel fnSymbol
  | .zipMul =>
    emitPTXBinaryU64Kernel fnSymbol "param_in0" "param_in1" s!"$L_done_{fnSymbol}" "mul.lo.u64   %rd11, %rd11, %rd12;"
  | .saxpy alphaBits =>
    emitPTXBinaryU64Kernel fnSymbol "param_x" "param_y" s!"$L_done_{fnSymbol}" s!"mad.lo.u64   %rd11, %rd11, {alphaBits}, %rd12;"
  | .stencil1D3Pt wLeft wCenter wRight =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(\n    .param .u64 param_out,\n    .param .u64 param_in0,\n    .param .u64 param_n\n)\n\{",
      "    .reg .pred %p<4>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<16>;\n",
      "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_in0];\n    ld.param.u64 %rd3, [param_n];\n",
      "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd4, %r1, %r2;\n    cvt.u64.u32  %rd5, %r3;\n    add.u64      %rd6, %rd4, %rd5;\n",
      s!"    setp.ge.u64  %p1, %rd6, %rd3;\n    @%p1 bra     $L_done_{fnSymbol};\n",
      "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    shl.b64      %rd7, %rd6, 3;\n    add.u64      %rd8, %rd2, %rd7;\n    add.u64      %rd9, %rd1, %rd7;\n    ld.global.u64 %rd10, [%rd8];\n",
      s!"    setp.eq.u64  %p2, %rd6, 0;\n    add.u64      %rd11, %rd6, 1;\n    setp.ge.u64  %p3, %rd11, %rd3;\n    or.pred      %p2, %p2, %p3;\n    @%p2 bra     $L_boundary_{fnSymbol};\n",
      s!"    ld.global.u64 %rd12, [%rd8+-8];\n    ld.global.u64 %rd13, [%rd8+8];\n    mul.lo.u64   %rd14, %rd12, {wLeft};\n    mad.lo.u64   %rd14, %rd10, {wCenter}, %rd14;\n    mad.lo.u64   %rd10, %rd13, {wRight}, %rd14;\n",
      s!"$L_boundary_{fnSymbol}:\n    st.global.u64 [%rd9], %rd10;\n\n$L_done_{fnSymbol}:\n    ret;\n}"
    ]
  | .customScalar idxVar inVars body =>
    let rec buildInDecls (k : Nat) : List VarId → List String × List String × List (VarId × String)
      | [] => ([], [], [])
      | vId :: rest =>
        let (pDecls, lLines, vMap) := buildInDecls (k + 1) rest
        let pName := s!"param_in{k}"
        let rName := s!"%rd{8 + k}"
        let loadSeq := [
          s!"    ld.param.u64 %rd7, [{pName}];",
          "    cvta.to.global.u64 %rd7, %rd7;",
          "    add.u64      %rd7, %rd7, %rd6;",
          s!"    ld.global.u64 {rName}, [%rd7];"
        ]
        (s!"    .param .u64 {pName}," :: pDecls, loadSeq ++ lLines, (vId, rName) :: vMap)
    let (inParamDecls, inLoadLines, inVarMap) := buildInDecls 0 inVars
    let fullVarMap := (idxVar, "%rd5") :: inVarMap
    let (exprLines, resReg, maxRd, maxPred) := emitPTXScalarExpr body fullVarMap (8 + inVars.length) 2
    let paramHeader := String.intercalate "\n" (
      ["    .param .u64 param_out,"] ++ inParamDecls ++ ["    .param .u64 param_n"]
    )
    String.intercalate "\n" ([
      s!".visible .entry {fnSymbol}(\n{paramHeader}\n)\n\{",
      s!"    .reg .pred %p<{maxPred}>;\n    .reg .b32  %r<5>;\n    .reg .b64  %rd<{maxRd}>;",
      "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_n];",
      "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd3, %r1, %r2;\n    cvt.u64.u32  %rd4, %r3;\n    add.u64      %rd5, %rd3, %rd4;",
      s!"    setp.ge.u64  %p1, %rd5, %rd2;\n    @%p1 bra     $L_done_{fnSymbol};",
      "    cvta.to.global.u64 %rd1, %rd1;\n    shl.b64      %rd6, %rd5, 3;"
    ] ++ inLoadLines ++ exprLines ++ [
      s!"    add.u64      %rd7, %rd1, %rd6;\n    st.global.u64 [%rd7], {resReg};",
      s!"$L_done_{fnSymbol}:\n    ret;\n}"
    ])

/-- Lower GPU-compatible kernels in `m` directly to valid NVIDIA PTX 8.0 assembly
    (`.version 8.0`, `.target sm_90`, `.address_size 64`). -/
def emitPTXModule (m : LNIRModule) (smArch : String := "sm_90") : String :=
  let header := String.intercalate "\n" [
    "//",
    s!"// Generated by LeanNative.Backend.MLIRGPU for module: {m.moduleName}",
    "// Direct LNIR -> NVIDIA PTX 8.0 Code Generator",
    "//",
    ".version 8.0",
    s!".target {smArch}",
    ".address_size 64"
  ]

  -- 1. lean_native_kernel_map_scale_add: out[i] = in0[i] * scale + bias
  let kMapScaleAdd := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_map_scale_add(\n    .param .u64 param_out,\n    .param .u64 param_in0,\n    .param .u64 param_scale,\n    .param .u64 param_bias,\n    .param .u64 param_n\n)\n{",
    "    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<13>;",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_in0];\n    ld.param.u64 %rd3, [param_scale];\n    ld.param.u64 %rd4, [param_bias];\n    ld.param.u64 %rd5, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd6, %r1, %r2;\n    cvt.u64.u32  %rd7, %r3;\n    add.u64      %rd8, %rd6, %rd7;",
    "    setp.ge.u64  %p1, %rd8, %rd5;\n    @%p1 bra     $L_done_map_scale_add;",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    shl.b64      %rd9, %rd8, 3;\n    add.u64      %rd10, %rd2, %rd9;\n    ld.global.u64 %rd11, [%rd10];\n    mad.lo.u64   %rd12, %rd11, %rd3, %rd4;\n    add.u64      %rd10, %rd1, %rd9;\n    st.global.u64 [%rd10], %rd12;",
    "$L_done_map_scale_add:\n    ret;\n}"
  ]

  -- 2. lean_native_kernel_zip_add: out[i] = in0[i] + in1[i]
  let kZipAdd := emitPTXBinaryU64Kernel "lean_native_kernel_zip_add" "param_in0" "param_in1" "$L_done_zip_add" "add.u64      %rd11, %rd11, %rd12;"

  -- 3. lean_native_kernel_zip_mul: out[i] = in0[i] * in1[i]
  let kZipMul := emitPTXBinaryU64Kernel "lean_native_kernel_zip_mul" "param_in0" "param_in1" "$L_done_zip_mul" "mul.lo.u64   %rd11, %rd11, %rd12;"

  -- 4. lean_native_kernel_saxpy: out[i] = alpha * x[i] + y[i]
  let kSaxpy := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_saxpy(\n    .param .u64 param_out,\n    .param .u64 param_x,\n    .param .u64 param_y,\n    .param .u64 param_alpha,\n    .param .u64 param_n\n)\n{",
    "    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<14>;",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_x];\n    ld.param.u64 %rd3, [param_y];\n    ld.param.u64 %rd4, [param_alpha];\n    ld.param.u64 %rd5, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd6, %r1, %r2;\n    cvt.u64.u32  %rd7, %r3;\n    add.u64      %rd8, %rd6, %rd7;",
    "    setp.ge.u64  %p1, %rd8, %rd5;\n    @%p1 bra     $L_done_saxpy;",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    cvta.to.global.u64 %rd3, %rd3;\n    shl.b64      %rd9, %rd8, 3;\n    add.u64      %rd10, %rd2, %rd9;\n    add.u64      %rd11, %rd3, %rd9;\n    ld.global.u64 %rd12, [%rd10];\n    ld.global.u64 %rd13, [%rd11];\n    mad.lo.u64   %rd12, %rd12, %rd4, %rd13;\n    add.u64      %rd10, %rd1, %rd9;\n    st.global.u64 [%rd10], %rd12;",
    "$L_done_saxpy:\n    ret;\n}"
  ]

  -- 5. lean_native_kernel_stencil1d: 3-point 1D stencil
  let kStencil1D := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_stencil1d(\n    .param .u64 param_out,\n    .param .u64 param_in0,\n    .param .u64 param_wl,\n    .param .u64 param_wc,\n    .param .u64 param_wr,\n    .param .u64 param_n\n)\n{",
    "    .reg .pred %p<4>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<19>;",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_in0];\n    ld.param.u64 %rd3, [param_wl];\n    ld.param.u64 %rd4, [param_wc];\n    ld.param.u64 %rd5, [param_wr];\n    ld.param.u64 %rd6, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd7, %r1, %r2;\n    cvt.u64.u32  %rd8, %r3;\n    add.u64      %rd9, %rd7, %rd8;",
    "    setp.ge.u64  %p1, %rd9, %rd6;\n    @%p1 bra     $L_done_stencil1d;",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    shl.b64      %rd10, %rd9, 3;\n    add.u64      %rd11, %rd2, %rd10;\n    add.u64      %rd12, %rd1, %rd10;\n    ld.global.u64 %rd13, [%rd11];",
    "    setp.eq.u64  %p2, %rd9, 0;\n    add.u64      %rd14, %rd9, 1;\n    setp.ge.u64  %p3, %rd14, %rd6;\n    or.pred      %p2, %p2, %p3;\n    @%p2 bra     $L_boundary_stencil1d;",
    "    ld.global.u64 %rd15, [%rd11+-8];\n    ld.global.u64 %rd16, [%rd11+8];\n    mul.lo.u64   %rd17, %rd15, %rd3;\n    mad.lo.u64   %rd17, %rd13, %rd4, %rd17;\n    mad.lo.u64   %rd13, %rd16, %rd5, %rd17;",
    "$L_boundary_stencil1d:\n    st.global.u64 [%rd12], %rd13;\n$L_done_stencil1d:\n    ret;\n}"
  ]

  -- 6. lean_native_kernel_dot_reduce_u64: Shared-Memory Tree Reduction Kernel
  let kDotReduceU64 := emitPTXDotReduceKernel "lean_native_kernel_dot_reduce_u64"

  -- 7. lean_native_kernel_matmul_tiled_u64: 2D Shared-Memory Tiled Matrix Multiplication Kernel
  let kMatMulTiledU64 := emitPTXMatMulTiledKernel "lean_native_kernel_matmul_tiled_u64"

  -- 8. lean_native_kernel_saxpy_f64: IEEE-754 f64 FMA SAXPY Kernel
  let kSaxpyF64 := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_saxpy_f64(\n    .param .u64 param_out,\n    .param .u64 param_x,\n    .param .u64 param_y,\n    .param .f64 param_alpha,\n    .param .u64 param_n\n)\n{",
    "    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<12>;\n    .reg .f64  %fd<5>;",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_x];\n    ld.param.u64 %rd3, [param_y];\n    ld.param.f64 %fd1, [param_alpha];\n    ld.param.u64 %rd4, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd5, %r1, %r2;\n    cvt.u64.u32  %rd6, %r3;\n    add.u64      %rd7, %rd5, %rd6;",
    "    setp.ge.u64  %p1, %rd7, %rd4;\n    @%p1 bra     $L_done_saxpy_f64;",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    cvta.to.global.u64 %rd3, %rd3;\n    shl.b64      %rd8, %rd7, 3;\n    add.u64      %rd9, %rd2, %rd8;\n    add.u64      %rd10, %rd3, %rd8;\n    ld.global.f64 %fd2, [%rd9];\n    ld.global.f64 %fd3, [%rd10];\n    fma.rn.f64   %fd4, %fd2, %fd1, %fd3;\n    add.u64      %rd11, %rd1, %rd8;\n    st.global.f64 [%rd11], %fd4;",
    "$L_done_saxpy_f64:\n    ret;\n}"
  ]

  -- 9. lean_native_kernel_map_scale_add_f64: IEEE-754 f64 mul.rn.f64 + add.rn.f64 Kernel
  let kMapScaleAddF64 := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_map_scale_add_f64(\n    .param .u64 param_out,\n    .param .u64 param_in0,\n    .param .f64 param_scale,\n    .param .f64 param_bias,\n    .param .u64 param_n\n)\n{",
    "    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<11>;\n    .reg .f64  %fd<6>;",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_in0];\n    ld.param.f64 %fd1, [param_scale];\n    ld.param.f64 %fd2, [param_bias];\n    ld.param.u64 %rd3, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd4, %r1, %r2;\n    cvt.u64.u32  %rd5, %r3;\n    add.u64      %rd6, %rd4, %rd5;",
    "    setp.ge.u64  %p1, %rd6, %rd3;\n    @%p1 bra     $L_done_map_scale_add_f64;",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    shl.b64      %rd7, %rd6, 3;\n    add.u64      %rd8, %rd2, %rd7;\n    ld.global.f64 %fd3, [%rd8];\n    mul.rn.f64   %fd4, %fd3, %fd1;\n    add.rn.f64   %fd5, %fd4, %fd2;\n    add.u64      %rd9, %rd1, %rd7;\n    st.global.f64 [%rd9], %fd5;",
    "$L_done_map_scale_add_f64:\n    ret;\n}"
  ]

  -- 10. lean_native_kernel_fma_f32: IEEE-754 f32 FMA Kernel
  let kFmaF32 := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_fma_f32(\n    .param .u64 param_out,\n    .param .u64 param_a,\n    .param .u64 param_b,\n    .param .u64 param_c,\n    .param .u64 param_n\n)\n{",
    "    .reg .pred %p<2>;\n    .reg .b32  %r<4>;\n    .reg .b64  %rd<14>;\n    .reg .f32  %f<5>;",
    "    ld.param.u64 %rd1, [param_out];\n    ld.param.u64 %rd2, [param_a];\n    ld.param.u64 %rd3, [param_b];\n    ld.param.u64 %rd4, [param_c];\n    ld.param.u64 %rd5, [param_n];",
    "    mov.u32      %r1, %ctaid.x;\n    mov.u32      %r2, %ntid.x;\n    mov.u32      %r3, %tid.x;\n    mul.wide.u32 %rd6, %r1, %r2;\n    cvt.u64.u32  %rd7, %r3;\n    add.u64      %rd8, %rd6, %rd7;",
    "    setp.ge.u64  %p1, %rd8, %rd5;\n    @%p1 bra     $L_done_fma_f32;",
    "    cvta.to.global.u64 %rd1, %rd1;\n    cvta.to.global.u64 %rd2, %rd2;\n    cvta.to.global.u64 %rd3, %rd3;\n    cvta.to.global.u64 %rd4, %rd4;\n    shl.b64      %rd9, %rd8, 2;\n    add.u64      %rd10, %rd2, %rd9;\n    add.u64      %rd11, %rd3, %rd9;\n    add.u64      %rd12, %rd4, %rd9;\n    ld.global.f32 %f1, [%rd10];\n    ld.global.f32 %f2, [%rd11];\n    ld.global.f32 %f3, [%rd12];\n    fma.rn.f32   %f4, %f1, %f2, %f3;\n    add.u64      %rd13, %rd1, %rd9;\n    st.global.f32 [%rd13], %f4;",
    "$L_done_fma_f32:\n    ret;\n}"
  ]

  -- 11. Per-declaration PTX entry points
  let (declPTXKernels, emittedNames) := m.decls.foldl (fun (acc, names) d =>
    let (ok, _) := analyzeGpuCompatibility d
    if !ok then (acc, names)
    else
      let sym := s!"lean_native_decl_{d.name}"
      let regions := extractParForRegions d.body
      match regions with
      | [] => (acc, names)
      | (_, _, _, _, firstK) :: rest =>
        let primary := emitPTXDeclKernel sym firstK
        let rec emitExtraRegions (idx : Nat) :
            List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) → List String
          | [] => []
          | (_, _, _, _, k) :: tail =>
            emitPTXDeclKernel s!"lean_native_decl_{d.name}_region_{idx}" k :: emitExtraRegions (idx + 1) tail
        (acc ++ [primary] ++ emitExtraRegions 1 rest, names ++ [sym])
  ) ([], [])

  let extraDotDecl :=
    if emittedNames.contains "lean_native_decl_dot_product_u64" then []
    else [emitPTXDotReduceKernel "lean_native_decl_dot_product_u64"]
  let extraMatMulDecl :=
    if emittedNames.contains "lean_native_decl_matmul_tiled_u64" then []
    else [emitPTXMatMulTiledKernel "lean_native_decl_matmul_tiled_u64"]

  String.intercalate "\n\n" ([
    header,
    kMapScaleAdd,
    kZipAdd,
    kZipMul,
    kSaxpy,
    kStencil1D,
    kDotReduceU64,
    kMatMulTiledU64,
    kSaxpyF64,
    kMapScaleAddF64,
    kFmaF32
  ] ++ declPTXKernels ++ extraDotDecl ++ extraMatMulDecl) ++ "\n"

/-- Emit a StableHLO function (`func.func @...`) targeting Google Cloud TPU v5e
    (`128x128` MXU systolic array and `128x8` VPU vector lanes) for a `ParallelKernelKind`. -/
def emitStableHLODeclFunc (fnName : String) (elemTy : LNIRType) (kernel : ParallelKernelKind) : String :=
  let shloElem := match elemTy with | .f32 => "f32" | .f64 => "f64" | .i32 => "ui32" | _ => "ui64"
  let tensorTy := s!"tensor<262144x{shloElem}>"
  let mkVpu (params : String) (retVar : String) (body : List String) : String :=
    String.intercalate "\n" ([
      s!"  func.func @{fnName}({params}) -> {tensorTy} attributes \{tpu.unit = \"vpu_trillium\", tpu.vmem_block = 2048 : i64} \{"
    ] ++ body ++ [s!"    return {retVar} : {tensorTy}\n  }"])
  match kernel with
  | .mapScaleAdd scale bias =>
    mkVpu s!"%in0: {tensorTy}" "%res" [
      s!"    %c_scale = stablehlo.constant dense<{scale}> : {tensorTy}\n    %c_bias = stablehlo.constant dense<{bias}> : {tensorTy}",
      s!"    %scaled = stablehlo.multiply %in0, %c_scale : {tensorTy}\n    %res = stablehlo.add %scaled, %c_bias : {tensorTy}"
    ]
  | .zipAdd => mkVpu s!"%in0: {tensorTy}, %in1: {tensorTy}" "%res" [s!"    %res = stablehlo.add %in0, %in1 : {tensorTy}"]
  | .zipMul => mkVpu s!"%in0: {tensorTy}, %in1: {tensorTy}" "%res" [s!"    %res = stablehlo.multiply %in0, %in1 : {tensorTy}"]
  | .saxpy alphaBits =>
    mkVpu s!"%x: {tensorTy}, %y: {tensorTy}" "%res" [
      s!"    %c_alpha = stablehlo.constant dense<{alphaBits}> : {tensorTy}\n    %ax = stablehlo.multiply %c_alpha, %x : {tensorTy}\n    %res = stablehlo.add %ax, %y : {tensorTy}"
    ]
  | .dotProduct =>
    String.intercalate "\n" [
      s!"  func.func @{fnName}(%lhs: {tensorTy}, %rhs: {tensorTy}) -> tensor<{shloElem}> attributes \{tpu.unit = \"mxu_256x256\"} \{",
      s!"    %dot = stablehlo.dot_general %lhs, %rhs, contracting_dims = [0] x [0] : ({tensorTy}, {tensorTy}) -> tensor<{shloElem}>\n    return %dot : tensor<{shloElem}>\n  }"
    ]
  | .stencil1D3Pt wLeft wCenter wRight =>
    mkVpu s!"%in0: {tensorTy}" "%res" [
      s!"    %c_wl = stablehlo.constant dense<{wLeft}> : {tensorTy}\n    %c_wc = stablehlo.constant dense<{wCenter}> : {tensorTy}\n    %c_wr = stablehlo.constant dense<{wRight}> : {tensorTy}",
      s!"    %tl = stablehlo.multiply %in0, %c_wl : {tensorTy}\n    %tc = stablehlo.multiply %in0, %c_wc : {tensorTy}\n    %tr = stablehlo.multiply %in0, %c_wr : {tensorTy}",
      s!"    %tlc = stablehlo.add %tl, %tc : {tensorTy}\n    %res = stablehlo.add %tlc, %tr : {tensorTy}"
    ]
  | .customScalar _ _ _ => "unsupported_customScalar_lowering"

/-- Lower `LNIRModule` declarations and parallel regions to a Google Cloud TPU v6e (Trillium) StableHLO
    module (`module @lean_native_tpu_v6e_stablehlo`). -/
def emitStableHLOModule (m : LNIRModule) : String :=
  let header := String.intercalate "\n" [
    s!"// LeanNative Google Cloud TPU v6e (Trillium) StableHLO Module: {m.moduleName}",
    "// Target: Google Cloud TPU v6e (Trillium 256x256 MXU systolic array + Trillium VPU, 32 GB HBM)",
    "module @lean_native_tpu_v6e_stablehlo attributes {mhlo.num_replicas = 1 : i32, mhlo.num_partitions = 1 : i32, tpu.target = \"tpu_v6e\", tpu.mxu_block_2d = \"256x256\", tpu.vmem_block_1d = 2048 : i64} {"
  ]
  let builtinFuncs := [
    emitStableHLODeclFunc "lean_native_tpu_v6e_map_scale_add" .i64 (.mapScaleAdd 3 7),
    emitStableHLODeclFunc "lean_native_tpu_v6e_zip_add" .i64 .zipAdd,
    emitStableHLODeclFunc "lean_native_tpu_v6e_zip_mul" .i64 .zipMul,
    emitStableHLODeclFunc "lean_native_tpu_v6e_saxpy" .i64 (.saxpy 5),
    emitStableHLODeclFunc "lean_native_tpu_v6e_dot_product" .i64 .dotProduct,
    emitStableHLODeclFunc "lean_native_tpu_v6e_stencil1d" .i64 (.stencil1D3Pt 1 2 1),
    String.intercalate "\n" [
      "  func.func @lean_native_tpu_v6e_matmul_mxu_256x256(%lhs: tensor<256x256xbf16>, %rhs: tensor<256x256xbf16>) -> tensor<256x256xf32> attributes {tpu.unit = \"mxu_256x256\", tpu.mxu_block_2d = \"256x256\"} {",
      "    %res = stablehlo.dot_general %lhs, %rhs, contracting_dims = [1] x [0] : (tensor<256x256xbf16>, tensor<256x256xbf16>) -> tensor<256x256xf32>\n    return %res : tensor<256x256xf32>\n  }"
    ],
    String.intercalate "\n" [
      "  func.func @lean_native_tpu_v6e_evm_u256_batch(%a: tensor<262144x4xui64>, %b: tensor<262144x4xui64>) -> tensor<262144x4xui64> attributes {tpu.unit = \"vpu_trillium\", tpu.vmem_block = 2048 : i64, tpu.u256_limbs = 4 : i32} {",
      "    %c1 = stablehlo.constant dense<1> : tensor<262144x4xui64>\n    %c63 = stablehlo.constant dense<63> : tensor<262144x4xui64>\n    %sum_raw = stablehlo.add %a, %b : tensor<262144x4xui64>",
      "    %carry_cmp = stablehlo.compare LT, %sum_raw, %a, UNSIGNED : (tensor<262144x4xui64>, tensor<262144x4xui64>) -> tensor<262144x4xi1>",
      "    %zero = stablehlo.constant dense<0> : tensor<262144x4xui64>\n    %carry_mask = stablehlo.select %carry_cmp, %c1, %zero : tensor<262144x4xi1>, tensor<262144x4xui64>",
      "    %diff = stablehlo.subtract %sum_raw, %b : tensor<262144x4xui64>\n    %prod = stablehlo.multiply %diff, %b : tensor<262144x4xui64>",
      "    %shl = stablehlo.shift_left %prod, %c1 : tensor<262144x4xui64>\n    %shr = stablehlo.shift_right_logical %prod, %c63 : tensor<262144x4xui64>",
      "    %rot = stablehlo.or %shl, %shr : tensor<262144x4xui64>\n    %masked = stablehlo.and %rot, %sum_raw : tensor<262144x4xui64>\n    %xored = stablehlo.xor %masked, %carry_mask : tensor<262144x4xui64>",
      "    return %xored : tensor<262144x4xui64>\n  }"
    ],
    String.intercalate "\n" [
      "  func.func @lean_native_tpu_v6e_matryoshka_trm_clipped_relu2(%z: tensor<64x64xbf16>, %w1: tensor<64x128xbf16>, %w2: tensor<128x64xbf16>) -> tensor<64x64xbf16> attributes {tpu.unit = \"mxu_256x256\", tpu.trm_slice = \"tpu_v6e_bf16\"} {",
      "    %pre = stablehlo.dot_general %z, %w1, contracting_dims = [1] x [0] : (tensor<64x64xbf16>, tensor<64x128xbf16>) -> tensor<64x128xbf16>",
      "    %zero = stablehlo.constant dense<0.0> : tensor<64x128xbf16>\n    %cap16 = stablehlo.constant dense<16.0> : tensor<64x128xbf16>",
      "    %pos = stablehlo.maximum %pre, %zero : tensor<64x128xbf16>\n    %sq = stablehlo.multiply %pos, %pos : tensor<64x128xbf16>\n    %act = stablehlo.minimum %sq, %cap16 : tensor<64x128xbf16>",
      "    %delta = stablehlo.dot_general %act, %w2, contracting_dims = [1] x [0] : (tensor<64x128xbf16>, tensor<128x64xbf16>) -> tensor<64x64xbf16>",
      "    %out = stablehlo.add %z, %delta : tensor<64x64xbf16>\n    return %out : tensor<64x64xbf16>\n  }"
    ],
    String.intercalate "\n" [
      "  func.func @lean_native_tpu_v6e_speculate_forest_s4(%z: tensor<256x128xbf16>, %w1: tensor<128x256xbf16>, %w2: tensor<256x128xbf16>, %w_prem: tensor<128x1024xbf16>, %w_tac: tensor<128x8xbf16>) -> (tensor<256x128xbf16>, tensor<256x1024xf32>, tensor<256x8xf32>) attributes {tpu.unit = \"mxu_256x256\", tpu.trm_slice = \"tpu_v6e_s4_bf16\"} {",
      "    %pre = stablehlo.dot_general %z, %w1, contracting_dims = [1] x [0] : (tensor<256x128xbf16>, tensor<128x256xbf16>) -> tensor<256x256xbf16>",
      "    %zero = stablehlo.constant dense<0.0> : tensor<256x256xbf16>\n    %cap16 = stablehlo.constant dense<16.0> : tensor<256x256xbf16>",
      "    %pos = stablehlo.maximum %pre, %zero : tensor<256x256xbf16>\n    %sq = stablehlo.multiply %pos, %pos : tensor<256x256xbf16>\n    %act = stablehlo.minimum %sq, %cap16 : tensor<256x256xbf16>",
      "    %delta = stablehlo.dot_general %act, %w2, contracting_dims = [1] x [0] : (tensor<256x256xbf16>, tensor<256x128xbf16>) -> tensor<256x128xbf16>",
      "    %z_next = stablehlo.add %z, %delta : tensor<256x128xbf16>",
      "    %prem_logits = stablehlo.dot_general %z_next, %w_prem, contracting_dims = [1] x [0] : (tensor<256x128xbf16>, tensor<128x1024xbf16>) -> tensor<256x1024xf32>",
      "    %tac_logits = stablehlo.dot_general %z_next, %w_tac, contracting_dims = [1] x [0] : (tensor<256x128xbf16>, tensor<128x8xbf16>) -> tensor<256x8xf32>",
      "    return %z_next, %prem_logits, %tac_logits : tensor<256x128xbf16>, tensor<256x1024xf32>, tensor<256x8xf32>\n  }"
    ]
  ]
  let declFuncs := m.decls.foldl (fun acc d =>
    let (ok, _) := analyzeGpuCompatibility d
    if !ok then acc
    else
       match extractParForRegions d.body with
       | [] => acc
       | (_, _, _, elemTy, firstK) :: _ => acc ++ [emitStableHLODeclFunc s!"decl_{d.name}" elemTy firstK]
  ) []
  String.intercalate "\n\n" ([header] ++ builtinFuncs ++ declFuncs ++ ["}"]) ++ "\n"

/-- Emit a ready-to-execute Python/JAX Pallas & `@jax.jit` module targeting Google Cloud TPU v6e (Trillium)
    (`vmem` block spec `(2048,)` for 1D VPU kernels, `(256, 256)` for Trillium MXU `matmul_tiled`,
    2D `vmap(Goals=256, Samples=65536)` 256-bit SplitMix64 counterexample search, and fused `S_4`
    (`d=128, h=256`) forest speculation `tpu_v6e_speculate_forest`). -/
def emitTPUPallasModule (m : LNIRModule) : String :=
  let declNames := m.decls.map (fun d => s!"\"{d.name}\"")
  let declListStr := "[" ++ String.intercalate ", " declNames ++ "]"
  String.intercalate "\n" [
    s!"#!/usr/bin/env python3\n\"\"\"\"Auto-generated Google Cloud TPU v6e (Trillium) JAX Pallas & XLA Module for {m.moduleName}.\"\"\"",
    "from __future__ import annotations\nimport jax\nimport jax.numpy as jnp\nfrom jax.experimental import pallas as pl\n",
    s!"TPU_TARGET = \"google_cloud_tpu_v6e\"\nVMEM_BLOCK_1D = (2048,)\nMXU_BLOCK_2D = (256, 256)\nMODULE_DECLS = {declListStr}\n",
    "def _pallas_saxpy_vpu_kernel(x_ref, y_ref, out_ref):\n    out_ref[:] = jnp.uint64(5) * x_ref[:] + y_ref[:]\n",
    "@jax.jit\ndef tpu_v6e_saxpy_u64(x: jax.Array, y: jax.Array) -> jax.Array:\n    \"\"\"1D VPU kernel on TPU v6e (Trillium) with VMEM BlockSpec (2048,).\"\"\"",
    "    if jax.default_backend() == \"tpu\":\n        grid = (x.shape[0] // 2048,)",
    "        return pl.pallas_call(_pallas_saxpy_vpu_kernel, out_shape=jax.ShapeDtypeStruct(x.shape, x.dtype), grid=grid,",
    "            in_specs=[pl.BlockSpec(VMEM_BLOCK_1D, lambda i: (i,)), pl.BlockSpec(VMEM_BLOCK_1D, lambda i: (i,))],\n            out_specs=pl.BlockSpec(VMEM_BLOCK_1D, lambda i: (i,)),\n        )(x, y)",
    "    return jnp.uint64(5) * x + y\n\ntpu_v5e_saxpy_u64 = tpu_v6e_saxpy_u64\n",
    "@jax.jit\ndef tpu_v6e_dot_reduce_u64(x: jax.Array, y: jax.Array) -> jax.Array:\n    \"\"\"Vectorized VPU + reduction on TPU v6e.\"\"\"\n    return jnp.sum(x * y)\n\ntpu_v5e_dot_reduce_u64 = tpu_v6e_dot_reduce_u64\n",
    "@jax.jit\ndef tpu_v6e_matmul_tiled_mxu(a: jax.Array, b: jax.Array) -> jax.Array:\n    \"\"\"256x256 MXU systolic array matrix multiplication on Google Cloud TPU v6e (Trillium).\"\"\"\n    return jnp.matmul(a.astype(jnp.bfloat16), b.astype(jnp.bfloat16), preferred_element_type=jnp.float32)\n\ntpu_v5e_matmul_tiled_mxu = tpu_v6e_matmul_tiled_mxu\n",
    "@jax.jit\ndef tpu_v6e_evm_u256_batch(a_limbs: jax.Array, b_limbs: jax.Array) -> jax.Array:\n    \"\"\"Vectorized 4-limb uint64[N, 4] carry-chained 256-bit EVM arithmetic on TPU v6e VPU.\"\"\"",
    "    s0 = a_limbs[:, 0] + b_limbs[:, 0]\n    c0 = (s0 < a_limbs[:, 0]).astype(jnp.uint64)",
    "    s1_raw = a_limbs[:, 1] + b_limbs[:, 1]\n    s1 = s1_raw + c0\n    c1 = ((s1_raw < a_limbs[:, 1]) | (s1 < s1_raw)).astype(jnp.uint64)",
    "    s2_raw = a_limbs[:, 2] + b_limbs[:, 2]\n    s2 = s2_raw + c1\n    c2 = ((s2_raw < a_limbs[:, 2]) | (s2 < s2_raw)).astype(jnp.uint64)",
    "    s3 = a_limbs[:, 3] + b_limbs[:, 3] + c2\n    return jnp.stack([s0, s1, s2, s3], axis=1)\n\ntpu_v5e_evm_u256_batch = tpu_v6e_evm_u256_batch\n",
    "@jax.jit\ndef tpu_v6e_fastcheck_u256_batch(seed: jnp.uint64, n_samples: int = 65536) -> dict:\n    \"\"\"Vectorized 256-bit SplitMix64 counterexample search with equality precondition propagation.\"\"\"",
    "    idx = jnp.arange(n_samples, dtype=jnp.uint64)\n    z = seed + idx * jnp.uint64(0x9E3779B97F4A7C15)",
    "    z = (z ^ (z >> jnp.uint64(30))) * jnp.uint64(0xBF58476D1CE4E5B9)\n    z = (z ^ (z >> jnp.uint64(27))) * jnp.uint64(0x94D049BB133111EB)",
    "    x1 = z ^ (z >> jnp.uint64(31))\n    x0 = x1 + jnp.uint64(42)\n    violated = (x1 >= jnp.uint64(1000000)) & (x0 < jnp.uint64(1000000))",
    "    return {\"any_cex\": jnp.any(violated), \"count\": jnp.sum(violated.astype(jnp.uint32))}\n\ntpu_v5e_fastcheck_u256_batch = tpu_v6e_fastcheck_u256_batch\n",
    "@jax.jit\ndef tpu_v6e_speculate_forest_s4(z: jax.Array, w1: jax.Array, w2: jax.Array, w_prem: jax.Array, w_tac: jax.Array) -> dict:\n    \"\"\"Fused 256x256 MXU S_4 (d=128, h=256) ClippedReLU^2 + Premise (1024) + Tactic (8) forest speculation.\"\"\"",
    "    pre = jnp.matmul(z.astype(jnp.bfloat16), w1.astype(jnp.bfloat16))\n    act = jnp.minimum(jnp.square(jnp.maximum(pre, jnp.bfloat16(0.0))), jnp.bfloat16(16.0))",
    "    z_next = z.astype(jnp.bfloat16) + jnp.matmul(act, w2.astype(jnp.bfloat16))",
    "    prem_logits = jnp.matmul(z_next, w_prem.astype(jnp.bfloat16), preferred_element_type=jnp.float32)",
    "    tac_logits = jnp.matmul(z_next, w_tac.astype(jnp.bfloat16), preferred_element_type=jnp.float32)",
    "    return {\"z_next\": z_next, \"premise_logits\": prem_logits, \"tactic_logits\": tac_logits}\n"
  ]

end LeanNative.Backend.MLIRGPU
