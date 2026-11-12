import LeanNative.Backend.LLVM
import LeanNative.Backend.LLVMLower
import LeanNative.Driver.BuildExe
import LeanNative.Driver.CoreCLI
import LeanNative.Driver.CAbiEmit
import LeanNative.Proofs.LedgerEmbedded32Proofs

namespace LeanNative.Tests.LedgerEmbedded32Tests

open LeanNative.IR
open LeanNative.Backend.LLVM
open LeanNative.Backend.LLVMLower
open LeanNative.Driver.CoreCLI
open LeanNative.Proofs.LedgerEmbedded32

/-- Sample freestanding Bitcoin module exercising `ByteArray` slice reads + `USize` (`i32` on ILP32)
    alongside `ledgerBip32VarintDecl`. -/
def ledgerSliceAndScalarModule : LNIRModule :=
  { moduleName := "ledger_bitcoin_smoke"
  , decls := [
      ledgerBip32VarintDecl,
      { name := "ledger_read_bip32_be32"
      , params := [ { id := 0, name := "buf", ty := .sarray .i8, borrow := true }
                  , { id := 1, name := "off", ty := .usize } ]
      , retTy := .i32
      , body :=
          .letBind 2 .usize (.sarrayLen 0)
            (.letBind 3 .usize (.scalar (.binOp .add (.var 1) (.constU64 4)))
              (.letBind 4 .i1 (.scalar (.binOp .le (.var 3) (.var 2)))
                (.ite 4
                  (.letBind 5 .i8 (.sarrayGet 0 1 .i8)
                    (.letBind 6 .usize (.scalar (.binOp .add (.var 1) (.constU64 1)))
                      (.letBind 7 .i8 (.sarrayGet 0 6 .i8)
                        (.letBind 8 .usize (.scalar (.binOp .add (.var 1) (.constU64 2)))
                          (.letBind 9 .i8 (.sarrayGet 0 8 .i8)
                            (.letBind 10 .usize (.scalar (.binOp .add (.var 1) (.constU64 3)))
                              (.letBind 11 .i8 (.sarrayGet 0 10 .i8)
                                (.letBind 12 .i32 (.scalar (.binOp .shl (.var 5) (.constU64 24)))
                                  (.letBind 13 .i32 (.scalar (.binOp .shl (.var 7) (.constU64 16)))
                                    (.letBind 14 .i32 (.scalar (.binOp .shl (.var 9) (.constU64 8)))
                                      (.letBind 15 .i32 (.scalar (.binOp .bitOr (.var 12) (.var 13)))
                                        (.letBind 16 .i32 (.scalar (.binOp .bitOr (.var 15) (.var 14)))
                                          (.letBind 17 .i32 (.scalar (.binOp .bitOr (.var 16) (.var 11)))
                                            (.ret 17))))))))))))))
                  (.letBind 18 .i32 (.scalar (.constU64 0)) (.ret 18))))) }
    ] }

#guard checkFreestandingModule ledgerSliceAndScalarModule .thumbv6m == none
#guard checkFreestandingModule ledgerSliceAndScalarModule .thumbv8mMain == none
#guard checkFreestandingModule ledgerSliceAndScalarModule .riscv32imac == none

/-- Negative fail-closed test: heap-allocating declaration is rejected by `emitLLVMFreestanding?`. -/
def heapAllocRejectModule : LNIRModule :=
  { moduleName := "ledger_heap_reject"
  , decls := [{
      name := "bad_heap_alloc"
      params := [{ id := 0, name := "x", ty := .i64 }]
      retTy := .objPtr
      body := .letBind 1 .objPtr (.allocCtor 0 [] [0]) (.ret 1)
    }] }

#guard match emitLLVMFreestanding? heapAllocRejectModule .thumbv6m with
  | .error _ => true
  | .ok _ => false

#guard match emitLLVMFreestanding? heapAllocRejectModule .riscv32imac with
  | .error _ => true
  | .ok _ => false

#guard match emitLLVMFreestanding? ledgerSliceAndScalarModule .thumbv6m with
  | .ok ir =>
    (ir.splitOn "target triple = \"thumbv6m-none-eabi\"").length > 1 &&
    (ir.splitOn "i32 noundef %arg_v1").length > 1 &&
    (ir.splitOn "@malloc").length == 1 &&
    (ir.splitOn "@lean_alloc_ctor").length == 1 &&
    (ir.splitOn "uwtable").length == 1 &&
    (ir.splitOn "minsize optsize").length > 1 &&
    TargetArch.thumbv6m.clangFlags.contains "-ffunction-sections" &&
    TargetArch.thumbv6m.clangFlags.contains "-fdata-sections"
  | .error _ => false

#guard match emitLLVMFreestanding? ledgerSliceAndScalarModule .riscv32imac with
  | .ok ir =>
    (ir.splitOn "target datalayout = \"e-m:e-p:32:32-i64:64-n32-S128\"").length > 1 &&
    (ir.splitOn "i32 noundef %arg_v1").length > 1 &&
    (ir.splitOn "@malloc").length == 1 &&
    (ir.splitOn "@lean_alloc_ctor").length == 1 &&
    (ir.splitOn "uwtable").length == 1
  | .error _ => false

/-- Regression guard for Cortex-M0+ (`thumbv6m`) freestanding 64-bit multiplication:
    `emitLLVMFreestanding?` must expand `i64 * i64` via 32-bit partial products without
    emitting raw `mul i64` or referencing `__aeabi_lmul`. -/
def thumbv6mMul64Module : LNIRModule :=
  { moduleName := "ledger_thumbv6m_mul64"
  , decls := [{
      name := "mul64_partial_products"
      params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
      retTy := .i64
      body := .letBind 2 .i64 (.scalar (.binOp .mul (.var 0) (.var 1))) (.ret 2)
    }] }

#guard match emitLLVMFreestanding? thumbv6mMul64Module .thumbv6m with
  | .ok ir =>
    (ir.splitOn "mul i64").length == 1 &&
    (ir.splitOn "__aeabi_lmul").length == 1 &&
    (ir.splitOn "mul i32").length > 1
  | .error _ => false

/-- Flat-pointer, bounded-loop, `Unit` (`void`), and intra-module helper call IR contract across
    all 4 freestanding targets: `.rawPtr` parameters emit `ptr noundef` (never `noalias`),
    `.unit` returns emit `void`, loads/stores use natural `align 2`/`align 4`, and local helpers
    are emitted as direct LLVM calls with zero heap runtime. -/
private def flatPtrLoopIROk (arch : TargetArch) : Bool :=
  match emitLLVMFreestanding? ledgerFlatPtrLoopModule arch with
  | .ok ir =>
    (ir.splitOn s!"target triple = \"{arch.llvmTriple}\"").length > 1 &&
    (ir.splitOn "define dso_local zeroext i8 @llb_bytes_eq(ptr noundef %arg_v0, ptr noundef %arg_v1, i32 noundef %arg_v2)").length > 1 &&
    (ir.splitOn "define dso_local i64 @llb_sum_u32(ptr noundef %arg_v0, i32 noundef %arg_v1)").length > 1 &&
    (ir.splitOn "define dso_local void @llb_sort_u16(ptr noundef %arg_v0, i32 noundef %arg_v1)").length > 1 &&
    (ir.splitOn "define dso_local void @llb_swap_u8_entry(ptr noundef %arg_v0, i32 noundef %arg_v1, i32 noundef %arg_v2)").length > 1 &&
    (ir.splitOn "call void @l_swap_u8_helper(").length > 1 &&
    (ir.splitOn "load i16, ptr").length > 1 &&
    (ir.splitOn "align 2").length > 1 &&
    (ir.splitOn "load i32, ptr").length > 1 &&
    (ir.splitOn "align 4").length > 1 &&
    (ir.splitOn "noalias").length == 1 &&
    (ir.splitOn "@malloc").length == 1 &&
    (ir.splitOn "@lean_alloc_ctor").length == 1 &&
    (!arch.isFreestandingEmbedded || (ir.splitOn "!llvm.loop").length == 1)
  | .error _ => false

#guard flatPtrLoopIROk .thumbv6m
#guard flatPtrLoopIROk .thumbv8mMain
#guard flatPtrLoopIROk .riscv32imac
#guard flatPtrLoopIROk .x86_64

/-- Multi-line `@[export]` source signatures using `ConstBytes`, `MutBytes`, `ConstU32s`,
    `MutU16s`, and `Unit` parse to exact C99 and Rust FFI bindings. -/
private def flatPtrSourceAbiText : String :=
  "@[export llb_bytes_eq]\n" ++
  "def bytesEq (a : ConstBytes) (b : ConstBytes)\n" ++
  "    (len : UInt32) : UInt8 :=\n" ++
  "  1\n" ++
  "\n" ++
  "@[export llb_sort_u16]\n" ++
  "def sortU16 (arr : MutU16s)\n" ++
  "    (count : UInt32) : Unit :=\n" ++
  "  ()\n" ++
  "\n" ++
  "@[export llb_sum_u32]\n" ++
  "def sumU32 (arr : ConstU32s)\n" ++
  "    (len : UInt32) : UInt64 :=\n" ++
  "  0\n" ++
  "\n" ++
  "@[export llb_sort_fixed_bytes]\n" ++
  "def sortFixedBytes (buf : MutBytes)\n" ++
  "    (count : UInt32)\n" ++
  "    (stride : UInt32) : Unit :=\n" ++
  "  ()\n"

#guard
  let (sigs, _) := extractLeanSourceCAbiAndGuards flatPtrSourceAbiText
  let hdr := emitCAbiHeaderFromSigs sigs (width? := some .bits32)
  let rust := emitCAbiRustFromSigs sigs
  (hdr.splitOn "uint8_t llb_bytes_eq(const uint8_t* a, const uint8_t* b, uint32_t len);").length > 1 &&
  (hdr.splitOn "void llb_sort_u16(uint16_t* arr, uint32_t count);").length > 1 &&
  (hdr.splitOn "uint64_t llb_sum_u32(const uint32_t* arr, uint32_t len);").length > 1 &&
  (hdr.splitOn "void llb_sort_fixed_bytes(uint8_t* buf, uint32_t count, uint32_t stride);").length > 1 &&
  (rust.splitOn "pub fn llb_bytes_eq(a: *const u8, b: *const u8, len: u32) -> u8;").length > 1 &&
  (rust.splitOn "pub fn llb_sort_u16(arr: *mut u16, count: u32);").length > 1 &&
  (rust.splitOn "pub fn llb_sum_u32(arr: *const u32, len: u32) -> u64;").length > 1 &&
  (rust.splitOn "pub fn llb_sort_fixed_bytes(buf: *mut u8, count: u32, stride: u32);").length > 1

/-- Resolve an LLVM `llvm-nm` binary on PATH or versioned LLVM directories. -/
private def resolveLlvmNm : IO String := do
  for cand in ["llvm-nm", "llvm-nm-19", "llvm-nm-18", "llvm-nm-20", "/usr/lib/llvm-19/bin/llvm-nm", "/usr/lib/llvm-18/bin/llvm-nm"] do
    try
      let out ← IO.Process.output { cmd := cand, args := #["--version"] }
      if out.exitCode == 0 then return cand
    catch _ => pure ()
  return "llvm-nm"

/-- Concrete end-to-end `LLVMLower` + `emitLLVMFreestanding?` + `clang -c` + `llvm-nm -u` + `-fstack-usage`
    smoke suite across `.thumbv6m`, `.thumbv8mMain`, and `.riscv32imac`. -/
def runLedgerEmbeddedClangSmokeSuite (clangBin : String := "clang") : IO Bool := do
  let nmBin ← resolveLlvmNm
  let pid ← IO.monoNanosNow
  let targets : List TargetArch := [.thumbv6m, .thumbv8mMain, .riscv32imac]
  for arch in targets do
    -- 1) Compile `LLVMLower` pretty-printed IR (`ppLoweredDeclForTarget`) via `clang -c`
    let some loweredIr := ppLoweredDeclForTarget arch ledgerBip32VarintDecl
      | return false
    let lowLl := s!"/tmp/ln_ledger_low_{arch.triple}_{pid}.ll"
    let lowObj := s!"/tmp/ln_ledger_low_{arch.triple}_{pid}.o"
    let lowSu := s!"/tmp/ln_ledger_low_{arch.triple}_{pid}.su"
    IO.FS.writeFile lowLl loweredIr
    let lowOut ← IO.Process.output {
      cmd := clangBin
      args := arch.clangFlags ++ #["-c", lowLl, "-o", lowObj]
    }
    try IO.FS.removeFile lowLl catch _ => pure ()
    if lowOut.exitCode != 0 || !(← System.FilePath.pathExists lowObj) then
      try IO.FS.removeFile lowObj catch _ => pure ()
      try IO.FS.removeFile lowSu catch _ => pure ()
      return false
    let lowBytes ← IO.FS.readBinFile lowObj
    let (lowElfOk, _) := verifyObjectBytesForTarget arch lowBytes
    let lowNm ← IO.Process.output { cmd := nmBin, args := #["-u", lowObj] }
    let lowSuOk ← System.FilePath.pathExists lowSu
    let lowSuTxt ← if lowSuOk then IO.FS.readFile lowSu else pure ""
    try IO.FS.removeFile lowObj catch _ => pure ()
    try IO.FS.removeFile lowSu catch _ => pure ()
    if !lowElfOk || lowNm.exitCode != 0 || !lowNm.stdout.trimAscii.isEmpty ||
       !lowSuOk || (lowSuTxt.splitOn "ledger_bip32_varint_meta").length < 2 then
      return false
    -- 2) Compile full freestanding `emitLLVMFreestanding?` slice+scalar module via `clang -c`
    let .ok fsIr := emitLLVMFreestanding? ledgerSliceAndScalarModule arch
      | return false
    let fsLl := s!"/tmp/ln_ledger_fs_{arch.triple}_{pid}.ll"
    let fsObj := s!"/tmp/ln_ledger_fs_{arch.triple}_{pid}.o"
    let fsSu := s!"/tmp/ln_ledger_fs_{arch.triple}_{pid}.su"
    IO.FS.writeFile fsLl fsIr
    let fsOut ← IO.Process.output {
      cmd := clangBin
      args := arch.clangFlags ++ #["-c", fsLl, "-o", fsObj]
    }
    try IO.FS.removeFile fsLl catch _ => pure ()
    if fsOut.exitCode != 0 || !(← System.FilePath.pathExists fsObj) then
      try IO.FS.removeFile fsObj catch _ => pure ()
      try IO.FS.removeFile fsSu catch _ => pure ()
      return false
    let fsBytes ← IO.FS.readBinFile fsObj
    let (fsElfOk, _) := verifyObjectBytesForTarget arch fsBytes
    let fsNmU ← IO.Process.output { cmd := nmBin, args := #["-u", fsObj] }
    let fsNmAll ← IO.Process.output { cmd := nmBin, args := #[fsObj] }
    let fsSuOk ← System.FilePath.pathExists fsSu
    let fsSuTxt ← if fsSuOk then IO.FS.readFile fsSu else pure ""
    try IO.FS.removeFile fsObj catch _ => pure ()
    try IO.FS.removeFile fsSu catch _ => pure ()
    if !fsElfOk || fsNmU.exitCode != 0 || !fsNmU.stdout.trimAscii.isEmpty ||
       (fsNmAll.stdout.splitOn "malloc").length > 1 ||
       (fsNmAll.stdout.splitOn "lean_alloc").length > 1 ||
        !fsSuOk || (fsSuTxt.splitOn "ledger_read_bip32_be32").length < 2 then
      return false
  let pid2 ← IO.monoNanosNow
  let srcPath := s!"/tmp/ln_flatptr_src_{pid2}.lean"
  let srcText :=
    "structure ConstBytes where addr : USize\n" ++
    "structure MutBytes where addr : USize\n" ++
    "structure ConstU32s where addr : USize\n" ++
    "structure MutU16s where addr : USize\n" ++
    "\n" ++
    "@[noinline] def readU8 (p : ConstBytes) (idx : UInt32) : UInt8 :=\n" ++
    "  let _ := p; let _ := idx; 0\n" ++
    "@[noinline] def readMutU8 (p : MutBytes) (idx : UInt32) : UInt8 :=\n" ++
    "  let _ := p; let _ := idx; 0\n" ++
    "@[noinline] def writeU8 (p : MutBytes) (idx : UInt32) (val : UInt8) : MutBytes :=\n" ++
    "  let _ := idx; let _ := val; p\n" ++
    "@[noinline] def readU32 (p : ConstU32s) (idx : UInt32) : UInt32 :=\n" ++
    "  let _ := p; let _ := idx; 0\n" ++
    "@[noinline] def readMutU16 (p : MutU16s) (idx : UInt32) : UInt16 :=\n" ++
    "  let _ := p; let _ := idx; 0\n" ++
    "@[noinline] def writeU16 (p : MutU16s) (idx : UInt32) (val : UInt16) : MutU16s :=\n" ++
    "  let _ := idx; let _ := val; p\n" ++
    "\n" ++
    "@[noinline] def forRangeU64 (lo hi : UInt32) (init : UInt64)\n" ++
    "    (step : UInt32 → UInt64 → UInt64) : UInt64 :=\n" ++
    "  let count := (hi - lo).toNat\n" ++
    "  let rec go (fuel : Nat) (cur : UInt32) (acc : UInt64) : UInt64 :=\n" ++
    "    match fuel with | 0 => acc | fuel' + 1 => go fuel' (cur + 1) (step cur acc)\n" ++
    "  if decide (lo < hi) then go count lo init else init\n" ++
    "\n" ++
    "@[noinline] def forRangeU32 (lo hi : UInt32) (init : UInt32)\n" ++
    "    (step : UInt32 → UInt32 → UInt32) : UInt32 :=\n" ++
    "  let count := (hi - lo).toNat\n" ++
    "  let rec go (fuel : Nat) (cur : UInt32) (acc : UInt32) : UInt32 :=\n" ++
    "    match fuel with | 0 => acc | fuel' + 1 => go fuel' (cur + 1) (step cur acc)\n" ++
    "  if decide (lo < hi) then go count lo init else init\n" ++
    "\n" ++
    "@[noinline] def forRangeUnit (lo hi : UInt32) (step : UInt32 → Unit) : Unit :=\n" ++
    "  let count := (hi - lo).toNat\n" ++
    "  let rec go (fuel : Nat) (cur : UInt32) : Unit :=\n" ++
    "    match fuel with | 0 => () | fuel' + 1 => let _ := step cur; go fuel' (cur + 1)\n" ++
    "  if decide (lo < hi) then go count lo else ()\n" ++
    "\n" ++
    "def swapBytesHelper (buf : MutBytes) (aOff bOff stride : UInt32) : Unit :=\n" ++
    "  forRangeUnit 0 stride (fun k =>\n" ++
    "    let va := readMutU8 buf (aOff + k)\n" ++
    "    let vb := readMutU8 buf (bOff + k)\n" ++
    "    let _ := writeU8 buf (aOff + k) vb\n" ++
    "    let _ := writeU8 buf (bOff + k) va\n" ++
    "    ())\n" ++
    "\n" ++
    "def cmpSlicesLt (buf : MutBytes) (aOff bOff stride : UInt32) : UInt32 :=\n" ++
    "  let st := forRangeU32 0 stride 0 (fun k acc =>\n" ++
    "    if acc != 0 then acc\n" ++
    "    else\n" ++
    "      let va := readMutU8 buf (aOff + k)\n" ++
    "      let vb := readMutU8 buf (bOff + k)\n" ++
    "      if va < vb then 1 else if va > vb then 2 else 0)\n" ++
    "  if st == 1 then 1 else 0\n" ++
    "\n" ++
    "@[export llb_bytes_eq]\n" ++
    "def bytesEq (a : ConstBytes) (b : ConstBytes) (len : UInt32) : UInt8 :=\n" ++
    "  let diff := forRangeU32 0 len 0 (fun i acc =>\n" ++
    "    let ba := readU8 a i\n" ++
    "    let bb := readU8 b i\n" ++
    "    acc ||| (ba ^^^ bb).toUInt32)\n" ++
    "  if diff == 0 then 1 else 0\n" ++
    "\n" ++
    "@[export llb_sum_u32]\n" ++
    "def sumU32 (arr : ConstU32s) (len : UInt32) : UInt64 :=\n" ++
    "  forRangeU64 0 len 0 (fun i acc => acc + (readU32 arr i).toUInt64)\n" ++
    "\n" ++
    "@[export llb_sort_u16]\n" ++
    "def sortU16 (arr : MutU16s) (count : UInt32) : Unit :=\n" ++
    "  if count <= 1 then ()\n" ++
    "  else\n" ++
    "    forRangeUnit 1 count (fun i =>\n" ++
    "      let key := readMutU16 arr i\n" ++
    "      let pos := forRangeU32 0 i i (fun step curPos =>\n" ++
    "        let j := i - 1 - step\n" ++
    "        if curPos == j + 1 then\n" ++
    "          let vj := readMutU16 arr j\n" ++
    "          if vj > key then\n" ++
    "            let _ := writeU16 arr (j + 1) vj\n" ++
    "            j\n" ++
    "          else curPos\n" ++
    "        else curPos)\n" ++
    "      let _ := writeU16 arr pos key\n" ++
    "      ())\n" ++
    "\n" ++
    "@[export llb_sort_fixed_bytes]\n" ++
    "def sortFixedBytes (buf : MutBytes) (count : UInt32) (stride : UInt32) : Unit :=\n" ++
    "  if count <= 1 || stride == 0 then ()\n" ++
    "  else\n" ++
    "    forRangeUnit 1 count (fun i =>\n" ++
    "      let _ := forRangeU32 0 i i (fun step curIdx =>\n" ++
    "        let j := i - 1 - step\n" ++
    "        if curIdx == j + 1 then\n" ++
    "          let jOff := j * stride\n" ++
    "          let cOff := curIdx * stride\n" ++
    "          if cmpSlicesLt buf cOff jOff stride == 1 then\n" ++
    "            let _ := swapBytesHelper buf jOff cOff stride\n" ++
    "            j\n" ++
    "          else curIdx\n" ++
    "        else curIdx)\n" ++
    "      ())\n"
  IO.FS.writeFile srcPath srcText
  let hook? := some (fun path arch => LeanNative.IR.ingestLeanSourceFile path path arch false)
  let targetSpecs : List (String × String) :=
    [("thumbv6m", "thumbv6m"), ("thumbv8m.main", "thumbv8m"), ("riscv32imac", "riscv32"), ("x86_64", "x86_64")]
  for (targetFlag, stem) in targetSpecs do
    let outA := s!"/tmp/ln_flatptr_{stem}_{pid2}.a"
    let rc ← LeanNative.Driver.CoreCLI.runEmitFreestandingCLib "lean-native" hook?
      [srcPath, "--target", targetFlag, "-o", outA]
    if rc != 0 then
      try IO.FS.removeFile srcPath catch _ => pure ()
      return false
  let x64A := s!"/tmp/ln_flatptr_x86_64_{pid2}.a"
  let x64H := s!"/tmp/ln_flatptr_x86_64_{pid2}.h"
  let harnessC := s!"/tmp/ln_flatptr_harness_{pid2}.c"
  let harnessBin := s!"/tmp/ln_flatptr_harness_{pid2}"
  let harnessText :=
    "#include <assert.h>\n" ++
    "#include <stdio.h>\n" ++
    "#include <string.h>\n" ++
    s!"#include \"{x64H}\"\n" ++
    "int main(void) {\n" ++
    "  const uint8_t b1[6] = {0x02,0x11,0x22,0x33,0x44,0x55};\n" ++
    "  const uint8_t b2[6] = {0x02,0x11,0x22,0x33,0x44,0x55};\n" ++
    "  const uint8_t b3[6] = {0x02,0x11,0x22,0x33,0x99,0x55};\n" ++
    "  assert(llb_bytes_eq(b1, b1, 6) == 1);\n" ++
    "  assert(llb_bytes_eq(b1, b2, 6) == 1);\n" ++
    "  assert(llb_bytes_eq(b1, b3, 6) == 0);\n" ++
    "  assert(llb_bytes_eq(b1, b3, 4) == 1);\n" ++
    "  assert(llb_bytes_eq(b1, b3, 0) == 1);\n" ++
    "  const uint32_t nums[5] = {1000000000U,2000000000U,3000000000U,42U,7U};\n" ++
    "  assert(llb_sum_u32(nums, 0) == 0ULL);\n" ++
    "  assert(llb_sum_u32(nums, 5) == 6000000049ULL);\n" ++
    "  uint16_t u16s[7] = {900,12,65535,0,12,42,7};\n" ++
    "  llb_sort_u16(u16s, 0);\n" ++
    "  assert(u16s[0] == 900);\n" ++
    "  llb_sort_u16(u16s, 7);\n" ++
    "  const uint16_t expU16[7] = {0,7,12,12,42,900,65535};\n" ++
    "  for (int i = 0; i < 7; i++) assert(u16s[i] == expU16[i]);\n" ++
    "  uint8_t pks[4 * 33];\n" ++
    "  memset(pks, 0, sizeof(pks));\n" ++
    "  pks[0*33+0]=0x03; pks[0*33+32]=0xAA;\n" ++
    "  pks[1*33+0]=0x02; pks[1*33+32]=0xFF;\n" ++
    "  pks[2*33+0]=0x02; pks[2*33+32]=0x01;\n" ++
    "  pks[3*33+0]=0x03; pks[3*33+32]=0x10;\n" ++
    "  llb_sort_fixed_bytes(pks, 4, 33);\n" ++
    "  assert(pks[0*33+0]==0x02 && pks[0*33+32]==0x01);\n" ++
    "  assert(pks[1*33+0]==0x02 && pks[1*33+32]==0xFF);\n" ++
    "  assert(pks[2*33+0]==0x03 && pks[2*33+32]==0x10);\n" ++
    "  assert(pks[3*33+0]==0x03 && pks[3*33+32]==0xAA);\n" ++
    "  printf(\"ALL_FREESTANDING_RUNTIME_TESTS_PASSED\\n\");\n" ++
    "  return 0;\n" ++
    "}\n"
  IO.FS.writeFile harnessC harnessText
  let linkOut ← IO.Process.output {
    cmd := clangBin
    args := #["-std=c11", "-Wall", "-Wextra", "-Werror", harnessC, x64A, "-o", harnessBin]
  }
  let runOut ← if linkOut.exitCode == 0 then
      IO.Process.output { cmd := harnessBin, args := #[] }
    else pure { exitCode := 1, stdout := "", stderr := linkOut.stderr }
  let ok := linkOut.exitCode == 0 && runOut.exitCode == 0 &&
    (runOut.stdout.splitOn "ALL_FREESTANDING_RUNTIME_TESTS_PASSED").length > 1
  for stem in ["thumbv6m", "thumbv8m", "riscv32", "x86_64"] do
    let base := s!"/tmp/ln_flatptr_{stem}_{pid2}"
    for ext in [".a", ".o", ".ll", ".h", ".su"] do
      try IO.FS.removeFile (base ++ ext) catch _ => pure ()
  try IO.FS.removeFile srcPath catch _ => pure ()
  try IO.FS.removeFile harnessC catch _ => pure ()
  try IO.FS.removeFile harnessBin catch _ => pure ()
  return ok

end LeanNative.Tests.LedgerEmbedded32Tests
