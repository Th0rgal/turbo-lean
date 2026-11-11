import LeanNative.Backend.LLVM
import LeanNative.Backend.LLVMLower
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
  return true

end LeanNative.Tests.LedgerEmbedded32Tests
