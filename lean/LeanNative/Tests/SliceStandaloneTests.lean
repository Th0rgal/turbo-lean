import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.Bridge
import LeanNative.Driver.BuildExe
import LeanNative.Backend.LLVM
import LeanNative.Backend.LLVMEmitVerify
import LeanNative.Semantics.Eval
import LeanNative.Proofs.SliceBridgeStandaloneProofs

namespace LeanNative.Tests.SliceStandaloneTests

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.Backend
open LeanNative.Semantics

/-! ## Wave 0.A Conformance, Real LCNF Ingestion, LLVM Width/ABI & 4-Mutant Kill Suite -/

def sampleSliceHeap : HeapState :=
  { buffers :=
      [ { id := 1, exclusive := false, data := #[65, 66, 67, 68] }
      , { id := 2, exclusive := false, data := #[0x3FF0000000000000, 0x4000000000000000, 0x4008000000000000] } ]
  , nextId := 2 }

def sampleSliceEnv : VarEnv :=
  (((VarEnv.empty.bind 0 (.sarrayId 1)).bind 1 (.sarrayId 2)).bind 2 (.u64 2)).bind 3 (.u64 0)

-- 1. Positive canonical lowering checks (`ByteArray.usize`/`uget`, `FloatArray.usize`/`uget` + erased `.unit` proof args)
#guard lowerSliceIntrinsicPure? ``ByteArray.usize [0] .usize [.sarray .i8] false .x86_64 ==
  some (.sarrayLen 0)
#guard lowerSliceIntrinsicPure? ``FloatArray.usize [1] .usize [.sarray .f64] false .x86_64 ==
  some (.sarrayLen 1)
#guard lowerSliceIntrinsicPure? ``ByteArray.uget [0, 2, 3] .i8 [.sarray .i8, .usize, .unit] false .x86_64 ==
  some (.sarrayGet 0 2 .i8)
#guard lowerSliceIntrinsicPure? ``FloatArray.uget [1, 2, 3] .f64 [.sarray .f64, .usize, .unit] false .x86_64 ==
  some (.sarrayGet 1 2 .f64)

-- 2. End-to-end target evaluation over `sampleSliceHeap`
#guard (lowerSliceIntrinsicPure? ``ByteArray.usize [0] .usize [.sarray .i8] false .x86_64).bind
  (fun e => (evalExpr sampleSliceEnv sampleSliceHeap e).toOption.map Prod.fst) == some (Val.u64 4)
#guard (lowerSliceIntrinsicPure? ``ByteArray.uget [0, 2, 3] .i8 [.sarray .i8, .usize, .unit] false .x86_64).bind
  (fun e => (evalExpr sampleSliceEnv sampleSliceHeap e).toOption.map Prod.fst) == some (Val.u64 67)
#guard (lowerSliceIntrinsicPure? ``FloatArray.uget [1, 2, 3] .f64 [.sarray .f64, .usize, .unit] false .x86_64).bind
  (fun e => (evalExpr sampleSliceEnv sampleSliceHeap e).toOption.map Prod.fst) == some (Val.u64 0x4008000000000000)

-- 3. 4-Mutant + `wasm32` layout fail-closed guards (local shadow, `.objPtr`, GPU `.usize`, `wasm32` `sarray`, element mismatch, `get!`)
#guard lowerSliceIntrinsicPure? ``ByteArray.usize [0] .usize [.sarray .i8] true .x86_64 == none
#guard lowerSliceIntrinsicPure? ``ByteArray.uget [0, 2] .i8 [.objPtr, .usize] false .x86_64 == none
#guard lowerSliceIntrinsicPure? ``ByteArray.usize [0] .usize [.sarray .i8] false .nvptx64 == none
#guard lowerSliceIntrinsicPure? ``ByteArray.usize [0] .usize [.sarray .i8] false .wasm32 == none
#guard lowerSliceIntrinsicPure? ``ByteArray.uget [0, 2] .i8 [.sarray .i8, .usize] false .wasm32 == none
#guard lowerSliceIntrinsicPure? ``ByteArray.uget [0, 2] .i8 [.sarray .f64, .usize] false .x86_64 == none
#guard lowerSliceIntrinsicPure? ``ByteArray.get! [0, 2] .i8 [.sarray .i8, .usize] false .x86_64 == none

-- 4. `resolveStandaloneLinkMode` fail-closed guards (`--standalone` never silently falls through to `-lleanshared`)
#guard (resolveStandaloneLinkMode false true false true true).toOption == some true
#guard (resolveStandaloneLinkMode false false true true true).toOption == some false
#guard (resolveStandaloneLinkMode false true true true true).isOk == false
#guard (resolveStandaloneLinkMode true true false true true).isOk == false
#guard (resolveStandaloneLinkMode false true false false true).isOk == false
#guard (resolveStandaloneLinkMode false true false true false).isOk == false

-- 5. LLVM backend element-width GEP/load & `double` (`Float`) ABI guards
private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def llvmSliceWidthAndFloatAbiModule : LNIRModule where
  moduleName := "llvm_slice_width_and_float_abi"
  decls := [
    { name := "read_byte_slice"
      params := [{ id := 0, name := "b", ty := .sarray .i8 }, { id := 1, name := "i", ty := .usize }]
      retTy := .i8
      body := .letBind 2 .i8 (.sarrayGet 0 1 .i8) (.ret 2) },
    { name := "read_float_slice"
      params := [{ id := 0, name := "fa", ty := .sarray .f64 }, { id := 1, name := "i", ty := .usize }]
      retTy := .f64
      body := .letBind 2 .f64 (.sarrayGet 0 1 .f64) (.ret 2) },
    { name := "hoisted_raw_byte_rw"
      params := [
        { id := 0, name := "p", ty := .rawPtr .i8 },
        { id := 1, name := "i", ty := .usize },
        { id := 2, name := "v", ty := .i8 }
      ]
      retTy := .i8
      body := .rawStore 0 1 2 .i8 (.letBind 3 .i8 (.rawLoad 0 1 .i8) (.ret 3)) },
    { name := "parfor_and_cow_byte_slice"
      params := [{ id := 0, name := "b", ty := .sarray .i8 }, { id := 1, name := "n", ty := .i64 }]
      retTy := .i8
      body :=
        .letBind 2 (.sarray .i8) (.sarrayEnsureExclusive 0 .i8)
          (.parFor 3 1 [2] .i8 (.customScalar 10 [11] (.binOp .add (.var 11) (.constU64 7)))
            (.letBind 4 .i64 (.scalar (.constU64 1))
              (.letBind 5 .i8 (.sarrayGet 3 4 .i8) (.ret 5)))) }
  ]

def llvmSliceWidthAndFloatAbiIr : String :=
  emitLLVMOptimized llvmSliceWidthAndFloatAbiModule .x86_64

def llvmSliceWidthAndFloatAbiBaselineIr : String :=
  emitLLVMBaseline llvmSliceWidthAndFloatAbiModule .x86_64

#guard findUnsupportedLLVMCall? llvmSliceWidthAndFloatAbiModule == none
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "getelementptr inbounds i8, ptr %sget_data"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "load i8, ptr %sget_gep"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "getelementptr inbounds i64, ptr %sget_data"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "load i64, ptr %sget_gep"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "define dso_local double @read_float_slice(ptr noalias noundef %arg_v0, i64 noundef %arg_v1)"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "bitcast i64"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "getelementptr inbounds i8, ptr %ldp"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "store i8 %rst_tr8"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "load i8, ptr %rld_gep"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "@lean_native_ensure_exclusive_e1(ptr"
#guard !(hasSubstr llvmSliceWidthAndFloatAbiIr "call ptr @lean_native_ensure_exclusive_uninit_e1(ptr")
#guard hasSubstr llvmSliceWidthAndFloatAbiBaselineIr "@lean_native_ensure_exclusive_e1(ptr"
#guard LeanNative.Backend.LLVMEmitVerify.checkStencilAndExclusiveSublenDecl false == true
#guard LeanNative.Backend.LLVMEmitVerify.checkStencilAndExclusiveSublenDecl true == true
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "getelementptr inbounds i8, ptr %cs_ptr"
#guard hasSubstr llvmSliceWidthAndFloatAbiIr "store i8 %p_out_tr8"

-- 5b. Narrow overflow-boundary evaluator-versus-LLVM equivalence (`LLVMEmitVerify.checkNarrowByteOverflowDecl`)
#guard LeanNative.Backend.LLVMEmitVerify.checkNarrowByteOverflowDecl false == true
#guard LeanNative.Backend.LLVMEmitVerify.checkNarrowByteOverflowDecl true == true

-- 5c. Element-width consistency & 32-bit `wasm32` `lean_sarray_object` layout emission (16-byte header, `i32` `m_size`)
def llvmSliceWidthWasmIr : String :=
  emitLLVMOptimized llvmSliceWidthAndFloatAbiModule .wasm32

#guard findUnsupportedLLVMCall? llvmSliceWidthAndFloatAbiModule .wasm32 == none
#guard hasSubstr llvmSliceWidthWasmIr " = getelementptr inbounds i8, ptr %ldp"
#guard hasSubstr llvmSliceWidthWasmIr ", i64 16\n  %sget_gep"
#guard hasSubstr llvmSliceWidthWasmIr "%sz32 = load i32, ptr %sz_ptr, align 4"
#guard hasSubstr llvmSliceWidthWasmIr "%cap_ptr = getelementptr inbounds i8, ptr %new_arr, i64 12"
#guard hasSubstr llvmSliceWidthWasmIr "declare noalias ptr @malloc(i32 noundef)"
#guard hasSubstr llvmSliceWidthWasmIr "%b_ovf = icmp ugt i64 %total_bytes, 4294967295"
#guard hasSubstr llvmSliceWidthWasmIr "%new_arr = call noalias ptr @malloc(i32 %alloc_sz32)"
#guard !(hasSubstr llvmSliceWidthWasmIr "@malloc(i64")
#guard LeanNative.Backend.LLVMEmitVerify.checkFreshByteParForDecl false == true
#guard LeanNative.Backend.LLVMEmitVerify.checkFreshByteParForDecl true == true
#guard LeanNative.Backend.LLVMEmitVerify.checkNarrowByteDotProdDecl false == true
#guard LeanNative.Backend.LLVMEmitVerify.checkNarrowByteDotProdDecl true == true
#guard LeanNative.Proofs.symbolicCodeRefines
  (.letBind 2 .i64 (.sarrayGet 0 1 .i64) (.ret 2))
  (.letBind 2 .i64 (.sarrayGet 0 1 .i8) (.ret 2)) == false
#guard LeanNative.Proofs.symbolicCodeRefines
  (.letBind 2 .i64 (.rawLoad 0 1 .i64) (.ret 2))
  (.letBind 2 .i64 (.rawLoad 0 1 .i8) (.ret 2)) == false

def mismatchedElemTypeDecl : LNIRDecl where
  name := "mismatched_sarray_elem_ty"
  params := [{ id := 0, name := "a", ty := .sarray .i64 }, { id := 1, name := "i", ty := .usize }]
  retTy := .i8
  body := .letBind 2 .i8 (.sarrayGet 0 1 .i8) (.ret 2)

#guard mismatchedElemTypeDecl.checkElemTypes == some "inconsistent_elem_type"
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInDecl [] mismatchedElemTypeDecl ==
  some "inconsistent_elem_type"
#guard (LeanNative.Proofs.validateTranslationDecl mismatchedElemTypeDecl mismatchedElemTypeDecl 4).passed == false
#guard LeanNative.Proofs.runSymbolicValidatedDecl id mismatchedElemTypeDecl == none

def mismatchedLoopAccElemTypeDecl : LNIRDecl where
  name := "mismatched_seqfor_acc_elem_ty"
  params := [{ id := 0, name := "a64", ty := .sarray .i64 }, { id := 1, name := "b8", ty := .sarray .i8 }]
  retTy := .i64
  body :=
    .letBind 2 .i64 (.scalar (.constU64 0))
      (.letBind 3 .i64 (.scalar (.constU64 1))
        (.seqFor 4 2 3 5 0 (.sarray .i64)
          (.ite 3 (.ret 1) (.ret 5))
          (.letBind 6 .i64 (.sarrayGet 5 2 .i64) (.ret 6))))

#guard mismatchedLoopAccElemTypeDecl.checkElemTypes == some "inconsistent_elem_type"
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInDecl [] mismatchedLoopAccElemTypeDecl ==
  some "inconsistent_elem_type"
#guard (LeanNative.Proofs.validateTranslationDecl mismatchedLoopAccElemTypeDecl mismatchedLoopAccElemTypeDecl 4).passed == false
#guard LeanNative.Proofs.runSymbolicValidatedDecl id mismatchedLoopAccElemTypeDecl == none

def mismatchedNestedLoopAccElemTypeDecl : LNIRDecl where
  name := "mismatched_nested_seqfor_acc_elem_ty"
  params := [{ id := 0, name := "a64", ty := .sarray .i64 }, { id := 1, name := "b8", ty := .sarray .i8 }]
  retTy := .i64
  body :=
    .letBind 2 .i64 (.scalar (.constU64 0))
      (.letBind 3 .i64 (.scalar (.constU64 1))
        (.seqFor 4 2 3 5 0 (.sarray .i64)
          (.seqFor 6 2 3 7 2 .i64 (.ret 7) (.ret 1))
          (.letBind 8 .i64 (.sarrayGet 5 2 .i64) (.ret 8))))

#guard mismatchedNestedLoopAccElemTypeDecl.checkElemTypes == some "inconsistent_elem_type"
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInDecl [] mismatchedNestedLoopAccElemTypeDecl ==
  some "inconsistent_elem_type"
#guard (LeanNative.Proofs.validateTranslationDecl mismatchedNestedLoopAccElemTypeDecl mismatchedNestedLoopAccElemTypeDecl 4).passed == false
#guard LeanNative.Proofs.runSymbolicValidatedDecl id mismatchedNestedLoopAccElemTypeDecl == none

def mismatchedLocalCallSliceModule : LNIRModule where
  moduleName := "LeanNative.Tests.MismatchedLocalCallSlice"
  decls := [
    { name := "read_i8_at_one"
      params := [{ id := 0, name := "b", ty := .sarray .i8 }]
      retTy := .i8
      body := .letBind 1 .i64 (.scalar (.constU64 1)) (.letBind 2 .i8 (.sarrayGet 0 1 .i8) (.ret 2)) },
    { name := "caller_passes_i64_to_i8"
      params := [{ id := 0, name := "a64", ty := .sarray .i64 }]
      retTy := .i64
      body := .letBind 1 .i64 (.call "read_i8_at_one" [0] .i8 false) (.ret 1) }
  ]

#guard findUnsupportedLLVMCall? mismatchedLocalCallSliceModule ==
  some ("caller_passes_i64_to_i8", "inconsistent_elem_type")
#guard (LeanNative.Proofs.validateTranslationModule mismatchedLocalCallSliceModule mismatchedLocalCallSliceModule 4).allPassed == false

def validLocalCallSliceModule : LNIRModule where
  moduleName := "LeanNative.Tests.ValidLocalCallSlice"
  decls := [
    { name := "read_i8_head_or_zero"
      params := [{ id := 0, name := "b", ty := .sarray .i8 }]
      retTy := .i8
      body :=
        .letBind 1 .i64 (.sarrayLen 0)
          (.letBind 2 .i64 (.scalar (.constU64 0))
            (.letBind 3 .i1 (.scalar (.binOp .lt (.var 2) (.var 1)))
              (.ite 3
                (.letBind 4 .i8 (.sarrayGet 0 2 .i8) (.ret 4))
                (.letBind 5 .i8 (.scalar (.constU64 0)) (.ret 5))))) },
    { name := "caller_passes_i8_to_i8"
      params := [{ id := 0, name := "b8", ty := .sarray .i8 }]
      retTy := .i64
      body :=
        .letBind 1 .i64 (.call "read_i8_head_or_zero" [0] .i8 false)
          (.letBind 2 .i64 (.scalar (.constU64 1))
            (.letBind 3 .i64 (.scalar (.binOp .add (.var 1) (.var 2)))
              (.ret 3))) }
  ]

def validLocalCallSliceInlinedTargetModule : LNIRModule where
  moduleName := "LeanNative.Tests.ValidLocalCallSlice"
  decls := [
    validLocalCallSliceModule.decls[0]!,
    { name := "caller_passes_i8_to_i8"
      params := [{ id := 0, name := "b8", ty := .sarray .i8 }]
      retTy := .i64
      body :=
        .letBind 10 .i64 (.sarrayLen 0)
          (.letBind 11 .i64 (.scalar (.constU64 0))
            (.letBind 12 .i1 (.scalar (.binOp .lt (.var 11) (.var 10)))
              (.ite 12
                (.letBind 13 .i8 (.sarrayGet 0 11 .i8)
                  (.letBind 14 .i64 (.scalar (.constU64 1))
                    (.letBind 15 .i64 (.scalar (.binOp .add (.var 13) (.var 14)))
                      (.ret 15))))
                (.letBind 16 .i64 (.scalar (.constU64 1))
                  (.ret 16))))) }
  ]

def buggyLocalCallSliceTargetModule : LNIRModule where
  moduleName := "LeanNative.Tests.ValidLocalCallSlice"
  decls := [
    validLocalCallSliceModule.decls[0]!,
    { name := "caller_passes_i8_to_i8"
      params := [{ id := 0, name := "b8", ty := .sarray .i8 }]
      retTy := .i64
      body :=
        .letBind 1 .i64 (.call "read_i8_head_or_zero" [0] .i8 false)
          (.letBind 2 .i64 (.scalar (.constU64 2))
            (.letBind 3 .i64 (.scalar (.binOp .add (.var 1) (.var 2)))
              (.ret 3))) }
  ]

#guard findUnsupportedLLVMCall? validLocalCallSliceModule == none
#guard (LeanNative.Proofs.validateTranslationModule validLocalCallSliceModule validLocalCallSliceModule 8).allPassed == true
#guard (LeanNative.Proofs.validateTranslationModule validLocalCallSliceModule validLocalCallSliceInlinedTargetModule 8).allPassed == true
#guard (LeanNative.Proofs.validateTranslationModule validLocalCallSliceModule buggyLocalCallSliceTargetModule 8).allPassed == false

def i64CallIntoI1DstSrcModule : LNIRModule where
  moduleName := "LeanNative.Tests.I64CallIntoI1Dst"
  decls := [
    { name := "ret_two_i64"
      params := []
      retTy := .i64
      body := .letBind 0 .i64 (.scalar (.constU64 2)) (.ret 0) },
    { name := "caller_binds_i1_returns_i64"
      params := []
      retTy := .i64
      body := .letBind 1 .i1 (.call "ret_two_i64" [] .i64 false) (.ret 1) }
  ]

def i64CallIntoI1DstBuggyTgtModule : LNIRModule where
  moduleName := "LeanNative.Tests.I64CallIntoI1Dst"
  decls := [
    i64CallIntoI1DstSrcModule.decls[0]!,
    { name := "caller_binds_i1_returns_i64"
      params := []
      retTy := .i64
      body := .letBind 1 .i1 (.scalar (.constBool true)) (.ret 1) }
  ]

#guard (LeanNative.Proofs.validateTranslationModule i64CallIntoI1DstSrcModule i64CallIntoI1DstBuggyTgtModule 4).allPassed == false

def packedI1LoadHelperSrcModule : LNIRModule where
  moduleName := "LeanNative.Tests.PackedI1LoadHelper"
  decls := [
    { name := "load_packed_i1_head"
      params := [{ id := 0, name := "b", ty := .sarray .i1 }]
      retTy := .i1
      body :=
        .letBind 1 .i64 (.sarrayLen 0)
          (.letBind 2 .i64 (.scalar (.constU64 0))
            (.letBind 3 .i1 (.scalar (.binOp .lt (.var 2) (.var 1)))
              (.ite 3
                (.letBind 4 .i64 (.sarrayGet 0 2 .i1) (.ret 4))
                (.letBind 5 .i64 (.scalar (.constU64 0)) (.ret 5))))) },
    { name := "caller_widens_i1_helper"
      params := [{ id := 0, name := "b", ty := .sarray .i1 }]
      retTy := .i64
      body := .letBind 1 .i64 (.call "load_packed_i1_head" [0] .i1 false) (.ret 1) }
  ]

def packedI1LoadUnmaskedBuggyTgtModule : LNIRModule where
  moduleName := "LeanNative.Tests.PackedI1LoadHelper"
  decls := [
    packedI1LoadHelperSrcModule.decls[0]!,
    { name := "caller_widens_i1_helper"
      params := [{ id := 0, name := "b", ty := .sarray .i1 }]
      retTy := .i64
      body :=
        .letBind 10 .i64 (.sarrayLen 0)
          (.letBind 11 .i64 (.scalar (.constU64 0))
            (.letBind 12 .i1 (.scalar (.binOp .lt (.var 11) (.var 10)))
              (.ite 12
                (.letBind 13 .i64 (.sarrayGet 0 11 .i1) (.ret 13))
                (.letBind 14 .i64 (.scalar (.constU64 0)) (.ret 14))))) }
  ]

def packedI1LoadMaskedValidTgtModule : LNIRModule where
  moduleName := "LeanNative.Tests.PackedI1LoadHelper"
  decls := [
    packedI1LoadHelperSrcModule.decls[0]!,
    { name := "caller_widens_i1_helper"
      params := [{ id := 0, name := "b", ty := .sarray .i1 }]
      retTy := .i64
      body :=
        .letBind 10 .i64 (.sarrayLen 0)
          (.letBind 11 .i64 (.scalar (.constU64 0))
            (.letBind 12 .i1 (.scalar (.binOp .lt (.var 11) (.var 10)))
              (.ite 12
                (.letBind 13 .i64 (.sarrayGet 0 11 .i1)
                  (.letBind 15 .i64 (.scalar (.constU64 1))
                    (.letBind 16 .i64 (.scalar (.binOp .bitAnd (.var 13) (.var 15)))
                      (.ret 16))))
                (.letBind 14 .i64 (.scalar (.constU64 0)) (.ret 14))))) }
  ]

#guard (LeanNative.Proofs.validateTranslationModule packedI1LoadHelperSrcModule packedI1LoadHelperSrcModule 8).allPassed == true
#guard (LeanNative.Proofs.validateTranslationModule packedI1LoadHelperSrcModule packedI1LoadUnmaskedBuggyTgtModule 8).allPassed == false
#guard (LeanNative.Proofs.validateTranslationModule packedI1LoadHelperSrcModule packedI1LoadMaskedValidTgtModule 8).allPassed == true

def nestedTupleBufferEraseDecl : LNIRDecl where
  name := "nested_tuple_buffer_erase"
  params := [{ id := 0, name := "a64", ty := .sarray .i64 }, { id := 1, name := "x", ty := .i64 }]
  retTy := .i64
  body :=
    .letBind 2 (.tuple [.sarray .i64, .i64]) (.mkTuple [0, 1])
      (.letBind 3 (.tuple [.tuple [.i64, .i64], .i64]) (.mkTuple [2, 1])
        (.letBind 4 (.tuple [.i64, .i64]) (.projTuple 3 0)
          (.letBind 5 .i64 (.projTuple 4 0) (.ret 5))))

#guard nestedTupleBufferEraseDecl.checkElemTypes == some "inconsistent_elem_type"
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInDecl [] nestedTupleBufferEraseDecl ==
  some "inconsistent_elem_type"
#guard (LeanNative.Proofs.validateTranslationDecl nestedTupleBufferEraseDecl nestedTupleBufferEraseDecl 4).passed == false
#guard LeanNative.Proofs.runSymbolicValidatedDecl id nestedTupleBufferEraseDecl == none

def rawLoadOnSarrayObjectDecl : LNIRDecl where
  name := "raw_load_on_sarray_object"
  params := [{ id := 0, name := "arr", ty := .sarray .i8 }, { id := 1, name := "idx", ty := .usize }]
  retTy := .i8
  body := .letBind 2 .i8 (.rawLoad 0 1 .i8) (.ret 2)

#guard rawLoadOnSarrayObjectDecl.checkElemTypes == some "inconsistent_elem_type"
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInDecl [] rawLoadOnSarrayObjectDecl ==
  some "inconsistent_elem_type"
#guard (LeanNative.Proofs.validateTranslationDecl rawLoadOnSarrayObjectDecl rawLoadOnSarrayObjectDecl 4).passed == false
#guard LeanNative.Proofs.runSymbolicValidatedDecl id rawLoadOnSarrayObjectDecl == none

def rawStoreOnSarrayObjectDecl : LNIRDecl where
  name := "raw_store_on_sarray_object"
  params := [
    { id := 0, name := "arr", ty := .sarray .i8 },
    { id := 1, name := "idx", ty := .usize },
    { id := 2, name := "val", ty := .i8 }
  ]
  retTy := .i8
  body := .rawStore 0 1 2 .i8 (.ret 2)

#guard rawStoreOnSarrayObjectDecl.checkElemTypes == some "inconsistent_elem_type"
#guard LeanNative.Backend.LLVM.findUnsupportedLLVMCallInDecl [] rawStoreOnSarrayObjectDecl ==
  some "inconsistent_elem_type"
#guard (LeanNative.Proofs.validateTranslationDecl rawStoreOnSarrayObjectDecl rawStoreOnSarrayObjectDecl 4).passed == false
#guard LeanNative.Proofs.runSymbolicValidatedDecl id rawStoreOnSarrayObjectDecl == none

-- 6. Real Lean 4.35 LCNF source-ingestion regression (`ingestModuleDecls` on real `ByteArray`/`FloatArray` functions)
theorem usize_lt_imp_size_lt {n : Nat} {i : USize} (h : i < n.toUSize) : i.toNat < n := by
  rw [USize.lt_iff_toNat_lt] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le n USize.size)

@[noinline] def sampleByteUsize (b : ByteArray) : USize := b.usize
@[noinline] def sampleFloatUsize (fa : FloatArray) : USize := fa.usize
@[noinline] def sampleByteHeadOrZero (b : ByteArray) : UInt8 :=
  if h : (0 : USize) < b.usize then b.uget 0 (usize_lt_imp_size_lt h) else 0
@[noinline] def sampleFloatAtOrFallback (fa : FloatArray) (idx : USize) (fallback : Float) : Float :=
  if h : idx < fa.usize then fa.uget idx (usize_lt_imp_size_lt h) else fallback

def verifyRealSliceIngestion : Lean.CoreM Bool := do
  let m ← ingestModuleDecls
    #[``sampleByteUsize, ``sampleFloatUsize, ``sampleByteHeadOrZero, ``sampleFloatAtOrFallback]
    "SliceStandaloneTests" .x86_64 false
  let some dBU := m.decls.find? (·.name.endsWith "sampleByteUsize") | return false
  let some dFU := m.decls.find? (·.name.endsWith "sampleFloatUsize") | return false
  let some dBH := m.decls.find? (·.name.endsWith "sampleByteHeadOrZero") | return false
  let some dFH := m.decls.find? (·.name.endsWith "sampleFloatAtOrFallback") | return false
  let pBU ← match dBU.params.head? with | some p => pure p.id | none => return false
  let pFU ← match dFU.params.head? with | some p => pure p.id | none => return false
  let pBH ← match dBH.params.head? with | some p => pure p.id | none => return false
  let (pFH0, pFH1, pFH2) ← match dFH.params with
    | [p0, p1, p2] => pure (p0.id, p1.id, p2.id)
    | _ => return false
  let rBU := (evalCode 512 (VarEnv.empty.bind pBU (.sarrayId 1)) sampleSliceHeap dBU.body).toOption.map Prod.fst
  let rFU := (evalCode 512 (VarEnv.empty.bind pFU (.sarrayId 2)) sampleSliceHeap dFU.body).toOption.map Prod.fst
  let rBH := (evalCode 512 (VarEnv.empty.bind pBH (.sarrayId 1)) sampleSliceHeap dBH.body).toOption.map Prod.fst
  let envFH := (((VarEnv.empty.bind pFH0 (.sarrayId 2)).bind pFH1 (.u64 2)).bind pFH2 (.u64 0))
  let rFH := (evalCode 512 envFH sampleSliceHeap dFH.body).toOption.map Prod.fst
  let llvmUnsupported := findUnsupportedLLVMCall? m
  let ir := emitLLVMOptimized m .x86_64
  return m.decls.all (·.assurance != .unsupported) &&
    rBU == some (Val.u64 4) &&
    rFU == some (Val.u64 3) &&
    rBH == some (Val.u64 65) &&
    rFH == some (Val.u64 0x4008000000000000) &&
    llvmUnsupported.isNone &&
    hasSubstr ir "getelementptr inbounds i8" &&
    hasSubstr ir "getelementptr inbounds i64" &&
    hasSubstr ir "double @"

#guard LeanNative.Backend.LLVMEmitVerify.checkNarrowByteInputMaskDivDecl false
#guard LeanNative.Backend.LLVMEmitVerify.checkNarrowByteInputMaskDivDecl true

/-- info: true -/
#guard_msgs in
#eval verifyRealSliceIngestion

end LeanNative.Tests.SliceStandaloneTests
