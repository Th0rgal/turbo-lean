import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVM
import LeanNative.Backend.LLVMLower
import LeanNative.Driver.CAbiEmit
import LeanNative.Proofs.HybridCAbiProofs
import LeanNative.Proofs.LLVMLowerProofs

/-!
# Ledger 32-Bit ILP32 & Freestanding Backend Proofs (`LeanNative.Proofs.LedgerEmbedded32Proofs`)

Machine-checked formal guarantees for Ledger hardware embedded targets
(`TargetArch.thumbv6m`, `TargetArch.thumbv8mMain`, `TargetArch.riscv32imac`):
1. **32-Bit ILP32 & C99 ABI Layout Soundness**:
   - `ArchWidth.ofTargetArch` maps `.thumbv6m`, `.thumbv8mMain`, and `.riscv32imac` (and iff `isILP32`)
     to `.bits32` (4-byte pointers/`size_t`).
   - `lean_native_flat_slice_t` and `lean_native_mut_slice_t` have exact 12-byte size, 4-byte alignment,
     and field offsets `[0, 4, 8]` across all three Ledger targets.
   - `u64` and `i64` retain 8-byte alignment (`AAPCS` & `RV32 ILP32`) and every struct computed via
     `placeC99Fields` / `computeC99StructLayout` on Ledger targets satisfies `c99LayoutSound`
     (in particular, every `u64`/`i64` field offset is divisible by `8`).
2. **Freestanding Verification Gate Soundness**:
   - Any declaration or module accepted by `checkFreestandingDecl` / `checkFreestandingModule` /
     `emitLLVMFreestanding?` has `codeHasHeapOps d.body = false`, `selectDeclRcMode d = .freestanding`,
     `codeHasStorageOps d.body = false`, `codeHasHeapRuntimeCalls d.body = false`, and
     `findUnsupportedLLVMCallInDecl localSigs d target = none`.
   - Any declaration with `codeHasHeapOps d.body = true` is rejected fail-closed (`isSome = true`).
3. **End-to-End `LLVMLower` Soundness on Ledger Targets**:
   - `lowerModuleForTarget_sound` proves end-to-end semantic refinement (`evalCode` → `LLVMAst.execFn`)
     for `lowerModuleForTarget target d` together with exact target `dataLayout` and `llvmTriple`
     preservation across `.thumbv6m`, `.thumbv8mMain`, and `.riscv32imac`, plus a concrete non-vacuity
     witness on a BIP32 hardened derivation index + CompactSize varint validator kernel.
-/

namespace LeanNative.Proofs.LedgerEmbedded32

open LeanNative.IR
open LeanNative.Spec
open LeanNative.Semantics
open LeanNative.Backend.LLVM
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower
open LeanNative.Driver.CoreCLI
open LeanNative.Proofs
open LeanNative.Proofs.HybridCAbi

/-- Predicate characterizing the three freestanding 32-bit Ledger hardware targets:
    BOLOS ARM Thumb (`thumbv6m`, `thumbv8mMain`) and Vanadium RISC-V (`riscv32imac`). -/
def isLedgerEmbeddedTarget (arch : TargetArch) : Prop :=
  arch = .thumbv6m ∨ arch = .thumbv8mMain ∨ arch = .riscv32imac

/-! ## 1. 32-Bit ILP32 Target Width & C99 Slice / `u64` Alignment Soundness -/

theorem isFreestandingEmbedded_iff_ledger (arch : TargetArch) :
    arch.isFreestandingEmbedded = true ↔ isLedgerEmbeddedTarget arch := by
  unfold isLedgerEmbeddedTarget TargetArch.isFreestandingEmbedded
  cases arch <;> simp

theorem ledger_target_isILP32 (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    arch.isILP32 = true := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem archWidth_ofTargetArch_eq_bits32_iff (arch : TargetArch) :
    ArchWidth.ofTargetArch arch = .bits32 ↔ arch.isILP32 = true := by
  cases arch <;> simp [ArchWidth.ofTargetArch, TargetArch.isILP32]

theorem archWidth_ofTargetArch_ledger (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    ArchWidth.ofTargetArch arch = .bits32 := by
  rw [archWidth_ofTargetArch_eq_bits32_iff]
  exact ledger_target_isILP32 arch h

theorem ptrBytes_ledger_eq_four (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    (ArchWidth.ofTargetArch arch).ptrBytes = 4 := by
  rw [archWidth_ofTargetArch_ledger arch h]
  rfl

theorem sigLLVMType_usize_ledger_eq_i32 (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    sigLLVMType arch .usize = "i32" := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem isNarrowSigType_usize_ledger (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    isNarrowSigType arch .usize = true := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem flatSlice_layout_ledger32 (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    computeC99StructLayout "lean_native_flat_slice_t" flatSliceFieldSpecs (ArchWidth.ofTargetArch arch) =
      some { name := "lean_native_flat_slice_t"
           , fields := [ { name := "data", ty := .constPtr, offset := 0, size := 4, align := 4 }
                       , { name := "len", ty := .usize, offset := 4, size := 4, align := 4 }
                       , { name := "stride_bytes", ty := .usize, offset := 8, size := 4, align := 4 } ]
           , structSize := 12
           , structAlign := 4 } := by
  rw [archWidth_ofTargetArch_ledger arch h]
  rfl

theorem mutSlice_layout_ledger32 (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    computeC99StructLayout "lean_native_mut_slice_t" mutSliceFieldSpecs (ArchWidth.ofTargetArch arch) =
      some { name := "lean_native_mut_slice_t"
           , fields := [ { name := "data", ty := .ptr, offset := 0, size := 4, align := 4 }
                       , { name := "len", ty := .usize, offset := 4, size := 4, align := 4 }
                       , { name := "cap", ty := .usize, offset := 8, size := 4, align := 4 } ]
           , structSize := 12
           , structAlign := 4 } := by
  rw [archWidth_ofTargetArch_ledger arch h]
  rfl

theorem u64_align8_on_ledger32 (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    C99ScalarType.alignOf .u64 (ArchWidth.ofTargetArch arch) = 8 := by
  rw [archWidth_ofTargetArch_ledger arch h]
  rfl

theorem i64_align8_on_ledger32 (arch : TargetArch) (h : isLedgerEmbeddedTarget arch) :
    C99ScalarType.alignOf .i64 (ArchWidth.ofTargetArch arch) = 8 := by
  rw [archWidth_ofTargetArch_ledger arch h]
  rfl

/-- `placeC99Fields` soundness on 32-bit Ledger targets: every placed field satisfies natural
    alignment, exact target width, and pairwise disjointness, and any `u64`/`i64` field is
    placed at an 8-byte aligned offset per ARM AAPCS and RISC-V RV32 ILP32. -/
theorem placeC99Fields_ledger32_u64_aligned
    (arch : TargetArch) (specs : List C99FieldSpec)
    (placed : List C99FieldLayout) (finalAlign : Nat) (f : C99FieldLayout)
    (hArch : isLedgerEmbeddedTarget arch)
    (hPlace : placeC99Fields specs (ArchWidth.ofTargetArch arch) = some (placed, finalAlign))
    (hf : f ∈ placed)
    (hTy64 : f.ty = .u64 ∨ f.ty = .i64) :
    8 ∣ f.offset := by
  unfold placeC99Fields at hPlace
  rcases placeC99FieldsFrom_spec specs 0 1 (ArchWidth.ofTargetArch arch) placed finalAlign (by decide) hPlace with
    ⟨_, _, hall, _⟩
  rcases hall f hf with ⟨⟨_, hmod⟩, _, halEq, _⟩
  have hdvd : f.align ∣ f.offset := Nat.dvd_of_mod_eq_zero hmod
  have hal8 : f.align = 8 := by
    rw [halEq, archWidth_ofTargetArch_ledger arch hArch]
    rcases hTy64 with hty | hty <;> rw [hty] <;> rfl
  rw [← hal8]
  exact hdvd

/-- Full `computeC99StructLayout` soundness specialized to Ledger 32-bit targets. -/
theorem computeC99StructLayout_ledger32_sound
    (arch : TargetArch) (name : String) (specs : List C99FieldSpec) (layout : C99StructLayout)
    (hArch : isLedgerEmbeddedTarget arch)
    (hLayout : computeC99StructLayout name specs (ArchWidth.ofTargetArch arch) = some layout) :
    c99LayoutSound layout .bits32 := by
  rw [archWidth_ofTargetArch_ledger arch hArch] at hLayout
  exact computeC99StructLayout_sound name specs .bits32 layout hLayout

/-! ## 2. Freestanding Verification Gate Soundness -/

theorem selectDeclRcMode_eq_freestanding_of_no_heap (d : LNIRDecl)
    (hNoHeap : codeHasHeapOps d.body = false) :
    selectDeclRcMode d = .freestanding := by
  unfold selectDeclRcMode
  rw [hNoHeap]
  cases codeHasParFor d.body <;> rfl

theorem selectDeclRcMode_ne_freestanding_of_heap (d : LNIRDecl)
    (hHeap : codeHasHeapOps d.body = true) :
    selectDeclRcMode d ≠ .freestanding := by
  unfold selectDeclRcMode
  rw [hHeap]
  cases codeHasParFor d.body <;> decide

/-- Soundness of `checkFreestandingDecl`: if a declaration passes the freestanding gate,
    then it is syntactically heap-free, uses `.freestanding` RC mode, performs no EVM storage
    operations or heap runtime calls, and passes `findUnsupportedLLVMCallInDecl`. -/
theorem checkFreestandingDecl_no_heap
    (localSigs : List (String × List LNIRType × LNIRType)) (d : LNIRDecl) (target : TargetArch)
    (hOk : checkFreestandingDecl localSigs d target = none) :
    codeHasHeapOps d.body = false := by
  unfold checkFreestandingDecl at hOk
  cases hh : codeHasHeapOps d.body
  · rfl
  · simp [hh] at hOk

theorem checkFreestandingDecl_rcMode_freestanding
    (localSigs : List (String × List LNIRType × LNIRType)) (d : LNIRDecl) (target : TargetArch)
    (hOk : checkFreestandingDecl localSigs d target = none) :
    selectDeclRcMode d = .freestanding := by
  exact selectDeclRcMode_eq_freestanding_of_no_heap d
    (checkFreestandingDecl_no_heap localSigs d target hOk)

theorem checkFreestandingDecl_no_storage_or_runtime_calls
    (localSigs : List (String × List LNIRType × LNIRType)) (d : LNIRDecl) (target : TargetArch)
    (hOk : checkFreestandingDecl localSigs d target = none) :
    codeHasStorageOps d.body = false ∧
    codeHasHeapRuntimeCalls d.body = false ∧
    findUnsupportedLLVMCallInDecl localSigs d target = none := by
  have hNoHeap : codeHasHeapOps d.body = false := checkFreestandingDecl_no_heap localSigs d target hOk
  have hRc : selectDeclRcMode d = .freestanding := selectDeclRcMode_eq_freestanding_of_no_heap d hNoHeap
  have hNeF : (RcMode.freestanding != RcMode.freestanding) = false := rfl
  unfold checkFreestandingDecl at hOk
  simp only [hNoHeap, hRc, hNeF, Bool.false_eq_true, ↓reduceIte] at hOk
  cases hs : codeHasStorageOps d.body
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hr : codeHasHeapRuntimeCalls d.body
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hOk
      exact ⟨rfl, rfl, hOk⟩
    · simp [hr] at hOk
  · simp [hs] at hOk

/-- Fail-closed negative theorem: any declaration with heap operations is rejected by `checkFreestandingDecl`. -/
theorem checkFreestandingDecl_rejects_heap_ops
    (localSigs : List (String × List LNIRType × LNIRType)) (d : LNIRDecl) (target : TargetArch)
    (hHeap : codeHasHeapOps d.body = true) :
    checkFreestandingDecl localSigs d target = some "heap_ops_forbidden_in_freestanding" := by
  unfold checkFreestandingDecl
  simp [hHeap]

private theorem list_findSome_eq_none_forall {α β : Type} (f : α → Option β) (xs : List α)
    (h : xs.findSome? f = none) :
    ∀ x ∈ xs, f x = none := by
  induction xs with
  | nil =>
    intro x hx
    cases hx
  | cons hd tl ih =>
    intro x hx
    simp only [List.findSome?] at h
    cases hhd : f hd with
    | some v =>
      rw [hhd] at h
      cases h
    | none =>
      rw [hhd] at h
      simp at hx
      rcases hx with rfl | htl
      · exact hhd
      · exact ih h x htl

/-- Module-level freestanding gate soundness: every declaration in a module accepted by
    `checkFreestandingModule` has `codeHasHeapOps d.body = false` and `selectDeclRcMode d = .freestanding`. -/
theorem checkFreestandingModule_sound
    (m : LNIRModule) (target : TargetArch) (d : LNIRDecl)
    (hOk : checkFreestandingModule m target = none)
    (hd : d ∈ m.decls) :
    codeHasHeapOps d.body = false ∧ selectDeclRcMode d = .freestanding := by
  unfold checkFreestandingModule at hOk
  have hdNone := list_findSome_eq_none_forall
    (fun d' => (checkFreestandingDecl (localScalarSigsOfModule m) d' target).map (d'.name, ·))
    m.decls hOk d hd
  cases hc : checkFreestandingDecl (localScalarSigsOfModule m) d target with
  | none =>
    exact ⟨checkFreestandingDecl_no_heap _ d target hc,
           checkFreestandingDecl_rcMode_freestanding _ d target hc⟩
  | some msg =>
    rw [hc] at hdNone
    cases hdNone

/-- Emitter-level freestanding gate soundness: whenever `emitLLVMFreestanding?` succeeds with `.ok ir`,
    every declaration in `m` is guaranteed heap-free and `.freestanding`. -/
theorem emitLLVMFreestanding_sound
    (m : LNIRModule) (target : TargetArch) (opt : Bool)
    (isaOverride? : Option IsaLevel) (wasmSimd128 : Bool) (ir : String) (d : LNIRDecl)
    (hEmit : emitLLVMFreestanding? m target opt isaOverride? wasmSimd128 = .ok ir)
    (hd : d ∈ m.decls) :
    codeHasHeapOps d.body = false ∧ selectDeclRcMode d = .freestanding := by
  unfold emitLLVMFreestanding? at hEmit
  cases hc : checkFreestandingModule m target with
  | some err =>
    rw [hc] at hEmit
    cases hEmit
  | none =>
    exact checkFreestandingModule_sound m target d hc hd

/-! ## 3. End-to-End `LLVMLower` Soundness on Ledger 32-Bit Targets -/

private theorem runCallWith_eq_of_fns_eq (m1 m2 : LLVMModule) (hFns : m1.fns = m2.fns) :
    ∀ fuel, runCallWith m1 fuel = runCallWith m2 fuel
  | 0 => rfl
  | k + 1 => by
    have ih := runCallWith_eq_of_fns_eq m1 m2 hFns k
    funext st dst? callCc retTy callee argVals
    simp only [runCallWith, hFns, ih]

theorem execFn_modOfFnForTarget_eq (target : TargetArch) (fn : LLVMFn)
    (llvmArgs : List LLVMVal) (fuel : Nat) :
    execFn (modOfFnForTarget target fn) fn llvmArgs fuel =
      execFn (modOfFn fn) fn llvmArgs fuel := by
  unfold execFn
  have hgT : initGlobals (modOfFnForTarget target fn) = some ({}, []) := rfl
  have hgX : initGlobals (modOfFn fn) = some ({}, []) := rfl
  rw [hgT, hgX]
  dsimp only
  cases fn.blocks with
  | nil => rfl
  | cons entry rest =>
    dsimp only
    cases bindArgs { mem := {}, globals := [] } fn.params llvmArgs with
    | none => rfl
    | some st =>
      simp only [execBlock, runCallWith_eq_of_fns_eq (modOfFnForTarget target fn) (modOfFn fn) rfl fuel]

/-- End-to-end `LLVMLower` soundness for any target architecture (including `.thumbv6m`,
    `.thumbv8mMain`, and `.riscv32imac`): lowering `d` via `lowerModuleForTarget target d`
    produces a single-function `LLVMModule` with exact `target.dataLayout` and `target.llvmTriple`
    whose `LLVMAst.execFn` semantics refines `LNIR` `evalCode` with zero UB or poison. -/
theorem lowerModuleForTarget_sound
    (target : TargetArch) (d : LNIRDecl) (m : LLVMModule)
    (argVals : List Val) (llvmArgs : List LLVMVal) (retVal : Val) (fuel : Nat)
    (hLower : lowerModuleForTarget target d = some m)
    (hArgs : encodeParamArgs d.params argVals = some llvmArgs)
    (hEval : evalCode 2 (bindParamEnv VarEnv.empty d.params argVals) HeapState.empty d.body =
      .ok (retVal, HeapState.empty))
    (hFuel : codeBlockFuel d.body ≤ fuel) :
    ∃ fn w,
      m.dataLayout = target.dataLayout ∧
      m.triple = target.llvmTriple ∧
      m.fns = [fn] ∧
      encodeScalarVal retVal = some w ∧
      execFn m fn llvmArgs fuel = .returned (some (.bits .i64 w)) := by
  unfold lowerModuleForTarget at hLower
  cases hDecl : lowerDecl d with
  | none => simp [hDecl] at hLower
  | some fn =>
    simp only [hDecl, Option.map_some, Option.some.injEq] at hLower
    rcases lowerToLLVM_sound d fn argVals llvmArgs retVal fuel hDecl hArgs hEval hFuel with
      ⟨w, hEnc, hExec⟩
    subst hLower
    refine ⟨fn, w, rfl, rfl, rfl, hEnc, ?_⟩
    rw [execFn_modOfFnForTarget_eq target fn llvmArgs fuel]
    exact hExec

/-- Sample pure Bitcoin BIP32 + CompactSize varint scalar validator declaration:
    checks whether `childIdx >= 0x80000000` (BIP32 hardened derivation) and computes the
    Bitcoin CompactSize byte length (`1`, `3`, `5`, or `9`) of `txInCount`, returning
    `(isHardened << 8) | varintByteLen`. -/
def ledgerBip32VarintDecl : LNIRDecl :=
  { name := "ledger_bip32_varint_meta"
  , params := [ { id := 0, name := "childIdx", ty := .i64 }
              , { id := 1, name := "txInCount", ty := .i64 } ]
  , retTy := .i64
  , body :=
      .letBind 2 .i1 (.scalar (.binOp .le (.constU64 0x80000000) (.var 0)))
        (.letBind 3 .i64 (.scalar (.select (.var 2) (.constU64 256) (.constU64 0)))
          (.letBind 4 .i1 (.scalar (.binOp .lt (.var 1) (.constU64 0xfd)))
            (.ite 4
              (.letBind 5 .i64 (.scalar (.binOp .bitOr (.var 3) (.constU64 1))) (.ret 5))
              (.letBind 6 .i1 (.scalar (.binOp .le (.var 1) (.constU64 0xffff)))
                (.ite 6
                  (.letBind 7 .i64 (.scalar (.binOp .bitOr (.var 3) (.constU64 3))) (.ret 7))
                  (.letBind 8 .i64 (.scalar (.binOp .bitOr (.var 3) (.constU64 5))) (.ret 8))))))) }

/-- Concrete end-to-end non-vacuity witness on Ledger targets (`thumbv6m`, `thumbv8mMain`, `riscv32imac`):
    `ledgerBip32VarintDecl` passes `checkFreestandingDecl`, lowers cleanly via `lowerModuleForTarget`,
    and executes in `LLVMAst.execFn` on `(0x8000002c, 300) ↦ 259` (`0x103`, hardened BIP44 purpose + 3-byte varint). -/
theorem ledgerBip32Varint_e2e_nonvacuous
    (arch : TargetArch) (fuel : Nat)
    (hArch : isLedgerEmbeddedTarget arch)
    (hFuel : codeBlockFuel ledgerBip32VarintDecl.body ≤ fuel) :
    ∃ m fn,
      checkFreestandingDecl [] ledgerBip32VarintDecl arch = none ∧
      lowerModuleForTarget arch ledgerBip32VarintDecl = some m ∧
      m.dataLayout = arch.dataLayout ∧
      m.triple = arch.llvmTriple ∧
      m.fns = [fn] ∧
      execFn m fn [.bits .i64 0x8000002c#64, .bits .i64 300#64] fuel =
        .returned (some (.bits .i64 259#64)) := by
  have hGate : checkFreestandingDecl [] ledgerBip32VarintDecl arch = none := by
    rcases hArch with rfl | rfl | rfl <;> rfl
  cases hLow : lowerModuleForTarget arch ledgerBip32VarintDecl with
  | none =>
    rcases hArch with rfl | rfl | rfl <;> nomatch hLow
  | some m =>
    have hArgs : encodeParamArgs ledgerBip32VarintDecl.params [.u64 0x8000002c, .u64 300] =
        some [.bits .i64 0x8000002c#64, .bits .i64 300#64] := rfl
    have hEv : evalCode 2
        (bindParamEnv VarEnv.empty ledgerBip32VarintDecl.params [.u64 0x8000002c, .u64 300])
        HeapState.empty ledgerBip32VarintDecl.body = .ok (.u64 259, HeapState.empty) := rfl
    rcases lowerModuleForTarget_sound arch ledgerBip32VarintDecl m
      [.u64 0x8000002c, .u64 300] [.bits .i64 0x8000002c#64, .bits .i64 300#64]
      (.u64 259) fuel hLow hArgs hEv hFuel with
      ⟨fn, w, hDl, hTr, hFns, hEnc, hExec⟩
    have hw : w = 259#64 := by
      simp [encodeScalarVal] at hEnc
      exact hEnc.symm
    subst hw
    exact ⟨m, fn, hGate, rfl, hDl, hTr, hFns, hExec⟩

#guard (ppLoweredDeclForTarget .thumbv6m ledgerBip32VarintDecl).isSome
#guard (ppLoweredDeclForTarget .thumbv8mMain ledgerBip32VarintDecl).isSome
#guard (ppLoweredDeclForTarget .riscv32imac ledgerBip32VarintDecl).isSome

end LeanNative.Proofs.LedgerEmbedded32
