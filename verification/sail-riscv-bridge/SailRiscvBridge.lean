import SailRiscvBridge.Bisimulation
import Lean

/-!
# `SailRiscvBridge` Root & Kernel Axiom Audit

Verifies at compile time that every Stage 3E / Milestone `M5` RV64 bisimulation theorem
against upstream `opencompl/sail-riscv-lean` has `0 sorryAx`, `0 Lean.ofReduceBool`,
`0 Lean.trustCompiler`, and `0` computational / reservation / SoftFloat `RiscvExtras`
axioms (`load_reservation`, `match_reservation`, `cancel_reservation`, `valid_reservation`,
`get_16_random_bits`, `plat_term_read`, `riscv_f*` / `riscv_i*` / `riscv_ui*`), allowing
only standard Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) plus
the two dead-branch upstream platform symbols (`sys_enable_experimental_extensions` from
`hartSupports`'s `.Ext_Zibi`/`.Ext_Zvabd` arms and `plat_term_write` from `mmio_write`'s
disabled `htif_tohost_base = none` arm).
-/

namespace SailRiscvBridge.Audit

open Lean Elab Command

def bridgedTheorems : List Name :=
  [ ``SailRiscvBridge.rv64_xlen_params
  , ``SailRiscvBridge.rX_bits_zreg
  , ``SailRiscvBridge.wX_bits_zreg_noop
  , ``SailRiscvBridge.wX_then_rX_x1
  , ``SailRiscvBridge.to_bits_truncate_eq_ofInt
  , ``SailRiscvBridge.riscvDivU64Spec_bisim_sail
  , ``SailRiscvBridge.riscvRemU64Spec_bisim_sail
  , ``SailRiscvBridge.riscvDivRemU64Spec_euclidean
  , ``SailRiscvBridge.mult_to_bits_half_low_unsigned_eq_mul
  , ``SailRiscvBridge.mult_to_bits_half_high_unsigned_toNat
  , ``SailRiscvBridge.encdec_mul_op_roundtrip
  , ``SailRiscvBridge.clmul64_eq_sail_carryless_mul_lo
  , ``SailRiscvBridge.clmul64Hi_eq_sail_carryless_mul_hi
  , ``SailRiscvBridge.clmul64_pair_eq_sail_carryless_mul
  , ``SailRiscvBridge.riscvDivS64Spec_bisim_sail
  , ``SailRiscvBridge.riscvRemS64Spec_bisim_sail
  , ``SailRiscvBridge.riscvDivRemS64Spec_euclidean
  , ``SailRiscvBridge.mult_to_bits_half_high_signed_eq_mulh
  , ``SailRiscvBridge.mult_to_bits_half_high_signed_unsigned_eq_mulhsu
  , ``SailRiscvBridge.sail_carryless_mulr_eq_extract_carryless_mul
  , ``SailRiscvBridge.clmul64RSpec_bisim_sail
  , ``SailRiscvBridge.sail_carryless_mul_comm
  , ``SailRiscvBridge.clmul64_comm
  , ``SailRiscvBridge.clmul64Hi_comm
  , ``SailRiscvBridge.clmul64_direct_order_bisim_sail
  , ``SailRiscvBridge.rv64iRtypeSpec_bisim_sail
  , ``SailRiscvBridge.rv64iItypeSpec_bisim_sail
  , ``SailRiscvBridge.rv64iShiftIopSpec_bisim_sail
  , ``SailRiscvBridge.get_arch_pc_run
  , ``SailRiscvBridge.rv64iUtypeSpec_bisim_sail_x1
  , ``SailRiscvBridge.rv64iBtypeTakenSpec_bisim_sail
  , ``SailRiscvBridge.sailBtypeTakenCore_complement
  , ``SailRiscvBridge.rv64iRtypewSpec_bisim_sail
  , ``SailRiscvBridge.rv64iAddiwSpec_bisim_sail
  , ``SailRiscvBridge.rv64iShiftIwopSpec_bisim_sail
  , ``SailRiscvBridge.riscvMulwSpec_bisim_sail
  , ``SailRiscvBridge.riscvDivwSpec_bisim_sail
  , ``SailRiscvBridge.riscvDivuwSpec_bisim_sail
  , ``SailRiscvBridge.riscvRemwSpec_bisim_sail
  , ``SailRiscvBridge.riscvRemuwSpec_bisim_sail
  , ``SailRiscvBridge.riscvDivRemW_euclidean
  , ``SailRiscvBridge.rv64iJalSpec_bisim_sail
  , ``SailRiscvBridge.rv64iJalrSpec_bisim_sail
  , ``SailRiscvBridge.rv64iJumpTargetAlignedSpec_bisim_sail
  , ``SailRiscvBridge.pcAccess_redirect_and_tick_bisim
  , ``SailRiscvBridge.jal_x1_state_bisim_sail
  , ``SailRiscvBridge.jalr_same_reg_x1_state_bisim_sail
  , ``SailRiscvBridge.rv64Zba_bisim_sail
  , ``SailRiscvBridge.rv64Zbs_bisim_sail
  , ``SailRiscvBridge.rv64ZbbAluRotExt_bisim_sail
  , ``SailRiscvBridge.rv64ZbbRev8Spec_bisim_sail
  , ``SailRiscvBridge.rv64ZbbOrcbSpec_bisim_sail
  , ``SailRiscvBridge.rv64ZbbClzCtz_bisim_sail
  , ``SailRiscvBridge.rv64ZbbCpop_bisim_sail
  , ``SailRiscvBridge.rv64iEffectiveAddr_ext_data_get_addr_bisim
  , ``SailRiscvBridge.rv64iAlignedAddr_bisim_sail
  , ``SailRiscvBridge.rv64iLoadExtend_bisim_sail
  , ``SailRiscvBridge.rv64iStoreTruncate_bisim_sail
  , ``SailRiscvBridge.write_ram_plain_bisim_sail
  , ``SailRiscvBridge.read_ram_plain_bisim_sail
  , ``SailRiscvBridge.sailStoreRamExec_sp_ra_bisim
  , ``SailRiscvBridge.sailLoadRamExec_sp_ra_bisim
  , ``SailRiscvBridge.rv64StoreLoadBytes_roundtrip_1
  , ``SailRiscvBridge.rv64StoreLoadBytes_roundtrip_2
  , ``SailRiscvBridge.rv64StoreLoadBytes_roundtrip_4
  , ``SailRiscvBridge.rv64StoreLoadBytes_roundtrip_8
  , ``SailRiscvBridge.rv64StoreThenLoad_roundtrip_bisim
  , ``SailRiscvBridge.rvcRegIdx_creg2reg_idx_bisim
  , ``SailRiscvBridge.rvcNopIllegal_bisim_sail
  , ``SailRiscvBridge.rvcStackPointerAddi_bisim_sail
  , ``SailRiscvBridge.rvcLiLui_bisim_sail
  , ``SailRiscvBridge.rvcAluImmShift_bisim_sail
  , ``SailRiscvBridge.rvcAluReg_bisim_sail
  , ``SailRiscvBridge.rvcLoad_bisim_sail
  , ``SailRiscvBridge.rvcStore_bisim_sail
  , ``SailRiscvBridge.rvcBranch_bisim_sail
  , ``SailRiscvBridge.rvcJumpExpand_bisim_sail
  , ``SailRiscvBridge.rvcJalr_x1_state_bisim_sail
  , ``SailRiscvBridge.rvcZcbExpand_bisim_sail
  , ``SailRiscvBridge.rvcZcbDirectSailM_x8_bisim
  , ``SailRiscvBridge.rv64ZaamoEncdec_bisim_sail
  , ``SailRiscvBridge.rv64ZaamoAlu_bisim_sail
  , ``SailRiscvBridge.rv64ZacasRegPair_bisim_sail
  , ``SailRiscvBridge.sailAmo64RamExec_bisim_sail
  , ``SailRiscvBridge.rv64ZalrscFlagsAndWidths_bisim_sail
  , ``SailRiscvBridge.rv64ZalrscRamAndScStatus_bisim_sail
  , ``SailRiscvBridge.rv64ZicsrOpAndAccess_bisim_sail
  , ``SailRiscvBridge.rv64ZicsrPrivAndReadOnlyCheck_bisim_sail
  , ``SailRiscvBridge.rv64PrivEffectiveAndTvm_bisim_sail
  , ``SailRiscvBridge.rv64Satp64ModeDecode_bisim_sail
  , ``SailRiscvBridge.rv64Sv39Sv48CanonicalVaddr_bisim_sail
  , ``SailRiscvBridge.rv64SvPtePermissionsAndDirtyBits_bisim_sail
  , ``SailRiscvBridge.rv64TranslationException_bisim_sail
  , ``SailRiscvBridge.rv64TlbMatchPpnAndSfence_bisim_sail
  , ``SailRiscvBridge.rv64SfenceVmaAndTlbLookup_bisim_sail
  , ``SailRiscvBridge.rv64PmpAndPmaCheck_bisim_sail
  , ``SailRiscvBridge.rv64ReadWritePte_bisim_sail
  , ``SailRiscvBridge.rv64UpdateAndWritePte_bisim_sail
  , ``SailRiscvBridge.rv64PtWalkSv39_bisim_sail
  , ``SailRiscvBridge.rv64PtWalkSv48_bisim_sail
  , ``SailRiscvBridge.rv64TranslateTlbHitAndMiss_bisim_sail
  , ``SailRiscvBridge.rv64TranslateAndTranslateAddr_bisim_sail
  , ``SailRiscvBridge.rv64TrapVectorAndXepc_bisim_sail
  , ``SailRiscvBridge.rv64ExceptionDelegateeAndSyncExc_bisim_sail
  , ``SailRiscvBridge.rv64InterruptPriorityAndDispatch_bisim_sail
  , ``SailRiscvBridge.rv64TrapHandlerMachineAndSupervisor_bisim_sail
  , ``SailRiscvBridge.rv64Mret_bisim_sail
  , ``SailRiscvBridge.rv64Sret_bisim_sail
  , ``SailRiscvBridge.rv64FpEnablementAndNanBoxing_bisim_sail
  , ``SailRiscvBridge.rv64FpRegsAndDirtyContext_bisim_sail
  , ``SailRiscvBridge.rv64FcsrRoundingAndAccrueFflags_bisim_sail
  , ``SailRiscvBridge.rv64FpSplitPredicatesAndCompare_bisim_sail
  , ``SailRiscvBridge.rv64FloatClassifyAndOnehot_bisim_sail
  , ``SailRiscvBridge.rv64FpLoadStoreAndRvcExec_bisim_sail
  , ``SailRiscvBridge.rv64FpMoveAndClassifyExec_bisim_sail
  , ``SailRiscvBridge.rv64FpSignInjectAndMinMaxExec_bisim_sail
  ]

set_option maxRecDepth 4096 in
theorem bridgedTheorems_nodup : bridgedTheorems.Nodup := by
  decide

def minAuditedTheorems : Nat := 116

def allowedAxioms : List Name :=
  [ ``propext
  , ``Classical.choice
  , ``Quot.sound
  , ``sys_enable_experimental_extensions
  , ``plat_term_write
  ]

elab "#verify_sail_riscv_bridge_axioms" : command => do
  let env ← getEnv
  if bridgedTheorems.length < minAuditedTheorems then
    throwError "Expected at least {minAuditedTheorems} bridged theorems, found {bridgedTheorems.length}"
  let mut seen : List Name := []
  for thm in bridgedTheorems do
    if seen.contains thm then
      throwError "Duplicate bridged theorem {thm} in bridgedTheorems"
    seen := thm :: seen
    let some _ := env.find? thm
      | throwError "Missing bridged theorem {thm}"
    let axs ← liftCoreM <| Lean.collectAxioms thm
    for ax in axs do
      if !allowedAxioms.contains ax then
        throwError "Forbidden axiom {ax} in theorem {thm} (found {axs})"
  logInfo m!"[sail-riscv-bridge] Verified {bridgedTheorems.length} RV64 bisimulation theorems (0 sorryAx, 0 SoftFloat/reservation axioms)"

#verify_sail_riscv_bridge_axioms

end SailRiscvBridge.Audit
