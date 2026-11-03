import LeanNative.Proofs.PTXSIMT2

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst

/-! ## 5. Instruction-level execution lemmas

    Concrete `execNonBarrierInstr` equations for the instruction subset emitted by `PTXLower`,
    derived under `RegTyped` register files and the `SafePTXLog` memory invariant. -/

@[simp] private theorem mask_u64_id (v : BitVec 64) : maskForType .u64 v = v := rfl
@[simp] private theorem mask_b64_id (v : BitVec 64) : maskForType .b64 v = v := rfl
@[simp] private theorem mask_s64_id (v : BitVec 64) : maskForType .s64 v = v := rfl
@[simp] private theorem mask_b32_eq (v : BitVec 64) : maskForType .b32 v = v &&& 0xFFFF_FFFF#64 := rfl

@[simp] theorem mask32_id (v : BitVec 64) (hfit : (v >>> 32) = 0#64) :
    maskForType .u32 v = v := by
  have hdiv : v.toNat / 4294967296 = 0 := by
    have := congrArg BitVec.toNat hfit
    simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this
  have hlt : v.toNat < 4294967296 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [maskForType, BitVec.toNat_and, BitVec.toNat_ofNat]
  have heq : 4294967295 % 2 ^ 64 = 2 ^ 32 - 1 := by decide
  rw [heq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]

private theorem evalOp_reg_rd (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (i : Nat) (hi : i < nRd)
    (v : BitVec 64) (hlk : th.regs.regs.lookup s!"%rd{i}" = some (.scalar v)) :
    evalOperand cta th (.reg s!"%rd{i}") (some 64) = .ok v := by
  unfold evalOperand; exact readScalarChecked_rd hrt i hi v hlk

private theorem evalOp_reg_r (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (i : Nat) (hi : i < nR)
    (v : BitVec 64) (hlk : th.regs.regs.lookup s!"%r{i}" = some (.scalar v)) :
    evalOperand cta th (.reg s!"%r{i}") (some 32) = .ok v := by
  unfold evalOperand; exact readScalarChecked_r hrt i hi v hlk

private theorem evalOp_imm (cta : PTXCTAState) (th : PTXThreadState) (v : BitVec 64) (w : Option Nat) :
    evalOperand cta th (.immU64 v) w = .ok v := rfl

private theorem evalOp_sreg (cta : PTXCTAState) (th : PTXThreadState) (sr : SpecialReg) (w : Option Nat) :
    evalOperand cta th (.sreg sr) w =
      .ok (evalSpecialReg cta.gridDim cta.blockDim cta.ctaId th.tid sr) := rfl

private theorem setScalar_rd_simp (th : PTXThreadState) {nP nR nRd : Nat}
    (hrt : RegTyped th.regs nP nR nRd) (i : Nat) (hi : i < nRd) (v : BitVec 64) :
    th.regs.setScalar s!"%rd{i}" v (some 64) = .ok (th.regs.setScalarRaw s!"%rd{i}" v) :=
  setScalar_rd hrt i hi v

private theorem setScalar_r_simp (th : PTXThreadState) {nP nR nRd : Nat}
    (hrt : RegTyped th.regs nP nR nRd) (i : Nat) (hi : i < nR) (v : BitVec 64)
    (hfit : (v >>> 32) = 0#64) :
    th.regs.setScalar s!"%r{i}" v (some 32) =
      .ok (th.regs.setScalarRaw s!"%r{i}" (v &&& 0xFFFF_FFFF#64)) :=
  setScalar_r hrt i hi v hfit

private theorem setPred_p_simp (th : PTXThreadState) {nP nR nRd : Nat}
    (hrt : RegTyped th.regs nP nR nRd) (i : Nat) (hi : i < nP) (b : Bool) :
    th.regs.setPred s!"%p{i}" b = .ok (th.regs.setPredRaw s!"%p{i}" b) :=
  setPred_p hrt i hi b

@[simp] private theorem ptxOk_bind {α β : Type} (x : α) (f : α → PTXOutcome β) :
    (PTXOutcome.ok x).bind f = f x := rfl

@[simp] private theorem ptxBitWidth_u64 : PTXType.u64.bitWidth = 64 := rfl
@[simp] private theorem ptxBitWidth_b64 : PTXType.b64.bitWidth = 64 := rfl
@[simp] private theorem ptxBitWidth_s64 : PTXType.s64.bitWidth = 64 := rfl
@[simp] private theorem ptxBitWidth_u32 : PTXType.u32.bitWidth = 32 := rfl
@[simp] private theorem ptxBitWidth_b32 : PTXType.b32.bitWidth = 32 := rfl
@[simp] private theorem ptxByteWidth_u64 : PTXType.u64.byteWidth = 8 := rfl
@[simp] private theorem ptxIsBit_b64 : PTXType.b64.isBitType = true := rfl
@[simp] private theorem ptxIsBit_b32 : PTXType.b32.isBitType = true := rfl
@[simp] private theorem ptxEq_u32_pred : (PTXType.u32 == .pred) = false := rfl
@[simp] private theorem ptxEq_u32_b32 : (PTXType.u32 == .b32) = false := rfl
@[simp] private theorem ptxEq_u32_s32 : (PTXType.u32 == .s32) = false := rfl

section ExecLemmas
set_option linter.unusedSimpArgs false

def thStep (th : PTXThreadState) (rf' : PTXRegFile) : PTXThreadState :=
  { th with pc := th.pc + 1, regs := rf' }

def thMem (th : PTXThreadState) : PTXThreadState :=
  { th with pc := th.pc + 1 }

local macro "ptx_exec_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [execNonBarrierInstr, evalAddr, checkAligned, recordEpochAccess,
    ptxBitWidth_u64, ptxBitWidth_b64, ptxBitWidth_s64, ptxBitWidth_u32, ptxBitWidth_b32,
    ptxByteWidth_u64, ptxIsBit_b64, ptxIsBit_b32, ptxOk_bind,
    Bool.not_true, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true,
    mask_u64_id, mask_b64_id, mask_s64_id, mask_b32_eq, ptxEq_u32_pred, ptxEq_u32_b32, ptxEq_u32_s32,
    Bool.false_eq_true, ite_false, ite_true, thStep, thMem,
    (show (PTXType.u64 == .pred) = false from rfl),
    (show (PTXType.u64 == .f32) = false from rfl),
    (show (PTXType.u64 == .f64) = false from rfl),
    (show (PTXType.u64 == .s64) = false from rfl),
    (show (PTXType.u64 == .s32) = false from rfl),
    (show (PTXType.u64 == .b8) = false from rfl),
    (show (PTXType.b64 == .pred) = false from rfl),
    (show (PTXType.b64 == .b8) = false from rfl),
    (show (PTXType.b32 == .pred) = false from rfl),
    (show (PTXType.s64 == .f32) = false from rfl),
    (show (PTXType.s64 == .f64) = false from rfl),
    (show (PTXType.s64 == .pred) = false from rfl),
    (show (PTXType.s64 == .b8) = false from rfl),
    (show (PTXType.u32 == .f32) = false from rfl),
    (show (PTXType.u32 == .f64) = false from rfl),
    (show (PTXMulMode.lo == .wide) = false from rfl),
    (show (PTXMulMode.lo == .rn) = false from rfl),
    (show (PTXMulMode.wide == .wide) = true from rfl),
    (show (PTXType.u32 == .u32) = true from rfl), $args,*])

theorem exec_mov_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di si : Nat)
    (hdi : di < nRd) (hsi : si < nRd) (v : BitVec 64)
    (hlk : th.regs.regs.lookup s!"%rd{si}" = some (.scalar v)) :
    execNonBarrierInstr stmts cta th (.mov .u64 s!"%rd{di}" (.reg s!"%rd{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v), cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt si hsi v hlk, mask_u64_id,
    setScalar_rd_simp th hrt di hdi v]

theorem exec_mov_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di : Nat) (hdi : di < nRd) (v : BitVec 64) :
    execNonBarrierInstr stmts cta th (.mov .u64 s!"%rd{di}" (.immU64 v)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v), cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_imm cta th v _, mask_u64_id, setScalar_rd_simp th hrt di hdi v]

theorem exec_mov_sreg_r (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di : Nat) (hdi : di < nR)
    (sr : SpecialReg) (v : BitVec 64)
    (hv : evalSpecialReg cta.gridDim cta.blockDim cta.ctaId th.tid sr = v)
    (hfit : (v >>> 32) = 0#64) :
    execNonBarrierInstr stmts cta th (.mov .u32 s!"%r{di}" (.sreg sr)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%r{di}" (v &&& 0xFFFF_FFFF#64)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_sreg cta th sr _, hv, mask32_id v hfit, setScalar_r_simp th hrt di hdi v hfit]

theorem exec_add_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.add .none .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va + vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va + vb)]

theorem exec_add_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (va c : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.add .none .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 c)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va + c)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_imm cta th c _,
    mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va + c)]

theorem exec_sub_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.sub .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va - vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va - vb)]

theorem exec_mul_lo_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.mul .lo .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va * vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va * vb)]

theorem exec_mul_lo_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (va c : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.mul .lo .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 c)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va * c)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_imm cta th c _,
    mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va * c)]

theorem exec_mul_wide_u32 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nR) (hbi : bi < nR) (va vb : BitVec 64)
    (hfa : (va >>> 32) = 0#64) (hfb : (vb >>> 32) = 0#64)
    (hla : th.regs.regs.lookup s!"%r{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%r{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.mul .wide .u32 s!"%rd{di}" (.reg s!"%r{ai}") (.reg s!"%r{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va * vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_r cta th hrt ai hai va hla, evalOp_reg_r cta th hrt bi hbi vb hlb,
    (show va &&& 4294967295#64 = va from mask32_id va hfa),
    (show vb &&& 4294967295#64 = vb from mask32_id vb hfb),
    setScalar_rd_simp th hrt di hdi (va * vb)]

theorem exec_mad_lo_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi ci : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (hci : ci < nRd)
    (va vb vc : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb))
    (hlc : th.regs.regs.lookup s!"%rd{ci}" = some (.scalar vc)) :
    execNonBarrierInstr stmts cta th
        (.mad .lo .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}") (.reg s!"%rd{ci}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va * vb + vc)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    evalOp_reg_rd cta th hrt ci hci vc hlc,
    mask_u64_id, mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va * vb + vc)]

theorem exec_mad_lo_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai ci : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hci : ci < nRd) (va vc c : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlc : th.regs.regs.lookup s!"%rd{ci}" = some (.scalar vc)) :
    execNonBarrierInstr stmts cta th
        (.mad .lo .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 c) (.reg s!"%rd{ci}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va * c + vc)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_imm cta th c _,
    evalOp_reg_rd cta th hrt ci hci vc hlc,
    mask_u64_id, mask_u64_id, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (va * c + vc)]

theorem exec_div_u64 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hnz : vb ≠ 0#64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.div .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va / vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hne : (vb == 0#64) = false := beq_eq_false_iff_ne.mpr hnz
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_u64_id, mask_u64_id, hne, setScalar_rd_simp th hrt di hdi (va / vb)]

theorem exec_rem_u64 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hnz : vb ≠ 0#64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.rem .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va % vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hne : (vb == 0#64) = false := beq_eq_false_iff_ne.mpr hnz
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_u64_id, mask_u64_id, hne, setScalar_rd_simp th hrt di hdi (va % vb)]

theorem exec_bitAnd_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.bitAnd .b64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va &&& vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_b64_id, mask_b64_id,
    setScalar_rd_simp th hrt di hdi (va &&& vb)]

theorem exec_bitAnd_r_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nR) (hai : ai < nR) (va c : BitVec 64)
    (hla : th.regs.regs.lookup s!"%r{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.bitAnd .b32 s!"%r{di}" (.reg s!"%r{ai}") (.immU64 c)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%r{di}" ((va &&& c) &&& 0xFFFF_FFFF#64)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hfit' : ((va &&& c &&& 4294967295#64) >>> 32) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have heq : 4294967295 % 2 ^ 64 = 2 ^ 32 - 1 := by decide
    rw [heq, Nat.and_two_pow_sub_one_eq_mod]
    have hlt : (va.toNat &&& c.toNat) % 2 ^ 32 < 4294967296 := Nat.mod_lt _ (by decide)
    omega
  have hassoc : va &&& (c &&& 4294967295#64) = va &&& c &&& 4294967295#64 := (BitVec.and_assoc va c 4294967295#64).symm
  have hself : va &&& c &&& 4294967295#64 &&& 4294967295#64 = va &&& c &&& 4294967295#64 := by
    rw [BitVec.and_assoc, BitVec.and_self]
  ptx_exec_simp [evalOp_reg_r cta th hrt ai hai va hla, evalOp_imm cta th c _, hassoc,
    setScalar_r_simp th hrt di hdi (va &&& c &&& 4294967295#64) hfit', hself]

theorem exec_bitOr_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.bitOr .b64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va ||| vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_b64_id, mask_b64_id,
    setScalar_rd_simp th hrt di hdi (va ||| vb)]

theorem exec_bitXor_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.bitXor .b64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va ^^^ vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    mask_b64_id, mask_b64_id,
    setScalar_rd_simp th hrt di hdi (va ^^^ vb)]

theorem exec_bitNot_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (va : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.bitNot .b64 s!"%rd{di}" (.reg s!"%rd{ai}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (~~~va)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, mask_b64_id,
    setScalar_rd_simp th hrt di hdi (~~~va)]

theorem exec_neg_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (va : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.neg .s64 s!"%rd{di}" (.reg s!"%rd{ai}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (0#64 - va)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, mask_s64_id,
    setScalar_rd_simp th hrt di hdi (0#64 - va)]

private theorem evalShift_r (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (si : Nat) (hsi : si < nR)
    (v : BitVec 64) (hfit : (v >>> 32) = 0#64)
    (hlk : th.regs.regs.lookup s!"%r{si}" = some (.scalar v)) :
    evalShiftAmount cta th (.reg s!"%r{si}") = .ok v.toNat := by
  have hne : ((v >>> 32) != 0#64) = false := by rw [hfit]; rfl
  have hmask : v &&& 0xFFFF_FFFF#64 = v := mask32_id v hfit
  simp only [evalShiftAmount, ptxBitWidth_u32, evalOp_reg_r cta th hrt si hsi v hlk,
    ptxOk_bind, hne, Bool.false_eq_true, ite_false, hmask]

theorem exec_shl_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai si : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hsi : si < nR) (va vs : BitVec 64)
    (hfit : (vs >>> 32) = 0#64) (hsh : vs.toNat < 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hls : th.regs.regs.lookup s!"%r{si}" = some (.scalar vs)) :
    execNonBarrierInstr stmts cta th (.shl .b64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%r{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va <<< vs.toNat)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hlt : ¬ vs.toNat ≥ 64 := by omega
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, mask_b64_id,
    evalShift_r cta th hrt si hsi vs hfit hls, hlt, ite_false,
    setScalar_rd_simp th hrt di hdi (va <<< vs.toNat)]

theorem exec_shr_u64 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai si : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hsi : si < nR) (va vs : BitVec 64)
    (hfit : (vs >>> 32) = 0#64) (hsh : vs.toNat < 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hls : th.regs.regs.lookup s!"%r{si}" = some (.scalar vs)) :
    execNonBarrierInstr stmts cta th (.shr .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%r{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va >>> vs.toNat)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hlt : ¬ vs.toNat ≥ 64 := by omega
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, mask_u64_id,
    evalShift_r cta th hrt si hsi vs hfit hls, hlt, ite_false,
    setScalar_rd_simp th hrt di hdi (va >>> vs.toNat)]

theorem exec_shr_s64 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai si : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hsi : si < nR) (va vs : BitVec 64)
    (hfit : (vs >>> 32) = 0#64) (hsh : vs.toNat < 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hls : th.regs.regs.lookup s!"%r{si}" = some (.scalar vs)) :
    execNonBarrierInstr stmts cta th (.shr .s64 s!"%rd{di}" (.reg s!"%rd{ai}") (.reg s!"%r{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (BitVec.sshiftRight va vs.toNat)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hcl : (if vs.toNat ≥ 63 then 63 else vs.toNat) = vs.toNat := by split <;> omega
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalShift_r cta th hrt si hsi vs hfit hls, hcl,
    setScalar_rd_simp th hrt di hdi (BitVec.sshiftRight va vs.toNat)]

theorem exec_cvt_u32_u64 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di si : Nat)
    (hdi : di < nR) (hsi : si < nRd) (v : BitVec 64)
    (hlk : th.regs.regs.lookup s!"%rd{si}" = some (.scalar v)) :
    execNonBarrierInstr stmts cta th (.cvt .none .u32 .u64 s!"%r{di}" (.reg s!"%rd{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%r{di}" ((v &&& 0xFFFF_FFFF#64) &&& 0xFFFF_FFFF#64)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hout : evalPTXCvt .none .u32 .u64 v = .ok (v &&& 0xFFFF_FFFF#64) := rfl
  have hfit : ((v &&& 0xFFFF_FFFF#64) >>> 32) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have heq : 4294967295 % 2 ^ 64 = 2 ^ 32 - 1 := by decide
    rw [heq, Nat.and_two_pow_sub_one_eq_mod]
    have hlt : v.toNat % 2 ^ 32 < 4294967296 := Nat.mod_lt _ (by decide)
    omega
  ptx_exec_simp [evalOp_reg_rd cta th hrt si hsi v hlk, hout,
    setScalar_r_simp th hrt di hdi (v &&& 0xFFFF_FFFF#64) hfit]

theorem exec_cvt_u64_u32 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di si : Nat)
    (hdi : di < nRd) (hsi : si < nR) (v : BitVec 64) (hfit : (v >>> 32) = 0#64)
    (hlk : th.regs.regs.lookup s!"%r{si}" = some (.scalar v)) :
    execNonBarrierInstr stmts cta th (.cvt .none .u64 .u32 s!"%rd{di}" (.reg s!"%r{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hout : evalPTXCvt .none .u64 .u32 v = .ok v := by
    change PTXOutcome.ok (maskForType .u64 (maskForType .u32 v)) = PTXOutcome.ok v
    rw [mask32_id v hfit, mask_u64_id]
  ptx_exec_simp [evalOp_reg_r cta th hrt si hsi v hlk, hout, setScalar_rd_simp th hrt di hdi v]

theorem exec_setp_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (cmp : PTXCmpOp) (pi ai bi : Nat)
    (hpi : pi < nP) (hai : ai < nRd) (hbi : bi < nRd) (va vb : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va))
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar vb)) :
    execNonBarrierInstr stmts cta th (.setp cmp .u64 s!"%p{pi}" (.reg s!"%rd{ai}") (.reg s!"%rd{bi}")) =
      .ok (thStep th (th.regs.setPredRaw s!"%p{pi}" (evalPTXCmp cmp .u64 va vb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_reg_rd cta th hrt bi hbi vb hlb,
    setPred_p_simp th hrt pi hpi (evalPTXCmp cmp .u64 va vb)]

theorem exec_setp_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (cmp : PTXCmpOp) (pi ai : Nat)
    (hpi : pi < nP) (hai : ai < nRd) (va c : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.setp cmp .u64 s!"%p{pi}" (.reg s!"%rd{ai}") (.immU64 c)) =
      .ok (thStep th (th.regs.setPredRaw s!"%p{pi}" (evalPTXCmp cmp .u64 va c)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_imm cta th c _,
    setPred_p_simp th hrt pi hpi (evalPTXCmp cmp .u64 va c)]

theorem exec_selp_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ti fi pi : Nat)
    (hdi : di < nRd) (hti : ti < nRd) (hfi : fi < nRd) (hpi : pi < nP)
    (vt vf : BitVec 64) (cond : Bool)
    (hlt : th.regs.regs.lookup s!"%rd{ti}" = some (.scalar vt))
    (hlf : th.regs.regs.lookup s!"%rd{fi}" = some (.scalar vf))
    (hlp : th.regs.regs.lookup s!"%p{pi}" = some (.pred cond)) :
    execNonBarrierInstr stmts cta th
        (.selp .u64 s!"%rd{di}" (.reg s!"%rd{ti}") (.reg s!"%rd{fi}") s!"%p{pi}") =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (if cond then vt else vf)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [readPredChecked_p hrt pi hpi cond hlp,
    evalOp_reg_rd cta th hrt ti hti vt hlt, evalOp_reg_rd cta th hrt fi hfi vf hlf,
    mask_u64_id,
    setScalar_rd_simp th hrt di hdi (if cond then vt else vf)]

theorem exec_selp_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di pi : Nat)
    (hdi : di < nRd) (hpi : pi < nP) (vt vf : BitVec 64) (cond : Bool)
    (hlp : th.regs.regs.lookup s!"%p{pi}" = some (.pred cond)) :
    execNonBarrierInstr stmts cta th
        (.selp .u64 s!"%rd{di}" (.immU64 vt) (.immU64 vf) s!"%p{pi}") =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (if cond then vt else vf)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [readPredChecked_p hrt pi hpi cond hlp, evalOp_imm cta th vt _, evalOp_imm cta th vf _,
    mask_u64_id,
    setScalar_rd_simp th hrt di hdi (if cond then vt else vf)]

theorem exec_ldParam_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di : Nat) (hdi : di < nRd)
    (pname : String) (v : BitVec 64)
    (hlk : cta.paramMem.lookupParam? pname = some v) :
    execNonBarrierInstr stmts cta th (.ldParam .u64 s!"%rd{di}" pname) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v), cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [hlk, mask_u64_id, setScalar_rd_simp th hrt di hdi v]

theorem exec_cvta_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di si : Nat)
    (hdi : di < nRd) (hsi : si < nRd) (v : BitVec 64)
    (hlk : th.regs.regs.lookup s!"%rd{si}" = some (.scalar v)) :
    execNonBarrierInstr stmts cta th (.cvtaToGlobal .u64 s!"%rd{di}" (.reg s!"%rd{si}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v), cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt si hsi v hlk, mask_u64_id,
    setScalar_rd_simp th hrt di hdi v]

theorem exec_ldGlobal_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (outBase len : Nat)
    (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (di bi : Nat) (hdi : di < nRd) (hbi : bi < nRd) (base : Nat) (v : BitVec 64)
    (hlk : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar (BitVec.ofNat 64 base)))
    (hbase : base < 2 ^ 64) (halign : base % 8 = 0)
    (hload : cta.globalMem.loadBits base 8 = some v)
    (hlog : SafePTXLog outBase len allowedLanes laneOf cta.epochLog)
    (hin : base + 8 ≤ outBase) :
    execNonBarrierInstr stmts cta th (.ldGlobal .u64 s!"%rd{di}" (.regOffset s!"%rd{bi}" 0)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v), cta.globalMem, cta.sharedMem,
        { tid := th.tid, space := .global, addr := base, width := 8, isWrite := false,
          isAtomic := false } :: cta.epochLog) := by
  have hread := readScalarChecked_rd hrt bi hbi _ hlk
  have htoNat : (BitVec.ofNat 64 base).toNat = base := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbase]
  have hnn : ¬ (Int.ofNat base + 0 < 0) := by simp [Int.add_zero]
  have haddr : (Int.ofNat base + 0).toNat = base := by simp [Int.add_zero]
  have hnoRace := findDataRace_none_read outBase len allowedLanes laneOf cta.epochLog th.tid base hlog hin
  have haligned : (base % 8 == 0) = true := by simp [halign]
  ptx_exec_simp [hread, htoNat, hnn, ite_false, haddr, haligned, hnoRace, hload,
    mask_u64_id, setScalar_rd_simp th hrt di hdi v]

theorem exec_ldGlobal_rd_disp (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (outBase len : Nat)
    (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (di bi : Nat) (hdi : di < nRd) (hbi : bi < nRd) (base : Nat) (disp : Int) (v : BitVec 64)
    (hlk : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar (BitVec.ofNat 64 base)))
    (hbase : base < 2 ^ 64) (hnn : ¬ (Int.ofNat base + disp < 0))
    (halign : (Int.ofNat base + disp).toNat % 8 = 0)
    (hload : cta.globalMem.loadBits (Int.ofNat base + disp).toNat 8 = some v)
    (hlog : SafePTXLog outBase len allowedLanes laneOf cta.epochLog)
    (hin : (Int.ofNat base + disp).toNat + 8 ≤ outBase) :
    execNonBarrierInstr stmts cta th (.ldGlobal .u64 s!"%rd{di}" (.regOffset s!"%rd{bi}" disp)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" v), cta.globalMem, cta.sharedMem,
        { tid := th.tid, space := .global, addr := (Int.ofNat base + disp).toNat, width := 8,
          isWrite := false, isAtomic := false } :: cta.epochLog) := by
  have hread := readScalarChecked_rd hrt bi hbi _ hlk
  have htoNat : (BitVec.ofNat 64 base).toNat = base := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbase]
  have hnoRace := findDataRace_none_read outBase len allowedLanes laneOf cta.epochLog th.tid
    (Int.ofNat base + disp).toNat hlog hin
  have haligned : ((Int.ofNat base + disp).toNat % 8 == 0) = true := beq_iff_eq.mpr halign
  have h1 : (if Int.ofNat base + disp < 0 then
      PTXOutcome.invalidOperand s!"negative effective address {Int.ofNat base + disp}"
    else PTXOutcome.ok (Int.ofNat base + disp).toNat) = .ok (Int.ofNat base + disp).toNat :=
    ite_eq_right hnn
  ptx_exec_simp [hread, htoNat, h1, haligned, hnoRace, hload,
    mask_u64_id, setScalar_rd_simp th hrt di hdi v]

theorem exec_stGlobal_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (outBase len : Nat)
    (allowedLanes : Nat → Prop) (laneOf : Dim3 → Nat)
    (si bi : Nat) (hsi : si < nRd) (hbi : bi < nRd) (base : Nat)
    (v : BitVec 64) (g' : ByteMemory)
    (hlb : th.regs.regs.lookup s!"%rd{bi}" = some (.scalar (BitVec.ofNat 64 base)))
    (hls : th.regs.regs.lookup s!"%rd{si}" = some (.scalar v))
    (hbase : base < 2 ^ 64) (halign : base % 8 = 0)
    (hstore : cta.globalMem.storeBits base 8 v = some g')
    (hlog : SafePTXLog outBase len allowedLanes laneOf cta.epochLog)
    (hcx : ∃ cx < len, ¬ allowedLanes cx ∧ base = outBase + cx * 8) :
    execNonBarrierInstr stmts cta th (.stGlobal .u64 (.regOffset s!"%rd{bi}" 0) (.reg s!"%rd{si}")) =
      .ok (thMem th, g', cta.sharedMem,
        { tid := th.tid, space := .global, addr := base, width := 8, isWrite := true,
          isAtomic := false } :: cta.epochLog) := by
  rcases hcx with ⟨cx, hcxLen, hnot, haddrEq⟩
  have hreadB := readScalarChecked_rd hrt bi hbi _ hlb
  have htoNat : (BitVec.ofNat 64 base).toNat = base := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbase]
  have hnn : ¬ (Int.ofNat base + 0 < 0) := by simp [Int.add_zero]
  have haddr : (Int.ofNat base + 0).toNat = base := by simp [Int.add_zero]
  have hnoRace : findDataRace? cta.epochLog th.tid .global base 8 true = none := by
    rw [haddrEq]; exact findDataRace_none_write outBase len allowedLanes laneOf cta.epochLog th.tid cx hlog hcxLen hnot
  have haligned : (base % 8 == 0) = true := by simp [halign]
  ptx_exec_simp [hreadB, htoNat, hnn, ite_false, haddr, evalOp_reg_rd cta th hrt si hsi v hls,
    mask_u64_id, haligned, hnoRace, hstore]

theorem exec_bra_pred (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (pi : Nat) (hpi : pi < nP)
    (cond : Bool) (lbl : String) (target : Nat)
    (hlp : th.regs.regs.lookup s!"%p{pi}" = some (.pred cond))
    (hlbl : findLabelPC? stmts lbl = some target) :
    execPredicatedInstr stmts cta th (some { predReg := s!"%p{pi}" }) (.bra lbl) =
      .ok (if cond then { th with pc := target } else { th with pc := th.pc + 1 },
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  simp only [execPredicatedInstr, evalPredGuard, readPredChecked_p hrt pi hpi cond hlp,
    ptxOk_bind, Bool.false_eq_true, ite_false]
  cases cond
  · rfl
  · simp only [ite_true, execNonBarrierInstr, hlbl]

theorem exec_mad_lo_imm2 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (va cb cc : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th
        (.mad .lo .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 cb) (.immU64 cc)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va * cb + cc)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_imm cta th cb _,
    evalOp_imm cta th cc _, mask_u64_id, setScalar_rd_simp th hrt di hdi (va * cb + cc)]

theorem exec_selp_imm_rd (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di fi pi : Nat)
    (hdi : di < nRd) (hfi : fi < nRd) (hpi : pi < nP) (vt vf : BitVec 64) (cond : Bool)
    (hlf : th.regs.regs.lookup s!"%rd{fi}" = some (.scalar vf))
    (hlp : th.regs.regs.lookup s!"%p{pi}" = some (.pred cond)) :
    execNonBarrierInstr stmts cta th
        (.selp .u64 s!"%rd{di}" (.immU64 vt) (.reg s!"%rd{fi}") s!"%p{pi}") =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (if cond then vt else vf)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [readPredChecked_p hrt pi hpi cond hlp, evalOp_imm cta th vt _,
    evalOp_reg_rd cta th hrt fi hfi vf hlf, mask_u64_id,
    setScalar_rd_simp th hrt di hdi (if cond then vt else vf)]

theorem exec_bitAnd_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (va c : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.bitAnd .b64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 c)) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va &&& c)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, evalOp_imm cta th c _,
    mask_b64_id, setScalar_rd_simp th hrt di hdi (va &&& c)]

theorem exec_bitOr_pred (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai bi : Nat)
    (hdi : di < nP) (hai : ai < nP) (hbi : bi < nP) (pa pb : Bool)
    (hla : th.regs.regs.lookup s!"%p{ai}" = some (.pred pa))
    (hlb : th.regs.regs.lookup s!"%p{bi}" = some (.pred pb)) :
    execNonBarrierInstr stmts cta th (.bitOr .pred s!"%p{di}" (.reg s!"%p{ai}") (.reg s!"%p{bi}")) =
      .ok (thStep th (th.regs.setPredRaw s!"%p{di}" (pa || pb)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hp : (PTXType.pred == .pred) = true := rfl
  simp only [execNonBarrierInstr, hp, ite_true, evalPredOperand,
    readPredChecked_p hrt ai hai pa hla, readPredChecked_p hrt bi hbi pb hlb,
    ptxOk_bind, setPred_p_simp th hrt di hdi (pa || pb), thStep]

theorem exec_shl_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai k : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hk : k < 64) (va : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.shl .b64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 (BitVec.ofNat 64 k))) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va <<< k)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hk32 : k < 4294967296 := by omega
  have hk64 : k < 2 ^ 64 := by omega
  have hfit : (BitVec.ofNat 64 k >>> 32) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.shiftRight_eq_div_pow]
    change k / 4294967296 = 0; omega
  have hne : ((BitVec.ofNat 64 k >>> 32) != 0#64) = false := by rw [hfit]; rfl
  have hm : BitVec.ofNat 64 k &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 k := mask32_id _ hfit
  have htn : (BitVec.ofNat 64 k).toNat = k := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hsh : evalShiftAmount cta th (.immU64 (BitVec.ofNat 64 k)) = .ok k := by
    simp only [evalShiftAmount, evalOp_imm cta th _ _, ptxOk_bind, hne, Bool.false_eq_true, ite_false, hm, htn]
  have hlt : ¬ k ≥ 64 := by omega
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, hsh, hlt, ite_false,
    setScalar_rd_simp th hrt di hdi (va <<< k)]

theorem exec_shr_u64_imm (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai k : Nat)
    (hdi : di < nRd) (hai : ai < nRd) (hk : k < 64) (va : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.shr .u64 s!"%rd{di}" (.reg s!"%rd{ai}") (.immU64 (BitVec.ofNat 64 k))) =
      .ok (thStep th (th.regs.setScalarRaw s!"%rd{di}" (va >>> k)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hk32 : k < 4294967296 := by omega
  have hk64 : k < 2 ^ 64 := by omega
  have hfit : (BitVec.ofNat 64 k >>> 32) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.shiftRight_eq_div_pow]
    change k / 4294967296 = 0; omega
  have hne : ((BitVec.ofNat 64 k >>> 32) != 0#64) = false := by rw [hfit]; rfl
  have hm : BitVec.ofNat 64 k &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 k := mask32_id _ hfit
  have htn : (BitVec.ofNat 64 k).toNat = k := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  have hsh : evalShiftAmount cta th (.immU64 (BitVec.ofNat 64 k)) = .ok k := by
    simp only [evalShiftAmount, evalOp_imm cta th _ _, ptxOk_bind, hne, Bool.false_eq_true, ite_false, hm, htn]
  have hlt : ¬ k ≥ 64 := by omega
  ptx_exec_simp [evalOp_reg_rd cta th hrt ai hai va hla, hsh, hlt, ite_false,
    setScalar_rd_simp th hrt di hdi (va >>> k)]

theorem exec_clz_b64 (stmts : List PTXStmt) (cta : PTXCTAState) (th : PTXThreadState)
    {nP nR nRd : Nat} (hrt : RegTyped th.regs nP nR nRd) (di ai : Nat)
    (hdi : di < nR) (hai : ai < nRd) (va : BitVec 64)
    (hla : th.regs.regs.lookup s!"%rd{ai}" = some (.scalar va)) :
    execNonBarrierInstr stmts cta th (.clz .b64 s!"%r{di}" (.reg s!"%rd{ai}")) =
      .ok (thStep th (th.regs.setScalarRaw s!"%r{di}" (BitVec.clz va)),
        cta.globalMem, cta.sharedMem, cta.epochLog) := by
  have hle64 : (BitVec.clz va).toNat ≤ 64 := BitVec.clz_le
  have hfit : (BitVec.clz va >>> 32) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change (BitVec.clz va).toNat / 4294967296 = 0; omega
  have hm : BitVec.clz va &&& 0xFFFF_FFFF#64 = BitVec.clz va := mask32_id _ hfit
  have hok : ((PTXType.b64 != .b32 && PTXType.b64 != .u32 && PTXType.b64 != .b64 && PTXType.b64 != .u64)) = false := rfl
  have h32 : (PTXType.b64 == .b32 || PTXType.b64 == .u32) = false := rfl
  simp only [execNonBarrierInstr, hok, Bool.false_eq_true, ite_false, ptxBitWidth_b64,
    evalOp_reg_rd cta th hrt ai hai va hla, ptxOk_bind, h32, hm,
    setScalar_r_simp th hrt di hdi (BitVec.clz va) hfit, thStep]

end ExecLemmas

end LeanNative.Proofs.PTXSIMT
