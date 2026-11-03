import LeanNative.Proofs.PTXGrid

namespace LeanNative.Proofs.PTXSIMT

open LeanNative.Backend.PTXAst

/-! ## 7. Output buffer, 1D lanes, and the standard kernel preamble

    `packGlobalBuffers` lays input word buffers end to end and appends a zero output
    region. `stdKernelParams` / `stdKernelRegs` are exactly the declarations
    `PTXLower.kernelOf` emits, and `gidLane` is the register state a 1D lane has after
    the 13-instruction `stdGidSetup` prefix when its global id is in range. -/

theorem zeros_size (n : Nat) : (ByteMemory.zeros n).bytes.size = n := by
  simp [ByteMemory.zeros]

theorem packGlobalBuffers_out_size (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) :
    (packGlobalBuffers nIn len inWords).bytes.size = (nIn + 1) * len * 8 :=
  packGlobalBuffers_size nIn len inWords hlen

private theorem loadBits_append_right (mPre mSuf : ByteMemory) (off : Nat)
    (h : off + 8 ≤ mSuf.bytes.size) :
    ({ bytes := mPre.bytes ++ mSuf.bytes } : ByteMemory).loadBits (mPre.bytes.size + off) 8 =
      mSuf.loadBits off 8 := by
  let tot : ByteMemory := { bytes := mPre.bytes ++ mSuf.bytes }
  have hsz : mPre.bytes.size + off + 8 ≤ tot.bytes.size := by
    simp [tot, Array.size_append]; omega
  unfold ByteMemory.loadBits
  rw [ite_eq_left_iff.mpr fun hc => absurd hsz hc,
      ite_eq_left_iff.mpr fun hc => absurd h hc]
  apply readLE_cong_shift tot mSuf (mPre.bytes.size + off) off 8
  intro i hi
  have hge : mPre.bytes.size ≤ mPre.bytes.size + off + i := by omega
  have hidx : (mPre.bytes.size + off + i) - mPre.bytes.size = off + i := by omega
  simp only [tot, Array.getElem?_append_right hge, hidx]

private theorem reconLE_zero (k : Nat) : reconLE 0#64 k = 0#64 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [reconLE, ih]

theorem zeros_loadBits (n addr : Nat) (h : addr + 8 ≤ n) :
    (ByteMemory.zeros n).loadBits addr 8 = some 0#64 := by
  unfold ByteMemory.zeros ByteMemory.loadBits
  simp only [Array.size_replicate]
  rw [ite_eq_left_iff.mpr fun hc => absurd h hc]
  have hbytes : ∀ b < 8,
      (Array.replicate n (0 : UInt8))[addr + b]? = some (0 : UInt8) := by
    intro b hb
    rw [Array.getElem?_replicate, ite_eq_left_iff.mpr fun hc => absurd (by omega) hc]
  rw [readLE_from_bytes { bytes := Array.replicate n 0 } addr 0#64 8
    (fun b hb => by
      have hsh : ((0#64 : BitVec 64) >>> (b * 8)).toNat % 256 = 0 := by simp
      rw [hsh]; exact hbytes b hb), reconLE_zero]

/-- A lane's output slot starts zero. -/
theorem packGlobalBuffers_load_out_init (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) (i : Nat) (hi : i < len) :
    (packGlobalBuffers nIn len inWords).loadBits (nIn * len * 8 + i * 8) 8 = some 0#64 := by
  unfold packGlobalBuffers
  rw [concatByteMems_append]
  let pre := concatByteMems ((List.range nIn).map fun j => ByteMemory.ofU64Words (inWords j))
  have hpreSz : pre.bytes.size = nIn * len * 8 := by
    have h1 := concatByteMems_size_uniform ((List.range nIn).map fun j => ByteMemory.ofU64Words (inWords j))
      (len * 8) fun m hm => by
        rcases List.mem_map.mp hm with ⟨k, hk, rfl⟩
        rw [ofU64Words_size, hlen k (List.mem_range.mp hk)]
    simpa [pre, Nat.mul_assoc] using h1
  have hmid : i * 8 + 8 ≤ (ByteMemory.zeros (len * 8)).bytes.size := by simp [zeros_size]; omega
  have hpre : concatByteMems [ByteMemory.zeros (len * 8)] = ByteMemory.zeros (len * 8) := by
    simp [concatByteMems]
  rw [← hpreSz, hpre, loadBits_append_right pre (ByteMemory.zeros (len * 8)) (i * 8) hmid]
  exact zeros_loadBits (len * 8) (i * 8) (by omega)

/-- Storing a lane's output word touches only that lane's slot. -/
theorem storeBits_out_lane (nIn len : Nat) (inWords : Nat → List (BitVec 64))
    (hlen : ∀ j < nIn, (inWords j).length = len) (i : Nat) (hi : i < len) (v : BitVec 64) :
    ∃ g',
      (packGlobalBuffers nIn len inWords).storeBits (nIn * len * 8 + i * 8) 8 v = some g' ∧
      g'.bytes.size = (nIn + 1) * len * 8 ∧
      g'.loadBits (nIn * len * 8 + i * 8) 8 = some v ∧
      (∀ i' < len, i' ≠ i → g'.loadBits (nIn * len * 8 + i' * 8) 8 =
        (packGlobalBuffers nIn len inWords).loadBits (nIn * len * 8 + i' * 8) 8) ∧
      (∀ j < nIn, ∀ k < len, g'.loadBits (j * len * 8 + k * 8) 8 =
        (packGlobalBuffers nIn len inWords).loadBits (j * len * 8 + k * 8) 8) := by
  have hsz := packGlobalBuffers_size nIn len inWords hlen
  have hbound : nIn * len * 8 + i * 8 + 8 ≤ (packGlobalBuffers nIn len inWords).bytes.size := by
    rw [hsz]
    have hi8 : i * 8 + 8 ≤ len * 8 := by
      have : i + 1 ≤ len := by omega
      have h := Nat.mul_le_mul_right 8 this
      simpa [Nat.right_distrib, Nat.one_mul] using h
    calc nIn * len * 8 + i * 8 + 8
        = nIn * len * 8 + (i * 8 + 8) := by omega
      _ ≤ nIn * len * 8 + len * 8 := Nat.add_le_add_left hi8 _
      _ = (nIn + 1) * len * 8 := by simp [Nat.add_mul, Nat.one_mul]
  rcases storeBits_eq_some_and_size (packGlobalBuffers nIn len inWords) (nIn * len * 8 + i * 8) v hbound with
    ⟨g', hst, hsz', hread, hdisj⟩
  refine ⟨g', hst, by rw [hsz', hsz], hread, ?_, ?_⟩
  · intro i' hi' hne
    apply hdisj
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro j hj k hk
    apply hdisj
    apply Or.inl
    have hk8 : k * 8 + 8 ≤ len * 8 := by
      have : k + 1 ≤ len := by omega
      have h := Nat.mul_le_mul_right 8 this
      simpa [Nat.right_distrib, Nat.one_mul] using h
    have hjl : (j + 1) * len ≤ nIn * len := Nat.mul_le_mul_right len (by omega)
    have hjl8 : (j + 1) * len * 8 ≤ nIn * len * 8 :=
      Nat.mul_le_mul_right 8 hjl
    have hjl8' : j * len * 8 + len * 8 ≤ nIn * len * 8 := by
      simpa [Nat.add_mul, Nat.one_mul, Nat.right_distrib] using hjl8
    omega

def stdKernelParams (nIn : Nat) : List PTXParamDecl :=
  { ty := .u64, name := "param_out" } ::
    (List.range nIn).map (fun i => { ty := .u64, name := s!"param_in{i}" }) ++
    [{ ty := .u64, name := "param_n" }]

def stdKernelRegs (nP nR nRd : Nat) : List PTXRegDecl :=
  [ { ty := .pred, prefixName := "%p", count := nP }
  , { ty := .u32, prefixName := "%r", count := nR }
  , { ty := .u64, prefixName := "%rd", count := nRd } ]

/-- The register file every lowered kernel starts with is well typed. -/
theorem initRegs_typed (nP nR nRd : Nat) (hp : 0 < nP) (hr : 0 < nR) (hrd : 0 < nRd) :
    RegTyped (PTXRegFile.ofRegDecls (stdKernelRegs nP nR nRd)) nP nR nRd :=
  ofRegDecls_regTyped nP nR nRd hp hr hrd

def laneOf1D (blockSize : Nat) (ctaId tid : Dim3) : Nat :=
  ctaId.x * blockSize + tid.x

/-- One thread of a 1D CTA, at its initial program counter. -/
def mkLane (rf : PTXRegFile) (localBytes tx : Nat) : PTXThreadState :=
  { tid := { x := tx, y := 0, z := 0 }
    pc := 0
    regs := rf
    localMem := ByteMemory.zeros localBytes
    halted := false }

theorem initCTA_threads_1d (k : PTXKernel) (gridDim : Dim3) (blockSize : Nat)
    (ctaId : Dim3) (gMem : ByteMemory) (pMem : ParamMemory) :
    (initCTAState k gridDim { x := blockSize, y := 1, z := 1 } ctaId gMem pMem).threads =
      (List.range blockSize).map (fun tx =>
        mkLane (PTXRegFile.ofRegDecls k.regDecls) k.localBytes tx) := by
  unfold initCTAState
  simp only [dim3_coords_1d, List.map_map]
  apply List.map_congr_left
  intro tx _
  rfl

/-- State of a lane after the 13-instruction `stdGidSetup`, when `gid < len`. -/
def gidLane (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile) (localBytes tx : Nat)
    (gid : Nat) (nIn len : Nat) : PTXThreadState :=
  let base := rfSet (rfSet (rfSet (rfSet (rfSet (rfSet (rfSet rf
    "%r0" (BitVec.ofNat 64 ctaId.x))
    "%r1" (BitVec.ofNat 64 blockSize))
    "%r2" (BitVec.ofNat 64 tx))
    "%rd0" (BitVec.ofNat 64 (ctaId.x * blockSize)))
    "%rd1" (BitVec.ofNat 64 tx))
    "%rd2" (BitVec.ofNat 64 gid))
    "%rd3" (BitVec.ofNat 64 len)
  let withPred := base.setPredRaw "%p0" false
  let out := rfSet (rfSet (rfSet withPred
    "%rd4" (BitVec.ofNat 64 (nIn * len * 8)))
    "%rd5" (BitVec.ofNat 64 (gid * 8)))
    "%rd6" (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))
  { tid := { x := tx, y := 0, z := 0 }
    pc := 13
    regs := out
    localMem := ByteMemory.zeros localBytes
    halted := false }

theorem gidLane_typed {nP nR nRd : Nat} (blockSize : Nat) (ctaId : Dim3)
    {rf : PTXRegFile} (hrt : RegTyped rf nP nR nRd) (localBytes tx gid nIn len : Nat) :
    RegTyped (gidLane blockSize ctaId rf localBytes tx gid nIn len).regs nP nR nRd :=
  hrt

theorem laneOf1D_lt (ctaX blockSize tx : Nat)
    (hcta : ctaX < 2 ^ 32) (hblk : blockSize < 2 ^ 32) (htx : tx < 2 ^ 32) :
    ctaX * blockSize + tx < 2 ^ 64 := by
  have h1 : ctaX * blockSize ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (Nat.le_sub_one_of_lt hcta) (Nat.le_sub_one_of_lt hblk)
  have h2 : (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) < 2 ^ 64 := by decide
  omega

theorem gidLane_pc (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx gid nIn len : Nat) :
    (gidLane blockSize ctaId rf localBytes tx gid nIn len).pc = 13 := by
  unfold gidLane; rfl

theorem gidLane_lookup_gid (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx gid nIn len : Nat) :
    (gidLane blockSize ctaId rf localBytes tx gid nIn len).regs.regs.lookup "%rd2" =
      some (.scalar (BitVec.ofNat 64 gid)) := by
  unfold gidLane
  dsimp only [PTXRegFile.setPredRaw]
  rw [lookup_rfSet_ne _ "%rd6" "%rd2" _ (by decide),
      lookup_rfSet_ne _ "%rd5" "%rd2" _ (by decide),
      lookup_rfSet_ne _ "%rd4" "%rd2" _ (by decide),
      setAssoc_lookup_ne _ "%p0" "%rd2" _ (by decide),
      lookup_rfSet_ne _ "%rd3" "%rd2" _ (by decide),
      lookup_rfSet_self]

theorem gidLane_lookup_off (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx gid nIn len : Nat) :
    (gidLane blockSize ctaId rf localBytes tx gid nIn len).regs.regs.lookup "%rd5" =
      some (.scalar (BitVec.ofNat 64 (gid * 8))) := by
  unfold gidLane
  rw [lookup_rfSet_ne _ "%rd6" "%rd5" _ (by decide)]
  exact lookup_rfSet_self _ "%rd5" _

theorem gidLane_lookup_out (blockSize : Nat) (ctaId : Dim3) (rf : PTXRegFile)
    (localBytes tx gid nIn len : Nat) :
    (gidLane blockSize ctaId rf localBytes tx gid nIn len).regs.regs.lookup "%rd6" =
      some (.scalar (BitVec.ofNat 64 (nIn * len * 8 + gid * 8))) := by
  unfold gidLane
  exact lookup_rfSet_self _ "%rd6" _

/-- The output address of an in-range lane is an aligned slot inside the buffer. -/
theorem outAddr_in_range (nIn len gid : Nat) (hgid : gid < len) :
    nIn * len * 8 + gid * 8 + 8 ≤ (nIn + 1) * len * 8 ∧
    (nIn * len * 8 + gid * 8) % 8 = 0 := by
  refine ⟨?_, by omega⟩
  have hgid8 : gid * 8 + 8 ≤ len * 8 := by
    have : gid + 1 ≤ len := by omega
    have h := Nat.mul_le_mul_right 8 this
    simpa [Nat.right_distrib, Nat.one_mul] using h
  calc nIn * len * 8 + gid * 8 + 8
      = nIn * len * 8 + (gid * 8 + 8) := by omega
    _ ≤ nIn * len * 8 + len * 8 := Nat.add_le_add_left hgid8 _
    _ = (nIn + 1) * len * 8 := by simp [Nat.add_mul, Nat.one_mul]

end LeanNative.Proofs.PTXSIMT
