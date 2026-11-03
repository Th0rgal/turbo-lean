import LeanNative.Proofs.MetalSIMT2

namespace LeanNative.Proofs.MetalSIMT

open LeanNative.Backend.MetalAst

theorem loadTypedElem_ulong (structs : List MSLStructDecl) (mem : ByteMemory) (elemIdx : Nat) :
    loadTypedElem structs mem .ulong (elemIdx * 8) =
      (mem.readU64Word? elemIdx).map (fun v => (v, [])) := by
  unfold loadTypedElem ByteMemory.readU64Word?
  have hfn : structFieldNames structs .ulong = [] := rfl
  have hbw : MSLType.ulong.byteWidth = 8 := rfl
  simp only [hfn, hbw, maskForType]
  cases mem.loadBits (elemIdx * 8) 8 <;> rfl

theorem storeTypedElem_ulong (structs : List MSLStructDecl) (mem : ByteMemory) (byteAddr : Nat)
    (val : BitVec 64) (fields : List (String × BitVec 64)) :
    storeTypedElem structs mem .ulong byteAddr val fields =
      mem.storeBits byteAddr 8 val := by
  unfold storeTypedElem
  have hfn : structFieldNames structs .ulong = [] := rfl
  simp only [hfn]
  rfl

theorem lookup_setIndexedMem_same (bufs : List (Nat × ByteMemory)) (idx : Nat) (mem : ByteMemory) :
    (setIndexedMem bufs idx mem).lookup idx = some mem := by
  induction bufs with
  | nil => simp [setIndexedMem]
  | cons hd tl ih =>
    rcases hd with ⟨idx', mem'⟩
    unfold setIndexedMem
    by_cases h : idx' = idx
    · subst h; simp
    · have hbf : (idx' == idx) = false := beq_false_of_ne h
      have hbf2 : (idx == idx') = false := beq_false_of_ne (Ne.symm h)
      simp [hbf, List.lookup, hbf2, ih]

theorem lookup_setIndexedMem_ne (bufs : List (Nat × ByteMemory)) (idx idx' : Nat)
    (mem : ByteMemory) (hne : idx' ≠ idx) :
    (setIndexedMem bufs idx mem).lookup idx' = bufs.lookup idx' := by
  induction bufs with
  | nil =>
    have hbf : (idx' == idx) = false := beq_false_of_ne hne
    simp [setIndexedMem, List.lookup, hbf]
  | cons hd tl ih =>
    rcases hd with ⟨k, m⟩
    unfold setIndexedMem
    by_cases hk : k = idx
    · subst hk
      have hbf : (idx' == k) = false := beq_false_of_ne hne
      simp [List.lookup, hbf]
    · have hbf : (k == idx) = false := beq_false_of_ne hk
      simp only [hbf, Bool.false_eq_true, ite_false, List.lookup]
      cases idx' == k
      · exact ih
      · rfl

theorem ev_clz_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a : MSLExpr) (bv : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := bv, fields := [], locals := ls, log := log })
    (hta : inferExprType g ls a = .ulong) :
    evalExprWithCall callEval fuel g tid ls log (.clz a) =
      .ok { value := BitVec.ofNat 64 bv.clz.toNat, fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  dsimp only [bindEval]
  rw [hta]
  have htr : bv.setWidth 64 = bv := BitVec.setWidth_eq bv
  dsimp only [MSLType.isFloat, MSLType.bitWidth, maskForType, BitVec.truncate]
  rw [htr]
  rfl

theorem ev_var_gid_uint (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (cx : Nat) (hcx : cx < 2 ^ 32)
    (hl : ls.lookup? "gid" = some (BitVec.ofNat 64 cx))
    (ht : ls.lookupType? "gid" = some .uint) :
    evalExprWithCall callEval fuel g tid ls log (.var "gid") =
      .ok { value := BitVec.ofNat 64 cx, fields := [], locals := ls, log := log } ∧
    evalExprWithCall callEval fuel g tid ls log (.cast .ulong (.var "gid")) =
      .ok { value := BitVec.ofNat 64 cx, fields := [], locals := ls, log := log } := by
  have hvar : evalExprWithCall callEval fuel g tid ls log (.var "gid") =
      .ok { value := BitVec.ofNat 64 cx, fields := [], locals := ls, log := log } := by
    rw [evalExprWithCall]
    simp only [hl, ht]
    rfl
  refine ⟨hvar, ?_⟩
  rw [evalExprWithCall, hvar]
  simp only [bindEval, inferExprType, ht]
  have hcast : evalMSLCast .ulong .uint (BitVec.ofNat 64 cx) = .ok (BitVec.ofNat 64 cx) := by
    have hmask : BitVec.ofNat 64 cx &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 cx := by
      apply BitVec.eq_of_toNat_eq
      change (cx % 2 ^ 64) &&& 4294967295 = cx % 2 ^ 64
      have hmod64 : cx % 2 ^ 64 = cx := Nat.mod_eq_of_lt (by omega)
      rw [hmod64]
      have h4 : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
      rw [h4, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt hcx
    show MSLOutcome.ok (BitVec.ofNat 64 cx &&& 0xFFFF_FFFF#64) = MSLOutcome.ok (BitVec.ofNat 64 cx)
    rw [hmask]
  rw [hcast]

theorem ev_var_const_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (name : String) (bufIdx : Nat) (bv : BitVec 64)
    (hln : ls.lookup? name = none) (hlt : ls.lookupType? name = none)
    (hb : g.bindings.lookup name = some (.constantScalar bufIdx .ulong))
    (hc : g.constantBuffers.lookup bufIdx = some (ByteMemory.ofU64Words [bv])) :
    evalExprWithCall callEval fuel g tid ls log (.var name) =
      .ok { value := bv, fields := [], locals := ls, log := log } ∧
    inferExprType g ls (.var name) = .ulong := by
  have hload : loadTypedElem g.structs (ByteMemory.ofU64Words [bv]) .ulong 0 = some (bv, []) := by
    have h0 : (0 : Nat) = 0 * 8 := rfl
    rw [h0, loadTypedElem_ulong]
    have hw := ofU64Words_readU64Word [bv] 0 (by simp)
    simp only [hw, List.getElem_cons_zero, Option.map]
  refine ⟨?_, ?_⟩
  · rw [evalExprWithCall]
    simp only [hln, hb, hc, hload]
  · simp only [inferExprType, hlt, hb]

theorem ev_index_dev_read (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (target : String) (idxExpr : MSLExpr)
    (k nIn lo hi elemIdx : Nat) (words : List (BitVec 64))
    (hidx : evalExprWithCall callEval fuel g tid ls log idxExpr =
      .ok { value := BitVec.ofNat 64 elemIdx, fields := [], locals := ls, log := log })
    (helemLt : elemIdx < words.length)
    (hwLen : words.length < 2 ^ 64)
    (harr : ls.lookupArray? target = none)
    (hbind : g.bindings.lookup target = some (.deviceBuf k true .ulong))
    (hdev : g.deviceBuffers.lookup k = some (ByteMemory.ofU64Words words))
    (hk : k < nIn)
    (hlog : ∀ a ∈ log, SimtLogInv nIn lo hi a) :
    ∃ log',
      evalExprWithCall callEval fuel g tid ls log (.index target idxExpr) =
        .ok { value := words[elemIdx], fields := [], locals := ls, log := log' } ∧
      (∀ a ∈ log', SimtLogInv nIn lo hi a) ∧
      log'.isEmpty = false := by
  have htoNat : (BitVec.ofNat 64 elemIdx).toNat = elemIdx := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans helemLt hwLen)]
  have ⟨hrec, hlog'⟩ := recordEpochAccess_read_ok log tid k nIn lo hi (elemIdx * 8) hk hlog
  have hload : loadTypedElem g.structs (ByteMemory.ofU64Words words) .ulong (elemIdx * 8) =
      some (words[elemIdx], []) := by
    rw [loadTypedElem_ulong, ofU64Words_readU64Word words elemIdx helemLt]
    rfl
  refine ⟨{ tid, target := .deviceBuf k, addr := elemIdx * 8, width := 8, isWrite := false, isAtomic := false } :: log, ?_, hlog', rfl⟩
  rw [evalExprWithCall, hidx]
  simp only [bindEval, harr, htoNat, readBoundElement, hbind, hdev, aggregateByteWidth]
  have hbw : MSLType.ulong.byteWidth = 8 := rfl
  simp only [hbw, hrec, hload]

theorem exec_indexAssign_dev_write (g : MSLGroupState) (th : MSLThreadState)
    (rest : List MSLStmt) (idxExpr rhs : MSLExpr)
    (nIn lo elemIdx len : Nat) (val : BitVec 64)
    (log1 : List MSLAccess) (outMem : ByteMemory)
    (hidx : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog idxExpr =
      .ok { value := BitVec.ofNat 64 elemIdx, fields := [], locals := th.locals, log := g.epochLog })
    (hrhs : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs =
      .ok { value := val, fields := [], locals := th.locals, log := log1 })
    (helemLt : elemIdx < len) (hlen64 : len * 8 ≤ 2 ^ 64)
    (harr : th.locals.lookupArray? "out" = none)
    (hbind : g.bindings.lookup "out" = some (.deviceBuf nIn false .ulong))
    (hdev : g.deviceBuffers.lookup nIn = some outMem)
    (hsize : outMem.bytes.size = len * 8)
    (hle : lo ≤ elemIdx)
    (hlog1 : ∀ a ∈ log1, SimtLogInv nIn lo elemIdx a) :
    ∃ outMem' log2,
      execNonBarrierStmt g th (.indexAssign "out" idxExpr rhs) rest =
        .ok ({ th with stmts := rest },
             { g with epochLog := log2, deviceBuffers := setIndexedMem g.deviceBuffers nIn outMem' }) ∧
      outMem'.bytes.size = len * 8 ∧
      outMem'.readU64Word? elemIdx = some val ∧
      (∀ j, j ≠ elemIdx → outMem'.readU64Word? j = outMem.readU64Word? j) ∧
      (∀ a ∈ log2, SimtLogInv nIn lo (elemIdx + 1) a) ∧
      log2.isEmpty = false := by
  have htoNat : (BitVec.ofNat 64 elemIdx).toNat = elemIdx := by
    have hlt : elemIdx < 2 ^ 64 := by omega
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have ⟨hrec, hlog2⟩ := recordEpochAccess_write_ok log1 th.tid nIn lo elemIdx hle hlog1
  have hstore : outMem.storeBits (elemIdx * 8) 8 val =
      some { bytes := ByteMemory.writeLEAux outMem.bytes (elemIdx * 8) val 8 } := by
    exact storeBits_8_eq outMem elemIdx val (by rw [hsize]; omega)
  let outMem' : ByteMemory := { bytes := ByteMemory.writeLEAux outMem.bytes (elemIdx * 8) val 8 }
  let entry : MSLAccess :=
    { tid := th.tid, target := .deviceBuf nIn, addr := elemIdx * 8, width := 8, isWrite := true, isAtomic := false }
  refine ⟨outMem', entry :: log1, ?_, ?_, ?_, ?_, hlog2, rfl⟩
  · unfold execNonBarrierStmt
    dsimp only [execStmtWithCall]
    rw [hidx]
    have hag : aggregateByteWidth g.structs .ulong = 8 := rfl
    simp only [hrhs, htoNat, harr, execIndexWrite, hbind, hag, hrec,
      writeDeviceBuffer, hdev, storeTypedElem_ulong, hstore]
    rfl
  · rw [writeLEAux_size, hsize]
  · exact storeBits_8_read_same outMem outMem' elemIdx val hstore
  · intro j hj
    exact storeBits_8_read_ne outMem outMem' elemIdx j val hj hstore


theorem ev_logOr_ulong (callEval : Nat → MSLGroupState → Dim3 → MSLLocals →
      List MSLAccess → String → MSLExprList → MSLOutcome MSLEval)
    (fuel : Nat) (g : MSLGroupState) (tid : Dim3) (ls : MSLLocals)
    (log : List MSLAccess) (a b : MSLExpr) (va vb : BitVec 64)
    (ha : evalExprWithCall callEval fuel g tid ls log a =
      .ok { value := va, fields := [], locals := ls, log := log })
    (hb : evalExprWithCall callEval fuel g tid ls log b =
      .ok { value := vb, fields := [], locals := ls, log := log }) :
    evalExprWithCall callEval fuel g tid ls log (.logOr a b) =
      .ok { value := if (va != 0#64) || (vb != 0#64) then 1#64 else 0#64,
            fields := [], locals := ls, log := log } := by
  rw [evalExprWithCall, ha]
  dsimp only [bindEval]
  cases hva : (va != 0#64)
  · simp only [Bool.false_eq_true, ite_false, Bool.false_or, hb]
    cases hvb : (vb == 0#64)
    · have hne : (vb != 0#64) = true := by simpa [bne_iff_ne, beq_iff_eq] using hvb
      simp [hne]
    · have hne : (vb != 0#64) = false := by
        cases h : (vb != 0#64)
        · rfl
        · rw [bne_iff_ne] at h; rw [beq_iff_eq] at hvb; exact absurd hvb h
      simp [hne]
  · simp

theorem exec_varDecl_ulong (g : MSLGroupState) (th : MSLThreadState)
    (rest : List MSLStmt) (name : String) (rhs : MSLExpr)
    (val : BitVec 64) (log1 : List MSLAccess)
    (hrhsNotConst : ∀ src, rhs = .var src → ∀ idx ty, g.bindings.lookup src ≠ some (.constantScalar idx ty))
    (hrhs : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog rhs =
      .ok { value := val, fields := [], locals := th.locals, log := log1 }) :
    execNonBarrierStmt g th (.varDecl .ulong name rhs) rest =
      .ok ({ th with locals := th.locals.setTyped name .ulong val, stmts := rest },
           { g with epochLog := log1 }) := by
  unfold execNonBarrierStmt
  dsimp only [execStmtWithCall]
  have hbc : ∀ idx ty, (match g.bindings.lookup name with
      | none => match rhs with | .var src => g.bindings.lookup src | _ => none
      | some _ => none) ≠ some (.constantScalar idx ty) := by
    intro idx ty
    cases g.bindings.lookup name with
    | none =>
      cases rhs with
      | var src => exact hrhsNotConst src rfl idx ty
      | _ => intro h; cases h
    | some _ => intro h; cases h
  split
  · rename_i idx ty hcs
    exact absurd hcs (hbc idx ty)
  · simp only [hrhs, bindValue, maskForType, List.foldl]

theorem exec_ifElse_step (g : MSLGroupState) (th : MSLThreadState)
    (rest : List MSLStmt) (cond : MSLExpr) (thenBr elseBr : MSLBlock)
    (cval : BitVec 64) (log1 : List MSLAccess)
    (hc : evalExprWithCall kernelCallEval (effectiveCalleeFuel g) g th.tid th.locals g.epochLog cond =
      .ok { value := cval, fields := [], locals := th.locals, log := log1 }) :
    execNonBarrierStmt g th (.ifElse cond thenBr elseBr) rest =
      .ok ({ th with stmts := (if cval != 0#64 then thenBr.toList else elseBr.toList) ++ rest },
           { g with epochLog := log1 }) := by
  unfold execNonBarrierStmt
  dsimp only [execStmtWithCall]
  rw [hc]

theorem exec_returnStmt_step (g : MSLGroupState) (th : MSLThreadState) (rest : List MSLStmt) :
    execNonBarrierStmt g th .returnStmt rest =
      .ok ({ th with stmts := [], halted := true }, g) := rfl


def stdKernelParams (nIn : Nat) : List MSLParamDecl :=
  (List.range nIn).map (fun i =>
    { ty := .pointer .device true .ulong, name := s!"in{i}", attr := some (.buffer i) }) ++
  [ { ty := .pointer .device false .ulong, name := "out", attr := some (.buffer nIn) }
  , { ty := .ref .constant .ulong, name := "n", attr := some (.buffer (nIn + 1)) }
  , { ty := .uint, name := "gid", attr := some .threadPositionInGrid } ]

def stdBindings (nIn : Nat) : List (String × MSLBufferBinding) :=
  (List.range nIn).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong)) ++
    [("out", .deviceBuf nIn false .ulong), ("n", .constantScalar (nIn + 1) .ulong)]

theorem in_ne_lit (i : Nat) :
    s!"in{i}" ≠ "out" ∧ s!"in{i}" ≠ "n" ∧ s!"in{i}" ≠ "gid" ∧ s!"in{i}" ≠ "gid64" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    intro h
    have hc := congrArg (fun s => s.toList.head?) h
    simp [toString] at hc
  }

theorem in_ne_var (i id : Nat) : s!"in{i}" ≠ s!"v{id}" := by
  intro h
  have hc := congrArg (fun s => s.toList.head?) h
  simp [toString] at hc

theorem var_ne_special (id : Nat) :
    s!"v{id}" ≠ "out" ∧ s!"v{id}" ≠ "n" ∧ s!"v{id}" ≠ "gid" ∧ s!"v{id}" ≠ "gid64" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> {
    intro h
    have hc := congrArg (fun s => s.toList.head?) h
    simp [toString] at hc
  }

theorem buildKernelBindings_std (k : MSLKernelDecl) (nIn : Nat)
    (hparams : k.params = stdKernelParams nIn) (hshared : k.sharedDecls = []) :
    buildKernelBindings k = stdBindings nIn := by
  let bindFn := fun (p : MSLParamDecl) =>
    match p.attr, p.ty with
    | some (.buffer idx), .pointer .device isConst elemTy =>
      some (p.name, MSLBufferBinding.deviceBuf idx isConst elemTy)
    | some (.buffer idx), .pointer .constant _ elemTy =>
      some (p.name, MSLBufferBinding.constantBuf idx elemTy)
    | some (.buffer idx), .ref .constant elemTy =>
      some (p.name, MSLBufferBinding.constantScalar idx elemTy)
    | some (.buffer _), .pointer .threadgroup _ elemTy =>
      some (p.name, MSLBufferBinding.threadgroupArr p.name elemTy)
    | _, _ => none
  change k.params.filterMap bindFn ++ k.sharedDecls.map (fun s => (s.name, .threadgroupArr s.name s.elemTy)) = stdBindings nIn
  rw [hparams, hshared, List.map_nil, List.append_nil]
  unfold stdKernelParams stdBindings
  rw [List.filterMap_append]
  have h1 : ∀ xs : List Nat,
      (xs.map (fun i =>
        ({ ty := .pointer .device true .ulong, name := s!"in{i}", attr := some (.buffer i) } : MSLParamDecl))).filterMap bindFn =
      xs.map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.filterMap_cons, bindFn]
      rw [ih]
  rw [h1 (List.range nIn)]
  rfl

private theorem lookup_mapIn_lt :
    ∀ (nIn j : Nat), j < nIn →
      ((List.range nIn).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong))).lookup s!"in{j}" =
        some (.deviceBuf j true .ulong)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, hj => by
    rw [List.range_succ, List.map_append, List.lookup_append]
    by_cases hjn : j = n
    · subst hjn
      have hnone : ((List.range j).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong))).lookup s!"in{j}" = none := by
        rw [List.lookup_eq_none_iff]
        intro ⟨k, v⟩ hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨i, hi, heq⟩
        cases heq
        rw [List.mem_range] at hi
        simp only [bne_iff_ne, ne_eq]
        intro heqS
        have hij := prefix_nat_inj "in" j i (by simpa [toString] using heqS)
        omega
      rw [hnone]
      simp
    · rw [lookup_mapIn_lt n j (by omega)]
      rfl

private theorem lookup_mapIn_other (nIn : Nat) (s : String)
    (hne : ∀ i < nIn, s ≠ s!"in{i}") :
    ((List.range nIn).map (fun i => (s!"in{i}", MSLBufferBinding.deviceBuf i true .ulong))).lookup s = none := by
  rw [List.lookup_eq_none_iff]
  intro ⟨k, v⟩ hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, heq⟩
  cases heq
  rw [List.mem_range] at hi
  simpa [bne_iff_ne] using hne i hi

theorem stdBindings_lookup_in (nIn j : Nat) (hj : j < nIn) :
    (stdBindings nIn).lookup s!"in{j}" = some (.deviceBuf j true .ulong) := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_lt nIn j hj]
  rfl

theorem stdBindings_lookup_out (nIn : Nat) :
    (stdBindings nIn).lookup "out" = some (.deviceBuf nIn false .ulong) := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_other nIn "out" (fun i _ => (in_ne_lit i).1.symm)]
  rfl

theorem stdBindings_lookup_n (nIn : Nat) :
    (stdBindings nIn).lookup "n" = some (.constantScalar (nIn + 1) .ulong) := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_other nIn "n" (fun i _ => (in_ne_lit i).2.1.symm)]
  rfl

theorem stdBindings_lookup_none (nIn : Nat) (s : String)
    (hin : ∀ i < nIn, s ≠ s!"in{i}") (hout : s ≠ "out") (hn : s ≠ "n") :
    (stdBindings nIn).lookup s = none := by
  unfold stdBindings
  rw [List.lookup_append, lookup_mapIn_other nIn s hin]
  simp [List.lookup, beq_false_of_ne hout, beq_false_of_ne hn]

theorem initThreadLocals_std (k : MSLKernelDecl) (g0 : MSLGroupState) (tid : Dim3) (nIn : Nat)
    (hparams : k.params = stdKernelParams nIn) :
    initThreadLocals k g0 tid =
      initBuiltinLocal MSLLocals.empty "gid" .uint
        (g0.groupId.x * g0.groupDim.x + tid.x,
         g0.groupId.y * g0.groupDim.y + tid.y,
         g0.groupId.z * g0.groupDim.z + tid.z) := by
  let stepFn := fun (acc : MSLLocals) (p : MSLParamDecl) =>
    match p.attr with
    | some (.buffer _) | none => acc
    | some attr => initBuiltinLocal acc p.name p.ty (evalBuiltinCoords g0 tid attr)
  change k.params.foldl stepFn MSLLocals.empty = _
  rw [hparams]
  unfold stdKernelParams
  rw [List.foldl_append]
  have hfoldIn : ∀ xs : List Nat,
      (xs.map (fun i =>
        ({ ty := .pointer .device true .ulong, name := s!"in{i}", attr := some (.buffer i) } : MSLParamDecl))).foldl
        stepFn MSLLocals.empty = MSLLocals.empty := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.foldl_cons, stepFn]; exact ih
  rw [hfoldIn (List.range nIn)]
  rfl

theorem initBuiltinLocal_gid_props (cx : Nat) (hcx : cx < 2 ^ 32) :
    let ls := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
    ls.lookup? "gid" = some (BitVec.ofNat 64 cx) ∧
    ls.lookupType? "gid" = some .uint ∧
    ls.arrays = [] ∧
    (∀ s, s ≠ "gid" → ls.lookup? s = none ∧ ls.lookupType? s = none) := by
  have hmask : maskForType .uint (BitVec.ofNat 64 cx) = BitVec.ofNat 64 cx := by
    change BitVec.ofNat 64 cx &&& 0xFFFF_FFFF#64 = BitVec.ofNat 64 cx
    apply BitVec.eq_of_toNat_eq
    change (cx % 2 ^ 64) &&& 4294967295 = cx % 2 ^ 64
    have h64 : cx < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h64]
    have h4 : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide
    rw [h4, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hcx]
  dsimp only [initBuiltinLocal, MSLLocals.setField, MSLLocals.setTyped, MSLLocals.empty,
    MSLLocals.setAssoc, MSLLocals.setTypeAssoc]
  rw [hmask]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro s hs
  simp [MSLLocals.lookup?, MSLLocals.lookupType?, List.lookup, beq_false_of_ne hs]

theorem dim3_coords_1d (m : Nat) :
    ({ x := m, y := 1, z := 1 } : Dim3).coords =
      (List.range m).map (fun x => ({ x := x, y := 0, z := 0 } : Dim3)) := by
  unfold Dim3.coords
  simp [List.range_succ]


def LaneInnerSpec (nIn len stepsInner : Nat)
    (inWords : Nat → List (BitVec 64)) (specWord : Nat → BitVec 64)
    (inner : List MSLStmt) : Prop :=
  ∀ (g : MSLGroupState) (done todo : List MSLThreadState)
    (cx tx lo f : Nat) (outMem : ByteMemory),
    cx < len → cx < 2 ^ 32 → len * 8 ≤ 2 ^ 64 → lo ≤ cx → stepsInner + 1 ≤ f →
    g.structs = [] → g.funcs = [] → g.bindings = stdBindings nIn →
    g.constantBuffers = [(nIn + 1, ByteMemory.ofU64Words [BitVec.ofNat 64 len])] →
    (∀ j < nIn, g.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j)) ∧
      (inWords j).length = len) →
    g.deviceBuffers.lookup nIn = some outMem →
    outMem.bytes.size = len * 8 →
    (∀ a ∈ g.epochLog, SimtLogInv nIn lo cx a) →
    (∀ d ∈ done, d.halted = true) →
    g.threads = done ++ (
      { tid := { x := tx, y := 0, z := 0 }
        locals := initBuiltinLocal MSLLocals.empty "gid" .uint (cx, 0, 0)
        stmts := inner ++ [.returnStmt]
        halted := false } :: todo) →
    ∃ (f' : Nat) (thH : MSLThreadState) (g' : MSLGroupState) (outMem' : ByteMemory),
      runGroupWithDeviceLog f g [] = runGroupWithDeviceLog f' g' [] ∧
      f - (stepsInner + 1) ≤ f' ∧
      thH.halted = true ∧
      g'.threads = done ++ (thH :: todo) ∧
      g'.structs = [] ∧ g'.funcs = [] ∧ g'.bindings = stdBindings nIn ∧
      g'.constantBuffers = g.constantBuffers ∧
      (∀ j < nIn, g'.deviceBuffers.lookup j = some (ByteMemory.ofU64Words (inWords j))) ∧
      g'.deviceBuffers.lookup nIn = some outMem' ∧
      outMem'.bytes.size = len * 8 ∧
      outMem'.readU64Word? cx = some (specWord cx) ∧
      (∀ i, i ≠ cx → outMem'.readU64Word? i = outMem.readU64Word? i) ∧
      (∀ a ∈ g'.epochLog, SimtLogInv nIn lo (cx + 1) a)


end LeanNative.Proofs.MetalSIMT
