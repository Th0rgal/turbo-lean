import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.Backend.LLVM

open LeanSys.Par
open LeanNative.IR

def sanitizeSymbol (s : String) : String :=
  let res := String.ofList (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')
  if res.isEmpty then "ln_anon" else res

def targetDataLayout (t : TargetArch) : String :=
  t.dataLayout

def cpuTriple : TargetArch → String
  | .nvptx64 | .hybridCpuGpu => "x86_64-unknown-linux-gnu"
  | t => t.llvmTriple

def tupleFieldLLVMType (f : LNIRType) : String := if f.is256Bit then "i256" else "i64"

def slotLLVMType : LNIRType → String
  | .objPtr | .taggedPtr | .sarray _ | .rawPtr _ | .storageMap => "ptr"
  | .u256 | .i256 => "i256"
  | .tuple fs => "{ " ++ String.intercalate ", " (fs.map tupleFieldLLVMType) ++ " }"
  | _ => "i64"

def sigLLVMType : LNIRType → String | .unit => "void" | ty => slotLLVMType ty

partial def collectScalarVars : ScalarExpr → List (VarId × LNIRType)
  | .constU64 _ | .constBool _ => []
  | .var id => [(id, .i64)]
  | .binOp _ l r => collectScalarVars l ++ collectScalarVars r
  | .unaryOp _ a => collectScalarVars a
  | .select c t e | .fma c t e => collectScalarVars c ++ collectScalarVars t ++ collectScalarVars e

def collectExprVars : LNIRExpr → List (VarId × LNIRType)
  | .scalar e => collectScalarVars e
  | .constU256 _ => []
  | .mulDivDown a b d | .mulDivUp a b d => [(a, .u256), (b, .u256), (d, .u256)]
  | .storageLoad m s => [(m, .storageMap), (s, .u256)]
  | .storageStore m s v => [(m, .storageMap), (s, .u256), (v, .u256)]
  | .mkTuple fs => fs.map (·, .i64)
  | .projTuple tv _ => [(tv, .i64)]
  | .allocCtor _ ofs sfs => ofs.map (·, .objPtr) ++ sfs.map (·, .i64)
  | .ctorGetObj v _ | .ctorGetScalar v _ _ | .isExclusive v | .sarrayLen v | .unboxScalar v _ => [(v, .objPtr)]
  | .sarrayDataPtr av et | .sarrayEnsureExclusive av et => [(av, .sarray et)]
  | .sarrayGet av iv et => [(av, .sarray et), (iv, .i64)]
  | .sarraySet av iv vv et => [(av, .sarray et), (iv, .i64), (vv, et)]
  | .rawLoad pv iv et => [(pv, .rawPtr et), (iv, .i64)]
  | .boxScalar vv ty => [(vv, ty)]
  | .call _ args _ _ => args.map (·, .i64)

/-- Collect all `(VarId, LNIRType)` bindings and references in an `LNIRCode` block so we can pre-allocate
    type-consistent `alloca` slots in the function `entry` block. -/
partial def collectCodeVars (code : LNIRCode) : List (VarId × LNIRType) :=
  match code with
  | .letBind dst ty rhs k => (dst, ty) :: collectExprVars rhs ++ collectCodeVars k
  | .rawStore pv iv vv et k => (pv, .rawPtr et) :: (iv, .i64) :: (vv, et) :: collectCodeVars k
  | .incRef ov _ k => (ov, .objPtr) :: collectCodeVars k
  | .decRef ov _ k => (ov, .objPtr) :: collectCodeVars k
  | .ite cv t e => (cv, .i64) :: collectCodeVars t ++ collectCodeVars e
  | .seqFor idxVar loVar hiVar accVar accInit accTy stepBody k =>
    (idxVar, .i64) :: (loVar, .i64) :: (hiVar, .i64) :: (accVar, accTy) :: (accInit, accTy) ::
      (collectCodeVars stepBody ++ collectCodeVars k)
  | .parFor outVar lenVar inputs elemTy kernel k =>
    let kVars := match kernel with
      | .customScalar iv ins body => (iv, .i64) :: ins.map (fun v => (v, elemTy)) ++ collectScalarVars body
      | _ => []
    (outVar, .sarray elemTy) :: (lenVar, .i64) ::
      (inputs.map (fun v => (v, .sarray elemTy))) ++ kVars ++ collectCodeVars k
  | .ret v => [(v, .i64)]
  | .unreachable => []

/-- Binding sites only (`letBind`, loop index/accumulator, `parFor` output and kernel index):
    their declared types are authoritative over the fallbacks guessed from references. -/
partial def collectCodeDecls : LNIRCode → List (VarId × LNIRType)
  | .letBind dst ty _ k => (dst, ty) :: collectCodeDecls k
  | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k => collectCodeDecls k
  | .ite _ t e => collectCodeDecls t ++ collectCodeDecls e
  | .seqFor idxVar _ _ accVar _ accTy stepBody k =>
    (idxVar, .i64) :: (accVar, accTy) :: (collectCodeDecls stepBody ++ collectCodeDecls k)
  | .parFor outVar _ _ elemTy kernel k =>
    let kDecls := match kernel with
      | .customScalar iv _ _ => [(iv, .i64)]
      | _ => []
    (outVar, .sarray elemTy) :: kDecls ++ collectCodeDecls k
  | .ret _ | .unreachable => []

/-- Deduplicate variable declarations, keeping the first recorded type for each `VarId`. -/
def dedupVars (vars : List (VarId × LNIRType)) : List (VarId × LNIRType) :=
  vars.foldl (fun acc (vid, ty) =>
    if acc.any (fun (id, _) => id == vid) then acc
    else acc ++ [(vid, ty)]
  ) []

/-- Slot types for a declaration: parameters, then binding sites, then reference fallbacks. -/
def declSlotVars (d : LNIRDecl) : List (VarId × LNIRType) :=
  dedupVars (d.params.map (fun p => (p.id, p.ty)) ++ collectCodeDecls d.body ++ collectCodeVars d.body)

/-- Syntactic check whether an `LNIRExpr` performs heap allocation, boxing, or CoW exclusivity checks. -/
def exprHasHeapOps : LNIRExpr → Bool
  | .allocCtor _ _ _ | .sarrayEnsureExclusive _ _ | .boxScalar _ _ => true
  | _ => false

/-- Syntactic check whether an `LNIRCode` block performs RC or heap operations. -/
partial def codeHasHeapOps : LNIRCode → Bool
  | .incRef _ _ _ | .decRef _ _ _ => true
  | .letBind _ _ rhs k => exprHasHeapOps rhs || codeHasHeapOps k
  | .rawStore _ _ _ _ k => codeHasHeapOps k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasHeapOps t || codeHasHeapOps e
  | .parFor _ _ _ _ _ k => true || codeHasHeapOps k
  | .ret _ | .unreachable => false

/-- Syntactic check whether an `LNIRCode` block contains a data-parallel `parFor` loop. -/
partial def codeHasParFor : LNIRCode → Bool
  | .parFor _ _ _ _ _ _ => true
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k => codeHasParFor k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasParFor t || codeHasParFor e
  | .ret _ | .unreachable => false

/-- Syntactic check whether an `LNIRCode` block contains EVM 256-bit `.storageLoad` or `.storageStore`. -/
partial def codeHasStorageOps : LNIRCode → Bool
  | .letBind _ _ (.storageLoad _ _) _ | .letBind _ _ (.storageStore _ _ _) _ => true
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k | .parFor _ _ _ _ _ k => codeHasStorageOps k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasStorageOps t || codeHasStorageOps e
  | .ret _ | .unreachable => false

/-- Syntactic check whether a `ScalarExpr` exercises AArch64 crypto/carryless intrinsics (`clmul64`, `clmul64Hi`, `eor3`). -/
partial def scalarHasCryptoOps : ScalarExpr → Bool
  | .constU64 _ | .constBool _ | .var _ => false
  | .binOp .clmul64 _ _ | .binOp .clmul64Hi _ _ | .binOp .eor3 _ _ => true
  | .binOp _ l r => scalarHasCryptoOps l || scalarHasCryptoOps r
  | .unaryOp _ a => scalarHasCryptoOps a
  | .select c t e | .fma c t e => scalarHasCryptoOps c || scalarHasCryptoOps t || scalarHasCryptoOps e

def exprHasCryptoOps : LNIRExpr → Bool
  | .scalar e => scalarHasCryptoOps e
  | _ => false

/-- Syntactic check whether an `LNIRCode` block exercises AArch64 crypto/carryless intrinsics (`pmull64`, `eor3u`). -/
partial def codeHasCryptoOps : LNIRCode → Bool
  | .letBind _ _ rhs k => exprHasCryptoOps rhs || codeHasCryptoOps k
  | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k => codeHasCryptoOps k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => codeHasCryptoOps t || codeHasCryptoOps e
  | .parFor _ _ _ _ (.customScalar _ _ body) k => scalarHasCryptoOps body || codeHasCryptoOps k
  | .parFor _ _ _ _ _ k => codeHasCryptoOps k
  | .ret _ | .unreachable => false

/-- Select and certify the optimal `RcMode` for `d` from its LNIR AST via `RcMode.verifySafe`:
    - Pure scalar / slice declarations (`hasHeap = 0`) -> `.freestanding` (`0`)
    - Single-threaded heap declarations (`hasHeap = 1, isMt = 0`) -> `.singleThreaded` (`1`)
    - Multi-threaded / `parFor` declarations (`hasHeap = 1, isMt = 1`) -> `.atomic` (`2`) -/
def selectDeclRcMode (d : LNIRDecl) : RcMode :=
  let hasHeap : UInt8 := if codeHasHeapOps d.body then 1 else 0
  let isMt : UInt8 := if codeHasParFor d.body then 1 else 0
  let cand : RcMode :=
    if hasHeap == 0 then .freestanding
    else if isMt == 0 then .singleThreaded
    else .atomic
  if RcMode.verifySafe cand.toCode hasHeap isMt == 1 then cand else .atomic

/-- Intrinsic hardware capabilities that `d` can exercise on an unconstrained AArch64 target.
    Note: `LNIRDecl` operates on integer/pointer/256-bit types, so `fp16`, `dotprod`, `i8mm`, `bf16`,
    and `sme2` are `false`; `sve2`/`sveBitperm` are exercised iff `d` contains a `parFor` loop;
    `sha3` is exercised iff `d` contains `clmul64`/`clmul64Hi`/`eor3`; `lse` iff `selectDeclRcMode d == .atomic`. -/
def declIntrinsicRequires (d : LNIRDecl) : IsaLevel :=
  let usesAtomic := selectDeclRcMode d == .atomic
  let usesSimd := codeHasParFor d.body
  let usesCrypto := codeHasCryptoOps d.body
  let base : ArmBase :=
    if usesSimd then .v9_0
    else if usesCrypto then .v8_5
    else if usesAtomic then .v8_2
    else .v8_0
  { base       := base
    neon       := true
    fp16       := false
    dotprod    := false
    i8mm       := false
    bf16       := false
    sve2       := usesSimd
    sveBitperm := usesSimd
    sme2       := false
    lse        := usesAtomic
    sha3       := usesCrypto }

/-- Exact `IsaLevel` capability profile exercised by `emitDeclLLVM` when lowering `d` under `targetIsa`.
    Each capability flag directly mirrors the exact guard in `emitDeclLLVM` / `emitScalarExpr` / `emitMetadataFooter`
    (never attributing `fp16`/`dotprod`/`i8mm`/`bf16` to integer `parFor` loops, and gating `pmull64`/`eor3u` on `targetIsa.sha3`). -/
def codegenRequires (d : LNIRDecl) (targetIsa : IsaLevel := IsaLevel.arm64Baseline) : IsaLevel :=
  let usesAtomic := (selectDeclRcMode d == .atomic) && targetIsa.lse
  let usesSimd := codeHasParFor d.body
  let usesCrypto := codeHasCryptoOps d.body && targetIsa.sha3
  let emitSve2 := usesSimd && targetIsa.sve2
  let emitBitperm := emitSve2 && targetIsa.sveBitperm
  let reqRank :=
    if emitSve2 then 4
    else if usesCrypto then 2
    else if usesAtomic then 1
    else 0
  { base       := ArmBase.ofRank (Nat.min reqRank targetIsa.base.rank)
    neon       := targetIsa.neon
    fp16       := false
    dotprod    := false
    i8mm       := false
    bf16       := false
    sve2       := emitSve2
    sveBitperm := emitBitperm
    sme2       := false
    lse        := usesAtomic
    sha3       := usesCrypto }

theorem codegen_rank_le_target (s c a : Bool) (b : ArmBase) :
    decide ((ArmBase.ofRank (Nat.min (if s then 4 else if c then 2 else if a then 1 else 0) b.rank)).rank ≤ b.rank) = true := by
  cases s <;> cases c <;> cases a <;> cases b <;> rfl

/-- Formal capability admission theorem: for every `LNIRDecl` `d` and target `IsaLevel` `targetIsa`,
    the capabilities exercised by `emitDeclLLVM` (`codegenRequires d targetIsa`) satisfy `≤ targetIsa`. -/
theorem codegen_requires_le_target (d : LNIRDecl) (targetIsa : IsaLevel) :
    (codegenRequires d targetIsa).le targetIsa = true := by
  unfold codegenRequires IsaLevel.le
  dsimp only
  rw [codegen_rank_le_target]
  simp only [IsaLevel.bool_imp_self, IsaLevel.bool_and_imp_right, Bool.not_false, Bool.true_or, Bool.and_self]

/-- Mutable state for emitting LLVM instructions within a single declaration. -/
structure EmitState where
  optimized : Bool
  target    : TargetArch := .x86_64
  isa       : IsaLevel := IsaLevel.arm64Baseline
  rcMode    : RcMode := .atomic
  localScalarSigs : List (String × Nat) := []
  varTypes  : List (VarId × LNIRType)
  nextTmp   : Nat := 0
  scalarBindings : List (VarId × String) := []
  lines     : List String := []
  deriving Inhabited

abbrev EmitM := StateM EmitState

def freshTmp (prefixStr : String := "t") : EmitM String := do
  let st ← get
  let idx := st.nextTmp
  set { st with nextTmp := idx + 1 }
  return s!"%{prefixStr}_{idx}"

def freshLabel (prefixStr : String := "bb") : EmitM String := do
  let st ← get
  let idx := st.nextTmp
  set { st with nextTmp := idx + 1 }
  return s!"{prefixStr}_{idx}"

def emitLine (line : String) : EmitM Unit := do
  modify fun st => { st with lines := st.lines ++ [line] }

def getVarSlotType (vid : VarId) : EmitM LNIRType := do
  return ((← get).varTypes.lookup vid).getD .i64

private def loadVarSlotRaw (vid : VarId) (pfx : String) : EmitM (String × String) := do
  let llvmTy := slotLLVMType (← getVarSlotType vid)
  let raw ← freshTmp pfx
  emitLine s!"  {raw} = load {llvmTy}, ptr %slot_v{vid}, align 8"
  return (llvmTy, raw)

/-- Load a `VarId` as an `i64` SSA value (converting `ptr` via `ptrtoint` or `i256` via `trunc` if necessary). -/
def loadVarAsI64 (vid : VarId) : EmitM String := do
  let (llvmTy, raw) ← loadVarSlotRaw vid "ld"
  if llvmTy == "i64" then return raw
  else if llvmTy == "i256" then
    let c ← freshTmp "tr64"
    emitLine s!"  {c} = trunc i256 {raw} to i64"
    return c
  else if llvmTy == "ptr" then
    let c ← freshTmp "p2i"
    emitLine s!"  {c} = ptrtoint ptr {raw} to i64"
    return c
  else
    let c ← freshTmp "extr"
    emitLine s!"  {c} = extractvalue {llvmTy} {raw}, 0"
    return c

/-- Load a `VarId` as an `i256` SSA value (converting `i64` via `zext` if necessary). -/
def loadVarAsI256 (vid : VarId) : EmitM String := do
  let (llvmTy, raw) ← loadVarSlotRaw vid "ld256"
  if llvmTy == "i256" then return raw
  let v64 ← if llvmTy == "i64" then pure raw else loadVarAsI64 vid
  let c ← freshTmp "zext256"
  emitLine s!"  {c} = zext i64 {v64} to i256"
  return c

/-- Load a `VarId` as an LLVM `ptr` SSA value (converting `i64` via `inttoptr` if necessary). -/
def loadVarAsPtr (vid : VarId) : EmitM String := do
  let (llvmTy, raw) ← loadVarSlotRaw vid "ldp"
  if llvmTy == "ptr" then return raw
  else if llvmTy == "i64" || llvmTy == "i256" then
    let v64 ← if llvmTy == "i64" then pure raw else do
      let tr ← freshTmp "tr64"
      emitLine s!"  {tr} = trunc i256 {raw} to i64"
      pure tr
    let c ← freshTmp "i2p"
    emitLine s!"  {c} = inttoptr i64 {v64} to ptr"
    return c
  else return "null"

/-- Store an `i64` SSA value into `%slot_v{dst}`, coercing to the slot's type if needed. -/
def storeI64ToVar (dst : VarId) (valI64 : String) : EmitM Unit := do
  let llvmTy := slotLLVMType (← getVarSlotType dst)
  if llvmTy == "i64" then
    emitLine s!"  store i64 {valI64}, ptr %slot_v{dst}, align 8"
  else if llvmTy == "i256" then
    let z ← freshTmp "zext256"
    emitLine s!"  {z} = zext i64 {valI64} to i256"
    emitLine s!"  store i256 {z}, ptr %slot_v{dst}, align 8"
  else if llvmTy == "ptr" then
    let p ← freshTmp "i2p"
    emitLine s!"  {p} = inttoptr i64 {valI64} to ptr"
    emitLine s!"  store ptr {p}, ptr %slot_v{dst}, align 8"
  else
    emitLine s!"  ; tuple slot %slot_v{dst} skipped scalar store"

/-- Store an `i256` SSA value into `%slot_v{dst}`, coercing to the slot's type if needed. -/
def storeI256ToVar (dst : VarId) (valI256 : String) : EmitM Unit := do
  let llvmTy := slotLLVMType (← getVarSlotType dst)
  if llvmTy == "i256" then
    emitLine s!"  store i256 {valI256}, ptr %slot_v{dst}, align 8"
  else if llvmTy == "i64" || llvmTy == "ptr" then
    let tr ← freshTmp "tr64"
    emitLine s!"  {tr} = trunc i256 {valI256} to i64"
    storeI64ToVar dst tr
  else
    emitLine s!"  ; tuple slot %slot_v{dst} skipped i256 store"

/-- Store a `ptr` SSA value into `%slot_v{dst}`, coercing to the slot's type if needed. -/
def storePtrToVar (dst : VarId) (valPtr : String) : EmitM Unit := do
  let llvmTy := slotLLVMType (← getVarSlotType dst)
  if llvmTy == "ptr" then
    emitLine s!"  store ptr {valPtr}, ptr %slot_v{dst}, align 8"
  else if llvmTy == "i64" || llvmTy == "i256" then
    let i ← freshTmp "p2i"
    emitLine s!"  {i} = ptrtoint ptr {valPtr} to i64"
    storeI64ToVar dst i
  else
    emitLine s!"  ; tuple slot %slot_v{dst} skipped ptr store"

/-- Copy value from `%slot_v{src}` to `%slot_v{dst}`. -/
def copyVarSlot (dst src : VarId) : EmitM Unit := do
  let llvmDst := slotLLVMType (← getVarSlotType dst)
  if llvmDst == "ptr" then storePtrToVar dst (← loadVarAsPtr src)
  else if llvmDst == "i256" then storeI256ToVar dst (← loadVarAsI256 src)
  else if llvmDst == "i64" then storeI64ToVar dst (← loadVarAsI64 src)
  else
    let llvmSrc := slotLLVMType (← getVarSlotType src)
    if llvmSrc == llvmDst then
      let tmp ← freshTmp "tup"
      emitLine s!"  {tmp} = load {llvmDst}, ptr %slot_v{src}, align 8"
      emitLine s!"  store {llvmDst} {tmp}, ptr %slot_v{dst}, align 8"
    else
      storeI64ToVar dst (← loadVarAsI64 src)

/-- Check whether a `ScalarExpr` references any 256-bit variable or 256-bit operator. -/
partial def scalarExprIs256Bit : ScalarExpr → EmitM Bool
  | .constU64 _ | .constBool _ => return false
  | .var id => return (← getVarSlotType id).is256Bit
  | .binOp (.addChecked256) _ _ | .binOp (.subChecked256) _ _ | .binOp (.mulChecked256) _ _ => return true
  | .binOp _ l r => return (← scalarExprIs256Bit l) || (← scalarExprIs256Bit r)
  | .unaryOp .clz256 _ => return true
  | .unaryOp _ a => scalarExprIs256Bit a
  | .select c t e | .fma c t e => return (← scalarExprIs256Bit c) || (← scalarExprIs256Bit t) || (← scalarExprIs256Bit e)

abbrev LNIRScalarExpr := ScalarExpr

private def emitChecked256Op (opName pfx lVal rVal res : String) : EmitM String := do
  let ov ← freshTmp (pfx ++ "_ov")
  let flag ← freshTmp (pfx ++ "_flag")
  let trapLbl ← freshLabel (pfx ++ "_trap")
  let okLbl ← freshLabel (pfx ++ "_ok")
  let useLimbs := (← get).target.isAArch64 && (opName == "uadd" || opName == "usub")
  let callee := if useLimbs then s!"@lean_native_u256_{opName}_limbs" else s!"@llvm.{opName}.with.overflow.i256"
  emitLine s!"  {ov} = call \{ i256, i1 } {callee}(i256 {lVal}, i256 {rVal})"
  emitLine s!"  {flag} = extractvalue \{ i256, i1 } {ov}, 1"
  emitLine s!"  br i1 {flag}, label %{trapLbl}, label %{okLbl}"
  emitLine s!"{trapLbl}:"
  emitLine "  call void @llvm.trap()"
  emitLine "  unreachable"
  emitLine s!"{okLbl}:"
  emitLine s!"  {res} = extractvalue \{ i256, i1 } {ov}, 0"
  return res

partial def emitScalarExprWithWidth (tyStr : String) (shiftMask : String) (e : LNIRScalarExpr) : EmitM String := do
  let is256 := tyStr == "i256"
  let sfx := if is256 then "256" else ""
  let emitSub (x : LNIRScalarExpr) : EmitM String := emitScalarExprWithWidth tyStr shiftMask x
  let emit256 (x : LNIRScalarExpr) : EmitM String := emitScalarExprWithWidth "i256" "255" x
  let emitConst (valStr pfx : String) : EmitM String := do
    if is256 then
      let res ← freshTmp pfx
      emitLine s!"  {res} = add i256 0, {valStr}"
      return res
    else return valStr
  let emitChecked (intr : String) : EmitM (String → String → String → EmitM String) :=
    return fun lVal rVal res =>
      if is256 then emitChecked256Op intr intr lVal rVal res
      else do let v256 ← emit256 e; emitLine s!"  {res} = trunc i256 {v256} to i64"; return res
  match e with
  | .constU64 v => emitConst s!"{v}" "c256"
  | .constBool b => emitConst (if b then "1" else "0") "b256"
  | .var id =>
    match (← get).scalarBindings.lookup id with
    | none => if is256 then loadVarAsI256 id else loadVarAsI64 id
    | some v =>
      if !is256 then return v
      else
        let wide ← freshTmp "bound256"
        emitLine s!"  {wide} = zext i64 {v} to i256"
        return wide
  | .binOp .bitXor (.binOp .bitXor a b) c =>
    let st ← get
    if !is256 && st.optimized && st.target.isAArch64 && st.isa.sha3 then
      let aVal ← emitSub a
      let bVal ← emitSub b
      let cVal ← emitSub c
      let va ← freshTmp "eor3_va"; let vb ← freshTmp "eor3_vb"; let vc ← freshTmp "eor3_vc"
      let vp ← freshTmp "eor3_vp"; let res ← freshTmp "eor3_res"
      emitLine s!"  {va} = insertelement <2 x i64> zeroinitializer, i64 {aVal}, i64 0\n  {vb} = insertelement <2 x i64> zeroinitializer, i64 {bVal}, i64 0\n  {vc} = insertelement <2 x i64> zeroinitializer, i64 {cVal}, i64 0\n  {vp} = call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64(<2 x i64> {va}, <2 x i64> {vb}, <2 x i64> {vc})\n  {res} = extractelement <2 x i64> {vp}, i64 0"
      return res
    else
      let lVal ← emitSub (.binOp .bitXor a b)
      let rVal ← emitSub c
      let res ← freshTmp ("alu" ++ sfx)
      emitLine s!"  {res} = xor {tyStr} {lVal}, {rVal}"
      return res
  | .binOp op lhs rhs =>
    if is256 && (op == .clmul64 || op == .clmul64Hi || op == .gf2Affine || op == .eor3) then
      let v64 ← emitScalarExprWithWidth "i64" "63" e
      let res ← freshTmp "alu256_gf"
      emitLine s!"  {res} = zext i64 {v64} to i256"
      return res
    else
    let lVal ← emitSub lhs
    let rVal ← emitSub rhs
    let res ← freshTmp ("alu" ++ sfx)
    let emitDivRem (llvmOp pfx : String) : EmitM String := do
      match is256, rhs with
      | false, .constU64 d =>
        if d != 0 then emitLine s!"  {res} = {llvmOp} i64 {lVal}, {rVal}"
        else emitLine s!"  {res} = add i64 0, 0"
        return res
      | _, _ =>
        let safeR ← freshTmp (pfx ++ sfx ++ "_rhs")
        let isZero ← freshTmp (pfx ++ sfx ++ "_z")
        emitLine s!"  {isZero} = icmp eq {tyStr} {rVal}, 0"
        emitLine s!"  {safeR} = select i1 {isZero}, {tyStr} 1, {tyStr} {rVal}"
        emitLine s!"  {res} = {llvmOp} {tyStr} {lVal}, {safeR}"
        return res
    let emitShift (llvmOp pfx : String) : EmitM String := do
      match is256, rhs with
      | false, .constU64 k =>
        emitLine s!"  {res} = {llvmOp} i64 {lVal}, {k &&& 63}"
        return res
      | _, _ =>
        let masked ← freshTmp (pfx ++ sfx ++ "_amt")
        emitLine s!"  {masked} = and {tyStr} {rVal}, {shiftMask}"
        emitLine s!"  {res} = {llvmOp} {tyStr} {lVal}, {masked}"
        return res
    let emitCmp (pred sfxCmp : String) : EmitM String := do
      let cmp ← freshTmp ("cmp" ++ sfx ++ "_" ++ sfxCmp)
      emitLine s!"  {cmp} = icmp {pred} {tyStr} {lVal}, {rVal}"
      emitLine s!"  {res} = zext i1 {cmp} to {tyStr}"
      return res
    match op with
    | .add    => emitLine s!"  {res} = add {tyStr} {lVal}, {rVal}"; return res
    | .sub    => emitLine s!"  {res} = sub {tyStr} {lVal}, {rVal}"; return res
    | .mul    => emitLine s!"  {res} = mul {tyStr} {lVal}, {rVal}"; return res
    | .bitAnd => emitLine s!"  {res} = and {tyStr} {lVal}, {rVal}"; return res
    | .bitOr  => emitLine s!"  {res} = or {tyStr} {lVal}, {rVal}"; return res
    | .bitXor => emitLine s!"  {res} = xor {tyStr} {lVal}, {rVal}"; return res
    | .div    => emitDivRem "udiv" "div"
    | .mod    => emitDivRem "urem" "mod"
    | .shl    => emitShift "shl" "sh"
    | .shr    => emitShift "lshr" "sh"
    | .sar    => emitShift "ashr" "sar"
    | .eq     => emitCmp "eq" "eq"
    | .lt     => emitCmp "ult" "lt"
    | .le     => emitCmp "ule" "le"
    | .addChecked256 => (← emitChecked "uadd") lVal rVal res
    | .subChecked256 => (← emitChecked "usub") lVal rVal res
    | .mulChecked256 => (← emitChecked "umul") lVal rVal res
    | .clmul64 | .clmul64Hi =>
      let st ← get
      let isHi := op == .clmul64Hi
      let lane := if isHi then "1" else "0"
      if st.optimized && (st.target == .x86_64 || st.target == .hybridCpuGpu) then
        let va ← freshTmp "cl_va"; let vb ← freshTmp "cl_vb"; let vp ← freshTmp "cl_vp"
        emitLine s!"  {va} = insertelement <2 x i64> zeroinitializer, i64 {lVal}, i64 0\n  {vb} = insertelement <2 x i64> zeroinitializer, i64 {rVal}, i64 0\n  {vp} = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> {va}, <2 x i64> {vb}, i8 0)\n  {res} = extractelement <2 x i64> {vp}, i64 {lane}"
        return res
      else if st.optimized && st.target.isAArch64 && st.isa.sha3 then
        let vp8 ← freshTmp "cl_vp8"; let vp ← freshTmp "cl_vp"
        emitLine s!"  {vp8} = call <16 x i8> @llvm.aarch64.neon.pmull64(i64 {lVal}, i64 {rVal})\n  {vp} = bitcast <16 x i8> {vp8} to <2 x i64>\n  {res} = extractelement <2 x i64> {vp}, i64 {lane}"
        return res
      else
        let mut acc := "0"
        for i in [(if isHi then 1 else 0):64] do
          let bit ← freshTmp "cl_bit"; let low ← freshTmp "cl_low"; let mask ← freshTmp "cl_mask"
          let shifted ← freshTmp "cl_shift"; let term ← freshTmp "cl_term"; let next ← freshTmp "cl_acc"
          let shInstr := if isHi then s!"lshr i64 {lVal}, {64 - i}" else s!"shl i64 {lVal}, {i}"
          emitLine s!"  {bit} = lshr i64 {rVal}, {i}\n  {low} = and i64 {bit}, 1\n  {mask} = sub i64 0, {low}\n  {shifted} = {shInstr}\n  {term} = and i64 {shifted}, {mask}\n  {next} = xor i64 {acc}, {term}"; acc := next
        return acc
    | .gf2Affine =>
      let mut acc := "0"
      for i in [0:8] do
        let row ← freshTmp "gf_row"; let bits ← freshTmp "gf_bits"; let byte ← freshTmp "gf_byte"
        emitLine s!"  {row} = lshr i64 {rVal}, {i * 8}\n  {bits} = and i64 {row}, {lVal}\n  {byte} = and i64 {bits}, 255"
        let mut parity := byte
        for shift in [4, 2, 1] do
          let hi ← freshTmp "gf_hi"; let folded ← freshTmp "gf_fold"
          emitLine s!"  {hi} = lshr i64 {parity}, {shift}\n  {folded} = xor i64 {parity}, {hi}"; parity := folded
        let bit ← freshTmp "gf_bit"; let placed ← freshTmp "gf_placed"; let next ← freshTmp "gf_acc"
        emitLine s!"  {bit} = and i64 {parity}, 1\n  {placed} = shl i64 {bit}, {i}\n  {next} = or i64 {acc}, {placed}"; acc := next
      return acc
    | .eor3 =>
      let st ← get
      let hi ← freshTmp "eor3_hi"; let lo ← freshTmp "eor3_lo"
      if st.optimized && st.target.isAArch64 && st.isa.sha3 then
        let va ← freshTmp "eor3_va"; let vb ← freshTmp "eor3_vb"; let vc ← freshTmp "eor3_vc"; let vp ← freshTmp "eor3_vp"
        emitLine s!"  {hi} = lshr i64 {rVal}, 32\n  {lo} = and i64 {rVal}, 4294967295\n  {va} = insertelement <2 x i64> zeroinitializer, i64 {lVal}, i64 0\n  {vb} = insertelement <2 x i64> zeroinitializer, i64 {hi}, i64 0\n  {vc} = insertelement <2 x i64> zeroinitializer, i64 {lo}, i64 0\n  {vp} = call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64(<2 x i64> {va}, <2 x i64> {vb}, <2 x i64> {vc})\n  {res} = extractelement <2 x i64> {vp}, i64 0"
        return res
      else
        let hiXor ← freshTmp "eor3_hi_xor"
        emitLine s!"  {hi} = lshr i64 {rVal}, 32\n  {lo} = and i64 {rVal}, 4294967295\n  {hiXor} = xor i64 {lVal}, {hi}\n  {res} = xor i64 {hiXor}, {lo}"
        return res
  | .unaryOp op arg =>
    if !is256 && op == .clz256 then
      let v256 ← emit256 e
      let res ← freshTmp "un"
      emitLine s!"  {res} = trunc i256 {v256} to i64"
      return res
    else
      let aVal ← emitSub arg
      let res ← freshTmp ("un" ++ sfx)
      match op with
      | .not    => emitLine s!"  {res} = xor {tyStr} {aVal}, -1"; return res
      | .neg    => emitLine s!"  {res} = sub {tyStr} 0, {aVal}"; return res
      | .clz256 => emitLine s!"  {res} = call i256 @llvm.ctlz.i256(i256 {aVal}, i1 false)"; return res
  | .select cond thenVal elseVal =>
    let cVal ← emitSub cond
    let tVal ← emitSub thenVal
    let eVal ← emitSub elseVal
    let cBool ← freshTmp ("sel" ++ sfx ++ "_cond")
    let res ← freshTmp ("sel" ++ sfx)
    emitLine s!"  {cBool} = icmp ne {tyStr} {cVal}, 0"
    emitLine s!"  {res} = select i1 {cBool}, {tyStr} {tVal}, {tyStr} {eVal}"
    return res
  | .fma a b c =>
    let aVal ← emitSub a
    let bVal ← emitSub b
    let cVal ← emitSub c
    let mulTmp ← freshTmp ("fma" ++ sfx ++ "_mul")
    let res ← freshTmp ("fma" ++ sfx ++ "_add")
    emitLine s!"  {mulTmp} = mul {tyStr} {aVal}, {bVal}"
    emitLine s!"  {res} = add {tyStr} {mulTmp}, {cVal}"
    return res

/-- Lower a `ScalarExpr` into `i256` SSA instructions, returning the resulting `i256` SSA value string. -/
def emitScalarExpr256 (e : LNIRScalarExpr) (s : EmitState) : String × EmitState :=
  emitScalarExprWithWidth "i256" "255" e s

/-- Lower a `ScalarExpr` into `i64` SSA instructions, returning the resulting `i64` SSA value string. -/
def emitScalarExpr (e : LNIRScalarExpr) (s : EmitState) : String × EmitState :=
  emitScalarExprWithWidth "i64" "63" e s

/-- Emit 512-bit exact `mulDivDown` (`roundUp = false`) or `mulDivUp` (`roundUp = true`) for 256-bit EVM values. -/
def emitMulDiv512 (dst aVar bVar denomVar : VarId) (roundUp : Bool) : EmitM Unit := do
  let aVal ← loadVarAsI256 aVar
  let bVal ← loadVarAsI256 bVar
  let dVal ← loadVarAsI256 denomVar
  let a512 ← freshTmp "zext512_a"
  let b512 ← freshTmp "zext512_b"
  let d512 ← freshTmp "zext512_d"
  let prod512 ← freshTmp "mul512"
  let isZero ← freshTmp "d512_z"
  let safeD512 ← freshTmp "safe_d512"
  for line in [
    s!"  {a512} = zext i256 {aVal} to i512",
    s!"  {b512} = zext i256 {bVal} to i512",
    s!"  {d512} = zext i256 {dVal} to i512",
    s!"  {prod512} = mul nuw i512 {a512}, {b512}",
    s!"  {isZero} = icmp eq i512 {d512}, 0",
    s!"  {safeD512} = select i1 {isZero}, i512 1, i512 {d512}"
  ] do emitLine line
  let num512 ← if roundUp then do
    let dMinus1 ← freshTmp "dm1_512"
    let numTmp ← freshTmp "num512"
    emitLine s!"  {dMinus1} = sub i512 {safeD512}, 1"
    emitLine s!"  {numTmp} = add i512 {prod512}, {dMinus1}"
    pure numTmp
  else pure prod512
  let quot512 ← freshTmp "udiv512"
  let res256 ← freshTmp "trunc256"
  emitLine s!"  {quot512} = udiv i512 {num512}, {safeD512}"
  emitLine s!"  {res256} = trunc i512 {quot512} to i256"
  storeI256ToVar dst res256

/-- Lower an `LNIRExpr` and store its result into `%slot_v{dst}`. -/
def emitLetExpr (dst : VarId) (ty : LNIRType) (expr : LNIRExpr) : EmitM Unit := do
  let st ← get
  let opt := st.optimized
  match expr with
  | .scalar e =>
    let is256 ← scalarExprIs256Bit e
    if ty.is256Bit || is256 then
      let val256 ← emitScalarExpr256 e
      storeI256ToVar dst val256
    else
      let val ← emitScalarExpr e
      storeI64ToVar dst val
  | .constU256 w =>
    let cVal ← freshTmp "c256"
    emitLine s!"  {cVal} = add i256 0, {w.toNat}"
    storeI256ToVar dst cVal
  | .mulDivDown aVar bVar denomVar =>
    emitMulDiv512 dst aVar bVar denomVar false
  | .mulDivUp aVar bVar denomVar =>
    emitMulDiv512 dst aVar bVar denomVar true
  | .storageLoad mapVar slotVar =>
    let mapPtr ← loadVarAsPtr mapVar
    let slotVal ← loadVarAsI256 slotVar
    let loadedVal ← freshTmp "sload_val"
    for line in [
      s!"  store i256 {slotVal}, ptr %evm_scratch_slot, align 8\n  store i256 0, ptr %evm_scratch_val, align 8",
      s!"  call void @lean_native_evm_sload(ptr {mapPtr}, ptr %evm_scratch_slot, ptr %evm_scratch_val)",
      s!"  {loadedVal} = load i256, ptr %evm_scratch_val, align 8"
    ] do emitLine line
    storeI256ToVar dst loadedVal
  | .storageStore mapVar slotVar valVar =>
    let mapPtr ← loadVarAsPtr mapVar
    let slotVal ← loadVarAsI256 slotVar
    let val256 ← loadVarAsI256 valVar
    for line in [
      s!"  store i256 {slotVal}, ptr %evm_scratch_slot, align 8\n  store i256 {val256}, ptr %evm_scratch_val, align 8",
      s!"  call void @lean_native_evm_sstore(ptr {mapPtr}, ptr %evm_scratch_slot, ptr %evm_scratch_val)"
    ] do emitLine line
    storePtrToVar dst mapPtr
  | .mkTuple fields =>
    let dstSlotTy ← getVarSlotType dst
    let llvmTy := slotLLVMType dstSlotTy
    if !opt then
      -- In baseline mode, simulate boxed heap tuple allocation cost
      let f0 ← match fields[0]? with
        | some v => loadVarAsI64 v
        | none => pure "0"
      let boxed ← freshTmp "box_tup"
      emitLine s!"  {boxed} = call ptr @lean_native_box_u64(i64 {f0})"
    if let .tuple fieldTys := dstSlotTy then
      let mut curAgg := "undef"
      for idx in [0 : fields.length] do
        if let some fVar := fields[idx]? then
          let fTy := tupleFieldLLVMType (fieldTys[idx]?.getD .i64)
          let fVal ← if fTy == "i256" then loadVarAsI256 fVar else loadVarAsI64 fVar
          let nextAgg ← freshTmp "tup_ins"
          emitLine s!"  {nextAgg} = insertvalue {llvmTy} {curAgg}, {fTy} {fVal}, {idx}"
          curAgg := nextAgg
      emitLine s!"  store {llvmTy} {curAgg}, ptr %slot_v{dst}, align 8"
    else
      match fields[0]? with
      | some f0 => copyVarSlot dst f0
      | none => storeI64ToVar dst "0"
  | .projTuple tupleVar idx =>
    let tupSlotTy ← getVarSlotType tupleVar
    let llvmTupTy := slotLLVMType tupSlotTy
    if let .tuple fieldTys := tupSlotTy then
      let tupVal ← freshTmp "tup_ld"
      let extr ← freshTmp "tup_proj"
      emitLine s!"  {tupVal} = load {llvmTupTy}, ptr %slot_v{tupleVar}, align 8"
      emitLine s!"  {extr} = extractvalue {llvmTupTy} {tupVal}, {idx}"
      if tupleFieldLLVMType (fieldTys[idx]?.getD .i64) == "i256" then storeI256ToVar dst extr
      else storeI64ToVar dst extr
    else
      let v ← loadVarAsI64 tupleVar
      storeI64ToVar dst v
  | .allocCtor _ objFields scalarFields =>
    let allFields := objFields ++ scalarFields
    match allFields[0]? with
    | some f0 =>
      let v ← loadVarAsI64 f0
      let boxed ← freshTmp "ctor"
      emitLine s!"  {boxed} = call ptr @lean_native_box_u64(i64 {v})"
      storePtrToVar dst boxed
    | none =>
      storePtrToVar dst "null"
  | .ctorGetObj ctorVar _ =>
    let p ← loadVarAsPtr ctorVar
    storePtrToVar dst p
  | .ctorGetScalar ctorVar _ _ =>
    let p ← loadVarAsPtr ctorVar
    let u ← freshTmp "unbox_fld"
    emitLine s!"  {u} = call i64 @lean_native_unbox_u64(ptr {p})"
    storeI64ToVar dst u
  | .isExclusive objVar =>
    let p ← loadVarAsPtr objVar
    let rc ← freshTmp "rc_val"
    let eq1 ← freshTmp "is_excl"
    let eq1_64 ← freshTmp "is_excl64"
    emitLine s!"  {rc} = load i32, ptr {p}, align 4"
    emitLine s!"  {eq1} = icmp eq i32 {rc}, 1"
    emitLine s!"  {eq1_64} = zext i1 {eq1} to i64"
    storeI64ToVar dst eq1_64
  | .sarrayLen arrVar =>
    let arrPtr ← loadVarAsPtr arrVar
    -- Offset 8 bytes (1 x i64) is `size_t m_size` in `lean_native_sarray_u64`
    let szPtr ← freshTmp "sz_ptr"
    let szVal ← freshTmp "sz_val"
    emitLine s!"  {szPtr} = getelementptr inbounds i64, ptr {arrPtr}, i64 1"
    emitLine s!"  {szVal} = load i64, ptr {szPtr}, align 8"
    storeI64ToVar dst szVal
  | .sarrayDataPtr arrVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    -- Offset 24 bytes (3 x i64) is `uint64_t m_data[]` in `lean_native_sarray_u64`
    let dataPtr ← freshTmp "data_ptr"
    emitLine s!"  {dataPtr} = getelementptr inbounds i64, ptr {arrPtr}, i64 3"
    storePtrToVar dst dataPtr
  | .sarrayEnsureExclusive arrVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    if opt then
      -- Inline fast-path exclusivity check with @llvm.expect.i1
      let rcVal ← freshTmp "cow_rc"
      let isExcl ← freshTmp "cow_excl"
      let expExcl ← freshTmp "cow_exp"
      let fastLbl ← freshLabel "cow_fast"
      let slowLbl ← freshLabel "cow_slow"
      let mergeLbl ← freshLabel "cow_merge"
      let clonedPtr ← freshTmp "cow_cloned"
      emitLine s!"  {rcVal} = load i32, ptr {arrPtr}, align 4"
      emitLine s!"  {isExcl} = icmp eq i32 {rcVal}, 1"
      emitLine s!"  {expExcl} = call i1 @llvm.expect.i1(i1 {isExcl}, i1 true)"
      emitLine s!"  br i1 {expExcl}, label %{fastLbl}, label %{slowLbl}"
      emitLine s!"{fastLbl}:"
      storePtrToVar dst arrPtr
      emitLine s!"  br label %{mergeLbl}"
      emitLine s!"{slowLbl}:"
      emitLine s!"  {clonedPtr} = call ptr @lean_native_ensure_exclusive(ptr {arrPtr})"
      storePtrToVar dst clonedPtr
      emitLine s!"  br label %{mergeLbl}"
      emitLine s!"{mergeLbl}:"
    else
      let exclPtr ← freshTmp "cow_base"
      emitLine s!"  {exclPtr} = call ptr @lean_native_ensure_exclusive(ptr {arrPtr})"
      storePtrToVar dst exclPtr
  | .sarrayGet arrVar idxVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    let idxVal ← loadVarAsI64 idxVar
    let dataPtr ← freshTmp "sget_data"
    let elemPtr ← freshTmp "sget_gep"
    let elemVal ← freshTmp "sget_val"
    emitLine s!"  {dataPtr} = getelementptr inbounds i64, ptr {arrPtr}, i64 3"
    emitLine s!"  {elemPtr} = getelementptr inbounds i64, ptr {dataPtr}, i64 {idxVal}"
    emitLine s!"  {elemVal} = load i64, ptr {elemPtr}, align 8"
    storeI64ToVar dst elemVal
  | .sarraySet arrVar idxVar valVar _ =>
    let arrPtr ← loadVarAsPtr arrVar
    let idxVal ← loadVarAsI64 idxVar
    let valI64 ← loadVarAsI64 valVar
    let targetArr ←
      if opt then
        pure arrPtr
      else do
        let excl ← freshTmp "sset_excl"
        emitLine s!"  {excl} = call ptr @lean_native_ensure_exclusive(ptr {arrPtr})"
        pure excl
    let dataPtr ← freshTmp "sset_data"
    let elemPtr ← freshTmp "sset_gep"
    emitLine s!"  {dataPtr} = getelementptr inbounds i64, ptr {targetArr}, i64 3"
    emitLine s!"  {elemPtr} = getelementptr inbounds i64, ptr {dataPtr}, i64 {idxVal}"
    emitLine s!"  store i64 {valI64}, ptr {elemPtr}, align 8"
    storePtrToVar dst targetArr
  | .rawLoad ptrVar idxVar _ =>
    let rawPtr ← loadVarAsPtr ptrVar
    let idxVal ← loadVarAsI64 idxVar
    let elemPtr ← freshTmp "rld_gep"
    let elemVal ← freshTmp "rld_val"
    emitLine s!"  {elemPtr} = getelementptr inbounds i64, ptr {rawPtr}, i64 {idxVal}"
    emitLine s!"  {elemVal} = load i64, ptr {elemPtr}, align 8"
    storeI64ToVar dst elemVal
  | .boxScalar valVar _ =>
    let v ← loadVarAsI64 valVar
    if opt then
      -- Inline tagged pointer scalar boxing: (v << 1) | 1
      let sh ← freshTmp "tag_shl"
      let tagged ← freshTmp "tag_or"
      let taggedPtr ← freshTmp "tag_ptr"
      emitLine s!"  {sh} = shl i64 {v}, 1"
      emitLine s!"  {tagged} = or i64 {sh}, 1"
      emitLine s!"  {taggedPtr} = inttoptr i64 {tagged} to ptr"
      storePtrToVar dst taggedPtr
    else
      let boxed ← freshTmp "box_call"
      emitLine s!"  {boxed} = call ptr @lean_native_box_u64(i64 {v})"
      storePtrToVar dst boxed
  | .unboxScalar boxVar _ =>
    let p ← loadVarAsPtr boxVar
    if opt then
      let pInt ← freshTmp "untag_int"
      let uVal ← freshTmp "untag_shr"
      emitLine s!"  {pInt} = ptrtoint ptr {p} to i64"
      emitLine s!"  {uVal} = lshr i64 {pInt}, 1"
      storeI64ToVar dst uVal
    else
      let uVal ← freshTmp "unbox_call"
      emitLine s!"  {uVal} = call i64 @lean_native_unbox_u64(ptr {p})"
      storeI64ToVar dst uVal
  | .call callee args _ isExt =>
    let st ← get
    if !isExt && slotLLVMType ty == "i64" && st.localScalarSigs.lookup callee == some args.length then
      let argVals ← args.mapM loadVarAsI64
      let argSig := String.intercalate ", " (argVals.map (fun v => s!"i64 {v}"))
      let callRes ← freshTmp "call"
      emitLine s!"  {callRes} = call i64 @{sanitizeSymbol callee}({argSig})"
      storeI64ToVar dst callRes
    else
      match args[0]? with
      | some a0 => copyVarSlot dst a0
      | none =>
        let sTy := slotLLVMType ty
        if sTy == "ptr" then storePtrToVar dst "null"
        else if sTy == "i256" then storeI256ToVar dst "0"
        else storeI64ToVar dst "0"

/-- Emit inline or baseline reference count adjustment (`incRef` / `decRef`) under `RcMode`. -/
def emitRefCountOp (isInc : Bool) (objVar : VarId) (count : Nat) : EmitM Unit := do
  let st ← get
  if st.rcMode == .freestanding then return ()
  let objPtr ← loadVarAsPtr objVar
  if st.optimized then
    let isNull ← freshTmp "rc_null"
    let chkLbl ← freshLabel "rc_chk"
    let updLbl ← freshLabel "rc_upd"
    let doneLbl ← freshLabel "rc_done"
    let rcVal ← freshTmp "rc_cur"
    let isPos ← freshTmp "rc_pos"
    let expPos ← freshTmp "rc_exp"
    let nextRc ← freshTmp "rc_next"
    let updLine :=
      if st.rcMode == .atomic then
        let rmwOp := if isInc then "add" else "sub"
        let ord := if isInc then "monotonic" else "acq_rel"
        s!"{updLbl}:\n  {nextRc} = atomicrmw {rmwOp} ptr {objPtr}, i32 {count} {ord}, align 4\n  br label %{doneLbl}\n{doneLbl}:"
      else
        let opStr := if isInc then "add nsw" else "sub nsw"
        s!"{updLbl}:\n  {nextRc} = {opStr} i32 {rcVal}, {count}\n  store i32 {nextRc}, ptr {objPtr}, align 4\n  br label %{doneLbl}\n{doneLbl}:"
    for line in [
      s!"  {isNull} = icmp eq ptr {objPtr}, null\n  br i1 {isNull}, label %{doneLbl}, label %{chkLbl}",
      s!"{chkLbl}:\n  {rcVal} = load i32, ptr {objPtr}, align 4\n  {isPos} = icmp sgt i32 {rcVal}, 0",
      s!"  {expPos} = call i1 @llvm.expect.i1(i1 {isPos}, i1 true)\n  br i1 {expPos}, label %{updLbl}, label %{doneLbl}",
      updLine
    ] do emitLine line
  else
    let fn := if isInc then "@lean_native_inc" else "@lean_native_dec"
    emitLine s!"  call void {fn}(ptr {objPtr}, i64 {count})"

/-- Emit a `parFor` data-parallel loop in LLVM IR with direct SSA `phi` induction variable
    and uninitialized output allocation when every index is overwritten (`kernel != .stencil1D3Pt`). -/
def emitParForLoop (outVar lenVar : VarId) (inputs : List VarId) (_elemTy : LNIRType)
    (kernel : ParallelKernelKind) : EmitM Unit := do
  let st ← get
  let opt := st.optimized
  let nVal ← loadVarAsI64 lenVar
  let in0Var := inputs[0]?.getD outVar
  let in1Var := inputs[1]?.getD in0Var
  let in0Arr ← loadVarAsPtr in0Var
  let in1Arr ← loadVarAsPtr in1Var
  emitLine "  ; certified chunk-partition & exclusive output invariant: leannative_verify_parfor_chunk_partition"
  let outArr ← freshTmp "par_out"
  let allocFn :=
    match kernel with
    | .stencil1D3Pt _ _ _ => "@lean_native_ensure_exclusive"
    | _ => if opt then "@lean_native_ensure_exclusive_uninit" else "@lean_native_ensure_exclusive"
  emitLine s!"  {outArr} = call ptr {allocFn}(ptr {in0Arr})"
  storePtrToVar outVar outArr
  let outData ← freshTmp "par_out_data"
  let in0Data ← freshTmp "par_in0_data"
  let in1Data ← freshTmp "par_in1_data"
  emitLine s!"  {outData} = getelementptr inbounds i64, ptr {outArr}, i64 3"
  emitLine s!"  {in0Data} = getelementptr inbounds i64, ptr {in0Arr}, i64 3"
  emitLine s!"  {in1Data} = getelementptr inbounds i64, ptr {in1Arr}, i64 3"

  let preHdrLbl ← freshLabel "par_prehdr"
  let condLbl ← freshLabel "par_cond"
  let bodyLbl ← freshLabel "par_body"
  let latchLbl ← freshLabel "par_latch"
  let exitLbl ← freshLabel "par_exit"
  let ivVal ← freshTmp "par_iv"
  let nextIv ← freshTmp "par_iv_next"
  let cmpVal ← freshTmp "par_cmp"
  emitLine s!"  br label %{preHdrLbl}\n{preHdrLbl}:\n  br label %{condLbl}\n{condLbl}:"
  emitLine s!"  {ivVal} = phi i64 [ 0, %{preHdrLbl} ], [ {nextIv}, %{latchLbl} ]"
  emitLine s!"  {cmpVal} = icmp ult i64 {ivVal}, {nVal}"
  emitLine s!"  br i1 {cmpVal}, label %{bodyLbl}, label %{exitLbl}"
  emitLine s!"{bodyLbl}:"

  let p0 ← freshTmp "p_in0"
  let v0 ← freshTmp "v_in0"
  emitLine s!"  {p0} = getelementptr inbounds i64, ptr {in0Data}, i64 {ivVal}\n  {v0} = load i64, ptr {p0}, align 8"
  let loadIn1 : EmitM String := do
    let p1 ← freshTmp "p_in1"; let v1 ← freshTmp "v_in1"
    emitLine s!"  {p1} = getelementptr inbounds i64, ptr {in1Data}, i64 {ivVal}\n  {v1} = load i64, ptr {p1}, align 8"
    return v1
  let resVal ← match kernel with
    | .mapScaleAdd scale bias => do
      let m ← freshTmp "msa_mul"; let a ← freshTmp "msa_add"
      emitLine s!"  {m} = mul i64 {v0}, {scale}\n  {a} = add i64 {m}, {bias}"; pure a
    | .zipAdd => do
      let v1 ← loadIn1; let a ← freshTmp "za_add"
      emitLine s!"  {a} = add i64 {v0}, {v1}"; pure a
    | .zipMul | .dotProduct => do
      let v1 ← loadIn1; let m ← freshTmp "zm_mul"
      emitLine s!"  {m} = mul i64 {v0}, {v1}"; pure m
    | .saxpy alphaBits => do
      let v1 ← loadIn1; let m ← freshTmp "sax_mul"; let a ← freshTmp "sax_add"
      emitLine s!"  {m} = mul i64 {v0}, {alphaBits}\n  {a} = add i64 {m}, {v1}"; pure a
    | .stencil1D3Pt _ wCenter _ => do
      let m ← freshTmp "st_mul"; emitLine s!"  {m} = mul i64 {v0}, {wCenter}"; pure m
    | .customScalar idxVar inVars body => do
      let saved := (← get).scalarBindings
      let mut bindings := [(idxVar, ivVal)]
      for (bound, input) in inVars.zip inputs do
        let arr ← loadVarAsPtr input; let ptr ← freshTmp "cs_ptr"; let elemPtr ← freshTmp "cs_at"; let value ← freshTmp "cs_value"
        emitLine s!"  {ptr} = getelementptr inbounds i64, ptr {arr}, i64 3\n  {elemPtr} = getelementptr inbounds i64, ptr {ptr}, i64 {ivVal}\n  {value} = load i64, ptr {elemPtr}, align 8"
        bindings := bindings ++ [(bound, value)]
      modify fun s => { s with scalarBindings := bindings ++ saved }
      let value ← emitScalarExprWithWidth "i64" "63" body
      modify fun s => { s with scalarBindings := saved }; pure value
  let pOut ← freshTmp "p_out"
  emitLine s!"  {pOut} = getelementptr inbounds i64, ptr {outData}, i64 {ivVal}\n  store i64 {resVal}, ptr {pOut}, align 8"
  let addOp := if opt then "add nuw nsw i64" else "add i64"
  let loopMd := if opt then ", !llvm.loop !0" else ", !llvm.loop !3"
  emitLine s!"  br label %{latchLbl}\n{latchLbl}:\n  {nextIv} = {addOp} {ivVal}, 1\n  br label %{condLbl}{loopMd}\n{exitLbl}:"

/-- Check if a loop body accesses contiguous memory (`rawLoad`, `rawStore`, `sarrayGet`, `sarraySet`). -/
partial def loopBodyHasArrayMem : LNIRCode → Bool
  | .letBind _ _ (.rawLoad _ _ _) _ | .letBind _ _ (.sarrayGet _ _ _) _
  | .letBind _ _ (.sarraySet _ _ _ _) _ | .rawStore _ _ _ _ _ | .parFor _ _ _ _ _ _ => true
  | .letBind _ _ _ k | .incRef _ _ k | .decRef _ _ k => loopBodyHasArrayMem k
  | .ite _ t e | .seqFor _ _ _ _ _ _ t e => loopBodyHasArrayMem t || loopBodyHasArrayMem e
  | .ret _ | .unreachable => false

/-- Try to extract a multi-way tag comparison `ite` chain on a single discriminant `VarId`:
    `let cmp_i = (discr == tag_i); ite cmp_i branch_i rest`.
    Returns `some (discrVar, [(cmpVar_i, tag_i, branch_i), ...], defaultBranch)`. -/
partial def collectSwitchChain (expectedDiscr : Option VarId) (code : LNIRCode) :
    Option (VarId × List (VarId × UInt64 × LNIRCode) × LNIRCode) :=
  match code with
    | .letBind cmpVar _ (.scalar (.binOp .eq (.var discrVar) (.constU64 tagVal)))
        (.ite condVar thenBranch elseBranch) =>
      if cmpVar == condVar && (expectedDiscr.isNone || expectedDiscr == some discrVar) then
        match collectSwitchChain (some discrVar) elseBranch with
        | some (_, moreCases, defBranch) => some (discrVar, (cmpVar, tagVal, thenBranch) :: moreCases, defBranch)
        | none => some (discrVar, [(cmpVar, tagVal, thenBranch)], elseBranch)
      else none
    | _ => none

/-- Recursively lower an `LNIRCode` block into LLVM 18 instructions.
    When `loopAccTarget` is `some (accVar, latchLbl)`, `.ret v` inside a `seqFor` step body
    copies `v` into `accVar` and branches to `latchLbl` instead of returning from the function. -/
partial def emitCode (code : LNIRCode) (retTy : LNIRType)
    (loopAccTarget : Option (VarId × String) := none) : EmitM Unit := do
  let opt := (← get).optimized
  match code with
  | .letBind dst ty val k =>
    match collectSwitchChain none code with
    | some (discrVar, rawCases, defaultBranch) =>
      let dedupCases := rawCases.foldl (fun acc item@(_, tagVal, _) =>
        if acc.any (fun (_, t, _) => t == tagVal) then acc else acc ++ [item]) []
      if dedupCases.length >= 2 then
        let discrVal ← loadVarAsI64 discrVar
        let defLbl ← freshLabel "sw_default"
        let mut labeledCases : List (String × UInt64 × LNIRCode) := []
        for (_, tagVal, brCode) in dedupCases do
          labeledCases := labeledCases ++ [(← freshLabel s!"sw_case_{tagVal}", tagVal, brCode)]
        emitLine s!"  switch i64 {discrVal}, label %{defLbl} ["
        for (caseLbl, tagVal, _) in labeledCases do emitLine s!"    i64 {tagVal}, label %{caseLbl}"
        emitLine "  ]"
        for (caseLbl, _, brCode) in labeledCases do emitLine s!"{caseLbl}:"; emitCode brCode retTy loopAccTarget
        emitLine s!"{defLbl}:"; emitCode defaultBranch retTy loopAccTarget
      else emitLetExpr dst ty val; emitCode k retTy loopAccTarget
    | none =>
      let st ← get
      let isArm := st.optimized && st.target.isAArch64 && st.isa.sha3
      match isArm, ty, val, k with
      | true, .i64, .scalar (.binOp .bitXor (.var a) (.var b)),
          .letBind dst2 .i64 (.scalar (.binOp .bitXor (.var c) (.var d))) k2 =>
        if c == dst || d == dst then
          let thirdVar := if c == dst then d else c
          let aVal ← loadVarAsI64 a
          let bVal ← loadVarAsI64 b
          let x1 ← freshTmp "xor_pair"
          emitLine s!"  {x1} = xor i64 {aVal}, {bVal}"
          storeI64ToVar dst x1
          let cVal ← loadVarAsI64 thirdVar
          let va ← freshTmp "eor3_va"; let vb ← freshTmp "eor3_vb"; let vc ← freshTmp "eor3_vc"
          let vp ← freshTmp "eor3_vp"; let res ← freshTmp "eor3_res"
          emitLine s!"  {va} = insertelement <2 x i64> zeroinitializer, i64 {aVal}, i64 0\n  {vb} = insertelement <2 x i64> zeroinitializer, i64 {bVal}, i64 0\n  {vc} = insertelement <2 x i64> zeroinitializer, i64 {cVal}, i64 0\n  {vp} = call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64(<2 x i64> {va}, <2 x i64> {vb}, <2 x i64> {vc})\n  {res} = extractelement <2 x i64> {vp}, i64 0"
          storeI64ToVar dst2 res
          emitCode k2 retTy loopAccTarget
        else
          emitLetExpr dst ty val; emitCode k retTy loopAccTarget
      | _, _, _, _ =>
        emitLetExpr dst ty val; emitCode k retTy loopAccTarget
  | .rawStore ptrVar idxVar valVar _ k =>
    let rawPtr ← loadVarAsPtr ptrVar
    let idxVal ← loadVarAsI64 idxVar
    let valI64 ← loadVarAsI64 valVar
    let gep ← freshTmp "rst_gep"
    emitLine s!"  {gep} = getelementptr inbounds i64, ptr {rawPtr}, i64 {idxVal}"
    emitLine s!"  store i64 {valI64}, ptr {gep}, align 8"
    emitCode k retTy loopAccTarget
  | .incRef objVar count k =>
    emitRefCountOp true objVar count
    emitCode k retTy loopAccTarget
  | .decRef objVar count k =>
    emitRefCountOp false objVar count
    emitCode k retTy loopAccTarget
  | .ite condVar thenBranch elseBranch =>
    let condTy ← getVarSlotType condVar
    let cBool ← freshTmp "ite_cond"
    let thenLbl ← freshLabel "ite_then"
    let elseLbl ← freshLabel "ite_else"
    if slotLLVMType condTy == "i256" then
      let cVal ← loadVarAsI256 condVar
      emitLine s!"  {cBool} = icmp ne i256 {cVal}, 0"
    else
      let cVal ← loadVarAsI64 condVar
      emitLine s!"  {cBool} = icmp ne i64 {cVal}, 0"
    emitLine s!"  br i1 {cBool}, label %{thenLbl}, label %{elseLbl}"
    emitLine s!"{thenLbl}:"
    emitCode thenBranch retTy loopAccTarget
    emitLine s!"{elseLbl}:"
    emitCode elseBranch retTy loopAccTarget
  | .seqFor idxVar loVar hiVar accVar accInit _ stepBody k =>
    let loVal ← loadVarAsI64 loVar
    let hiVal ← loadVarAsI64 hiVar
    copyVarSlot accVar accInit
    let preHdrLbl ← freshLabel "loop_prehdr"
    let hdrLbl ← freshLabel "loop_hdr"
    let bodyLbl ← freshLabel "loop_body"
    let latchLbl ← freshLabel "loop_latch"
    let exitLbl ← freshLabel "loop_exit"
    let curIdx ← freshTmp "loop_idx"
    let idxNext ← freshTmp "loop_next"
    let cmp ← freshTmp "loop_cmp"
    emitLine s!"  br label %{preHdrLbl}\n{preHdrLbl}:\n  br label %{hdrLbl}\n{hdrLbl}:"
    emitLine s!"  {curIdx} = phi i64 [ {loVal}, %{preHdrLbl} ], [ {idxNext}, %{latchLbl} ]"
    storeI64ToVar idxVar curIdx
    emitLine s!"  {cmp} = icmp ult i64 {curIdx}, {hiVal}"
    emitLine s!"  br i1 {cmp}, label %{bodyLbl}, label %{exitLbl}"
    emitLine s!"{bodyLbl}:"
    emitCode stepBody retTy (some (accVar, latchLbl))
    emitLine s!"{latchLbl}:"
    let addOp := if opt then "add nuw nsw i64" else "add i64"
    emitLine s!"  {idxNext} = {addOp} {curIdx}, 1"
    let isVecLoop := loopBodyHasArrayMem stepBody
    let loopMd :=
      if !opt then ", !llvm.loop !3"
      else if isVecLoop then ", !llvm.loop !0"
      else ", !llvm.loop !6"
    emitLine s!"  br label %{hdrLbl}{loopMd}"
    emitLine s!"{exitLbl}:"
    emitCode k retTy loopAccTarget
  | .parFor outVar lenVar inputs elemTy kernel k =>
    emitParForLoop outVar lenVar inputs elemTy kernel
    emitCode k retTy loopAccTarget
  | .ret v =>
    match loopAccTarget with
    | some (accVar, latchLbl) =>
      copyVarSlot accVar v
      emitLine s!"  br label %{latchLbl}"
    | none =>
      let llvmRet := sigLLVMType retTy
      if llvmRet == "void" then emitLine "  ret void"
      else if llvmRet == "ptr" then emitLine s!"  ret ptr {← loadVarAsPtr v}"
      else if llvmRet == "i256" then emitLine s!"  ret i256 {← loadVarAsI256 v}"
      else if llvmRet == "i64" then emitLine s!"  ret i64 {← loadVarAsI64 v}"
      else
        let tup ← freshTmp "ret_tup"
        emitLine s!"  {tup} = load {llvmRet}, ptr %slot_v{v}, align 8\n  ret {llvmRet} {tup}"
  | .unreachable =>
    match loopAccTarget with
    | some (_, latchLbl) =>
      emitLine s!"  br label %{latchLbl}"
    | none =>
      let llvmRet := sigLLVMType retTy
      emitLine (if llvmRet == "void" then "  ret void" else if llvmRet == "ptr" then "  ret ptr null"
                else if llvmRet == "i256" then "  ret i256 0" else "  ret i64 0")

/-- Emit an LLVM 18 function definition for a single `LNIRDecl`, parameterized by `IsaLevel`. -/
def emitDeclLLVM (optimized : Bool) (d : LNIRDecl) (target : TargetArch := .x86_64)
    (localScalarSigs : List (String × Nat) := []) (isaOverride? : Option IsaLevel := none) : String :=
  let fnSym := sanitizeSymbol d.name
  let retTypeStr := sigLLVMType d.retTy
  let paramSigs := d.params.map fun p =>
    let pTy := slotLLVMType p.ty
    let attrs :=
      if optimized && pTy == "ptr" then " noalias noundef"
      else if optimized && (pTy == "i64" || pTy == "i256") then " noundef"
      else ""
    s!"{pTy}{attrs} %arg_v{p.id}"
  let paramSigStr := String.intercalate ", " paramSigs
  let fnAttr := if optimized then "#0" else "#1"
  let allVars := declSlotVars d
  let allocaLines := allVars.foldl (fun acc (vid, ty) =>
    let sTy := slotLLVMType ty
    let zeroVal := if sTy == "ptr" then "null" else if sTy == "i64" || sTy == "i256" then "0" else "zeroinitializer"
    acc ++ [s!"  %slot_v{vid} = alloca {sTy}, align 8\n  store {sTy} {zeroVal}, ptr %slot_v{vid}, align 8"]
  ) []
  let storeArgLines := d.params.map fun p => s!"  store {slotLLVMType p.ty} %arg_v{p.id}, ptr %slot_v{p.id}, align 8"
  let evmScratchLines :=
    if codeHasStorageOps d.body then
      ["  %evm_scratch_slot = alloca i256, align 8\n  %evm_scratch_val = alloca i256, align 8"]
    else []
  let rcMode := selectDeclRcMode d
  let targetIsa := isaOverride?.getD target.isaLevel
  let declIsa := codegenRequires d targetIsa
  let (_, finalState) := (emitCode d.body d.retTy none).run {
    optimized, target, isa := declIsa, rcMode, localScalarSigs, varTypes := allVars
  }
  String.intercalate "\n" ([
    s!"; LNIRDecl: {d.name} (assurance={d.assurance}, isGpuCand={d.isGpuCand}, rcMode={repr rcMode}, isaMask={declIsa.hwcapMask})",
    s!"define dso_local {retTypeStr} @{fnSym}({paramSigStr}) {fnAttr} \{\nentry:"
  ] ++ allocaLines ++ evmScratchLines ++ storeArgLines ++ finalState.lines ++ ["}"])

/-- Emit self-contained `weak_odr` runtime and C ABI benchmark kernels in LLVM 18 opaque-pointer IR. -/
def emitRuntimeAndCAbiHelpers (optimized : Bool) (target : TargetArch := .x86_64) : String :=
  let attr := if optimized then "#0" else "#1"
  let loopMd := if optimized then ", !llvm.loop !0" else ", !llvm.loop !3"
  let clmulDecl :=
    if target.isAArch64 then
      "declare <16 x i8> @llvm.aarch64.neon.pmull64(i64, i64) #2\ndeclare <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64(<2 x i64>, <2 x i64>, <2 x i64>) #2\ndeclare i64 @llvm.vscale.i64() #2"
    else "declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8 immarg) #2"
  let mkRcFn (fnName lbl op : String) (isDec : Bool := false) : String :=
    let ord := if isDec then "acq_rel" else "monotonic"
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @{fnName}(ptr %obj, i64 %count) {attr} \{",
      "entry:\n  %is_null = icmp eq ptr %obj, null\n  br i1 %is_null, label %done, label %check",
      "check:\n  %p_int = ptrtoint ptr %obj to i64\n  %tag = and i64 %p_int, 1\n  %is_scalar = icmp ne i64 %tag, 0\n  br i1 %is_scalar, label %done, label %upd",
      s!"upd:\n  %rc = load i32, ptr %obj, align 4\n  %is_pos = icmp sgt i32 %rc, 0\n  br i1 %is_pos, label %{lbl}, label %done",
      s!"{lbl}:\n  %c32 = trunc i64 %count to i32\n  %rc_prev = atomicrmw {op} ptr %obj, i32 %c32 {ord}, align 4\n  br label %done",
      "done:\n  ret void\n}"
    ]
  let mkEnsureExclFn (fnName : String) (copyPayload : Bool) : String :=
    let copyBytes := if copyPayload then "%total_bytes" else "24"
    String.intercalate "\n" [
      s!"define weak_odr dso_local ptr @{fnName}(ptr %arr) {attr} \{",
      "entry:\n  %is_null = icmp eq ptr %arr, null\n  br i1 %is_null, label %ret_same, label %chk_rc",
      "chk_rc:\n  %rc = load i32, ptr %arr, align 4\n  %is_excl = icmp eq i32 %rc, 1\n  %exp = call i1 @llvm.expect.i1(i1 %is_excl, i1 true)\n  br i1 %exp, label %ret_same, label %clone",
      "ret_same:\n  ret ptr %arr",
      "clone:\n  %sz_ptr = getelementptr inbounds i64, ptr %arr, i64 1\n  %sz = load i64, ptr %sz_ptr, align 8\n  %bytes_data = shl i64 %sz, 3\n  %total_bytes = add i64 %bytes_data, 24",
      s!"  %new_arr = call noalias ptr @malloc(i64 %total_bytes)\n  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %new_arr, ptr align 8 %arr, i64 {copyBytes}, i1 false)\n  store i32 1, ptr %new_arr, align 4",
      "  %gt1 = icmp sgt i32 %rc, 1\n  br i1 %gt1, label %dec_old, label %done_clone",
      "dec_old:\n  %rc_prev = atomicrmw sub ptr %arr, i32 1 acq_rel, align 4\n  br label %done_clone\ndone_clone:\n  ret ptr %new_arr\n}"
    ]
  let mkCpuLoopFnWithAttr (fnAttr fnLoopMd sig : String) (bodyLines : List String) : String :=
    String.intercalate "\n" ([
      s!"define weak_odr dso_local void @{sig} {fnAttr} \{",
      "entry:\n  %cmp0 = icmp eq i64 %n, 0\n  br i1 %cmp0, label %exit, label %loop",
      "loop:\n  %i = phi i64 [ 0, %entry ], [ %i_next, %loop ]"
    ] ++ bodyLines ++ [
      s!"  %i_next = add nuw nsw i64 %i, 1\n  %done = icmp eq i64 %i_next, %n\n  br i1 %done, label %exit, label %loop{fnLoopMd}",
      "exit:\n  ret void\n}"
    ])
  let mkCpuLoopFn (sig : String) (bodyLines : List String) : String :=
    mkCpuLoopFnWithAttr attr loopMd sig bodyLines
  let mkU256LimbOpFn (fnName intrOp : String) : String :=
    String.intercalate "\n" [
      s!"define weak_odr dso_local \{ i256, i1 } @{fnName}(i256 %a, i256 %b) {attr} \{",
      "entry:",
      "  %a0 = trunc i256 %a to i64\n  %b0 = trunc i256 %b to i64",
      "  %as1 = lshr i256 %a, 64\n  %a1 = trunc i256 %as1 to i64\n  %bs1 = lshr i256 %b, 64\n  %b1 = trunc i256 %bs1 to i64",
      "  %as2 = lshr i256 %a, 128\n  %a2 = trunc i256 %as2 to i64\n  %bs2 = lshr i256 %b, 128\n  %b2 = trunc i256 %bs2 to i64",
      "  %as3 = lshr i256 %a, 192\n  %a3 = trunc i256 %as3 to i64\n  %bs3 = lshr i256 %b, 192\n  %b3 = trunc i256 %bs3 to i64",
      s!"  %s0 = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %a0, i64 %b0)\n  %r0 = extractvalue \{ i64, i1 } %s0, 0\n  %c0 = extractvalue \{ i64, i1 } %s0, 1",
      s!"  %s1a = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %a1, i64 %b1)\n  %r1a = extractvalue \{ i64, i1 } %s1a, 0\n  %c1a = extractvalue \{ i64, i1 } %s1a, 1\n  %c0z = zext i1 %c0 to i64\n  %s1b = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %r1a, i64 %c0z)\n  %r1 = extractvalue \{ i64, i1 } %s1b, 0\n  %c1b = extractvalue \{ i64, i1 } %s1b, 1\n  %c1 = or i1 %c1a, %c1b",
      s!"  %s2a = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %a2, i64 %b2)\n  %r2a = extractvalue \{ i64, i1 } %s2a, 0\n  %c2a = extractvalue \{ i64, i1 } %s2a, 1\n  %c1z = zext i1 %c1 to i64\n  %s2b = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %r2a, i64 %c1z)\n  %r2 = extractvalue \{ i64, i1 } %s2b, 0\n  %c2b = extractvalue \{ i64, i1 } %s2b, 1\n  %c2 = or i1 %c2a, %c2b",
      s!"  %s3a = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %a3, i64 %b3)\n  %r3a = extractvalue \{ i64, i1 } %s3a, 0\n  %c3a = extractvalue \{ i64, i1 } %s3a, 1\n  %c2z = zext i1 %c2 to i64\n  %s3b = call \{ i64, i1 } @llvm.{intrOp}.with.overflow.i64(i64 %r3a, i64 %c2z)\n  %r3 = extractvalue \{ i64, i1 } %s3b, 0\n  %c3b = extractvalue \{ i64, i1 } %s3b, 1\n  %c3 = or i1 %c3a, %c3b",
      "  %w0 = zext i64 %r0 to i256\n  %w1 = zext i64 %r1 to i256\n  %w1s = shl i256 %w1, 64\n  %w2 = zext i64 %r2 to i256\n  %w2s = shl i256 %w2, 128\n  %w3 = zext i64 %r3 to i256\n  %w3s = shl i256 %w3, 192",
      "  %o01 = or i256 %w0, %w1s\n  %o23 = or i256 %w2s, %w3s\n  %res = or i256 %o01, %o23",
      "  %p0 = insertvalue { i256, i1 } poison, i256 %res, 0\n  %p1 = insertvalue { i256, i1 } %p0, i1 %c3, 1\n  ret { i256, i1 } %p1\n}"
    ]
  let saxpyBody := [
    "  %px = getelementptr inbounds i64, ptr %x, i64 %i\n  %py = getelementptr inbounds i64, ptr %y, i64 %i\n  %po = getelementptr inbounds i64, ptr %out, i64 %i",
    "  %vx = load i64, ptr %px, align 8\n  %vy = load i64, ptr %py, align 8\n  %prod = mul i64 %vx, %alpha\n  %res = add i64 %prod, %vy\n  store i64 %res, ptr %po, align 8"
  ]
  let mapScaleAddBody := [
    "  %pi = getelementptr inbounds i64, ptr %in0, i64 %i\n  %po = getelementptr inbounds i64, ptr %out, i64 %i",
    "  %vi = load i64, ptr %pi, align 8\n  %prod = mul i64 %vi, %scale\n  %res = add i64 %prod, %bias\n  store i64 %res, ptr %po, align 8"
  ]
  let zipAddBody := [
    "  %p0 = getelementptr inbounds i64, ptr %in0, i64 %i\n  %p1 = getelementptr inbounds i64, ptr %in1, i64 %i\n  %po = getelementptr inbounds i64, ptr %out, i64 %i",
    "  %v0 = load i64, ptr %p0, align 8\n  %v1 = load i64, ptr %p1, align 8\n  %res = add i64 %v0, %v1\n  store i64 %res, ptr %po, align 8"
  ]
  let xorAssignBody := [
    "  %pd = getelementptr inbounds i64, ptr %dst, i64 %i\n  %ps = getelementptr inbounds i64, ptr %src, i64 %i",
    "  %vd = load i64, ptr %pd, align 8\n  %vs = load i64, ptr %ps, align 8\n  %vx = xor i64 %vd, %vs\n  store i64 %vx, ptr %pd, align 8"
  ]
  let mkSve2LoopFn (sve2Attr fnLoopMd sig : String) (splatLines vecBodyLines scalarBodyLines : List String) : String :=
    String.intercalate "\n" ([
      s!"define weak_odr dso_local void @{sig} {sve2Attr} \{",
      "entry:\n  %cmp0 = icmp eq i64 %n, 0\n  br i1 %cmp0, label %exit, label %preheader",
      "preheader:\n  %vscale = call i64 @llvm.vscale.i64()\n  %step = shl nuw nsw i64 %vscale, 1\n  %vec_min = icmp uge i64 %n, %step\n  br i1 %vec_min, label %vec.ph, label %scalar.ph",
      "vec.ph:\n  %n_mod = urem i64 %n, %step\n  %n_vec = sub nuw i64 %n, %n_mod"
    ] ++ splatLines ++ [
      "  br label %vec.body",
      "vec.body:\n  %iv = phi i64 [ 0, %vec.ph ], [ %iv_next, %vec.body ]"
    ] ++ vecBodyLines ++ [
      s!"  %iv_next = add nuw i64 %iv, %step\n  %vcond = icmp ult i64 %iv_next, %n_vec\n  br i1 %vcond, label %vec.body, label %vec.exit{fnLoopMd}",
      "vec.exit:\n  %vec_done = icmp eq i64 %n_vec, %n\n  br i1 %vec_done, label %exit, label %scalar.ph",
      "scalar.ph:\n  %s_start = phi i64 [ 0, %preheader ], [ %n_vec, %vec.exit ]\n  br label %loop",
      "loop:\n  %i = phi i64 [ %s_start, %scalar.ph ], [ %i_next, %loop ]"
    ] ++ scalarBodyLines ++ [
      "  %i_next = add nuw nsw i64 %i, 1\n  %done = icmp eq i64 %i_next, %n\n  br i1 %done, label %exit, label %loop, !llvm.loop !3",
      "exit:\n  ret void\n}"
    ])
  let mkDispatchFn (fnName paramSig callArgs : String) : String :=
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @{fnName}_dispatch({paramSig}, i64 %hwcaps) {attr} \{",
      "entry:",
      "  %sel = call i8 @leansys_select_isa(i64 %hwcaps, i64 895, i8 3, i8 3)",
      "  %use_sve2 = icmp eq i8 %sel, 3",
      "  br i1 %use_sve2, label %sve2, label %baseline",
      "sve2:",
      s!"  call void @{fnName}__sve2({callArgs})",
      "  ret void",
      "baseline:",
      s!"  call void @{fnName}__baseline({callArgs})",
      "  ret void",
      "}"
    ]
  let aarch64MultiVariantStr :=
    if target.isAArch64 then
      let sve2Attr := if optimized then "#3" else "#1"
      let sve2LoopMd := if optimized then ", !llvm.loop !9" else ", !llvm.loop !3"
      [ String.intercalate "\n" [
          s!"define weak_odr dso_local i8 @leansys_select_isa(i64 %detected, i64 %req_mask, i8 %req_var, i8 %max_var) {attr} \{",
          "entry:",
          "  %gt0 = icmp ugt i8 %req_var, 0",
          "  %le_max = icmp ule i8 %req_var, %max_var",
          "  %max_ok = icmp ule i8 %max_var, 4",
          "  %b0 = and i1 %gt0, %le_max",
          "  %b1 = and i1 %b0, %max_ok",
          "  %is1 = icmp eq i8 %req_var, 1",
          "  %is2 = icmp eq i8 %req_var, 2",
          "  %is3 = icmp eq i8 %req_var, 3",
          "  %is4 = icmp eq i8 %req_var, 4",
          "  %m4 = select i1 %is4, i64 927, i64 -1",
          "  %m3 = select i1 %is3, i64 895, i64 %m4",
          "  %m2 = select i1 %is2, i64 799, i64 %m3",
          "  %canon = select i1 %is1, i64 775, i64 %m2",
          "  %mask_eq = icmp eq i64 %req_mask, %canon",
          "  %masked = and i64 %detected, %req_mask",
          "  %caps_ok = icmp eq i64 %masked, %req_mask",
          "  %b2 = and i1 %b1, %mask_eq",
          "  %admit = and i1 %b2, %caps_ok",
          "  %sel = select i1 %admit, i8 %req_var, i8 0",
          "  ret i8 %sel",
          "}"
        ],
        mkCpuLoopFnWithAttr attr loopMd "lean_native_cpu_saxpy_u64__baseline(ptr noalias %out, ptr noalias %x, ptr noalias %y, i64 %alpha, i64 %n)" saxpyBody,
        mkSve2LoopFn sve2Attr sve2LoopMd "lean_native_cpu_saxpy_u64__sve2(ptr noalias %out, ptr noalias %x, ptr noalias %y, i64 %alpha, i64 %n)"
          [ "  %a_ins = insertelement <vscale x 2 x i64> poison, i64 %alpha, i64 0",
            "  %a_splat = shufflevector <vscale x 2 x i64> %a_ins, <vscale x 2 x i64> poison, <vscale x 2 x i32> zeroinitializer" ]
          [ "  %vpx = getelementptr inbounds i64, ptr %x, i64 %iv\n  %vpy = getelementptr inbounds i64, ptr %y, i64 %iv\n  %vpo = getelementptr inbounds i64, ptr %out, i64 %iv",
            "  %svx = load <vscale x 2 x i64>, ptr %vpx, align 8\n  %svy = load <vscale x 2 x i64>, ptr %vpy, align 8",
            "  %svprod = mul <vscale x 2 x i64> %svx, %a_splat\n  %svres = add <vscale x 2 x i64> %svprod, %svy\n  store <vscale x 2 x i64> %svres, ptr %vpo, align 8" ]
          saxpyBody,
        mkDispatchFn "lean_native_cpu_saxpy_u64" "ptr noalias %out, ptr noalias %x, ptr noalias %y, i64 %alpha, i64 %n" "ptr %out, ptr %x, ptr %y, i64 %alpha, i64 %n",
        mkCpuLoopFnWithAttr attr loopMd "lean_native_cpu_map_scale_add_u64__baseline(ptr noalias %out, ptr noalias %in0, i64 %scale, i64 %bias, i64 %n)" mapScaleAddBody,
        mkSve2LoopFn sve2Attr sve2LoopMd "lean_native_cpu_map_scale_add_u64__sve2(ptr noalias %out, ptr noalias %in0, i64 %scale, i64 %bias, i64 %n)"
          [ "  %s_ins = insertelement <vscale x 2 x i64> poison, i64 %scale, i64 0",
            "  %s_splat = shufflevector <vscale x 2 x i64> %s_ins, <vscale x 2 x i64> poison, <vscale x 2 x i32> zeroinitializer",
            "  %b_ins = insertelement <vscale x 2 x i64> poison, i64 %bias, i64 0",
            "  %b_splat = shufflevector <vscale x 2 x i64> %b_ins, <vscale x 2 x i64> poison, <vscale x 2 x i32> zeroinitializer" ]
          [ "  %vpi = getelementptr inbounds i64, ptr %in0, i64 %iv\n  %vpo = getelementptr inbounds i64, ptr %out, i64 %iv",
            "  %svi = load <vscale x 2 x i64>, ptr %vpi, align 8",
            "  %svprod = mul <vscale x 2 x i64> %svi, %s_splat\n  %svres = add <vscale x 2 x i64> %svprod, %b_splat\n  store <vscale x 2 x i64> %svres, ptr %vpo, align 8" ]
          mapScaleAddBody,
        mkDispatchFn "lean_native_cpu_map_scale_add_u64" "ptr noalias %out, ptr noalias %in0, i64 %scale, i64 %bias, i64 %n" "ptr %out, ptr %in0, i64 %scale, i64 %bias, i64 %n",
        mkCpuLoopFnWithAttr attr loopMd "lean_native_cpu_zip_add_u64__baseline(ptr noalias %out, ptr noalias %in0, ptr noalias %in1, i64 %n)" zipAddBody,
        mkSve2LoopFn sve2Attr sve2LoopMd "lean_native_cpu_zip_add_u64__sve2(ptr noalias %out, ptr noalias %in0, ptr noalias %in1, i64 %n)"
          []
          [ "  %vp0 = getelementptr inbounds i64, ptr %in0, i64 %iv\n  %vp1 = getelementptr inbounds i64, ptr %in1, i64 %iv\n  %vpo = getelementptr inbounds i64, ptr %out, i64 %iv",
            "  %sv0 = load <vscale x 2 x i64>, ptr %vp0, align 8\n  %sv1 = load <vscale x 2 x i64>, ptr %vp1, align 8",
            "  %svres = add <vscale x 2 x i64> %sv0, %sv1\n  store <vscale x 2 x i64> %svres, ptr %vpo, align 8" ]
          zipAddBody,
        mkDispatchFn "lean_native_cpu_zip_add_u64" "ptr noalias %out, ptr noalias %in0, ptr noalias %in1, i64 %n" "ptr %out, ptr %in0, ptr %in1, i64 %n",
        mkCpuLoopFnWithAttr attr loopMd "lean_native_cpu_xor_assign_u64__baseline(ptr noalias %dst, ptr noalias %src, i64 %n)" xorAssignBody,
        mkSve2LoopFn sve2Attr sve2LoopMd "lean_native_cpu_xor_assign_u64__sve2(ptr noalias %dst, ptr noalias %src, i64 %n)"
          []
          [ "  %vpd = getelementptr inbounds i64, ptr %dst, i64 %iv\n  %vps = getelementptr inbounds i64, ptr %src, i64 %iv",
            "  %svd = load <vscale x 2 x i64>, ptr %vpd, align 8\n  %svs = load <vscale x 2 x i64>, ptr %vps, align 8",
            "  %svx = xor <vscale x 2 x i64> %svd, %svs\n  store <vscale x 2 x i64> %svx, ptr %vpd, align 8" ]
          xorAssignBody,
        mkDispatchFn "lean_native_cpu_xor_assign_u64" "ptr noalias %dst, ptr noalias %src, i64 %n" "ptr %dst, ptr %src, i64 %n"
      ]
    else []
  String.intercalate "\n\n" ([
    String.intercalate "\n" [
      "; --- LeanNative Runtime Intrinsics & C ABI Entrypoints ---",
      "declare i1 @llvm.expect.i1(i1, i1) #2\n" ++ clmulDecl,
      "declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64) #2\ndeclare { i64, i1 } @llvm.usub.with.overflow.i64(i64, i64) #2",
      "declare { i256, i1 } @llvm.uadd.with.overflow.i256(i256, i256) #2\ndeclare { i256, i1 } @llvm.usub.with.overflow.i256(i256, i256) #2\ndeclare { i256, i1 } @llvm.umul.with.overflow.i256(i256, i256) #2",
      "declare i256 @llvm.ctlz.i256(i256, i1 immarg) #2\ndeclare void @llvm.trap()",
      "declare void @lean_native_evm_sload(ptr, ptr, ptr)\ndeclare void @lean_native_evm_sstore(ptr, ptr, ptr)\ndeclare i64 @lean_native_trm_matryoshka_parity_u64(i64)",
      "declare noalias ptr @malloc(i64 noundef)\ndeclare void @free(ptr noundef)\ndeclare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg)"
    ],
    mkU256LimbOpFn "lean_native_u256_uadd_limbs" "uadd",
    mkU256LimbOpFn "lean_native_u256_usub_limbs" "usub",
    mkRcFn "lean_native_inc" "do_inc" "add" false,
    mkRcFn "lean_native_dec" "do_dec" "sub" true,
    s!"define weak_odr dso_local ptr @lean_native_box_u64(i64 %val) {attr} \{\nentry:\n  %sh = shl i64 %val, 1\n  %tagged = or i64 %sh, 1\n  %p = inttoptr i64 %tagged to ptr\n  ret ptr %p\n}",
    s!"define weak_odr dso_local i64 @lean_native_unbox_u64(ptr %boxed) {attr} \{\nentry:\n  %i = ptrtoint ptr %boxed to i64\n  %v = lshr i64 %i, 1\n  ret i64 %v\n}",
    mkEnsureExclFn "lean_native_ensure_exclusive" true,
    mkEnsureExclFn "lean_native_ensure_exclusive_uninit" false,
    mkCpuLoopFn "lean_native_cpu_saxpy_u64(ptr noalias %out, ptr noalias %x, ptr noalias %y, i64 %alpha, i64 %n)" saxpyBody,
    mkCpuLoopFn "lean_native_cpu_map_scale_add_u64(ptr noalias %out, ptr noalias %in0, i64 %scale, i64 %bias, i64 %n)" [
      "  %pi = getelementptr inbounds i64, ptr %in0, i64 %i\n  %po = getelementptr inbounds i64, ptr %out, i64 %i",
      "  %vi = load i64, ptr %pi, align 8\n  %prod = mul i64 %vi, %scale\n  %res = add i64 %prod, %bias\n  store i64 %res, ptr %po, align 8"
    ],
    mkCpuLoopFn "lean_native_cpu_zip_add_u64(ptr noalias %out, ptr noalias %in0, ptr noalias %in1, i64 %n)" [
      "  %p0 = getelementptr inbounds i64, ptr %in0, i64 %i\n  %p1 = getelementptr inbounds i64, ptr %in1, i64 %i\n  %po = getelementptr inbounds i64, ptr %out, i64 %i",
      "  %v0 = load i64, ptr %p0, align 8\n  %v1 = load i64, ptr %p1, align 8\n  %res = add i64 %v0, %v1\n  store i64 %res, ptr %po, align 8"
    ],
    mkCpuLoopFn "lean_native_cpu_xor_assign_u64(ptr noalias %dst, ptr noalias %src, i64 %n)" [
      "  %pd = getelementptr inbounds i64, ptr %dst, i64 %i\n  %ps = getelementptr inbounds i64, ptr %src, i64 %i",
      "  %vd = load i64, ptr %pd, align 8\n  %vs = load i64, ptr %ps, align 8\n  %vx = xor i64 %vd, %vs\n  store i64 %vx, ptr %pd, align 8"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @lean_native_swscale_down2x2_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH) {attr} \{",
      "entry:\n  %cmp_h = icmp eq i64 %dstH, 0\n  %cmp_w = icmp eq i64 %dstW, 0\n  %empty = or i1 %cmp_h, %cmp_w\n  br i1 %empty, label %exit, label %outer.ph",
      "outer.ph:\n  %vec_end = and i64 %dstW, -16\n  %has_vec = icmp uge i64 %dstW, 16\n  br label %outer.body",
      "outer.body:\n  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]\n  %sy0 = shl nuw i64 %dy, 1\n  %sy1 = or i64 %sy0, 1\n  %r0_off = mul nuw i64 %sy0, %srcStride\n  %r1_off = mul nuw i64 %sy1, %srcStride\n  %dst_off = mul nuw i64 %dy, %dstW\n  %r0_ptr = getelementptr inbounds i8, ptr %src, i64 %r0_off\n  %r1_ptr = getelementptr inbounds i8, ptr %src, i64 %r1_off\n  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off\n  br i1 %has_vec, label %vec.body, label %scalar.check",
      "vec.body:\n  %vdx = phi i64 [ 0, %outer.body ], [ %vdx_next, %vec.body ]\n  %vsx0 = shl nuw i64 %vdx, 1\n  %vsx1 = add nuw i64 %vsx0, 16\n  %vp00 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx0\n  %vp01 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx1\n  %vp10 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx0\n  %vp11 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx1\n  %vr0_lo = load <16 x i8>, ptr %vp00, align 1\n  %vr0_hi = load <16 x i8>, ptr %vp01, align 1\n  %vr1_lo = load <16 x i8>, ptr %vp10, align 1\n  %vr1_hi = load <16 x i8>, ptr %vp11, align 1",
      "  %r0_even = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>",
      "  %r0_odd  = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>",
      "  %r1_even = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <16 x i32> <i32 0, i32 2, i32 4, i32 6, i32 8, i32 10, i32 12, i32 14, i32 16, i32 18, i32 20, i32 22, i32 24, i32 26, i32 28, i32 30>",
      "  %r1_odd  = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <16 x i32> <i32 1, i32 3, i32 5, i32 7, i32 9, i32 11, i32 13, i32 15, i32 17, i32 19, i32 21, i32 23, i32 25, i32 27, i32 29, i32 31>",
      "  %z00 = zext <16 x i8> %r0_even to <16 x i16>\n  %z01 = zext <16 x i8> %r0_odd to <16 x i16>\n  %z10 = zext <16 x i8> %r1_even to <16 x i16>\n  %z11 = zext <16 x i8> %r1_odd to <16 x i16>",
      "  %vs0 = add nuw nsw <16 x i16> %z00, %z01\n  %vs1 = add nuw nsw <16 x i16> %z10, %z11\n  %vsum = add nuw nsw <16 x i16> %vs0, %vs1",
      "  %vrnd = add nuw nsw <16 x i16> %vsum, <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>",
      "  %vavg = lshr <16 x i16> %vrnd, <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>",
      "  %vout = trunc <16 x i16> %vavg to <16 x i8>\n  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %vdx\n  store <16 x i8> %vout, ptr %vdst_p, align 1",
      "  %vdx_next = add nuw i64 %vdx, 16\n  %vdone = icmp eq i64 %vdx_next, %vec_end\n  br i1 %vdone, label %scalar.check, label %vec.body, !llvm.loop !6",
      "scalar.check:\n  %dx_start = phi i64 [ 0, %outer.body ], [ %vec_end, %vec.body ]\n  %has_rem = icmp ult i64 %dx_start, %dstW\n  br i1 %has_rem, label %inner.body, label %outer.latch",
      "inner.body:\n  %dx = phi i64 [ %dx_start, %scalar.check ], [ %dx_next, %inner.body ]\n  %sx0 = shl nuw i64 %dx, 1\n  %sx1 = or i64 %sx0, 1\n  %p00_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx0\n  %p01_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx1\n  %p10_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx0\n  %p11_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx1\n  %b00 = load i8, ptr %p00_ptr, align 1\n  %b01 = load i8, ptr %p01_ptr, align 1\n  %b10 = load i8, ptr %p10_ptr, align 1\n  %b11 = load i8, ptr %p11_ptr, align 1\n  %u00 = zext i8 %b00 to i32\n  %u01 = zext i8 %b01 to i32\n  %u10 = zext i8 %b10 to i32\n  %u11 = zext i8 %b11 to i32\n  %s0 = add nuw nsw i32 %u00, %u01\n  %s1 = add nuw nsw i32 %u10, %u11\n  %sum = add nuw nsw i32 %s0, %s1\n  %rnd = add nuw nsw i32 %sum, 2\n  %avg = lshr i32 %rnd, 2\n  %out_b = trunc i32 %avg to i8\n  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx\n  store i8 %out_b, ptr %dst_ptr, align 1\n  %dx_next = add nuw i64 %dx, 1\n  %done_x = icmp eq i64 %dx_next, %dstW\n  br i1 %done_x, label %outer.latch, label %inner.body",
      "outer.latch:\n  %dy_next = add nuw i64 %dy, 1\n  %done_y = icmp eq i64 %dy_next, %dstH\n  br i1 %done_y, label %exit, label %outer.body",
      "exit:\n  ret void\n}"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @lean_native_swscale_down2x2_fused_eq_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcStride, i64 noundef %dstW, i64 noundef %dstH, i64 noundef %contrastQ8_64, i64 noundef %brightness64) {attr} \{",
      "entry:\n  %is_id_c = icmp eq i64 %contrastQ8_64, 256\n  %is_id_b = icmp eq i64 %brightness64, 0\n  %is_id = and i1 %is_id_c, %is_id_b\n  br i1 %is_id, label %fast_id, label %chk_empty",
      "fast_id:\n  call void @lean_native_swscale_down2x2_u8(ptr %dst, ptr %src, i64 %srcStride, i64 %dstW, i64 %dstH)\n  ret void",
      "chk_empty:\n  %cmp_h = icmp eq i64 %dstH, 0\n  %cmp_w = icmp eq i64 %dstW, 0\n  %empty = or i1 %cmp_h, %cmp_w\n  br i1 %empty, label %exit, label %outer.ph",
      "outer.ph:\n  %cQ8 = trunc i64 %contrastQ8_64 to i32\n  %brt = trunc i64 %brightness64 to i32\n  br label %outer.body",
      "outer.body:\n  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]\n  %sy0 = shl nuw i64 %dy, 1\n  %sy1 = or i64 %sy0, 1\n  %r0_off = mul nuw i64 %sy0, %srcStride\n  %r1_off = mul nuw i64 %sy1, %srcStride\n  %dst_off = mul nuw i64 %dy, %dstW\n  %r0_ptr = getelementptr inbounds i8, ptr %src, i64 %r0_off\n  %r1_ptr = getelementptr inbounds i8, ptr %src, i64 %r1_off\n  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off\n  br label %inner.body",
      "inner.body:\n  %dx = phi i64 [ 0, %outer.body ], [ %dx_next, %inner.body ]\n  %sx0 = shl nuw i64 %dx, 1\n  %sx1 = or i64 %sx0, 1\n  %p00_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx0\n  %p01_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx1\n  %p10_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx0\n  %p11_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx1\n  %b00 = load i8, ptr %p00_ptr, align 1\n  %b01 = load i8, ptr %p01_ptr, align 1\n  %b10 = load i8, ptr %p10_ptr, align 1\n  %b11 = load i8, ptr %p11_ptr, align 1\n  %u00 = zext i8 %b00 to i32\n  %u01 = zext i8 %b01 to i32\n  %u10 = zext i8 %b10 to i32\n  %u11 = zext i8 %b11 to i32\n  %s0 = add nuw nsw i32 %u00, %u01\n  %s1 = add nuw nsw i32 %u10, %u11\n  %sum = add nuw nsw i32 %s0, %s1\n  %rnd = add nuw nsw i32 %sum, 2\n  %avg = lshr i32 %rnd, 2\n  %cnt = sub nsw i32 %avg, 128\n  %mulc = mul nsw i32 %cnt, %cQ8\n  %rndc = add nsw i32 %mulc, 128\n  %shrc = ashr i32 %rndc, 8\n  %add128 = add nsw i32 %shrc, 128\n  %scaled = add nsw i32 %add128, %brt\n  %lt0 = icmp slt i32 %scaled, 0\n  %gt255 = icmp sgt i32 %scaled, 255\n  %cl0 = select i1 %lt0, i32 0, i32 %scaled\n  %cl = select i1 %gt255, i32 255, i32 %cl0\n  %out_b = trunc i32 %cl to i8\n  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx\n  store i8 %out_b, ptr %dst_ptr, align 1\n  %dx_next = add nuw i64 %dx, 1\n  %done_x = icmp eq i64 %dx_next, %dstW\n  br i1 %done_x, label %outer.latch, label %inner.body" ++ loopMd,
      "outer.latch:\n  %dy_next = add nuw i64 %dy, 1\n  %done_y = icmp eq i64 %dy_next, %dstH\n  br i1 %done_y, label %exit, label %outer.body",
      "exit:\n  ret void\n}"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @lean_native_swscale_down3x3_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcW, i64 noundef %dstW, i64 noundef %dstH) {attr} \{",
      "entry:\n  %cmp_h = icmp eq i64 %dstH, 0\n  %cmp_w = icmp eq i64 %dstW, 0\n  %empty = or i1 %cmp_h, %cmp_w\n  br i1 %empty, label %exit, label %outer.ph",
      "outer.ph:\n  %vec_end = and i64 %dstW, -8\n  %has_vec = icmp uge i64 %dstW, 8\n  br label %outer.body",
      "outer.body:\n  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]\n  %sy0 = mul nuw i64 %dy, 3\n  %sy1 = add nuw i64 %sy0, 1\n  %sy2 = add nuw i64 %sy0, 2\n  %r0_off = mul nuw i64 %sy0, %srcW\n  %r1_off = mul nuw i64 %sy1, %srcW\n  %r2_off = mul nuw i64 %sy2, %srcW\n  %dst_off = mul nuw i64 %dy, %dstW\n  %r0_ptr = getelementptr inbounds i8, ptr %src, i64 %r0_off\n  %r1_ptr = getelementptr inbounds i8, ptr %src, i64 %r1_off\n  %r2_ptr = getelementptr inbounds i8, ptr %src, i64 %r2_off\n  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off\n  br i1 %has_vec, label %vec.body, label %scalar.check",
      "vec.body:\n  %vdx = phi i64 [ 0, %outer.body ], [ %vdx_next, %vec.body ]\n  %vsx0 = mul nuw i64 %vdx, 3\n  %vsx1 = add nuw i64 %vsx0, 16\n  %vp00 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx0\n  %vp01 = getelementptr inbounds i8, ptr %r0_ptr, i64 %vsx1\n  %vp10 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx0\n  %vp11 = getelementptr inbounds i8, ptr %r1_ptr, i64 %vsx1\n  %vp20 = getelementptr inbounds i8, ptr %r2_ptr, i64 %vsx0\n  %vp21 = getelementptr inbounds i8, ptr %r2_ptr, i64 %vsx1",
      "  %vr0_lo = load <16 x i8>, ptr %vp00, align 1\n  %vr0_hi8 = load <8 x i8>, ptr %vp01, align 1\n  %vr0_hi = shufflevector <8 x i8> %vr0_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>",
      "  %vr1_lo = load <16 x i8>, ptr %vp10, align 1\n  %vr1_hi8 = load <8 x i8>, ptr %vp11, align 1\n  %vr1_hi = shufflevector <8 x i8> %vr1_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>",
      "  %vr2_lo = load <16 x i8>, ptr %vp20, align 1\n  %vr2_hi8 = load <8 x i8>, ptr %vp21, align 1\n  %vr2_hi = shufflevector <8 x i8> %vr2_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>",
      "  %r0_c0 = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <8 x i32> <i32 0, i32 3, i32 6, i32 9, i32 12, i32 15, i32 18, i32 21>\n  %r0_c1 = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <8 x i32> <i32 1, i32 4, i32 7, i32 10, i32 13, i32 16, i32 19, i32 22>\n  %r0_c2 = shufflevector <16 x i8> %vr0_lo, <16 x i8> %vr0_hi, <8 x i32> <i32 2, i32 5, i32 8, i32 11, i32 14, i32 17, i32 20, i32 23>",
      "  %r1_c0 = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <8 x i32> <i32 0, i32 3, i32 6, i32 9, i32 12, i32 15, i32 18, i32 21>\n  %r1_c1 = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <8 x i32> <i32 1, i32 4, i32 7, i32 10, i32 13, i32 16, i32 19, i32 22>\n  %r1_c2 = shufflevector <16 x i8> %vr1_lo, <16 x i8> %vr1_hi, <8 x i32> <i32 2, i32 5, i32 8, i32 11, i32 14, i32 17, i32 20, i32 23>",
      "  %r2_c0 = shufflevector <16 x i8> %vr2_lo, <16 x i8> %vr2_hi, <8 x i32> <i32 0, i32 3, i32 6, i32 9, i32 12, i32 15, i32 18, i32 21>\n  %r2_c1 = shufflevector <16 x i8> %vr2_lo, <16 x i8> %vr2_hi, <8 x i32> <i32 1, i32 4, i32 7, i32 10, i32 13, i32 16, i32 19, i32 22>\n  %r2_c2 = shufflevector <16 x i8> %vr2_lo, <16 x i8> %vr2_hi, <8 x i32> <i32 2, i32 5, i32 8, i32 11, i32 14, i32 17, i32 20, i32 23>",
      "  %z00 = zext <8 x i8> %r0_c0 to <8 x i16>\n  %z01 = zext <8 x i8> %r0_c1 to <8 x i16>\n  %z02 = zext <8 x i8> %r0_c2 to <8 x i16>\n  %z10 = zext <8 x i8> %r1_c0 to <8 x i16>\n  %z11 = zext <8 x i8> %r1_c1 to <8 x i16>\n  %z12 = zext <8 x i8> %r1_c2 to <8 x i16>\n  %z20 = zext <8 x i8> %r2_c0 to <8 x i16>\n  %z21 = zext <8 x i8> %r2_c1 to <8 x i16>\n  %z22 = zext <8 x i8> %r2_c2 to <8 x i16>",
      "  %s0a = add nuw nsw <8 x i16> %z00, %z01\n  %s0 = add nuw nsw <8 x i16> %s0a, %z02\n  %s1a = add nuw nsw <8 x i16> %z10, %z11\n  %s1 = add nuw nsw <8 x i16> %s1a, %z12\n  %s2a = add nuw nsw <8 x i16> %z20, %z21\n  %s2 = add nuw nsw <8 x i16> %s2a, %z22\n  %s01 = add nuw nsw <8 x i16> %s0, %s1\n  %sum9 = add nuw nsw <8 x i16> %s01, %s2\n  %sum32 = zext <8 x i16> %sum9 to <8 x i32>",
      "  %rnd = add nuw nsw <8 x i32> %sum32, <i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4>\n  %prod = mul nuw nsw <8 x i32> %rnd, <i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282>\n  %avg = lshr <8 x i32> %prod, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>",
      "  %vout = trunc <8 x i32> %avg to <8 x i8>\n  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %vdx\n  store <8 x i8> %vout, ptr %vdst_p, align 1\n  %vdx_next = add nuw i64 %vdx, 8\n  %vdone = icmp eq i64 %vdx_next, %vec_end\n  br i1 %vdone, label %scalar.check, label %vec.body, !llvm.loop !6",
      "scalar.check:\n  %dx_start = phi i64 [ 0, %outer.body ], [ %vec_end, %vec.body ]\n  %has_rem = icmp ult i64 %dx_start, %dstW\n  br i1 %has_rem, label %inner.body, label %outer.latch",
      "inner.body:\n  %dx = phi i64 [ %dx_start, %scalar.check ], [ %dx_next, %inner.body ]\n  %sx0 = mul nuw i64 %dx, 3\n  %sx1 = add nuw i64 %sx0, 1\n  %sx2 = add nuw i64 %sx0, 2\n  %p00_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx0\n  %p01_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx1\n  %p02_ptr = getelementptr inbounds i8, ptr %r0_ptr, i64 %sx2\n  %p10_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx0\n  %p11_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx1\n  %p12_ptr = getelementptr inbounds i8, ptr %r1_ptr, i64 %sx2\n  %p20_ptr = getelementptr inbounds i8, ptr %r2_ptr, i64 %sx0\n  %p21_ptr = getelementptr inbounds i8, ptr %r2_ptr, i64 %sx1\n  %p22_ptr = getelementptr inbounds i8, ptr %r2_ptr, i64 %sx2\n  %b00 = load i8, ptr %p00_ptr, align 1\n  %b01 = load i8, ptr %p01_ptr, align 1\n  %b02 = load i8, ptr %p02_ptr, align 1\n  %b10 = load i8, ptr %p10_ptr, align 1\n  %b11 = load i8, ptr %p11_ptr, align 1\n  %b12 = load i8, ptr %p12_ptr, align 1\n  %b20 = load i8, ptr %p20_ptr, align 1\n  %b21 = load i8, ptr %p21_ptr, align 1\n  %b22 = load i8, ptr %p22_ptr, align 1\n  %u00 = zext i8 %b00 to i32\n  %u01 = zext i8 %b01 to i32\n  %u02 = zext i8 %b02 to i32\n  %u10 = zext i8 %b10 to i32\n  %u11 = zext i8 %b11 to i32\n  %u12 = zext i8 %b12 to i32\n  %u20 = zext i8 %b20 to i32\n  %u21 = zext i8 %b21 to i32\n  %u22 = zext i8 %b22 to i32\n  %sr0a = add nuw nsw i32 %u00, %u01\n  %sr0 = add nuw nsw i32 %sr0a, %u02\n  %sr1a = add nuw nsw i32 %u10, %u11\n  %sr1 = add nuw nsw i32 %sr1a, %u12\n  %sr2a = add nuw nsw i32 %u20, %u21\n  %sr2 = add nuw nsw i32 %sr2a, %u22\n  %sr01 = add nuw nsw i32 %sr0, %sr1\n  %ssum9 = add nuw nsw i32 %sr01, %sr2\n  %srnd = add nuw nsw i32 %ssum9, 4\n  %sprod = mul nuw nsw i32 %srnd, 7282\n  %savg = lshr i32 %sprod, 16\n  %out_b = trunc i32 %savg to i8\n  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx\n  store i8 %out_b, ptr %dst_ptr, align 1\n  %dx_next = add nuw i64 %dx, 1\n  %done_x = icmp eq i64 %dx_next, %dstW\n  br i1 %done_x, label %outer.latch, label %inner.body",
      "outer.latch:\n  %dy_next = add nuw i64 %dy, 1\n  %done_y = icmp eq i64 %dy_next, %dstH\n  br i1 %done_y, label %exit, label %outer.body",
      "exit:\n  ret void\n}"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @lean_native_swscale_down3to2_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %srcW, i64 noundef %dstW, i64 noundef %dstH) {attr} \{",
      "entry:\n  %cmp_h = icmp eq i64 %dstH, 0\n  %cmp_w = icmp eq i64 %dstW, 0\n  %empty = or i1 %cmp_h, %cmp_w\n  br i1 %empty, label %exit, label %outer.ph",
      "outer.ph:\n  %vec_end = and i64 %dstW, -16\n  %has_vec = icmp uge i64 %dstW, 16\n  br label %outer.body",
      "outer.body:\n  %dy = phi i64 [ 0, %outer.ph ], [ %dy_next, %outer.latch ]\n  %dy_half = lshr i64 %dy, 1\n  %sy_base = mul nuw i64 %dy_half, 3\n  %dy_odd = and i64 %dy, 1\n  %is_odd_y = icmp ne i64 %dy_odd, 0\n  %syA = add nuw i64 %sy_base, %dy_odd\n  %syB = add nuw i64 %syA, 1\n  %rA_off = mul nuw i64 %syA, %srcW\n  %rB_off = mul nuw i64 %syB, %srcW\n  %dst_off = mul nuw i64 %dy, %dstW\n  %rA_ptr = getelementptr inbounds i8, ptr %src, i64 %rA_off\n  %rB_ptr = getelementptr inbounds i8, ptr %src, i64 %rB_off\n  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %dst_off\n  %vwA = select i1 %is_odd_y, <16 x i16> <i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1>, <16 x i16> <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>\n  %vwB = select i1 %is_odd_y, <16 x i16> <i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2, i16 2>, <16 x i16> <i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1, i16 1>\n  br i1 %has_vec, label %vec.body, label %scalar.check",
      "vec.body:\n  %vdx = phi i64 [ 0, %outer.body ], [ %vdx_next, %vec.body ]\n  %vdx_half = lshr i64 %vdx, 1\n  %vsx0 = mul nuw i64 %vdx_half, 3\n  %vsx1 = add nuw i64 %vsx0, 16\n  %vpA0 = getelementptr inbounds i8, ptr %rA_ptr, i64 %vsx0\n  %vpA1 = getelementptr inbounds i8, ptr %rA_ptr, i64 %vsx1\n  %vpB0 = getelementptr inbounds i8, ptr %rB_ptr, i64 %vsx0\n  %vpB1 = getelementptr inbounds i8, ptr %rB_ptr, i64 %vsx1",
      "  %vrA_lo = load <16 x i8>, ptr %vpA0, align 1\n  %vrA_hi8 = load <8 x i8>, ptr %vpA1, align 1\n  %vrA_hi = shufflevector <8 x i8> %vrA_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>",
      "  %vrB_lo = load <16 x i8>, ptr %vpB0, align 1\n  %vrB_hi8 = load <8 x i8>, ptr %vpB1, align 1\n  %vrB_hi = shufflevector <8 x i8> %vrB_hi8, <8 x i8> poison, <16 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef, i32 undef>",
      "  %rA_c0 = shufflevector <16 x i8> %vrA_lo, <16 x i8> %vrA_hi, <16 x i32> <i32 0, i32 1, i32 3, i32 4, i32 6, i32 7, i32 9, i32 10, i32 12, i32 13, i32 15, i32 16, i32 18, i32 19, i32 21, i32 22>\n  %rA_c1 = shufflevector <16 x i8> %vrA_lo, <16 x i8> %vrA_hi, <16 x i32> <i32 1, i32 2, i32 4, i32 5, i32 7, i32 8, i32 10, i32 11, i32 13, i32 14, i32 16, i32 17, i32 19, i32 20, i32 22, i32 23>",
      "  %rB_c0 = shufflevector <16 x i8> %vrB_lo, <16 x i8> %vrB_hi, <16 x i32> <i32 0, i32 1, i32 3, i32 4, i32 6, i32 7, i32 9, i32 10, i32 12, i32 13, i32 15, i32 16, i32 18, i32 19, i32 21, i32 22>\n  %rB_c1 = shufflevector <16 x i8> %vrB_lo, <16 x i8> %vrB_hi, <16 x i32> <i32 1, i32 2, i32 4, i32 5, i32 7, i32 8, i32 10, i32 11, i32 13, i32 14, i32 16, i32 17, i32 19, i32 20, i32 22, i32 23>",
      "  %zA0 = zext <16 x i8> %rA_c0 to <16 x i16>\n  %zA1 = zext <16 x i8> %rA_c1 to <16 x i16>\n  %zB0 = zext <16 x i8> %rB_c0 to <16 x i16>\n  %zB1 = zext <16 x i8> %rB_c1 to <16 x i16>",
      "  %mA0 = mul nuw nsw <16 x i16> %zA0, <i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1>\n  %mA1 = mul nuw nsw <16 x i16> %zA1, <i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2>\n  %rowA_h = add nuw nsw <16 x i16> %mA0, %mA1",
      "  %mB0 = mul nuw nsw <16 x i16> %zB0, <i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1>\n  %mB1 = mul nuw nsw <16 x i16> %zB1, <i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2, i16 1, i16 2>\n  %rowB_h = add nuw nsw <16 x i16> %mB0, %mB1",
      "  %wrowA = mul nuw nsw <16 x i16> %rowA_h, %vwA\n  %wrowB = mul nuw nsw <16 x i16> %rowB_h, %vwB\n  %sum9 = add nuw nsw <16 x i16> %wrowA, %wrowB\n  %sum32 = zext <16 x i16> %sum9 to <16 x i32>",
      "  %rnd = add nuw nsw <16 x i32> %sum32, <i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4, i32 4>\n  %prod = mul nuw nsw <16 x i32> %rnd, <i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282, i32 7282>\n  %avg = lshr <16 x i32> %prod, <i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16, i32 16>",
      "  %vout = trunc <16 x i32> %avg to <16 x i8>\n  %vdst_p = getelementptr inbounds i8, ptr %dst_row, i64 %vdx\n  store <16 x i8> %vout, ptr %vdst_p, align 1\n  %vdx_next = add nuw i64 %vdx, 16\n  %vdone = icmp eq i64 %vdx_next, %vec_end\n  br i1 %vdone, label %scalar.check, label %vec.body, !llvm.loop !6",
      "scalar.check:\n  %dx_start = phi i64 [ 0, %outer.body ], [ %vec_end, %vec.body ]\n  %has_rem = icmp ult i64 %dx_start, %dstW\n  br i1 %has_rem, label %inner.body, label %outer.latch",
      "inner.body:\n  %dx = phi i64 [ %dx_start, %scalar.check ], [ %dx_next, %inner.body ]\n  %dx_half = lshr i64 %dx, 1\n  %sx_base = mul nuw i64 %dx_half, 3\n  %dx_odd = and i64 %dx, 1\n  %is_odd_x = icmp ne i64 %dx_odd, 0\n  %sxA = add nuw i64 %sx_base, %dx_odd\n  %sxB = add nuw i64 %sxA, 1\n  %p00_ptr = getelementptr inbounds i8, ptr %rA_ptr, i64 %sxA\n  %p01_ptr = getelementptr inbounds i8, ptr %rA_ptr, i64 %sxB\n  %p10_ptr = getelementptr inbounds i8, ptr %rB_ptr, i64 %sxA\n  %p11_ptr = getelementptr inbounds i8, ptr %rB_ptr, i64 %sxB\n  %b00 = load i8, ptr %p00_ptr, align 1\n  %b01 = load i8, ptr %p01_ptr, align 1\n  %b10 = load i8, ptr %p10_ptr, align 1\n  %b11 = load i8, ptr %p11_ptr, align 1\n  %u00 = zext i8 %b00 to i32\n  %u01 = zext i8 %b01 to i32\n  %u10 = zext i8 %b10 to i32\n  %u11 = zext i8 %b11 to i32\n  %u00_2 = shl nuw nsw i32 %u00, 1\n  %u01_2 = shl nuw nsw i32 %u01, 1\n  %u10_2 = shl nuw nsw i32 %u10, 1\n  %u11_2 = shl nuw nsw i32 %u11, 1\n  %rA_even = add nuw nsw i32 %u00_2, %u01\n  %rA_odd  = add nuw nsw i32 %u00, %u01_2\n  %rB_even = add nuw nsw i32 %u10_2, %u11\n  %rB_odd  = add nuw nsw i32 %u10, %u11_2\n  %rowA_h_s = select i1 %is_odd_x, i32 %rA_odd, i32 %rA_even\n  %rowB_h_s = select i1 %is_odd_x, i32 %rB_odd, i32 %rB_even\n  %rowA_h_2 = shl nuw nsw i32 %rowA_h_s, 1\n  %rowB_h_2 = shl nuw nsw i32 %rowB_h_s, 1\n  %s_even_y = add nuw nsw i32 %rowA_h_2, %rowB_h_s\n  %s_odd_y  = add nuw nsw i32 %rowA_h_s, %rowB_h_2\n  %ssum9 = select i1 %is_odd_y, i32 %s_odd_y, i32 %s_even_y\n  %srnd = add nuw nsw i32 %ssum9, 4\n  %sprod = mul nuw nsw i32 %srnd, 7282\n  %savg = lshr i32 %sprod, 16\n  %out_b = trunc i32 %savg to i8\n  %dst_ptr = getelementptr inbounds i8, ptr %dst_row, i64 %dx\n  store i8 %out_b, ptr %dst_ptr, align 1\n  %dx_next = add nuw i64 %dx, 1\n  %done_x = icmp eq i64 %dx_next, %dstW\n  br i1 %done_x, label %outer.latch, label %inner.body",
      "outer.latch:\n  %dy_next = add nuw i64 %dy, 1\n  %done_y = icmp eq i64 %dy_next, %dstH\n  br i1 %done_y, label %exit, label %outer.body",
      "exit:\n  ret void\n}"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @lean_native_av1_cdef_filter_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %w, i64 noundef %h, i64 noundef %priStr64, i64 noundef %damping64) {attr} \{",
      "entry:\n  %total = mul nuw i64 %w, %h\n  %has_bytes = icmp ugt i64 %total, 0\n  br i1 %has_bytes, label %copy.init, label %exit",
      "copy.init:\n  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %total, i1 false)\n  %w_lt3 = icmp ult i64 %w, 3\n  %h_lt3 = icmp ult i64 %h, 3\n  %pri32 = trunc i64 %priStr64 to i32\n  %pri_le0 = icmp sle i32 %pri32, 0\n  %skip0 = or i1 %w_lt3, %h_lt3\n  %skip = or i1 %skip0, %pri_le0\n  br i1 %skip, label %exit, label %outer.ph",
      "outer.ph:\n  %h_limit = sub nuw i64 %h, 1\n  %w_limit = sub nuw i64 %w, 1\n  %dmp32 = trunc i64 %damping64 to i32\n  %dmp_pos = icmp ugt i32 %dmp32, 0\n  %shift = select i1 %dmp_pos, i32 %dmp32, i32 1\n  br label %outer.body",
      "outer.body:\n  %r = phi i64 [ 1, %outer.ph ], [ %r_next, %outer.latch ]\n  %r_prev = sub nuw i64 %r, 1\n  %r_next_row = add nuw i64 %r, 1\n  %row_off = mul nuw i64 %r, %w\n  %up_off  = mul nuw i64 %r_prev, %w\n  %dn_off  = mul nuw i64 %r_next_row, %w\n  %row_ptr = getelementptr inbounds i8, ptr %src, i64 %row_off\n  %up_ptr  = getelementptr inbounds i8, ptr %src, i64 %up_off\n  %dn_ptr  = getelementptr inbounds i8, ptr %src, i64 %dn_off\n  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %row_off\n  br label %inner.body",
      "inner.body:\n  %c = phi i64 [ 1, %outer.body ], [ %c_next, %inner.body ]\n  %c_prev = sub nuw i64 %c, 1\n  %c_plus = add nuw i64 %c, 1\n  %p_px = getelementptr inbounds i8, ptr %row_ptr, i64 %c\n  %p_n0 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_prev\n  %p_n1 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_plus\n  %p_n2 = getelementptr inbounds i8, ptr %up_ptr, i64 %c\n  %p_n3 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c\n  %b_px = load i8, ptr %p_px, align 1\n  %b_n0 = load i8, ptr %p_n0, align 1\n  %b_n1 = load i8, ptr %p_n1, align 1\n  %b_n2 = load i8, ptr %p_n2, align 1\n  %b_n3 = load i8, ptr %p_n3, align 1\n  %px = zext i8 %b_px to i32\n  %n0 = zext i8 %b_n0 to i32\n  %n1 = zext i8 %b_n1 to i32\n  %n2 = zext i8 %b_n2 to i32\n  %n3 = zext i8 %b_n3 to i32",
      "  %d0 = sub nsw i32 %n0, %px\n  %neg0 = icmp slt i32 %d0, 0\n  %nd0 = sub nsw i32 0, %d0\n  %ad0 = select i1 %neg0, i32 %nd0, i32 %d0\n  %sh0 = ashr i32 %ad0, %shift\n  %tm0 = sub nsw i32 %pri32, %sh0\n  %t0_lt0 = icmp slt i32 %tm0, 0\n  %ad0_lt = icmp slt i32 %ad0, %tm0\n  %min0 = select i1 %ad0_lt, i32 %ad0, i32 %tm0\n  %mag0 = select i1 %t0_lt0, i32 0, i32 %min0\n  %nmag0 = sub nsw i32 0, %mag0\n  %c0 = select i1 %neg0, i32 %nmag0, i32 %mag0",
      "  %d1 = sub nsw i32 %n1, %px\n  %neg1 = icmp slt i32 %d1, 0\n  %nd1 = sub nsw i32 0, %d1\n  %ad1 = select i1 %neg1, i32 %nd1, i32 %d1\n  %sh1 = ashr i32 %ad1, %shift\n  %tm1 = sub nsw i32 %pri32, %sh1\n  %t1_lt0 = icmp slt i32 %tm1, 0\n  %ad1_lt = icmp slt i32 %ad1, %tm1\n  %min1 = select i1 %ad1_lt, i32 %ad1, i32 %tm1\n  %mag1 = select i1 %t1_lt0, i32 0, i32 %min1\n  %nmag1 = sub nsw i32 0, %mag1\n  %c1 = select i1 %neg1, i32 %nmag1, i32 %mag1",
      "  %d2 = sub nsw i32 %n2, %px\n  %neg2 = icmp slt i32 %d2, 0\n  %nd2 = sub nsw i32 0, %d2\n  %ad2 = select i1 %neg2, i32 %nd2, i32 %d2\n  %sh2 = ashr i32 %ad2, %shift\n  %tm2 = sub nsw i32 %pri32, %sh2\n  %t2_lt0 = icmp slt i32 %tm2, 0\n  %ad2_lt = icmp slt i32 %ad2, %tm2\n  %min2 = select i1 %ad2_lt, i32 %ad2, i32 %tm2\n  %mag2 = select i1 %t2_lt0, i32 0, i32 %min2\n  %nmag2 = sub nsw i32 0, %mag2\n  %c2 = select i1 %neg2, i32 %nmag2, i32 %mag2",
      "  %d3 = sub nsw i32 %n3, %px\n  %neg3 = icmp slt i32 %d3, 0\n  %nd3 = sub nsw i32 0, %d3\n  %ad3 = select i1 %neg3, i32 %nd3, i32 %d3\n  %sh3 = ashr i32 %ad3, %shift\n  %tm3 = sub nsw i32 %pri32, %sh3\n  %t3_lt0 = icmp slt i32 %tm3, 0\n  %ad3_lt = icmp slt i32 %ad3, %tm3\n  %min3 = select i1 %ad3_lt, i32 %ad3, i32 %tm3\n  %mag3 = select i1 %t3_lt0, i32 0, i32 %min3\n  %nmag3 = sub nsw i32 0, %mag3\n  %c3 = select i1 %neg3, i32 %nmag3, i32 %mag3",
      "  %s01 = add nsw i32 %c0, %c1\n  %s23 = add nsw i32 %c2, %c3\n  %sum = add nsw i32 %s01, %s23\n  %srnd = add nsw i32 %sum, 2\n  %sdiv = ashr i32 %srnd, 2\n  %out_raw = add nsw i32 %px, %sdiv\n  %lt0 = icmp slt i32 %out_raw, 0\n  %gt255 = icmp sgt i32 %out_raw, 255\n  %cl0 = select i1 %lt0, i32 0, i32 %out_raw\n  %cl = select i1 %gt255, i32 255, i32 %cl0\n  %out_b = trunc i32 %cl to i8\n  %dst_p = getelementptr inbounds i8, ptr %dst_row, i64 %c\n  store i8 %out_b, ptr %dst_p, align 1\n  %c_next = add nuw nsw i64 %c, 1\n  %done_c = icmp eq i64 %c_next, %w_limit\n  br i1 %done_c, label %outer.latch, label %inner.body" ++ loopMd,
      "outer.latch:\n  %r_next = add nuw nsw i64 %r, 1\n  %done_r = icmp eq i64 %r_next, %h_limit\n  br i1 %done_r, label %exit, label %outer.body",
      "exit:\n  ret void\n}"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local void @lean_native_stencil2d_box3x3_u8(ptr noalias noundef %dst, ptr noalias noundef %src, i64 noundef %w, i64 noundef %h) {attr} \{",
      "entry:\n  %total = mul nuw i64 %w, %h\n  %has_bytes = icmp ugt i64 %total, 0\n  br i1 %has_bytes, label %copy.init, label %exit",
      "copy.init:\n  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %dst, ptr align 1 %src, i64 %total, i1 false)\n  %w_lt3 = icmp ult i64 %w, 3\n  %h_lt3 = icmp ult i64 %h, 3\n  %skip = or i1 %w_lt3, %h_lt3\n  br i1 %skip, label %exit, label %outer.ph",
      "outer.ph:\n  %h_limit = sub nuw i64 %h, 1\n  %w_limit = sub nuw i64 %w, 1\n  br label %outer.body",
      "outer.body:\n  %r = phi i64 [ 1, %outer.ph ], [ %r_next, %outer.latch ]\n  %r_prev = sub nuw i64 %r, 1\n  %r_next_row = add nuw i64 %r, 1\n  %up_off  = mul nuw i64 %r_prev, %w\n  %row_off = mul nuw i64 %r, %w\n  %dn_off  = mul nuw i64 %r_next_row, %w\n  %up_ptr  = getelementptr inbounds i8, ptr %src, i64 %up_off\n  %row_ptr = getelementptr inbounds i8, ptr %src, i64 %row_off\n  %dn_ptr  = getelementptr inbounds i8, ptr %src, i64 %dn_off\n  %dst_row = getelementptr inbounds i8, ptr %dst, i64 %row_off\n  br label %inner.body",
      "inner.body:\n  %c = phi i64 [ 1, %outer.body ], [ %c_next, %inner.body ]\n  %c_prev = sub nuw i64 %c, 1\n  %c_plus = add nuw i64 %c, 1\n  %p00 = getelementptr inbounds i8, ptr %up_ptr, i64 %c_prev\n  %p01 = getelementptr inbounds i8, ptr %up_ptr, i64 %c\n  %p02 = getelementptr inbounds i8, ptr %up_ptr, i64 %c_plus\n  %p10 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_prev\n  %p11 = getelementptr inbounds i8, ptr %row_ptr, i64 %c\n  %p12 = getelementptr inbounds i8, ptr %row_ptr, i64 %c_plus\n  %p20 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c_prev\n  %p21 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c\n  %p22 = getelementptr inbounds i8, ptr %dn_ptr, i64 %c_plus\n  %b00 = load i8, ptr %p00, align 1\n  %b01 = load i8, ptr %p01, align 1\n  %b02 = load i8, ptr %p02, align 1\n  %b10 = load i8, ptr %p10, align 1\n  %b11 = load i8, ptr %p11, align 1\n  %b12 = load i8, ptr %p12, align 1\n  %b20 = load i8, ptr %p20, align 1\n  %b21 = load i8, ptr %p21, align 1\n  %b22 = load i8, ptr %p22, align 1\n  %u00 = zext i8 %b00 to i32\n  %u01 = zext i8 %b01 to i32\n  %u02 = zext i8 %b02 to i32\n  %u10 = zext i8 %b10 to i32\n  %u11 = zext i8 %b11 to i32\n  %u12 = zext i8 %b12 to i32\n  %u20 = zext i8 %b20 to i32\n  %u21 = zext i8 %b21 to i32\n  %u22 = zext i8 %b22 to i32\n  %s0 = add nuw nsw i32 %u00, %u01\n  %s1 = add nuw nsw i32 %s0, %u02\n  %s2 = add nuw nsw i32 %s1, %u10\n  %s3 = add nuw nsw i32 %s2, %u11\n  %s4 = add nuw nsw i32 %s3, %u12\n  %s5 = add nuw nsw i32 %s4, %u20\n  %s6 = add nuw nsw i32 %s5, %u21\n  %sum9 = add nuw nsw i32 %s6, %u22\n  %rnd = add nuw nsw i32 %sum9, 4\n  %prod = mul nuw nsw i32 %rnd, 7282\n  %avg = lshr i32 %prod, 16\n  %out_b = trunc i32 %avg to i8\n  %dst_p = getelementptr inbounds i8, ptr %dst_row, i64 %c\n  store i8 %out_b, ptr %dst_p, align 1\n  %c_next = add nuw nsw i64 %c, 1\n  %done_c = icmp eq i64 %c_next, %w_limit\n  br i1 %done_c, label %outer.latch, label %inner.body" ++ loopMd,
      "outer.latch:\n  %r_next = add nuw nsw i64 %r, 1\n  %done_r = icmp eq i64 %r_next, %h_limit\n  br i1 %done_r, label %exit, label %outer.body",
      "exit:\n  ret void\n}"
    ],
    String.intercalate "\n" [
      s!"define weak_odr dso_local i64 @lean_native_luma_stats_u8(ptr noalias noundef readonly %src, i64 noundef %nPixels, i64 noundef %step) {attr} \{",
      "entry:\n  %has_px = icmp ugt i64 %nPixels, 0\n  %step_pos = icmp ugt i64 %step, 0\n  %ok = and i1 %has_px, %step_pos\n  br i1 %ok, label %loop.body, label %exit.zero",
      "loop.body:\n  %idx = phi i64 [ 0, %entry ], [ %idx_next, %loop.body ]\n  %sum = phi i64 [ 0, %entry ], [ %sum_next, %loop.body ]\n  %sumSq = phi i64 [ 0, %entry ], [ %sumSq_next, %loop.body ]\n  %cnt = phi i64 [ 0, %entry ], [ %cnt_next, %loop.body ]\n  %p = getelementptr inbounds i8, ptr %src, i64 %idx\n  %b = load i8, ptr %p, align 1\n  %v = zext i8 %b to i64\n  %v2 = mul nuw i64 %v, %v\n  %sum_next = add nuw i64 %sum, %v\n  %sumSq_next = add nuw i64 %sumSq, %v2\n  %cnt_next = add nuw i64 %cnt, 1\n  %idx_next = add nuw i64 %idx, %step\n  %more = icmp ult i64 %idx_next, %nPixels\n  br i1 %more, label %loop.body, label %compute.out" ++ loopMd,
      "compute.out:\n  %mean = udiv i64 %sum_next, %cnt_next\n  %meanSq = udiv i64 %sumSq_next, %cnt_next\n  %sq = mul nuw i64 %mean, %mean\n  %gt = icmp ugt i64 %meanSq, %sq\n  %diff = sub nuw i64 %meanSq, %sq\n  %var = select i1 %gt, i64 %diff, i64 0\n  %var_hi = shl i64 %var, 32\n  %mean_lo = and i64 %mean, 4294967295\n  %packed = or i64 %var_hi, %mean_lo\n  ret i64 %packed",
      "exit.zero:\n  ret i64 0\n}"
    ]
  ] ++ aarch64MultiVariantStr)

/-- Emit LLVM 18 loop vectorization & attribute metadata footer parameterized by `IsaLevel`.
    Uses 4-way loop interleaving (`!llvm.loop.interleave.count = 4`) and selects scalable SVE2
    vectorization (`!llvm.loop.vectorize.scalable.enable = true`) when `isa.sve2` holds, or
    fixed-width 128-bit NEON vectorization on `arm64Baseline`/`appleA15`/`appleA16_A17`. -/
def emitMetadataFooter (target : TargetArch) (isaOverride? : Option IsaLevel := none) : String :=
  let isa := isaOverride?.getD target.isaLevel
  let cpuAttr :=
    if target.isWasm then
      "\"target-features\"=\"+simd128\""
    else if !target.isAArch64 then
      "\"target-cpu\"=\"x86-64-v2\""
    else if target.isIOS then
      s!"\"target-cpu\"=\"{isa.appleCpuName}\" \"target-features\"=\"{isa.llvmTargetFeatures},+rcpc\""
    else
      s!"\"target-features\"=\"{isa.llvmTargetFeatures}\""
  let vecModeMeta :=
    if target.isAArch64 then
      if isa.sve2 then "!8 = !{!\"llvm.loop.vectorize.scalable.enable\", i1 true}"
      else "!8 = !{!\"llvm.loop.vectorize.scalable.enable\", i1 false}"
    else "!8 = !{!\"llvm.loop.vectorize.width\", i32 4}"
  let sve2AttrLine :=
    if target.isAArch64 then
      [s!"attributes #3 = \{ nounwind uwtable \"target-features\"=\"{IsaLevel.tensorG3.llvmTargetFeatures}\" }"]
    else []
  let sve2MetaLines :=
    if target.isAArch64 then
      [ "!9 = distinct !{!9, !1, !7, !10}",
        "!10 = !{!\"llvm.loop.vectorize.scalable.enable\", i1 true}" ]
    else []
  String.intercalate "\n" ([
    s!"attributes #0 = \{ nounwind uwtable {cpuAttr} }",
    "attributes #1 = { noinline nounwind optnone uwtable }",
    "attributes #2 = { nocallback nofree nosync nounwind willreturn memory(none) }"
  ] ++ sve2AttrLine ++ [
    "",
    "!llvm.ident = !{!4}",
    "!0 = distinct !{!0, !1, !7, !8}",
    "!1 = !{!\"llvm.loop.vectorize.enable\", i1 true}",
    "!2 = !{!\"llvm.loop.unroll.count\", i32 4}",
    "!3 = distinct !{!3, !5}",
    "!4 = !{!\"lean-native LLVM 18 verified backend\"}",
    "!5 = !{!\"llvm.loop.vectorize.enable\", i1 false}",
    "!6 = distinct !{!6, !2}",
    "!7 = !{!\"llvm.loop.interleave.count\", i32 4}",
    vecModeMeta
  ] ++ sve2MetaLines)

def isABIScalarIntType : LNIRType → Bool | .i64 | .usize | .i32 | .i16 | .i8 | .i1 => true | _ => false
def isABIPtrType : LNIRType → Bool | .sarray _ | .objPtr | .taggedPtr => true | _ => false
def isABIThunkableType (ty : LNIRType) : Bool := isABIScalarIntType ty || isABIPtrType ty
def isExternDecl (d : LNIRDecl) : Bool :=
  match d.body with
  | .letBind dst _ (.call fn _ _ true) (.ret retVar) => dst == retVar && fn == d.name
  | _ => false

def emitLLVMABIWrapperDecl (d : LNIRDecl) : String :=
  if isExternDecl d || !(d.params.all (fun p => isABIThunkableType p.ty)) || !(isABIThunkableType d.retTy) then ""
  else
    let fnSym := sanitizeSymbol d.name
    let indexedParams := (List.range d.params.length).zip d.params
    let abiParamSig := String.intercalate ", " (indexedParams.map fun (idx, _) => s!"ptr %abi_arg{idx}")
    let (unboxLines, callArgs) := indexedParams.foldl (fun (lines, args) (idx, p) =>
      if isABIScalarIntType p.ty then
        (lines ++ [s!"  %raw_{idx} = ptrtoint ptr %abi_arg{idx} to i64", s!"  %unboxed_{idx} = lshr i64 %raw_{idx}, 1"], args ++ [s!"i64 %unboxed_{idx}"])
      else (lines, args ++ [s!"ptr %abi_arg{idx}"])
    ) ([], [])
    let callArgsStr := String.intercalate ", " callArgs
    let callAndRetLines :=
      if isABIScalarIntType d.retTy then
        [ s!"  %ret64 = call i64 @{fnSym}({callArgsStr})",
          "  %shl = shl i64 %ret64, 1\n  %tagged = or i64 %shl, 1\n  %boxptr = inttoptr i64 %tagged to ptr\n  ret ptr %boxptr" ]
      else [ s!"  %ret = call ptr @{fnSym}({callArgsStr})\n  ret ptr %ret" ]
    String.intercalate "\n" ([
      s!"; Lean 4 C-ABI Wrapper Thunk for {d.name}",
      s!"define dso_local ptr @lean_native_abi_{fnSym}({abiParamSig}) #0 \{\nentry:"
    ] ++ unboxLines ++ callAndRetLines ++ ["}"])

def emitLLVMModule (optimized : Bool) (m : LNIRModule) (target : TargetArch := .x86_64)
    (isaOverride? : Option IsaLevel := none) : String :=
  let modeStr := if optimized then "optimized" else "baseline"
  let header := String.intercalate "\n" [
    s!"; ModuleID = '{m.moduleName}.{modeStr}'",
    s!"source_filename = \"{m.moduleName}.lean\"",
    s!"target datalayout = \"{targetDataLayout target}\"",
    s!"target triple = \"{cpuTriple target}\""
  ]
  let localScalarSigs := m.decls.filterMap fun d =>
    if d.retTy == .i64 && d.params.all (fun p => p.ty == .i64) then
      some (d.name, d.params.length)
    else none
  let declStrs := m.decls.map (emitDeclLLVM optimized · target localScalarSigs isaOverride?)
  let abiWrapperStrs := if optimized then (m.decls.map emitLLVMABIWrapperDecl).filter (!·.isEmpty) else []
  let runtimeStr := emitRuntimeAndCAbiHelpers optimized target
  let footer := emitMetadataFooter target isaOverride?
  String.intercalate "\n\n" ([header, runtimeStr] ++ declStrs ++ abiWrapperStrs ++ [footer]) ++ "\n"

def emitLLVMBaseline (m : LNIRModule) (target : TargetArch := .x86_64)
    (isaOverride? : Option IsaLevel := none) : String :=
  emitLLVMModule false m target isaOverride?

def emitLLVMOptimized (m : LNIRModule) (target : TargetArch := .x86_64)
    (isaOverride? : Option IsaLevel := none) : String :=
  emitLLVMModule true m target isaOverride?

/-- Slot-type regression: a 3-field tuple parameter with an `i256` field, a projection that
    precedes the tuple's own binding, and a `ptr`-returning `.call` with an `i64` argument. -/
def slotTypeRegressionModule : LNIRModule where
  moduleName := "slot_type_regression"
  decls := [{
    name := "slot_type_regression"
    params := [{ id := 0, name := "t", ty := .tuple [.i64, .u256, .i64] }, { id := 1, name := "n", ty := .i64 }]
    retTy := .i64
    body :=
      .letBind 2 .u256 (.projTuple 0 1)
        (.letBind 3 .i64 (.projTuple 4 2)
          (.letBind 4 (.tuple [.i64, .u256, .i64]) (.mkTuple [1, 2, 1])
            (.letBind 5 .objPtr (.call "lean_native_box_u64" [1] .objPtr)
              (.letBind 6 .objPtr (.call "lean_native_ensure_exclusive" [5] .objPtr)
                (.ret 3)))))
  }]

def slotTypeRegressionOk : Bool :=
  let d := slotTypeRegressionModule.decls.head!
  let vars := declSlotVars d
  let tup3 := "{ i64, i256, i64 }"
  let ir := emitLLVMOptimized slotTypeRegressionModule
  let has (s : String) := (ir.splitOn s).length > 1
  vars.lookup 0 == some (.tuple [.i64, .u256, .i64]) && vars.lookup 4 == some (.tuple [.i64, .u256, .i64]) &&
    vars.lookup 2 == some .u256 && vars.lookup 5 == some .objPtr && vars.lookup 6 == some .objPtr &&
    has s!"%slot_v4 = alloca {tup3}" && has "%slot_v5 = alloca ptr" && has "%slot_v6 = alloca ptr" && has "%slot_v2 = alloca i256" &&
    has s!"extractvalue {tup3}" && has s!"insertvalue {tup3}" && !has "{ i64, i64 }"

end LeanNative.Backend.LLVM

namespace LeanNative.Backend

export LeanNative.Backend.LLVM (emitLLVMBaseline emitLLVMOptimized emitLLVMABIWrapperDecl)

end LeanNative.Backend
