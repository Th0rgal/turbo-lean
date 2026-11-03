import LeanNative.Proofs.SymbolicTVExpr

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## Symbolic Execution of `ScalarExpr`, `LNIRExpr`, `LNIRCode`, and `LNIRDecl` -/

/-- Symbolic execution state tracking variable bindings, buffer aliases, exclusivity,
    normalized memory writes, and Alive2 `noUB` / `nonPoison` flags. -/
structure SymExecState where
  vars          : List (VarId × SymStateVal) := []
  bufAliases    : List (VarId × VarId) := []
  exclusiveBufs : List VarId := []
  allocRoots    : List VarId := []
  /-- C1.1: `|objFields|` of each `allocCtor` root, so `ctorGetScalar i` reads `scalarFields[i]` (never a flat index). -/
  ctorObjCounts : List (VarId × Nat) := []
  typedTuples   : List VarId := []
  boolVars      : List VarId := []
  u64Vars       : List VarId := []
  u256Vars      : List VarId := []
  sarrayVars    : List VarId := []
  objPtrVars    : List VarId := []
  extSeenRoots  : List VarId := []
  extLivenessRoots : List VarId := []
  extRcDeltas   : List (VarId × SymExpr) := []
  extRcDeltaBounds : List (VarId × Nat) := []
  refCounts     : List (VarId × Nat) := []
  rcExprs       : List (VarId × SymExpr) := []
  memWrites     : List (MemWriteSpace × VarId × SymExpr × SymExpr) := []
  heapStepEpoch : Nat := 0
  extFreeEpoch  : Nat := 0
  nextDynAllocIdx : Nat := 0
  synVarBase    : VarId := 30000
  reachCond     : SymExpr := .constBool true
  ubCond        : SymExpr := .constBool true
  noUB          : Bool := true
  nonPoison     : Bool := true
  reachable     : Bool := true
  symUnsupported : Bool := false
  /-- Symbolic-execution or RC-tracking fuel ran out (HEAPOBJ_CONTRACT C6.1/C6.2): never bypassed by identity. -/
  symExhausted  : Bool := false
  deriving Repr, Inhabited, BEq

namespace SymExecState

def lookupVar (st : SymExecState) (v : VarId) : SymStateVal :=
  match st.vars.lookup v with
  | some sv => sv
  | none => { expr := .symVar v, nonPoison := true, noUB := true }

def bindVar (st : SymExecState) (v : VarId) (sv : SymStateVal) : SymExecState :=
  let nextNoUB := st.noUB && sv.noUB
  { st with
    vars := (v, sv) :: st.vars.filter (fun (id, _) => id != v)
    ubCond := if sv.noUB then st.ubCond else .constBool false
    noUB := nextNoUB
    nonPoison := st.nonPoison && sv.nonPoison }

def resolveBuf (st : SymExecState) (v : VarId) : VarId :=
  match st.bufAliases.lookup v with
  | some root => root
  | none => v

def aliasBuf (st : SymExecState) (dst src : VarId) : SymExecState :=
  let root := st.resolveBuf src
  { st with bufAliases := (dst, root) :: st.bufAliases.filter (fun (id, _) => id != dst) }

def markExclusive (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  { st with
    exclusiveBufs := root :: st.exclusiveBufs.filter (· != root)
    refCounts := (root, 1) :: st.refCounts.filter (fun (id, _) => id != root)
    rcExprs := (root, .constU64 1) :: st.rcExprs.filter (fun (id, _) => id != root) }

def lookupExtRcDeltaExpr (st : SymExecState) (root : VarId) : SymExpr :=
  (st.extRcDeltas.lookup root).getD (.constU64 0)

def lookupExtRcDeltaBound (st : SymExecState) (root : VarId) : Nat :=
  (st.extRcDeltaBounds.lookup root).getD 0

def markUnsupported (st : SymExecState) : SymExecState :=
  { st with symUnsupported := true, noUB := false, nonPoison := false }

/-- Incomplete analysis (fuel / RC-tracking exhaustion): unsupported **and** exhausted (C6). -/
def markExhausted (st : SymExecState) : SymExecState :=
  { st.markUnsupported with symExhausted := true }

def addExtRcDelta (st : SymExecState) (bufVar : VarId) (count : Nat) (inc : Bool) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root || count == 0 then st
  else
    let prevBound := st.lookupExtRcDeltaBound root
    let nextBound := prevBound + count
    if nextBound > 0x7FFFFFFFFFFFFFFF then
      st.markUnsupported
    else
      let prev := st.lookupExtRcDeltaExpr root
      let next := normSymExpr (normSymBinOpStep (if inc then .add else .sub) prev (.constU64 count.toUInt64))
      let rest := st.extRcDeltas.filter (fun (id, _) => id != root)
      let restBounds := st.extRcDeltaBounds.filter (fun (id, _) => id != root)
      { st with
        extRcDeltas := if next == .constU64 0 then rest else (root, next) :: rest
        extRcDeltaBounds := (root, nextBound) :: restBounds }

def noteExtRoot (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root || st.extSeenRoots.contains root then st
  else { st with extSeenRoots := root :: st.extSeenRoots }

def bumpExternalHeapEpoch (st : SymExecState) (bufVar : VarId) (mayFree : Bool) : SymExecState :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root then st
  else
    let st0 := st.noteExtRoot root
    let nextEpoch := st0.heapStepEpoch + 1
    { st0 with
      heapStepEpoch := nextEpoch
      extFreeEpoch := if mayFree then st0.extFreeEpoch + 1 else st0.extFreeEpoch
      extLivenessRoots := if mayFree then [] else st0.extLivenessRoots
      exclusiveBufs := st0.exclusiveBufs.filter (fun b => b == root || st0.allocRoots.contains b)
      refCounts := st0.refCounts.filter (fun (b, _) => b == root || st0.allocRoots.contains b)
      rcExprs := st0.rcExprs.filter (fun (b, _) => b == root || st0.allocRoots.contains b) }

def lookupRcExpr (st : SymExecState) (bufVar : VarId) : SymExpr :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => .constU64 rc.toUInt64
  | none =>
    match st.rcExprs.lookup root with
    | some e => e
    | none =>
      if st.allocRoots.contains root then .constU64 0
      else .rcSym st.heapStepEpoch root

def markAllocated (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  let st1 := st.markExclusive root
  { st1 with allocRoots := root :: st1.allocRoots.filter (· != root) }

def conjoinUbCond (c1 c2 : SymExpr) : SymExpr :=
  match c1, c2 with
  | .constBool false, _ | _, .constBool false => .constBool false
  | .constBool true, x => x
  | x, .constBool true => x
  | x, y => if x == y then x else normSymIteStep x y (.constBool false)

def requireUbCond (st : SymExecState) (cond : SymExpr) : SymExecState :=
  let ncond := normSymExpr cond
  match ncond with
  | .constBool true => st
  | .constBool false => { st with noUB := false, nonPoison := false, ubCond := .constBool false }
  | _ => { st with ubCond := conjoinUbCond st.ubCond ncond }

def noteExtLiveRoot (st : SymExecState) (bufVar : VarId) : SymExecState :=
  let root := st.resolveBuf bufVar
  let st0 := st.noteExtRoot root
  if st0.allocRoots.contains root || st0.extLivenessRoots.contains root then st0
  else { st0 with extLivenessRoots := root :: st0.extLivenessRoots }

def liveRcCond (st : SymExecState) (bufVar : VarId) : SymExpr :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => .constBool (rc > 0)
  | none =>
    if st.exclusiveBufs.contains root || st.extLivenessRoots.contains root then .constBool true
    else if st.extFreeEpoch == 0 then
      match st.rcExprs.lookup root with
      | some rcE => normSymBinOpStep .lt (.constU64 0) rcE
      | none => .binOp .lt (.constU64 0) (.rcSym 0 root)
    else
      normSymBinOpStep .lt (.constU64 0) (st.lookupRcExpr root)

def exclRcCond (st : SymExecState) (bufVar : VarId) : SymExpr :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => .constBool (rc == 1)
  | none =>
    if st.exclusiveBufs.contains root then .constBool true
    else normSymBinOpStep .eq (st.lookupRcExpr root) (.constU64 1)

/-- Collision-free Cantor pairing `π(a, b)` on `Nat` (`(a + b) * (a + b + 1) / 2 + b`),
    strictly injective on `Nat × Nat` with `π(a, b) ≥ b`. -/
def cantorPairNat (a b : Nat) : Nat :=
  ((a + b) * (a + b + 1)) / 2 + b

/-- Collision-free synthetic projected-field root ID for `(epoch, parentRoot, idx)` (`idx < 16`).
    Because `parentRoot * 16 + idx + 1 ≥ 1` and `cantorPairNat` is a bijection on `Nat × Nat`,
    `projFieldRootId base ep r idx` is strictly `≥ base` and injective across arbitrary nesting
    depths and arbitrary `heapStepEpoch` values! -/
def projFieldRootId (synVarBase epoch parentRoot idx : Nat) : VarId :=
  let maxTmp := synVarBase + 16 + 2048
  maxTmp + cantorPairNat epoch (parentRoot * 16 + idx + 2)

def dynAllocRootId (synVarBase allocIdx : Nat) : VarId :=
  let maxTmp := synVarBase + 16 + 2048
  maxTmp + cantorPairNat allocIdx 1

def desugarTmpBase (synVarBase fuel' : Nat) : VarId :=
  synVarBase + 16 + fuel' * 4

/-- Check whether `root` is a heap/constructor object root rather than a pure scalar or typed SSA tuple. -/
def isDefinitelyHeapRoot (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root || st.sarrayVars.contains root || st.objPtrVars.contains root ||
     (st.refCounts.lookup root).isSome || (st.rcExprs.lookup root).isSome || st.exclusiveBufs.contains root then
    true
  else match (st.lookupVar root).expr with
    | .tuple _ => !(st.typedTuples.contains root)
    | _ => false

def isHeapObjectRoot (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  st.isDefinitelyHeapRoot root || st.extSeenRoots.contains root

def clearAlias (st : SymExecState) (v : VarId) : SymExecState :=
  { st with bufAliases := st.bufAliases.filter (fun (id, _) => id != v) }

def markTypedTuple (st : SymExecState) (v : VarId) : SymExecState :=
  { st with typedTuples := v :: st.typedTuples.filter (· != v) }

def unmarkTypedTuple (st : SymExecState) (v : VarId) : SymExecState :=
  { st with typedTuples := st.typedTuples.filter (· != v) }

def clearVarSortTags (st : SymExecState) (v : VarId) : SymExecState :=
  { st with
    typedTuples := st.typedTuples.filter (· != v)
    boolVars := st.boolVars.filter (· != v)
    u64Vars := st.u64Vars.filter (· != v)
    u256Vars := st.u256Vars.filter (· != v)
    sarrayVars := st.sarrayVars.filter (· != v)
    objPtrVars := st.objPtrVars.filter (· != v) }

def markBoolVar (st : SymExecState) (v : VarId) : SymExecState :=
  let root := st.resolveBuf v
  let heapRoot := st.allocRoots.contains root || st.sarrayVars.contains root || st.objPtrVars.contains root ||
    (match (st.lookupVar root).expr with | .tuple _ => !(st.typedTuples.contains root) | _ => false)
  if heapRoot then st
  else
    { st with
      boolVars := v :: st.boolVars.filter (· != v)
      u64Vars := st.u64Vars.filter (· != v)
      u256Vars := st.u256Vars.filter (· != v) }

def markU64Var (st : SymExecState) (v : VarId) : SymExecState :=
  let root := st.resolveBuf v
  let heapRoot := st.allocRoots.contains root || st.sarrayVars.contains root || st.objPtrVars.contains root ||
    (match (st.lookupVar root).expr with | .tuple _ => !(st.typedTuples.contains root) | _ => false)
  if heapRoot then st
  else
    { st with
      u64Vars := v :: st.u64Vars.filter (· != v)
      boolVars := st.boolVars.filter (· != v)
      u256Vars := st.u256Vars.filter (· != v) }

def markU256Var (st : SymExecState) (v : VarId) : SymExecState :=
  let root := st.resolveBuf v
  let heapRoot := st.allocRoots.contains root || st.sarrayVars.contains root || st.objPtrVars.contains root ||
    (match (st.lookupVar root).expr with | .tuple _ => !(st.typedTuples.contains root) | _ => false)
  if heapRoot then st
  else
    { st with
      u256Vars := v :: st.u256Vars.filter (· != v)
      boolVars := st.boolVars.filter (· != v)
      u64Vars := st.u64Vars.filter (· != v) }

def hasKnownRuntimeSort (st : SymExecState) (v : VarId) : Bool :=
  let root := st.resolveBuf v
  st.boolVars.contains v || st.u64Vars.contains v || st.u256Vars.contains v ||
  st.sarrayVars.contains v || st.objPtrVars.contains v || st.typedTuples.contains v ||
  st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
  st.sarrayVars.contains root || st.objPtrVars.contains root || st.typedTuples.contains root ||
  st.allocRoots.contains root ||
  (match (st.lookupVar root).expr with
   | .constBool _ | .constU64 _ | .constU256 _ | .tuple _ | .unit => true
   | _ => false)

def markSarrayVar (st : SymExecState) (v : VarId) : SymExecState :=
  let root := st.resolveBuf v
  if st.allocRoots.contains root || st.objPtrVars.contains root ||
     st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
     st.typedTuples.contains root then st
  else
    { st with
      sarrayVars := v :: st.sarrayVars.filter (· != v)
      boolVars := st.boolVars.filter (· != v)
      u64Vars := st.u64Vars.filter (· != v)
      u256Vars := st.u256Vars.filter (· != v)
      objPtrVars := st.objPtrVars.filter (· != v) }

def markObjPtrVar (st : SymExecState) (v : VarId) : SymExecState :=
  let root := st.resolveBuf v
  if st.allocRoots.contains root || st.sarrayVars.contains root ||
     st.boolVars.contains root || st.u64Vars.contains root || st.u256Vars.contains root ||
     st.typedTuples.contains root then st
  else
    { st with
      objPtrVars := v :: st.objPtrVars.filter (· != v)
      boolVars := st.boolVars.filter (· != v)
      u64Vars := st.u64Vars.filter (· != v)
      u256Vars := st.u256Vars.filter (· != v)
      sarrayVars := st.sarrayVars.filter (· != v) }

/-- True when `bufVar` cannot hold an immediate unboxed scalar/bool/tuple/unit in `VarEnv`
    (i.e. it is an allocated object, `.sarray` parameter, `.objPtr` parameter, or constructor-tag-refined root). -/
def isNeverScalarRef (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  st.allocRoots.contains root || st.sarrayVars.contains root || st.objPtrVars.contains root ||
  (match (st.lookupVar root).expr with
   | .tuple _ => !(st.typedTuples.contains root)
   | _ => false)

def isImmediateScalarObj (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  if st.allocRoots.contains root || (st.refCounts.lookup root).isSome ||
     (st.rcExprs.lookup root).isSome || st.exclusiveBufs.contains root then
    false
  else
    match (st.lookupVar root).expr with
    | .constU64 _ | .constU256 _ | .constBool _ | .unit => true
    | _ => false


def isBufLive (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  match st.refCounts.lookup root with
  | some rc => rc > 0
  | none => true

def isBufExclusive (st : SymExecState) (bufVar : VarId) : Bool :=
  let root := st.resolveBuf bufVar
  st.exclusiveBufs.contains root

def readBufSym (st : SymExecState) (space : MemWriteSpace) (bufVar : VarId) (idx : SymExpr) : SymExpr :=
  let root := st.resolveBuf bufVar
  let nidx := normSymExpr idx
  match st.memWrites.find? (fun (sp, b, i, _) => sp == space && b == root && i == nidx) with
  | some (_, _, _, val) => val
  | none =>
    if space == .ctorObj then
      match nidx with
      | .constU64 idxU64 =>
        let i := idxU64.toNat
        if i < 8 then .symVar (projFieldRootId st.synVarBase 0 root i)
        else .bufElem space root nidx
      | _ => .bufElem space root nidx
    else if space == .ctorScalar then
      match nidx with
      | .constU64 idxU64 =>
        let i := idxU64.toNat
        if i < 8 then .symVar (projFieldRootId st.synVarBase 0 root (8 + i))
        else .bufElem space root nidx
      | _ => .bufElem space root nidx
    else if space == .ctorTag then
      match (st.lookupVar root).expr with
      | .tuple (tag :: _) => tag
      | _ => .ctorTag 0 root
    else
      .bufElem space root nidx

def writeBufSym (st : SymExecState) (space : MemWriteSpace) (bufVar : VarId) (idx val : SymExpr) (requireExcl : Bool) : SymExecState :=
  let root := st.resolveBuf bufVar
  let nidx := normSymExpr idx
  let nval := normSymExpr val
  let stExcl := if requireExcl then st.requireUbCond (st.exclRcCond root) else st
  let exclOk := if requireExcl then st.isBufExclusive root else true
  let filtered := stExcl.memWrites.filter (fun (sp, b, i, _) => !(sp == space && b == root && i == nidx))
  { stExcl with
    memWrites := (space, root, nidx, nval) :: filtered
    noUB := stExcl.noUB && exclOk }

/-- Fuel-bounded unfolding of heap-allocated constructor roots (`allocRoots` / `refCounts`) plus
    path-aware canonical alpha-renaming of freshly allocated root IDs (`200000 + idx`).
    This preserves internal aliasing/sharing relationships across returns and writes as well as
    terminal reference counts across equivalent allocations with different SSA `VarId`s while
    leaving input parameter and projected synthetic input IDs intact. -/
def expandHeapExpr (st : SymExecState) : Nat → SymExpr → SymExpr
  | 0, e => e
  | d + 1, .symVar id =>
    let root := st.resolveBuf id
    let rootExpr := (st.lookupVar root).expr
    let hasCachedCtorTuple :=
      !(st.typedTuples.contains root) &&
      (match rootExpr with | .tuple _ => true | _ => false)
    if st.allocRoots.contains root || (st.refCounts.lookup root).isSome ||
       (st.rcExprs.lookup root).isSome || hasCachedCtorTuple then
      let rcExpr := st.lookupRcExpr root
      let rootMarker : SymExpr :=
        if st.allocRoots.contains root then .allocTag root else .symVar root
      match rootExpr with
      | .tuple fs =>
        let fs' := fs.map (expandHeapExpr st d)
        .tuple (rootMarker :: rcExpr :: fs')
      | .ite c t f =>
        if st.allocRoots.contains root then
          let mkArm (arm : SymExpr) : SymExpr :=
            match arm with
            | .tuple fs => .tuple (rootMarker :: rcExpr :: fs.map (expandHeapExpr st d))
            | _ => .tuple [rootMarker, rcExpr]
          normSymIteStep c (mkArm t) (mkArm f)
        else
          rootExpr
      | .symVar rId =>
        let eff := st.resolveBuf rId
        if st.allocRoots.contains eff then
          .tuple [.allocTag eff, rcExpr]
        else
          .symVar eff
      | e => e
    else .symVar root
  | d + 1, .tuple fs => .tuple (fs.map (expandHeapExpr st d))
  | d + 1, .ite c t e =>
    normSymIteStep c (expandHeapExpr st d t) (expandHeapExpr st d e)
  | _ + 1, e => e

def alphaRenameAllocTags (_st : SymExecState) (expr : SymExpr) : SymExpr :=
  let rec go (e : SymExpr) (ren : List (VarId × VarId)) : SymExpr × List (VarId × VarId) :=
    match e with
    | .allocTag origRoot =>
      match ren.lookup origRoot with
      | some canonId => (.allocTag canonId, ren)
      | none =>
        let canonId := ren.length
        (.allocTag canonId, ren ++ [(origRoot, canonId)])
    | .mulDiv256 isUp a b d =>
      let (a', ren1) := go a ren
      let (b', ren2) := go b ren1
      let (d', ren3) := go d ren2
      (.mulDiv256 isUp a' b' d', ren3)
    | .binOp op l r =>
      let (l', ren1) := go l ren
      let (r', ren2) := go r ren1
      (normSymBinOpStep op l' r', ren2)
    | .unaryOp op a =>
      let (a', ren1) := go a ren
      (normSymUnaryOpStep op a', ren1)
    | .ite c t f =>
      let (c', renC) := go c ren
      let (t', _) := go t renC
      let (f', _) := go f renC
      (normSymIteStep c' t' f', renC)
    | .tuple fs =>
      let (fs', renFinal) := fs.foldl (fun (acc, curRen) f =>
        let (f', nextRen) := go f curRen
        (acc ++ [f'], nextRen)) ([], ren)
      (.tuple fs', renFinal)
    | .bufElem sp b idx =>
      let (idx', ren1) := go idx ren
      (.bufElem sp b idx', ren1)
    | other => (other, ren)
  (go expr []).1

mutual
  /-- Simplify nested `.ite` and matching boolean atoms over condition `c` under path assumption `val`. -/
  def substCondInSymExpr (c : SymExpr) (val : Bool) : SymExpr → SymExpr
    | .ite c2 t f =>
      let e := SymExpr.ite c2 t f
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else if c2 == c then
        if val then substCondInSymExpr c val t else substCondInSymExpr c val f
      else if c2 == normSymUnaryOpStep .not c then
        if val then substCondInSymExpr c val f else substCondInSymExpr c val t
      else
        normSymIteStep (substCondInSymExpr c val c2) (substCondInSymExpr c val t) (substCondInSymExpr c val f)
    | .tuple fs =>
      let e := SymExpr.tuple fs
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else .tuple (substCondInSymExprList c val fs)
    | .binOp op l r =>
      let e := SymExpr.binOp op l r
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else
        let impliedBounds : Bool :=
          val && (match c, e with
            | .binOp .lt (.constU64 i) (.ctorLen sc1 ep1 r1), .binOp .lt (.constU64 j) (.ctorLen sc2 ep2 r2) =>
              sc1 == sc2 && ep1 == ep2 && r1 == r2 && decide (j ≤ i)
            | _, _ => false)
        if impliedBounds then .constBool true
        else normSymBinOpStep op (substCondInSymExpr c val l) (substCondInSymExpr c val r)
    | .mulDiv256 isUp a b d =>
      let e := SymExpr.mulDiv256 isUp a b d
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else .mulDiv256 isUp (substCondInSymExpr c val a) (substCondInSymExpr c val b) (substCondInSymExpr c val d)
    | .unaryOp op a =>
      let e := SymExpr.unaryOp op a
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else normSymUnaryOpStep op (substCondInSymExpr c val a)
    | .bufElem sp b idx =>
      let e := SymExpr.bufElem sp b idx
      if e == c then .constBool val
      else if e == normSymUnaryOpStep .not c then .constBool (!val)
      else .bufElem sp b (substCondInSymExpr c val idx)
    | other =>
      if other == c then .constBool val
      else if other == normSymUnaryOpStep .not c then .constBool (!val)
      else other

  def substCondInSymExprList (c : SymExpr) (val : Bool) : List SymExpr → List SymExpr
    | [] => []
    | x :: xs => substCondInSymExpr c val x :: substCondInSymExprList c val xs
end

/-- Distribute `.tuple` across `.ite` (`(ite c t f, x) -> ite c (t[c=true], x[c=true]) (f[c=false], x[c=false])`)
    up to bounded fuel so every feasible path's `(retVal, memWrites)` pair is alpha-renamed jointly! -/
def hoistIteTupleFuel : Nat → SymExpr → SymExpr
  | 0, e => e
  | d + 1, .tuple fs =>
    let fs' := fs.map (hoistIteTupleFuel d)
    let rec splitFirstIte : List SymExpr → List SymExpr → Option (SymExpr × List SymExpr × List SymExpr)
      | _, [] => none
      | pre, .ite c t f :: post =>
        let preT := pre.map (substCondInSymExpr c true)
        let postT := post.map (substCondInSymExpr c true)
        let preF := pre.map (substCondInSymExpr c false)
        let postF := post.map (substCondInSymExpr c false)
        some (c, preT ++ [substCondInSymExpr c true t] ++ postT,
                 preF ++ [substCondInSymExpr c false f] ++ postF)
      | pre, x :: post => splitFirstIte (pre ++ [x]) post
    match splitFirstIte [] fs' with
    | some (c, tFs, fFs) =>
      normSymIteStep c (hoistIteTupleFuel d (.tuple tFs)) (hoistIteTupleFuel d (.tuple fFs))
    | none => .tuple fs'
  | d + 1, .ite c t f =>
    let hc := hoistIteTupleFuel d c
    match hc with
    | .ite cOuter cT cF =>
      let tSub := substCondInSymExpr cOuter true t
      let fSub := substCondInSymExpr cOuter true f
      let tSubF := substCondInSymExpr cOuter false t
      let fSubF := substCondInSymExpr cOuter false f
      normSymIteStep cOuter
        (hoistIteTupleFuel d (normSymIteStep cT tSub fSub))
        (hoistIteTupleFuel d (normSymIteStep cF tSubF fSubF))
    | _ =>
      normSymIteStep hc
        (hoistIteTupleFuel d (substCondInSymExpr hc true t))
        (hoistIteTupleFuel d (substCondInSymExpr hc false f))
  | _ + 1, e => e

def pruneDeadLiveAllocEntries : SymExpr → SymExpr
  | .ite c t f => normSymIteStep c (pruneDeadLiveAllocEntries t) (pruneDeadLiveAllocEntries f)
  | .tuple [retE, writesE, .tuple allocEs] =>
    let kept := allocEs.filter fun entry =>
      match entry with
      | .tuple (_ :: .constU64 0 :: _) => false
      | _ => true
    .tuple [retE, writesE, .tuple kept]
  | other => other

def summarizeHeapExpr (st : SymExecState) (expr : SymExpr) : SymExpr :=
  normSymExpr (st.alphaRenameAllocTags (hoistIteTupleFuel 16 (normSymExpr (st.expandHeapExpr 16 expr))))

end SymExecState


end LeanNative.Proofs
