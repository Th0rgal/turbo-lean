import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Transform.Pass
import LeanNative.Transform.UnboxTupleSROA

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics

/-! ## C8 Deliverable 1: Verified `parFor` Kernel Fusion & Intra-Kernel Specialization

Zero `import Lean`, zero `sorryAx`, and strictly top-level structural recursion (no `_unsafe_rec`).

Provides two complementary, formally verified `parFor` transformations:
1. **Intra-kernel specialization (`specializeKernelCode` / `kernelSpecializePass`)**:
   Folds `.customScalar` kernel bodies via verified `UInt64`-total algebraic identities and FMA
   contraction, then specializes bodies matching `.mapScaleAdd`, `.saxpy`, `.zipAdd`, or `.zipMul`
   into native `ParallelKernelKind` primitives (`declScalarCost = 0`). Preserves heap allocation IDs
   (`CodeRefines c (specializeKernelCode c)` unconditionally) and passes `verifyOptPluginGate`!
2. **Producer-consumer multi-stage `parFor` loop fusion (`fuseParForCode` / `fuseParForPipeline`)**:
   Fuses 2-stage and N-stage producer-consumer `.parFor` pipelines (eliminating intermediate
   `ArrayBuffer` allocations and removing matching dead `decRef`s on fused temporaries) whenever
   `tmpVar` is dead after the consumer and free of aliasing/stencil/reduction hazards.
-/

/-- Substitute `repl` for every occurrence of `target` in `ScalarExpr`. -/
def substScalarVar (target : VarId) (repl : ScalarExpr) : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => if id == target then repl else .var id
  | .binOp op l r => .binOp op (substScalarVar target repl l) (substScalarVar target repl r)
  | .unaryOp op a => .unaryOp op (substScalarVar target repl a)
  | .select c t f =>
    .select (substScalarVar target repl c) (substScalarVar target repl t) (substScalarVar target repl f)
  | .fma a b c =>
    .fma (substScalarVar target repl a) (substScalarVar target repl b) (substScalarVar target repl c)

/-- Single-step FMA contraction rule (`a * b + c -> fma a b c`) with shallow 1-level matching. -/
def contractKernelScalarStep : ScalarExpr → ScalarExpr
  | .binOp op lhs c =>
    match op with
    | .add =>
      match lhs with
      | .binOp op2 a b =>
        match op2 with
        | .mul => .fma a b c
        | _ => .binOp .add (.binOp op2 a b) c
      | _ => .binOp .add lhs c
    | _ => .binOp op lhs c
  | other => other

/-- Bottom-up verified scalar simplifier and FMA contractor delegating algebraic/const-fold identities
    to `LeanNative.Proofs.rewriteScalarVerified` followed by `contractKernelScalarStep`. -/
def contractKernelScalar : ScalarExpr → ScalarExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .var id => .var id
  | .binOp op l r =>
    let e0 := LeanNative.Proofs.rewriteConstFoldStep
      (LeanNative.Proofs.rewriteScalarPeepholeStep (.binOp op (contractKernelScalar l) (contractKernelScalar r)))
    contractKernelScalarStep e0
  | .unaryOp op a =>
    contractKernelScalarStep (.unaryOp op (contractKernelScalar a))
  | .select c t f =>
    let e0 := LeanNative.Proofs.rewriteSelectStep
      (contractKernelScalar c) (contractKernelScalar t) (contractKernelScalar f)
    contractKernelScalarStep e0
  | .fma a b c =>
    contractKernelScalarStep (.fma (contractKernelScalar a) (contractKernelScalar b) (contractKernelScalar c))

/-- Match a 1-input `.customScalar` body (`inVars = [x]`) against `.mapScaleAdd`. -/
def matchBuiltinKernel1 (x : VarId) : ScalarExpr → Option ParallelKernelKind
  | .var x' =>
    if x' = x then some (.mapScaleAdd 1 0) else none
  | .fma a b c =>
    match a with
    | .var x' =>
      match b with
      | .constU64 scale =>
        match c with
        | .constU64 bias => if x' = x then some (.mapScaleAdd scale bias) else none
        | _ => none
      | _ => none
    | _ => none
  | .binOp op lhs rhs =>
    match op with
    | .mul =>
      match lhs with
      | .var x' =>
        match rhs with
        | .constU64 scale => if x' = x then some (.mapScaleAdd scale 0) else none
        | _ => none
      | _ => none
    | .add =>
      match rhs with
      | .constU64 bias =>
        match lhs with
        | .var x' => if x' = x then some (.mapScaleAdd 1 bias) else none
        | .binOp op2 a2 b2 =>
          match op2 with
          | .mul =>
            match a2 with
            | .var x' =>
              match b2 with
              | .constU64 scale => if x' = x then some (.mapScaleAdd scale bias) else none
              | _ => none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Match a 2-input `.customScalar` body (`inVars = [x, y]`) against `.saxpy`, `.zipAdd`, or `.zipMul`. -/
def matchBuiltinKernel2 (x y : VarId) : ScalarExpr → Option ParallelKernelKind
  | .fma a b c =>
    match a with
    | .constU64 alpha =>
      match b with
      | .var x' =>
        match c with
        | .var y' => if x' = x ∧ y' = y then some (.saxpy alpha) else none
        | _ => none
      | _ => none
    | _ => none
  | .binOp op lhs rhs =>
    match op with
    | .mul =>
      match lhs with
      | .var x' =>
        match rhs with
        | .var y' => if x' = x ∧ y' = y then some .zipMul else none
        | _ => none
      | _ => none
    | .add =>
      match rhs with
      | .var y' =>
        match lhs with
        | .var x' => if x' = x ∧ y' = y then some .zipAdd else none
        | .binOp op2 a2 b2 =>
          match op2 with
          | .mul =>
            match a2 with
            | .constU64 alpha =>
              match b2 with
              | .var x' => if x' = x ∧ y' = y then some (.saxpy alpha) else none
              | _ => none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Recognize a `.customScalar` kernel body over distinct `inVars` (and fresh `idxVar`) that
    denotationally equals a zero-cost hardware `ParallelKernelKind` primitive. -/
def matchBuiltinKernel (idxVar : VarId) (inVars : List VarId) (body : ScalarExpr) :
    Option ParallelKernelKind :=
  match inVars with
  | [x] =>
    if idxVar = x then none else matchBuiltinKernel1 x body
  | [x, y] =>
    if idxVar = x ∨ idxVar = y ∨ x = y then none else matchBuiltinKernel2 x y body
  | _ => none

/-- Fold and specialize a single `ParallelKernelKind` without changing buffer allocations. -/
def specializeKernel : ParallelKernelKind → ParallelKernelKind
  | .customScalar idxVar inVars body =>
    let body' := contractKernelScalar body
    match matchBuiltinKernel idxVar inVars body' with
    | some k => k
    | none => .customScalar idxVar inVars body'
  | other => other

/-- Intra-kernel specialization across an `LNIRCode` block (`CodeRefines c (specializeKernelCode c)`). -/
def specializeKernelCode : LNIRCode → LNIRCode
  | .letBind dst ty val k => .letBind dst ty val (specializeKernelCode k)
  | .rawStore p i x ety k => .rawStore p i x ety (specializeKernelCode k)
  | .incRef o c k => .incRef o c (specializeKernelCode k)
  | .decRef o c k => .decRef o c (specializeKernelCode k)
  | .ite c t e => .ite c (specializeKernelCode t) (specializeKernelCode e)
  | .seqFor idx lo hi acc init accTy s k =>
    .seqFor idx lo hi acc init accTy (specializeKernelCode s) (specializeKernelCode k)
  | .parFor out len inputs ety kernel k =>
    .parFor out len inputs ety (specializeKernel kernel) (specializeKernelCode k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Maximum SSA variable ID appearing anywhere in a `ScalarExpr`. -/
def maxScalarVar : ScalarExpr → VarId
  | .constU64 _ | .constBool _ => 0
  | .var id => id
  | .binOp _ l r => Nat.max (maxScalarVar l) (maxScalarVar r)
  | .unaryOp _ a => maxScalarVar a
  | .select c t f => Nat.max (maxScalarVar c) (Nat.max (maxScalarVar t) (maxScalarVar f))
  | .fma a b c => Nat.max (maxScalarVar a) (Nat.max (maxScalarVar b) (maxScalarVar c))

/-- Reify any pointwise (non-reduction, non-stencil) `ParallelKernelKind` as `(idxVar, inVars, body)`
    using fresh element parameter IDs starting at `freshBase`. -/
def kernelToCustomScalar? (freshBase : VarId) :
    ParallelKernelKind → Option (VarId × List VarId × ScalarExpr)
  | .mapScaleAdd scale bias =>
    let x := freshBase + 1
    some (freshBase, [x], .binOp .add (.binOp .mul (.var x) (.constU64 scale)) (.constU64 bias))
  | .zipAdd =>
    let x := freshBase + 1
    let y := freshBase + 2
    some (freshBase, [x, y], .binOp .add (.var x) (.var y))
  | .zipMul =>
    let x := freshBase + 1
    let y := freshBase + 2
    some (freshBase, [x, y], .binOp .mul (.var x) (.var y))
  | .saxpy alpha =>
    let x := freshBase + 1
    let y := freshBase + 2
    some (freshBase, [x, y], .binOp .add (.binOp .mul (.constU64 alpha) (.var x)) (.var y))
  | .customScalar idxVar inVars body =>
    some (idxVar, inVars, body)
  | .dotProduct | .stencil1D3Pt _ _ _ => none

/-- Closed-form composition of two `.mapScaleAdd` kernels:
    `(x * s1 + b1) * s2 + b2 = x * (s1 * s2) + (b1 * s2 + b2)`. -/
def fuseMapScaleAddPair (s1 b1 s2 b2 : UInt64) : ParallelKernelKind :=
  .mapScaleAdd (s1 * s2) (b1 * s2 + b2)

/-- Replace every occurrence of `tmpVar` in consumer `(inputs2, inVars2, body2)` with the producer
    `inputs1` and inline `prodBody` for the corresponding consumer element variable. -/
def substConsumerInputs
    (tmpVar : VarId) (inputs1 : List VarId) (prodInVars : List VarId) (prodBody : ScalarExpr)
    (nextFresh : VarId) :
    List VarId → List VarId → ScalarExpr → Option (List VarId × List VarId × ScalarExpr)
  | [], [], body => some ([], [], body)
  | inBuf :: restInputs, iv :: restVars, body =>
    if inBuf == tmpVar then
      let freshVars := (List.range prodInVars.length).map (fun k => nextFresh + k)
      let renamedProd := (prodInVars.zip freshVars).foldl
        (fun acc (oldV, newV) => substScalarVar oldV (.var newV) acc) prodBody
      let body' := substScalarVar iv renamedProd body
      match substConsumerInputs tmpVar inputs1 prodInVars prodBody
          (nextFresh + prodInVars.length + 1) restInputs restVars body' with
      | some (rIns, rVars, rBody) =>
        some (inputs1 ++ rIns, freshVars ++ rVars, rBody)
      | none => none
    else
      match substConsumerInputs tmpVar inputs1 prodInVars prodBody nextFresh restInputs restVars body with
      | some (rIns, rVars, rBody) =>
        some (inBuf :: rIns, iv :: rVars, rBody)
      | none => none
  | _, _, _ => none

/-- Structural equality on `LNIRType` (total, reflexive on all scalar/array/pointer/unit types). -/
def sameElemType : LNIRType → LNIRType → Bool
  | .i1, .i1 | .i8, .i8 | .i16, .i16 | .i32, .i32 | .i64, .i64 | .usize, .usize
  | .u256, .u256 | .i256, .i256 | .f16, .f16 | .f32, .f32 | .f64, .f64
  | .objPtr, .objPtr | .taggedPtr, .taggedPtr | .storageMap, .storageMap | .unit, .unit => true
  | .sarray a, .sarray b | .rawPtr a, .rawPtr b => sameElemType a b
  | .tuple as, .tuple bs => as == bs
  | _, _ => false

/-- Structural scalar sort (`some true` = guaranteed `.u64`, `some false` = guaranteed `.bool`,
    `none` = untyped or 256-bit) over `.u64`-bound element variables `allowedU64Vars`.
    Defined by single-pass structural recursion (`0` `_unsafe_rec`). -/
def inferScalarSort? (allowedU64Vars : List VarId) : ScalarExpr → Option Bool
  | .constU64 _ => some true
  | .constBool _ => some false
  | .var id => if allowedU64Vars.contains id then some true else none
  | .fma a b c =>
    if inferScalarSort? allowedU64Vars a == some true &&
       inferScalarSort? allowedU64Vars b == some true &&
       inferScalarSort? allowedU64Vars c == some true then
      some true
    else none
  | .binOp op l r =>
    let sl := inferScalarSort? allowedU64Vars l
    let sr := inferScalarSort? allowedU64Vars r
    match op with
    | .eq =>
      if (sl == some true && sr == some true) || (sl == some false && sr == some false) then
        some false
      else none
    | .lt | .le =>
      if sl == some true && sr == some true then some false else none
    | .addChecked256 | .subChecked256 | .mulChecked256 => none
    | _ =>
      if sl == some true && sr == some true then some true else none
  | .unaryOp op a =>
    let sa := inferScalarSort? allowedU64Vars a
    match op with
    | .not => sa
    | .neg => if sa == some true then some true else none
    | .clz256 => none
  | .select c t f =>
    let sc := inferScalarSort? allowedU64Vars c
    let st := inferScalarSort? allowedU64Vars t
    let sf := inferScalarSort? allowedU64Vars f
    if sc.isSome && st.isSome && st == sf then st else none

/-- Coerce a producer `ScalarExpr` over `allowedU64Vars` to a `UInt64`-producing `ScalarExpr` matching
    `evalParKernelElem`'s output buffer write (`Eval.lean:489–490`), or return `none` if untyped/256-bit. -/
def coerceProducerScalarToU64? (allowedU64Vars : List VarId) (e : ScalarExpr) : Option ScalarExpr :=
  match inferScalarSort? allowedU64Vars e with
  | some true => some e
  | some false => some (.select e (.constU64 1) (.constU64 0))
  | none => none

/-- Strict verified two-stage `.mapScaleAdd` producer-consumer fusion across an `LNIRCode` block,
    restricted exclusively to the pattern proven by `LeanNative.Proofs.fuseParForKernels_sound`. -/
def fuseVerifiedMapScaleAddCode : LNIRCode → LNIRCode
  | .letBind dst ty val k => .letBind dst ty val (fuseVerifiedMapScaleAddCode k)
  | .rawStore p i x ety k => .rawStore p i x ety (fuseVerifiedMapScaleAddCode k)
  | .incRef o c k => .incRef o c (fuseVerifiedMapScaleAddCode k)
  | .decRef o c k => .decRef o c (fuseVerifiedMapScaleAddCode k)
  | .ite c t e => .ite c (fuseVerifiedMapScaleAddCode t) (fuseVerifiedMapScaleAddCode e)
  | .seqFor idx lo hi acc init accTy s k =>
    .seqFor idx lo hi acc init accTy (fuseVerifiedMapScaleAddCode s) (fuseVerifiedMapScaleAddCode k)
  | .parFor out1 len1 in1 ety1 k1 k =>
    match k1, in1, k with
    | .mapScaleAdd s1 b1, [srcBuf], .parFor out2 len2 [cBuf] ety2 (.mapScaleAdd s2 b2) (.ret retV) =>
      if out1 != out2 && out1 != len1 && srcBuf != out1 && cBuf == out1 &&
         len1 == len2 && sameElemType ety1 ety2 && retV == out2 then
        .parFor out2 len2 [srcBuf] ety2 (fuseMapScaleAddPair s1 b1 s2 b2) (.ret retV)
      else
        .parFor out1 len1 in1 ety1 k1 (fuseVerifiedMapScaleAddCode k)
    | _, _, _ => .parFor out1 len1 in1 ety1 k1 (fuseVerifiedMapScaleAddCode k)
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Fuse a producer `(inputs1, k1)` feeding `tmpVar` into consumer `(inputs2, k2)` over identical `lenVar`.
    Handles algebraic fast paths (`mapScaleAdd + mapScaleAdd`, `zipAdd/zipMul/saxpy + mapScaleAdd`)
    as well as general pointwise `.customScalar` producer-consumer pipelines. -/
def fuseTwoParForStage
    (tmpVar : VarId) (inputs1 : List VarId) (k1 : ParallelKernelKind)
    (inputs2 : List VarId) (k2 : ParallelKernelKind) :
    Option (List VarId × ParallelKernelKind) :=
  if !inputs2.contains tmpVar || inputs1.contains tmpVar then none
  else
    match k1, k2, inputs1, inputs2 with
    | .mapScaleAdd s1 b1, .mapScaleAdd s2 b2, [srcBuf], [cBuf] =>
      if cBuf == tmpVar then some ([srcBuf], fuseMapScaleAddPair s1 b1 s2 b2) else none
    | .saxpy a1, .mapScaleAdd s2 b2, [xBuf, yBuf], [cBuf] =>
      if cBuf == tmpVar && s2 == 1 && b2 == 0 then some ([xBuf, yBuf], .saxpy a1) else none
    | _, _, _, _ =>
      let b1 := match k1 with | .customScalar iv vs bd => Nat.max iv (Nat.max (vs.foldl Nat.max 0) (maxScalarVar bd)) | _ => 100
      let b2 := match k2 with | .customScalar iv vs bd => Nat.max iv (Nat.max (vs.foldl Nat.max 0) (maxScalarVar bd)) | _ => 200
      let base := Nat.max tmpVar (Nat.max (inputs1.foldl Nat.max 0) (Nat.max (inputs2.foldl Nat.max 0) (Nat.max b1 b2))) + 10
      match kernelToCustomScalar? base k1, kernelToCustomScalar? (base + 50) k2 with
      | some (idx1, pVars, pBody), some (idx2, cVars, cBody) =>
        if inputs1.length != pVars.length || inputs2.length != cVars.length then none
        else if pVars.eraseDups.length != pVars.length || pVars.contains idx1 then none
        else if cVars.eraseDups.length != cVars.length || cVars.contains idx2 then none
        else if scalarExprUsesVar tmpVar pBody || scalarExprUsesVar tmpVar cBody then none
        else
          match coerceProducerScalarToU64? (idx1 :: pVars) pBody with
          | none => none
          | some pBodyU64 =>
            let freshIdx := base + 99
            let pBodyFreshIdx := substScalarVar idx1 (.var freshIdx) pBodyU64
            let cBodyFreshIdx := substScalarVar idx2 (.var freshIdx) cBody
            match substConsumerInputs tmpVar inputs1 pVars pBodyFreshIdx (base + 100) inputs2 cVars cBodyFreshIdx with
            | some (fusedInputs, fusedVars, fusedBody) =>
              let simplified := contractKernelScalar fusedBody
              let kern := specializeKernel (.customScalar freshIdx fusedVars simplified)
              some (fusedInputs, kern)
            | none => none
      | _, _ => none

/-- Strip a single `.decRef tmpVar 1` from `code` if `tmpVar` is never referenced before that release,
    allowing producer-consumer fusion when explicit RC cleanup is present. -/
def stripDeadTmpDecRef (tmpVar : VarId) : LNIRCode → LNIRCode
  | .decRef v c k =>
    if v == tmpVar && c == 1 && !codeUsesVar tmpVar k then k
    else .decRef v c (stripDeadTmpDecRef tmpVar k)
  | .letBind dst ty val k =>
    if exprUsesVar tmpVar val || dst == tmpVar then .letBind dst ty val k
    else .letBind dst ty val (stripDeadTmpDecRef tmpVar k)
  | .incRef v c k =>
    if v == tmpVar then .incRef v c k
    else .incRef v c (stripDeadTmpDecRef tmpVar k)
  | .parFor out len ins ety kern k =>
    if out == tmpVar || len == tmpVar || ins.contains tmpVar || kernelUsesVar tmpVar kern then
      .parFor out len ins ety kern k
    else .parFor out len ins ety kern (stripDeadTmpDecRef tmpVar k)
  | other => other

/-- Bottom-up multi-stage producer-consumer `parFor` fusion across an `LNIRCode` block.
    Because `rest` is fused first, 3-stage and N-stage pipelines fuse into a single `parFor` pass! -/
def fuseParForCode : LNIRCode → LNIRCode
  | .letBind dst ty val k => .letBind dst ty val (fuseParForCode k)
  | .rawStore p i x ety k => .rawStore p i x ety (fuseParForCode k)
  | .incRef o c k => .incRef o c (fuseParForCode k)
  | .decRef o c k => .decRef o c (fuseParForCode k)
  | .ite c t e => .ite c (fuseParForCode t) (fuseParForCode e)
  | .seqFor idx lo hi acc init accTy s k =>
    .seqFor idx lo hi acc init accTy (fuseParForCode s) (fuseParForCode k)
  | .parFor out1 len1 in1 ety1 k1 k =>
    let k1' := specializeKernel k1
    let k' := fuseParForCode k
    match k' with
    | .parFor out2 len2 in2 ety2 k2 rest =>
      let restCleaned := stripDeadTmpDecRef out1 rest
      if out1 != out2 && len1 == len2 && sameElemType ety1 ety2 && !codeUsesVar out1 restCleaned then
        match fuseTwoParForStage out1 in1 k1' in2 k2 with
        | some (fusedIns, fusedKern) =>
          .parFor out2 len2 fusedIns ety2 fusedKern restCleaned
        | none => .parFor out1 len1 in1 ety1 k1' k'
      else
        .parFor out1 len1 in1 ety1 k1' k'
    | _ => .parFor out1 len1 in1 ety1 k1' k'
  | .ret v => .ret v
  | .unreachable => .unreachable

/-- Count the number of `.parFor` kernel launches in `LNIRCode`. -/
def countParForLaunches : LNIRCode → Nat
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k =>
    countParForLaunches k
  | .ite _ t e => countParForLaunches t + countParForLaunches e
  | .seqFor _ _ _ _ _ _ s k => countParForLaunches s + countParForLaunches k
  | .parFor _ _ _ _ _ k => 1 + countParForLaunches k
  | .ret _ | .unreachable => 0

/-- Full multi-stage `parFor` fusion on an `LNIRDecl`. -/
def fuseParForDecl (d : LNIRDecl) : LNIRDecl :=
  { d with body := fuseParForCode d.body }

/-- Multi-stage producer-consumer `parFor` loop fusion pass (`fuseParForCode`).
    Follows the P0 Provenance Contract (`Contract V2`):
    - No-op (`d'.body == d.body`) stamps `.verifiedKernelProof` via `CodeRefines.refl`.
    - Exact 2-stage `.mapScaleAdd` pipelines matching `fuseVerifiedMapScaleAddCode` carry the
      observational buffer-data theorem `LeanNative.Proofs.fuseParForKernels_sound` (`stTgt.nextId + 1 = stSrc.nextId`,
      so `AssuranceLevel.tested` rather than `CodeRefines` `VerifiedKernelProof`).
    - Extended multi-stage / `.customScalar` / RC-cleanup rewrites stamp `AssuranceLevel.tested`
      (`KernelFusion.multi_stage_tested`) and never claim `.verifiedKernelProof`. -/
def kernelFusionPass : TransformPass where
  name := "KernelFusion"
  assurance := .tested
  theoremRef := "LeanNative.Proofs.fuseParForKernels_sound"
  runDecl := fun d =>
    let inHash := d.structuralHash
    let d' := fuseParForDecl d
    let changed := d'.body != d.body
    let isVerified2Stage := changed && d'.body == fuseVerifiedMapScaleAddCode d.body
    let stepAssurance : AssuranceLevel := if !changed then .verifiedKernelProof else .tested
    let comb := AssuranceLevel.combine d.assurance stepAssurance
    let dOut : LNIRDecl := { d' with assurance := comb }
    let outHash := dOut.structuralHash
    let thmRef :=
      if !changed then "LeanNative.Semantics.CodeRefines.refl"
      else if isVerified2Stage then "LeanNative.Proofs.fuseParForKernels_sound"
      else "KernelFusion.multi_stage_tested"
    (dOut, {
      passName := "KernelFusion"
      declName := d.name
      inputHash := inHash
      outputHash := outHash
      changed := changed
      assurance := comb
      theoremRef := thmRef
      notes := if changed then
        s!"Fused parFor launches ({countParForLaunches d.body} -> {countParForLaunches d'.body}; assurance={comb})"
      else "No fusible adjacent parFor stages"
    })

end LeanNative.Transform
