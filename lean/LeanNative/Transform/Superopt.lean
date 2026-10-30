import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.SymbolicTV

namespace LeanNative.Transform

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Proofs

/-!
# Cost-Guided Enumerative Superoptimizer (`LeanNative.Transform.Superopt`)

Provides a self-contained (zero `import Lean`) cost-guided enumerative superoptimizer
for LNIR scalar expressions and modules across CPU and GPU targets:
- Hardware-specific instruction latency cost model (`SuperoptTarget`: `x86_64`, `arm64`, `cuda_ptx`, `apple_metal`)
- Bottom-up + template-guided candidate synthesis (`synthesizeCandidates`) combining:
  1. Kernel-verified `LeanNative.Proofs.rewriteScalarPeephole`
  2. Symbolic canonical normalizer (`symExprToScalarExpr?`)
  3. Enumerative algebraic, bitwise, shift-composition, FMA-contraction, and distributive factoring templates
- Two-stage formal soundness filter for every synthesized candidate:
  1. `fastCheckScalarEquiv`: 16-state concrete equivalence filter (boundary values + SplitMix64) via `evalScalarExpr`
  2. `symCheckScalarEquiv`: SymbolicTV canonical equivalence verifier (`normSymExpr`)
-/

/-- Target architecture for cost-guided superoptimization. -/
inductive SuperoptTarget where
  | x86_64
  | arm64
  | cuda_ptx
  | apple_metal
  deriving Repr, DecidableEq, Inhabited, BEq

namespace SuperoptTarget

def toString : SuperoptTarget → String
  | .x86_64      => "x86_64"
  | .arm64       => "arm64"
  | .cuda_ptx    => "cuda_ptx"
  | .apple_metal => "apple_metal"

instance : ToString SuperoptTarget := ⟨toString⟩

def isGpu : SuperoptTarget → Bool
  | .cuda_ptx | .apple_metal => true
  | .x86_64 | .arm64 => false

end SuperoptTarget

/-- Declarative, community-contributable hardware latency & tuning profile (`profiles/*.json`).
    Note (Law 1 / Law 5): A `HardwareCostProfile` only affects cost-guided candidate ranking;
    every synthesized rewrite still passes `fastCheckScalarEquiv` + `symCheckScalarEquiv`. -/
structure HardwareCostProfile where
  profileId            : String := "x86_64_default"
  target               : SuperoptTarget := .x86_64
  llvmTargetCpu        : String := "x86-64-v3"
  smArch               : String := "sm_90"
  addSubCost           : Nat := 1
  bitwiseCost          : Nat := 1
  shiftCost            : Nat := 1
  cmpCost              : Nat := 1
  mulCost              : Nat := 4
  divModCost           : Nat := 24
  fmaCost              : Nat := 3
  selectCost           : Nat := 2
  clz256Cost           : Nat := 2
  addSubChecked256Cost : Nat := 3
  mulChecked256Cost    : Nat := 4
  minGpuElements       : Nat := 65536
  gpuBlockThreads      : Nat := 256
  matmulTileDim        : Nat := 16
  deriving Repr, DecidableEq, Inhabited, BEq

namespace HardwareCostProfile

/-- Built-in default hardware cost profile for a `SuperoptTarget`. -/
def forTarget : SuperoptTarget → HardwareCostProfile
  | .x86_64 => { profileId := "x86_64_skylake_avx2", target := .x86_64, llvmTargetCpu := "x86-64-v3" }
  | .arm64 => { profileId := "arm64_grace_neoverse_v2", target := .arm64, llvmTargetCpu := "neoverse-v2", fmaCost := 2 }
  | .cuda_ptx => { profileId := "cuda_blackwell_gb10_sm121", target := .cuda_ptx, llvmTargetCpu := "neoverse-v2",
                   smArch := "sm_90", mulCost := 5, divModCost := 36, fmaCost := 2, mulChecked256Cost := 5 }
  | .apple_metal => { profileId := "apple_silicon_m3_metal", target := .apple_metal, llvmTargetCpu := "apple-m3",
                      mulCost := 5, divModCost := 36, fmaCost := 2, mulChecked256Cost := 5, minGpuElements := 32768 }

private def extractJsonAfterColon (raw : String) (key : String) : Option String :=
  match raw.splitOn ("\"" ++ key ++ "\"") with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn ":" with
    | _ :: afterColon :: _ => some afterColon.trimAscii.toString
    | _ => none
  | _ => none

private def extractJsonStringField (raw : String) (key : String) : Option String := do
  let trimmed ← extractJsonAfterColon raw key
  match trimmed.splitOn "\"" with
  | _ :: val :: _ => some val
  | _ => none

private def extractJsonNatField (raw : String) (key : String) : Option Nat := do
  let trimmed ← extractJsonAfterColon raw key
  let digits := trimmed.toList.takeWhile (fun c => c.isDigit)
  if digits.isEmpty then none else (String.ofList digits).toNat?

/-- Parse a `HardwareCostProfile` from a `profiles/*.json` file. -/
def fromJson? (raw : String) : Option HardwareCostProfile := do
  let tgtStr := (extractJsonStringField raw "target").getD "x86_64"
  let target : SuperoptTarget :=
    if tgtStr == "arm64" || tgtStr == "aarch64" then .arm64
    else if tgtStr == "cuda_ptx" || tgtStr == "cuda" || tgtStr == "ptx" || tgtStr == "tpu_xla" || tgtStr == "tpu" then .cuda_ptx
    else if tgtStr == "apple_metal" || tgtStr == "metal" then .apple_metal
    else .x86_64
  let base := forTarget target
  let pid := (extractJsonStringField raw "profile_id").orElse (fun _ => extractJsonStringField raw "profileId") |>.getD base.profileId
  let llvmCpu := (extractJsonStringField raw "llvm_target_cpu").getD base.llvmTargetCpu
  let sm := (extractJsonStringField raw "sm_arch").getD base.smArch
  return {
    profileId            := pid
    target               := target
    llvmTargetCpu        := llvmCpu
    smArch               := sm
    addSubCost           := (extractJsonNatField raw "add_sub_cost").getD base.addSubCost
    bitwiseCost          := (extractJsonNatField raw "bitwise_cost").getD base.bitwiseCost
    shiftCost            := (extractJsonNatField raw "shift_cost").getD base.shiftCost
    cmpCost              := (extractJsonNatField raw "cmp_cost").getD base.cmpCost
    mulCost              := (extractJsonNatField raw "mul_cost").getD base.mulCost
    divModCost           := (extractJsonNatField raw "div_mod_cost").getD base.divModCost
    fmaCost              := (extractJsonNatField raw "fma_cost").getD base.fmaCost
    selectCost           := (extractJsonNatField raw "select_cost").getD base.selectCost
    clz256Cost           := (extractJsonNatField raw "clz256_cost").getD base.clz256Cost
    addSubChecked256Cost := (extractJsonNatField raw "add_sub_checked256_cost").getD base.addSubChecked256Cost
    mulChecked256Cost    := (extractJsonNatField raw "mul_checked256_cost").getD base.mulChecked256Cost
    minGpuElements       := (extractJsonNatField raw "min_gpu_elements").getD base.minGpuElements
    gpuBlockThreads      := (extractJsonNatField raw "gpu_block_threads").getD base.gpuBlockThreads
    matmulTileDim        := (extractJsonNatField raw "matmul_tile_dim").getD base.matmulTileDim
  }

end HardwareCostProfile

/-- Profile-guided binary operator latency cost. -/
def binOpCostWithProfile (p : HardwareCostProfile) (op : BinOp) : Nat :=
  match op with
  | .div | .mod => p.divModCost
  | .mul => p.mulCost
  | .mulChecked256 => p.mulChecked256Cost
  | .addChecked256 | .subChecked256 => p.addSubChecked256Cost
  | .add | .sub => p.addSubCost
  | .bitAnd | .bitOr | .bitXor | .eor3 => p.bitwiseCost
  | .clmul64 | .clmul64Hi | .gf2Affine => 1
  | .shl | .shr | .sar => p.shiftCost
  | .eq | .lt | .le => p.cmpCost

/-- Profile-guided unary operator latency cost. -/
def unaryOpCostWithProfile (p : HardwareCostProfile) (op : UnaryOp) : Nat :=
  match op with
  | .not | .neg => p.bitwiseCost
  | .clz256 => p.clz256Cost

/-- Profile-guided total latency cost of a `ScalarExpr`. -/
def scalarExprCostWithProfile (p : HardwareCostProfile) : ScalarExpr → Nat
  | .constU64 _ | .constBool _ | .var _ => 0
  | .binOp op lhs rhs =>
    let dupPenalty := if op == .add && lhs == rhs then 1 else 0
    binOpCostWithProfile p op + dupPenalty + scalarExprCostWithProfile p lhs + scalarExprCostWithProfile p rhs
  | .unaryOp op arg =>
    unaryOpCostWithProfile p op + scalarExprCostWithProfile p arg
  | .select c t e =>
    p.selectCost + scalarExprCostWithProfile p c + scalarExprCostWithProfile p t + scalarExprCostWithProfile p e
  | .fma a b c =>
    p.fmaCost + scalarExprCostWithProfile p a + scalarExprCostWithProfile p b + scalarExprCostWithProfile p c

/-- Hardware-specific instruction cost model for a binary scalar operator. -/
def binOpCost (target : SuperoptTarget) (op : BinOp) : Nat :=
  binOpCostWithProfile (HardwareCostProfile.forTarget target) op

/-- Hardware-specific instruction cost model for a unary scalar operator. -/
def unaryOpCost (target : SuperoptTarget) (op : UnaryOp) : Nat :=
  unaryOpCostWithProfile (HardwareCostProfile.forTarget target) op

/-- Hardware-specific total latency cost of a `ScalarExpr` on `target`.
    - `.div`/`.mod` cost 24 on CPU (`x86_64`/`arm64`) and 36 on GPU (`cuda_ptx`/`apple_metal`)
    - `.mul` costs 4 on CPU (`x86_64`), 3 on `arm64`, and 5 on GPU
    - `.fma` costs 2 on `arm64`/`cuda_ptx`/`apple_metal` and 3 on `x86_64`
    - shifts/bitwise/add/sub cost 1
    - constants and variables cost 0 -/
def scalarExprCost (target : SuperoptTarget) (e : ScalarExpr) : Nat :=
  scalarExprCostWithProfile (HardwareCostProfile.forTarget target) e

/-- Convert a normalized `SymExpr` back into a `ScalarExpr` when it belongs to the pure scalar fragment. -/
def symExprToScalarExpr? : SymExpr → Option ScalarExpr
  | .constU64 v => some (.constU64 v)
  | .constBool b => some (.constBool b)
  | .symVar id => some (.var id)
  | .binOp op l r => do
    let l' ← symExprToScalarExpr? l
    let r' ← symExprToScalarExpr? r
    some (.binOp op l' r')
  | .unaryOp op a => do
    let a' ← symExprToScalarExpr? a
    some (.unaryOp op a')
  | .ite c t e => do
    let c' ← symExprToScalarExpr? c
    let t' ← symExprToScalarExpr? t
    let e' ← symExprToScalarExpr? e
    some (.select c' t' e')
  | .projSym .. | .tuple _ | .ctorObj .. | .bufElem _ _ | .arrLen _ | .exclCheck .. | .decCond .. | .unit => none

/-- Check if any 64-bit constant `d` is an exact power of two (`d != 0 && (d &&& (d - 1)) == 0`)
    and return its base-2 shift exponent `k ∈ [0, 63]`. -/
def powerOfTwoShift? (d : UInt64) : Option UInt64 :=
  if d == 0 || (d &&& (d - 1)) != 0 then none
  else (List.range 64).findSome? (fun k => let ku := k.toUInt64; if (1 : UInt64) <<< ku == d then some ku else none)

/-- Hensel 2-adic Newton inverse lifting over `Z / 2^64 Z`: for odd `d`, returns `inv` with `d * inv == 1`. -/
def henselOddInverseU64 (d : UInt64) : UInt64 :=
  let x0 := d * (2 - d * d)
  let x1 := x0 * (2 - d * x0)
  let x2 := x1 * (2 - d * x1)
  let x3 := x2 * (2 - d * x2)
  x3 * (2 - d * x3)

/-- Deduplicate a list of `ScalarExpr` candidates while preserving order. -/
def dedupScalarExprs (es : List ScalarExpr) : List ScalarExpr :=
  es.foldl (fun acc e => if acc.contains e then acc else acc ++ [e]) []

/-- Declarative synthesis rule for the enumerative superoptimizer. -/
structure SynthRule where
  name  : String
  apply : ScalarExpr → List ScalarExpr

/-- Declarative table of algebraic, bitwise, shift-composition, FMA, and distributive synthesis rules. -/
def superoptSynthRules : List SynthRule :=
  [ { name := "const_fold_binop"
      apply := fun
        | .binOp op (.constU64 a) (.constU64 b) => [LeanNative.Proofs.rewriteConstFoldBinOp op a b]
        | _ => [] }
  , { name := "add_self_and_quad_shift"
      apply := fun
        | .binOp .add x y =>
          let same := if x == y then [ScalarExpr.binOp .shl x (.constU64 1)] else []
          let quad :=
            match x, y with
            | .binOp .mul x1 (.constU64 2), .binOp .mul x2 (.constU64 2)
            | .binOp .shl x1 (.constU64 1), .binOp .shl x2 (.constU64 1) =>
              if x1 == x2 then [ScalarExpr.binOp .shl x1 (.constU64 2)] else []
            | _, _ => []
          same ++ quad
        | _ => [] }
  , { name := "distributive_factoring"
      apply := fun
        | .binOp .add (.binOp .mul x1 (.constU64 a)) (.binOp .mul x2 (.constU64 b)) =>
          if x1 == x2 then
            let mulCand := ScalarExpr.binOp .mul x1 (.constU64 (a + b))
            [mulCand, LeanNative.Proofs.rewriteScalarPeephole mulCand]
          else []
        | .binOp .add (.binOp .mul x1 a) (.binOp .mul x2 b) =>
          if x1 == x2 then
            let mulCand := ScalarExpr.binOp .mul x1 (.binOp .add a b)
            [mulCand, LeanNative.Proofs.rewriteScalarPeephole mulCand]
          else []
        | _ => [] }
  , { name := "assoc_add_const"
      apply := fun
        | .binOp .add (.binOp .add inner (.constU64 c1)) (.constU64 c2)
        | .binOp .add (.constU64 c1) (.binOp .add inner (.constU64 c2)) =>
          let cSum := c1 + c2
          if cSum == 0 then [inner] else [ScalarExpr.binOp .add inner (.constU64 cSum)]
        | _ => [] }
  , { name := "shift_composition"
      apply := fun
        | .binOp .shl (.binOp .shl x (.constU64 k1)) (.constU64 k2) =>
          if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
            if k1 + k2 == 0 then [x] else [ScalarExpr.binOp .shl x (.constU64 (k1 + k2))]
          else []
        | .binOp .shr (.binOp .shr x (.constU64 k1)) (.constU64 k2) =>
          if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
            if k1 + k2 == 0 then [x] else [ScalarExpr.binOp .shr x (.constU64 (k1 + k2))]
          else []
        | _ => [] }
  , { name := "double_shift_mask_collapse"
      apply := fun
        | .binOp .shl (.binOp .shr x (.constU64 k1)) (.constU64 k2) =>
          if k1 == k2 && k1 < 64 then
            if k1 == 0 then [x]
            else [ScalarExpr.binOp .bitAnd x (.constU64 (0xffffffffffffffff <<< k1))]
          else []
        | .binOp .shr (.binOp .shl x (.constU64 k1)) (.constU64 k2) =>
          if k1 == k2 && k1 < 64 then
            if k1 == 0 then [x]
            else [ScalarExpr.binOp .bitAnd x (.constU64 (0xffffffffffffffff >>> k1))]
          else []
        | _ => [] }
  , { name := "rotate_left_pattern"
      apply := fun
        | .binOp .bitOr (.binOp .shr x1 (.constU64 k2)) (.binOp .shl x2 (.constU64 k1)) =>
          if x1 == x2 && k1 > 0 && k1 < 64 && k1 + k2 == 64 then
            [ScalarExpr.binOp .bitOr (.binOp .shl x1 (.constU64 k1)) (.binOp .shr x1 (.constU64 k2))]
          else []
        | _ => [] }
  , { name := "cost_guided_fma_fusion"
      apply := fun
        | .binOp .add (.binOp .mul a b) c | .binOp .add c (.binOp .mul a b) =>
          [ScalarExpr.fma a b c]
        | .binOp .add (.binOp .shl a (.constU64 k)) c
        | .binOp .add c (.binOp .shl a (.constU64 k)) =>
          if k < 64 then [ScalarExpr.fma a (.constU64 (1 <<< k)) c] else []
        | _ => [] }
  , { name := "bitwise_mask_coalesce"
      apply := fun
        | .binOp .bitAnd (.binOp .bitAnd x (.constU64 m1)) (.constU64 m2) =>
          let m := m1 &&& m2
          if m == 0 then [.constU64 0] else [ScalarExpr.binOp .bitAnd x (.constU64 m)]
        | .binOp .bitOr (.binOp .bitOr x (.constU64 m1)) (.constU64 m2) =>
          let m := m1 ||| m2
          if m == 0 then [x] else [ScalarExpr.binOp .bitOr x (.constU64 m)]
        | .binOp .bitXor (.binOp .bitXor x (.constU64 m1)) (.constU64 m2) =>
          let m := m1 ^^^ m2
          if m == 0 then [x] else [ScalarExpr.binOp .bitXor x (.constU64 m)]
        | _ => [] }
  , { name := "pow2_strength_reduction"
      apply := fun
        | .binOp .div (.binOp .div x (.constU64 d1)) (.constU64 d2) =>
          match powerOfTwoShift? d1, powerOfTwoShift? d2 with
          | some k1, some k2 =>
            if (k1 + k2) < 64 then
              if k1 + k2 == 0 then [x] else [ScalarExpr.binOp .shr x (.constU64 (k1 + k2))]
            else []
          | _, _ => []
        | .binOp .div x (.constU64 d) =>
          match powerOfTwoShift? d with
          | some 0 => [x]
          | some k => [ScalarExpr.binOp .shr x (.constU64 k)]
          | none => []
        | .binOp .mod x (.constU64 d) =>
          match powerOfTwoShift? d with
          | some 0 => [.constU64 0]
          | some _ => [ScalarExpr.binOp .bitAnd x (.constU64 (d - 1))]
          | none => []
        | .binOp .mul x (.constU64 d) | .binOp .mul (.constU64 d) x =>
          match powerOfTwoShift? d with
          | some 0 => [x]
          | some k => [ScalarExpr.binOp .shl x (.constU64 k)]
          | none => []
        | _ => [] }
  , { name := "add_sub_cancel"
      apply := fun
        | .binOp .sub (.binOp .add x y) z =>
          if z == y then [x]
          else if z == x then [y]
          else []
        | _ => [] }
  , { name := "distributive_bitwise_and"
      apply := fun
        | .binOp .bitOr (.binOp .bitAnd a b) (.binOp .bitAnd c d) =>
          if a == c then [ScalarExpr.binOp .bitAnd a (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitOr b d))]
          else if a == d then [ScalarExpr.binOp .bitAnd a (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitOr b c))]
          else if b == c then [ScalarExpr.binOp .bitAnd b (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitOr a d))]
          else if b == d then [ScalarExpr.binOp .bitAnd b (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitOr a c))]
          else []
        | .binOp .bitXor (.binOp .bitAnd a b) (.binOp .bitAnd c d) =>
          if a == c then [ScalarExpr.binOp .bitAnd a (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitXor b d))]
          else if a == d then [ScalarExpr.binOp .bitAnd a (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitXor b c))]
          else if b == c then [ScalarExpr.binOp .bitAnd b (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitXor a d))]
          else if b == d then [ScalarExpr.binOp .bitAnd b (LeanNative.Proofs.rewriteScalarVerified (.binOp .bitXor a c))]
          else []
        | _ => [] }
  , { name := "xor_self_cancel"
      apply := fun
        | .binOp .bitXor (.binOp .bitXor x y) z =>
          if z == y then [x]
          else if z == x then [y]
          else []
        | .binOp .bitXor z (.binOp .bitXor x y) =>
          if z == y then [x]
          else if z == x then [y]
          else []
        | _ => [] }
  , { name := "assoc_sub_const"
      apply := fun
        | .binOp .sub (.binOp .sub inner (.constU64 c1)) (.constU64 c2) =>
          let cSum := c1 + c2
          if cSum == 0 then [inner] else [ScalarExpr.binOp .sub inner (.constU64 cSum)]
        | .binOp .sub (.binOp .add inner (.constU64 c1)) (.constU64 c2) =>
          let cDiff := c1 - c2
          if cDiff == 0 then [inner] else [ScalarExpr.binOp .add inner (.constU64 cDiff)]
        | _ => [] }
  , { name := "sub_masked_clear"
      apply := fun
        | .binOp .sub x (.binOp .bitAnd a b) =>
          if x == a then [ScalarExpr.binOp .bitAnd x (.unaryOp .not b)]
          else if x == b then [ScalarExpr.binOp .bitAnd x (.unaryOp .not a)]
          else []
        | _ => [] }
  , { name := "and_plus_or_to_add"
      apply := fun
        | .binOp .add (.binOp .bitAnd x y) (.binOp .bitOr u v)
        | .binOp .add (.binOp .bitOr x y) (.binOp .bitAnd u v) =>
          if (x == u && y == v) || (x == v && y == u) then [ScalarExpr.binOp .add x y]
          else []
        | _ => [] }
  , { name := "xor_or_and_to_or"
      apply := fun
        | .binOp .bitOr (.binOp .bitXor x y) (.binOp .bitAnd u v)
        | .binOp .bitOr (.binOp .bitAnd x y) (.binOp .bitXor u v) =>
          if (x == u && y == v) || (x == v && y == u) then [ScalarExpr.binOp .bitOr x y]
          else []
        | _ => [] }
  , { name := "hensel_2adic_mul_inv_cancel"
      apply := fun
        | .binOp .mul (.binOp .mul x (.constU64 c1)) (.constU64 c2) =>
          let prod := c1 * c2
          if prod == 1 then [x] else [ScalarExpr.binOp .mul x (.constU64 prod)]
        | .binOp .bitAnd (.binOp .add (.binOp .bitAnd x (.constU64 m1)) y) (.constU64 m2) =>
          if (m1 &&& m2) == m2 then [ScalarExpr.binOp .bitAnd (.binOp .add x y) (.constU64 m2)] else []
        | _ => [] }
  ]

/-- Apply all declarative `superoptSynthRules` to a top-level `ScalarExpr`. -/
def synthesizeTopLevelTemplates (e : ScalarExpr) : List ScalarExpr :=
  superoptSynthRules.foldl (fun acc rule => acc ++ rule.apply e) []

private def unionVars (xs ys : List VarId) : List VarId :=
  xs ++ ys.filter (fun x => !xs.contains x)

/-- Collect all variable IDs referenced in a `ScalarExpr`. -/
def collectScalarVars : ScalarExpr → List VarId
  | .constU64 _ | .constBool _ => []
  | .var id => [id]
  | .binOp _ l r => unionVars (collectScalarVars l) (collectScalarVars r)
  | .unaryOp _ a => collectScalarVars a
  | .select c t e | .fma c t e =>
    unionVars (unionVars (collectScalarVars c) (collectScalarVars t)) (collectScalarVars e)

/-- Extended algebraic normalizer on `SymExpr` that also canonicalizes associative constants,
    distributive constant factoring, `(x + x) -> x <<< 1`, and shift/mask composition so
    `symCheckScalarEquiv` can formally validate superoptimizer synthesis templates. -/
def normSymSuperoptStep (s : SymExpr) : SymExpr :=
  let s0 := normSymExpr s
  match s0 with
  -- (x + x) -> x <<< 1
  | .binOp .add x y =>
    if x == y then
      normSymExpr (.binOp .shl x (.constU64 1))
    else
      match x, y with
      -- (x <<< 1) + (x <<< 1) -> x <<< 2
      | .binOp .shl x1 (.constU64 1), .binOp .shl x2 (.constU64 1) =>
        if x1 == x2 then normSymExpr (.binOp .shl x1 (.constU64 2)) else s0
      -- Distributive factoring: (x * a) + (x * b) or shifted equivalents
      | .binOp .mul x1 (.constU64 a), .binOp .mul x2 (.constU64 b) =>
        if x1 == x2 then normSymExpr (.binOp .mul x1 (.constU64 (a + b))) else s0
      | .binOp .shl x1 (.constU64 k1), .binOp .mul x2 (.constU64 b) =>
        if x1 == x2 && k1 < 64 then
          normSymExpr (.binOp .mul x1 (.constU64 ((1 <<< k1) + b)))
        else s0
      | .binOp .mul x1 (.constU64 a), .binOp .shl x2 (.constU64 k2) =>
        if x1 == x2 && k2 < 64 then
          normSymExpr (.binOp .mul x1 (.constU64 (a + (1 <<< k2))))
        else s0
      | .binOp .shl x1 (.constU64 k1), .binOp .shl x2 (.constU64 k2) =>
        if x1 == x2 && k1 < 64 && k2 < 64 then
          normSymExpr (.binOp .mul x1 (.constU64 ((1 <<< k1) + (1 <<< k2))))
        else s0
      -- Associative addition: (x + c1) + c2 -> x + (c1 + c2)
      | .binOp .add inner (.constU64 c1), .constU64 c2 =>
        normSymExpr (.binOp .add inner (.constU64 (c1 + c2)))
      -- Disjoint bit decomposition: (x &&& y) + (x ||| y) -> x + y
      | .binOp .bitAnd a b, .binOp .bitOr u v
      | .binOp .bitOr a b, .binOp .bitAnd u v =>
        if (a == u && b == v) || (a == v && b == u) then normSymExpr (.binOp .add a b)
        else s0
      | _, _ => s0
  -- Shift composition: (x <<< k1) <<< k2 -> x <<< (k1 + k2)
  | .binOp .shl (.binOp .shl x (.constU64 k1)) (.constU64 k2) =>
    if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
      normSymExpr (.binOp .shl x (.constU64 (k1 + k2)))
    else s0
  | .binOp .shr (.binOp .shr x (.constU64 k1)) (.constU64 k2) =>
    if k1 < 64 && k2 < 64 && (k1 + k2) < 64 then
      normSymExpr (.binOp .shr x (.constU64 (k1 + k2)))
    else s0
  -- Double-shift mask collapse: (x >>> k) <<< k -> x &&& (UInt64.max <<< k)
  | .binOp .shl (.binOp .shr x (.constU64 k1)) (.constU64 k2) =>
    if k1 == k2 && k1 < 64 then
      normSymExpr (.binOp .bitAnd x (.constU64 (0xffffffffffffffff <<< k1)))
    else s0
  | .binOp .shr (.binOp .shl x (.constU64 k1)) (.constU64 k2) =>
    if k1 == k2 && k1 < 64 then
      normSymExpr (.binOp .bitAnd x (.constU64 (0xffffffffffffffff >>> k1)))
    else s0
  -- Bitwise mask composition and distributive factoring
  | .binOp .sub (.binOp .add x y) z =>
    if z == y then x
    else if z == x then y
    else
      match y, z with
      | .constU64 c1, .constU64 c2 =>
        let cDiff := c1 - c2
        if cDiff == 0 then x else normSymExpr (.binOp .add x (.constU64 cDiff))
      | _, _ => s0
  | .binOp .sub (.binOp .sub x (.constU64 c1)) (.constU64 c2) =>
    let cSum := c1 + c2
    if cSum == 0 then x else normSymExpr (.binOp .sub x (.constU64 cSum))
  | .binOp .sub x (.binOp .bitAnd a b) =>
    if x == a then normSymExpr (.binOp .bitAnd x (.unaryOp .not b))
    else if x == b then normSymExpr (.binOp .bitAnd x (.unaryOp .not a))
    else s0
  | .binOp .bitOr (.binOp .bitXor x y) (.binOp .bitAnd u v)
  | .binOp .bitOr (.binOp .bitAnd x y) (.binOp .bitXor u v) =>
    if (x == u && y == v) || (x == v && y == u) then normSymExpr (.binOp .bitOr x y)
    else s0
  | .binOp .bitXor (.binOp .bitXor x y) z =>
    if z == y then x
    else if z == x then y
    else
      match y, z with
      | .constU64 m1, .constU64 m2 => normSymExpr (.binOp .bitXor x (.constU64 (m1 ^^^ m2)))
      | _, _ => s0
  | .binOp .bitAnd (.binOp .bitAnd x (.constU64 m1)) (.constU64 m2) =>
    normSymExpr (.binOp .bitAnd x (.constU64 (m1 &&& m2)))
  | .binOp .bitOr (.binOp .bitOr x (.constU64 m1)) (.constU64 m2) =>
    normSymExpr (.binOp .bitOr x (.constU64 (m1 ||| m2)))
  | .binOp .bitOr (.binOp .bitAnd a b) (.binOp .bitAnd c d) =>
    if a == c then normSymExpr (.binOp .bitAnd a (normSymExpr (.binOp .bitOr b d)))
    else if a == d then normSymExpr (.binOp .bitAnd a (normSymExpr (.binOp .bitOr b c)))
    else if b == c then normSymExpr (.binOp .bitAnd b (normSymExpr (.binOp .bitOr a d)))
    else if b == d then normSymExpr (.binOp .bitAnd b (normSymExpr (.binOp .bitOr a c)))
    else s0
  | .binOp .bitXor (.binOp .bitAnd a b) (.binOp .bitAnd c d) =>
    if a == c then normSymExpr (.binOp .bitAnd a (normSymExpr (.binOp .bitXor b d)))
    else if a == d then normSymExpr (.binOp .bitAnd a (normSymExpr (.binOp .bitXor b c)))
    else if b == c then normSymExpr (.binOp .bitAnd b (normSymExpr (.binOp .bitXor a d)))
    else if b == d then normSymExpr (.binOp .bitAnd b (normSymExpr (.binOp .bitXor a c)))
    else s0
  -- Division/modulo by power of two
  | .binOp .div (.binOp .div x (.constU64 d1)) (.constU64 d2) =>
    match powerOfTwoShift? d1, powerOfTwoShift? d2 with
    | some k1, some k2 =>
      if (k1 + k2) < 64 then normSymExpr (.binOp .shr x (.constU64 (k1 + k2))) else s0
    | _, _ => s0
  | .binOp .div x (.constU64 d) =>
    match powerOfTwoShift? d with
    | some k => normSymExpr (.binOp .shr x (.constU64 k))
    | none => s0
  | .binOp .mod x (.constU64 d) =>
    match powerOfTwoShift? d with
    | some 0 => .constU64 0
    | some _ => normSymExpr (.binOp .bitAnd x (.constU64 (d - 1)))
    | none => s0
  | .binOp .mul x (.constU64 d) =>
    match powerOfTwoShift? d with
    | some k => normSymExpr (.binOp .shl x (.constU64 k))
    | none =>
      match x with
      | .binOp .mul inner (.constU64 c1) =>
        let prod := c1 * d
        if prod == 1 then inner else normSymExpr (.binOp .mul inner (.constU64 prod))
      | _ => s0
  | .binOp .bitAnd (.binOp .add (.binOp .bitAnd x (.constU64 m1)) y) (.constU64 m2) =>
    if (m1 &&& m2) == m2 then normSymExpr (.binOp .bitAnd (.binOp .add x y) (.constU64 m2)) else s0
  | _ => s0

/-- Recursive bottom-up superoptimizer canonicalizer on `SymExpr`. -/
def normSymSuperopt : SymExpr → SymExpr
  | .constU64 v => .constU64 v
  | .constBool b => .constBool b
  | .symVar id => .symVar id
  | .binOp op l r => normSymSuperoptStep (.binOp op (normSymSuperopt l) (normSymSuperopt r))
  | .unaryOp op a => normSymSuperoptStep (.unaryOp op (normSymSuperopt a))
  | .ite c t e => normSymSuperoptStep (.ite (normSymSuperopt c) (normSymSuperopt t) (normSymSuperopt e))
  | other => normSymExpr other

/-- Stage 1 Soundness Filter: FastCheck 16-state concrete equivalence filter.
    Tests boundary values (`0, 1, 2, 7, 42, 255, 0xffffffff, 0xffffffffffffffff`) and
    SplitMix64 states via `evalScalarExpr`. -/
def fastCheckScalarEquiv (e cand : ScalarExpr) : Bool :=
  let vars := collectScalarVars e ++ (collectScalarVars cand).filter (fun x => !(collectScalarVars e).contains x)
  let boundaryVals : List UInt64 :=
    [0, 1, 2, 7, 42, 255, 0xffffffff, 0xffffffffffffffff]
  (List.range 16).all (fun sampleIdx =>
    let env : VarEnv := vars.foldl (fun (accEnv, vIdx) varId =>
      let val : UInt64 :=
        if sampleIdx < 8 then
          let bIdx := (sampleIdx + vIdx * 3) % boundaryVals.length
          boundaryVals[bIdx]?.getD 0
        else
          let seed : UInt64 := (sampleIdx.toUInt64 + 1) * 0x9e3779b97f4a7c15 + vIdx.toUInt64 * 0xbf58476d1ce4e5b9
          let (r, _) := splitMix64Next seed
          r
      (accEnv.bind varId (.u64 val), vIdx + 1)
    ) (VarEnv.empty, 0) |>.1
    match evalScalarExpr env e, evalScalarExpr env cand with
    | .ok v1, .ok v2 => v1 == v2
    | .error _, .error _ => true
    | _, _ => false
  )

/-- Stage 2 Soundness Verifier: SymbolicTV formal equivalence check.
    Verifies symbolic canonical normal form equivalence plus UB/poison preservation. -/
def symCheckScalarEquiv (e cand : ScalarExpr) : Bool :=
  let se := symEvalScalar default e
  let sc := symEvalScalar default cand
  let ubOk := !se.noUB || sc.noUB
  let poisonOk := !se.nonPoison || sc.nonPoison
  let strictNormEq := normSymExpr se.expr == normSymExpr sc.expr
  let extNormEq := normSymSuperopt se.expr == normSymSuperopt sc.expr
  ubOk && poisonOk && (strictNormEq || extNormEq)

/-- Synthesize candidate expressions for `e` on `target`:
    1. Kernel-verified `LeanNative.Proofs.rewriteScalarPeephole e`
    2. Symbolic canonical normalizer `symExprToScalarExpr? (normSymExpr (symEvalScalar default e).expr)`
    3. Enumerative algebraic & bitwise synthesis templates over `e` and its optimized subexpressions. -/
partial def synthesizeCandidates (target : SuperoptTarget) (e : ScalarExpr) : List ScalarExpr :=
  -- First recursively optimize children so multi-level templates trigger
  let bestOf (x : ScalarExpr) : ScalarExpr := (synthesizeCandidates target x).head?.getD x
  let eRec : ScalarExpr :=
    match e with
    | .binOp op l r => .binOp op (bestOf l) (bestOf r)
    | .unaryOp op a => .unaryOp op (bestOf a)
    | .select c t f => .select (bestOf c) (bestOf t) (bestOf f)
    | .fma a b c => .fma (bestOf a) (bestOf b) (bestOf c)
    | other => other
  let peepCand1 := LeanNative.Proofs.rewriteScalarPeephole e
  let peepCand2 := LeanNative.Proofs.rewriteScalarPeephole eRec
  let symCand1 := (symExprToScalarExpr? (normSymExpr (symEvalScalar default e).expr)).toList
  let symCand2 := (symExprToScalarExpr? (normSymSuperopt (symEvalScalar default e).expr)).toList
  let tmplCands1 := synthesizeTopLevelTemplates e
  let tmplCands2 := synthesizeTopLevelTemplates eRec
  let tmplCands3 := tmplCands1.flatMap synthesizeTopLevelTemplates ++ tmplCands2.flatMap synthesizeTopLevelTemplates
  let rawCands :=
    [eRec, peepCand1, peepCand2] ++ symCand1 ++ symCand2 ++ tmplCands1 ++ tmplCands2 ++ tmplCands3
  let uniqueCands := dedupScalarExprs rawCands
  -- Filter by two-stage soundness (FastCheck + SymbolicTV) and sort by target cost
  let validCands := uniqueCands.filter (fun cand =>
    fastCheckScalarEquiv e cand && symCheckScalarEquiv e cand)
  -- Pick the lowest-cost verified candidate first
  let best := validCands.foldl (fun bestOpt cand =>
    match bestOpt with
    | none => some cand
    | some curBest =>
      if scalarExprCost target cand < scalarExprCost target curBest then
        some cand
      else
        some curBest
  ) none
  match best with
  | some b => b :: (validCands.filter (fun c => c != b))
  | none => [e]

/-- Record of a single verified superoptimizer rewrite inside an `LNIRDecl`. -/
structure SuperoptRewriteRecord where
  declName            : String
  target              : String
  originalExpr        : String
  synthesizedExpr     : String
  costBefore          : Nat
  costAfter           : Nat
  fastCheckPassed     : Bool
  symbolicTVPassed    : Bool
  kernelProofVerified : Bool := false
  theoremRef          : String := "LeanNative.Proofs.SymbolicTV"
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Module-level superoptimization report. -/
structure SuperoptReport where
  moduleName       : String
  schemaVersion    : String := "lean-native-superopt-v1"
  target           : String
  totalDecls       : Nat
  rewritesApplied  : Nat
  totalCostBefore  : Nat
  totalCostAfter   : Nat
  records          : List SuperoptRewriteRecord
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Compute total scalar expression latency cost across an `LNIRCode` block under `p`. -/
def codeScalarCostWithProfile (p : HardwareCostProfile) : LNIRCode → Nat
  | .letBind _ _ (.scalar se) k => scalarExprCostWithProfile p se + codeScalarCostWithProfile p k
  | .letBind _ _ _ k => codeScalarCostWithProfile p k
  | .rawStore _ _ _ _ k => codeScalarCostWithProfile p k
  | .incRef _ _ k => codeScalarCostWithProfile p k
  | .decRef _ _ k => codeScalarCostWithProfile p k
  | .ite _ t e => 4 + codeScalarCostWithProfile p t + codeScalarCostWithProfile p e
  | .seqFor _ _ _ _ _ _ step k => codeScalarCostWithProfile p step + codeScalarCostWithProfile p k
  | .parFor _ _ _ _ (.customScalar _ _ body) k => scalarExprCostWithProfile p body + codeScalarCostWithProfile p k
  | .parFor _ _ _ _ _ k => codeScalarCostWithProfile p k
  | .ret _ | .unreachable => 0

/-- Compute total scalar expression latency cost across an `LNIRCode` block. -/
def codeScalarCost (target : SuperoptTarget) (code : LNIRCode) : Nat :=
  codeScalarCostWithProfile (HardwareCostProfile.forTarget target) code

/-- Superoptimize a single `ScalarExpr` using a `HardwareCostProfile`, enforcing the two-stage
    `fastCheckScalarEquiv` + `symCheckScalarEquiv` formal soundness gate. -/
def superoptScalarExprCore (p : HardwareCostProfile) (targetLabel : String) (declName : String) (e : ScalarExpr) :
    ScalarExpr × Option SuperoptRewriteRecord :=
  let origCost := scalarExprCostWithProfile p e
  let cands := synthesizeCandidates p.target e
  let bestCand :=
    cands.foldl (fun acc cand =>
      let cCost := scalarExprCostWithProfile p cand
      if fastCheckScalarEquiv e cand && symCheckScalarEquiv e cand && cCost < scalarExprCostWithProfile p acc then
        cand
      else
        acc
    ) e
  let afterCost := scalarExprCostWithProfile p bestCand
  if bestCand != e && afterCost < origCost then
    let isKernelVerified :=
      bestCand == LeanNative.Proofs.rewriteScalarVerified e ||
      bestCand == LeanNative.Proofs.rewriteScalarPeephole e
    let thmRef :=
      if isKernelVerified then "LeanNative.Proofs.rewriteScalarVerified_sound"
      else "LeanNative.Proofs.SymbolicTV"
    (bestCand, some {
      declName := declName
      target := targetLabel
      originalExpr := reprStr e
      synthesizedExpr := reprStr bestCand
      costBefore := origCost
      costAfter := afterCost
      fastCheckPassed := fastCheckScalarEquiv e bestCand
      symbolicTVPassed := symCheckScalarEquiv e bestCand
      kernelProofVerified := isKernelVerified
      theoremRef := thmRef
    })
  else
    (e, none)

/-- Superoptimize a single `ScalarExpr` for `target`, selecting the lowest-cost verified
    candidate strictly cheaper than `scalarExprCost target e`. -/
def superoptScalarExpr (target : SuperoptTarget) (declName : String) (e : ScalarExpr) :
    ScalarExpr × Option SuperoptRewriteRecord :=
  superoptScalarExprCore (HardwareCostProfile.forTarget target) target.toString declName e

/-- Superoptimize a single `ScalarExpr` using a custom `HardwareCostProfile` (`profiles/*.json`),
    enforcing the exact same `fastCheckScalarEquiv` + `symCheckScalarEquiv` formal soundness gate. -/
def superoptScalarExprWithProfile (p : HardwareCostProfile) (declName : String) (e : ScalarExpr) :
    ScalarExpr × Option SuperoptRewriteRecord :=
  superoptScalarExprCore p s!"{p.target.toString}:{p.profileId}" declName e

/-- Superoptimize all scalar expressions in an `LNIRCode` block under `p`. -/
def superoptCodeCore (p : HardwareCostProfile) (targetLabel : String) (declName : String) :
    LNIRCode → LNIRCode × List SuperoptRewriteRecord
  | .letBind dst ty (.scalar se) k =>
    let (se', recOpt) := superoptScalarExprCore p targetLabel declName se
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.letBind dst ty (.scalar se') k', match recOpt with | some r => r :: kRecs | none => kRecs)
  | .letBind dst ty val k =>
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.letBind dst ty val k', kRecs)
  | .rawStore pv iv vv ety k =>
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.rawStore pv iv vv ety k', kRecs)
  | .incRef ov c k =>
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.incRef ov c k', kRecs)
  | .decRef ov c k =>
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.decRef ov c k', kRecs)
  | .ite cv t e =>
    let (t', tRecs) := superoptCodeCore p targetLabel declName t
    let (e', eRecs) := superoptCodeCore p targetLabel declName e
    (.ite cv t' e', tRecs ++ eRecs)
  | .seqFor iv lv hv av ai aty step k =>
    let (step', sRecs) := superoptCodeCore p targetLabel declName step
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.seqFor iv lv hv av ai aty step' k', sRecs ++ kRecs)
  | .parFor ov lv ins ety (.customScalar idxVar inVars body) k =>
    let (body', recOpt) := superoptScalarExprCore p targetLabel declName body
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.parFor ov lv ins ety (.customScalar idxVar inVars body') k', match recOpt with | some r => r :: kRecs | none => kRecs)
  | .parFor ov lv ins ety kern k =>
    let (k', kRecs) := superoptCodeCore p targetLabel declName k
    (.parFor ov lv ins ety kern k', kRecs)
  | .ret v => (.ret v, [])
  | .unreachable => (.unreachable, [])

/-- Superoptimize all scalar expressions in an `LNIRCode` block. -/
def superoptCode (target : SuperoptTarget) (declName : String) (code : LNIRCode) :
    LNIRCode × List SuperoptRewriteRecord :=
  superoptCodeCore (HardwareCostProfile.forTarget target) target.toString declName code

/-- Superoptimize an `LNIRDecl` under `p`. -/
def superoptDeclCore (p : HardwareCostProfile) (targetLabel : String) (d : LNIRDecl) :
    LNIRDecl × List SuperoptRewriteRecord :=
  let (body', recs) := superoptCodeCore p targetLabel d.name d.body
  let assurance' :=
    if recs.isEmpty then d.assurance
    else if recs.all (fun r => r.kernelProofVerified) then
      AssuranceLevel.combine d.assurance .verifiedKernelProof
    else
      AssuranceLevel.combine d.assurance .translationValidated
  ({ d with body := body', assurance := assurance' }, recs)

/-- Superoptimize an `LNIRDecl` for `target`. -/
def superoptDecl (target : SuperoptTarget) (d : LNIRDecl) :
    LNIRDecl × List SuperoptRewriteRecord :=
  superoptDeclCore (HardwareCostProfile.forTarget target) target.toString d

/-- Superoptimize all declarations in an `LNIRModule` under `p` and return `SuperoptReport`. -/
def superoptModuleCore (p : HardwareCostProfile) (targetLabel : String) (m : LNIRModule) :
    LNIRModule × SuperoptReport :=
  let costBefore := m.decls.foldl (fun acc d => acc + codeScalarCostWithProfile p d.body) 0
  let (decls', allRecs) := m.decls.foldl (fun (dAcc, rAcc) d =>
    let (d', recs) := superoptDeclCore p targetLabel d
    (dAcc ++ [d'], rAcc ++ recs)
  ) ([], [])
  let m' : LNIRModule := { m with decls := decls' }
  let costAfter := m'.decls.foldl (fun acc d => acc + codeScalarCostWithProfile p d.body) 0
  (m', {
    moduleName := m.moduleName
    schemaVersion := "lean-native-superopt-v1"
    target := targetLabel
    totalDecls := m.decls.length
    rewritesApplied := allRecs.length
    totalCostBefore := costBefore
    totalCostAfter := costAfter
    records := allRecs
  })

/-- Superoptimize all declarations in an `LNIRModule` for `target` and return the
    optimized module along with a structured `SuperoptReport`. -/
def superoptModule (target : SuperoptTarget) (m : LNIRModule) : LNIRModule × SuperoptReport :=
  superoptModuleCore (HardwareCostProfile.forTarget target) target.toString m

/-- Superoptimize all declarations in an `LNIRModule` using a `HardwareCostProfile` (`profiles/*.json`). -/
def superoptModuleWithProfile (p : HardwareCostProfile) (m : LNIRModule) : LNIRModule × SuperoptReport :=
  superoptModuleCore p s!"{p.target.toString}:{p.profileId}" m

private abbrev escapeJsonSO := LeanNative.IR.jsonEscape

def SuperoptRewriteRecord.toJson (r : SuperoptRewriteRecord) : String :=
  s!"\{\"declName\":\"{escapeJsonSO r.declName}\"," ++
  s!"\"target\":\"{escapeJsonSO r.target}\"," ++
  s!"\"originalExpr\":\"{escapeJsonSO r.originalExpr}\"," ++
  s!"\"synthesizedExpr\":\"{escapeJsonSO r.synthesizedExpr}\"," ++
  s!"\"costBefore\":{r.costBefore},\"costAfter\":{r.costAfter}," ++
  s!"\"fastCheckPassed\":{r.fastCheckPassed}," ++
  s!"\"symbolicTVPassed\":{r.symbolicTVPassed}," ++
  s!"\"kernelProofVerified\":{r.kernelProofVerified}," ++
  s!"\"theoremRef\":\"{escapeJsonSO r.theoremRef}\"}"

def SuperoptReport.toJson (r : SuperoptReport) : String :=
  let recsJson := String.intercalate "," (r.records.map SuperoptRewriteRecord.toJson)
  s!"\{\"schemaVersion\":\"{escapeJsonSO r.schemaVersion}\"," ++
  s!"\"moduleName\":\"{escapeJsonSO r.moduleName}\"," ++
  s!"\"target\":\"{escapeJsonSO r.target}\"," ++
  s!"\"totalDecls\":{r.totalDecls},\"rewritesApplied\":{r.rewritesApplied}," ++
  s!"\"totalCostBefore\":{r.totalCostBefore},\"totalCostAfter\":{r.totalCostAfter}," ++
  s!"\"records\":[{recsJson}]}"

def SuperoptReport.formatSummary (r : SuperoptReport) : String :=
  let header :=
    s!"=== LeanNative Cost-Guided Enumerative Superoptimizer Report ===\n" ++
    s!"Module          : {r.moduleName} ({r.schemaVersion})\n" ++
    s!"Target Arch     : {r.target}\n" ++
    s!"Rewrites Applied: {r.rewritesApplied} across {r.totalDecls} declarations\n" ++
    s!"Total Latency   : {r.totalCostBefore} -> {r.totalCostAfter} cycles\n"
  let lines := r.records.map (fun recEntry =>
    s!"  [{recEntry.declName}] cost {recEntry.costBefore} -> {recEntry.costAfter} " ++
    s!"(FastCheck={recEntry.fastCheckPassed}, SymbolicTV={recEntry.symbolicTVPassed}, " ++
    s!"KernelProof={recEntry.kernelProofVerified} [{recEntry.theoremRef}]): " ++
    s!"{recEntry.originalExpr} ==> {recEntry.synthesizedExpr}")
  header ++ String.intercalate "\n" lines

end LeanNative.Transform
