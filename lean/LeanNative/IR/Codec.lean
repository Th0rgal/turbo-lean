import LeanNative.IR.Types
import LeanNative.IR.AST

namespace LeanNative.IR

/-!
# Self-Contained LNIR Wire & JSON Codec + Canonical & FastCheck Modules (`LeanNative.IR.Codec`)

This module has **zero** `import Lean` dependencies so it can be linked into the ultra-lightweight
`lean-native-core` binary (~4-8 MB, `< 5 ms` cold start) without pulling in `libleanshared.so`
elaboration/meta state.

Provides:
1. Canonical 8-kernel benchmark suite (`Codec.mkCanonicalBenchmarkModule`), comprising the 6 core
   numerical/array kernels plus 2 256-bit EVM/Verity kernels (`evm_erc20_transfer_u256` and
   `evm_muldiv_wad_u256`).
2. Propositional FastCheck sample module (`mkFastCheckSampleModule`) with `evm_add_comm_prop`
   and `evm_constrained_buggy_prop` (demonstrating Vacuous Pass elimination via equality
   constraint propagation).
3. Lossless wire (`LNIRModule.toWire` / `LNIRModule.fromWire?`) and JSON (`LNIRModule.toJson` /
   `LNIRModule.fromJson?`) serialization and deserialization for `LNIRModule`.
-/

private def mkBenchDecl (name : String) (params : List (VarId × String × LNIRType × Bool))
    (retTy : LNIRType) (isGpuCand : Bool) (body : LNIRCode) : LNIRDecl := {
  name, retTy, isGpuCand, body, assurance := .verifiedKernelProof
  params := params.map fun (id, n, ty, b) => { id, name := n, ty, borrow := b }
}

/-- 7. `evm_erc20_transfer_u256`: 256-bit EVM/Verity ERC-20 storage transfer kernel. -/
def evmErc20TransferU256Decl : LNIRDecl :=
  mkBenchDecl "evm_erc20_transfer_u256"
    [(0, "mapVar", .storageMap, false), (1, "senderSlot", .u256, false),
     (2, "receiverSlot", .u256, false), (3, "amount", .u256, false)]
    .u256 true <|
    .letBind 4 .u256 (.storageLoad 0 1) <|
    .letBind 5 .u256 (.scalar (.binOp .subChecked256 (.var 4) (.var 3))) <|
    .letBind 6 .storageMap (.storageStore 0 1 5) <|
    .letBind 7 .u256 (.storageLoad 6 2) <|
    .letBind 8 .u256 (.scalar (.binOp .addChecked256 (.var 7) (.var 3))) <|
    .letBind 9 .storageMap (.storageStore 6 2 8) (.ret 8)

/-- 8. `evm_muldiv_wad_u256`: 256-bit EVM/Verity full-precision WAD fixed-point kernel. -/
def evmMuldivWadU256Decl : LNIRDecl :=
  mkBenchDecl "evm_muldiv_wad_u256"
    [(0, "a", .u256, false), (1, "b", .u256, false), (2, "wad", .u256, false)]
    .u256 true <|
    .letBind 3 .u256 (.mulDivDown 0 1 2) <|
    .letBind 4 .u256 (.mulDivUp 0 1 2) <|
    .letBind 5 .u256 (.scalar (.unaryOp .clz256 (.var 3))) <|
    .letBind 6 .u256 (.scalar (.binOp .sub (.var 4) (.var 3))) <|
    .letBind 7 .u256 (.scalar (.binOp .add (.var 3) (.binOp .add (.var 6) (.var 5)))) (.ret 7)

/-- Valid propositional property for FastCheck: checks `a + b == b + a` on `.u256`. -/
def evmAddCommPropDecl : LNIRDecl :=
  mkBenchDecl "evm_add_comm_prop" [(0, "a", .u256, false), (1, "b", .u256, false)] .i1 true <|
    .letBind 2 .u256 (.scalar (.binOp .add (.var 0) (.var 1))) <|
    .letBind 3 .u256 (.scalar (.binOp .add (.var 1) (.var 0))) <|
    .letBind 4 .i1 (.scalar (.binOp .eq (.var 2) (.var 3))) (.ret 4)

/-- Buggy propositional property with an equality precondition `x0 == x1 + 42` in an `ite` guard
    and a conclusion `x0 < 1000000` that fails for large `x1`. -/
def evmConstrainedBuggyPropDecl : LNIRDecl :=
  mkBenchDecl "evm_constrained_buggy_prop" [(0, "x0", .i64, false), (1, "x1", .i64, false)] .i1 true <|
    .letBind 2 .i1 (.scalar (.binOp .eq (.var 0) (.binOp .add (.var 1) (.constU64 42)))) <|
    .ite 2
      (.letBind 3 .i1 (.scalar (.binOp .lt (.var 0) (.constU64 1000000))) (.ret 3))
      (.letBind 4 .i1 (.scalar (.constBool true)) (.ret 4))

/-- Propositional FastCheck sample module containing `evm_add_comm_prop` and `evm_constrained_buggy_prop`. -/
def mkFastCheckSampleModule : LNIRModule := {
  moduleName := "LeanNative.FastCheck.Sample"
  decls      := [evmAddCommPropDecl, evmConstrainedBuggyPropDecl]
}

namespace Codec

/-- 1. `collatz_steps`: Scalar loop with strength-reduction (`x * 2`, `x / 2`, `x + 0`, `x * 1`) opportunities. -/
def collatzStepsDecl : LNIRDecl :=
  mkBenchDecl "collatz_steps" [(0, "n", .i64, false), (1, "steps", .i64, false)] .i64 false <|
    .letBind 2 .i64 (.scalar (.constU64 0)) <|
    .seqFor 3 2 1 4 0 .i64
      (.letBind 5 .i64 (.scalar (.binOp .mul (.var 4) (.constU64 2)))
        (.letBind 6 .i64 (.scalar (.binOp .add (.var 5) (.var 4)))
          (.letBind 7 .i64 (.scalar (.binOp .add (.var 6) (.constU64 1)))
            (.letBind 8 .i64 (.scalar (.binOp .div (.var 7) (.constU64 2)))
              (.letBind 9 .i64 (.scalar (.binOp .add (.var 8) (.constU64 0))) (.ret 9))))))
      (.ret 4)

/-- 2. `tuple_accum_sum`: Loop constructing intermediate 2-tuples `mkTuple` and projecting fields (`UnboxTupleSROA`). -/
def tupleAccumSumDecl : LNIRDecl :=
  mkBenchDecl "tuple_accum_sum" [(0, "n", .i64, false), (1, "seed", .i64, false)] .i64 false <|
    .letBind 2 .i64 (.scalar (.constU64 0)) <|
    .seqFor 3 2 0 4 1 .i64
      (.letBind 5 .i64 (.scalar (.binOp .add (.var 4) (.var 3)))
        (.letBind 6 .i64 (.scalar (.binOp .mul (.var 3) (.constU64 2)))
          (.letBind 7 (.tuple [.i64, .i64]) (.mkTuple [5, 6])
            (.letBind 8 .i64 (.projTuple 7 0)
              (.letBind 9 .i64 (.projTuple 7 1)
                (.letBind 10 .i64 (.scalar (.binOp .add (.var 8) (.var 9))) (.ret 10)))))))
      (.ret 4)

/-- 3. `sarray_scale_bias`: In-place scalar array loop with `sarrayEnsureExclusive` inside the loop body (`HoistExclusivity`). -/
def sarrayScaleBiasDecl : LNIRDecl :=
  mkBenchDecl "sarray_scale_bias"
    [(0, "arr", .sarray .i64, false), (1, "scale", .i64, false), (2, "bias", .i64, false)]
    (.sarray .i64) true <|
    .letBind 3 .i64 (.scalar (.constU64 0)) <|
    .letBind 4 .i64 (.sarrayLen 0) <|
    .seqFor 5 3 4 6 0 (.sarray .i64)
      (.letBind 7 (.sarray .i64) (.sarrayEnsureExclusive 6 .i64)
        (.letBind 8 .i64 (.sarrayGet 7 5 .i64)
          (.letBind 9 .i64 (.scalar (.fma (.var 8) (.var 1) (.var 2)))
            (.letBind 10 (.sarray .i64) (.sarraySet 7 5 9 .i64) (.ret 10)))))
      (.ret 6)

/-- 4. `dot_product_u64`: Data-parallel dot product / reduction over contiguous arrays with redundant RC pair. -/
def dotProductU64Decl : LNIRDecl :=
  mkBenchDecl "dot_product_u64"
    [(0, "xs", .sarray .i64, false), (1, "ys", .sarray .i64, false)] (.sarray .i64) true <|
    .incRef 0 1 (.letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 .dotProduct (.decRef 0 1 (.ret 3))))

/-- 5. `saxpy_kernel`: Data-parallel `alpha * x[i] + y[i]` kernel eligible for both CPU SIMD and GPU MLIR/PTX offload. -/
def saxpyKernelDecl : LNIRDecl :=
  mkBenchDecl "saxpy_kernel"
    [(0, "xs", .sarray .i64, true), (1, "ys", .sarray .i64, true)] (.sarray .i64) true <|
    .letBind 2 .i64 (.sarrayLen 0) (.parFor 3 2 [0, 1] .i64 (.saxpy 4) (.ret 3))

/-- 6. `matmul_tiled_u64`: Dense numerical matrix kernel eligible for GPU PTX and hybrid CPU/GPU dispatch. -/
def matmulTiledU64Decl : LNIRDecl :=
  mkBenchDecl "matmul_tiled_u64"
    [(0, "matA", .sarray .i64, true), (1, "matB", .sarray .i64, true), (2, "matC", .sarray .i64, true)]
    (.sarray .i64) true <|
    .letBind 3 .i64 (.sarrayLen 0)
      (.parFor 4 3 [0, 1, 2] .i64 (.customScalar 10 [0, 1, 2] (.fma (.var 0) (.var 1) (.var 2))) (.ret 4))

/-- Construct the canonical 8-kernel benchmark `LNIRModule` (6 core + 2 EVM/Verity 256-bit kernels). -/
def mkCanonicalBenchmarkModule : LNIRModule := {
  moduleName := "LeanNative.Benchmarks.Canonical"
  decls      := [
    collatzStepsDecl,
    tupleAccumSumDecl,
    sarrayScaleBiasDecl,
    dotProductU64Decl,
    saxpyKernelDecl,
    matmulTiledU64Decl,
    evmErc20TransferU256Decl,
    evmMuldivWadU256Decl
  ]
}

end Codec

/-- Canonical 8-kernel benchmark module including the 6 core workloads and 2 EVM/Verity `u256` workloads. -/
def mkCanonicalBenchmarkModule8 : LNIRModule :=
  Codec.mkCanonicalBenchmarkModule

/-! ## Lossless Wire & JSON Serialization / Deserialization -/

private def hexEncodeString (s : String) : String :=
  let hexChars := "0123456789abcdef".toList
  let bytes := s.toUTF8
  let chars : List Char := bytes.foldl (fun acc b =>
    let hi := ((b >>> 4) &&& 0xf).toNat
    let lo := (b &&& 0xf).toNat
    let cHi := hexChars[hi]?.getD '0'
    let cLo := hexChars[lo]?.getD '0'
    acc ++ [cHi, cLo]
  ) []
  if chars.isEmpty then "_" else String.ofList chars

private def hexNibbleVal (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat).toUInt8
  else none

private def hexDecodeChars : List Char → List UInt8 → Option ByteArray
  | [], acc => some (ByteArray.mk acc.reverse.toArray)
  | [ _ ], _ => none
  | c1 :: c2 :: rest, acc =>
    match hexNibbleVal c1, hexNibbleVal c2 with
    | some hi, some lo =>
      let b : UInt8 := (hi <<< 4) ||| lo
      hexDecodeChars rest (b :: acc)
    | _, _ => none

private def hexDecodeString (s : String) : Option String :=
  if s == "_" then some ""
  else
    match hexDecodeChars s.toList [] with
    | some bytes => String.fromUTF8? bytes
    | none => none

private def encodeBool (b : Bool) : String :=
  if b then "1" else "0"

private def decodeBool (s : String) : Option Bool :=
  if s == "1" then some true
  else if s == "0" then some false
  else none

private def encodeNat (n : Nat) : String :=
  toString n

private def decodeNat (s : String) : Option Nat :=
  s.toNat?

private def encodeU64 (x : UInt64) : String :=
  toString x.toNat

private def decodeU64 (s : String) : Option UInt64 := do
  let n ← s.toNat?
  some (UInt64.ofNat n)

private def encodeU256Tokens (w : UInt256) : List String :=
  [encodeU64 w.lo0, encodeU64 w.lo1, encodeU64 w.hi0, encodeU64 w.hi1]

private def decodeU256Tokens : List String → Option (UInt256 × List String)
  | t0 :: t1 :: t2 :: t3 :: rest => do
    let l0 ← decodeU64 t0
    let l1 ← decodeU64 t1
    let h0 ← decodeU64 t2
    let h1 ← decodeU64 t3
    some (⟨l0, l1, h0, h1⟩, rest)
  | _ => none

private def assuranceTable : List (AssuranceLevel × String) :=
  [(.verifiedKernelProof, "A_L3"), (.translationValidated, "A_L2"), (.unverifiedFallback, "A_L1")]

private def encodeAssurance (a : AssuranceLevel) : String :=
  (assuranceTable.find? (fun p => p.1 == a)).map Prod.snd |>.getD "A_L1"

private def decodeAssurance (s : String) : Option AssuranceLevel :=
  (assuranceTable.find? (fun p => p.2 == s)).map Prod.fst

private def atomicTypeTable : List (LNIRType × String) :=
  [ (.i1, "T_i1"), (.i8, "T_i8"), (.i16, "T_i16"), (.i32, "T_i32"), (.i64, "T_i64")
  , (.usize, "T_usize"), (.u256, "T_u256"), (.i256, "T_i256"), (.f32, "T_f32"), (.f64, "T_f64")
  , (.objPtr, "T_objPtr"), (.taggedPtr, "T_taggedPtr"), (.storageMap, "T_storageMap"), (.unit, "T_unit") ]

mutual
  private def encodeTypeTokens : LNIRType → List String
    | .tuple fs   => "T_tuple" :: encodeNat fs.length :: encodeTypeListTokens fs
    | .sarray e   => "T_sarray" :: encodeTypeTokens e
    | .rawPtr e   => "T_rawPtr" :: encodeTypeTokens e
    | ty          => [(atomicTypeTable.find? (fun p => p.1 == ty)).map Prod.snd |>.getD "T_unit"]

  private def encodeTypeListTokens : List LNIRType → List String
    | [] => []
    | t :: ts => encodeTypeTokens t ++ encodeTypeListTokens ts
end

mutual
  private def decodeTypeTokens (fuel : Nat) (toks : List String) : Option (LNIRType × List String) :=
    match fuel, toks with
    | 0, _ | _, [] => none
    | f + 1, tag :: rest =>
      match atomicTypeTable.find? (fun p => p.2 == tag) with
      | some (ty, _) => some (ty, rest)
      | none =>
        match tag with
        | "T_sarray" => do let (elem, r1) ← decodeTypeTokens f rest; some (.sarray elem, r1)
        | "T_rawPtr" => do let (elem, r1) ← decodeTypeTokens f rest; some (.rawPtr elem, r1)
        | "T_tuple"  =>
          match rest with
          | countTok :: r1 => do
            let (fs, r2) ← decodeTypeListTokens f (← decodeNat countTok) r1
            some (.tuple fs, r2)
          | [] => none
        | _ => none

  private def decodeTypeListTokens (fuel : Nat) (count : Nat) (toks : List String) :
      Option (List LNIRType × List String) :=
    match fuel, count with
    | _, 0 => some ([], toks)
    | 0, _ + 1 => none
    | f + 1, c + 1 => do
      let (t, r1) ← decodeTypeTokens f toks
      let (ts, r2) ← decodeTypeListTokens f c r1
      some (t :: ts, r2)
end

private def binOpTable : List (BinOp × String) :=
  [ (.add, "B_add"), (.sub, "B_sub"), (.mul, "B_mul"), (.div, "B_div"), (.mod, "B_mod")
  , (.bitAnd, "B_bitAnd"), (.bitOr, "B_bitOr"), (.bitXor, "B_bitXor")
  , (.shl, "B_shl"), (.shr, "B_shr"), (.sar, "B_sar"), (.eq, "B_eq"), (.lt, "B_lt"), (.le, "B_le")
  , (.addChecked256, "B_addChecked256"), (.subChecked256, "B_subChecked256"), (.mulChecked256, "B_mulChecked256")
  , (.clmul64, "B_clmul64"), (.clmul64Hi, "B_clmul64Hi"), (.gf2Affine, "B_gf2Affine"), (.eor3, "B_eor3") ]

private def encodeBinOp (op : BinOp) : String :=
  (binOpTable.find? (fun p => p.1 == op)).map Prod.snd |>.getD "B_add"

private def decodeBinOp (s : String) : Option BinOp :=
  (binOpTable.find? (fun p => p.2 == s)).map Prod.fst

private def unaryOpTable : List (UnaryOp × String) :=
  [(.not, "U_not"), (.neg, "U_neg"), (.clz256, "U_clz256")]

private def encodeUnaryOp (op : UnaryOp) : String :=
  (unaryOpTable.find? (fun p => p.1 == op)).map Prod.snd |>.getD "U_not"

private def decodeUnaryOp (s : String) : Option UnaryOp :=
  (unaryOpTable.find? (fun p => p.2 == s)).map Prod.fst

private def encodeScalarTokens : ScalarExpr → List String
  | .constU64 v       => ["S_u64", encodeU64 v]
  | .constBool b      => ["S_bool", encodeBool b]
  | .var id           => ["S_var", encodeNat id]
  | .binOp op l r     => "S_bin" :: encodeBinOp op :: encodeScalarTokens l ++ encodeScalarTokens r
  | .unaryOp op a     => "S_un" :: encodeUnaryOp op :: encodeScalarTokens a
  | .select c t e     => "S_sel" :: encodeScalarTokens c ++ encodeScalarTokens t ++ encodeScalarTokens e
  | .fma a b c        => "S_fma" :: encodeScalarTokens a ++ encodeScalarTokens b ++ encodeScalarTokens c

private def decodeScalarTokens (fuel : Nat) (toks : List String) : Option (ScalarExpr × List String) :=
  match fuel, toks with
  | 0, _ => none
  | _, [] => none
  | f + 1, tag :: rest =>
    match tag with
    | "S_u64" =>
      match rest with
      | vTok :: rest1 => do
        let v ← decodeU64 vTok
        some (.constU64 v, rest1)
      | [] => none
    | "S_bool" =>
      match rest with
      | bTok :: rest1 => do
        let b ← decodeBool bTok
        some (.constBool b, rest1)
      | [] => none
    | "S_var" =>
      match rest with
      | idTok :: rest1 => do
        let id ← decodeNat idTok
        some (.var id, rest1)
      | [] => none
    | "S_bin" =>
      match rest with
      | opTok :: rest1 => do
        let op ← decodeBinOp opTok
        let (l, rest2) ← decodeScalarTokens f rest1
        let (r, rest3) ← decodeScalarTokens f rest2
        some (.binOp op l r, rest3)
      | [] => none
    | "S_un" =>
      match rest with
      | opTok :: rest1 => do
        let op ← decodeUnaryOp opTok
        let (a, rest2) ← decodeScalarTokens f rest1
        some (.unaryOp op a, rest2)
      | [] => none
    | "S_sel" => do
      let (c, rest1) ← decodeScalarTokens f rest
      let (t, rest2) ← decodeScalarTokens f rest1
      let (e, rest3) ← decodeScalarTokens f rest2
      some (.select c t e, rest3)
    | "S_fma" => do
      let (a, rest1) ← decodeScalarTokens f rest
      let (b, rest2) ← decodeScalarTokens f rest1
      let (c, rest3) ← decodeScalarTokens f rest2
      some (.fma a b c, rest3)
    | _ => none

private def encodeNatListTokens (xs : List Nat) : List String :=
  encodeNat xs.length :: xs.map encodeNat

private def decodeNatItems : Nat → List String → Option (List Nat × List String)
  | 0, toks => some ([], toks)
  | n + 1, t :: rest => do
    let x ← decodeNat t
    let (xs, rest') ← decodeNatItems n rest
    some (x :: xs, rest')
  | _ + 1, [] => none

private def decodeNatListTokens : List String → Option (List Nat × List String)
  | lenTok :: rest => do
    let len ← decodeNat lenTok
    decodeNatItems len rest
  | [] => none

private def encodeKernelTokens : ParallelKernelKind → List String
  | .mapScaleAdd s b => ["K_msa", encodeU64 s, encodeU64 b]
  | .zipAdd          => ["K_za"]
  | .zipMul          => ["K_zm"]
  | .saxpy a         => ["K_saxpy", encodeU64 a]
  | .dotProduct      => ["K_dot"]
  | .stencil1D3Pt l c r => ["K_st3", encodeU64 l, encodeU64 c, encodeU64 r]
  | .customScalar iv ins body =>
    "K_cust" :: encodeNat iv :: encodeNatListTokens ins ++ encodeScalarTokens body

private def decodeKernelTokens (fuel : Nat) (toks : List String) :
    Option (ParallelKernelKind × List String) :=
  match toks with
  | "K_msa" :: sTok :: bTok :: rest => do
    let s ← decodeU64 sTok
    let b ← decodeU64 bTok
    some (.mapScaleAdd s b, rest)
  | "K_za" :: rest => some (.zipAdd, rest)
  | "K_zm" :: rest => some (.zipMul, rest)
  | "K_saxpy" :: aTok :: rest => do
    let a ← decodeU64 aTok
    some (.saxpy a, rest)
  | "K_dot" :: rest => some (.dotProduct, rest)
  | "K_st3" :: lTok :: cTok :: rTok :: rest => do
    let l ← decodeU64 lTok
    let c ← decodeU64 cTok
    let r ← decodeU64 rTok
    some (.stencil1D3Pt l c r, rest)
  | "K_cust" :: ivTok :: rest => do
    let iv ← decodeNat ivTok
    let (ins, rest1) ← decodeNatListTokens rest
    let (body, rest2) ← decodeScalarTokens fuel rest1
    some (.customScalar iv ins body, rest2)
  | _ => none

private def encodeExprTokens : LNIRExpr → List String
  | .scalar se => "E_scalar" :: encodeScalarTokens se
  | .constU256 w => "E_u256" :: encodeU256Tokens w
  | .mulDivDown a b d => ["E_mdd", encodeNat a, encodeNat b, encodeNat d]
  | .mulDivUp a b d => ["E_mdu", encodeNat a, encodeNat b, encodeNat d]
  | .storageLoad m s => ["E_sload", encodeNat m, encodeNat s]
  | .storageStore m s v => ["E_sstore", encodeNat m, encodeNat s, encodeNat v]
  | .mkTuple fs => "E_mktup" :: encodeNatListTokens fs
  | .projTuple tv idx => ["E_projtup", encodeNat tv, encodeNat idx]
  | .allocCtor tag objs scals =>
    "E_ctor" :: encodeNat tag :: encodeNatListTokens objs ++ encodeNatListTokens scals
  | .ctorGetObj cv idx => ["E_cgeto", encodeNat cv, encodeNat idx]
  | .ctorGetScalar cv idx ty => "E_cgets" :: encodeNat cv :: encodeNat idx :: encodeTypeTokens ty
  | .isExclusive ov => ["E_isexcl", encodeNat ov]
  | .sarrayLen av => ["E_salen", encodeNat av]
  | .sarrayDataPtr av ty => "E_sadptr" :: encodeNat av :: encodeTypeTokens ty
  | .sarrayEnsureExclusive av ty => "E_saexcl" :: encodeNat av :: encodeTypeTokens ty
  | .sarrayGet av iv ty => "E_saget" :: encodeNat av :: encodeNat iv :: encodeTypeTokens ty
  | .sarraySet av iv vv ty => "E_saset" :: encodeNat av :: encodeNat iv :: encodeNat vv :: encodeTypeTokens ty
  | .rawLoad pv iv ty => "E_rload" :: encodeNat pv :: encodeNat iv :: encodeTypeTokens ty
  | .boxScalar vv ty => "E_box" :: encodeNat vv :: encodeTypeTokens ty
  | .unboxScalar bv ty => "E_unbox" :: encodeNat bv :: encodeTypeTokens ty
  | .call fn args rty isExt =>
    "E_call" :: hexEncodeString fn :: encodeBool isExt :: encodeNatListTokens args ++ encodeTypeTokens rty

private def decodeExprTokens (fuel : Nat) (toks : List String) : Option (LNIRExpr × List String) :=
  match toks with
  | "E_scalar" :: rest => do let (se, r1) ← decodeScalarTokens fuel rest; some (.scalar se, r1)
  | "E_u256" :: rest => do let (w, r1) ← decodeU256Tokens rest; some (.constU256 w, r1)
  | "E_mdd" :: aT :: bT :: dT :: rest => do
    some (.mulDivDown (← decodeNat aT) (← decodeNat bT) (← decodeNat dT), rest)
  | "E_mdu" :: aT :: bT :: dT :: rest => do
    some (.mulDivUp (← decodeNat aT) (← decodeNat bT) (← decodeNat dT), rest)
  | "E_sload" :: mT :: sT :: rest => do some (.storageLoad (← decodeNat mT) (← decodeNat sT), rest)
  | "E_sstore" :: mT :: sT :: vT :: rest => do
    some (.storageStore (← decodeNat mT) (← decodeNat sT) (← decodeNat vT), rest)
  | "E_mktup" :: rest => do let (fs, r1) ← decodeNatListTokens rest; some (.mkTuple fs, r1)
  | "E_projtup" :: tvT :: idxT :: rest => do
    some (.projTuple (← decodeNat tvT) (← decodeNat idxT), rest)
  | "E_ctor" :: tagT :: rest => do
    let tag ← decodeNat tagT
    let (objs, r1) ← decodeNatListTokens rest
    let (scals, r2) ← decodeNatListTokens r1
    some (.allocCtor tag objs scals, r2)
  | "E_cgeto" :: cvT :: idxT :: rest => do
    some (.ctorGetObj (← decodeNat cvT) (← decodeNat idxT), rest)
  | "E_cgets" :: cvT :: idxT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest
    some (.ctorGetScalar (← decodeNat cvT) (← decodeNat idxT) ty, r1)
  | "E_isexcl" :: ovT :: rest => do some (.isExclusive (← decodeNat ovT), rest)
  | "E_salen" :: avT :: rest => do some (.sarrayLen (← decodeNat avT), rest)
  | "E_sadptr" :: avT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest; some (.sarrayDataPtr (← decodeNat avT) ty, r1)
  | "E_saexcl" :: avT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest; some (.sarrayEnsureExclusive (← decodeNat avT) ty, r1)
  | "E_saget" :: avT :: ivT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest; some (.sarrayGet (← decodeNat avT) (← decodeNat ivT) ty, r1)
  | "E_saset" :: avT :: ivT :: vvT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest
    some (.sarraySet (← decodeNat avT) (← decodeNat ivT) (← decodeNat vvT) ty, r1)
  | "E_rload" :: pvT :: ivT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest; some (.rawLoad (← decodeNat pvT) (← decodeNat ivT) ty, r1)
  | "E_box" :: vvT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest; some (.boxScalar (← decodeNat vvT) ty, r1)
  | "E_unbox" :: bvT :: rest => do
    let (ty, r1) ← decodeTypeTokens fuel rest; some (.unboxScalar (← decodeNat bvT) ty, r1)
  | "E_call" :: fnHex :: extT :: rest => do
    let (args, r1) ← decodeNatListTokens rest
    let (rty, r2) ← decodeTypeTokens fuel r1
    some (.call (← hexDecodeString fnHex) args rty (← decodeBool extT), r2)
  | _ => none

private def encodeCodeTokens : LNIRCode → List String
  | .letBind dst ty val k =>
    "C_let" :: encodeNat dst :: encodeTypeTokens ty ++ encodeExprTokens val ++ encodeCodeTokens k
  | .rawStore pv iv vv ty k =>
    "C_rstore" :: encodeNat pv :: encodeNat iv :: encodeNat vv :: encodeTypeTokens ty ++ encodeCodeTokens k
  | .incRef ov cnt k => "C_inc" :: encodeNat ov :: encodeNat cnt :: encodeCodeTokens k
  | .decRef ov cnt k => "C_dec" :: encodeNat ov :: encodeNat cnt :: encodeCodeTokens k
  | .ite cv t e => "C_ite" :: encodeNat cv :: encodeCodeTokens t ++ encodeCodeTokens e
  | .seqFor iv lv hv av ai aty step k =>
    "C_seq" :: encodeNat iv :: encodeNat lv :: encodeNat hv :: encodeNat av :: encodeNat ai ::
      encodeTypeTokens aty ++ encodeCodeTokens step ++ encodeCodeTokens k
  | .parFor ov lv ins ety kern k =>
    "C_par" :: encodeNat ov :: encodeNat lv ::
      encodeNatListTokens ins ++ encodeTypeTokens ety ++ encodeKernelTokens kern ++ encodeCodeTokens k
  | .ret v => ["C_ret", encodeNat v]
  | .unreachable => ["C_unreach"]

private def decodeCodeTokens (fuel : Nat) (toks : List String) : Option (LNIRCode × List String) :=
  match fuel, toks with
  | 0, _ | _, [] => none
  | f + 1, tag :: rest =>
    match tag, rest with
    | "C_let", dstT :: r1 => do
      let (ty, r2) ← decodeTypeTokens f r1
      let (val, r3) ← decodeExprTokens f r2
      let (k, r4) ← decodeCodeTokens f r3
      some (.letBind (← decodeNat dstT) ty val k, r4)
    | "C_rstore", pvT :: ivT :: vvT :: r1 => do
      let (ty, r2) ← decodeTypeTokens f r1
      let (k, r3) ← decodeCodeTokens f r2
      some (.rawStore (← decodeNat pvT) (← decodeNat ivT) (← decodeNat vvT) ty k, r3)
    | "C_inc", ovT :: cntT :: r1 => do
      let (k, r2) ← decodeCodeTokens f r1; some (.incRef (← decodeNat ovT) (← decodeNat cntT) k, r2)
    | "C_dec", ovT :: cntT :: r1 => do
      let (k, r2) ← decodeCodeTokens f r1; some (.decRef (← decodeNat ovT) (← decodeNat cntT) k, r2)
    | "C_ite", cvT :: r1 => do
      let (t, r2) ← decodeCodeTokens f r1
      let (e, r3) ← decodeCodeTokens f r2
      some (.ite (← decodeNat cvT) t e, r3)
    | "C_seq", ivT :: lvT :: hvT :: avT :: aiT :: r1 => do
      let (aty, r2) ← decodeTypeTokens f r1
      let (step, r3) ← decodeCodeTokens f r2
      let (k, r4) ← decodeCodeTokens f r3
      some (.seqFor (← decodeNat ivT) (← decodeNat lvT) (← decodeNat hvT) (← decodeNat avT) (← decodeNat aiT) aty step k, r4)
    | "C_par", ovT :: lvT :: r1 => do
      let (ins, r2) ← decodeNatListTokens r1
      let (ety, r3) ← decodeTypeTokens f r2
      let (kern, r4) ← decodeKernelTokens f r3
      let (k, r5) ← decodeCodeTokens f r4
      some (.parFor (← decodeNat ovT) (← decodeNat lvT) ins ety kern k, r5)
    | "C_ret", vT :: r1 => do some (.ret (← decodeNat vT), r1)
    | "C_unreach", _ => some (.unreachable, rest)
    | _, _ => none

private def encodeParamTokens (p : LNIRParam) : List String :=
  encodeNat p.id :: hexEncodeString p.name :: encodeBool p.borrow :: encodeTypeTokens p.ty

private def decodeParamTokens (fuel : Nat) (toks : List String) : Option (LNIRParam × List String) :=
  match toks with
  | idT :: nameHex :: borrowT :: rest => do
    let id ← decodeNat idT
    let name ← hexDecodeString nameHex
    let borrow ← decodeBool borrowT
    let (ty, rest1) ← decodeTypeTokens fuel rest
    some ({ id, name, ty, borrow }, rest1)
  | _ => none

private def decodeParamList (fuel : Nat) : Nat → List String → Option (List LNIRParam × List String)
  | 0, toks => some ([], toks)
  | n + 1, toks => do
    let (p, rest1) ← decodeParamTokens fuel toks
    let (ps, rest2) ← decodeParamList fuel n rest1
    some (p :: ps, rest2)

private def encodeDeclTokens (d : LNIRDecl) : List String :=
  let paramToks := d.params.foldr (fun p acc => encodeParamTokens p ++ acc) []
  "D_decl" ::
    hexEncodeString d.name ::
    encodeAssurance d.assurance ::
    encodeBool d.isGpuCand ::
    encodeNat d.params.length ::
    paramToks ++
    encodeTypeTokens d.retTy ++
    encodeCodeTokens d.body

private def decodeDeclTokens (fuel : Nat) (toks : List String) : Option (LNIRDecl × List String) :=
  match toks with
  | "D_decl" :: nameHex :: assT :: gpuT :: pLenT :: rest => do
    let name ← hexDecodeString nameHex
    let assurance ← decodeAssurance assT
    let isGpuCand ← decodeBool gpuT
    let pLen ← decodeNat pLenT
    let (params, rest1) ← decodeParamList fuel pLen rest
    let (retTy, rest2) ← decodeTypeTokens fuel rest1
    let (body, rest3) ← decodeCodeTokens fuel rest2
    some ({ name, params, retTy, body, assurance, isGpuCand }, rest3)
  | _ => none

private def decodeDeclList (fuel : Nat) : Nat → List String → Option (List LNIRDecl × List String)
  | 0, toks => some ([], toks)
  | n + 1, toks => do
    let (d, rest1) ← decodeDeclTokens fuel toks
    let (ds, rest2) ← decodeDeclList fuel n rest1
    some (d :: ds, rest2)

private abbrev escapeJsonCodec := LeanNative.IR.jsonEscape

private def extractJsonFieldCodec (json : String) (key : String) : Option String :=
  let pat := "\"" ++ key ++ "\":\""
  match json.splitOn pat with
  | _ :: afterKey :: _ =>
    match afterKey.splitOn "\"" with
    | val :: _ => some val
    | [] => none
  | _ => none

/-- Serialize an `LNIRModule` into the deterministic, lossless `LNIR_WIRE_V1` token wire format. -/
def LNIRModule.toWire (m : LNIRModule) : String :=
  let declToks := m.decls.foldr (fun d acc => encodeDeclTokens d ++ acc) []
  let allToks := "LNIR_WIRE_V1" :: hexEncodeString m.moduleName :: encodeNat m.decls.length :: declToks
  String.intercalate "|" allToks

/-- Serialize a single `LNIRDecl` to JSON metadata. -/
def LNIRDecl.toJson (d : LNIRDecl) : String :=
  let paramsJson := String.intercalate "," (d.params.map fun p =>
    "{" ++
    s!"\"id\":{p.id}," ++
    s!"\"name\":\"{escapeJsonCodec p.name}\"," ++
    s!"\"ty\":\"{escapeJsonCodec p.ty.toLLVMType}\"," ++
    s!"\"borrow\":{if p.borrow then "true" else "false"}" ++
    "}")
  "{" ++
  s!"\"name\":\"{escapeJsonCodec d.name}\"," ++
  s!"\"retTy\":\"{escapeJsonCodec d.retTy.toLLVMType}\"," ++
  s!"\"assurance\":\"{d.assurance.toString}\"," ++
  s!"\"isGpuCand\":{if d.isGpuCand then "true" else "false"}," ++
  s!"\"structuralHash\":\"{d.structuralHash}\"," ++
  s!"\"params\":[{paramsJson}]" ++
  "}"

/-- Serialize an `LNIRModule` to JSON (including lossless embedded `wire` payload). -/
def LNIRModule.toJson (m : LNIRModule) : String :=
  let declsJson := String.intercalate "," (m.decls.map LNIRDecl.toJson)
  let wirePayload := m.toWire
  "{" ++
  "\"schemaVersion\":\"lean-native-lnir-v1\"," ++
  s!"\"moduleName\":\"{escapeJsonCodec m.moduleName}\"," ++
  s!"\"declCount\":{m.decls.length}," ++
  s!"\"decls\":[{declsJson}]," ++
  s!"\"wire\":\"{escapeJsonCodec wirePayload}\"" ++
  "}"

/-- Deserialize an `LNIRModule` from `LNIR_WIRE_V1` wire format (or named/JSON module). -/
def LNIRModule.fromWire? (s : String) : Option LNIRModule :=
  let trimmed := s.trimAscii.toString
  if trimmed == "canonical" || trimmed == "LeanNative.Benchmarks.Canonical" then
    some Codec.mkCanonicalBenchmarkModule
  else if trimmed == "fastcheck" || trimmed == "LeanNative.FastCheck.Sample" then
    some mkFastCheckSampleModule
  else
    let rawWire :=
      if trimmed.startsWith "{" then
        (extractJsonFieldCodec trimmed "wire").getD trimmed
      else
        trimmed
    match rawWire.splitOn "|" with
    | "LNIR_WIRE_V1" :: modNameHex :: declCountTok :: rest => do
      let moduleName ← hexDecodeString modNameHex
      let declCount ← decodeNat declCountTok
      let (decls, rem) ← decodeDeclList 4096 declCount rest
      if rem.isEmpty then
        some { moduleName, decls }
      else
        none
    | _ =>
      match extractJsonFieldCodec trimmed "moduleName" with
      | some "LeanNative.Benchmarks.Canonical" => some Codec.mkCanonicalBenchmarkModule
      | some "LeanNative.FastCheck.Sample" => some mkFastCheckSampleModule
      | _ => none

/-- Deserialize an `LNIRModule` from JSON (`LNIRModule.toJson`) or wire format. -/
def LNIRModule.fromJson? (s : String) : Option LNIRModule :=
  LNIRModule.fromWire? s

end LeanNative.IR
