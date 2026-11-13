import LeanSys.Par

namespace LeanSys.Par.IsaLevel

/-- Lower an `IsaLevel` capability profile into an LLVM 18 `"target-features"` string.
    Note: `sme2` is represented in the lattice for capability admission, while LLVM 18 lowering
    intentionally gates SME2 intrinsics behind explicit toolchain support. -/
def llvmTargetFeatures (a : LeanSys.Par.IsaLevel) : String :=
  let baseArch := match a.base with
    | .v8_0 => "+v8a"
    | .v8_2 => "+v8.2a"
    | .v8_5 => "+v8.5a"
    | .v8_6 => "+v8.6a"
    | .v9_0 => "+v9a"
    | .v9_2 => "+v9.2a"
  let feats : List String :=
    [baseArch] ++
    (if a.neon then ["+neon", "+fp-armv8"] else []) ++
    (if a.fp16 then ["+fullfp16", "+fp16fml"] else []) ++
    (if a.dotprod then ["+dotprod"] else []) ++
    (if a.i8mm then ["+i8mm"] else []) ++
    (if a.bf16 then ["+bf16"] else []) ++
    (if a.sve2 then ["+sve", "+sve2"] else []) ++
    (if a.sveBitperm && a.sve2 then ["+sve2-bitperm"] else []) ++
    (if a.lse then ["+lse"] else []) ++
    (if a.sha3 then ["+aes", "+sha2", "+sha3"] else [])
  String.intercalate "," feats

/-- Lower an `IsaLevel` capability profile into a portable Clang `-march=...` flag for AArch64 ELF/Android targets. -/
def clangArchFlag (a : LeanSys.Par.IsaLevel) : String :=
  let baseStr := match a.base with
    | .v8_0 => "armv8-a"
    | .v8_2 => "armv8.2-a"
    | .v8_5 => "armv8.5-a"
    | .v8_6 => "armv8.6-a"
    | .v9_0 => "armv9-a"
    | .v9_2 => "armv9.2-a"
  let exts : List String :=
    (if a.fp16 then ["+fp16", "+fp16fml"] else []) ++
    (if a.dotprod then ["+dotprod"] else []) ++
    (if a.i8mm then ["+i8mm"] else []) ++
    (if a.bf16 then ["+bf16"] else []) ++
    (if a.sve2 then ["+sve2"] else []) ++
    (if a.sveBitperm && a.sve2 then ["+sve2-bitperm"] else []) ++
    (if a.lse then ["+lse"] else []) ++
    (if a.sha3 then ["+sha3"] else [])
  "-march=" ++ baseStr ++ String.join exts

/-- Select the Apple Silicon `-mcpu=` / `"target-cpu"` name corresponding to an `IsaLevel` capability profile
    (`apple-a15` for A15 baseline, `apple-a16` when `i8mm`/`bf16` are enabled, `apple-m4` when `sme2` is enabled). -/
def appleCpuName (a : LeanSys.Par.IsaLevel) : String :=
  if a.sme2 then "apple-m4"
  else if a.i8mm || a.bf16 then "apple-a16"
  else if a.sha3 then "apple-a15"
  else "apple-a14"

end LeanSys.Par.IsaLevel

namespace LeanNative.IR

open LeanSys.Par
export LeanSys.Par (ArmBase IsaLevel CoreCluster CoreTopology WorkerBudget)

/-- Carryless product, low 64 bits. One definition for Eval, LLVM, Metal and PTX. -/
def clmul64 (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a <<< iu) else acc) else acc
  go 0 0
/-- Carryless product, high 64 bits of the 128-bit polynomial product. -/
def clmul64Hi (a b : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 64 then let iu := i.toUInt64; go (i + 1) (if ((b >>> iu) &&& 1) == 1 then acc ^^^ (a >>> (64 - iu)) else acc) else acc
  go 1 0
/-- Parity of the low 8 bits: 1 if odd, 0 if even. -/
def gf2Dot8 (row x : UInt64) : UInt64 :=
  let rec go (j : Nat) (s : UInt64) : UInt64 :=
    if _ : j < 8 then let ju := j.toUInt64; go (j + 1) (s ^^^ (((row >>> ju) &&& 1) &&& ((x >>> ju) &&& 1))) else s &&& 1
  go 0 0
/-- GF(2^8) affine map of the low byte, constant term 0. Matrix rows packed in `m`. -/
def gf2Affine (x m : UInt64) : UInt64 :=
  let xb := x &&& 0xff
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if _ : i < 8 then let iu := i.toUInt64; go (i + 1) (acc ||| (gf2Dot8 ((m >>> (iu * 8)) &&& 0xff) xb <<< iu)) else acc
  go 0 0

/-- Three-input xor. The third input is the low half of `b`, the second its high half. -/
def eor3 (a b : UInt64) : UInt64 := a ^^^ (b >>> 32) ^^^ (b &&& 0xffffffff)

/-- Eight independent byte affine maps, with GFNI's high-byte-first matrix rows.
    The immediate is masked to eight bits, as in the machine instruction. -/
def gf2Affine64 (x m imm8 : UInt64) : UInt64 :=
  Fin.foldl 8 (fun out b =>
    let xb := (x >>> (b.val.toUInt64 * 8)) &&& 0xff
    let y := Fin.foldl 8 (fun acc i =>
      let row := m >>> ((7 - i.val.toUInt64) * 8)
      let parity := Fin.foldl 8 (fun p j =>
        p ^^^ (((row >>> j.val.toUInt64) &&& 1) &&& ((xb >>> j.val.toUInt64) &&& 1))) 0
      acc ||| (parity <<< i.val.toUInt64)) 0
    out ||| ((y ^^^ (imm8 &&& 0xff)) <<< (b.val.toUInt64 * 8))) 0

/-- Intel ternary truth-table order: bit index `(a << 2) | (b << 1) | c`. -/
def ternaryLogic64 (a b c imm8 : UInt64) : UInt64 :=
  Fin.foldl 64 (fun out i =>
    let s := i.val.toUInt64
    let idx := (((a >>> s) &&& 1) <<< 2) ||| (((b >>> s) &&& 1) <<< 1) ||| ((c >>> s) &&& 1)
    out ||| (((imm8 >>> idx) &&& 1) <<< s)) 0

/-- Checked little-endian word read at a byte offset; out-of-range reads return zero. -/
def uget64LE (a : @& ByteArray) (byteOff : USize) : UInt64 :=
  if byteOff.toNat + 8 <= a.size then
    Fin.foldl 8 (fun out i =>
      out ||| ((a.get! (byteOff.toNat + i.val)).toUInt64 <<< (i.val.toUInt64 * 8))) 0
  else 0

/-- Checked little-endian word update at a byte offset; out-of-range writes do nothing. -/
def uset64LE (a : ByteArray) (byteOff : USize) (val : UInt64) : ByteArray :=
  if byteOff.toNat + 8 <= a.size then
    Fin.foldl 8 (fun out i =>
      out.set! (byteOff.toNat + i.val) (val >>> (i.val.toUInt64 * 8)).toUInt8) a
  else a

/-- Canonical masked carryless-product forms used by existing pure Lean kernels.
    Recognition checks every referenced helper body, not the exported symbol. -/
namespace MaskedClmul

@[inline] def nativeSelect (a b i : UInt64) : UInt64 :=
  a &&& (0 - ((b >>> i) &&& 1))

@[inline] def nativeClmulByte (a b : UInt64) : UInt64 :=
  nativeSelect a b 0 ^^^ nativeSelect (a <<< 1) b 1 ^^^
  nativeSelect (a <<< 2) b 2 ^^^ nativeSelect (a <<< 3) b 3 ^^^
  nativeSelect (a <<< 4) b 4 ^^^ nativeSelect (a <<< 5) b 5 ^^^
  nativeSelect (a <<< 6) b 6 ^^^ nativeSelect (a <<< 7) b 7

@[inline] def nativeClmulByteHi (a b : UInt64) : UInt64 :=
  nativeSelect (a >>> 63) b 1 ^^^ nativeSelect (a >>> 62) b 2 ^^^
  nativeSelect (a >>> 61) b 3 ^^^ nativeSelect (a >>> 60) b 4 ^^^
  nativeSelect (a >>> 59) b 5 ^^^ nativeSelect (a >>> 58) b 6 ^^^
  nativeSelect (a >>> 57) b 7

@[inline]
def nativeClmulLo (a b : UInt64) : UInt64 :=
  nativeClmulByte a b ^^^ (nativeClmulByte a (b >>> 8) <<< 8) ^^^
  (nativeClmulByte a (b >>> 16) <<< 16) ^^^ (nativeClmulByte a (b >>> 24) <<< 24) ^^^
  (nativeClmulByte a (b >>> 32) <<< 32) ^^^ (nativeClmulByte a (b >>> 40) <<< 40) ^^^
  (nativeClmulByte a (b >>> 48) <<< 48) ^^^ (nativeClmulByte a (b >>> 56) <<< 56)

@[inline] def nativeClmulUpper (a b i j : UInt64) : UInt64 :=
  (nativeClmulByte a (b >>> i) >>> j) ^^^ (nativeClmulByteHi a (b >>> i) <<< i)

@[inline]
def nativeClmulHi (a b : UInt64) : UInt64 :=
  nativeSelect (a >>> 63) b 1 ^^^ nativeSelect (a >>> 62) b 2 ^^^
  nativeSelect (a >>> 61) b 3 ^^^ nativeSelect (a >>> 60) b 4 ^^^
  nativeSelect (a >>> 59) b 5 ^^^ nativeSelect (a >>> 58) b 6 ^^^
  nativeSelect (a >>> 57) b 7 ^^^ nativeSelect (a >>> 56) b 8 ^^^
  nativeSelect (a >>> 55) b 9 ^^^ nativeSelect (a >>> 54) b 10 ^^^
  nativeSelect (a >>> 53) b 11 ^^^ nativeSelect (a >>> 52) b 12 ^^^
  nativeSelect (a >>> 51) b 13 ^^^ nativeSelect (a >>> 50) b 14 ^^^
  nativeSelect (a >>> 49) b 15 ^^^ nativeSelect (a >>> 48) b 16 ^^^
  nativeSelect (a >>> 47) b 17 ^^^ nativeSelect (a >>> 46) b 18 ^^^
  nativeSelect (a >>> 45) b 19 ^^^ nativeSelect (a >>> 44) b 20 ^^^
  nativeSelect (a >>> 43) b 21 ^^^ nativeSelect (a >>> 42) b 22 ^^^
  nativeSelect (a >>> 41) b 23 ^^^ nativeSelect (a >>> 40) b 24 ^^^
  nativeSelect (a >>> 39) b 25 ^^^ nativeSelect (a >>> 38) b 26 ^^^
  nativeSelect (a >>> 37) b 27 ^^^ nativeSelect (a >>> 36) b 28 ^^^
  nativeSelect (a >>> 35) b 29 ^^^ nativeSelect (a >>> 34) b 30 ^^^
  nativeSelect (a >>> 33) b 31 ^^^ nativeSelect (a >>> 32) b 32 ^^^
  nativeSelect (a >>> 31) b 33 ^^^ nativeSelect (a >>> 30) b 34 ^^^
  nativeSelect (a >>> 29) b 35 ^^^ nativeSelect (a >>> 28) b 36 ^^^
  nativeSelect (a >>> 27) b 37 ^^^ nativeSelect (a >>> 26) b 38 ^^^
  nativeSelect (a >>> 25) b 39 ^^^ nativeSelect (a >>> 24) b 40 ^^^
  nativeSelect (a >>> 23) b 41 ^^^ nativeSelect (a >>> 22) b 42 ^^^
  nativeSelect (a >>> 21) b 43 ^^^ nativeSelect (a >>> 20) b 44 ^^^
  nativeSelect (a >>> 19) b 45 ^^^ nativeSelect (a >>> 18) b 46 ^^^
  nativeSelect (a >>> 17) b 47 ^^^ nativeSelect (a >>> 16) b 48 ^^^
  nativeSelect (a >>> 15) b 49 ^^^ nativeSelect (a >>> 14) b 50 ^^^
  nativeSelect (a >>> 13) b 51 ^^^ nativeSelect (a >>> 12) b 52 ^^^
  nativeSelect (a >>> 11) b 53 ^^^ nativeSelect (a >>> 10) b 54 ^^^
  nativeSelect (a >>> 9) b 55 ^^^ nativeSelect (a >>> 8) b 56 ^^^
  nativeSelect (a >>> 7) b 57 ^^^ nativeSelect (a >>> 6) b 58 ^^^
  nativeSelect (a >>> 5) b 59 ^^^ nativeSelect (a >>> 4) b 60 ^^^
  nativeSelect (a >>> 3) b 61 ^^^ nativeSelect (a >>> 2) b 62 ^^^
  nativeSelect (a >>> 1) b 63

end MaskedClmul

/-- Variable identifier in LNIR SSA/ANF form. -/
abbrev VarId := Nat

/-- Join point identifier in LNIR control flow. -/
abbrev JoinPointId := Nat

/-- Explicit formal assurance level attached to passes, certificates, and declarations.
    Follows the actual executed compilation branch (`P0` Provenance Contract):
    - `verifiedKernelProof` (`L4`): The exact executable transformation branch `runCode` on `d.body`
      is backed by a machine-checked Lean 4 proof `∀ c, CodeRefines c (runCode c)` with `0 sorryAx`.
    - `translationValidated` (`L3`): An extended candidate `candBody != vc.runCode d.body` was selected
      and accepted by `SymbolicTV.validateTranslationDecl` (symbolic + concrete evaluation equivalence).
    - `tested` (`L2`): The pass or lowering step is validated by the 3-way differential conformance suite
      but not covered by a kernel refinement proof or total translation validator.
    - `unverifiedFallback` (`L1`, `"Assumed"`): Uses external C/Rust FFI (`@[extern]`), IO, or assumed target toolchain lowering.
    - `unsupported` (`L0`): Construct or target feature is outside the supported subset and must fail closed. -/
inductive AssuranceLevel where
  | verifiedKernelProof
  | translationValidated
  | tested
  | unverifiedFallback
  | unsupported
  deriving Repr, DecidableEq, Inhabited, BEq

namespace AssuranceLevel

def toString : AssuranceLevel → String
  | .verifiedKernelProof  => "VerifiedKernelProof"
  | .translationValidated => "TranslationValidated"
  | .tested               => "Tested"
  | .unverifiedFallback   => "Assumed"
  | .unsupported          => "Unsupported"

instance : ToString AssuranceLevel := ⟨toString⟩

def rank : AssuranceLevel → Nat
  | .unsupported          => 0
  | .unverifiedFallback   => 1
  | .tested               => 2
  | .translationValidated => 3
  | .verifiedKernelProof  => 4

/-- Combine two assurance levels conservatively (weakest link / minimum guarantee wins). -/
def combine (a b : AssuranceLevel) : AssuranceLevel :=
  if a.rank ≤ b.rank then a else b

end AssuranceLevel

/-- Target hardware architecture for code generation and cost modeling. -/
inductive TargetArch where
  | x86_64
  | arm64
  | macosArm64
  | iosArm64
  | iosSimArm64
  | androidArm64
  | wasm32
  | nvptx64
  | hybridCpuGpu
  deriving Repr, DecidableEq, Inhabited, BEq

namespace TargetArch

def triple : TargetArch → String
  | .x86_64       => "x86_64-unknown-linux-gnu"
  | .arm64        => "aarch64-unknown-linux-gnu"
  | .macosArm64   => "arm64-apple-macosx"
  | .iosArm64     => "arm64-apple-ios"
  | .iosSimArm64  => "arm64-apple-ios-simulator"
  | .androidArm64 => "aarch64-linux-android"
  | .wasm32       => "wasm32-unknown-unknown"
  | .nvptx64      => "nvptx64-nvidia-cuda"
  | .hybridCpuGpu => "hybrid-cpu-nvptx64"

def symbolPrefix : TargetArch → String
  | .macosArm64 | .iosArm64 | .iosSimArm64 => "_"
  | _ => ""

def isAArch64 : TargetArch → Bool
  | .arm64 | .macosArm64 | .iosArm64 | .iosSimArm64 | .androidArm64 => true
  | _ => false

def isMacOS : TargetArch → Bool
  | .macosArm64 => true
  | _ => false

def isIOS : TargetArch → Bool
  | .iosArm64 | .iosSimArm64 => true
  | _ => false

def isApple : TargetArch → Bool
  | .macosArm64 | .iosArm64 | .iosSimArm64 => true
  | _ => false

def isWasm : TargetArch → Bool
  | .wasm32 => true
  | _ => false

def llvmTriple : TargetArch → String
  | .macosArm64  => "arm64-apple-macosx14.0.0"
  | .iosArm64    => "arm64-apple-ios16.0.0"
  | .iosSimArm64 => "arm64-apple-ios16.0.0-simulator"
  | t            => t.triple

def dataLayout : TargetArch → String
  | .x86_64 | .hybridCpuGpu => "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
  | .arm64 | .androidArm64 => "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
  | .macosArm64 | .iosArm64 | .iosSimArm64 => "e-m:o-i64:64-i128:128-n32:64-S128"
  | .wasm32 => "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20"
  | .nvptx64 => "e-i64:64-i128:128-v16:16-v32:32-n16:32:64"

/-- Default compile-time `IsaLevel` baseline for an AArch64 `TargetArch`
    (`appleA15` for macOS M2 / iOS 16+ targets, portable `arm64Baseline` for Linux/Android ARM64). -/
def isaLevel : TargetArch → IsaLevel
  | .macosArm64 | .iosArm64 | .iosSimArm64 => IsaLevel.appleA15
  | _                                      => IsaLevel.arm64Baseline

/-- Canonical Clang compiler flags for `TargetArch` parameterized by optional `IsaLevel` override. -/
def clangFlags (t : TargetArch) (isaOverride? : Option IsaLevel := none) (wasmSimd128 : Bool := false) : Array String :=
  let isa := isaOverride?.getD t.isaLevel
  match t with
  | .x86_64       => #["--target=x86_64-unknown-linux-gnu", "-O3", "-fPIC", "-mpclmul", "-mavx2", "-Wno-override-module"]
  | .arm64        => #["--target=aarch64-unknown-linux-gnu", "-O3", "-fPIC", isa.clangArchFlag, "-Wno-override-module"]
  | .androidArm64 => #["--target=aarch64-linux-android29", "-O3", "-fPIC", isa.clangArchFlag, "-Wno-override-module"]
  | .macosArm64   =>
    let cpu := if isa == IsaLevel.appleA15 then "apple-m2" else isa.appleCpuName
    #["--target=arm64-apple-macosx14.0.0", "-O3", "-fPIC", s!"-mcpu={cpu}", "-Wno-override-module"]
  | .iosArm64     => #["--target=arm64-apple-ios16.0.0", "-O3", "-fPIC", s!"-mcpu={isa.appleCpuName}", "-Wno-override-module"]
  | .iosSimArm64  => #["--target=arm64-apple-ios16.0.0-simulator", "-O3", "-fPIC", s!"-mcpu={isa.appleCpuName}", "-Wno-override-module"]
  | .wasm32       =>
    let simdFlags := if wasmSimd128 then #["-msimd128"] else #[]
    #["--target=wasm32-unknown-unknown", "-O3", "-Wno-override-module"] ++ simdFlags
  | _             => #[s!"--target={t.triple}", "-O3", "-fPIC", "-Wno-override-module"]

end TargetArch

/-- Certified reference-counting emission discipline (`RcMode`):
    - `freestanding`: zero heap RC ops (for unboxed scalar / caller-borrowed slice kernels)
    - `singleThreaded`: non-atomic `load`/`add`/`sub`/`store` (no cross-thread sharing)
    - `atomic`: ARMv8.1-A LSE `atomicrmw add`/`sub` (`ldadd`/`ldaddal` on Apple A15) -/
inductive RcMode where
  | freestanding
  | singleThreaded
  | atomic
  deriving Repr, DecidableEq, Inhabited, BEq

namespace RcMode

def toCode : RcMode → UInt8
  | .freestanding   => 0
  | .singleThreaded => 1
  | .atomic         => 2

/-- Reference-counting mode safety verifier (`leannative_verify_rc_mode_safe`):
    - `rcMode = 0` (`freestanding`): admissible iff `hasHeapAllocs = 0`
    - `rcMode = 1` (`singleThreaded`): admissible iff `isMultiThreaded = 0 ∨ hasHeapAllocs = 0`
    - `rcMode = 2` (`atomic` LSE `ldadd`/`ldaddal`): admissible for all heap & thread configurations -/
@[inline]
def verifySafe (rcMode hasHeapAllocs isMultiThreaded : UInt8) : UInt8 :=
  if rcMode == 0 then
    if hasHeapAllocs == 0 then 1 else 0
  else if rcMode == 1 then
    if isMultiThreaded == 0 || hasHeapAllocs == 0 then 1 else 0
  else if rcMode == 2 then 1
  else 0

end RcMode

/-- 256-bit unsigned integer (`u256` / `EVMWord`), represented as four 64-bit limbs
    in little-endian order (`lo0` = bits 0..63, `lo1` = bits 64..127,
    `hi0` = bits 128..191, `hi1` = bits 192..255). -/
structure UInt256 where
  lo0 : UInt64 := 0
  lo1 : UInt64 := 0
  hi0 : UInt64 := 0
  hi1 : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Alias for EVM 256-bit word (`UInt256`). -/
abbrev EVMWord := UInt256

namespace UInt256

def modulusNat : Nat := 2 ^ 256

def zero : UInt256 := ⟨0, 0, 0, 0⟩
def one  : UInt256 := ⟨1, 0, 0, 0⟩
def max  : UInt256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩
def maxU64  : UInt256 := ⟨0xffffffffffffffff, 0, 0, 0⟩
def maxU128 : UInt256 := ⟨0xffffffffffffffff, 0xffffffffffffffff, 0, 0⟩
def twoPow255 : UInt256 := ⟨0, 0, 0, 0x8000000000000000⟩

def ofUInt64 (x : UInt64) : UInt256 := ⟨x, 0, 0, 0⟩

def toNat (w : UInt256) : Nat :=
  w.lo0.toNat +
  w.lo1.toNat * (2 ^ 64) +
  w.hi0.toNat * (2 ^ 128) +
  w.hi1.toNat * (2 ^ 192)

def ofNat (n : Nat) : UInt256 :=
  let m := n % modulusNat
  let l0 := (m % (2 ^ 64)).toUInt64
  let l1 := ((m / (2 ^ 64)) % (2 ^ 64)).toUInt64
  let h0 := ((m / (2 ^ 128)) % (2 ^ 64)).toUInt64
  let h1 := ((m / (2 ^ 192)) % (2 ^ 64)).toUInt64
  ⟨l0, l1, h0, h1⟩

def add (a b : UInt256) : UInt256 :=
  let s0 := a.lo0.toNat + b.lo0.toNat
  let c0 := s0 / (2 ^ 64)
  let s1 := a.lo1.toNat + b.lo1.toNat + c0
  let c1 := s1 / (2 ^ 64)
  let s2 := a.hi0.toNat + b.hi0.toNat + c1
  let c2 := s2 / (2 ^ 64)
  let s3 := a.hi1.toNat + b.hi1.toNat + c2
  ⟨UInt64.ofNat s0, UInt64.ofNat s1, UInt64.ofNat s2, UInt64.ofNat s3⟩

def sub (a b : UInt256) : UInt256 :=
  ofNat ((a.toNat + modulusNat - (b.toNat % modulusNat)) % modulusNat)

def mul (a b : UInt256) : UInt256 :=
  ofNat ((a.toNat * b.toNat) % modulusNat)

/-- Checked 256-bit addition returning `none` on overflow (`a + b >= 2^256`). -/
def addChecked (a b : UInt256) : Option UInt256 :=
  let s := a.toNat + b.toNat
  if s >= modulusNat then none else some (ofNat s)

/-- Checked 256-bit subtraction returning `none` on underflow (`a < b`). -/
def subChecked (a b : UInt256) : Option UInt256 :=
  if a.toNat < b.toNat then none else some (ofNat (a.toNat - b.toNat))

/-- Checked 256-bit multiplication returning `none` on overflow (`a * b >= 2^256`). -/
def mulChecked (a b : UInt256) : Option UInt256 :=
  let p := a.toNat * b.toNat
  if p >= modulusNat then none else some (ofNat p)

/-- Full 512-bit intermediate `floor((a * b) / denom)` (`mulDivDown` in EVM/Verity).
    Returns `none` if `denom == 0` or the quotient overflows `2^256`. -/
def mulDivDown (a b denom : UInt256) : Option UInt256 :=
  let d := denom.toNat
  if d == 0 then none
  else
    let q := (a.toNat * b.toNat) / d
    if q >= modulusNat then none else some (ofNat q)

/-- Full 512-bit intermediate `ceil((a * b) / denom)` (`mulDivUp` in EVM/Verity).
    Returns `none` if `denom == 0` or the rounded quotient overflows `2^256`. -/
def mulDivUp (a b denom : UInt256) : Option UInt256 :=
  let d := denom.toNat
  if d == 0 then none
  else
    let prod := a.toNat * b.toNat
    let q := (prod + d - 1) / d
    if q >= modulusNat then none else some (ofNat q)

def div (a b : UInt256) : Option UInt256 :=
  let d := b.toNat
  if d == 0 then none else some (ofNat (a.toNat / d))

def mod (a b : UInt256) : Option UInt256 :=
  let d := b.toNat
  if d == 0 then none else some (ofNat (a.toNat % d))

def bitAnd (a b : UInt256) : UInt256 :=
  ⟨a.lo0 &&& b.lo0, a.lo1 &&& b.lo1, a.hi0 &&& b.hi0, a.hi1 &&& b.hi1⟩

def bitOr (a b : UInt256) : UInt256 :=
  ⟨a.lo0 ||| b.lo0, a.lo1 ||| b.lo1, a.hi0 ||| b.hi0, a.hi1 ||| b.hi1⟩

def bitXor (a b : UInt256) : UInt256 :=
  ⟨a.lo0 ^^^ b.lo0, a.lo1 ^^^ b.lo1, a.hi0 ^^^ b.hi0, a.hi1 ^^^ b.hi1⟩

def bitNot (a : UInt256) : UInt256 :=
  ⟨~~~a.lo0, ~~~a.lo1, ~~~a.hi0, ~~~a.hi1⟩

def shl (a : UInt256) (shift : Nat) : UInt256 :=
  if shift >= 256 then zero
  else ofNat ((a.toNat * (2 ^ shift)) % modulusNat)

def shr (a : UInt256) (shift : Nat) : UInt256 :=
  if shift >= 256 then zero
  else ofNat (a.toNat / (2 ^ shift))

/-- 256-bit arithmetic shift right (`SAR` in EVM, sign-extending bit 255). -/
def sar (a : UInt256) (shift : Nat) : UInt256 :=
  let isNeg := (a.hi1 &&& 0x8000000000000000) != 0
  if shift >= 256 then
    if isNeg then max else zero
  else if shift == 0 then
    a
  else
    let logical := a.toNat / (2 ^ shift)
    if !isNeg then
      ofNat logical
    else
      let mask := (modulusNat - (2 ^ (256 - shift))) % modulusNat
      ofNat ((logical + mask) % modulusNat)

private def clzU64 (x : UInt64) : Nat :=
  if x == 0 then 64
  else
    let rec loop (fuel : Nat) (v : UInt64) (acc : Nat) : Nat :=
      match fuel with
      | 0 => acc
      | f + 1 =>
        if (v &&& 0x8000000000000000) != 0 then acc
        else loop f (v <<< 1) (acc + 1)
    loop 64 x 0

/-- Count leading zeros across all 256 bits (`0..256`). -/
def clz (a : UInt256) : UInt256 :=
  let n :=
    if a.hi1 != 0 then clzU64 a.hi1
    else if a.hi0 != 0 then 64 + clzU64 a.hi0
    else if a.lo1 != 0 then 128 + clzU64 a.lo1
    else 192 + clzU64 a.lo0
  ofUInt64 n.toUInt64

def lt (a b : UInt256) : Bool :=
  if a.hi1 != b.hi1 then decide (a.hi1 < b.hi1)
  else if a.hi0 != b.hi0 then decide (a.hi0 < b.hi0)
  else if a.lo1 != b.lo1 then decide (a.lo1 < b.lo1)
  else decide (a.lo0 < b.lo0)

def le (a b : UInt256) : Bool :=
  a == b || lt a b

@[simp]
theorem bitAnd_self (a : UInt256) : bitAnd a a = a := by
  cases a
  simp [bitAnd, UInt64.and_self]

@[simp]
theorem bitOr_self (a : UInt256) : bitOr a a = a := by
  cases a
  simp [bitOr, UInt64.or_self]

@[simp]
theorem bitXor_zero (a : UInt256) : bitXor a zero = a := by
  cases a
  simp [bitXor, zero, UInt64.xor_zero]

@[simp]
theorem zero_bitXor (a : UInt256) : bitXor zero a = a := by
  cases a
  simp [bitXor, zero, UInt64.zero_xor]

@[simp]
theorem bitOr_zero (a : UInt256) : bitOr a zero = a := by
  cases a
  simp [bitOr, zero, UInt64.or_zero]

@[simp]
theorem zero_bitOr (a : UInt256) : bitOr zero a = a := by
  cases a
  simp [bitOr, zero, UInt64.zero_or]

def toDecimalString (w : UInt256) : String :=
  toString w.toNat

end UInt256

/-- Formally specified types in LNIR (including 256-bit EVM words and Storage Maps). -/
inductive LNIRType where
  | i1
  | i8
  | i16
  | i32
  | i64
  | usize
  | u256                            -- 256-bit unsigned integer / EVMWord
  | i256                            -- 256-bit two's-complement signed integer
  | f16                             -- 16-bit IEEE 754 half-precision float (Apple7 / NEON fullfp16)
  | f32
  | f64
  | objPtr                          -- Heap lean_object*
  | taggedPtr                       -- Tagged scalar or lean_object* (tobject)
  | tuple (fields : List LNIRType)  -- Unboxed register-resident tuple/struct
  | sarray (elem : LNIRType)        -- Contiguous unboxed scalar array (ByteArray / FloatArray / UInt64 buffer)
  | rawPtr (elem : LNIRType)        -- Unboxed contiguous data pointer (m_data) after exclusivity check
  | storageMap                      -- 256-bit key-value EVM/Verity persistent storage mapping (uint256 -> uint256)
  | unit
  deriving Repr, Inhabited, BEq

namespace LNIRType

partial def toLLVMType : LNIRType → String
  | .i1          => "i1"
  | .i8          => "i8"
  | .i16         => "i16"
  | .i32         => "i32"
  | .i64         => "i64"
  | .usize       => "i64"
  | .u256        => "i256"
  | .i256        => "i256"
  | .f16         => "half"
  | .f32         => "float"
  | .f64         => "double"
  | .objPtr      => "ptr"
  | .taggedPtr   => "ptr"
  | .tuple fs    =>
    let inner := String.intercalate ", " (fs.map toLLVMType)
    "{ " ++ inner ++ " }"
  | .sarray _    => "ptr"
  | .rawPtr _    => "ptr"
  | .storageMap  => "ptr"
  | .unit        => "void"

def isUnboxedScalar : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 | .f16 | .f32 | .f64 => true
  | _ => false

def is256Bit : LNIRType → Bool
  | .u256 | .i256 => true
  | _ => false

def isGpuCompatible : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 | .f16 | .f32 | .f64 => true
  | .sarray elem | .rawPtr elem => elem.isUnboxedScalar
  | .storageMap => true
  | _ => false

/-- Whether a value of this type may hold (or own) a `lean_object*` (contract C1/C5 gate). -/
def containsHeapObject : LNIRType → Bool
  | .objPtr | .taggedPtr => true
  | .tuple fs => containsHeapObjectList fs
  | .sarray elem | .rawPtr elem => elem.containsHeapObject
  | _ => false
where
  containsHeapObjectList : List LNIRType → Bool
    | [] => false
    | t :: ts => t.containsHeapObject || containsHeapObjectList ts

end LNIRType

/-- Shared RFC-8259 JSON string escaping utility used across all codecs, reports, and certificates. -/
def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _    =>
      if c.toNat < 0x20 then
        acc ++ "\\u00" ++ String.singleton (Nat.digitChar (c.toNat / 16)) ++ String.singleton (Nat.digitChar (c.toNat % 16))
      else acc.push c
  ) ""

#guard jsonEscape "a\x01\x1f\"\\\n" == "a\\u0001\\u001f\\\"\\\\\\n"
#guard jsonEscape "\x0b\x08" == "\\u000b\\u0008"

/-- Format a string as a JSON quoted literal `"..."`. -/
def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

end LeanNative.IR
