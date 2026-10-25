namespace LeanNative.IR

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

/-- Variable identifier in LNIR SSA/ANF form. -/
abbrev VarId := Nat

/-- Join point identifier in LNIR control flow. -/
abbrev JoinPointId := Nat

/-- Explicit formal assurance level attached to passes, certificates, and declarations. -/
inductive AssuranceLevel where
  | verifiedKernelProof   -- L3: Proved semantics-preserving in Lean 4 kernel (zero sorryAx)
  | translationValidated  -- L2: Validated by independent certificate checker / symbolic evaluator
  | unverifiedFallback    -- L1: Uses external C/Rust FFI, IO, or unverified runtime fallback
  deriving Repr, DecidableEq, Inhabited, BEq

namespace AssuranceLevel

def toString : AssuranceLevel → String
  | .verifiedKernelProof  => "VerifiedKernelProof"
  | .translationValidated => "TranslationValidated"
  | .unverifiedFallback   => "UnverifiedFallback"

instance : ToString AssuranceLevel := ⟨toString⟩

/-- Combine two assurance levels conservatively (minimum guarantee wins). -/
def combine : AssuranceLevel → AssuranceLevel → AssuranceLevel
  | .verifiedKernelProof, .verifiedKernelProof => .verifiedKernelProof
  | .unverifiedFallback, _ => .unverifiedFallback
  | _, .unverifiedFallback => .unverifiedFallback
  | _, _ => .translationValidated

end AssuranceLevel

/-- Target hardware architecture for code generation and cost modeling. -/
inductive TargetArch where
  | x86_64
  | arm64
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
  | .iosArm64     => "arm64-apple-ios"
  | .iosSimArm64  => "arm64-apple-ios-simulator"
  | .androidArm64 => "aarch64-linux-android"
  | .wasm32       => "wasm32-unknown-unknown"
  | .nvptx64      => "nvptx64-nvidia-cuda"
  | .hybridCpuGpu => "hybrid-cpu-nvptx64"

def symbolPrefix : TargetArch → String
  | .iosArm64 | .iosSimArm64 => "_"
  | _ => ""

def isAArch64 : TargetArch → Bool
  | .arm64 | .iosArm64 | .iosSimArm64 | .androidArm64 => true
  | _ => false

def isIOS : TargetArch → Bool
  | .iosArm64 | .iosSimArm64 => true
  | _ => false

def llvmTriple : TargetArch → String
  | .iosArm64    => "arm64-apple-ios16.0.0"
  | .iosSimArm64 => "arm64-apple-ios16.0.0-simulator"
  | t            => t.triple

end TargetArch

/-- Certified reference-counting emission discipline (`RcMode`):
    - `freestanding`: zero heap RC ops (for unboxed scalar / caller-borrowed slice kernels)
    - `singleThreaded`: non-atomic `load`/`add`/`sub`/`store` + `free` on `1 -> 0`
    - `atomic`: ARMv8.1-A LSE `atomicrmw add`/`sub` (`ldadd`/`ldaddal` on Apple A15) + `free` on `1 -> 0` -/
inductive RcMode where
  | freestanding
  | singleThreaded
  | atomic
  deriving Repr, DecidableEq, Inhabited, BEq

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
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 | .f32 | .f64 => true
  | _ => false

def is256Bit : LNIRType → Bool
  | .u256 | .i256 => true
  | _ => false

def isGpuCompatible : LNIRType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .usize | .u256 | .i256 | .f32 | .f64 => true
  | .sarray elem | .rawPtr elem => elem.isUnboxedScalar
  | .storageMap => true
  | _ => false

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
    | _    => acc.push c
  ) ""

/-- Format a string as a JSON quoted literal `"..."`. -/
def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

end LeanNative.IR
