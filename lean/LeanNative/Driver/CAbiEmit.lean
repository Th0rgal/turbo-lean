import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec

namespace LeanNative.Driver.CoreCLI

open LeanNative.IR
open LeanNative.IR.Codec

def lnirTypeToCType : LNIRType → String
  | .i1 | .i8 => "uint8_t" | .i16 | .f16 => "uint16_t" | .i32 => "uint32_t" | .i64 | .tuple _ => "uint64_t"
  | .usize => "size_t" | .u256 | .i256 => "const uint64_t*" | .f32 => "float" | .f64 => "double"
  | .rawPtr .i8 => "uint8_t*" | .rawPtr .i16 => "uint16_t*" | .rawPtr .i32 => "const uint32_t*"
  | .rawPtr _ | .sarray _ | .objPtr | .taggedPtr | .storageMap => "void*" | .unit => "void"

/-- C pointer and `size_t` width. Native LP64 targets are 8 bytes; `wasm32` is 4 bytes. -/
inductive ArchWidth where
  | bits64
  | bits32
  deriving Repr, DecidableEq, Inhabited, BEq

namespace ArchWidth

/-- Byte size of `void*` and `size_t` for this width. -/
def ptrBytes : ArchWidth → Nat
  | .bits64 => 8
  | .bits32 => 4

/-- Exclusive upper bound of the unsigned address space (`2^64` vs `2^32`). -/
def addrLimit : ArchWidth → Nat
  | .bits64 => 2 ^ 64
  | .bits32 => 2 ^ 32

/-- Maximum representable unsigned `uintptr_t` / `size_t` (`2^64 - 1` vs `2^32 - 1`). -/
def maxAddr (w : ArchWidth) : Nat := w.addrLimit - 1

/-- `TargetArch` selects the C99 pointer width used by slice typedefs and static asserts. -/
def ofTargetArch : TargetArch → ArchWidth
  | .wasm32 | .thumbv6m | .thumbv8mMain | .riscv32imac => .bits32
  | _ => .bits64

end ArchWidth

/-!
# Typed C99 ABI layout and slice marshaling

These definitions compute the C99 layout that header and shim emission follow.
Validation rejects zero alignment, an offset that is not a multiple of the field
alignment, a strided slice whose `(len - 1) * byteStride + elemSize` span overflows
or wraps the target pointer width (`ArchWidth`), a misaligned `dataPtr`, and a null
pointer to a non-empty slice.
-/

/-- Unboxed C99 scalar or slice-struct value carried by a generated binding. -/
inductive C99ScalarType where
  | u8 | i8 | bool | cBool | u16 | i16 | u32 | i32 | u64 | i64 | usize | f32 | f64
  | ptr | constPtr | u8Ptr | constU8Ptr | u16Ptr | constU16Ptr | u32Ptr | constU32Ptr
  | u64Ptr | constU64Ptr | f64Ptr | constF64Ptr
  | flatSlice | mutSlice
  deriving Repr, DecidableEq, Inhabited

namespace C99ScalarType

/-- Natural C99 size in bytes parameterized by target pointer width (`8` on LP64, `4` on `wasm32`). -/
def sizeOf (ty : C99ScalarType) (width : ArchWidth := .bits64) : Nat :=
  match ty with
  | .u8 | .i8 | .bool | .cBool => 1
  | .u16 | .i16 => 2
  | .u32 | .i32 | .f32 => 4
  | .u64 | .i64 | .f64 => 8
  | .usize | .ptr | .constPtr | .u8Ptr | .constU8Ptr
  | .u16Ptr | .constU16Ptr | .u32Ptr | .constU32Ptr
  | .u64Ptr | .constU64Ptr | .f64Ptr | .constF64Ptr => width.ptrBytes
  | .flatSlice | .mutSlice => 3 * width.ptrBytes

/-- Natural C99 alignment in bytes parameterized by target pointer width. -/
def alignOf (ty : C99ScalarType) (width : ArchWidth := .bits64) : Nat :=
  match ty, width with
  | .u64, .bits32 | .i64, .bits32 | .f64, .bits32 => 8
  | .flatSlice, _ | .mutSlice, _ => width.ptrBytes
  | _, _ => ty.sizeOf width

/-- C spelling used by the generated header. -/
def cSpelling : C99ScalarType → String
  | .u8 => "uint8_t" | .i8 => "int8_t" | .bool => "bool" | .cBool => "_Bool"
  | .u16 => "uint16_t" | .i16 => "int16_t" | .u32 => "uint32_t" | .i32 => "int32_t"
  | .u64 => "uint64_t" | .i64 => "int64_t" | .usize => "size_t"
  | .f32 => "float" | .f64 => "double"
  | .ptr => "void*" | .constPtr => "const void*"
  | .u8Ptr => "uint8_t*" | .constU8Ptr => "const uint8_t*"
  | .u16Ptr => "uint16_t*" | .constU16Ptr => "const uint16_t*"
  | .u32Ptr => "uint32_t*" | .constU32Ptr => "const uint32_t*"
  | .u64Ptr => "uint64_t*" | .constU64Ptr => "const uint64_t*"
  | .f64Ptr => "double*" | .constF64Ptr => "const double*"
  | .flatSlice => "lean_native_flat_slice_t" | .mutSlice => "lean_native_mut_slice_t"

/-- Parse a C99 type spelling emitted by the C-ABI frontends into a typed `C99ScalarType`. -/
def ofCSpelling? (raw : String) : Option C99ScalarType :=
  let t := raw.trimAscii.toString
  if t == "uint8_t" then some .u8
  else if t == "int8_t" then some .i8
  else if t == "bool" then some .bool
  else if t == "_Bool" then some .cBool
  else if t == "uint16_t" then some .u16
  else if t == "int16_t" then some .i16
  else if t == "uint32_t" then some .u32
  else if t == "int32_t" then some .i32
  else if t == "uint64_t" then some .u64
  else if t == "int64_t" then some .i64
  else if t == "size_t" then some .usize
  else if t == "float" then some .f32
  else if t == "double" then some .f64
  else if t == "void*" then some .ptr
  else if t == "const void*" then some .constPtr
  else if t == "uint8_t*" then some .u8Ptr
  else if t == "const uint8_t*" then some .constU8Ptr
  else if t == "uint16_t*" then some .u16Ptr
  else if t == "const uint16_t*" then some .constU16Ptr
  else if t == "uint32_t*" then some .u32Ptr
  else if t == "const uint32_t*" then some .constU32Ptr
  else if t == "uint64_t*" then some .u64Ptr
  else if t == "const uint64_t*" then some .constU64Ptr
  else if t == "double*" then some .f64Ptr
  else if t == "const double*" then some .constF64Ptr
  else if t == "lean_native_flat_slice_t" then some .flatSlice
  else if t == "lean_native_mut_slice_t" then some .mutSlice
  else none

end C99ScalarType

/-- One field before offsets are assigned. -/
structure C99FieldSpec where
  name : String
  ty : C99ScalarType
  deriving Repr, DecidableEq, Inhabited

/-- One field after natural alignment has assigned its byte interval. -/
structure C99FieldLayout where
  name : String
  ty : C99ScalarType
  offset : Nat
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, Inhabited

namespace C99FieldLayout

/-- Half-open byte interval occupied by the field. -/
def byteEnd (f : C99FieldLayout) : Nat := f.offset + f.size

/-- The alignment is positive and divides the assigned offset. -/
def isAligned (f : C99FieldLayout) : Prop :=
  f.align ≠ 0 ∧ f.offset % f.align = 0

end C99FieldLayout

/-- Complete C99 aggregate: field intervals, struct alignment, and `sizeof`. -/
structure C99StructLayout where
  name : String
  fields : List C99FieldLayout
  structAlign : Nat
  structSize : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Explicit C99 slice descriptor: pointer, element count, stride, element size,alignment, and backing buffer byte capacity. -/
structure C99SliceDesc where
  dataPtr : Option Nat
  len : Nat
  byteStride : Nat
  elemSize : Nat
  align : Nat
  backingBytes : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Typed C function signature derived from scalar layouts (`retTy = none` represents `void`). -/
structure C99FnSig where
  cSymbol : String
  params : List C99FieldSpec
  retTy : Option C99ScalarType := none
  deriving Repr, DecidableEq, Inhabited

/-- C99 return type spelling (`"void"` when `retTy = none`). -/
def C99FnSig.retCSpelling (sig : C99FnSig) : String :=
  match sig.retTy with
  | some ty => ty.cSpelling
  | none => "void"

/-- Round `n` up to the next positive multiple of `a`; zero alignment fails closed. -/
def c99AlignUp (n a : Nat) : Option Nat :=
  if a = 0 then none else some ((n + (a - 1)) / a * a)

/-- Maximum of two natural numbers. -/
def c99NatMax (a b : Nat) : Nat := if a < b then b else a

/-- Place one field at the next naturally aligned offset for `width`. -/
def placeC99Field (off : Nat) (spec : C99FieldSpec) (width : ArchWidth := .bits64) : Option (C99FieldLayout × Nat) :=
  let sz := spec.ty.sizeOf width
  let al := spec.ty.alignOf width
  match c99AlignUp off al with
  | none => none
  | some aligned =>
    some ({ name := spec.name, ty := spec.ty, offset := aligned, size := sz, align := al }, aligned + sz)

/-- Place every field starting at `off`, returning placed fields and the running maximum alignment. -/
def placeC99FieldsFrom (specs : List C99FieldSpec) (off : Nat) (maxA : Nat) (width : ArchWidth := .bits64) :
    Option (List C99FieldLayout × Nat) :=
  match specs with
  | [] => some ([], maxA)
  | spec :: rs =>
    match placeC99Field off spec width with
    | none => none
    | some (field, nextOff) =>
      match placeC99FieldsFrom rs nextOff (c99NatMax maxA field.align) width with
      | none => none
      | some (restFields, finalAlign) => some (field :: restFields, finalAlign)

/-- Place every field from offset `0` with base alignment `1`. -/
def placeC99Fields (specs : List C99FieldSpec) (width : ArchWidth := .bits64) : Option (List C99FieldLayout × Nat) :=
  placeC99FieldsFrom specs 0 1 width

/-- Rightmost occupied byte of a field list. -/
def c99OccupiedEnd : List C99FieldLayout → Nat
  | [] => 0
  | f :: fs => c99NatMax f.byteEnd (c99OccupiedEnd fs)

/-- Place fields at naturally aligned offsets and round `sizeof` up to the struct alignment. -/
def computeC99StructLayout (name : String) (specs : List C99FieldSpec) (width : ArchWidth := .bits64) :
    Option C99StructLayout :=
  match placeC99Fields specs width with
  | none => none
  | some (placed, maxAlign) =>
    match c99AlignUp (c99OccupiedEnd placed) maxAlign with
    | none => none
    | some sz => some { name, fields := placed, structAlign := maxAlign, structSize := sz }

/-- Two half-open intervals do not overlap. -/
def c99IntervalsDisjoint (a0 a1 b0 b1 : Nat) : Prop :=
  a1 ≤ b0 ∨ b1 ≤ a0

/-- Every pair of distinct field intervals in list order is strictly disjoint. -/
def fieldsPairwiseDisjoint : List C99FieldLayout → Prop
  | [] => True
  | f :: fs => (∀ g ∈ fs, c99IntervalsDisjoint f.offset f.byteEnd g.offset g.byteEnd) ∧ fieldsPairwiseDisjoint fs

/-- A computed layout has positive alignment, aligned fields, disjoint intervals, and covering `sizeof`. -/
def c99LayoutSound (layout : C99StructLayout) (width : ArchWidth := .bits64) : Prop :=
  layout.structAlign ≠ 0 ∧ layout.structAlign ∣ layout.structSize ∧
  (∀ f ∈ layout.fields, f.isAligned ∧ f.size = f.ty.sizeOf width ∧ f.align = f.ty.alignOf width) ∧
  fieldsPairwiseDisjoint layout.fields ∧
  (∀ f ∈ layout.fields, f.byteEnd ≤ layout.structSize)

/-- Checked product bounded by `width.maxAddr`. `none` is the only result on unsigned overflow. -/
def checkedByteLen (len elemBytes : Nat) (width : ArchWidth := .bits64) : Option Nat :=
  if elemBytes = 0 then some 0
  else if len ≤ width.maxAddr / elemBytes then some (len * elemBytes)
  else none

/-- Exact physical byte span `(len - 1) * byteStride + elemSize` (or `0` when `len = 0`)
    for a strided slice, checked against unsigned overflow in `width`. -/
def checkedStridedSpan (len byteStride elemSize : Nat) (width : ArchWidth := .bits64) : Option Nat :=
  if elemSize = 0 ∨ byteStride < elemSize then none
  else if len = 0 then some 0
  else if byteStride = 0 then none
  else if len - 1 ≤ width.maxAddr / byteStride then
    let lastOff := (len - 1) * byteStride
    if lastOff + elemSize < width.addrLimit then some (lastOff + elemSize) else none
  else none

/-- Pure arithmetic byte span of `len` elements with `byteStride` and `elemSize`. -/
def stridedByteSpan (len byteStride elemSize : Nat) : Nat :=
  if len = 0 then 0 else (len - 1) * byteStride + elemSize

/-- A slice is marshalable when its geometry is aligned, its strided byte span fits in `width`
    and `backingBytes`, and any present `dataPtr` is `align`-aligned without pointer wrap-around. -/
def validC99Slice (s : C99SliceDesc) (width : ArchWidth := .bits64) : Prop :=
  s.align ≠ 0 ∧ s.elemSize ≠ 0 ∧ s.elemSize ≤ s.byteStride ∧
  s.byteStride % s.align = 0 ∧ s.elemSize % s.align = 0 ∧
  ∃ span,
    checkedStridedSpan s.len s.byteStride s.elemSize width = some span ∧
    (s.backingBytes = 0 ∨ span ≤ s.backingBytes) ∧
    match s.dataPtr with
    | none => s.len = 0
    | some ptr => ptr % s.align = 0 ∧ ptr + span ≤ width.addrLimit

/-- Validate a slice before a shim may pass it across the C boundary. -/
def validateC99Slice (s : C99SliceDesc) (width : ArchWidth := .bits64) : Bool :=
  s.align != 0 && s.elemSize != 0 && s.elemSize ≤ s.byteStride &&
  s.byteStride % s.align == 0 && s.elemSize % s.align == 0 &&
  match checkedStridedSpan s.len s.byteStride s.elemSize width with
  | none => false
  | some span =>
    (s.backingBytes == 0 || span ≤ s.backingBytes) &&
    match s.dataPtr with
    | none => s.len == 0
    | some ptr => ptr % s.align == 0 && ptr + span ≤ width.addrLimit

/-- Canonical field specification of `lean_native_flat_slice_t`. -/
def flatSliceFieldSpecs : List C99FieldSpec :=
  [ { name := "data", ty := .constPtr },
    { name := "len", ty := .usize },
    { name := "stride_bytes", ty := .usize } ]

/-- Canonical field specification of `lean_native_mut_slice_t`. -/
def mutSliceFieldSpecs : List C99FieldSpec :=
  [ { name := "data", ty := .ptr },
    { name := "len", ty := .usize },
    { name := "cap", ty := .usize } ]

/-- Render a single-line C99 `typedef struct { ... } name;` from a computed `C99StructLayout`. -/
def emitInlineC99Typedef (layout : C99StructLayout) : String :=
  let fields := String.intercalate " " (layout.fields.map fun f => s!"{f.ty.cSpelling} {f.name};")
  s!"typedef struct \{ {fields} } {layout.name};"

/-- Preprocessor guard matching supported 32-bit ILP32 targets with 8-byte `uint64_t` alignment
    (`wasm32`, ARM Thumb/EABI AAPCS, and RISC-V RV32 ILP32), while rejecting x86 `i386` (4-byte `uint64_t` alignment). -/
def ilp32PreprocGuard : String :=
  "#if defined(__wasm32__) || (defined(__ARM_ARCH) && !defined(__aarch64__)) || (defined(__riscv) && (__riscv_xlen == 32))"

/-- Render C11 `_Static_assert`s verifying `sizeof`, `_Alignof`, and `offsetof`
    for computed slice layouts across LP64 and supported ILP32 targets, failing closed on unsupported data models. -/
def emitSliceStaticAsserts (flat64 mut64 flat32 mut32 : C99StructLayout) : List String :=
  let mkChecks (layout : C99StructLayout) : List String :=
    [ s!"_Static_assert(sizeof({layout.name}) == {layout.structSize}, \"{layout.name} size\");",
      s!"_Static_assert(_Alignof({layout.name}) == {layout.structAlign}, \"{layout.name} align\");" ] ++
    layout.fields.map fun f =>
      s!"_Static_assert(offsetof({layout.name}, {f.name}) == {f.offset}, \"{layout.name}.{f.name} offset\");"
  [ "#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L",
    ilp32PreprocGuard ] ++
  mkChecks flat32 ++ mkChecks mut32 ++
  [ "#elif defined(__LP64__) || defined(_LP64)" ] ++
  mkChecks flat64 ++ mkChecks mut64 ++
  [ "#else",
    "#error \"Unsupported ABI data model: LeanNative C-ABI requires LP64 or wasm32\"",
    "#endif",
    "#endif" ]

/-- Render target-specific C11 `_Static_assert`s when an explicit `ArchWidth` is pinned,
    failing closed via `#error` on target/data-model mismatch. -/
def emitPinnedSliceStaticAsserts (flatLayout mutLayout : C99StructLayout)
    (width : ArchWidth := .bits64) : List String :=
  let (archGuard, errLine) :=
    match width with
    | .bits32 =>
      (ilp32PreprocGuard,
       "#error \"Mismatched or unsupported C-ABI target: pinned to wasm32 (32-bit)\"")
    | .bits64 =>
      ("#if defined(__LP64__) || defined(_LP64)",
       "#error \"Mismatched or unsupported C-ABI target: pinned to LP64 (64-bit)\"")
  let mkChecks (layout : C99StructLayout) : List String :=
    [ s!"_Static_assert(sizeof({layout.name}) == {layout.structSize}, \"{layout.name} size\");",
      s!"_Static_assert(_Alignof({layout.name}) == {layout.structAlign}, \"{layout.name} align\");" ] ++
    layout.fields.map fun f =>
      s!"_Static_assert(offsetof({layout.name}, {f.name}) == {f.offset}, \"{layout.name}.{f.name} offset\");"
  [ "#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L",
    archGuard ] ++
  mkChecks flatLayout ++ mkChecks mutLayout ++
  [ "#else",
    errLine,
    "#endif",
    "#endif" ]

def lnirTypeToRustType : LNIRType → String
  | .i1 | .i8 => "u8" | .i16 | .f16 => "u16" | .i32 => "u32" | .i64 | .tuple _ => "u64"
  | .usize => "usize" | .u256 | .i256 => "*const u64" | .f32 => "f32" | .f64 => "f64"
  | .rawPtr .i8 => "*mut u8" | .rawPtr .i16 => "*mut u16" | .rawPtr .i32 => "*const u32"
  | .rawPtr _ | .sarray _ | .objPtr | .taggedPtr | .storageMap => "*mut core::ffi::c_void" | .unit => "()"

structure CAbiBindingSig where
  cSymbol : String
  leanName : String
  params : List (String × String × String) -- (paramName, cType, rustType)
  retCType : String
  retRustType : String
  /-- Source-text signature (`def … :=` prefix) the binding was parsed from; empty for LNIR-derived sigs. -/
  srcSig : String := ""
  deriving Repr, Inhabited

/-- Convert a parsed or LNIR-derived `CAbiBindingSig` into a typed `C99FnSig`. -/
def CAbiBindingSig.toC99FnSig (s : CAbiBindingSig) : Option C99FnSig := do
  let typedParams ← s.params.mapM fun (nm, cTy, _) => do
    let ty ← C99ScalarType.ofCSpelling? cTy
    pure ({ name := nm, ty } : C99FieldSpec)
  let retRaw := s.retCType.trimAscii.toString
  let retOpt ←
    if retRaw == "void" then some none
    else (C99ScalarType.ofCSpelling? retRaw).map some
  some { cSymbol := s.cSymbol, params := typedParams, retTy := retOpt }

/-- Emit a C99 function prototype from a typed `C99FnSig`. -/
def emitC99FnProto (sig : C99FnSig) : String :=
  let params :=
    if sig.params.isEmpty then "void"
    else String.intercalate ", " (sig.params.map fun p => s!"{p.ty.cSpelling} {p.name}")
  s!"{sig.retCSpelling} {sig.cSymbol}({params});"

def mapLeanTypeStr (tyRaw : String) : String × String :=
  let raw := tyRaw.trimAscii.toString
  let t := (if raw.startsWith "@&" then (raw.drop 2).trimAscii else raw.trimAscii).toString
  if t == "Bool" || t == "UInt8" then ("uint8_t", "u8")
  else if t == "UInt16" then ("uint16_t", "u16")
  else if t == "UInt32" then ("uint32_t", "u32")
  else if t == "UInt64" || t == "Nat" then ("uint64_t", "u64")
  else if t == "Int64" || t == "Int" then ("int64_t", "i64")
  else if t == "USize" then ("size_t", "usize")
  else if t == "Float" then ("double", "f64")
  else if t == "Unit" then ("void", "()")
  else if t == "ByteArray" || t == "ConstBytes" then ("const uint8_t*", "*const u8")
  else if t == "MutBytes" then ("uint8_t*", "*mut u8")
  else if t == "ConstU32s" then ("const uint32_t*", "*const u32")
  else if t == "MutU16s" then ("uint16_t*", "*mut u16")
  else ("const void*", "*const core::ffi::c_void")

/-- `(names : Ty)` groups as `(name, rawTy)`; a group without `:` yields `(…, "")`. -/
private def parseParamGroupsRaw (sig : String) : List (String × String) :=
  ((sig.splitOn "(").drop 1).foldl (fun acc g =>
    match (g.splitOn ")").head? with
    | some inside =>
      match inside.splitOn ":" with
      | namesStr :: tyStr :: _ =>
        let names := (namesStr.splitOn " ").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
        acc ++ names.map (fun n => (n, tyStr.trimAscii.toString))
      | _ => acc ++ [(inside.trimAscii.toString, "")]
    | none => acc) []

private def parseParamGroups (sig : String) : List (String × String × String) :=
  (parseParamGroupsRaw sig).map fun (n, ty) => let (cTy, rsTy) := mapLeanTypeStr ty; (n, cTy, rsTy)

/-- Raw return type text; `none` when the signature has no explicit `: Ty` after its binders. -/
private def extractReturnTypeRaw? (sig : String) : Option String :=
  let afterParens := match (sig.splitOn ")").reverse.head? with | some s => s | none => sig
  let beforeEq := (afterParens.splitOn ":=").headD afterParens
  ((beforeEq.splitOn ":").drop 1).reverse.head?.map (·.trimAscii.toString)

/-- A returned mutable buffer is the caller's own pointer and has no C return value:
    `MutBytes` is `void`, `MutBytes × T` is `T`. -/
private def dropReturnedMutBuf (ty : String) : String :=
  match (ty.splitOn "×").map (·.trimAscii.toString) with
  | [b] => if b == "MutBytes" || b == "MutU16s" then "Unit" else ty
  | [b, t] => if b == "MutBytes" || b == "MutU16s" then t else ty
  | _ => ty

private def extractReturnTypeStr (sig : String) : String × String :=
  mapLeanTypeStr (dropReturnedMutBuf ((extractReturnTypeRaw? sig).getD "UInt64"))

/-- Extract `@[export <sym>]` / `@[inline, export <sym>]` signatures and `#guard` fixtures from `.lean` source text. -/
def extractLeanSourceCAbiAndGuards (raw : String) : List CAbiBindingSig × List (String × String) :=
  let lines := raw.splitOn "\n"
  let rec loop (ls : List String) (pendSym : Option String) (sigs : List CAbiBindingSig) (guards : List (String × String)) :
      List CAbiBindingSig × List (String × String) :=
    match ls with
    | [] => (sigs.reverse, guards.reverse)
    | line :: rest =>
      let tr := line.trimAscii.toString
      let guards' :=
        if tr.startsWith "#guard " then
          let expr := (tr.drop 7).trimAscii.toString
          match expr.splitOn "==" with
          | lhs :: rhs :: _ => (lhs.trimAscii.toString, rhs.trimAscii.toString) :: guards
          | _ => (expr, "true") :: guards
        else guards
      let symOpt :=
        match tr.splitOn "export " with
        | _ :: afterExp :: _ =>
          if tr.startsWith "@[" then
            let tok := String.ofList (afterExp.trimAscii.toString.toList.takeWhile (fun c => c != ']' && c != ',' && c != ' '))
            if tok.isEmpty then pendSym else some tok
          else pendSym
        | _ => pendSym
      if tr.startsWith "def " || tr.startsWith "abbrev " then
        match symOpt with
        | some sym =>
          let headerLines := tr :: (rest.take 12 |>.takeWhile (fun l =>
            let t := l.trimAscii.toString
            !(t.startsWith "def ") && !(t.startsWith "@[") && !(t.startsWith "/--") && !(t.startsWith "--")))
          let fullSig := String.intercalate " " (headerLines.map (·.trimAscii.toString))
          let sigHead := (fullSig.splitOn ":=").headD fullSig
          let afterDef := (sigHead.drop 4).trimAscii.toString
          let leanName := String.ofList (afterDef.toList.takeWhile (fun c => c != ' ' && c != '(' && c != ':'))
          let params := parseParamGroups sigHead
          let (retC, retRs) := extractReturnTypeStr sigHead
          loop rest none ({ cSymbol := sym, leanName, params, retCType := retC, retRustType := retRs, srcSig := sigHead } :: sigs) guards'
        | none => loop rest none sigs guards'
      else loop rest symOpt sigs guards'
  loop lines none [] []

/-- Lean types with an unboxed scalar C-ABI representation that `mapLeanTypeStr` maps faithfully.
    `Nat`/`Int` are boxed `lean_object*` at the Lean ABI, so they are deliberately absent. -/
def scalarCAbiLeanTypes : List String := ["Bool", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float", "Int64"]

/-- Provenance recorded in every `--signatures-only` artifact. -/
def signaturesOnlyMarker : String := "signatures-only: no Stage1D gate applied"

/-- P-cert C4 `--signatures-only`: bindings from exported source signatures alone, with no elaboration and hence no
    Stage 1D (RC-ADT) gate. Fails closed on: no export; an `@[… export …]` line not immediately followed by a plain
    `def`/`abbrev` (so every export attribute binds the declaration it annotates); implicit/instance binders; and any
    exported parameter or return type outside `scalarCAbiLeanTypes`. Only exported signatures are emitted, never
    helper prototypes or RC-ADT runtime declarations. -/
def extractSignaturesOnlyCAbi (raw : String) : Except String (List CAbiBindingSig × List (String × String)) := do
  let (sigs, guards) := extractLeanSourceCAbiAndGuards raw
  if sigs.isEmpty then throw "no `@[export]` signatures found"
  let lines := (raw.splitOn "\n").map (·.trimAscii.toString)
  let attrs := (lines.zip (lines.drop 1 ++ [""])).filter fun (l, _) => l.startsWith "@[" && (l.splitOn "export ").length > 1
  if let some (l, _) := attrs.find? fun (_, nxt) => !(nxt.startsWith "def " || nxt.startsWith "abbrev ") then
    throw s!"export attribute '{l}' is not immediately followed by a plain `def`/`abbrev`"
  if attrs.length != sigs.length then throw s!"{attrs.length} export attributes but {sigs.length} parsed signatures"
  for s in sigs do
    if (s.srcSig.splitOn "(").length != (s.srcSig.splitOn ")").length then
      throw s!"exported '{s.leanName}' ({s.cSymbol}) has an unparsed signature '{s.srcSig}'"
    if ["{", "[", "⦃"].any (fun b => (s.srcSig.splitOn b).length > 1) then
      throw s!"exported '{s.leanName}' ({s.cSymbol}) has an implicit/instance binder"
    let tys := (s.srcSig |> parseParamGroupsRaw).map (·.2) ++ [(extractReturnTypeRaw? s.srcSig).getD ""]
    if let some ty := tys.find? (!scalarCAbiLeanTypes.contains ·) then
      throw s!"exported '{s.leanName}' ({s.cSymbol}) has non-scalar type '{ty}'"
  return (sigs, guards)

def moduleToCAbiSigs (m : LNIRModule) : List CAbiBindingSig :=
  m.decls.map fun d => {
    cSymbol := d.name, leanName := d.name,
    params := d.params.map (fun p =>
      let cTy := if p.ty == .unit then "const void*" else lnirTypeToCType p.ty
      let rsTy := if p.ty == .unit then "*const core::ffi::c_void" else lnirTypeToRustType p.ty
      (p.name.replace "'" "_prime", cTy, rsTy)),
    retCType := lnirTypeToCType d.retTy, retRustType := lnirTypeToRustType d.retTy
  }

def readLeanSourceExpandingUmbrella (filePath : String) : IO String := do
  let raw ← try IO.FS.readFile filePath catch _ => pure ""
  if !filePath.endsWith ".lean" then return raw
  let subDir := System.FilePath.mk ((filePath.dropEnd 5).toString)
  if !(← subDir.pathExists) then return raw
  let stem := subDir.fileName.getD ""
  let mut outLines : Array String := #[]
  for line in raw.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "import " then
      let modPath := (trimmed.drop 7).trimAscii.toString
      let parts := modPath.splitOn "."
      match parts.reverse with
      | leaf :: parent :: _ =>
        let candPath := subDir / s!"{leaf}.lean"
        if parent == stem && (← candPath.pathExists) then
          let subRaw ← IO.FS.readFile candPath
          for subLine in subRaw.splitOn "\n" do
            if !subLine.trimAscii.toString.startsWith "import " then
              outLines := outLines.push subLine
        else
          outLines := outLines.push line
      | _ => outLines := outLines.push line
    else
      outLines := outLines.push line
  return String.intercalate "\n" outLines.toList

/-- `note?` (e.g. `signaturesOnlyMarker`) is recorded as provenance metadata in every emitted artifact.
    Slice typedefs (`lean_native_flat_slice_t`, `lean_native_mut_slice_t`) and C11 `_Static_assert`s
    are derived directly from `computeC99StructLayout` across `ArchWidth` (`24` bytes on 64-bit LP64,
    `12` bytes on 32-bit `wasm32`), and exported function prototypes route through typed `C99FnSig`. -/
def emitCAbiHeaderFromSigs (sigs : List CAbiBindingSig) (note? : Option String := none)
    (width? : Option ArchWidth := none) : String :=
  let declProtos := sigs.map fun s =>
    match s.toC99FnSig with
    | some fnSig => emitC99FnProto fnSig
    | none =>
      let paramsC :=
        if s.params.isEmpty then "void"
        else String.intercalate ", " (s.params.map fun (n, cTy, _) => s!"{cTy} {n}")
      s!"{s.retCType} {s.cSymbol}({paramsC});"
  let activeWidth := width?.getD .bits64
  let flat64 := (computeC99StructLayout "lean_native_flat_slice_t" flatSliceFieldSpecs .bits64).getD
    { name := "lean_native_flat_slice_t", fields := [], structAlign := 8, structSize := 24 }
  let mut64 := (computeC99StructLayout "lean_native_mut_slice_t" mutSliceFieldSpecs .bits64).getD
    { name := "lean_native_mut_slice_t", fields := [], structAlign := 8, structSize := 24 }
  let flat32 := (computeC99StructLayout "lean_native_flat_slice_t" flatSliceFieldSpecs .bits32).getD
    { name := "lean_native_flat_slice_t", fields := [], structAlign := 4, structSize := 12 }
  let mut32 := (computeC99StructLayout "lean_native_mut_slice_t" mutSliceFieldSpecs .bits32).getD
    { name := "lean_native_mut_slice_t", fields := [], structAlign := 4, structSize := 12 }
  let activeFlat := if activeWidth == .bits32 then flat32 else flat64
  let activeMut := if activeWidth == .bits32 then mut32 else mut64
  let staticAsserts := match width? with
    | some .bits32 => emitPinnedSliceStaticAsserts flat32 mut32 .bits32
    | some .bits64 => emitPinnedSliceStaticAsserts flat64 mut64 .bits64
    | none => emitSliceStaticAsserts flat64 mut64 flat32 mut32
  let widthTag := if activeWidth == .bits32 then "ILP32 (wasm32 / ARM Thumb / RV32)" else "LP64"
  String.intercalate "\n" ([
    "/* Auto-generated C99 Header by lean-native C-ABI Binding Generator */",
    s!"/* ABI Slice Layout ({widthTag}): sizeof({activeFlat.name}) == {activeFlat.structSize}, " ++
      s!"alignof == {activeFlat.structAlign} */"] ++
    (note?.map (s!"/* {·} */")).toList ++ [
    "#pragma once",
    "#ifndef LEAN_NATIVE_GENERATED_C_ABI_H",
    "#define LEAN_NATIVE_GENERATED_C_ABI_H",
    "#include <stdint.h>",
    "#include <stddef.h>",
    "#include <stdbool.h>",
    emitInlineC99Typedef activeFlat,
    emitInlineC99Typedef activeMut,
    "/* Zero-Runtime SliceOut C-ABI Contract: packed u64 span (start:32 | len:24 | kind:8) */",
    "typedef uint32_t (*lean_native_slice_out_scan_fn)(",
    "    const uint8_t* ptr, size_t len, uint64_t* out_spans, size_t cap, uint64_t* state_io);",
    "static inline uint64_t lean_native_pack_span(uint32_t start, uint32_t len, uint8_t kind) {",
    "    return ((uint64_t)start << 32) | ((uint64_t)(len & 0xFFFFFFU) << 8) | (uint64_t)kind;",
    "}",
    "static inline uint32_t lean_native_span_start(uint64_t span) {",
    "    return (uint32_t)(span >> 32);",
    "}",
    "static inline uint32_t lean_native_span_len(uint64_t span) {",
    "    return (uint32_t)((span >> 8) & 0xFFFFFFU);",
    "}",
    "static inline uint8_t lean_native_span_kind(uint64_t span) {",
    "    return (uint8_t)(span & 0xFFU);",
    "}"
  ] ++ staticAsserts ++ [
    "#ifdef __cplusplus",
    "extern \"C\" {",
    "#endif"
  ] ++ declProtos ++ [
    "#ifdef __cplusplus",
    "}",
    "#endif",
    "#endif /* LEAN_NATIVE_GENERATED_C_ABI_H */",
    ""])

/-- Generate ABI declarations and forwarding wrappers only; domain execution stays in the compiled library. -/
def emitCAbiRustFromSigs (sigs : List CAbiBindingSig) (note? : Option String := none) : String :=
  let declExterns := sigs.map fun s =>
    let paramsRs := String.intercalate ", " (s.params.map fun (n, _, rsTy) => s!"{n}: {rsTy}")
    let retPart := if s.retRustType == "()" then "" else s!" -> {s.retRustType}"
    s!"        pub fn {s.cSymbol}({paramsRs}){retPart};"
  let declWrappers := sigs.map fun s =>
    let retPart := if s.retRustType == "()" then "" else s!" -> {s.retRustType}"
    let paramsRs := String.intercalate ", " (s.params.map fun (n, _, rsTy) => s!"{n}: {rsTy}")
    let argsRs := String.intercalate ", " (s.params.map fun (n, _, _) => n)
    String.intercalate "\n" [
      "#[cfg_attr(not(debug_assertions), inline(always))]",
      s!"pub unsafe fn {s.cSymbol}({paramsRs}){retPart} \{",
      s!"    unsafe \{ c_abi::{s.cSymbol}({argsRs}) }",
      "}"
    ]
  String.intercalate "\n" ([
    "// Generated ABI forwarding wrappers; no independent Rust kernel implementation."
  ] ++ (note?.map (s!"// {·}")).toList ++ [
    "pub mod c_abi {",
    "    extern \"C\" {"
  ] ++ declExterns ++ ["    }", "}"] ++ declWrappers ++ [""])

def emitGuardFixturesJson (sourcePath : String) (sigs : List CAbiBindingSig) (guards : List (String × String))
    (note? : Option String := none) : String :=
  let esc := LeanNative.IR.jsonEscape
  let expJson := String.intercalate "," (sigs.map fun s =>
    s!"\{\"c_symbol\":\"{esc s.cSymbol}\",\"lean_name\":\"{esc s.leanName}\"," ++
      s!"\"arity\":{s.params.length},\"ret_c\":\"{esc s.retCType}\"," ++
      s!"\"ret_rust\":\"{esc s.retRustType}\"}")
  let prov := match note? with | some n => "\"provenance\":\"" ++ esc n ++ "\"," | none => ""
  let gJson := String.intercalate "," (guards.map fun (lhs, rhs) =>
    s!"\{\"expr\":\"{esc lhs}\",\"expected\":\"{esc rhs}\"}")
  s!"\{\"schema\":\"lean-native.cabi-fixtures.v1\",\"source\":\"{esc sourcePath}\"," ++
    s!"{prov}\"exports_count\":{sigs.length},\"guards_count\":{guards.length}," ++
    s!"\"exports\":[{expJson}],\"guards\":[{gJson}]}\n"

private def cTypeToSwiftType (cTy : String) : String :=
  if cTy == "uint8_t" then "UInt8"
  else if cTy == "int8_t" then "Int8"
  else if cTy == "bool" || cTy == "_Bool" then "Bool"
  else if cTy == "uint16_t" then "UInt16"
  else if cTy == "int16_t" then "Int16"
  else if cTy == "uint32_t" then "UInt32"
  else if cTy == "int32_t" then "Int32"
  else if cTy == "uint64_t" then "UInt64"
  else if cTy == "size_t" then "Int"
  else if cTy == "int64_t" then "Int64"
  else if cTy == "float" then "Float"
  else if cTy == "double" then "Double"
  else if cTy == "void" then "Void"
  else if cTy == "const uint8_t*" then "UnsafePointer<UInt8>?"
  else if cTy == "uint8_t*" then "UnsafeMutablePointer<UInt8>?"
  else if cTy == "const uint16_t*" then "UnsafePointer<UInt16>?"
  else if cTy == "uint16_t*" then "UnsafeMutablePointer<UInt16>?"
  else if cTy == "const uint32_t*" then "UnsafePointer<UInt32>?"
  else if cTy == "uint32_t*" then "UnsafeMutablePointer<UInt32>?"
  else if cTy == "const uint64_t*" then "UnsafePointer<UInt64>?"
  else if cTy == "uint64_t*" then "UnsafeMutablePointer<UInt64>?"
  else if cTy == "const double*" then "UnsafePointer<Double>?"
  else if cTy == "double*" then "UnsafeMutablePointer<Double>?"
  else if cTy == "void*" then "UnsafeMutableRawPointer?"
  else "UnsafeRawPointer?"

/-- Emit a Clang module map (`module.modulemap`) for Xcode / SwiftPM zero-copy C-ABI interop. -/
def emitModuleMap (moduleName : String := "TurboLeanCABI") (headerFile : String := "turbo_lean_cabi.h")
    (note? : Option String := none) : String :=
  (match note? with | some n => "// " ++ n ++ "\n" | none => "") ++ s!"module {moduleName} \{\n  header \"{headerFile}\"\n  export *\n}\n"

/-- Emit zero-copy Swift `@_silgen_name` C-ABI bindings (`TurboLeanKit.swift`) for iOS / macOS (`apple-a15`). -/
def emitCAbiSwiftFromSigs (sigs : List CAbiBindingSig) (enumName : String := "TurboLeanKernel")
    (note? : Option String := none) : String :=
  let externDecls := sigs.map fun s =>
    let paramsSw := String.intercalate ", " (s.params.map fun (n, cTy, _) => s!"_ {n}: {cTypeToSwiftType cTy}")
    let retSw := cTypeToSwiftType s.retCType
    s!"@_silgen_name(\"{s.cSymbol}\")\npublic func {s.cSymbol}({paramsSw}) -> {retSw}"
  let enumMethods := sigs.map fun s =>
    let paramsSw := String.intercalate ", " (s.params.map fun (n, cTy, _) => s!"_ {n}: {cTypeToSwiftType cTy}")
    let argsSw := String.intercalate ", " (s.params.map fun (n, _, _) => n)
    let retSw := cTypeToSwiftType s.retCType
    s!"  @inlinable public static func {s.leanName}({paramsSw}) -> {retSw} \{\n    {s.cSymbol}({argsSw})\n  }"
  String.intercalate "\n" ([
    "// Auto-generated Zero-Copy Swift C-ABI Bridge by lean-native (iOS / apple-a15)"] ++
    (note?.map (s!"// {·}")).toList ++ [
    "import Foundation",
    ""
  ] ++ externDecls ++ [
    "",
    s!"public enum {enumName} \{"
  ] ++ enumMethods ++ ["}", ""])

/-- Emit a C-ABI header (`.h`) for an `LNIRModule` parameterized by target `TargetArch`. -/
def emitCAbiHeader (m : LNIRModule) (arch : TargetArch := .x86_64) : String :=
  emitCAbiHeaderFromSigs (moduleToCAbiSigs m) none (some (ArchWidth.ofTargetArch arch))

/-- Publish one file by POSIX rename from an exclusively reserved sibling directory.
    Preserves any previous file on staging failure; power-loss durability is assumed. -/
def writeBinaryAtomic (path : String) (bytes : ByteArray) : IO Unit := do
  let nonce ← IO.monoNanosNow
  let stage := s!"{path}.tmp.{nonce}.stage"
  IO.FS.createDir stage
  try
    let payload := System.FilePath.mk stage / "payload"
    IO.FS.writeBinFile payload bytes
    IO.FS.rename payload path
  finally
    try IO.FS.removeDirAll stage catch _ => pure ()

def writeTextAtomic (path : String) (text : String) : IO Unit :=
  writeBinaryAtomic path text.toUTF8

/-- Publish an immutable artifact generation through one atomic symlink rename.
    Readers needing a multi-file snapshot resolve `bundle` once and use that
    generation directory. Old generations remain valid for concurrent readers.
    POSIX rename atomicity is assumed; power-loss durability is not claimed. -/
def publishArtifactBundle (bundle : String) (artifacts : List (String × ByteArray)) : IO String := do
  let bundlePath := System.FilePath.mk bundle
  match ← bundlePath.symlinkMetadata.toBaseIO with
  | .ok metadata =>
    if metadata.type != .symlink then
      throw <| IO.userError "Artifact bundle destination must be absent or a generation symlink"
  | .error _ => pure ()
  let names := artifacts.map (fun (name, _) => (System.FilePath.mk name).fileName.getD "")
  if names.any (fun n => n.isEmpty || n == "." || n == "..") || names.eraseDups.length != names.length then
    throw <| IO.userError "Artifact bundle members must have distinct file names"
  let nonce ← IO.monoNanosNow
  let generation := s!"{bundle}.gen.{nonce}"
  let pointer := s!"{generation}/.pointer"
  IO.FS.createDir generation -- exclusive reservation; collisions fail closed
  try
    for ((_, bytes), name) in artifacts.zip names do
      IO.FS.writeBinFile (System.FilePath.mk generation / name) bytes
    let generationAbs ← IO.FS.realPath generation
    let linked ← IO.Process.output { cmd := "ln", args := #["-s", generationAbs.toString, pointer] }
    if linked.exitCode != 0 then throw <| IO.userError s!"Failed to stage artifact bundle pointer: {linked.stderr}"
    if (← (System.FilePath.mk pointer).symlinkMetadata).type != .symlink ||
        (← IO.FS.realPath pointer) != generationAbs then
      throw <| IO.userError "Artifact bundle pointer failed verification"
    IO.FS.rename pointer bundle
    pure generationAbs.toString
  catch e =>
    try IO.FS.removeFile pointer catch _ => pure ()
    try IO.FS.removeDirAll generation catch _ => pure ()
    throw e

private def readU16LE (b : ByteArray) (off : Nat) : UInt16 :=
  if off + 1 < b.size then
    let b0 := (b.get! off).toUInt16
    let b1 := (b.get! (off + 1)).toUInt16
    b0 ||| (b1 <<< 8)
  else 0

private def readU32LE (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 3 < b.size then
    let b0 := (b.get! off).toUInt32
    let b1 := (b.get! (off + 1)).toUInt32
    let b2 := (b.get! (off + 2)).toUInt32
    let b3 := (b.get! (off + 3)).toUInt32
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
  else 0

private def checkMachOLoadCmds (b : ByteArray) (limit : Nat) : Nat → Nat → Option UInt32 → Option UInt32
  | 0, off, foundPlat => if off == limit then foundPlat else none
  | f + 1, off, foundPlat =>
    if off + 8 > limit then none
    else
      let cmd := readU32LE b off
      let cmdsize := (readU32LE b (off + 4)).toNat
      if cmdsize < 8 || cmdsize % 8 != 0 || off + cmdsize > limit then none
      else if cmd == 0x32 then
        if cmdsize < 24 || foundPlat.isSome then none
        else checkMachOLoadCmds b limit f (off + cmdsize) (some (readU32LE b (off + 8)))
      else
        checkMachOLoadCmds b limit f (off + cmdsize) foundPlat

/-- Check object format and CPU headers, plus Apple's platform load command.
    ELF headers do not distinguish Linux from Android or establish runtime ABI compatibility.
    These checks are not a complete object/linker or runtime validation.
    - `.x86_64` -> ELF64 (`\x7fELF\x02\x01`, `>= 64` bytes), `e_type == 1` (`ET_REL`), `e_machine == 0x3E` (`EM_X86_64`)
    - `.arm64` / `.androidArm64` -> ELF64 (`\x7fELF\x02\x01`, `>= 64` bytes), `e_type == 1` (`ET_REL`), `e_machine == 0xB7` (`EM_AARCH64`)
    - `.macosArm64` -> Mach-O 64-bit (`0xFEEDFACF`, `>= 32` bytes), `cputype == 0x0100000C` (`CPU_TYPE_ARM64`),
      `filetype == 1` (`MH_OBJECT`), `LC_BUILD_VERSION` (`cmd == 0x32`) with `platform == 1` (`PLATFORM_MACOS`)
    - `.iosArm64` -> Mach-O 64-bit (`0xFEEDFACF`, `>= 32` bytes), `cputype == 0x0100000C`, `filetype == 1` (`MH_OBJECT`),
      `LC_BUILD_VERSION` (`cmd == 0x32`) with `platform == 2` (`PLATFORM_IOS`)
    - `.iosSimArm64` -> Mach-O 64-bit (`0xFEEDFACF`, `>= 32` bytes), `cputype == 0x0100000C`, `filetype == 1` (`MH_OBJECT`),
      `LC_BUILD_VERSION` (`cmd == 0x32`) with `platform == 7` (`PLATFORM_IOSSIMULATOR`)
    - `.wasm32` -> WebAssembly binary magic (`\x00asm\x01\x00\x00\x00`, `> 8` bytes)
    - All other targets fail closed (`false`). -/
def verifyObjectBytesForTarget (arch : TargetArch) (b : ByteArray) : Bool × String :=
  if b.size < 32 then (false, s!"artifact too small ({b.size} bytes < 32)")
  else
    match arch with
    | .x86_64 =>
      let isElf64 := b.size >= 64 && b.get! 0 == 0x7F && b.get! 1 == 0x45 &&
        b.get! 2 == 0x4C && b.get! 3 == 0x46 && b.get! 4 == 2 && b.get! 5 == 1
      let etype := readU16LE b 16
      let mach := readU16LE b 18
      if !isElf64 then (false, "expected ELF64 little-endian header (>= 64 bytes)")
      else if etype != 1 then (false, s!"expected ELF relocatable object e_type=1 (ET_REL), got {etype}")
      else if mach != 0x3E then (false, s!"expected ELF e_machine=0x3E (EM_X86_64), got {mach}")
      else (true, "ELF64 ET_REL EM_X86_64; OS/ABI not verified")
    | .arm64 | .androidArm64 =>
      let isElf64 := b.size >= 64 && b.get! 0 == 0x7F && b.get! 1 == 0x45 &&
        b.get! 2 == 0x4C && b.get! 3 == 0x46 && b.get! 4 == 2 && b.get! 5 == 1
      let etype := readU16LE b 16
      let mach := readU16LE b 18
      if !isElf64 then (false, "expected ELF64 little-endian header (>= 64 bytes)")
      else if etype != 1 then (false, s!"expected ELF relocatable object e_type=1 (ET_REL), got {etype}")
      else if mach != 0xB7 then (false, s!"expected ELF e_machine=0xB7 (EM_AARCH64), got {mach}")
      else (true, "ELF64 ET_REL EM_AARCH64; OS/ABI not verified")
    | .macosArm64 | .iosArm64 | .iosSimArm64 =>
      let magic := readU32LE b 0
      let cputype := readU32LE b 4
      let filetype := readU32LE b 12
      let ncmds := (readU32LE b 16).toNat
      let sizeofcmds := (readU32LE b 20).toNat
      let expectedPlat : UInt32 :=
        match arch with
        | .macosArm64  => 1
        | .iosArm64    => 2
        | .iosSimArm64 => 7
        | _            => 0
      if magic != 0xFEEDFACF then (false, s!"expected Mach-O 64-bit magic 0xFEEDFACF, got {magic}")
      else if cputype != 0x0100000C then (false, s!"expected Mach-O CPU_TYPE_ARM64 (0x0100000C), got {cputype}")
      else if filetype != 1 then (false, s!"expected Mach-O MH_OBJECT (filetype=1), got {filetype}")
      else if 32 + sizeofcmds > b.size then (false, s!"Mach-O load commands exceed object size ({32 + sizeofcmds} > {b.size})")
      else
        match checkMachOLoadCmds b (32 + sizeofcmds) ncmds 32 none with
        | some plat =>
          if plat == expectedPlat then (true, s!"Mach-O ARM64 platform={plat}")
          else (false, s!"Mach-O platform mismatch: expected platform={expectedPlat} for {arch.triple}, got platform={plat}")
        | none => (false, "Mach-O missing LC_BUILD_VERSION (0x32) platform load command")
    | .wasm32 =>
      let isWasm := b.size > 8 && b.get! 0 == 0x00 && b.get! 1 == 0x61 && b.get! 2 == 0x73 && b.get! 3 == 0x6D &&
                    b.get! 4 == 0x01 && b.get! 5 == 0x00 && b.get! 6 == 0x00 && b.get! 7 == 0x00
      if isWasm then (true, "WASM32 v1")
      else (false, "expected WebAssembly binary magic (\\x00asm\\x01\\x00\\x00\\x00)")
    | .thumbv6m | .thumbv8mMain =>
      let isElf32 := b.size >= 52 && b.get! 0 == 0x7F && b.get! 1 == 0x45 &&
        b.get! 2 == 0x4C && b.get! 3 == 0x46 && b.get! 4 == 1 && b.get! 5 == 1
      let etype := readU16LE b 16
      let mach := readU16LE b 18
      if !isElf32 then (false, "expected ELF32 little-endian header (>= 52 bytes)")
      else if etype != 1 then (false, s!"expected ELF relocatable object e_type=1 (ET_REL), got {etype}")
      else if mach != 0x28 then (false, s!"expected ELF e_machine=0x28 (EM_ARM), got {mach}")
      else (true, "ELF32 ET_REL EM_ARM")
    | .riscv32imac =>
      let isElf32 := b.size >= 52 && b.get! 0 == 0x7F && b.get! 1 == 0x45 &&
        b.get! 2 == 0x4C && b.get! 3 == 0x46 && b.get! 4 == 1 && b.get! 5 == 1
      let etype := readU16LE b 16
      let mach := readU16LE b 18
      if !isElf32 then (false, "expected ELF32 little-endian header (>= 52 bytes)")
      else if etype != 1 then (false, s!"expected ELF relocatable object e_type=1 (ET_REL), got {etype}")
      else if mach != 0xF3 then (false, s!"expected ELF e_machine=0xF3 (EM_RISCV), got {mach}")
      else (true, "ELF32 ET_REL EM_RISCV")
    | _ => (false, s!"unsupported binary object verification target: {arch.triple}")

/-- Require exactly one complete non-index member equal to the compiled object.
    Parse the whole archive: substrings, trailing junk and extra objects fail. -/
def verifyStaticArchiveBytes (b expectedObj : ByteArray) : Bool :=
  if expectedObj.size == 0 || String.fromUTF8! (b.extract 0 8) != "!<arch>\n" then false
  else
    let rec members (off count fuel : Nat) : Bool :=
      if off == b.size then count == 1
      else match fuel with
      | 0 => false
      | fuel + 1 =>
        if off + 60 > b.size || b.get! (off + 58) != 0x60 || b.get! (off + 59) != 0x0A then false
        else
          let sizeText := (String.fromUTF8! (b.extract (off + 48) (off + 58))).trimAscii.toString
          match sizeText.toNat? with
          | none => false
          | some size =>
            let start := off + 60
            let stop := start + size
            let next := stop + size % 2
            if stop > b.size || next > b.size || (size % 2 == 1 && b.get! stop != 10) then false
            else
              let rawName := (String.fromUTF8! (b.extract off (off + 16))).trimAscii.toString
              let nameLen := if rawName.startsWith "#1/" then (rawName.drop 3).toString.toNat? else some 0
              match nameLen with
              | none => false
              | some n =>
                if n > size then false
                else
                  let nulSep := String.singleton (Char.ofNat 0)
                  let name :=
                    if n == 0 then rawName
                    else ((String.fromUTF8! (b.extract start (start + n))).splitOn nulSep).headD "" |>.trimAscii.toString
                  let isIndex := name == "/" || name == "//" || name == "/SYM64/" ||
                    name == "__.SYMDEF" || name == "__.SYMDEF SORTED"
                  if isIndex then members next count fuel
                  else if count != 0 || b.extract (start + n) stop != expectedObj then false
                  else members next (count + 1) fuel
    members 8 0 b.size

def verifyStaticArchiveFile (path : String) (expectedObj : ByteArray) : IO (Bool × String) := do
  if !(← System.FilePath.pathExists path) then
    return (false, s!"archive '{path}' does not exist")
  let b ← IO.FS.readBinFile path
  return if verifyStaticArchiveBytes b expectedObj then
    (true, "parsed archive with exactly one byte-identical object member")
  else (false, s!"archive '{path}' is malformed or does not bind exactly the expected object")

/-- Host byte view used by the pure marshal and unmarshal functions. -/
structure C99ByteView where
  bytes : ByteArray
  base : Nat
  len : Nat
  byteStride : Nat := 0
  elemSize : Nat
  align : Nat := 1
  width : ArchWidth := .bits64
  deriving DecidableEq, Inhabited

/-- The effective byte stride of a view (`elemSize` when `byteStride = 0`). -/
def C99ByteView.effectiveStride (v : C99ByteView) : Nat :=
  if v.byteStride = 0 then v.elemSize else v.byteStride

/-- A view stays inside its backing array, is aligned, and its strided span does not wrap `width`. -/
def C99ByteView.isValid (v : C99ByteView) : Prop :=
  v.align ≠ 0 ∧ v.elemSize ≠ 0 ∧ v.elemSize ≤ v.effectiveStride ∧
  v.base % v.align = 0 ∧
  ∃ span,
    checkedStridedSpan v.len v.effectiveStride v.elemSize v.width = some span ∧
    v.base + span ≤ v.bytes.size ∧
    v.base + span ≤ v.width.addrLimit

/-- Copy the `i`-th strided element (`elemSize` bytes at `base + i * stride`). -/
def copyStridedElem (bytes : ByteArray) (base stride elemSize i : Nat) : ByteArray :=
  bytes.extract (base + i * stride) (base + i * stride + elemSize)

/-- Fold strided element copies into a packed payload. -/
def marshalStridedGo (bytes : ByteArray) (base stride elemSize fuel : Nat) (acc : ByteArray) : ByteArray :=
  match fuel with
  | 0 => acc
  | n + 1 =>
    marshalStridedGo bytes base stride elemSize n
      (copyStridedElem bytes base stride elemSize n ++ acc)

/-- Copy the addressed strided elements into a packed buffer. Invalid geometry yields `none`. -/
def marshalSlice (v : C99ByteView) : Option ByteArray :=
  let stride := v.effectiveStride
  match checkedStridedSpan v.len stride v.elemSize v.width with
  | none => none
  | some span =>
    if v.align != 0 && v.base % v.align == 0 &&
        v.base + span ≤ v.bytes.size && v.base + span ≤ v.width.addrLimit then
      some (marshalStridedGo v.bytes v.base stride v.elemSize v.len ByteArray.empty)
    else none

/-- Write one packed element of `payload` back at a strided offset of `backing`. -/
def writeStridedElem (backing : ByteArray) (base stride elemSize i : Nat) (payload : ByteArray) : ByteArray :=
  let src := i * elemSize
  let dst := base + i * stride
  let elem := payload.extract src (src + elemSize)
  backing.extract 0 dst ++ elem ++ backing.extract (dst + elemSize) backing.size

/-- Fold packed payload elements back into strided slots. -/
def unmarshalStridedGo (backing : ByteArray) (base stride elemSize fuel : Nat) (payload : ByteArray) : ByteArray :=
  match fuel with
  | 0 => backing
  | n + 1 =>
    writeStridedElem (unmarshalStridedGo backing base stride elemSize n payload)
      base stride elemSize n payload

/-- Write a packed payload back into strided slots. The backing array size is preserved. -/
def unmarshalSlice (v : C99ByteView) (payload : ByteArray) : Option ByteArray :=
  let stride := v.effectiveStride
  match checkedStridedSpan v.len stride v.elemSize v.width with
  | none => none
  | some span =>
    if v.align != 0 && v.base % v.align == 0 &&
        v.base + span ≤ v.bytes.size && v.base + span ≤ v.width.addrLimit &&
        payload.size == v.len * v.elemSize then
      some (unmarshalStridedGo v.bytes v.base stride v.elemSize v.len payload)
    else none

/-- Derive the explicit `C99SliceDesc` for a `C99ByteView` so slice descriptor validation
    gates every host-side C-ABI slice call. -/
def C99ByteView.toSliceDesc (v : C99ByteView) : C99SliceDesc :=
  { dataPtr := some v.base
    len := v.len
    byteStride := v.effectiveStride
    elemSize := v.elemSize
    align := v.align
    backingBytes := v.bytes.size }

/-- Execute a validated host-side C-ABI slice call: verify `validateC99Slice` for `v.width`,
    marshal strided elements into a contiguous packed payload, run `kernel`, and unmarshal
    the transformed packed payload back into `v.bytes` while preserving non-addressed bytes. -/
def execValidatedSliceHostCall (v : C99ByteView) (kernel : ByteArray → ByteArray) : Option ByteArray :=
  if validateC99Slice v.toSliceDesc v.width then
    match marshalSlice v with
    | none => none
    | some packedIn => unmarshalSlice v (kernel packedIn)
  else none

/-- Width-aware zero-copy input/output byte-slice call descriptor for flat `(in_ptr, in_len, out_ptr, out_cap)`
    C99 / Rust / Swift / `wasm32` ABI boundaries over a shared backing memory image. -/
structure C99ZeroCopySliceIoCall where
  mem : ByteArray
  inPtr : Option Nat
  inLen : Nat
  outPtr : Option Nat
  outCap : Nat
  width : ArchWidth := .bits64
  deriving DecidableEq, Inhabited

/-- Proposition characterizing a valid width-aware zero-copy input/output byte-slice ABI call:
    non-null pointers for non-empty spans, `uintptr_t`/`size_t` representability (`≤ width.maxAddr`),
    target address-space (`≤ width.addrLimit`) and backing-buffer no-overflow, and non-aliasing
    (`disjoint`) whenever both input and output spans are non-empty. -/
def validZeroCopySliceIoCall (c : C99ZeroCopySliceIoCall) : Prop :=
  (match c.inPtr with
   | none => c.inLen = 0
   | some ip =>
     (c.inLen = 0 ∨ ip ≠ 0) ∧
     ip ≤ c.width.maxAddr ∧
     c.inLen ≤ c.width.maxAddr ∧
     ip + c.inLen ≤ c.mem.size ∧
     ip + c.inLen ≤ c.width.addrLimit) ∧
  (match c.outPtr with
   | none => c.outCap = 0
   | some op =>
     (c.outCap = 0 ∨ op ≠ 0) ∧
     op ≤ c.width.maxAddr ∧
     c.outCap ≤ c.width.maxAddr ∧
     op + c.outCap ≤ c.mem.size ∧
     op + c.outCap ≤ c.width.addrLimit) ∧
  (match c.inPtr, c.outPtr with
   | some ip, some op =>
     c.inLen = 0 ∨ c.outCap = 0 ∨ ip + c.inLen ≤ op ∨ op + c.outCap ≤ ip
   | _, _ => True)

/-- Boolean gate validating a zero-copy input/output byte-slice ABI call across `ArchWidth` (`LP64` / `wasm32`). -/
def validateZeroCopySliceIoCall (c : C99ZeroCopySliceIoCall) : Bool :=
  let inOk := match c.inPtr with
    | none => c.inLen == 0
    | some ip =>
      (c.inLen == 0 || ip != 0) &&
      decide (ip ≤ c.width.maxAddr) && decide (c.inLen ≤ c.width.maxAddr) &&
      decide (ip ≤ c.mem.size) && decide (c.inLen ≤ c.mem.size - ip) &&
      decide (ip ≤ c.width.addrLimit) && decide (c.inLen ≤ c.width.addrLimit - ip)
  let outOk := match c.outPtr with
    | none => c.outCap == 0
    | some op =>
      (c.outCap == 0 || op != 0) &&
      decide (op ≤ c.width.maxAddr) && decide (c.outCap ≤ c.width.maxAddr) &&
      decide (op ≤ c.mem.size) && decide (c.outCap ≤ c.mem.size - op) &&
      decide (op ≤ c.width.addrLimit) && decide (c.outCap ≤ c.width.addrLimit - op)
  let aliasOk := match c.inPtr, c.outPtr with
    | some ip, some op =>
      c.inLen == 0 || c.outCap == 0 ||
      decide (ip + c.inLen ≤ op) || decide (op + c.outCap ≤ ip)
    | _, _ => true
  inOk && outOk && aliasOk

/-- Outcome of a zero-copy input/output byte-slice host call, preserving `mem` identically on every error path. -/
inductive ZeroCopySliceIoOutcome where
  | ok (mem' : ByteArray) (writtenLen : Nat)
  | errInvalidGeometry (memUnchanged : ByteArray)
  | errKernelFailed (memUnchanged : ByteArray)
  | errOutputOverflow (memUnchanged : ByteArray) (neededLen : Nat)
  deriving DecidableEq, Inhabited

/-- Resulting memory image of a `ZeroCopySliceIoOutcome`. -/
def ZeroCopySliceIoOutcome.memory : ZeroCopySliceIoOutcome → ByteArray
  | .ok m _ => m
  | .errInvalidGeometry m => m
  | .errKernelFailed m => m
  | .errOutputOverflow m _ => m

/-- Splice `payload` into `mem` at `outBase` without changing total backing memory size (`payload.size ≤ outCap`). -/
def spliceOutputSlice (mem : ByteArray) (outBase : Nat) (payload : ByteArray) : ByteArray :=
  mem.extract 0 outBase ++ payload ++ mem.extract (outBase + payload.size) mem.size

/-- Extract the borrowed zero-copy input byte slice for `c`. -/
def zeroCopyInputBytes (c : C99ZeroCopySliceIoCall) : ByteArray :=
  match c.inPtr with
  | none => ByteArray.empty
  | some ip => c.mem.extract ip (ip + c.inLen)

/-- Execute a width-aware zero-copy `(in_ptr, in_len, out_ptr, out_cap)` host call:
    validates non-null/bounds/no-overflow/disjointness for `c.width`, borrows the exact input slice,
    runs `kernel`, rejects `none` or `payload.size > c.outCap` without mutating `c.mem`, and writes
    at most `c.outCap` bytes into `[outBase, outBase + payload.size)` while preserving all other bytes. -/
def execZeroCopySliceIoHostCall (c : C99ZeroCopySliceIoCall)
    (kernel : ByteArray → Option ByteArray) : ZeroCopySliceIoOutcome :=
  if validateZeroCopySliceIoCall c then
    match kernel (zeroCopyInputBytes c) with
    | none => .errKernelFailed c.mem
    | some outPayload =>
      if outPayload.size ≤ c.outCap then
        match c.outPtr with
        | none => .ok c.mem 0
        | some op =>
          if outPayload.size == 0 then .ok c.mem 0
          else .ok (spliceOutputSlice c.mem op outPayload) outPayload.size
      else
        .errOutputOverflow c.mem outPayload.size
  else
    .errInvalidGeometry c.mem

/-- Canonical typed C99 signature `(const uint8_t* in_ptr, size_t in_len, uint8_t* out_ptr, size_t out_cap) -> int64_t`
    for a zero-copy byte-slice kernel symbol (`>= 0` bytes written on success, `< 0` on error with zero partial mutation). -/
def mkZeroCopySliceIoCAbiSig (cSymbol : String) (leanName : String := cSymbol) : CAbiBindingSig :=
  { cSymbol
    leanName
    params := [
      ("in_ptr", "const uint8_t*", "*const u8"),
      ("in_len", "size_t", "usize"),
      ("out_ptr", "uint8_t*", "*mut u8"),
      ("out_cap", "size_t", "usize")
    ]
    retCType := "int64_t"
    retRustType := "i64" }

/-- Header fragment for one computed struct, including explicit offsets and C11 `_Static_assert`s
    for `sizeof`, `_Alignof`, and per-field `offsetof` when `width?` is specified,
    failing closed via `#error` on target/data-model mismatch. -/
def emitC99StructLayoutDecl (layout : C99StructLayout)
    (width? : Option ArchWidth := some .bits64) : String :=
  let fields := layout.fields.map fun f =>
    s!"  {f.ty.cSpelling} {f.name}; /* offset {f.offset}, size {f.size}, align {f.align} */"
  let staticAsserts :=
    match width? with
    | none => []
    | some width =>
      let (archGuard, errLine) :=
        match width with
        | .bits32 =>
          (ilp32PreprocGuard,
           "#error \"Mismatched or unsupported C-ABI target: pinned to wasm32 (32-bit)\"")
        | .bits64 =>
          ("#if defined(__LP64__) || defined(_LP64)",
           "#error \"Mismatched or unsupported C-ABI target: pinned to LP64 (64-bit)\"")
      let fieldAsserts := layout.fields.map fun f =>
        s!"_Static_assert(offsetof({layout.name}, {f.name}) == {f.offset}, \"{layout.name}.{f.name} offset\");"
      [ "#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L",
        archGuard,
        s!"_Static_assert(sizeof({layout.name}) == {layout.structSize}, \"{layout.name} size\");",
        s!"_Static_assert(_Alignof({layout.name}) == {layout.structAlign}, \"{layout.name} align\");" ] ++
      fieldAsserts ++
      [ "#else",
        errLine,
        "#endif",
        "#endif" ]
  String.intercalate "\n" ([
    s!"typedef struct {layout.name} \{"] ++ fields ++ [
    s!"} {layout.name};",
    s!"/* sizeof({layout.name}) = {layout.structSize}; alignof({layout.name}) = {layout.structAlign} */"] ++
    staticAsserts)

/-- Validate and emit a struct declaration for `width`. -/
def emitValidatedC99Struct (name : String) (specs : List C99FieldSpec)
    (width : ArchWidth := .bits64) : Option String :=
  (computeC99StructLayout name specs width).map (fun layout => emitC99StructLayoutDecl layout (some width))

/-- Host 64-bit float view (`FloatArray`, 8-byte IEEE-754 scalars) for C99 `double*` slice marshaling. -/
structure C99FloatView where
  floats : FloatArray
  base : Nat
  len : Nat
  deriving Inhabited

/-- A float view stays inside its backing `FloatArray` and fits 64-bit byte addressing. -/
def C99FloatView.isValid (v : C99FloatView) : Prop :=
  checkedByteLen v.len 8 = some (v.len * 8) ∧ v.base + v.len ≤ v.floats.size

/-- Marshal an aligned `FloatArray` subrange for a C99 `const double*` / `double*` slice. -/
def marshalFloatSlice (v : C99FloatView) : Option (Array Float) :=
  match checkedByteLen v.len 8 with
  | none => none
  | some _ =>
    if v.base + v.len ≤ v.floats.size then
      some (v.floats.data.extract v.base (v.base + v.len))
    else none

/-- Unmarshal a `double*` slice payload back into its backing `FloatArray` at `base`. -/
def unmarshalFloatSlice (backing : FloatArray) (base : Nat) (payload : Array Float) : Option FloatArray :=
  if base + payload.size ≤ backing.size then
    some ⟨backing.data.extract 0 base ++ payload ++ backing.data.extract (base + payload.size) backing.size⟩
  else none

/-- Emit a complete C99 header + forwarding shim pair for validated structs and typed function signatures. -/
def emitValidatedC99Bundle (structs : List (String × List C99FieldSpec)) (fns : List C99FnSig)
    (width : ArchWidth := .bits64) : Option (String × String) := do
  let layouts ← structs.mapM (fun (nm, specs) => computeC99StructLayout nm specs width)
  let structDecls := layouts.map (fun layout => emitC99StructLayoutDecl layout (some width))
  let protos := fns.map emitC99FnProto
  let shims := fns.map fun fn =>
    let params :=
      if fn.params.isEmpty then "void"
      else String.intercalate ", " (fn.params.map fun p => s!"{p.ty.cSpelling} {p.name}")
    let args := String.intercalate ", " (fn.params.map (·.name))
    let callStmt :=
      match fn.retTy with
      | some _ => s!"  return {fn.cSymbol}({args});"
      | none => s!"  {fn.cSymbol}({args});"
    String.intercalate "\n" [
      s!"{fn.retCSpelling} {fn.cSymbol}_c99_shim({params}) \{",
      callStmt,
      "}"
    ]
  let hdrParts :=
    ["#pragma once", "#ifndef LEAN_NATIVE_VALIDATED_C99_BUNDLE_H", "#define LEAN_NATIVE_VALIDATED_C99_BUNDLE_H",
     "#include <stdint.h>", "#include <stddef.h>", "#include <stdbool.h>"] ++
    structDecls ++ protos ++
    ["#endif /* LEAN_NATIVE_VALIDATED_C99_BUNDLE_H */"]
  let shimParts :=
    ["#include <stdint.h>", "#include <stddef.h>", "#include <stdbool.h>",
     "#ifndef LEAN_NATIVE_VALIDATED_C99_BUNDLE_H"] ++
    structDecls ++ ["#endif"] ++ protos ++ shims
  let hdr := String.intercalate "\n\n" hdrParts ++ "\n"
  let shim := String.intercalate "\n\n" shimParts ++ "\n"
  some (hdr, shim)

/-- Syntax-check emitted C11 text with `clang -std=c11 -fsyntax-only` and optional `extraFlags`.
    `arch` selects the LP64 host target or `wasm32`. -/
def c11SyntaxCheck (src : String) (arch : TargetArch := .x86_64)
    (extraFlags : Array String := #[]) : IO (Bool × String) := do
  let nonce ← IO.monoNanosNow
  let path := s!"/tmp/lean_native_cabi_{nonce}.c"
  IO.FS.writeFile path src
  try
    let sysClang : System.FilePath := "/usr/bin/clang"
    let brewClang : System.FilePath := "/opt/homebrew/opt/llvm/bin/clang"
    let appSysroot : List System.FilePath ← do
      try
        let exe ← IO.appPath
        match exe.parent >>= (·.parent) with
        | some root => pure [root]
        | none => pure []
      catch _ => pure []
    let sysrootEnv := ((← IO.getEnv "LEAN_SYSROOT").getD "").trimAscii.toString
    let elanHome := ((← IO.getEnv "ELAN_HOME").getD "").trimAscii.toString
    let home := ((← IO.getEnv "HOME").getD "").trimAscii.toString
    let tcRoots : List System.FilePath :=
      (if sysrootEnv.isEmpty then [] else [System.FilePath.mk sysrootEnv]) ++
      appSysroot ++
      (if elanHome.isEmpty then [] else [System.FilePath.mk s!"{elanHome}/toolchains/leanprover--lean4---v4.35.0"]) ++
      (if home.isEmpty then [] else [System.FilePath.mk s!"{home}/.elan/toolchains/leanprover--lean4---v4.35.0"]) ++
      [ System.FilePath.mk "/opt/orb/elan/toolchains/leanprover--lean4---v4.35.0",
        System.FilePath.mk "/var/lib/orb-node/orb-warm/elan/toolchains/leanprover--lean4---v4.35.0",
        System.FilePath.mk "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0",
        System.FilePath.mk "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0" ]
    let mut tcClangFound : Option (String × Array String) := none
    for sr in tcRoots do
      let cand := sr / "bin" / "clang"
      if ← cand.pathExists then
        tcClangFound := some (cand.toString, #[s!"-isystem{(sr / "include" / "clang").toString}"])
        break
    let fallbackIncArgs : Array String :=
      match tcClangFound with
      | some (_, inc) => inc
      | none => if sysrootEnv.isEmpty then #[] else #[s!"-isystem{sysrootEnv}/include/clang"]
    let (clangCmd, incArgs) ←
      if ← sysClang.pathExists then pure (sysClang.toString, #[])
      else if ← brewClang.pathExists then pure (brewClang.toString, #[])
      else match tcClangFound with
        | some (cmd, inc) => pure (cmd, inc)
        | none => pure ("clang", fallbackIncArgs)
    let targetArgs : Array String :=
      if !extraFlags.isEmpty then extraFlags
      else match arch with
        | .wasm32 => #["--target=wasm32-unknown-unknown", "-ffreestanding"]
        | .thumbv6m => #["--target=thumbv6m-none-eabi", "-ffreestanding"]
        | .thumbv8mMain => #["--target=thumbv8m.main-none-eabi", "-ffreestanding"]
        | .riscv32imac => #["--target=riscv32-unknown-none-elf", "-march=rv32imac", "-mabi=ilp32", "-ffreestanding"]
        | _ => #[]
    let out ← IO.Process.output {
      cmd := clangCmd
      args := targetArgs ++ incArgs ++ #["-std=c11", "-fsyntax-only", path]
    }
    return (out.exitCode == 0, out.stderr.trimAscii.toString)
  finally
    try IO.FS.removeFile path catch _ => pure ()

end LeanNative.Driver.CoreCLI
