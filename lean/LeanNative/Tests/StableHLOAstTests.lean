import LeanNative.Backend.StableHLOAst
import LeanNative.Backend.Semantics
import LeanNative.IR.LCNF
import LeanNative.Semantics.Eval

namespace LeanNative.Tests.StableHLOAstTests

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.StableHLOAst

def mkTensor (shape : List Nat) (elem : ElemType) (vals : List (BitVec 64)) : TensorVal :=
  { ty := { shape := shape, elem := elem }, data := vals.toArray }

def lookup? (res : Except ShapeError Env) (name : String) : Option TensorVal :=
  match res with
  | .ok env => env name
  | .error _ => none

def isErr (res : Except ShapeError Env) (p : ShapeError → Bool) : Bool :=
  match res with
  | .error e => p e
  | .ok _ => false

def isPoison (res : LeanMLIR.PoisonOr Val) : Bool :=
  match res with
  | .poison _ => true
  | .val _ => false

def isDivZero (res : Except UBError Val) : Bool :=
  match res with
  | .error .divisionByZero => true
  | _ => false

def isTypeErr (res : Except UBError Val) : Bool :=
  match res with
  | .error (.typeError _) => true
  | _ => false

def isOkTensor (res : Except ShapeError TensorVal) (expected : TensorVal) : Bool :=
  match res with
  | .ok v => v == expected
  | .error _ => false

def isOkVal (res : Except UBError Val) (expected : Val) : Bool :=
  match res with
  | .ok v => v == expected
  | .error _ => false

def vA : TensorVal := mkTensor [2, 2] .ui32 [10#64, 20#64, 30#64, 40#64]
def vB : TensorVal := mkTensor [2, 2] .ui32 [1#64, 2#64, 3#64, 4#64]
def vZ : TensorVal := mkTensor [2, 2] .ui32 [1#64, 0#64, 3#64, 4#64]

def baseEnv : Env :=
  ((Env.empty.bind "a" vA).bind "b" vB).bind "z" vZ

#guard lookup? (evalOp Env.empty (.constant "c" vA)) "c" == some vA

#guard isErr (evalOp Env.empty (.constant "bad" (mkTensor [2, 2] .ui32 [1#64, 2#64])))
  (fun | .volumeMismatch 2 4 => true | _ => false)

-- [B4]: ill-formed bound tensor with mismatched buffer size is rejected by lookup
def badBoundEnv : Env :=
  Env.empty.bind "bad" (mkTensor [2, 2] .ui32 [1#64, 2#64])

#guard isErr (evalOp badBoundEnv (.add "r" "bad" "bad"))
  (fun | .volumeMismatch 2 4 => true | _ => false)

#guard lookup? (evalOp baseEnv (.add "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [11#64, 22#64, 33#64, 44#64])

#guard lookup? (evalOp baseEnv (.subtract "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [9#64, 18#64, 27#64, 36#64])

#guard lookup? (evalOp baseEnv (.multiply "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [10#64, 40#64, 90#64, 160#64])

#guard lookup? (evalOp baseEnv (.divide "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [10#64, 10#64, 10#64, 10#64])

#guard isErr (evalOp baseEnv (.divide "r" "a" "z"))
  (fun | .divisionByZero => true | _ => false)

#guard lookup? (evalOp baseEnv (.remainder "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [0#64, 0#64, 0#64, 0#64])

#guard lookup? (evalOp baseEnv (.maximum "r" "a" "b")) "r" == some vA
#guard lookup? (evalOp baseEnv (.minimum "r" "a" "b")) "r" == some vB

#guard lookup? (evalOp baseEnv (.and "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [0#64, 0#64, 2#64, 0#64])

#guard lookup? (evalOp baseEnv (.or "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [11#64, 22#64, 31#64, 44#64])

#guard lookup? (evalOp baseEnv (.xor "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [11#64, 22#64, 29#64, 44#64])

#guard lookup? (evalOp baseEnv (.shiftLeft "r" "b" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [2#64, 8#64, 24#64, 64#64])

#guard lookup? (evalOp baseEnv (.shiftRightLogical "r" "a" "b")) "r" ==
  some (mkTensor [2, 2] .ui32 [5#64, 5#64, 3#64, 2#64])

def shraEnv : Env :=
  (Env.empty.bind "x" (mkTensor [2] .i8 [0x80#64, 0x40#64])).bind
    "s" (mkTensor [2] .i8 [2#64, 2#64])

#guard lookup? (evalOp shraEnv (.shiftRightArithmetic "r" "x" "s")) "r" ==
  some (mkTensor [2] .i8 [0xE0#64, 0x10#64])

-- [B1.1]: shift saturation at amt >= w (no mod 64 wrap)
def shSatEnv : Env :=
  ((Env.empty.bind "neg8" (mkTensor [1] .i8 [0x80#64])).bind
    "pos8" (mkTensor [1] .i8 [0x7F#64])).bind
    "amt64" (mkTensor [1] .i8 [64#64])

#guard lookup? (evalOp shSatEnv (.shiftLeft "r" "pos8" "amt64")) "r" ==
  some (mkTensor [1] .i8 [0#64])

#guard lookup? (evalOp shSatEnv (.shiftRightLogical "r" "neg8" "amt64")) "r" ==
  some (mkTensor [1] .i8 [0#64])

def shSat9Env : Env :=
  shSatEnv.bind "amt9" (mkTensor [1] .i8 [9#64])

#guard lookup? (evalOp shSat9Env (.shiftRightArithmetic "r" "neg8" "amt9")) "r" ==
  some (mkTensor [1] .i8 [0xFF#64])

#guard lookup? (evalOp shSat9Env (.shiftRightArithmetic "r" "pos8" "amt9")) "r" ==
  some (mkTensor [1] .i8 [0#64])

-- [B1.2]: signed max/min/compare/divide/remainder on i8..i64
def signed8Env : Env :=
  ((Env.empty.bind "m1" (mkTensor [1] .i8 [0xFF#64])).bind
    "p1" (mkTensor [1] .i8 [1#64])).bind
    "m7" (mkTensor [1] .i8 [0xF9#64])

#guard lookup? (evalOp signed8Env (.maximum "r" "m1" "p1")) "r" ==
  some (mkTensor [1] .i8 [1#64])

#guard lookup? (evalOp signed8Env (.minimum "r" "m1" "p1")) "r" ==
  some (mkTensor [1] .i8 [0xFF#64])

#guard lookup? (evalOp signed8Env (.compare "r" "m1" "p1" .lt)) "r" ==
  some (mkTensor [1] .i1 [1#64])

def signedDivEnv : Env :=
  signed8Env.bind "p2" (mkTensor [1] .i8 [2#64])

#guard lookup? (evalOp signedDivEnv (.divide "r" "m7" "p2")) "r" ==
  some (mkTensor [1] .i8 [0xFD#64])

#guard lookup? (evalOp signedDivEnv (.remainder "r" "m7" "p2")) "r" ==
  some (mkTensor [1] .i8 [0xFF#64])

-- [B1.3]: i1 is signless {0, 1}, NOT signed {-1, 0}
def i1Env : Env :=
  (Env.empty.bind "one" (mkTensor [1] .i1 [1#64])).bind
    "zero" (mkTensor [1] .i1 [0#64])

#guard lookup? (evalOp i1Env (.compare "r" "one" "zero" .lt)) "r" ==
  some (mkTensor [1] .i1 [0#64])

#guard lookup? (evalOp i1Env (.maximum "r" "one" "zero")) "r" ==
  some (mkTensor [1] .i1 [1#64])

-- [B1]: float arithmetic/compare/dot/reduce/convert (both directions) fail closed
def f32Env : Env :=
  ((Env.empty.bind "fa" (mkTensor [2] .f32 [0x3F800000#64, 0x40000000#64])).bind
    "fb" (mkTensor [2] .f32 [0x40400000#64, 0x40800000#64])).bind
    "f0" (mkTensor [] .f32 [0#64])

#guard isErr (evalOp f32Env (.add "r" "fa" "fb")) (fun _ => true)
#guard isErr (evalOp f32Env (.divide "r" "fa" "fb")) (fun _ => true)
#guard isErr (evalOp f32Env (.maximum "r" "fa" "fb")) (fun _ => true)
#guard isErr (evalOp f32Env (.shiftLeft "r" "fa" "fb")) (fun _ => true)
#guard isErr (evalOp f32Env (.compare "r" "fa" "fb" .lt)) (fun _ => true)
#guard isErr (evalOp f32Env (.dotGeneral "r" "fa" "fb" [] [] [0] [0] [])) (fun _ => true)
#guard isErr (evalOp f32Env (.reduce "r" "fa" "f0" [0] "add" [])) (fun _ => true)
#guard isErr (evalOp f32Env (.convert "r" "fa" .i32)) (fun _ => true)
#guard isErr (evalOp baseEnv (.convert "r" "a" .f32)) (fun _ => true)
#guard isErr (evalOp baseEnv (.convert "r" "a" .bf16)) (fun _ => true)
#guard isErr (evalOp baseEnv (.convert "r" "a" .f64)) (fun _ => true)

-- [B2]: signed .i32 / .i64 ops, OpenXLA INT_MIN / -1 = INT_MIN & INT_MIN % -1 = 0, and .i64 arithmetic right shift
def signed64Env : Env :=
  ((((Env.empty.bind "neg64" (mkTensor [1] .i64 [0x8000000000000000#64])).bind
    "m1_64" (mkTensor [1] .i64 [0xFFFFFFFFFFFFFFFF#64])).bind
    "z64" (mkTensor [1] .i64 [0#64])).bind
    "sh2" (mkTensor [1] .i64 [2#64])).bind
    "sh64" (mkTensor [1] .i64 [64#64])

#guard lookup? (evalOp signed64Env (.shiftRightArithmetic "r" "neg64" "sh2")) "r" ==
  some (mkTensor [1] .i64 [0xE000000000000000#64])

#guard lookup? (evalOp signed64Env (.shiftRightArithmetic "r" "neg64" "sh64")) "r" ==
  some (mkTensor [1] .i64 [0xFFFFFFFFFFFFFFFF#64])

#guard lookup? (evalOp signed64Env (.divide "r" "neg64" "m1_64")) "r" ==
  some (mkTensor [1] .i64 [0x8000000000000000#64])

#guard lookup? (evalOp signed64Env (.remainder "r" "neg64" "m1_64")) "r" ==
  some (mkTensor [1] .i64 [0#64])

#guard isErr (evalOp signed64Env (.divide "r" "neg64" "z64"))
  (fun | .divisionByZero => true | _ => false)

#guard lookup? (evalOp signed64Env (.compare "r" "neg64" "m1_64" .lt)) "r" ==
  some (mkTensor [1] .i1 [1#64])

def cmpSelProg : List StableHLOOp := [
  .compare "cmp" "a" "b" .gt,
  .select "sel" "cmp" "a" "b",
  .returnOp "sel"
]

#guard lookup? (evalOps baseEnv cmpSelProg) "cmp" ==
  some (mkTensor [2, 2] .i1 [1#64, 1#64, 1#64, 1#64])

#guard lookup? (evalOps baseEnv cmpSelProg) "sel" == some vA

-- [B1.9]: dead ops after returnOp fail closed
#guard isErr (evalOps baseEnv [.returnOp "a", .add "dead" "a" "b"])
  (fun | .shapeMismatch _ => true | _ => false)

def mixedPredEnv : Env :=
  baseEnv.bind "p" (mkTensor [2, 2] .i1 [1#64, 0#64, 0#64, 1#64])

#guard lookup? (evalOp mixedPredEnv (.select "sel" "p" "a" "b")) "sel" ==
  some (mkTensor [2, 2] .ui32 [10#64, 2#64, 3#64, 40#64])

def vec2Env : Env :=
  Env.empty.bind "v" (mkTensor [2] .ui32 [7#64, 9#64])

#guard lookup? (evalOp vec2Env (.broadcastInDim "b" "v" [2, 2] [1])) "b" ==
  some (mkTensor [2, 2] .ui32 [7#64, 9#64, 7#64, 9#64])

-- [B3]: axis-0 broadcast [7, 9] -> [2, 3] with dims = [0] yields [7, 7, 7, 9, 9, 9]
#guard lookup? (evalOp vec2Env (.broadcastInDim "b0" "v" [2, 3] [0])) "b0" ==
  some (mkTensor [2, 3] .ui32 [7#64, 7#64, 7#64, 9#64, 9#64, 9#64])

-- [B1.5]: broadcast_in_dim requires strictly increasing dims
def mat1x1Env : Env :=
  Env.empty.bind "m" (mkTensor [1, 1] .ui32 [42#64])

#guard isErr (evalOp mat1x1Env (.broadcastInDim "bad" "m" [2, 2] [1, 0]))
  (fun | .shapeMismatch _ => true | _ => false)

#guard isErr (evalOp mat1x1Env (.broadcastInDim "bad" "m" [2, 2] [0, 0]))
  (fun | .shapeMismatch _ => true | _ => false)

#guard lookup? (evalOp baseEnv (.reshape "flat" "a" [4])) "flat" ==
  some (mkTensor [4] .ui32 [10#64, 20#64, 30#64, 40#64])

#guard isErr (evalOp baseEnv (.reshape "bad" "a" [3, 2]))
  (fun | .volumeMismatch 4 6 => true | _ => false)

def mat2x3Env : Env :=
  ((Env.empty.bind "m" (mkTensor [2, 3] .ui32 [1#64, 2#64, 3#64, 4#64, 5#64, 6#64])).bind
    "i0" (mkTensor [] .ui32 [0#64])).bind "i1" (mkTensor [] .ui32 [1#64])

#guard lookup? (evalOp mat2x3Env (.slice "s" "m" [0, 1] [2, 3] [1, 1])) "s" ==
  some (mkTensor [2, 2] .ui32 [2#64, 3#64, 5#64, 6#64])

#guard lookup? (evalOp mat2x3Env (.dynamicSlice "ds" "m" ["i0", "i1"] [2, 2])) "ds" ==
  some (mkTensor [2, 2] .ui32 [2#64, 3#64, 5#64, 6#64])

-- [B1.6]: dynamic_slice clamps signed negative start index to 0 and rejects mismatched start types
def dynSignedEnv : Env :=
  ((mat2x3Env.bind "neg1" (mkTensor [] .i32 [0xFFFFFFFF#64])).bind
    "pos5" (mkTensor [] .i32 [5#64])).bind
    "u0" (mkTensor [] .ui32 [0#64])

#guard lookup? (evalOp dynSignedEnv (.dynamicSlice "ds" "m" ["neg1", "pos5"] [1, 2])) "ds" ==
  some (mkTensor [1, 2] .ui32 [2#64, 3#64])

#guard isErr (evalOp dynSignedEnv (.dynamicSlice "bad" "m" ["neg1", "u0"] [1, 2]))
  (fun | .shapeMismatch _ => true | _ => false)

-- [B1.8]: batched 2D matmul via dotGeneral
def dotEnv : Env :=
  (Env.empty.bind "u" (mkTensor [3] .ui64 [2#64, 3#64, 4#64])).bind
    "w" (mkTensor [3] .ui64 [5#64, 6#64, 7#64])

#guard lookup? (evalOp dotEnv (.dotGeneral "dot" "u" "w" [] [] [0] [0] [])) "dot" ==
  some (mkTensor [] .ui64 [56#64])

def batchDotEnv : Env :=
  (Env.empty.bind "lhs"
    (mkTensor [2, 2, 2] .ui32 [1#64, 2#64, 3#64, 4#64, 2#64, 0#64, 0#64, 2#64])).bind
  "rhs"
    (mkTensor [2, 2, 2] .ui32 [5#64, 6#64, 7#64, 8#64, 1#64, 3#64, 5#64, 7#64])

#guard lookup? (evalOp batchDotEnv (.dotGeneral "bd" "lhs" "rhs" [0] [0] [2] [1] [2, 2, 2])) "bd" ==
  some (mkTensor [2, 2, 2] .ui32 [19#64, 22#64, 43#64, 50#64, 2#64, 6#64, 10#64, 14#64])

-- [B3]: 2x3 · 3x2 [[1,2,3],[4,5,6]] · [[7,8],[9,10],[11,12]] on [1]x[0] -> [58, 64, 139, 154]
def matmul2x3x2Env : Env :=
  (Env.empty.bind "m23"
    (mkTensor [2, 3] .ui32 [1#64, 2#64, 3#64, 4#64, 5#64, 6#64])).bind
  "m32"
    (mkTensor [3, 2] .ui32 [7#64, 8#64, 9#64, 10#64, 11#64, 12#64])

#guard lookup? (evalOp matmul2x3x2Env (.dotGeneral "mm" "m23" "m32" [] [] [1] [0] [2, 2])) "mm" ==
  some (mkTensor [2, 2] .ui32 [58#64, 64#64, 139#64, 154#64])

-- [B3]: axis-0 reduce on 2x3 [[1,2,3],[4,5,6]] -> [5, 7, 9], plus non-add & signed max reduce
def red2x3Env : Env :=
  (matmul2x3x2Env.bind "z0" (mkTensor [] .ui32 [0#64])).bind
    "z1" (mkTensor [] .ui32 [1#64])

#guard lookup? (evalOp red2x3Env (.reduce "s0" "m23" "z0" [0] "add" [3])) "s0" ==
  some (mkTensor [3] .ui32 [5#64, 7#64, 9#64])

#guard lookup? (evalOp red2x3Env (.reduce "p0" "m23" "z1" [0] "mul" [3])) "p0" ==
  some (mkTensor [3] .ui32 [4#64, 10#64, 18#64])

def signedRedEnv : Env :=
  (Env.empty.bind "sv" (mkTensor [2] .i8 [0xFF#64, 1#64])).bind
    "smin" (mkTensor [] .i8 [0x80#64])

#guard lookup? (evalOp signedRedEnv (.reduce "smax" "sv" "smin" [0] "max" [])) "smax" ==
  some (mkTensor [] .i8 [1#64])

-- [B2]: reduce takes explicit outShape and checks reducer body against element type
def redEnv : Env :=
  baseEnv.bind "zero" (mkTensor [] .ui32 [0#64])

#guard lookup? (evalOp redEnv (.reduce "sum" "a" "zero" [1] "add_ui32" [2])) "sum" ==
  some (mkTensor [2] .ui32 [30#64, 70#64])

#guard isErr (evalOp redEnv (.reduce "bad" "a" "zero" [1] "add_ui32" [1, 2]))
  (fun | .shapeMismatch _ => true | _ => false)

#guard isErr (evalOp redEnv (.reduce "bad" "a" "zero" [1] "add_i8" [2]))
  (fun | .shapeMismatch _ => true | _ => false)

-- [B1.7]: signed widening sign-extends, narrowing truncates, convert to i1 tests != 0
def convEnv : Env :=
  ((Env.empty.bind "wide" (mkTensor [2] .ui16 [0x01FF#64, 0x000A#64])).bind
    "neg8" (mkTensor [2] .i8 [0xFE#64, 0x03#64])).bind
    "even8" (mkTensor [2] .ui8 [2#64, 0#64])

#guard lookup? (evalOp convEnv (.convert "narrow" "wide" .ui8)) "narrow" ==
  some (mkTensor [2] .ui8 [0xFF#64, 0x0A#64])

#guard lookup? (evalOp convEnv (.convert "sext" "neg8" .i16)) "sext" ==
  some (mkTensor [2] .i16 [0xFFFE#64, 0x0003#64])

#guard lookup? (evalOp convEnv (.convert "nz" "even8" .i1)) "nz" ==
  some (mkTensor [2] .i1 [1#64, 0#64])

-- [B2]: MLIR StableHLO pretty-printer emits per-op result types and valid syntax
def sampleFunc : FuncOp := {
  name := "saxpy_2x2"
  params := [("x", { shape := [2, 2], elem := .ui32 }), ("y", { shape := [2, 2], elem := .ui32 })]
  result := { shape := [2, 2], elem := .ui32 }
  body := [
    .constant "alpha" (mkTensor [2, 2] .ui32 [5#64, 5#64, 5#64, 5#64]),
    .multiply "ax" "alpha" "x",
    .add "out" "ax" "y",
    .returnOp "out"
  ]
}

def sampleModule : ModuleOp := {
  name := "c2c_demo"
  funcs := [sampleFunc]
}

def expectedPP : String :=
  "module @c2c_demo {\n" ++
  "  func.func @saxpy_2x2(%x: tensor<2x2xui32>, %y: tensor<2x2xui32>) -> tensor<2x2xui32> {\n" ++
  "    %alpha = stablehlo.constant dense<5> : tensor<2x2xui32>\n" ++
  "    %ax = stablehlo.multiply %alpha, %x : tensor<2x2xui32>\n" ++
  "    %out = stablehlo.add %ax, %y : tensor<2x2xui32>\n" ++
  "    return %out : tensor<2x2xui32>\n" ++
  "  }\n" ++
  "}"

#guard ppModuleOp sampleModule == expectedPP

#guard isOkTensor (evalModuleOp sampleModule "saxpy_2x2" [vB, vA])
  (mkTensor [2, 2] .ui32 [15#64, 30#64, 45#64, 60#64])

-- [B4]: pretty-printing of nested dense, signed negative, i1 booleans, compare, reduce, slice
def richFunc : FuncOp := {
  name := "rich_ops"
  params := [("x", { shape := [2, 2], elem := .i32 }), ("z", { shape := [], elem := .i32 })]
  result := { shape := [2], elem := .i32 }
  body := [
    .constant "c" (mkTensor [2, 2] .i32 [0xFFFFFFFF#64, 2#64, 3#64, 0xFFFFFFFE#64]),
    .compare "lt" "x" "c" .lt,
    .select "sel" "lt" "x" "c",
    .slice "sl" "sel" [0, 0] [2, 2] [1, 1],
    .reduce "red" "sl" "z" [1] "add" [2],
    .returnOp "red"
  ]
}

def expectedRichPP : String :=
  "  func.func @rich_ops(%x: tensor<2x2xi32>, %z: tensor<i32>) -> tensor<2xi32> {\n" ++
  "    %c = stablehlo.constant dense<[[-1, 2], [3, -2]]> : tensor<2x2xi32>\n" ++
  "    %lt = stablehlo.compare LT, %x, %c, SIGNED : (tensor<2x2xi32>, tensor<2x2xi32>) -> tensor<2x2xi1>\n" ++
  "    %sel = stablehlo.select %lt, %x, %c : tensor<2x2xi1>, tensor<2x2xi32>\n" ++
  "    %sl = stablehlo.slice %sel [0:2:1, 0:2:1] : (tensor<2x2xi32>) -> tensor<2x2xi32>\n" ++
  "    %red = stablehlo.reduce(%sl init: %z) across dimensions = [1] : " ++
  "(tensor<2x2xi32>, tensor<i32>) -> tensor<2xi32> reducer(%arg0: tensor<i32>, %arg1: tensor<i32>) {\n" ++
  "      %sum = stablehlo.add %arg0, %arg1 : tensor<i32>\n" ++
  "      stablehlo.return %sum : tensor<i32>\n" ++
  "    }\n" ++
  "    return %red : tensor<2xi32>\n" ++
  "  }"

#guard ppFuncOp richFunc == expectedRichPP

-- [B5]: LeanMLIR.applyWordBinOp & LCNF.primBinOp strict typing and u64 div/mod-by-zero
#guard isPoison (LeanMLIR.applyWordBinOp .div (.u64 42) (.u64 0))
#guard isPoison (LeanMLIR.applyWordBinOp .mod (.u64 42) (.u64 0))
#guard LeanMLIR.applyWordBinOp .div (.u64 42) (.u64 7) == .val (.u64 6)
#guard LeanMLIR.applyWordBinOp .mod (.u64 43) (.u64 7) == .val (.u64 1)

#guard isPoison (LeanMLIR.applyWordBinOp .add (.u64 0) (.bool true))
#guard isPoison (LeanMLIR.applyWordBinOp .mul (.u64 0) (.bool true))
#guard isPoison (LeanMLIR.applyWordBinOp .mul (.u64 1) (.bool true))
#guard isPoison (LeanMLIR.applyWordBinOp .div (.bool true) (.u64 1))
#guard isPoison (LeanMLIR.applyWordBinOp .sub (.bool true) (.u64 0))
#guard isPoison (LeanMLIR.applyWordBinOp .bitOr (.u64 0) (.bool true))
#guard isPoison (LeanMLIR.applyWordBinOp .bitXor (.bool true) (.u64 0))
#guard isPoison (LeanMLIR.applyWordBinOp .shl (.bool true) (.u64 0))
#guard isPoison (LeanMLIR.applyWordBinOp .shr (.bool true) (.u64 0))

#guard isDivZero (LCNF.primBinOp .div (.u64 42) (.u64 0))
#guard isDivZero (LCNF.primBinOp .mod (.u64 42) (.u64 0))
#guard isOkVal (LCNF.primBinOp .div (.u64 42) (.u64 7)) (.u64 6)
#guard isOkVal (LCNF.primBinOp .mod (.u64 43) (.u64 7)) (.u64 1)

#guard isTypeErr (LCNF.primBinOp .add (.u64 0) (.bool true))
#guard isTypeErr (LCNF.primBinOp .mul (.u64 0) (.bool true))
#guard isTypeErr (LCNF.primBinOp .mul (.u64 1) (.bool true))
#guard isTypeErr (LCNF.primBinOp .div (.bool true) (.u64 1))
#guard isTypeErr (LCNF.primBinOp .sub (.bool true) (.u64 0))
#guard isTypeErr (LCNF.primBinOp .bitOr (.u64 0) (.bool true))
#guard isTypeErr (LCNF.primBinOp .bitXor (.bool true) (.u64 0))
#guard isTypeErr (LCNF.primBinOp .shl (.bool true) (.u64 0))
#guard isTypeErr (LCNF.primBinOp .shr (.bool true) (.u64 0))

end LeanNative.Tests.StableHLOAstTests
