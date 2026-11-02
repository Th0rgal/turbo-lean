import LeanNative.Backend.StableHLOAst

namespace LeanNative.Tests.StableHLOAstTests

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

def vA : TensorVal := mkTensor [2, 2] .ui32 [10#64, 20#64, 30#64, 40#64]
def vB : TensorVal := mkTensor [2, 2] .ui32 [1#64, 2#64, 3#64, 4#64]
def vZ : TensorVal := mkTensor [2, 2] .ui32 [1#64, 0#64, 3#64, 4#64]

def baseEnv : Env :=
  ((Env.empty.bind "a" vA).bind "b" vB).bind "z" vZ

#guard lookup? (evalOp Env.empty (.constant "c" vA)) "c" == some vA

#guard isErr (evalOp Env.empty (.constant "bad" (mkTensor [2, 2] .ui32 [1#64, 2#64])))
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
  (Env.empty.bind "x" (mkTensor [2] .i8 [0x80#64, 0x40#64])).bind "s" (mkTensor [2] .i8 [2#64, 2#64])

#guard lookup? (evalOp shraEnv (.shiftRightArithmetic "r" "x" "s")) "r" ==
  some (mkTensor [2] .i8 [0xE0#64, 0x10#64])

def cmpSelProg : List StableHLOOp := [
  .compare "cmp" "a" "b" .gt,
  .select "sel" "cmp" "a" "b",
  .returnOp "sel"
]

#guard lookup? (evalOps baseEnv cmpSelProg) "cmp" ==
  some (mkTensor [2, 2] .i1 [1#64, 1#64, 1#64, 1#64])

#guard lookup? (evalOps baseEnv cmpSelProg) "sel" == some vA

def mixedPredEnv : Env :=
  baseEnv.bind "p" (mkTensor [2, 2] .i1 [1#64, 0#64, 0#64, 1#64])

#guard lookup? (evalOp mixedPredEnv (.select "sel" "p" "a" "b")) "sel" ==
  some (mkTensor [2, 2] .ui32 [10#64, 2#64, 3#64, 40#64])

def vec2Env : Env :=
  Env.empty.bind "v" (mkTensor [2] .ui32 [7#64, 9#64])

#guard lookup? (evalOp vec2Env (.broadcastInDim "b" "v" [2, 2] [1])) "b" ==
  some (mkTensor [2, 2] .ui32 [7#64, 9#64, 7#64, 9#64])

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

def dotEnv : Env :=
  (Env.empty.bind "u" (mkTensor [3] .ui64 [2#64, 3#64, 4#64])).bind
    "w" (mkTensor [3] .ui64 [5#64, 6#64, 7#64])

#guard lookup? (evalOp dotEnv (.dotGeneral "dot" "u" "w" [0] [0] [])) "dot" ==
  some (mkTensor [] .ui64 [56#64])

def redEnv : Env :=
  (baseEnv.bind "zero" (mkTensor [] .ui32 [0#64]))

#guard lookup? (evalOp redEnv (.reduce "sum" "a" "zero" [1] "add_u32")) "sum" ==
  some (mkTensor [2] .ui32 [30#64, 70#64])

def convEnv : Env :=
  Env.empty.bind "wide" (mkTensor [2] .ui16 [0x01FF#64, 0x000A#64])

#guard lookup? (evalOp convEnv (.convert "narrow" "wide" .ui8)) "narrow" ==
  some (mkTensor [2] .ui8 [0xFF#64, 0x0A#64])

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
  "    %ax = stablehlo.multiply %alpha, %x\n" ++
  "    %out = stablehlo.add %ax, %y\n" ++
  "    return %out\n" ++
  "  }\n" ++
  "}"

#guard ppModuleOp sampleModule == expectedPP

end LeanNative.Tests.StableHLOAstTests
