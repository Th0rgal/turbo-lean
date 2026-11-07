import Lean.Data.Json
import LeanNative.IR.Codec
import LeanNative.Backend.LLVM
import LeanNative.Backend.LLVMAst
import LeanNative.Backend.LLVMLower

namespace LeanNative.Driver.LLVMDiffCLI

open Lean
open LeanNative.IR
open LeanNative.Backend.TargetIR
open LeanNative.Backend.LLVM
open LeanNative.Backend.LLVMAst
open LeanNative.Backend.LLVMLower

structure DiffVector where
  inputs : List UInt64
  expectedTag : String
  expectedWord? : Option UInt64

structure DiffCase where
  id : String
  category : String
  fnName : String
  arity : Nat
  irText : String
  vectors : List DiffVector
  negativeMutantIr? : Option String := none
  negativeMutantReason? : Option String := none

private def mkTestMod (fns : List LLVMFn) : LLVMModule :=
  { dataLayout := TargetArch.x86_64.dataLayout
  , triple := TargetArch.x86_64.llvmTriple
  , fns := fns }

private def evalOutcomeToVec (inputs : List UInt64) : ExecOutcome → DiffVector
  | .returned (some (.bits .i64 bv)) =>
    { inputs := inputs, expectedTag := "val", expectedWord? := some bv.toNat.toUInt64 }
  | .returned (some (.bits _ bv)) =>
    { inputs := inputs, expectedTag := "val", expectedWord? := some bv.toNat.toUInt64 }
  | .returned (some .poison) =>
    { inputs := inputs, expectedTag := "poison", expectedWord? := none }
  | .returned _ =>
    { inputs := inputs, expectedTag := "other", expectedWord? := none }
  | .ub msg =>
    { inputs := inputs, expectedTag := s!"ub:{msg}", expectedWord? := none }
  | .outOfFuel =>
    { inputs := inputs, expectedTag := "out_of_fuel", expectedWord? := none }

private def buildCase (id category : String) (mod_ : LLVMModule) (fn : LLVMFn)
    (inputRows : List (List UInt64)) (fuel : Nat := 256)
    (negFn? : Option (LLVMFn × String) := none) : DiffCase :=
  let vecs := inputRows.map fun row =>
    let args := row.map fun u => LLVMVal.bits .i64 (BitVec.ofNat 64 u.toNat)
    evalOutcomeToVec row (execFn mod_ fn args fuel)
  let (negIr?, negReason?) := match negFn? with
    | none => (none, none)
    | some (mFn, reason) =>
      let mMod := mkTestMod [mFn]
      (some (PP.ppModule mMod), some reason)
  { id := id
  , category := category
  , fnName := fn.name
  , arity := fn.params.length
  , irText := PP.ppModule mod_
  , vectors := vecs
  , negativeMutantIr? := negIr?
  , negativeMutantReason? := negReason? }

private def p64 (r : String) : LLVMParam := ⟨r, .int .i64, []⟩
private def k64 (n : Nat) : Operand := .constInt .i64 (BitVec.ofNat 64 n)
private def k1 (b : Bool) : Operand := .constInt .i1 (if b then 1#1 else 0#1)

private def fnAluFlagsSelect : LLVMFn :=
  { name := "diff_alu_nsw_nuw_select"
  , retTy := .int .i64
  , params := [p64 "a", p64 "b"]
  , blocks := [
      { label := "entry"
      , body := [
          .add "poison_nsw" .nsw .i64 (.constInt .i64 (BitVec.ofNat 64 0x7fffffffffffffff)) (k64 1),
          .add "poison_prop" .none .i64 (.reg "poison_nsw") (.reg "a"),
          .icmp "cond" .ult (.int .i64) (.reg "a") (.reg "b"),
          .add "safe_sum" .none .i64 (.reg "a") (.reg "b"),
          .xor "safe_xor" .i64 (.reg "safe_sum") (k64 0x5a5a),
          .select "chosen1" (k1 true) (.int .i64) (.reg "safe_xor") (.reg "poison_prop"),
          .add "poison_nuw" .nuw .i64 (.constInt .i64 (BitVec.ofNat 64 0xffffffffffffffff)) (k64 1),
          .select "chosen2" (k1 false) (.int .i64) (.reg "poison_nuw") (.reg "chosen1"),
          .sub "diff" .none .i64 (.reg "chosen2") (.reg "b"),
          .select "res" (.reg "cond") (.int .i64) (.reg "chosen2") (.reg "diff")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnAluFlagsSelectMutant : LLVMFn :=
  { fnAluFlagsSelect with
    blocks := [
      { label := "entry"
      , body := [
          .sub "res" .none .i64 (.reg "b") (.reg "a")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnShiftsAndCasts : LLVMFn :=
  { name := "diff_shifts_exact_casts"
  , retTy := .int .i64
  , params := [p64 "a", p64 "b"]
  , blocks := [
      { label := "entry"
      , body := [
          .shl "over_shl" .none .i64 (.reg "a") (k64 64),
          .lshr "inexact_lshr" true .i64 (k64 7) (k64 1),
          .and_ "sh_amt" .i64 (.reg "b") (k64 31),
          .shl "sh1" .none .i64 (.reg "a") (.reg "sh_amt"),
          .ashr "sh2" false .i64 (.reg "sh1") (k64 3),
          .trunc "t32" .i64 (.reg "sh2") .i32,
          .sext "s64" .i32 (.reg "t32") .i64,
          .trunc "t16" .i64 (.reg "b") .i16,
          .zext "z64" .i16 (.reg "t16") .i64,
          .xor "comb" .i64 (.reg "s64") (.reg "z64"),
          .select "mask1" (k1 false) (.int .i64) (.reg "over_shl") (.reg "comb"),
          .select "res" (k1 true) (.int .i64) (.reg "mask1") (.reg "inexact_lshr")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnShiftsMutant : LLVMFn :=
  { fnShiftsAndCasts with
    blocks := [
      { label := "entry"
      , body := [
          .and_ "sh_amt" .i64 (.reg "b") (k64 31),
          .lshr "res" false .i64 (.reg "a") (.reg "sh_amt")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnDivRemSignedUnsigned : LLVMFn :=
  { name := "diff_sdiv_srem_udiv_urem"
  , retTy := .int .i64
  , params := [p64 "a", p64 "b"]
  , blocks := [
      { label := "entry"
      , body := [
          .or_ "b_nz" .i64 (.reg "b") (k64 1),
          .and_ "b_safe" .i64 (.reg "b_nz") (k64 0x7fffffffffffffff),
          .udiv "uq" false .i64 (.reg "a") (.reg "b_safe"),
          .urem "ur" .i64 (.reg "a") (.reg "b_safe"),
          .sdiv "sq" false .i64 (.reg "a") (.reg "b_safe"),
          .srem "sr" .i64 (.reg "a") (.reg "b_safe"),
          .add "u_acc" .none .i64 (.reg "uq") (.reg "ur"),
          .add "s_acc" .none .i64 (.reg "sq") (.reg "sr"),
          .xor "res" .i64 (.reg "u_acc") (.reg "s_acc")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnParallelPhiSwapLoop : LLVMFn :=
  { name := "diff_parallel_phi_swap_loop"
  , retTy := .int .i64
  , params := [p64 "x0", p64 "y0", p64 "steps_raw"]
  , blocks := [
      { label := "entry"
      , body := [
          .and_ "steps" .i64 (.reg "steps_raw") (k64 15)
        ]
      , term := .br "loop" },
      { label := "loop"
      , phis := [
          { dst := "i", ty := .int .i64, incomings := [(k64 0, "entry"), (.reg "i_next", "body")] },
          { dst := "p", ty := .int .i64, incomings := [(.reg "x0", "entry"), (.reg "q_upd", "body")] },
          { dst := "q", ty := .int .i64, incomings := [(.reg "y0", "entry"), (.reg "p", "body")] }
        ]
      , body := [
          .icmp "cont" .ult (.int .i64) (.reg "i") (.reg "steps")
        ]
      , term := .condBr (.reg "cont") "body" "exit" },
      { label := "body"
      , body := [
          .mul "p_scaled" .none .i64 (.reg "p") (k64 3),
          .add "q_upd" .none .i64 (.reg "q") (.reg "p_scaled"),
          .add "i_next" .none .i64 (.reg "i") (k64 1)
        ]
      , term := .br "loop" },
      { label := "exit"
      , body := [
          .shl "p_hi" .none .i64 (.reg "p") (k64 7),
          .xor "res" .i64 (.reg "p_hi") (.reg "q")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnSequentialPhiBugMutant : LLVMFn :=
  { fnParallelPhiSwapLoop with
    blocks := [
      { label := "entry"
      , body := [.and_ "steps" .i64 (.reg "steps_raw") (k64 15)]
      , term := .br "loop" },
      { label := "loop"
      , phis := [
          { dst := "i", ty := .int .i64, incomings := [(k64 0, "entry"), (.reg "i_next", "body")] },
          { dst := "p", ty := .int .i64, incomings := [(.reg "x0", "entry"), (.reg "q_upd", "body")] },
          { dst := "q", ty := .int .i64, incomings := [(.reg "y0", "entry"), (.reg "q_upd", "body")] }
        ]
      , body := [.icmp "cont" .ult (.int .i64) (.reg "i") (.reg "steps")]
      , term := .condBr (.reg "cont") "body" "exit" },
      { label := "body"
      , body := [
          .mul "p_scaled" .none .i64 (.reg "p") (k64 3),
          .add "q_upd" .none .i64 (.reg "q") (.reg "p_scaled"),
          .add "i_next" .none .i64 (.reg "i") (k64 1)
        ]
      , term := .br "loop" },
      { label := "exit"
      , body := [
          .shl "p_hi" .none .i64 (.reg "p") (k64 7),
          .xor "res" .i64 (.reg "p_hi") (.reg "q")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnAllocaGepMemory : LLVMFn :=
  let arrTy := LLVMType.array 4 (.int .i64)
  { name := "diff_alloca_gep_load_store"
  , retTy := .int .i64
  , params := [p64 "a", p64 "b", p64 "idx_raw"]
  , blocks := [
      { label := "entry"
      , body := [
          .alloca "buf" arrTy 8,
          .getelementptr "p0" true arrTy (.reg "buf") [(.i64, k64 0), (.i64, k64 0)],
          .getelementptr "p1" true arrTy (.reg "buf") [(.i64, k64 0), (.i64, k64 1)],
          .getelementptr "p2" true arrTy (.reg "buf") [(.i64, k64 0), (.i64, k64 2)],
          .getelementptr "p3" true arrTy (.reg "buf") [(.i64, k64 0), (.i64, k64 3)],
          .add "v1" .none .i64 (.reg "a") (.reg "b"),
          .xor "v2" .i64 (.reg "a") (.reg "b"),
          .mul "v3" .none .i64 (.reg "v1") (k64 5),
          .store false (.int .i64) (.reg "a") (.reg "p0") 8,
          .store false (.int .i64) (.reg "v1") (.reg "p1") 8,
          .store false (.int .i64) (.reg "v2") (.reg "p2") 8,
          .store false (.int .i64) (.reg "v3") (.reg "p3") 8,
          .and_ "idx" .i64 (.reg "idx_raw") (k64 3),
          .getelementptr "psel" true arrTy (.reg "buf") [(.i64, k64 0), (.i64, .reg "idx")],
          .load "picked" false (.int .i64) (.reg "psel") 8,
          .load "head" false (.int .i64) (.reg "p0") 8,
          .add "res" .none .i64 (.reg "picked") (.reg "head")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnSwitchAndCalleeHelper : LLVMFn :=
  { name := "diff_helper_mix"
  , retTy := .int .i64
  , params := [p64 "x", p64 "y"]
  , blocks := [
      { label := "entry"
      , body := [
          .mul "m" .none .i64 (.reg "x") (k64 9),
          .add "res" .none .i64 (.reg "m") (.reg "y")
        ]
      , term := .ret (some (.int .i64, .reg "res")) }
    ] }

private def fnSwitchAndCall : LLVMFn :=
  { name := "diff_switch_and_call"
  , retTy := .int .i64
  , params := [p64 "tag_raw", p64 "x", p64 "y"]
  , blocks := [
      { label := "entry"
      , body := [
          .and_ "tag" .i64 (.reg "tag_raw") (k64 3)
        ]
      , term := .switch .i64 (.reg "tag") "def_blk" [
          (BitVec.ofNat 64 0, "case0"),
          (BitVec.ofNat 64 1, "case1"),
          (BitVec.ofNat 64 2, "case2")
        ] },
      { label := "case0"
      , body := [
          .call (some "r0") (.int .i64) "diff_helper_mix" [(.int .i64, .reg "x"), (.int .i64, .reg "y")]
        ]
      , term := .ret (some (.int .i64, .reg "r0")) },
      { label := "case1"
      , body := [
          .sub "r1" .none .i64 (.reg "x") (.reg "y")
        ]
      , term := .ret (some (.int .i64, .reg "r1")) },
      { label := "case2"
      , body := [
          .call (some "r2") (.int .i64) "diff_helper_mix" [(.int .i64, .reg "y"), (.int .i64, .reg "x")]
        ]
      , term := .ret (some (.int .i64, .reg "r2")) },
      { label := "def_blk"
      , body := [
          .xor "rd" .i64 (.reg "x") (.reg "y")
        ]
      , term := .ret (some (.int .i64, .reg "rd")) }
    ] }

private def loweredLnirDecls : List (String × LNIRDecl × Option (LLVMFn × String)) :=
  let dSub := mkBinScalarDecl "lnir_sub64" .i64 (.binOp .sub (.var 0) (.var 1))
  let dShl := mkBinScalarDecl "lnir_shl64" .i64 (.binOp .shl (.var 0) (.var 1))
  let dUlt := mkBinScalarDecl "lnir_ult64" .i1 (.binOp .lt (.var 0) (.var 1))
  let dDiv := mkBinScalarDecl "lnir_udiv64" .i64 (.binOp .div (.var 0) (.var 1))
  let dIte : LNIRDecl :=
    { name := "lnir_ite_diamond"
    , params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    , retTy := .i64
    , body :=
        .letBind 2 .i1 (.scalar (.binOp .lt (.var 0) (.var 1)))
          (.ite 2
            (.letBind 3 .i64 (.scalar (.binOp .sub (.var 1) (.var 0))) (.ret 3))
            (.letBind 4 .i64 (.scalar (.binOp .sub (.var 0) (.var 1))) (.ret 4))) }
  [ ("lowered_lnir_sub64", dSub, some ({ mutantM1 with name := "lnir_sub64" }, "M1 swapped sub operands"))
  , ("lowered_lnir_shl64", dShl, some ({ mutantM2 with name := "lnir_shl64" }, "M2 shl lowered as lshr"))
  , ("lowered_lnir_ult64", dUlt, some ({ mutantM3 with name := "lnir_ult64" }, "M3 ult relaxed to ule"))
  , ("lowered_lnir_udiv64_zero_safe", dDiv, none)
  , ("lowered_lnir_ite_diamond", dIte, none) ]

def buildAllDiffCases : List DiffCase :=
  let inputs2 : List (List UInt64) :=
    [ [0, 0], [1, 2], [2, 1], [7, 7], [42, 5], [100, 37]
    , [0x7fffffffffffffff, 1], [0x8000000000000000, 3]
    , [0xffffffffffffffff, 0], [0xfffffffffffffffe, 63]
    , [0x123456789abcdef0, 19], [0xfedcba9876543210, 0x0f0f0f0f0f0f0f0f] ]
  let inputs3 : List (List UInt64) :=
    [ [0, 0, 0], [1, 2, 1], [3, 5, 2], [7, 11, 3], [13, 17, 4]
    , [19, 23, 7], [0xffffffffffffffff, 42, 5], [0x8000000000000000, 9, 10] ]
  let handCrafted : List DiffCase :=
    [ buildCase "ast_alu_nsw_nuw_select" "poison_select_alu"
        (mkTestMod [fnAluFlagsSelect]) fnAluFlagsSelect inputs2 256
        (some (fnAluFlagsSelectMutant, "alu_select replaced by swapped sub"))
    , buildCase "ast_shifts_exact_casts" "poison_shift_cast"
        (mkTestMod [fnShiftsAndCasts]) fnShiftsAndCasts inputs2 256
        (some (fnShiftsMutant, "shift/cast replaced by unmasked lshr"))
    , buildCase "ast_div_rem_signed_unsigned" "div_rem"
        (mkTestMod [fnDivRemSignedUnsigned]) fnDivRemSignedUnsigned inputs2 256
    , buildCase "ast_parallel_phi_swap_loop" "cfg_phi_loop"
        (mkTestMod [fnParallelPhiSwapLoop]) fnParallelPhiSwapLoop inputs3 512
        (some (fnSequentialPhiBugMutant, "sequential phi overwrite bug"))
    , buildCase "ast_alloca_gep_load_store" "memory_gep"
        (mkTestMod [fnAllocaGepMemory]) fnAllocaGepMemory inputs3 256
    , buildCase "ast_switch_and_internal_call" "cfg_switch_call"
        (mkTestMod [fnSwitchAndCalleeHelper, fnSwitchAndCall]) fnSwitchAndCall inputs3 256 ]
  let loweredCases : List DiffCase :=
    loweredLnirDecls.filterMap fun (cid, decl, neg?) => do
      let fn ← lowerDeclWithFacts decl
      let mod_ := modOfFn fn
      some (buildCase cid "lowered_lnir" mod_ fn inputs2 256 neg?)
  handCrafted ++ loweredCases

private def vecToJson (v : DiffVector) : Json :=
  Json.mkObj [
    ("inputs", Json.arr (v.inputs.map (fun u => Json.str (toString u))).toArray),
    ("expectedTag", Json.str v.expectedTag),
    ("expectedWord", match v.expectedWord? with
      | some w => Json.str (toString w)
      | none => Json.null)
  ]

private def caseToJson (c : DiffCase) : Json :=
  Json.mkObj [
    ("id", Json.str c.id),
    ("category", Json.str c.category),
    ("fnName", Json.str c.fnName),
    ("arity", toJson c.arity),
    ("irText", Json.str c.irText),
    ("vectors", Json.arr (c.vectors.map vecToJson).toArray),
    ("negativeMutantIr", match c.negativeMutantIr? with
      | some ir => Json.str ir
      | none => Json.null),
    ("negativeMutantReason", match c.negativeMutantReason? with
      | some r => Json.str r
      | none => Json.null)
  ]

/-- Emit Alive2 translation-validation fixture pairs (typed `LLVMLower` specs vs mutants M1..M5). -/
def buildAlive2MutantFixturesJson : Json :=
  let pairs : List (String × String × LLVMFn × LLVMFn) :=
    let dSub := mkBinScalarDecl "mutant_m1_sub_swap" .i64 (.binOp .sub (.var 0) (.var 1))
    let dShl := mkBinScalarDecl "mutant_m2_shl_as_shr" .i64 (.binOp .shl (.var 0) (.var 1))
    let dUlt := mkBinScalarDecl "mutant_m3_ult64_as_ule64" .i1 (.binOp .lt (.var 0) (.var 1))
    let f1 := (lowerDeclWithFacts dSub).getD mutantM1
    let f2 := (lowerDeclWithFacts dShl).getD mutantM2
    let f3 := (lowerDeclWithFacts dUlt).getD mutantM3
    [ ("M1_sub_swap", "swapped sub operands", f1, mutantM1)
    , ("M2_shl_as_lshr", "shl lowered as lshr", f2, mutantM2)
    , ("M3_ult64_as_ule64", "ult i64 relaxed to ule i64", f3, mutantM3)
    , ("M4_ult256_as_ule256", "ult i256 relaxed to ule i256",
        { specUlt256Fn with name := "mutant_m4_ult256_as_ule256" }, mutantM4)
    , ("M5_udiv_unguarded", "unguarded udiv UB on zero divisor",
        { specUdivGuardFn with name := "mutant_m5_udiv_unguarded" }, mutantM5) ]
  let loweredPositives : List Json :=
    loweredLnirDecls.filterMap fun (cid, decl, _) => do
      let fn ← lowerDeclWithFacts decl
      some (Json.mkObj [
        ("id", Json.str cid),
        ("fnName", Json.str fn.name),
        ("srcIr", Json.str (PP.ppModule (modOfFn fn)))
      ])
  Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("loweredPositives", Json.arr loweredPositives.toArray),
    ("negativeMutants", Json.arr (pairs.map fun (mid, desc, srcFn, tgtFn) =>
      Json.mkObj [
        ("id", Json.str mid),
        ("description", Json.str desc),
        ("fnName", Json.str srcFn.name),
        ("srcIr", Json.str (PP.ppModule (modOfFn srcFn))),
        ("tgtIr", Json.str (PP.ppModule (modOfFn tgtFn)))
      ]).toArray)
  ]

def run (args : List String) : IO UInt32 := do
  if args.contains "--alive2-fixtures" then
    IO.println (Json.compress buildAlive2MutantFixturesJson)
    return 0
  let cases := buildAllDiffCases
  if cases.any (fun c => c.vectors.any (fun v => v.expectedTag != "val")) then
    IO.eprintln "[llvm-diff-suite] internal error: positive test vector did not evaluate to a concrete value"
    return 1
  let out := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("caseCount", toJson cases.length),
    ("cases", Json.arr (cases.map caseToJson).toArray)
  ]
  IO.println (Json.compress out)
  return 0

end LeanNative.Driver.LLVMDiffCLI
