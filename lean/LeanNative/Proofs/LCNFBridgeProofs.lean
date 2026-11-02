import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.LCNF
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.BackendProofs

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend.Proofs

/-!
# Machine-Checked LCNF-to-LNIR Bridge Soundness (`LeanNative.Proofs.LCNFBridgeProofs`)

Milestone M4 (Item 1): Proves `lowerLCNFCode_sound` (`0 sorryAx`, `Contract V2`) establishing
that whenever `LCNF.lowerCode c = .ok lnirCode` and `EnvCorresponds lcnfEnv lnirEnv`,
evaluating `c` under the independent `LCNF.evalLCNF` operational semantics produces the
exact same `(Val × HeapState)` outcome (including UB traps) as `evalCode` on `lnirCode`.
-/

/-- Pointwise correspondence between an LCNF free-variable environment and an LNIR `VarEnv`. -/
def EnvCorresponds (lcnfEnv : LCNF.Env) (lnirEnv : VarEnv) : Prop :=
  ∀ x : VarId, lcnfEnv x = lnirEnv x

/-- Re-export `LCNF.lowerCode` and `LCNF.evalLCNF` in `LeanNative.Proofs` for roadmap contract compatibility. -/
abbrev lowerCode : LCNF.Code → Except String LNIRCode := LCNF.lowerCode
abbrev evalLCNF : LCNF.Env → HeapState → LCNF.Code → Nat → Except UBError (Val × HeapState) := LCNF.evalLCNF

/-- Observational equivalence of evaluation outcomes (`Except UBError (Val × HeapState)`). -/
def EvalOutcomeEquiv (r1 r2 : Except UBError (Val × HeapState)) : Prop :=
  r1 = r2

infix:50 " ≈ " => EvalOutcomeEquiv

theorem envCorresponds_eq {lcnfEnv : LCNF.Env} {lnirEnv : VarEnv}
    (h : EnvCorresponds lcnfEnv lnirEnv) : lcnfEnv = lnirEnv :=
  funext h

theorem envCorresponds_bind {lcnfEnv : LCNF.Env} {lnirEnv : VarEnv}
    (h : EnvCorresponds lcnfEnv lnirEnv) (x : VarId) (v : Val) :
    EnvCorresponds (LCNF.Env.bind lcnfEnv x v) (lnirEnv.bind x v) := by
  intro y
  simp [LCNF.Env.bind, VarEnv.bind, h y]

theorem toBv_eq_word (w : UInt256) : LCNF.toBv256 w = LeanMLIR.word256 w := rfl

theorem ofBv_eq_word (w : BitVec 256) : LCNF.ofBv256 w = LeanMLIR.ofWord256 w := rfl

theorem promoteBv_eq_asWord (v : Val) : LCNF.promoteBv256 v = LeanMLIR.asWord256 v := by
  cases v <;> rfl

theorem primSar64_eq_sar64 (a b : BitVec 64) : LCNF.primSar64 a b = LeanMLIR.sar64 a b := rfl

theorem primSar256_eq_sar256 (a : BitVec 256) (s : Nat) :
    LCNF.primSar256 a s = LeanMLIR.sar256 a s := rfl

theorem prim_add (v1 v2 : Val) (hdom : StrictWordBinOpDom .add v1 v2) :
    LCNF.primBinOp .add v1 v2 = evalBinOp .add v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b => exact congrArg (fun w => Except.ok (Val.u256 w)) (u256_add_bv a b)
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_sub (v1 v2 : Val) (hdom : StrictWordBinOpDom .sub v1 v2) :
    LCNF.primBinOp .sub v1 v2 = evalBinOp .sub v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b => exact congrArg (fun w => Except.ok (Val.u256 w)) (u256_sub_bv a b)
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_mul (v1 v2 : Val) (hdom : StrictWordBinOpDom .mul v1 v2) :
    LCNF.primBinOp .mul v1 v2 = evalBinOp .mul v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b => exact congrArg (fun w => Except.ok (Val.u256 w)) (u256_mul_bv a b)
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_div (v1 v2 : Val) (hdom : StrictWordBinOpDom .div v1 v2) :
    LCNF.primBinOp .div v1 v2 = evalBinOp .div v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b =>
      have hne : b ≠ 0 := hdom
      have hbeq : (b.toBitVec == 0#64) = false := by
        cases h : b.toBitVec == 0#64 with
        | false => rfl
        | true =>
          have hb0 : b = 0 := UInt64.eq_of_toBitVec_eq (eq_of_beq h)
          exact False.elim (hne hb0)
      have hL : LCNF.primBinOp .div (.u64 a) (.u64 b) =
          (if b.toBitVec == 0#64 then Except.error UBError.divisionByZero
           else Except.ok (Val.u64 (UInt64.ofBitVec (a.toBitVec / b.toBitVec)))) := rfl
      rw [hL, hbeq]
      rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .div (.u256 a) (.u256 b) =
          (if LCNF.toBv256 b == 0#256 then Except.error UBError.divisionByZero
           else Except.ok (Val.u256 (LCNF.ofBv256 (LCNF.toBv256 a / LCNF.toBv256 b)))) := rfl
      rw [hL, eval_div_u256, match9_eq, toBv_eq_word, toBv_eq_word, ofBv_eq_word,
          opt_to_except _ _ _ Val.u256, u256_div_opt]
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_mod (v1 v2 : Val) (hdom : StrictWordBinOpDom .mod v1 v2) :
    LCNF.primBinOp .mod v1 v2 = evalBinOp .mod v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b =>
      have hne : b ≠ 0 := hdom
      have hbeq : (b.toBitVec == 0#64) = false := by
        cases h : b.toBitVec == 0#64 with
        | false => rfl
        | true =>
          have hb0 : b = 0 := UInt64.eq_of_toBitVec_eq (eq_of_beq h)
          exact False.elim (hne hb0)
      have hL : LCNF.primBinOp .mod (.u64 a) (.u64 b) =
          (if b.toBitVec == 0#64 then Except.error UBError.divisionByZero
           else Except.ok (Val.u64 (UInt64.ofBitVec (a.toBitVec % b.toBitVec)))) := rfl
      rw [hL, hbeq]
      rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .mod (.u256 a) (.u256 b) =
          (if LCNF.toBv256 b == 0#256 then Except.error UBError.divisionByZero
           else Except.ok (Val.u256 (LCNF.ofBv256 (LCNF.toBv256 a % LCNF.toBv256 b)))) := rfl
      rw [hL, eval_mod_u256, match9_eq, toBv_eq_word, toBv_eq_word, ofBv_eq_word,
          opt_to_except _ _ _ Val.u256, u256_mod_opt]
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_bitAnd (v1 v2 : Val) (hdom : StrictWordBinOpDom .bitAnd v1 v2) :
    LCNF.primBinOp .bitAnd v1 v2 = evalBinOp .bitAnd v1 v2 := by
  cases v1 with
  | u64 _ =>
    cases v2 with
    | u64 _ => rfl
    | _ => nomatch hdom
  | u256 _ =>
    cases v2 with
    | u256 _ => rfl
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_bitOr (v1 v2 : Val) (hdom : StrictWordBinOpDom .bitOr v1 v2) :
    LCNF.primBinOp .bitOr v1 v2 = evalBinOp .bitOr v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => exact congrArg (fun x => Except.ok (Val.u64 x)) (u64_or_bv a b)
    | _ => nomatch hdom
  | u256 _ =>
    cases v2 with
    | u256 _ => rfl
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_bitXor (v1 v2 : Val) (hdom : StrictWordBinOpDom .bitXor v1 v2) :
    LCNF.primBinOp .bitXor v1 v2 = evalBinOp .bitXor v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => exact congrArg (fun x => Except.ok (Val.u64 x)) (u64_xor_bv a b)
    | _ => nomatch hdom
  | u256 _ =>
    cases v2 with
    | u256 _ => rfl
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_shl (v1 v2 : Val) (hdom : StrictWordBinOpDom .shl v1 v2) :
    LCNF.primBinOp .shl v1 v2 = evalBinOp .shl v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => exact congrArg (fun x => Except.ok (Val.u64 x)) (u64_shl_bv a b)
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .shl (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (LCNF.ofBv256 (LCNF.toBv256 a <<< (LCNF.toBv256 b).toNat))) := rfl
      have hR : evalBinOp .shl (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (UInt256.shl a b.toNat)) := rfl
      rw [hL, hR, toBv_eq_word, toBv_eq_word, ofBv_eq_word, word256_toNat, u256_shl_bv]
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_shr (v1 v2 : Val) (hdom : StrictWordBinOpDom .shr v1 v2) :
    LCNF.primBinOp .shr v1 v2 = evalBinOp .shr v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b => exact congrArg (fun x => Except.ok (Val.u64 x)) (u64_shr_bv a b)
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .shr (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (LCNF.ofBv256 (LCNF.toBv256 a >>> (LCNF.toBv256 b).toNat))) := rfl
      have hR : evalBinOp .shr (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (UInt256.shr a b.toNat)) := rfl
      rw [hL, hR, toBv_eq_word, toBv_eq_word, ofBv_eq_word, word256_toNat, u256_shr_bv]
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_sar (v1 v2 : Val) (hdom : StrictWordBinOpDom .sar v1 v2) :
    LCNF.primBinOp .sar v1 v2 = evalBinOp .sar v1 v2 := by
  cases v1 with
  | u64 a =>
    cases v2 with
    | u64 b =>
      have hL : LCNF.primBinOp .sar (.u64 a) (.u64 b) =
          Except.ok (Val.u64 (UInt64.ofBitVec (LCNF.primSar64 a.toBitVec b.toBitVec))) := rfl
      rw [hL, primSar64_eq_sar64, u64_sar_bv]
      rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .sar (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (LCNF.ofBv256 (LCNF.primSar256 (LCNF.toBv256 a) (LCNF.toBv256 b).toNat))) := rfl
      have hR : evalBinOp .sar (.u256 a) (.u256 b) =
          Except.ok (Val.u256 (UInt256.sar a b.toNat)) := rfl
      rw [hL, hR, toBv_eq_word, toBv_eq_word, ofBv_eq_word, primSar256_eq_sar256, word256_toNat, u256_sar_bv]
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_eq (v1 v2 : Val) (hdom : StrictWordBinOpDom .eq v1 v2) :
    LCNF.primBinOp .eq v1 v2 = evalBinOp .eq v1 v2 := by
  cases v1 with
  | u64 _ =>
    cases v2 with
    | u64 _ => rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .eq (.u256 a) (.u256 b) =
          Except.ok (Val.bool (LCNF.toBv256 a == LCNF.toBv256 b)) := rfl
      rw [hL, toBv_eq_word, toBv_eq_word, word_eq]
      rfl
    | _ => nomatch hdom
  | bool _ =>
    cases v2 with
    | bool _ => rfl
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_lt (v1 v2 : Val) (hdom : StrictWordBinOpDom .lt v1 v2) :
    LCNF.primBinOp .lt v1 v2 = evalBinOp .lt v1 v2 := by
  cases v1 with
  | u64 _ =>
    cases v2 with
    | u64 _ => rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .lt (.u256 a) (.u256 b) =
          Except.ok (Val.bool (decide (LCNF.toBv256 a < LCNF.toBv256 b))) := rfl
      rw [hL, toBv_eq_word, toBv_eq_word, word_lt]
      rfl
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_le (v1 v2 : Val) (hdom : StrictWordBinOpDom .le v1 v2) :
    LCNF.primBinOp .le v1 v2 = evalBinOp .le v1 v2 := by
  cases v1 with
  | u64 _ =>
    cases v2 with
    | u64 _ => rfl
    | _ => nomatch hdom
  | u256 a =>
    cases v2 with
    | u256 b =>
      have hL : LCNF.primBinOp .le (.u256 a) (.u256 b) =
          Except.ok (Val.bool (decide (LCNF.toBv256 a ≤ LCNF.toBv256 b))) := rfl
      rw [hL, toBv_eq_word, toBv_eq_word, word_le]
      rfl
    | _ => nomatch hdom
  | _ => nomatch hdom

theorem prim_addChecked (v1 v2 : Val) :
    LCNF.primBinOp .addChecked256 v1 v2 = evalBinOp .addChecked256 v1 v2 := by
  have hL : LCNF.primBinOp .addChecked256 v1 v2 =
      (match (v1.toU256?).map LeanMLIR.word256, (v2.toU256?).map LeanMLIR.word256 with
       | some a, some b =>
         if BitVec.uaddOverflow a b then Except.error (UBError.arithmeticOverflow "addChecked256 overflow")
         else Except.ok (Val.u256 (LCNF.ofBv256 (a + b)))
       | _, _ => Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")) := by
    have h0 : LCNF.primBinOp .addChecked256 v1 v2 =
      (match LCNF.promoteBv256 v1, LCNF.promoteBv256 v2 with
       | some a, some b =>
         if BitVec.uaddOverflow a b then Except.error (UBError.arithmeticOverflow "addChecked256 overflow")
         else Except.ok (Val.u256 (LCNF.ofBv256 (a + b)))
       | _, _ => Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")) := rfl
    rw [h0, promoteBv_eq_asWord v1, promoteBv_eq_asWord v2, asWord256_eq v1, asWord256_eq v2]
  have hM := optPair_map_eq (Except UBError Val) v1.toU256? v2.toU256?
    (fun a b =>
      if BitVec.uaddOverflow a b then Except.error (UBError.arithmeticOverflow "addChecked256 overflow")
      else Except.ok (Val.u256 (LCNF.ofBv256 (a + b))))
    (fun a b =>
      evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
        (fun res => Except.ok (Val.u256 res))
        (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
    (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands"))
    addChecked_inner_eq
  exact @Eq.trans (Except UBError Val) _ _ _ hL
    (@Eq.trans (Except UBError Val) _
      (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.addChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "addChecked256 overflow")))
        (Except.error (UBError.typeError "addChecked256 requires u256/u64 operands")))
      (evalBinOp .addChecked256 v1 v2)
      hM (Eq.symm (eval_addChecked_pair v1 v2)))

theorem prim_subChecked (v1 v2 : Val) :
    LCNF.primBinOp .subChecked256 v1 v2 = evalBinOp .subChecked256 v1 v2 := by
  have hL : LCNF.primBinOp .subChecked256 v1 v2 =
      (match (v1.toU256?).map LeanMLIR.word256, (v2.toU256?).map LeanMLIR.word256 with
       | some a, some b =>
         if decide (a < b) then Except.error (UBError.arithmeticOverflow "subChecked256 underflow")
         else Except.ok (Val.u256 (LCNF.ofBv256 (a - b)))
       | _, _ => Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")) := by
    have h0 : LCNF.primBinOp .subChecked256 v1 v2 =
      (match LCNF.promoteBv256 v1, LCNF.promoteBv256 v2 with
       | some a, some b =>
         if decide (a < b) then Except.error (UBError.arithmeticOverflow "subChecked256 underflow")
         else Except.ok (Val.u256 (LCNF.ofBv256 (a - b)))
       | _, _ => Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")) := rfl
    rw [h0, promoteBv_eq_asWord v1, promoteBv_eq_asWord v2, asWord256_eq v1, asWord256_eq v2]
  have hM := optPair_map_eq (Except UBError Val) v1.toU256? v2.toU256?
    (fun a b =>
      if decide (a < b) then Except.error (UBError.arithmeticOverflow "subChecked256 underflow")
      else Except.ok (Val.u256 (LCNF.ofBv256 (a - b))))
    (fun a b =>
      evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
        (fun res => Except.ok (Val.u256 res))
        (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
    (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands"))
    subChecked_inner_eq
  exact @Eq.trans (Except UBError Val) _ _ _ hL
    (@Eq.trans (Except UBError Val) _
      (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.subChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "subChecked256 underflow")))
        (Except.error (UBError.typeError "subChecked256 requires u256/u64 operands")))
      (evalBinOp .subChecked256 v1 v2)
      hM (Eq.symm (eval_subChecked_pair v1 v2)))

theorem prim_mulChecked (v1 v2 : Val) :
    LCNF.primBinOp .mulChecked256 v1 v2 = evalBinOp .mulChecked256 v1 v2 := by
  have hL : LCNF.primBinOp .mulChecked256 v1 v2 =
      (match (v1.toU256?).map LeanMLIR.word256, (v2.toU256?).map LeanMLIR.word256 with
       | some a, some b =>
         if BitVec.umulOverflow a b then Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")
         else Except.ok (Val.u256 (LCNF.ofBv256 (a * b)))
       | _, _ => Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")) := by
    have h0 : LCNF.primBinOp .mulChecked256 v1 v2 =
      (match LCNF.promoteBv256 v1, LCNF.promoteBv256 v2 with
       | some a, some b =>
         if BitVec.umulOverflow a b then Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")
         else Except.ok (Val.u256 (LCNF.ofBv256 (a * b)))
       | _, _ => Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")) := rfl
    rw [h0, promoteBv_eq_asWord v1, promoteBv_eq_asWord v2, asWord256_eq v1, asWord256_eq v2]
  have hM := optPair_map_eq (Except UBError Val) v1.toU256? v2.toU256?
    (fun a b =>
      if BitVec.umulOverflow a b then Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")
      else Except.ok (Val.u256 (LCNF.ofBv256 (a * b))))
    (fun a b =>
      evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
        (fun res => Except.ok (Val.u256 res))
        (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
    (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands"))
    mulChecked_inner_eq
  exact @Eq.trans (Except UBError Val) _ _ _ hL
    (@Eq.trans (Except UBError Val) _
      (optPairMatch (Except UBError Val) v1.toU256? v2.toU256?
        (fun a b =>
          evalBinOp.match_9 (fun _ => Except UBError Val) (a.mulChecked b)
            (fun res => Except.ok (Val.u256 res))
            (fun _ => Except.error (UBError.arithmeticOverflow "mulChecked256 overflow")))
        (Except.error (UBError.typeError "mulChecked256 requires u256/u64 operands")))
      (evalBinOp .mulChecked256 v1 v2)
      hM (Eq.symm (eval_mulChecked_pair v1 v2)))

theorem prim_clmul (v1 v2 : Val) : LCNF.primBinOp .clmul64 v1 v2 = evalBinOp .clmul64 v1 v2 := by
  cases v1 <;> cases v2 <;> rfl
theorem prim_clmulHi (v1 v2 : Val) : LCNF.primBinOp .clmul64Hi v1 v2 = evalBinOp .clmul64Hi v1 v2 := by
  cases v1 <;> cases v2 <;> rfl
theorem prim_gf2 (v1 v2 : Val) : LCNF.primBinOp .gf2Affine v1 v2 = evalBinOp .gf2Affine v1 v2 := by
  cases v1 <;> cases v2 <;> rfl
theorem prim_eor3 (v1 v2 : Val) : LCNF.primBinOp .eor3 v1 v2 = evalBinOp .eor3 v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem primBinOp_eq_evalBinOp (op : BinOp) (v1 v2 : Val)
    (hdom : StrictWordBinOpDom op v1 v2) :
    LCNF.primBinOp op v1 v2 = evalBinOp op v1 v2 := by
  cases op with
  | add => exact prim_add v1 v2 hdom
  | sub => exact prim_sub v1 v2 hdom
  | mul => exact prim_mul v1 v2 hdom
  | div => exact prim_div v1 v2 hdom
  | mod => exact prim_mod v1 v2 hdom
  | bitAnd => exact prim_bitAnd v1 v2 hdom
  | bitOr => exact prim_bitOr v1 v2 hdom
  | bitXor => exact prim_bitXor v1 v2 hdom
  | shl => exact prim_shl v1 v2 hdom
  | shr => exact prim_shr v1 v2 hdom
  | sar => exact prim_sar v1 v2 hdom
  | eq => exact prim_eq v1 v2 hdom
  | lt => exact prim_lt v1 v2 hdom
  | le => exact prim_le v1 v2 hdom
  | addChecked256 => exact prim_addChecked v1 v2
  | subChecked256 => exact prim_subChecked v1 v2
  | mulChecked256 => exact prim_mulChecked v1 v2
  | clmul64 => exact prim_clmul v1 v2
  | clmul64Hi => exact prim_clmulHi v1 v2
  | gf2Affine => exact prim_gf2 v1 v2
  | eor3 => exact prim_eor3 v1 v2

theorem lcnf_unary_not_u64 (n : UInt64) :
    LCNF.primUnaryOp .not (.u64 n) = .ok (.u64 (~~~n)) := rfl

theorem lcnf_unary_not_u256 (w : UInt256) :
    LCNF.primUnaryOp .not (.u256 w) = .ok (.u256 (UInt256.bitNot w)) := rfl

theorem lcnf_unary_not_bool (b : Bool) :
    LCNF.primUnaryOp .not (.bool b) = .ok (.bool (!b)) := rfl

theorem lcnf_unary_neg_u64 (n : UInt64) :
    LCNF.primUnaryOp .neg (.u64 n) = .ok (.u64 (0 - n)) := rfl

theorem lcnf_unary_neg_u256 (w : UInt256) :
    LCNF.primUnaryOp .neg (.u256 w) = .ok (.u256 (UInt256.sub UInt256.zero w)) := by
  have hL : LCNF.primUnaryOp .neg (.u256 w) =
      .ok (.u256 (LCNF.ofBv256 (0#256 - LCNF.toBv256 w))) := rfl
  rw [hL, toBv_eq_word, ofBv_eq_word, neg256_eq]

theorem lcnf_unary_clz_u256 (w : UInt256) :
    LCNF.primUnaryOp .clz256 (.u256 w) = .ok (.u256 (UInt256.clz w)) := by
  have hL : LCNF.primUnaryOp .clz256 (.u256 w) =
      .ok (.u256 (UInt256.clz (LCNF.ofBv256 (LCNF.toBv256 w)))) := rfl
  rw [hL, toBv_eq_word, ofBv_eq_word, ofWord_id]

theorem lcnf_unary_clz_u64 (n : UInt64) :
    LCNF.primUnaryOp .clz256 (.u64 n) =
      .ok (.u256 (UInt256.clz (UInt256.ofUInt64 n))) := by
  have hL : LCNF.primUnaryOp .clz256 (.u64 n) =
      .ok (.u256 (UInt256.clz (LCNF.ofBv256 (BitVec.ofNat 256 n.toBitVec.toNat)))) := rfl
  rw [hL, ofBv_eq_word, ofWord_ofU64]

theorem primUnaryOp_eq_evalUnaryOp (op : UnaryOp) (v : Val) :
    LCNF.primUnaryOp op v = evalUnaryOp op v := by
  cases op with
  | not =>
    cases v with
    | u64 n => exact lcnf_unary_not_u64 n
    | u256 w => exact lcnf_unary_not_u256 w
    | bool b => exact lcnf_unary_not_bool b
    | _ => rfl
  | neg =>
    cases v with
    | u64 n => exact lcnf_unary_neg_u64 n
    | u256 w => exact lcnf_unary_neg_u256 w
    | _ => rfl
  | clz256 =>
    cases v with
    | u256 w => exact lcnf_unary_clz_u256 w
    | u64 n => exact lcnf_unary_clz_u64 n
    | _ => rfl

/-- Strict typing and non-zero `u64` divisor precondition for `LCNF.LetValue`. -/
def StrictLetValue (env : LCNF.Env) : LCNF.LetValue → Prop
  | .binOp op aVar bVar =>
    ∀ va vb, env aVar = some va → env bVar = some vb → StrictWordBinOpDom op va vb
  | _ => True

/-- Execution-aware strict typing precondition for `LCNF.Code`. -/
def StrictLCNFCode (env : LCNF.Env) (st : HeapState) : LCNF.Code → Prop
  | .letBind dst _ty val k =>
    StrictLetValue env val ∧
      ∀ v st', LCNF.evalLetValue env st val = .ok (v, st') →
        StrictLCNFCode (LCNF.Env.bind env dst v) st' k
  | .inc objVar count k =>
    ∀ st', st.evalIncRef env objVar count = .ok st' → StrictLCNFCode env st' k
  | .dec objVar count k =>
    ∀ st', st.evalDecRef env objVar count = .ok st' → StrictLCNFCode env st' k
  | .casesBool discr falseBranch trueBranch =>
    (∀ v, env discr = some v →
      match v with
      | .bool false | .u64 _ | .u256 _ => StrictLCNFCode env st falseBranch
      | _ => True) ∧
    (∀ v, env discr = some v →
      match v with
      | .bool true | .u64 _ | .u256 _ => StrictLCNFCode env st trueBranch
      | _ => True)
  | .return _ | .unreach => True

/-- Soundness of `LCNF.lowerLetValue` with respect to `LCNF.evalLetValue` and `evalExpr`. -/
theorem lowerLetValue_sound (val : LCNF.LetValue) (expr : LNIRExpr)
    (env : VarEnv) (st : HeapState)
    (h_strict : StrictLetValue env val)
    (h_lv : LCNF.lowerLetValue val = .ok expr) :
    LCNF.evalLetValue env st val = evalExpr env st expr := by
  cases val with
  | litU64 n =>
    injection h_lv with heq
    subst heq
    rfl
  | litBool b =>
    injection h_lv with heq
    subst heq
    rfl
  | litU256 w =>
    injection h_lv with heq
    subst heq
    rfl
  | fvar x =>
    injection h_lv with heq
    subst heq
    dsimp [LCNF.evalLetValue, evalExpr, evalScalarExpr]
    cases env x <;> rfl
  | binOp op aVar bVar =>
    injection h_lv with heq
    subst heq
    dsimp [LCNF.lowerLetValue, LCNF.evalLetValue, evalExpr, evalScalarExpr]
    cases ha : env aVar with
    | none => rfl
    | some va =>
      cases hb : env bVar with
      | none => rfl
      | some vb =>
        dsimp only
        rw [primBinOp_eq_evalBinOp op va vb (h_strict va vb ha hb)]
        cases evalBinOp op va vb <;> rfl
  | unaryOp op aVar =>
    injection h_lv with heq
    subst heq
    dsimp [LCNF.lowerLetValue, LCNF.evalLetValue, evalExpr, evalScalarExpr]
    cases env aVar with
    | none => rfl
    | some va =>
      dsimp only
      rw [primUnaryOp_eq_evalUnaryOp op va]
      cases evalUnaryOp op va <;> rfl
  | mkPair aVar bVar =>
    injection h_lv with heq
    subst heq
    dsimp [LCNF.evalLetValue, evalExpr, evalVarList]
    cases env aVar with
    | none => rfl
    | some va =>
      cases env bVar with
      | none => rfl
      | some vb => rfl
  | projTuple tupleVar idx =>
    injection h_lv with heq
    subst heq
    rfl
  | sarrayLen arrVar =>
    injection h_lv with heq
    subst heq
    rfl
  | sarrayGet arrVar idxVar elemTy =>
    injection h_lv with heq
    subst heq
    rfl
  | sarraySet arrVar idxVar valVar elemTy =>
    injection h_lv with heq
    subst heq
    rfl
  | unsupportedCall fnName =>
    simp [LCNF.lowerLetValue] at h_lv

/-- Milestone M4 (Item 1): Machine-checked LCNF-to-LNIR bridge soundness (`lowerLCNFCode_sound`).
    Proved by structural induction on `c : LCNF.Code` against the independent `LCNF.evalLCNF`
    operational semantics (`0 sorryAx`). -/
theorem lowerLCNFCode_sound (c : LCNF.Code) (lnirCode : LNIRCode)
    (lcnfEnv : LCNF.Env) (lnirEnv : VarEnv) (st : HeapState) (fuel : Nat)
    (h_env : EnvCorresponds lcnfEnv lnirEnv)
    (h_strict : StrictLCNFCode lcnfEnv st c)
    (h_lower : lowerCode c = .ok lnirCode) :
    evalLCNF lcnfEnv st c fuel ≈ evalCode fuel lnirEnv st lnirCode := by
  unfold EvalOutcomeEquiv evalLCNF lowerCode at *
  induction c generalizing lnirCode lcnfEnv lnirEnv st with
  | letBind dst ty val k ih =>
    dsimp [LCNF.lowerCode] at h_lower
    rcases h_strict with ⟨hslv, hsk⟩
    cases hlv : LCNF.lowerLetValue val with
    | error err =>
      rw [hlv] at h_lower
      contradiction
    | ok expr =>
      rw [hlv] at h_lower
      cases hk : LCNF.lowerCode k with
      | error err =>
        rw [hk] at h_lower
        contradiction
      | ok k' =>
        rw [hk] at h_lower
        injection h_lower with heq
        subst heq
        have henv_eq := envCorresponds_eq h_env
        subst henv_eq
        dsimp [LCNF.evalLCNF, evalCode]
        have hsound := lowerLetValue_sound val expr lcnfEnv st hslv hlv
        rw [hsound]
        cases hexpr : evalExpr lcnfEnv st expr with
        | error _ => rfl
        | ok pair =>
          have heval_lv : LCNF.evalLetValue lcnfEnv st val = .ok (pair.1, pair.2) := by
            rw [hsound, hexpr]
          exact ih k' (LCNF.Env.bind lcnfEnv dst pair.1) (lcnfEnv.bind dst pair.1) pair.2
            (envCorresponds_bind h_env dst pair.1) (hsk pair.1 pair.2 heval_lv) hk
  | inc objVar count k ih =>
    dsimp [LCNF.lowerCode] at h_lower
    cases hk : LCNF.lowerCode k with
    | error err =>
      rw [hk] at h_lower
      contradiction
    | ok k' =>
      rw [hk] at h_lower
      injection h_lower with heq
      subst heq
      have henv_eq := envCorresponds_eq h_env
      subst henv_eq
      dsimp [LCNF.evalLCNF, evalCode]
      cases hinc : st.evalIncRef lcnfEnv objVar count with
      | error _ => rfl
      | ok st' => exact ih k' lcnfEnv lcnfEnv st' h_env (h_strict st' hinc) hk
  | dec objVar count k ih =>
    dsimp [LCNF.lowerCode] at h_lower
    cases hk : LCNF.lowerCode k with
    | error err =>
      rw [hk] at h_lower
      contradiction
    | ok k' =>
      rw [hk] at h_lower
      injection h_lower with heq
      subst heq
      have henv_eq := envCorresponds_eq h_env
      subst henv_eq
      dsimp [LCNF.evalLCNF, evalCode]
      cases hdec : st.evalDecRef lcnfEnv objVar count with
      | error _ => rfl
      | ok st' => exact ih k' lcnfEnv lcnfEnv st' h_env (h_strict st' hdec) hk
  | casesBool discr falseBranch trueBranch ihf iht =>
    dsimp [LCNF.lowerCode] at h_lower
    rcases h_strict with ⟨hsf, hst⟩
    cases hfb : LCNF.lowerCode falseBranch with
    | error err =>
      rw [hfb] at h_lower
      contradiction
    | ok fb' =>
      rw [hfb] at h_lower
      cases htb : LCNF.lowerCode trueBranch with
      | error err =>
        rw [htb] at h_lower
        contradiction
      | ok tb' =>
        rw [htb] at h_lower
        injection h_lower with heq
        subst heq
        have henv_eq := envCorresponds_eq h_env
        subst henv_eq
        dsimp [LCNF.evalLCNF, evalCode]
        cases hdiscr : lcnfEnv discr with
        | none => rfl
        | some cval =>
          cases cval with
          | bool b =>
            cases b with
            | false =>
              exact ihf fb' lcnfEnv lcnfEnv st h_env (hsf (.bool false) hdiscr) hfb
            | true =>
              exact iht tb' lcnfEnv lcnfEnv st h_env (hst (.bool true) hdiscr) htb
          | u64 n =>
            simp only
            split
            · exact iht tb' lcnfEnv lcnfEnv st h_env (hst (.u64 n) hdiscr) htb
            · exact ihf fb' lcnfEnv lcnfEnv st h_env (hsf (.u64 n) hdiscr) hfb
          | u256 w =>
            simp only
            split
            · exact iht tb' lcnfEnv lcnfEnv st h_env (hst (.u256 w) hdiscr) htb
            · exact ihf fb' lcnfEnv lcnfEnv st h_env (hsf (.u256 w) hdiscr) hfb
          | _ => rfl
  | «return» v =>
    dsimp [LCNF.lowerCode] at h_lower
    injection h_lower with heq
    subst heq
    have henv_eq := envCorresponds_eq h_env
    subst henv_eq
    rfl
  | unreach =>
    dsimp [LCNF.lowerCode] at h_lower
    injection h_lower with heq
    subst heq
    rfl

end LeanNative.Proofs
