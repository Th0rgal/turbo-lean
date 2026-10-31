import B2.ProbeClif

/-! Operation-level proof of the safe-denominator construction in Backend.Clif.totalDiv.
This uses both repositories' definitions; instruction-sequence simulation remains O3. -/
namespace B2.Division
open LeanNative.IR LeanNative.Semantics

theorem safe_denominator (y : UInt64) :
    (if y = 0 then (1 : UInt64) else y) ≠ 0 := by
  split <;> simp_all

theorem total_div_agrees (x y : UInt64) :
    (if y = 0 then .ok (0 : UInt64).toBitVec else
      Clif.Sem.udiv x.toBitVec (if y = 0 then (1 : UInt64) else y).toBitVec) =
      .ok (x / y).toBitVec := by
  by_cases h : y = 0
  · simp [h]
  · simpa [h] using (B2.Probe.div_agrees_nonzero x y h).2

theorem total_mod_agrees (x y : UInt64) :
    (if y = 0 then .ok x.toBitVec else
      Clif.Sem.urem x.toBitVec (if y = 0 then (1 : UInt64) else y).toBitVec) =
      .ok (x % y).toBitVec := by
  by_cases h : y = 0
  · simp [h]
  · have hv : y.toBitVec ≠ 0 :=
      fun e => h (UInt64.toBitVec_inj.mp (by simpa using e))
    simp only [h, ite_false, Clif.Sem.urem, hv, UInt64.toBitVec_mod]

/-- The eagerly executed division itself never sees a zero denominator. -/
theorem safe_div_executes (x y : UInt64) :
    Clif.Sem.udiv x.toBitVec (if y = 0 then (1 : UInt64) else y).toBitVec =
      .ok (x / (if y = 0 then 1 else y)).toBitVec :=
  (B2.Probe.div_agrees_nonzero x _ (safe_denominator y)).2

#print axioms total_div_agrees
#print axioms total_mod_agrees
#print axioms safe_div_executes
end B2.Division
