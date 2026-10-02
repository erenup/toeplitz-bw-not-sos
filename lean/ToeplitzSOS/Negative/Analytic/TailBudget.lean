import ToeplitzSOS.Negative.Analytic.Tails

/-! # Tail budget at finite scales

A single degree-16 term of the exponential series is enough. This proves the
budget throughout the real interval `0 < ε ≤ 2⁻¹⁶`, without a dyadic induction.
-/

namespace ToeplitzSOS.Negative.Analytic

set_option maxRecDepth 4096

/-- A proved Taylor term bounds the reciprocal exponential at every scale. -/
theorem exp_neg_reciprocal_bound {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-(1 / (4 * ε))) ≤ (Nat.factorial 16 : ℝ) * (4 * ε) ^ 16 := by
  have h := Real.pow_div_factorial_le_exp (x := 1 / (4 * ε)) (by positivity) 16
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (Nat.factorial 16 : ℝ) * (4 * ε) ^ 16 by positivity)
  convert! hmul using 1
  field_simp [ne_of_gt hε]

/-- The geometric-tail budget, with the scale relation `m = ε⁻²` stated explicitly. -/
theorem tail_budget {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ (2 : ℝ)⁻¹ ^ 16)
    {m : ℕ} (hm : (m : ℝ) = ε⁻¹ ^ 2) :
    2 ^ 32 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) ≤ ε⁻¹ ^ 2 := by
  have he : -ε * (m : ℝ) / 4 = -(1 / (4 * ε)) := by
    rw [hm]
    field_simp [ne_of_gt hε]
  rw [he]
  have hsmall : (2 : ℝ) ^ 64 * Nat.factorial 16 * ε ^ 10 ≤ 1 := by
    calc
      _ ≤ (2 : ℝ) ^ 64 * Nat.factorial 16 * ((2 : ℝ)⁻¹ ^ 16) ^ 10 := by gcongr
      _ ≤ 1 := by norm_num
  calc
    _ ≤ 2 ^ 32 * ε⁻¹ ^ 8 * ((Nat.factorial 16 : ℝ) * (4 * ε) ^ 16) :=
      mul_le_mul_of_nonneg_left (exp_neg_reciprocal_bound hε) (by positivity)
    _ = (2 : ℝ) ^ 64 * Nat.factorial 16 * ε ^ 8 := by
      field_simp [ne_of_gt hε]
      ring
    _ ≤ ε⁻¹ ^ 2 := by
      rw [inv_pow, inv_eq_one_div, le_div_iff₀ (by positivity : 0 < ε ^ 2)]
      convert! hsmall using 1
      ring

/-- The scaled error is at most ε, again uniformly throughout the scale interval. -/
theorem scaled_tail_budget {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ (2 : ℝ)⁻¹ ^ 16)
    {m : ℕ} (hm : (m : ℝ) = ε⁻¹ ^ 2) :
    ε ^ 4 * (2 ^ 32 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4)) ≤ ε := by
  have h := mul_le_mul_of_nonneg_left (tail_budget hε hε1 hm) (show 0 ≤ ε ^ 4 by positivity)
  have he : ε ^ 4 * ε⁻¹ ^ 2 = ε ^ 2 := by field_simp
  rw [he] at h
  have hε2 : ε ≤ 1 := hε1.trans (by norm_num)
  exact h.trans (by nlinarith)

end ToeplitzSOS.Negative.Analytic
