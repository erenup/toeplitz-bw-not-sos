import ToeplitzSOS.Negative.CornerCorrection

/-!
# Uniform bounds for the actual mixed correction coefficients

The averaged mixed Gram has the fixed baseline diagonal. Finite
Cauchy--Schwarz and the literal baseline entries give the coefficient
bound required by the analytic tail interface.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- The mixed baseline diagonal is nonnegative and bounded by its product weight. -/
theorem baselineMixedEntry_diagonal_bounds {m : ℕ} (p q : Fin m) :
    0 ≤ baselineMixedEntry p q p q ∧
      baselineMixedEntry p q p q ≤ 2 * (p.val + 1) * (q.val + 1) := by
  have he : baselineMixedEntry p q p q =
      2 * (p.val + 1 : ℝ) * (q.val + 1) - 2 * min (p.val + 1 : ℝ) (q.val + 1) := by
    simp [baselineMixedEntry, min_add_add_right]
  have hp : (p.val + 1 : ℝ) ≤ (p.val + 1 : ℝ) * (q.val + 1) := by
    nlinarith [show (0 : ℝ) ≤ p.val from Nat.cast_nonneg _, show (0 : ℝ) ≤ q.val from Nat.cast_nonneg _,
      mul_nonneg (show (0 : ℝ) ≤ p.val from Nat.cast_nonneg _) (show (0 : ℝ) ≤ q.val from Nat.cast_nonneg _)]
  have hm : min (p.val + 1 : ℝ) (q.val + 1) ≤ (p.val + 1 : ℝ) * (q.val + 1) :=
    (min_le_left _ _).trans hp
  have hn : 0 ≤ min (p.val + 1 : ℝ) (q.val + 1) := le_min (by positivity) (by positivity)
  rw [he]
  constructor <;> nlinarith

private theorem min_le_sqrt_weight {m : ℕ} (p q r s : Fin m) :
    (min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) : ℕ) ≤
      Real.sqrt ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ) := by
  let k := min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1))
  have hp : (k : ℝ) ≤ p.val + 1 := by
    exact_mod_cast (show k ≤ p.val + 1 from (min_le_left _ _).trans (min_le_left _ _))
  have hr : (k : ℝ) ≤ r.val + 1 := by
    exact_mod_cast (show k ≤ r.val + 1 from (min_le_right _ _).trans (min_le_left _ _))
  have hk : (k : ℝ) ^ 2 ≤ (p.val + 1 : ℝ) * (r.val + 1) := by
    simpa only [pow_two] using mul_le_mul hp hr (Nat.cast_nonneg k) (by positivity)
  have hqs : (1 : ℝ) ≤ (q.val + 1) * (s.val + 1) := by
    nlinarith [show (0 : ℝ) ≤ q.val from Nat.cast_nonneg _, show (0 : ℝ) ≤ s.val from Nat.cast_nonneg _,
      mul_nonneg (show (0 : ℝ) ≤ q.val from Nat.cast_nonneg _) (show (0 : ℝ) ≤ s.val from Nat.cast_nonneg _)]
  have hmul := mul_le_mul_of_nonneg_left hqs (show 0 ≤ (p.val + 1 : ℝ) * (r.val + 1) by positivity)
  have hbound : (k : ℝ) ^ 2 ≤ (p.val + 1 : ℝ) * (q.val + 1) * (r.val + 1) * (s.val + 1) := by
    nlinarith [hmul]
  have hs := Real.sq_sqrt (show 0 ≤ (p.val + 1 : ℝ) * (q.val + 1) * (r.val + 1) * (s.val + 1) by positivity)
  have hn := Real.sqrt_nonneg ((p.val + 1 : ℝ) * (q.val + 1) * (r.val + 1) * (s.val + 1))
  change (k : ℝ) ≤ _
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Every literal mixed baseline entry obeys the product-weight square-root bound. -/
theorem baselineMixedEntry_abs_le {m : ℕ} (p q r s : Fin m) :
    |baselineMixedEntry p q r s| ≤
      2 * Real.sqrt ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ) := by
  by_cases hd : p = r ∧ q = s
  · obtain ⟨rfl, rfl⟩ := hd
    have hb := baselineMixedEntry_diagonal_bounds p q
    have he : ((p.val + 1) * (q.val + 1) * (p.val + 1) * (q.val + 1) : ℝ) =
        ((p.val + 1) * (q.val + 1) : ℝ) ^ 2 := by ring
    rw [abs_of_nonneg hb.1, he, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [mul_assoc] using hb.2
  · by_cases ht : p.val + q.val = r.val + s.val
    · have he : baselineMixedEntry p q r s =
          -(2 * (min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) : ℕ) : ℝ) := by
        simp [baselineMixedEntry, hd, ht]
      rw [he, abs_neg, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (min_le_sqrt_weight p q r s) (by norm_num)
    · rw [baselineMixedEntry_eq_zero_of_ne p q r s ht, abs_zero]
      positivity

/-- Finite Cauchy--Schwarz bounds every averaged mixed Gram entry by its
fixed diagonal product weights. -/
theorem averagedMixedRows_abs_le {m n : ℕ} (a b : Fin n → PureIndex m → ℝ)
    (c : Fin n → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (p q r s : Fin m) : |mixedRowGram (averagedMixedRows c) p q r s| ≤
      2 * Real.sqrt ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ) := by
  let e := averagedMixedRows c
  have hc := sum_mul_sq_le_sq_mul_sq univ (fun j => e j p q) (fun j => e j r s)
  change mixedRowGram e p q r s ^ 2 ≤ (∑ j, e j p q ^ 2) * (∑ j, e j r s ^ 2) at hc
  have hdiag (u v : Fin m) : (∑ j, e j u v ^ 2) = baselineMixedEntry u v u v := by
    simpa only [e, pow_two, mixedRowGram] using averagedMixedRows_diagonal a b c h u v
  rw [hdiag p q, hdiag r s] at hc
  have hp := baselineMixedEntry_diagonal_bounds p q
  have hr := baselineMixedEntry_diagonal_bounds r s
  have hb := mul_le_mul hp.2 hr.2 hr.1 (show (0 : ℝ) ≤ 2 * (p.val + 1) * (q.val + 1) by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ (p.val + 1 : ℝ) * (q.val + 1) * (r.val + 1) * (s.val + 1) by positivity)
  have hn := Real.sqrt_nonneg ((p.val + 1 : ℝ) * (q.val + 1) * (r.val + 1) * (s.val + 1))
  change |mixedRowGram e p q r s| ≤ _
  nlinarith [sq_abs (mixedRowGram e p q r s), abs_nonneg (mixedRowGram e p q r s)]

/-- The actual complex correction coefficients satisfy the uniform bound (9). -/
theorem mixedCorrectionEntry_bound {m n : ℕ} (a b : Fin n → PureIndex m → ℝ)
    (c : Fin n → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (p q r s : Fin m) : ‖(mixedCorrectionEntry c p q r s : ℂ)‖ ≤
      4 * Real.sqrt ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, mixedCorrectionEntry]
  have hm := averagedMixedRows_abs_le a b c h p q r s
  have hb := baselineMixedEntry_abs_le p q r s
  have ht := abs_sub_le (mixedRowGram (averagedMixedRows c) p q r s) 0 (baselineMixedEntry p q r s)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  linarith

end
end ToeplitzSOS.Negative
