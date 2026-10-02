import ToeplitzSOS.Negative.GlobalBound

/-! # Conjugate closed form and the real-slice continuation bound -/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate

/-- The first conjugate denominator is the squared radial defect. -/
theorem factorA_conjugate (x : ℂ) :
    factorA x (conj x) (conj x) x = (((1 - ‖x‖^2)^2 : ℝ) : ℂ) := by
  simp [factorA, mul_comm (conj x) x, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    pow_two, -Complex.ofReal_pow]

/-- The second denominator includes the exact squared imaginary phase. -/
theorem factorB_conjugate (x : ℂ) :
    factorB x (conj x) (conj x) x = (((1 - ‖x‖^2)^2 + 4*x.im^2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [factorB, Complex.normSq_apply, pow_two] <;> ring

/-- The rational closed form, expressed without choosing a polar argument. -/
theorem referenceQ_conjugate (x : ℂ) (hx : ‖x‖ < 1) :
    referenceQ x (conj x) (conj x) x =
      ((8*x.im^2 / ((1-‖x‖^2)^2 * ((1-‖x‖^2)^2+4*x.im^2)^2) : ℝ) : ℂ) := by
  have hr : 0 < 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hA : factorA x (conj x) (conj x) x ≠ 0 := by
    rw [factorA_conjugate]
    exact_mod_cast ne_of_gt (sq_pos_of_pos hr)
  have hB : factorB x (conj x) (conj x) x ≠ 0 := by
    rw [factorB_conjugate]
    exact_mod_cast ne_of_gt (show 0 < (1-‖x‖^2)^2+4*x.im^2 by positivity)
  rw [referenceQ_repeated x (conj x) hA hB, factorA_conjugate, factorB_conjugate]
  push_cast
  ring

/-- Squared modulus of the first speed node on the real slice. -/
theorem analyticNodeX_norm_sq (ε u v : ℝ) :
    ‖analyticNodeX ε (u : ℂ) (v : ℂ)‖^2 = Real.exp (-(2*ε*u)) := by
  change ‖Analytic.speedNode ε (u : ℂ) (v : ℂ)‖^2 = _
  rw [Analytic.speedNode_norm]
  simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Squared imaginary component supplies rho times the squared phase cosine. -/
theorem analyticNodeX_im_sq (ε u v : ℝ) :
    (analyticNodeX ε (u : ℂ) (v : ℂ)).im^2 =
      Real.exp (-(2*ε*u)) * Real.cos (ε*v)^2 := by
  have he : (analyticNodeX ε (u : ℂ) (v : ℂ)).im =
      Real.exp (-ε*u) * Real.cos (ε*v) := by
    simp [analyticNodeX, Complex.exp_re, Complex.exp_im, Real.cos_neg]
  rw [he, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- The reference conjugate value is bounded throughout the full real rectangle. -/
theorem referenceQ_slice_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ (2 : ℝ)⁻¹^16)
    {u v : ℝ} (hu : 1/2 ≤ u) (hu' : u ≤ 2049/2) (hv : |v| ≤ 512) :
    (referenceQ (analyticNodeX ε u v) (conj (analyticNodeX ε u v))
      (conj (analyticNodeX ε u v)) (analyticNodeX ε u v)).re ≤ 16 * ε⁻¹^2 := by
  obtain ⟨ha,_,hr⟩ := Analytic.conjugate_radius_bounds hε hε1 hu hu'
  have hs := Analytic.conjugate_phase_bound hε hε1 hv
  have hx : ‖analyticNodeX ε u v‖ < 1 := by
    change ‖Analytic.speedNode ε u v‖ < 1
    rw [Analytic.speedNode_norm]
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  rw [referenceQ_conjugate _ hx, Complex.ofReal_re, analyticNodeX_norm_sq, analyticNodeX_im_sq]
  simpa [div_eq_mul_inv, inv_pow, mul_assoc] using Analytic.conjugate_reference_bound hε ha hs hr

/-- The actual plus factor satisfies the real-slice bound, including both finite tails. -/
theorem CornerGram.plusVector_slice (g : CornerGram cornerDepth) (hA : AnalyticInputs)
    (u v : ℝ) (hu : 1/2 ≤ u) (hu' : u ≤ 2049/2) (hv : |v| ≤ 512) :
    ‖g.plusVector epsilon u v‖^2 ≤ 2^20 * epsilon⁻¹^2 := by
  have hy : analyticNodeY epsilon u v = conj (analyticNodeX epsilon u v) :=
    Analytic.speedPartner_eq_conj epsilon u v
  have hx : ‖analyticNodeX epsilon u v‖ ≤ Real.exp (-epsilon/2) := by
    change ‖Analytic.speedNode epsilon u v‖ ≤ _
    rw [Analytic.speedNode_norm]
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [epsilon_pos]
  have he := g.repeated_tail_bound hA epsilon epsilon_pos
    (epsilon_le_small.trans (by norm_num)) _ hx
  have ht := Analytic.tail_budget epsilon_pos epsilon_le_small cornerDepth_cast
  have hr := referenceQ_slice_bound epsilon_pos epsilon_le_small hu hu' hv
  have hre := Complex.re_le_norm (hermitianDiagonal
    (plusBlock (baselineD cornerDepth) (baselineK cornerDepth) g.E g.T)
    (analyticNodeX epsilon u v) (conj (analyticNodeX epsilon u v)) -
    referenceQ (analyticNodeX epsilon u v) (conj (analyticNodeX epsilon u v))
      (conj (analyticNodeX epsilon u v)) (analyticNodeX epsilon u v))
  rw [Complex.sub_re] at hre
  rw [← hy, g.plusVector_norm, hy] at hre
  have hi : 0 ≤ epsilon⁻¹^2 := sq_nonneg _
  norm_num only [show (2:ℝ)^20 = 1048576 by norm_num]
  linarith

end
end ToeplitzSOS.Negative
