import ToeplitzSOS.Negative.GramEvaluation

/-!
# Algebraic reduction of the initial pure-kernel bounds

Partial conjugation gives the global majorant in terms of the finite D
kernel. The repeated-node identity and the two explicit tail fields give
the conjugate-node error bound. The remaining scalar phase/radius estimates concern only the
rational reference and finite geometric series.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate Finset

/-- Every plus diagonal is a sum of squared absolute values. -/
theorem CornerGram.plus_diagonal_nonneg {m : ℕ} (g : CornerGram m) (x y : ℂ) :
    0 ≤ (hermitianDiagonal (plusBlock (baselineD m) (baselineK m) g.E g.T) x y).re := by
  rw [g.plus_eq, pureGram_diagonal_re]
  exact sum_nonneg fun _ _ => sq_nonneg _

/-- Every minus diagonal is a sum of squared absolute values. -/
theorem CornerGram.minus_diagonal_nonneg {m : ℕ} (g : CornerGram m) (x y : ℂ) :
    0 ≤ (hermitianDiagonal (minusBlock (baselineD m) (baselineK m) g.E g.T) x y).re := by
  rw [g.minus_eq, pureGram_diagonal_re]
  exact sum_nonneg fun _ _ => sq_nonneg _

/-- The arbitrary plus repair is bounded by the two fixed diagonal kernels,
with no restriction on coefficients or rank. -/
theorem CornerGram.plus_le_diagonals {m : ℕ} (g : CornerGram m) (x y : ℂ) :
    (hermitianDiagonal (plusBlock (baselineD m) (baselineK m) g.E g.T) x y).re ≤
      2 * (hermitianDiagonal (baselineD m) x y).re +
      2 * (hermitianDiagonal (baselineD m) x (conj y)).re := by
  have he := congrArg Complex.re (partial_conjugation (baselineD m) (baselineK m)
    g.E g.T g.swap_E x y)
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero] at he
  have h1 := g.minus_diagonal_nonneg x y
  have h2 := g.plus_diagonal_nonneg x (conj y)
  have h3 := g.minus_diagonal_nonneg x (conj y)
  linarith

/-- Exact repeated-node identity in terms of the actual mixed correction. -/
theorem CornerGram.repeated_diagonal {m : ℕ} (g : CornerGram m) (x : ℂ) :
    hermitianDiagonal (plusBlock (baselineD m) (baselineK m) g.E g.T) x (conj x) =
      baselineQ m x (conj x) (conj x) x + mixedKernel g.correction x x (conj x) (conj x) := by
  have h := repeated_node (baselineD m) (baselineK m) (baselineB m)
    g.E g.T g.realign_E g.swap_T x (conj x)
  rw [g.correction_eq] at h
  simpa only [hermitianDiagonal, starRingEnd_self_apply, baselineQ] using h

/-- The full conjugate-node error, obtained only from the two tail
fields and the exact repeated-node identity. -/
theorem CornerGram.repeated_tail_bound {m : ℕ} (g : CornerGram m) (hA : AnalyticInputs)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ℂ)
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) :
    ‖hermitianDiagonal (plusBlock (baselineD m) (baselineK m) g.E g.T) x (conj x) -
        referenceQ x (conj x) (conj x) x‖ ≤
      2^32 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) := by
  have hc : ‖conj x‖ ≤ Real.exp (-ε / 2) := by simpa using hx
  have hq := (hA.baselineTail m ε hε hε1 x (conj x) (conj x) x hx hc hc hx).1
  have ht := hA.mixedTail m ε hε hε1 g.correction g.correction_bound g.low_means x hx
  have he : Real.exp (-ε * m / 2) ≤ Real.exp (-ε * m / 4) := by
    apply Real.exp_le_exp.mpr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have ht' : 2^26 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 2) ≤
      2^26 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  rw [g.repeated_diagonal]
  calc
    _ = ‖(baselineQ m x (conj x) (conj x) x - referenceQ x (conj x) (conj x) x) +
        mixedKernel g.correction x x (conj x) (conj x)‖ := by congr 1; ring
    _ ≤ ‖baselineQ m x (conj x) (conj x) x - referenceQ x (conj x) (conj x) x‖ +
        ‖mixedKernel g.correction x x (conj x) (conj x)‖ := norm_add_le _ _
    _ ≤ 2^30 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) +
        2^26 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) := add_le_add hq (ht.trans ht')
    _ ≤ _ := by
      have hp : 0 ≤ ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) := by positivity
      nlinarith

end
end ToeplitzSOS.Negative
