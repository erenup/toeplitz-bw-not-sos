import ToeplitzSOS.Certificates.Basic

/-! Exact rational certificate for the original polynomial.
The generator is untrusted; Lean checks the original polynomial identity below. -/

namespace ToeplitzSOS

open Certificates

noncomputable section

/-- A kernel-checked exact certificate for the Toeplitz BW polynomial at n = 3. -/
theorem toeplitzBW_isSumSq_n3 : IsSumSqHomQuad (toeplitzBW 3) := by
  let d : Fin 8 → NNReal := ![
    (4 : NNReal),
    (3 : NNReal),
    (6 : NNReal),
    (2 : NNReal),
    (12 : NNReal),
    (6 : NNReal),
    (12 : NNReal),
    (6 : NNReal)]
  let terms : Fin 8 →
      List (ℝ × Fin 5 × Fin 5) := ![
    [((1 : ℝ), (0 : Fin 5), (1 : Fin 5)), (((1 : ℝ) / 2), (3 : Fin 5), (4 : Fin 5))],
    [((1 : ℝ), (3 : Fin 5), (4 : Fin 5))],
    [((1 : ℝ), (0 : Fin 5), (2 : Fin 5))],
    [((1 : ℝ), (0 : Fin 5), (3 : Fin 5)), ((-1 : ℝ), (1 : Fin 5), (4 : Fin 5))],
    [((1 : ℝ), (1 : Fin 5), (2 : Fin 5))],
    [((1 : ℝ), (1 : Fin 5), (3 : Fin 5))],
    [((1 : ℝ), (2 : Fin 5), (3 : Fin 5))],
    [((1 : ℝ), (2 : Fin 5), (4 : Fin 5))]]
  let l : Fin 8 → MvPolynomial (V 3) ℝ := fun i ↦ wedgeForm (terms i)
  have hd : ∀ i, 0 ≤ (d i : ℝ) := fun i ↦ (d i).property
  have hl : ∀ i, (l i).IsHomogeneous 2 := by
    intro i
    exact wedgeForm_isHomogeneous _
  let q : Fin 8 → MvPolynomial (V 3) ℝ :=
    fun i ↦ MvPolynomial.C (Real.sqrt (d i : ℝ)) * l i
  refine ⟨8, q, fun i ↦ (hl i).C_mul (Real.sqrt (d i : ℝ)), ?_⟩
  have hmain : toeplitzBW 3 =
      ∑ i, MvPolynomial.C (d i : ℝ) * (l i) ^ 2 := by
    simp [Fin.sum_univ_succ, d, terms, l, wedgeForm, toeplitzBW, frob, inner, Matrix.mul_apply,
      X, Y, diagIndex, z, x, y]
    polynomial
  rw [hmain]
  apply Finset.sum_congr rfl
  intro i _
  simp only [q, mul_pow]
  rw [← map_pow, Real.sq_sqrt (hd i)]

end

end ToeplitzSOS
