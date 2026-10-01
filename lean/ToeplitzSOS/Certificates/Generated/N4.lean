import ToeplitzSOS.Certificates.Basic

/-! Exact rational certificate for the original polynomial.
The generator is untrusted; Lean checks the original polynomial identity below. -/

namespace ToeplitzSOS

open Certificates

noncomputable section

/-- A kernel-checked exact certificate for the Toeplitz BW polynomial at n = 4. -/
theorem toeplitzBW_isSumSq_n4 : IsSumSqHomQuad (toeplitzBW 4) := by
  let d : Fin 18 → NNReal := ![
    (4 : NNReal),
    (11 : NNReal),
    ((32 : NNReal) / 11),
    (10 : NNReal),
    (6 : NNReal),
    ((16 : NNReal) / 3),
    (8 : NNReal),
    (4 : NNReal),
    (3 : NNReal),
    (2 : NNReal),
    (16 : NNReal),
    (10 : NNReal),
    ((48 : NNReal) / 5),
    (24 : NNReal),
    (16 : NNReal),
    (24 : NNReal),
    (16 : NNReal),
    (8 : NNReal)]
  let terms : Fin 18 →
      List (ℝ × Fin 7 × Fin 7) := ![
    [((1 : ℝ), (0 : Fin 7), (1 : Fin 7)), (((1 : ℝ) / 2), (4 : Fin 7), (5 : Fin 7)), (((1 : ℝ) / 2), (5 : Fin 7), (6 : Fin 7))],
    [(((2 : ℝ) / 11), (1 : Fin 7), (2 : Fin 7)), ((1 : ℝ), (4 : Fin 7), (5 : Fin 7)), (((-1 : ℝ) / 11), (5 : Fin 7), (6 : Fin 7))],
    [(((3 : ℝ) / 4), (1 : Fin 7), (2 : Fin 7)), ((1 : ℝ), (5 : Fin 7), (6 : Fin 7))],
    [((1 : ℝ), (1 : Fin 7), (2 : Fin 7))],
    [((1 : ℝ), (0 : Fin 7), (2 : Fin 7)), (((1 : ℝ) / 3), (4 : Fin 7), (6 : Fin 7))],
    [((1 : ℝ), (4 : Fin 7), (6 : Fin 7))],
    [((1 : ℝ), (0 : Fin 7), (3 : Fin 7))],
    [((1 : ℝ), (0 : Fin 7), (4 : Fin 7)), (((-1 : ℝ) / 2), (1 : Fin 7), (5 : Fin 7)), (((-1 : ℝ) / 2), (2 : Fin 7), (6 : Fin 7))],
    [((1 : ℝ), (1 : Fin 7), (5 : Fin 7)), ((-1 : ℝ), (2 : Fin 7), (6 : Fin 7))],
    [((1 : ℝ), (0 : Fin 7), (5 : Fin 7)), ((-1 : ℝ), (1 : Fin 7), (6 : Fin 7))],
    [((1 : ℝ), (1 : Fin 7), (3 : Fin 7))],
    [((1 : ℝ), (1 : Fin 7), (4 : Fin 7)), (((-1 : ℝ) / 5), (2 : Fin 7), (5 : Fin 7))],
    [((1 : ℝ), (2 : Fin 7), (5 : Fin 7))],
    [((1 : ℝ), (2 : Fin 7), (3 : Fin 7))],
    [((1 : ℝ), (2 : Fin 7), (4 : Fin 7))],
    [((1 : ℝ), (3 : Fin 7), (4 : Fin 7))],
    [((1 : ℝ), (3 : Fin 7), (5 : Fin 7))],
    [((1 : ℝ), (3 : Fin 7), (6 : Fin 7))]]
  let l : Fin 18 → MvPolynomial (V 4) ℝ := fun i ↦ wedgeForm (terms i)
  have hd : ∀ i, 0 ≤ (d i : ℝ) := fun i ↦ (d i).property
  have hl : ∀ i, (l i).IsHomogeneous 2 := by
    intro i
    exact wedgeForm_isHomogeneous _
  let q : Fin 18 → MvPolynomial (V 4) ℝ :=
    fun i ↦ MvPolynomial.C (Real.sqrt (d i : ℝ)) * l i
  refine ⟨18, q, fun i ↦ (hl i).C_mul (Real.sqrt (d i : ℝ)), ?_⟩
  have hmain : toeplitzBW 4 =
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
