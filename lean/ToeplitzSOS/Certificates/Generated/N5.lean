import ToeplitzSOS.Certificates.Basic

/-! Exact rational certificate for the original polynomial.
The generator is untrusted; Lean checks the original polynomial identity below. -/

namespace ToeplitzSOS

open Certificates

noncomputable section

/-- A kernel-checked exact certificate for the Toeplitz BW polynomial at n = 5. -/
theorem toeplitzBW_isSumSq_n5 : IsSumSqHomQuad (toeplitzBW 5) := by
  let d : Fin 32 → NNReal := ![
    (4 : NNReal),
    (23 : NNReal),
    ((252 : NNReal) / 23),
    ((20 : NNReal) / 7),
    ((367 : NNReal) / 45),
    ((7540 : NNReal) / 367),
    (6 : NNReal),
    ((46 : NNReal) / 3),
    ((122 : NNReal) / 23),
    ((910 : NNReal) / 61),
    (8 : NNReal),
    ((15 : NNReal) / 2),
    (10 : NNReal),
    (6 : NNReal),
    ((22 : NNReal) / 3),
    ((48 : NNReal) / 11),
    (4 : NNReal),
    (3 : NNReal),
    (2 : NNReal),
    (20 : NNReal),
    (14 : NNReal),
    ((96 : NNReal) / 7),
    ((40 : NNReal) / 3),
    (30 : NNReal),
    (22 : NNReal),
    ((240 : NNReal) / 11),
    (40 : NNReal),
    (30 : NNReal),
    (40 : NNReal),
    (30 : NNReal),
    (20 : NNReal),
    (10 : NNReal)]
  let terms : Fin 32 →
      List (ℝ × Fin 9 × Fin 9) := ![
    [((1 : ℝ), (0 : Fin 9), (1 : Fin 9)), (((1 : ℝ) / 2), (5 : Fin 9), (6 : Fin 9)), (((1 : ℝ) / 2), (6 : Fin 9), (7 : Fin 9)), (((1 : ℝ) / 2), (7 : Fin 9), (8 : Fin 9))],
    [(((2 : ℝ) / 23), (1 : Fin 9), (2 : Fin 9)), (((2 : ℝ) / 23), (2 : Fin 9), (3 : Fin 9)), ((1 : ℝ), (5 : Fin 9), (6 : Fin 9)), (((-1 : ℝ) / 23), (6 : Fin 9), (7 : Fin 9)), (((-1 : ℝ) / 23), (7 : Fin 9), (8 : Fin 9))],
    [(((47 : ℝ) / 126), (1 : Fin 9), (2 : Fin 9)), (((4 : ℝ) / 21), (2 : Fin 9), (3 : Fin 9)), ((1 : ℝ), (6 : Fin 9), (7 : Fin 9)), (((-2 : ℝ) / 21), (7 : Fin 9), (8 : Fin 9))],
    [(((13 : ℝ) / 15), (1 : Fin 9), (2 : Fin 9)), (((4 : ℝ) / 5), (2 : Fin 9), (3 : Fin 9)), ((1 : ℝ), (7 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (2 : Fin 9)), (((-132 : ℝ) / 367), (2 : Fin 9), (3 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (3 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (2 : Fin 9)), (((1 : ℝ) / 3), (5 : Fin 9), (7 : Fin 9)), (((1 : ℝ) / 3), (6 : Fin 9), (8 : Fin 9))],
    [(((3 : ℝ) / 23), (1 : Fin 9), (3 : Fin 9)), ((1 : ℝ), (5 : Fin 9), (7 : Fin 9)), (((-1 : ℝ) / 23), (6 : Fin 9), (8 : Fin 9))],
    [(((24 : ℝ) / 61), (1 : Fin 9), (3 : Fin 9)), ((1 : ℝ), (6 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (3 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (3 : Fin 9)), (((1 : ℝ) / 4), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (4 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (5 : Fin 9)), (((-1 : ℝ) / 3), (1 : Fin 9), (6 : Fin 9)), (((-1 : ℝ) / 3), (2 : Fin 9), (7 : Fin 9)), (((-1 : ℝ) / 3), (3 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (6 : Fin 9)), (((-7 : ℝ) / 11), (2 : Fin 9), (7 : Fin 9)), (((-4 : ℝ) / 11), (3 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (7 : Fin 9)), ((-1 : ℝ), (3 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (6 : Fin 9)), (((-1 : ℝ) / 2), (1 : Fin 9), (7 : Fin 9)), (((-1 : ℝ) / 2), (2 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (7 : Fin 9)), ((-1 : ℝ), (2 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (7 : Fin 9)), ((-1 : ℝ), (1 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (4 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (5 : Fin 9)), (((-1 : ℝ) / 7), (2 : Fin 9), (6 : Fin 9)), (((-1 : ℝ) / 7), (3 : Fin 9), (7 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (6 : Fin 9)), (((-1 : ℝ) / 6), (3 : Fin 9), (7 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (7 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (4 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (5 : Fin 9)), (((-1 : ℝ) / 11), (3 : Fin 9), (6 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (6 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (4 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (5 : Fin 9))],
    [((1 : ℝ), (4 : Fin 9), (5 : Fin 9))],
    [((1 : ℝ), (4 : Fin 9), (6 : Fin 9))],
    [((1 : ℝ), (4 : Fin 9), (7 : Fin 9))],
    [((1 : ℝ), (4 : Fin 9), (8 : Fin 9))]]
  let l : Fin 32 → MvPolynomial (V 5) ℝ := fun i ↦ wedgeForm (terms i)
  have hd : ∀ i, 0 ≤ (d i : ℝ) := fun i ↦ (d i).property
  have hl : ∀ i, (l i).IsHomogeneous 2 := by
    intro i
    exact wedgeForm_isHomogeneous _
  let q : Fin 32 → MvPolynomial (V 5) ℝ :=
    fun i ↦ MvPolynomial.C (Real.sqrt (d i : ℝ)) * l i
  refine ⟨32, q, fun i ↦ (hl i).C_mul (Real.sqrt (d i : ℝ)), ?_⟩
  have hmain : toeplitzBW 5 =
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
