import ToeplitzSOS.Certificates.Basic

/-! Exact rational certificate for the original polynomial.
The generator is untrusted; Lean checks the original polynomial identity below. -/

namespace ToeplitzSOS

open Certificates

noncomputable section

/-- A kernel-checked exact certificate for the Toeplitz BW polynomial at n = 6. -/
theorem toeplitzBW_isSumSq_n6 : IsSumSqHomQuad (toeplitzBW 6) := by
  let d : Fin 50 → NNReal := ![
    (4 : NNReal),
    (39 : NNReal),
    ((896 : NNReal) / 39),
    ((153 : NNReal) / 14),
    ((48 : NNReal) / 17),
    ((113 : NNReal) / 16),
    ((1764 : NNReal) / 113),
    ((100 : NNReal) / 3),
    (6 : NNReal),
    ((88 : NNReal) / 3),
    ((337 : NNReal) / 22),
    ((1782 : NNReal) / 337),
    ((1372 : NNReal) / 99),
    ((9792 : NNReal) / 343),
    (8 : NNReal),
    ((39 : NNReal) / 2),
    ((292 : NNReal) / 39),
    ((1404 : NNReal) / 73),
    (10 : NNReal),
    ((48 : NNReal) / 5),
    (12 : NNReal),
    (8 : NNReal),
    ((23 : NNReal) / 2),
    ((224 : NNReal) / 23),
    ((40 : NNReal) / 7),
    (6 : NNReal),
    ((22 : NNReal) / 3),
    ((48 : NNReal) / 11),
    (4 : NNReal),
    (3 : NNReal),
    (2 : NNReal),
    (24 : NNReal),
    (18 : NNReal),
    ((178 : NNReal) / 9),
    ((1680 : NNReal) / 89),
    ((120 : NNReal) / 7),
    (36 : NNReal),
    (28 : NNReal),
    ((195 : NNReal) / 7),
    ((360 : NNReal) / 13),
    (48 : NNReal),
    (38 : NNReal),
    ((720 : NNReal) / 19),
    (60 : NNReal),
    (48 : NNReal),
    (60 : NNReal),
    (48 : NNReal),
    (36 : NNReal),
    (24 : NNReal),
    (12 : NNReal)]
  let terms : Fin 50 →
      List (ℝ × Fin 11 × Fin 11) := ![
    [((1 : ℝ), (0 : Fin 11), (1 : Fin 11)), (((1 : ℝ) / 2), (6 : Fin 11), (7 : Fin 11)), (((1 : ℝ) / 2), (7 : Fin 11), (8 : Fin 11)), (((1 : ℝ) / 2), (8 : Fin 11), (9 : Fin 11)), (((1 : ℝ) / 2), (9 : Fin 11), (10 : Fin 11))],
    [(((2 : ℝ) / 39), (1 : Fin 11), (2 : Fin 11)), (((2 : ℝ) / 39), (2 : Fin 11), (3 : Fin 11)), (((2 : ℝ) / 39), (3 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (6 : Fin 11), (7 : Fin 11)), (((-1 : ℝ) / 39), (7 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 39), (8 : Fin 11), (9 : Fin 11)), (((-1 : ℝ) / 39), (9 : Fin 11), (10 : Fin 11))],
    [(((79 : ℝ) / 448), (1 : Fin 11), (2 : Fin 11)), (((79 : ℝ) / 448), (2 : Fin 11), (3 : Fin 11)), (((5 : ℝ) / 56), (3 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (7 : Fin 11), (8 : Fin 11)), (((-5 : ℝ) / 112), (8 : Fin 11), (9 : Fin 11)), (((-5 : ℝ) / 112), (9 : Fin 11), (10 : Fin 11))],
    [(((79 : ℝ) / 204), (1 : Fin 11), (2 : Fin 11)), (((79 : ℝ) / 204), (2 : Fin 11), (3 : Fin 11)), (((10 : ℝ) / 51), (3 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (8 : Fin 11), (9 : Fin 11)), (((-5 : ℝ) / 51), (9 : Fin 11), (10 : Fin 11))],
    [(((15 : ℝ) / 16), (1 : Fin 11), (2 : Fin 11)), (((15 : ℝ) / 16), (2 : Fin 11), (3 : Fin 11)), (((5 : ℝ) / 6), (3 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (9 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (2 : Fin 11)), (((-79 : ℝ) / 113), (2 : Fin 11), (3 : Fin 11)), (((-56 : ℝ) / 113), (3 : Fin 11), (4 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (3 : Fin 11)), (((-8 : ℝ) / 21), (3 : Fin 11), (4 : Fin 11))],
    [((1 : ℝ), (3 : Fin 11), (4 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (2 : Fin 11)), (((1 : ℝ) / 3), (6 : Fin 11), (8 : Fin 11)), (((1 : ℝ) / 3), (7 : Fin 11), (9 : Fin 11)), (((1 : ℝ) / 3), (8 : Fin 11), (10 : Fin 11))],
    [(((3 : ℝ) / 44), (1 : Fin 11), (3 : Fin 11)), (((3 : ℝ) / 44), (2 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (6 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 44), (7 : Fin 11), (9 : Fin 11)), (((-1 : ℝ) / 44), (8 : Fin 11), (10 : Fin 11))],
    [(((89 : ℝ) / 337), (1 : Fin 11), (3 : Fin 11)), (((45 : ℝ) / 337), (2 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (7 : Fin 11), (9 : Fin 11)), (((-15 : ℝ) / 337), (8 : Fin 11), (10 : Fin 11))],
    [(((125 : ℝ) / 297), (1 : Fin 11), (3 : Fin 11)), (((40 : ℝ) / 99), (2 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (8 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (3 : Fin 11)), (((-39 : ℝ) / 343), (2 : Fin 11), (4 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (4 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (3 : Fin 11)), (((1 : ℝ) / 4), (6 : Fin 11), (9 : Fin 11)), (((1 : ℝ) / 4), (7 : Fin 11), (10 : Fin 11))],
    [(((4 : ℝ) / 39), (1 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (6 : Fin 11), (9 : Fin 11)), (((-1 : ℝ) / 39), (7 : Fin 11), (10 : Fin 11))],
    [(((20 : ℝ) / 73), (1 : Fin 11), (4 : Fin 11)), ((1 : ℝ), (7 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (4 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (4 : Fin 11)), (((1 : ℝ) / 5), (6 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (6 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (5 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (6 : Fin 11)), (((-1 : ℝ) / 4), (1 : Fin 11), (7 : Fin 11)), (((-1 : ℝ) / 4), (2 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 4), (3 : Fin 11), (9 : Fin 11)), (((-1 : ℝ) / 4), (4 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (7 : Fin 11)), (((-9 : ℝ) / 23), (2 : Fin 11), (8 : Fin 11)), (((-9 : ℝ) / 23), (3 : Fin 11), (9 : Fin 11)), (((-5 : ℝ) / 23), (4 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (8 : Fin 11)), (((-9 : ℝ) / 14), (3 : Fin 11), (9 : Fin 11)), (((-5 : ℝ) / 14), (4 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (3 : Fin 11), (9 : Fin 11)), ((-1 : ℝ), (4 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (7 : Fin 11)), (((-1 : ℝ) / 3), (1 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 3), (2 : Fin 11), (9 : Fin 11)), (((-1 : ℝ) / 3), (3 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (8 : Fin 11)), (((-7 : ℝ) / 11), (2 : Fin 11), (9 : Fin 11)), (((-4 : ℝ) / 11), (3 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (9 : Fin 11)), ((-1 : ℝ), (3 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 2), (1 : Fin 11), (9 : Fin 11)), (((-1 : ℝ) / 2), (2 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (9 : Fin 11)), ((-1 : ℝ), (2 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (0 : Fin 11), (9 : Fin 11)), ((-1 : ℝ), (1 : Fin 11), (10 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (5 : Fin 11))],
    [((1 : ℝ), (1 : Fin 11), (6 : Fin 11)), (((-1 : ℝ) / 9), (2 : Fin 11), (7 : Fin 11)), (((-1 : ℝ) / 9), (3 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 9), (4 : Fin 11), (9 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (7 : Fin 11)), (((-19 : ℝ) / 89), (3 : Fin 11), (8 : Fin 11)), (((-10 : ℝ) / 89), (4 : Fin 11), (9 : Fin 11))],
    [((1 : ℝ), (3 : Fin 11), (8 : Fin 11)), (((-1 : ℝ) / 7), (4 : Fin 11), (9 : Fin 11))],
    [((1 : ℝ), (4 : Fin 11), (9 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (5 : Fin 11))],
    [((1 : ℝ), (2 : Fin 11), (6 : Fin 11)), (((-1 : ℝ) / 14), (3 : Fin 11), (7 : Fin 11)), (((-1 : ℝ) / 14), (4 : Fin 11), (8 : Fin 11))],
    [((1 : ℝ), (3 : Fin 11), (7 : Fin 11)), (((-1 : ℝ) / 13), (4 : Fin 11), (8 : Fin 11))],
    [((1 : ℝ), (4 : Fin 11), (8 : Fin 11))],
    [((1 : ℝ), (3 : Fin 11), (5 : Fin 11))],
    [((1 : ℝ), (3 : Fin 11), (6 : Fin 11)), (((-1 : ℝ) / 19), (4 : Fin 11), (7 : Fin 11))],
    [((1 : ℝ), (4 : Fin 11), (7 : Fin 11))],
    [((1 : ℝ), (4 : Fin 11), (5 : Fin 11))],
    [((1 : ℝ), (4 : Fin 11), (6 : Fin 11))],
    [((1 : ℝ), (5 : Fin 11), (6 : Fin 11))],
    [((1 : ℝ), (5 : Fin 11), (7 : Fin 11))],
    [((1 : ℝ), (5 : Fin 11), (8 : Fin 11))],
    [((1 : ℝ), (5 : Fin 11), (9 : Fin 11))],
    [((1 : ℝ), (5 : Fin 11), (10 : Fin 11))]]
  let l : Fin 50 → MvPolynomial (V 6) ℝ := fun i ↦ wedgeForm (terms i)
  have hd : ∀ i, 0 ≤ (d i : ℝ) := fun i ↦ (d i).property
  have hl : ∀ i, (l i).IsHomogeneous 2 := by
    intro i
    exact wedgeForm_isHomogeneous _
  let q : Fin 50 → MvPolynomial (V 6) ℝ :=
    fun i ↦ MvPolynomial.C (Real.sqrt (d i : ℝ)) * l i
  refine ⟨50, q, fun i ↦ (hl i).C_mul (Real.sqrt (d i : ℝ)), ?_⟩
  have hmain : toeplitzBW 6 =
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
