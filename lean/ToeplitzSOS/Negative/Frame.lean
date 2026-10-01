import ToeplitzSOS.General.Moment

/-!
# The complete alternating frame of a quadratic SOS

Vanishing on the two coordinate axes and on the diagonal forces every
homogeneous quadratic summand to be alternating bilinear. The argument is
valid for arbitrary real coefficients and arbitrary finite square count.
It reuses the quadratic polarization proved in `General.Moment`.
-/

namespace ToeplitzSOS.Negative

open MvPolynomial Finset General

noncomputable section

/-- Every SOS of a polynomial vanishing on the axes and diagonal has a
complete representation by squares of alternating bilinear forms. -/
theorem exists_alternating_sos {P : Type*} [Fintype P]
    (p : MvPolynomial (CoordFamily × P) ℝ)
    (hx : ∀ U, eval (pt U 0) p = 0)
    (hy : ∀ V, eval (pt 0 V) p = 0)
    (hd : ∀ U, eval (pt U U) p = 0)
    (hsos : IsSumSqHomQuad p) :
    ∃ s : ℕ, ∃ B : Fin s → (P → ℝ) →ₗ[ℝ] (P → ℝ) →ₗ[ℝ] ℝ,
      (∀ j U V, B j U V = -B j V U) ∧
      ∀ U V, eval (pt U V) p = ∑ j, (B j U V) ^ 2 := by
  classical
  obtain ⟨s, q, hq, hp⟩ := hsos
  choose c hc using fun j => exists_quadForm (hq j)
  have heval : ∀ U V, eval (pt U V) p = ∑ j, (quadF (c j) (pt U V)) ^ 2 := by
    intro U V
    rw [hp]
    simp only [map_sum, map_pow, hc, quadF]
  have hzero : ∀ U V, eval (pt U V) p = 0 → ∀ j, quadF (c j) (pt U V) = 0 := by
    intro U V h j
    rw [heval] at h
    exact pow_eq_zero_iff two_ne_zero |>.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h j (mem_univ _))
  have hxj : ∀ j U, quadF (c j) (pt U 0) = 0 := fun j U => hzero U 0 (hx U) j
  have hyj : ∀ j V, quadF (c j) (pt 0 V) = 0 := fun j V => hzero 0 V (hy V) j
  have hdj : ∀ j U, quadF (c j) (pt U U) = 0 := fun j U => hzero U U (hd U) j
  refine ⟨s, fun j => bil (c j), fun j => bil_alt (c j) (hxj j) (hyj j) (hdj j), ?_⟩
  intro U V
  rw [heval]
  exact sum_congr rfl fun j _ => by rw [quadF_pt_eq_bil (c j) (hxj j) (hyj j)]

/-- The literal Toeplitz quartic vanishes when its second symbol vector is zero. -/
theorem eval_toeplitzBW_zero_right (n : ℕ) (U : Fin (2 * n - 1) → ℝ) :
    eval (pt U 0) (toeplitzBW n) = 0 := by
  simp [toeplitzBW, frob, inner, Matrix.mul_apply, X, Y, x, y, pt]

/-- The literal Toeplitz quartic vanishes when its first symbol vector is zero. -/
theorem eval_toeplitzBW_zero_left (n : ℕ) (U : Fin (2 * n - 1) → ℝ) :
    eval (pt 0 U) (toeplitzBW n) = 0 := by
  simp [toeplitzBW, frob, inner, Matrix.mul_apply, X, Y, x, y, pt]

/-- The literal Toeplitz quartic vanishes on equal symbol vectors. -/
theorem eval_toeplitzBW_self (n : ℕ) (U : Fin (2 * n - 1) → ℝ) :
    eval (pt U U) (toeplitzBW n) = 0 := by
  simp [toeplitzBW, frob, inner, Matrix.mul_apply, X, Y, x, y, pt, pow_two]
  ring

/-- The complete SOS cone of the catalogue polynomial lies in the alternating
frame; no support, rationality, square-count or prescribed-core assumption occurs. -/
theorem toeplitzBW_exists_alternating_sos {n : ℕ}
    (hsos : IsSumSqHomQuad (toeplitzBW n)) :
    ∃ s : ℕ, ∃ B : Fin s → (Fin (2 * n - 1) → ℝ) →ₗ[ℝ]
        (Fin (2 * n - 1) → ℝ) →ₗ[ℝ] ℝ,
      (∀ j U V, B j U V = -B j V U) ∧
      ∀ U V, eval (pt U V) (toeplitzBW n) = ∑ j, (B j U V) ^ 2 :=
  exists_alternating_sos _ (eval_toeplitzBW_zero_right n)
    (eval_toeplitzBW_zero_left n) (eval_toeplitzBW_self n) hsos

/-- A bilinear form on a finite coordinate space is its coefficient expansion. -/
theorem bilinear_eq_sum {P : Type*} [Fintype P] [DecidableEq P]
    (B : (P → ℝ) →ₗ[ℝ] (P → ℝ) →ₗ[ℝ] ℝ) (U V : P → ℝ) :
    B U V = ∑ a, ∑ b, B (Pi.single a 1) (Pi.single b 1) * (U a * V b) := by
  have hU : U = ∑ a, U a • Pi.single a (1 : ℝ) := by ext a; simp [Pi.single_apply]
  have hV : V = ∑ a, V a • Pi.single a (1 : ℝ) := by ext a; simp [Pi.single_apply]
  conv_lhs => rw [hU, hV]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun a _ => Finset.mul_sum _ _ _)]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- Alternating bilinear forms are linear combinations of all ordered wedges.
The factor one half compensates for including both orientations. -/
theorem alternating_eq_wedge_sum {P : Type*} [Fintype P] [DecidableEq P]
    (B : (P → ℝ) →ₗ[ℝ] (P → ℝ) →ₗ[ℝ] ℝ)
    (hB : ∀ U V, B U V = -B V U) (U V : P → ℝ) :
    B U V = (1 / 2 : ℝ) * ∑ a, ∑ b,
      B (Pi.single a 1) (Pi.single b 1) * (U a * V b - U b * V a) := by
  have h : ∑ a, ∑ b, B (Pi.single a 1) (Pi.single b 1) *
      (U a * V b - U b * V a) = B U V - B V U := by
    rw [bilinear_eq_sum B U V, bilinear_eq_sum B V U]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [h, hB V U]
  ring

end
end ToeplitzSOS.Negative
