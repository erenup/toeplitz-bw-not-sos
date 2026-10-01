import ToeplitzSOS.Defs
import ToeplitzSOS.ThmA.Defs

/-!
# Shared definitions for generated fixed-order certificates

The generated files express their quadratic forms as finite rational linear
combinations of the basic wedges `z`.  This file supplies the one reusable
homogeneity proof; certificate identities themselves are checked after fully
unfolding the original matrix definition.
-/

namespace ToeplitzSOS.Certificates

noncomputable section

/-- A list representation of a linear form in the wedges. -/
def wedgeForm {n : ℕ}
    (terms : List (ℝ × Fin (2 * n - 1) × Fin (2 * n - 1))) :
    MvPolynomial (V n) ℝ :=
  match terms with
  | [] => 0
  | (c, a, b) :: rest => MvPolynomial.C c * z a b + wedgeForm rest

/-- Every basic wedge is a homogeneous quadratic polynomial. -/
theorem z_isHomogeneous {n : ℕ} (a b : Fin (2 * n - 1)) :
    (z (n := n) a b).IsHomogeneous 2 := by
  unfold z x y
  simpa using
    ((MvPolynomial.isHomogeneous_X ℝ (CoordFamily.x, a)).mul
      (MvPolynomial.isHomogeneous_X ℝ (CoordFamily.y, b))).sub
    ((MvPolynomial.isHomogeneous_X ℝ (CoordFamily.x, b)).mul
      (MvPolynomial.isHomogeneous_X ℝ (CoordFamily.y, a)))

/-- A finite real linear combination of wedges is still homogeneous of degree two. -/
theorem wedgeForm_isHomogeneous {n : ℕ}
    (terms : List (ℝ × Fin (2 * n - 1) × Fin (2 * n - 1))) :
    (wedgeForm terms).IsHomogeneous 2 := by
  induction terms with
  | nil =>
      exact MvPolynomial.isHomogeneous_zero (σ := V n) (R := ℝ) (n := 2)
  | cons term rest ih =>
      obtain ⟨c, a, b⟩ := term
      exact ((z_isHomogeneous a b).C_mul c).add ih

/-- A wedge in the positive-side variables of the residual form. -/
def hWedge {m : ℕ} (a b : Fin m) : MvPolynomial (ThmA.HV m) ℝ :=
  MvPolynomial.X (CoordFamily.x, a) * MvPolynomial.X (CoordFamily.y, b) -
    MvPolynomial.X (CoordFamily.x, b) * MvPolynomial.X (CoordFamily.y, a)

/-- A list representation of a linear form in positive-side wedges. -/
def hWedgeForm {m : ℕ} (terms : List (ℝ × Fin m × Fin m)) :
    MvPolynomial (ThmA.HV m) ℝ :=
  match terms with
  | [] => 0
  | (c, a, b) :: rest => MvPolynomial.C c * hWedge a b + hWedgeForm rest

/-- Every positive-side wedge is a homogeneous quadratic polynomial. -/
theorem hWedge_isHomogeneous {m : ℕ} (a b : Fin m) :
    (hWedge a b).IsHomogeneous 2 := by
  unfold hWedge
  simpa using
    ((MvPolynomial.isHomogeneous_X ℝ (CoordFamily.x, a)).mul
      (MvPolynomial.isHomogeneous_X ℝ (CoordFamily.y, b))).sub
    ((MvPolynomial.isHomogeneous_X ℝ (CoordFamily.x, b)).mul
      (MvPolynomial.isHomogeneous_X ℝ (CoordFamily.y, a)))

/-- A finite real linear combination of positive-side wedges is homogeneous of degree two. -/
theorem hWedgeForm_isHomogeneous {m : ℕ}
    (terms : List (ℝ × Fin m × Fin m)) :
    (hWedgeForm terms).IsHomogeneous 2 := by
  induction terms with
  | nil =>
      exact MvPolynomial.isHomogeneous_zero (σ := ThmA.HV m) (R := ℝ) (n := 2)
  | cons term rest ih =>
      obtain ⟨c, a, b⟩ := term
      exact ((hWedge_isHomogeneous a b).C_mul c).add ih

end

end ToeplitzSOS.Certificates

namespace ToeplitzSOS

/-- Combine two kernel-checked quadratic SOS certificates. -/
theorem IsSumSqHomQuad.add {σ : Type*} {p r : MvPolynomial σ ℝ}
    (hp : IsSumSqHomQuad p) (hr : IsSumSqHomQuad r) :
    IsSumSqHomQuad (p + r) := by
  obtain ⟨m, q, hq, hp⟩ := hp
  obtain ⟨n, s, hs, hr⟩ := hr
  refine ⟨m + n, Fin.addCases q s, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using hq i
    | right i => simpa using hs i
  · rw [hp, hr]
    simp [Fin.sum_univ_add]

/-- Positive rational weighted wedge squares give real quadratic squares. -/
theorem Certificates.weightedWedgeSOS {n m : ℕ}
    (d : Fin m → NNReal)
    (terms : Fin m → List (ℝ × Fin (2 * n - 1) × Fin (2 * n - 1)))
    (p : MvPolynomial (V n) ℝ)
    (h : p = ∑ i, MvPolynomial.C (d i : ℝ) *
      (Certificates.wedgeForm (terms i)) ^ 2) :
    IsSumSqHomQuad p := by
  let l : Fin m → MvPolynomial (V n) ℝ := fun i ↦ Certificates.wedgeForm (terms i)
  let q : Fin m → MvPolynomial (V n) ℝ :=
    fun i ↦ MvPolynomial.C (Real.sqrt (d i : ℝ)) * l i
  refine ⟨m, q, ?_, ?_⟩
  · intro i
    exact (Certificates.wedgeForm_isHomogeneous _).C_mul _
  · rw [h]
    apply Finset.sum_congr rfl
    intro i _
    simp only [q, l, mul_pow]
    rw [← map_pow]
    exact congrArg (fun t : ℝ => MvPolynomial.C t *
      (Certificates.wedgeForm (terms i)) ^ 2)
      (Real.sq_sqrt (d i).property).symm

/-- The same square-root bridge for the residual-form decomposition's positive-side variables. -/
theorem Certificates.weightedHWedgeSOS {m r : ℕ}
    (d : Fin r → NNReal)
    (terms : Fin r → List (ℝ × Fin m × Fin m))
    (p : MvPolynomial (ThmA.HV m) ℝ)
    (h : p = ∑ i, MvPolynomial.C (d i : ℝ) *
      (Certificates.hWedgeForm (terms i)) ^ 2) :
    IsSumSqHomQuad p := by
  let l : Fin r → MvPolynomial (ThmA.HV m) ℝ := fun i ↦ Certificates.hWedgeForm (terms i)
  let q : Fin r → MvPolynomial (ThmA.HV m) ℝ :=
    fun i ↦ MvPolynomial.C (Real.sqrt (d i : ℝ)) * l i
  refine ⟨r, q, ?_, ?_⟩
  · intro i
    exact (Certificates.hWedgeForm_isHomogeneous _).C_mul _
  · rw [h]
    apply Finset.sum_congr rfl
    intro i _
    simp only [q, l, mul_pow]
    rw [← map_pow]
    exact congrArg (fun t : ℝ => MvPolynomial.C t *
      (Certificates.hWedgeForm (terms i)) ^ 2)
      (Real.sq_sqrt (d i).property).symm

end ToeplitzSOS
