import ToeplitzSOS.Negative.CornerExchange
import ToeplitzSOS.Negative.Frame

/-!
# Complete alternating coordinates of an arbitrary corner SOS

Every homogeneous quadratic summand is expanded in the two pure sectors and
the complete mixed sector. No restriction on its coefficients or rank is
introduced.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial General

/-- Coefficient of an alternating bilinear form at two coordinate vectors. -/
def cornerCoefficient {m : ℕ}
    (B : (CornerLabel m → ℝ) →ₗ[ℝ] (CornerLabel m → ℝ) →ₗ[ℝ] ℝ)
    (a b : CornerLabel m) : ℝ := B (Pi.single a 1) (Pi.single b 1)

/-- Evaluation of the wedge on two real coordinate vectors. -/
def realCornerWedge {m : ℕ} (U V : CornerLabel m → ℝ) (a b : CornerLabel m) : ℝ :=
  U a * V b - U b * V a

/-- Every alternating bilinear form has exactly the complete three-sector
coordinate expansion used by the corner proof. -/
theorem alternating_corner_expansion {m : ℕ}
    (B : (CornerLabel m → ℝ) →ₗ[ℝ] (CornerLabel m → ℝ) →ₗ[ℝ] ℝ)
    (hB : ∀ U V, B U V = -B V U) (U V : CornerLabel m → ℝ) :
    B U V =
      (∑ p : PureIndex m, cornerCoefficient B (false, p.1.1) (false, p.1.2) *
        realCornerWedge U V (false, p.1.1) (false, p.1.2)) +
      (∑ p : PureIndex m, cornerCoefficient B (true, p.1.1) (true, p.1.2) *
        realCornerWedge U V (true, p.1.1) (true, p.1.2)) +
      ∑ p : Fin m, ∑ q : Fin m, cornerCoefficient B (false, p) (true, q) *
        realCornerWedge U V (false, p) (true, q) := by
  classical
  have hs (a b : CornerLabel m) : cornerCoefficient B a b * realCornerWedge U V a b =
      cornerCoefficient B b a * realCornerWedge U V b a := by
    unfold cornerCoefficient realCornerWedge
    rw [hB (Pi.single a 1) (Pi.single b 1)]
    ring
  have hp (side : Bool) := sum_depthPairs m
    (fun p q => cornerCoefficient B (side, p) (side, q) *
      realCornerWedge U V (side, p) (side, q))
    (fun p q => hs _ _) (fun p => by simp [realCornerWedge])
  have hm : (∑ p : Fin m, ∑ q : Fin m, cornerCoefficient B (true, p) (false, q) *
      realCornerWedge U V (true, p) (false, q)) =
      ∑ p : Fin m, ∑ q : Fin m, cornerCoefficient B (false, p) (true, q) *
        realCornerWedge U V (false, p) (true, q) := by
    rw [sum_comm]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => hs _ _
  rw [alternating_eq_wedge_sum B hB U V]
  change (1 / 2 : ℝ) * (∑ a : CornerLabel m, ∑ b : CornerLabel m,
    cornerCoefficient B a b * realCornerWedge U V a b) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sum_add_distrib]
  rw [hp true, hp false, hm]
  ring

/-- The polynomial with arbitrary coefficients on both pure sectors and on
all mixed pairs. -/
def cornerLinear {m : ℕ} (a b : PureIndex m → ℝ) (c : Fin m → Fin m → ℝ) :
    MvPolynomial (CornerVariable m) ℝ :=
  (∑ p, C (a p) * pureWedge false p) + (∑ p, C (b p) * pureWedge true p) +
    ∑ p, ∑ q, C (c p q) * mixedWedge p q

private theorem eval_cornerWedge {m : ℕ} (U V : CornerLabel m → ℝ) (a b : CornerLabel m) :
    eval (pt U V) (cornerWedge a b) = realCornerWedge U V a b := by
  simp [cornerWedge, realCornerWedge, pt]

private theorem baseline_eval_axes (m : ℕ) :
    (∀ U, eval (pt U 0) (baselinePolynomial m) = 0) ∧
    (∀ V, eval (pt 0 V) (baselinePolynomial m) = 0) ∧
    (∀ U, eval (pt U U) (baselinePolynomial m) = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro U <;>
    simp [baselinePolynomial, pureWedge, mixedWedge, eval_cornerWedge, realCornerWedge, mul_comm]

/-- Every arbitrary homogeneous quadratic SOS of the baseline polynomial has
an unrestricted finite three-sector wedge representation. -/
theorem baseline_exists_wedge_sos {m : ℕ} (h : IsSumSqHomQuad (baselinePolynomial m)) :
    ∃ r : ℕ, ∃ a b : Fin r → PureIndex m → ℝ,
      ∃ c : Fin r → Fin m → Fin m → ℝ,
        baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2 := by
  classical
  obtain ⟨hx, hy, hd⟩ := baseline_eval_axes m
  obtain ⟨r, B, hB, he⟩ := exists_alternating_sos (baselinePolynomial m) hx hy hd h
  refine ⟨r, (fun j p => cornerCoefficient (B j) (false, p.1.1) (false, p.1.2)),
    (fun j p => cornerCoefficient (B j) (true, p.1.1) (true, p.1.2)),
    (fun j p q => cornerCoefficient (B j) (false, p) (true, q)), ?_⟩
  apply MvPolynomial.funext
  intro t
  let U : CornerLabel m → ℝ := fun p => t (.x, p)
  let V : CornerLabel m → ℝ := fun p => t (.y, p)
  have ht : t = pt U V := by
    funext p
    rcases p with ⟨c, p⟩
    cases c <;> rfl
  rw [ht, he]
  simp only [map_sum, map_pow]
  apply sum_congr rfl
  intro j _
  congr 1
  rw [alternating_corner_expansion (B j) (hB j) U V]
  simp [cornerLinear, pureWedge, mixedWedge, eval_cornerWedge]

/-- A catalogue SOS yields the complete wedge representation of the
stabilized baseline at every fitting corner depth. -/
theorem toeplitzBW_exists_corner_wedge_sos {m N : ℕ} (hN : 2 * m ≤ N)
    (h : IsSumSqHomQuad (toeplitzBW N)) :
    ∃ r : ℕ, ∃ a b : Fin r → PureIndex m → ℝ,
      ∃ c : Fin r → Fin m → Fin m → ℝ,
        baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2 := by
  apply baseline_exists_wedge_sos
  rw [← outerCorner_eq_baselinePolynomial hN]
  exact outerCorner_isSumSq_of h

end
end ToeplitzSOS.Negative
