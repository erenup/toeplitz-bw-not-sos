import ToeplitzSOS.Negative.Nodes
import ToeplitzSOS.Negative.Constants

/-!
# Applying the analytic interface to the realigned entries

The norm-factorization and its two norm bounds are explicit algebraic/Gram
premises. The only analytic premise used here is the `AnalyticInputs`
structure. The realigned array is never asserted to be PSD.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate

/-- The first analytic node as a function of the two complex speeds. -/
def analyticNodeX (ε : ℝ) (u v : ℂ) : ℂ :=
  Complex.I * Complex.exp (-(ε : ℂ) * (u + Complex.I * v))

/-- The second analytic node, with its negative phase. -/
def analyticNodeY (ε : ℝ) (u v : ℂ) : ℂ :=
  -Complex.I * Complex.exp (-(ε : ℂ) * (u - Complex.I * v))

/-- The precise scaled realigned entry used by the finite dual. -/
def scaledRealignedEntry (P : FourKernel) (i j : Fin 1024) : ℝ :=
  epsilon^4 * (realign P (witnessNode epsilon i) (conj (witnessNode epsilon i))
    (conj (witnessNode epsilon j)) (witnessNode epsilon j)).re

/-- The two-rectangle input gives every realigned entry its exact absolute
payment bound once the finite Gram factor and its two initial bounds are provided. -/
theorem scaledRealignedEntry_bound (hA : AnalyticInputs) (P : FourKernel)
    (d : ℕ) (F : ℂ → ℂ → EuclideanSpace ℂ (Fin d))
    (hfactor : ∀ u v, (hermitianDiagonal P (analyticNodeX epsilon u v)
      (analyticNodeY epsilon u v)).re = ‖F u v‖^2)
    (hu : ∀ v, Differentiable ℂ (fun u => F u v))
    (hv : ∀ u, Differentiable ℂ (F u))
    (hglobal : ∀ u v, 1 / 4 ≤ u.re - |v.im| →
      ‖F u v‖^2 ≤ 2^20 * epsilon⁻¹ ^ 4)
    (hslice : ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ 2049 / 2 → |v| ≤ 512 →
      ‖F (u : ℂ) (v : ℂ)‖^2 ≤ 2^20 * epsilon⁻¹ ^ 2)
    (i j : Fin 1024) : |scaledRealignedEntry P i j| ≤ realignedBound := by
  have hb := hA.twoRectangles d epsilon epsilon_pos epsilon_le_small F hu hv
    hglobal hslice (pairU i j) (pairV i j) (pair_mem_speedRegion i j)
  have he : scaledRealignedEntry P i j = epsilon^4 * ‖F (pairU i j) (pairV i j)‖^2 := by
    unfold scaledRealignedEntry
    rw [realigned_entry_eq_diagonal]
    have hx : witnessNode epsilon i = analyticNodeX epsilon (pairU i j) (pairV i j) :=
      witnessNode_pair epsilon i j
    have hy : conj (witnessNode epsilon j) = analyticNodeY epsilon (pairU i j) (pairV i j) :=
      conj_witnessNode_pair epsilon i j
    rw [hx, hy, hfactor]
  rw [he, abs_of_nonneg (by positivity)]
  exact hb.trans interpolation_constant

end
end ToeplitzSOS.Negative
