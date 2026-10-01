import ToeplitzSOS.Negative.Baseline

/-!
# Analytic estimates for the negative proof

`AnalyticInputs` packages the baseline and mixed-tail estimates and the
two-rectangle continuation bound, with all domains and constants explicit.
The fields are proved in `Analytic/Interface`, `Analytic/Tails`, and
`Analytic/MixedTail`; `Analytic/Interface` assembles `Analytic.analyticInputs`.
`Resolution` combines these estimates with the algebraic corner extraction.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate Finset

/-- The target region in the two complex speed coordinates. -/
def SpeedRegion (u v : ℂ) : Prop :=
  1 ≤ u.re ∧ u.re ≤ 2 ∧ |u.im| ≤ 256 ∧ |v.re| ≤ 256 ∧ |v.im| ≤ 1 / 2

/-- Complete low row and column means vanish. Incomplete high means are
unconstrained; the tail estimate is needed precisely for them. -/
def CompleteLowMeans {m : ℕ} (C : Fin m → Fin m → Fin m → Fin m → ℂ) : Prop :=
  (∀ g < m, ∀ r s, ∑ p, ∑ q, (if p.val + q.val = g then C p q r s else 0) = 0) ∧
  (∀ g < m, ∀ p q, ∑ r, ∑ s, (if r.val + s.val = g then C p q r s else 0) = 0)

/-- The three analytic estimates used by the finite proof, with all
parameters, domains and constants explicit and independent of Gram rank. -/
structure AnalyticInputs : Prop where
  /-- Equation (12): the finite baseline truncations have uniformly small tails. -/
  baselineTail : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ x y z w : ℂ,
      ‖x‖ ≤ Real.exp (-ε / 2) → ‖y‖ ≤ Real.exp (-ε / 2) →
      ‖z‖ ≤ Real.exp (-ε / 2) → ‖w‖ ≤ Real.exp (-ε / 2) →
      ‖baselineQ m x y z w - referenceQ x y z w‖ ≤
        2 ^ 30 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) ∧
      ‖baselineL m x y z w - referenceL x y z w‖ ≤
        2 ^ 30 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4)
  /-- The estimate after (12): fixed coefficient bounds and complete low
  means leave only a finite high-total tail on the repeated node. -/
  mixedTail : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ C : Fin m → Fin m → Fin m → Fin m → ℂ,
      (∀ p q r s, ‖C p q r s‖ ≤ 4 * Real.sqrt
        ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ)) →
      CompleteLowMeans C → ∀ x : ℂ, ‖x‖ ≤ Real.exp (-ε / 2) →
      ‖mixedKernel C x x (conj x) (conj x)‖ ≤
        2 ^ 26 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 2)
  /-- Equations (16)-(19): separately entire finite vectors obey the
  quantitative continuation bound from the global and real-slice bounds. -/
  twoRectangles : ∀ (d : ℕ) (ε : ℝ), 0 < ε → ε ≤ (2 : ℝ)⁻¹ ^ 16 →
    ∀ F : ℂ → ℂ → EuclideanSpace ℂ (Fin d),
      (∀ v, Differentiable ℂ (fun u => F u v)) →
      (∀ u, Differentiable ℂ (F u)) →
      (∀ u v, 1 / 4 ≤ u.re - |v.im| →
        ‖F u v‖ ^ 2 ≤ 2 ^ 20 * ε⁻¹ ^ 4) →
      (∀ u v : ℝ, 1 / 2 ≤ u → u ≤ 2049 / 2 → |v| ≤ 512 →
        ‖F (u : ℂ) (v : ℂ)‖ ^ 2 ≤ 2 ^ 20 * ε⁻¹ ^ 2) →
      ∀ u v, SpeedRegion u v →
        ε ^ 4 * ‖F u v‖ ^ 2 ≤ 2 ^ 20 * ε ^ (1 / 131072 : ℝ)

end
end ToeplitzSOS.Negative
