import ToeplitzSOS.Negative.AnalyticInputs
import ToeplitzSOS.Negative.Analytic.BaselineBounds
import ToeplitzSOS.Negative.Analytic.Continuation
import ToeplitzSOS.Negative.Analytic.MixedTail
import ToeplitzSOS.Negative.Analytic.Nodes
import ToeplitzSOS.Negative.Analytic.TailBudget

/-!
# Quantitative two-rectangle continuation interface

The analytic comparison theorems provide the continuation field of
`AnalyticInputs` with explicit constants.
-/

namespace ToeplitzSOS.Negative.Analytic
open ComplexConjugate

/-- The complete `mixedTail` field, for arbitrary coefficient tensors. -/
theorem mixedTail (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : Fin m → Fin m → Fin m → Fin m → ℂ)
    (hC : ∀ p q r s, ‖C p q r s‖ ≤ 4 * Real.sqrt
      ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ))
    (hmeans : CompleteLowMeans C) (x : ℂ) (hx : ‖x‖ ≤ Real.exp (-ε / 2)) :
    ‖mixedKernel C x x (conj x) (conj x)‖ ≤
      2 ^ 26 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 2) :=
  mixed_tail_bound m hε hε1 C hC hmeans.1 hmeans.2 x hx

/-- The complete `twoRectangles` field, uniformly over all Gram ranks. -/
theorem twoRectangles (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ (2 : ℝ)⁻¹ ^ 16)
    (F : ℂ → ℂ → EuclideanSpace ℂ (Fin d))
    (hFu : ∀ v, Differentiable ℂ (fun u => F u v))
    (hFv : ∀ u, Differentiable ℂ (F u))
    (hglobal : ∀ u v, 1 / 4 ≤ u.re - |v.im| → ‖F u v‖ ^ 2 ≤ 2 ^ 20 * ε⁻¹ ^ 4)
    (hreal : ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ 2049 / 2 → |v| ≤ 512 →
      ‖F (u : ℂ) (v : ℂ)‖ ^ 2 ≤ 2 ^ 20 * ε⁻¹ ^ 2)
    (u v : ℂ) (hregion : SpeedRegion u v) :
    ε ^ 4 * ‖F u v‖ ^ 2 ≤ 2 ^ 20 * ε ^ (1 / 131072 : ℝ) := by
  apply complex_speed_bound hFu hFv hε (hε1.trans (by norm_num))
    (fun u v h => by simpa only [div_eq_mul_inv, inv_pow] using hglobal u v h)
    (fun x hx y hy => by
      simpa only [div_eq_mul_inv, inv_pow] using hreal x y hx.1 hx.2 (abs_le.mpr hy))
    hregion.1 hregion.2.1 hregion.2.2.1 hregion.2.2.2.1 hregion.2.2.2.2

/-- Modular constructor retained for clients that supply the baseline estimate. -/
theorem analyticInputs_of_baselineTail
    (hbase : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ x y z w : ℂ,
        ‖x‖ ≤ Real.exp (-ε / 2) → ‖y‖ ≤ Real.exp (-ε / 2) →
        ‖z‖ ≤ Real.exp (-ε / 2) → ‖w‖ ≤ Real.exp (-ε / 2) →
        ‖baselineQ m x y z w - referenceQ x y z w‖ ≤
          2 ^ 30 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4) ∧
        ‖baselineL m x y z w - referenceL x y z w‖ ≤
          2 ^ 30 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 4)) : AnalyticInputs where
  baselineTail := hbase
  mixedTail := mixedTail
  twoRectangles := twoRectangles

/-- All analytic inputs of the negative proof, with no remaining analytic premise. -/
theorem analyticInputs : AnalyticInputs :=
  analyticInputs_of_baselineTail baselineTail

end ToeplitzSOS.Negative.Analytic
