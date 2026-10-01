import ToeplitzSOS.Negative.CornerGram
import ToeplitzSOS.Negative.FiniteObstruction

/-!
# Finite Gram evaluation, positivity, and the entire pure factor

This module consumes the algebraic `CornerGram` record. It proves the
nonnegative evaluated pairing and constructs the finite complex vector
whose norm is the plus-kernel diagonal. References: (16), (25), (28).
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset ComplexConjugate

/-- Real pure-wedge features commute with conjugation. -/
theorem pureFeature_conj {m : ℕ} (pq : PureIndex m) (x y : ℂ) :
    pureFeature pq (conj x) (conj y) = conj (pureFeature pq x y) := by
  simp [pureFeature]

/-- Real pure coefficients commute with conjugation of the input. -/
theorem pureLinear_conj {m : ℕ} (c : PureIndex m → ℝ) (x y : ℂ) :
    pureLinear c (conj x) (conj y) = conj (pureLinear c x y) := by
  simp [pureLinear, pureFeature_conj]

/-- Real mixed coefficients commute with conjugation of the input. -/
theorem mixedLinear_conj {m : ℕ} (c : Fin m → Fin m → ℝ) (x y : ℂ) :
    mixedLinear c (conj x) (conj y) = conj (mixedLinear c x y) := by
  simp [mixedLinear]

/-- The real pure diagonal is the sum of squared absolute feature values. -/
theorem pureGram_diagonal_re {m r : ℕ} (c : Fin r → PureIndex m → ℝ) (x y : ℂ) :
    (hermitianDiagonal (pureGramKernel c) x y).re = ∑ j, ‖pureLinear (c j) x y‖^2 := by
  simp [hermitianDiagonal, pureGramKernel, pureLinear_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

/-- The evaluated real part of a pure Gram is an actual real Gram. -/
theorem pureGram_eval_re {ι : Type*} {m r : ℕ}
    (c : Fin r → PureIndex m → ℝ) (x y : ι → ℂ) :
    (fun i j => (pureGramKernel c (x i) (y i) (conj (x j)) (conj (y j))).re) =
      realGram (fun k i => pureLinear (c k) (x i) (y i)) := by
  funext i j
  simp [pureGramKernel, pureLinear_conj, realGram, Complex.mul_re]

/-- The evaluated real part of a mixed Gram is an actual real Gram. -/
theorem mixedGram_eval_re {ι : Type*} {m r : ℕ}
    (c : Fin r → Fin m → Fin m → ℝ) (x y : ι → ℂ) :
    (fun i j => (mixedGramKernel c (x i) (y i) (conj (x j)) (conj (y j))).re) =
      realGram (fun k i => mixedLinear (c k) (x i) (y i)) := by
  funext i j
  simp [mixedGramKernel, mixedLinear_conj, realGram, Complex.mul_re]

/-- Pairing commutes with multiplication of every entry by a real scalar. -/
theorem pairing_scale {ι : Type*} [Fintype ι] (c : ι → ℝ) (A : ι → ι → ℝ) (t : ℝ) :
    pairing c (fun i j => t * A i j) = t * pairing c A := by
  simp only [pairing, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- Scaled finite pure Gram evaluation remains nonnegative on every real vector. -/
theorem scaled_pureGram_nonneg {m r : ℕ} (c : Fin r → PureIndex m → ℝ)
    (w : Fin 1024 → ℝ) : 0 ≤ pairing w (scaledKernel (pureGramKernel c)) := by
  have he : scaledKernel (pureGramKernel c) = fun i j => epsilon^4 *
      realGram (fun k i => pureLinear (c k) (witnessNode epsilon i)
        (conj (witnessNode epsilon i))) i j := by
    have h := pureGram_eval_re c (witnessNode epsilon) (fun i => conj (witnessNode epsilon i))
    funext i j
    have hh := congrFun (congrFun h i) j
    simpa only [scaledKernel, starRingEnd_self_apply] using congrArg (fun a : ℝ => epsilon^4 * a) hh
  rw [he, pairing_scale]
  exact mul_nonneg (by positivity) (pairing_realGram_nonneg w _)

/-- Scaled finite mixed Gram evaluation remains nonnegative on every real vector. -/
theorem scaled_mixedGram_nonneg {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ)
    (w : Fin 1024 → ℝ) : 0 ≤ pairing w (scaledKernel (mixedGramKernel c)) := by
  have he : scaledKernel (mixedGramKernel c) = fun i j => epsilon^4 *
      realGram (fun k i => mixedLinear (c k) (witnessNode epsilon i)
        (conj (witnessNode epsilon i))) i j := by
    have h := mixedGram_eval_re c (witnessNode epsilon) (fun i => conj (witnessNode epsilon i))
    funext i j
    have hh := congrFun (congrFun h i) j
    simpa only [scaledKernel, starRingEnd_self_apply] using congrArg (fun a : ℝ => epsilon^4 * a) hh
  rw [he, pairing_scale]
  exact mul_nonneg (by positivity) (pairing_realGram_nonneg w _)

/-- Every algebraic corner Gram supplies the nonnegative side of the finite dual. -/
theorem CornerGram.pairing_nonneg {m : ℕ} (g : CornerGram m) (w : Fin 1024 → ℝ) :
    0 ≤ pairing w (scaledKernel (mixedBlock (baselineB m) g.T +
      pureMean (baselineD m) (baselineK m) g.E g.T)) := by
  rw [scaledKernel_add, pairing_add, g.mixed_eq]
  have hp := scaled_pureGram_nonneg g.plusRows w
  have hm := scaled_pureGram_nonneg g.minusRows w
  have hb := scaled_mixedGram_nonneg g.mixedRows w
  have he : pairing w (scaledKernel (pureMean (baselineD m) (baselineK m) g.E g.T)) =
      (pairing w (scaledKernel (pureGramKernel g.plusRows)) +
        pairing w (scaledKernel (pureGramKernel g.minusRows))) / 2 := by
    rw [← g.plus_eq, ← g.minus_eq]
    simp only [pairing, scaledKernel, pureMean, Complex.add_re, Complex.div_ofNat_re]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

/-- The finite plus Gram vector on the analytic speed coordinates. -/
def CornerGram.plusVector {m : ℕ} (g : CornerGram m) (ε : ℝ) (u v : ℂ) :
    EuclideanSpace ℂ (Fin g.plusRank) :=
  WithLp.toLp 2 (fun j => pureLinear (g.plusRows j) (analyticNodeX ε u v) (analyticNodeY ε u v))

/-- The constructed vector is the exact norm factor needed by the rectangle comparison. -/
theorem CornerGram.plusVector_norm {m : ℕ} (g : CornerGram m) (ε : ℝ) (u v : ℂ) :
    (hermitianDiagonal (plusBlock (baselineD m) (baselineK m) g.E g.T)
      (analyticNodeX ε u v) (analyticNodeY ε u v)).re = ‖g.plusVector ε u v‖^2 := by
  rw [g.plus_eq, pureGram_diagonal_re, EuclideanSpace.norm_sq_eq]
  rfl

/-- The finite plus factor is entire in its first speed variable. -/
theorem CornerGram.plusVector_differentiable_left {m : ℕ} (g : CornerGram m) (ε : ℝ) (v : ℂ) :
    Differentiable ℂ (fun u => g.plusVector ε u v) := by
  rw [differentiable_piLp]
  intro j
  change Differentiable ℂ (fun u => pureLinear (g.plusRows j)
    (analyticNodeX ε u v) (analyticNodeY ε u v))
  unfold pureLinear pureFeature analyticNodeX analyticNodeY
  fun_prop

/-- The finite plus factor is entire in its second speed variable. -/
theorem CornerGram.plusVector_differentiable_right {m : ℕ} (g : CornerGram m) (ε : ℝ) (u : ℂ) :
    Differentiable ℂ (g.plusVector ε u) := by
  rw [differentiable_piLp]
  intro j
  change Differentiable ℂ (fun v => pureLinear (g.plusRows j)
    (analyticNodeX ε u v) (analyticNodeY ε u v))
  unfold pureLinear pureFeature analyticNodeX analyticNodeY
  fun_prop

end
end ToeplitzSOS.Negative
