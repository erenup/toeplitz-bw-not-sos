import ToeplitzSOS.Negative.InitialBounds
import ToeplitzSOS.Negative.Analytic.Nodes
import ToeplitzSOS.Negative.Analytic.TailBudget

/-! # Finite geometric majorant and the global continuation bound -/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset ComplexConjugate

/-- The selected natural corner depth is exactly the reciprocal square scale. -/
theorem cornerDepth_cast : (cornerDepth : ℝ) = epsilon⁻¹ ^ 2 := by
  unfold cornerDepth epsilon
  rw [symbolicTwoPow_eq, Nat.cast_pow, Nat.cast_ofNat]
  rw [inv_pow, ← Real.rpow_natCast (2 ^ (-4980737 : ℝ)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast (2 : ℝ) 9961474]
  congr 1
  norm_num

private theorem finite_weighted_geometric {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    (∑ p : Fin m, ((p.val : ℝ) + 1) * r ^ p.val) ≤ 1 / (1-r)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun p : ℕ => ((p : ℝ)+1)*r^p)]
  exact sum_le_hasSum (range m) (fun n _ => by positivity)
    (Analytic.hasSum_weighted_geometric hr hr1)

private theorem pureFeature_radial {m : ℕ} (pq : PureIndex m) {x y : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖pureFeature pq x y‖ ≤ 2 * r ^ pq.1.1.val * r ^ pq.1.2.val := by
  unfold pureFeature
  calc
    _ ≤ ‖x ^ pq.1.1.val * y ^ pq.1.2.val‖ + ‖x ^ pq.1.2.val * y ^ pq.1.1.val‖ := norm_sub_le _ _
    _ ≤ r ^ pq.1.1.val * r ^ pq.1.2.val + r ^ pq.1.2.val * r ^ pq.1.1.val := by
      simp only [norm_mul, norm_pow]
      gcongr
    _ = _ := by ring

/-- A uniform finite-D bound, obtained directly from finite positive terms. -/
theorem baselineD_radial_bound {m : ℕ} {x y : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    (hermitianDiagonal (baselineD m) x y).re ≤ 8 / (1-r^2)^4 := by
  have hr2 : r^2 < 1 := by nlinarith
  have hs := finite_weighted_geometric (sq_nonneg r) hr2 m
  have hd : (hermitianDiagonal (baselineD m) x y).re =
      ∑ pq : PureIndex m, (2 * (pq.1.1.val + 1) * (pq.1.2.val + 1) : ℝ) *
        ‖pureFeature pq x y‖^2 := by
    simp [hermitianDiagonal, baselineD, pureFeature_conj, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  rw [hd]
  let f : Fin m × Fin m → ℝ := fun pq =>
    ((pq.1.val : ℝ)+1) * (r^2)^pq.1.val * (((pq.2.val : ℝ)+1) * (r^2)^pq.2.val)
  have hterm (pq : PureIndex m) :
      (2 * (pq.1.1.val + 1) * (pq.1.2.val + 1) : ℝ) * ‖pureFeature pq x y‖^2 ≤ 8 * f pq.1 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (pureFeature_radial pq hr hx hy) 2
    have hh := mul_le_mul_of_nonneg_left h
      (show 0 ≤ (2 * (pq.1.1.val + 1) * (pq.1.2.val + 1) : ℝ) by positivity)
    dsimp only [f]
    convert! hh using 1
    ring
  have hsub : (∑ pq : PureIndex m, f pq.1) ≤ ∑ pq : Fin m × Fin m, f pq := by
    classical
    exact sum_le_sum_of_injOn Subtype.val (fun _ _ _ _ h => Subtype.ext h)
      (subset_univ _) (fun _ _ => le_rfl) (fun pq _ _ => by dsimp [f]; positivity)
  have hfull : (∑ pq : Fin m × Fin m, f pq) =
      (∑ p : Fin m, ((p.val : ℝ)+1) * (r^2)^p.val)^2 := by
    simp only [f, Fintype.sum_prod_type, ← mul_sum, ← sum_mul, pow_two]
  calc
    _ ≤ ∑ pq : PureIndex m, 8 * f pq.1 := sum_le_sum fun pq _ => hterm pq
    _ = 8 * ∑ pq : PureIndex m, f pq.1 := by rw [mul_sum]
    _ ≤ 8 * ∑ pq : Fin m × Fin m, f pq := by gcongr
    _ = 8 * (∑ p : Fin m, ((p.val : ℝ)+1) * (r^2)^p.val)^2 := by rw [hfull]
    _ ≤ 8 * (1 / (1-r^2)^2)^2 := by gcongr
    _ = _ := by simp only [div_pow, one_pow, ← pow_mul]; norm_num [div_eq_mul_inv]

/-- The finite plus Gram factor satisfies the global norm bound. -/
theorem CornerGram.plusVector_global {m : ℕ} (g : CornerGram m) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (u v : ℂ) (huv : 1/4 ≤ u.re - |v.im|) :
    ‖g.plusVector ε u v‖^2 ≤ 2^20 * ε⁻¹ ^ 4 := by
  obtain ⟨hx,hy⟩ := Analytic.speed_nodes_radial hε.le huv
  change ‖analyticNodeX ε u v‖ ≤ Real.exp (-ε/4) at hx
  change ‖analyticNodeY ε u v‖ ≤ Real.exp (-ε/4) at hy
  have hr : 0 ≤ Real.exp (-ε/4) := (Real.exp_pos _).le
  have hr1 : Real.exp (-ε/4) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 := baselineD_radial_bound (m := m) hr hr1 hx hy
  have h2 := baselineD_radial_bound (m := m) hr hr1 hx (by simpa using hy :
    ‖conj (analyticNodeY ε u v)‖ ≤ Real.exp (-ε/4))
  have hg := g.plus_le_diagonals (analyticNodeX ε u v) (analyticNodeY ε u v)
  rw [g.plusVector_norm] at hg
  have hexp : Real.exp (-ε/4)^2 = Real.exp (-ε/2) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp] at h1 h2
  have hd : ε/4 ≤ 1 - Real.exp (-ε/2) := by
    have h := Analytic.half_le_one_sub_exp_neg
      (show 0 ≤ ε/2 by positivity) (show ε/2 ≤ 1 by linarith)
    simpa only [div_div, show (2:ℝ)*2=4 by norm_num, neg_div] using h
  have hp : 0 < 1 - Real.exp (-ε/2) := by linarith
  calc
    _ ≤ 2 * (8 / (1 - Real.exp (-ε/2))^4) + 2 * (8 / (1 - Real.exp (-ε/2))^4) :=
      hg.trans (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
        (mul_le_mul_of_nonneg_left h2 (by norm_num)))
    _ = 32 / (1 - Real.exp (-ε/2))^4 := by ring
    _ ≤ 32 / (ε/4)^4 := by gcongr
    _ ≤ 2^20 * ε⁻¹ ^ 4 := by
      rw [inv_pow, inv_eq_one_div]
      field_simp
      norm_num

end
end ToeplitzSOS.Negative
