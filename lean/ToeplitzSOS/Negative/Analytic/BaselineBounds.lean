import ToeplitzSOS.Negative.Analytic.Truncation

/-! # Uniform coefficient bounds and baseline tails -/

namespace ToeplitzSOS.Negative.Analytic
noncomputable section

private theorem norm_nat_add_one (n : ℕ) : ‖(n : ℂ)+1‖ = (n : ℝ)+1 := by
  simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n+1)

/-- The first pair's weight is bounded by the full four-depth weight. -/
theorem pairWeight_le_depthWeight (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    ((p.1.1 : ℝ)+1) * ((p.1.2 : ℝ)+1) ≤ depthWeight p := by
  have h : 1 ≤ ((p.2.1 : ℝ)+1) * ((p.2.2 : ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.2.1, Nat.cast_nonneg (α := ℝ) p.2.2,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) p.2.1) (Nat.cast_nonneg (α := ℝ) p.2.2)]
  calc
    _ = (((p.1.1 : ℝ)+1) * ((p.1.2 : ℝ)+1)) * 1 := by ring
    _ ≤ (((p.1.1 : ℝ)+1) * ((p.1.2 : ℝ)+1)) *
        (((p.2.1 : ℝ)+1) * ((p.2.2 : ℝ)+1)) := by gcongr
    _ = _ := by simp only [depthWeight]; ring

/-- Each first-coordinate weight is dominated by the full product. -/
theorem firstWeight_le_depthWeight (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    (p.1.1 : ℝ)+1 ≤ depthWeight p := by
  calc
    _ ≤ ((p.1.1 : ℝ)+1) * ((p.1.2 : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) p.1.2,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) p.1.1) (Nat.cast_nonneg (α := ℝ) p.1.2)]
    _ ≤ _ := pairWeight_le_depthWeight p

/-- The four-way minimum coefficient is at most the depth weight. -/
theorem totalMinimum_le_depthWeight (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    (totalMinimum p : ℝ) ≤ depthWeight p := by
  have h : (totalMinimum p : ℝ) ≤ (p.1.1 : ℝ)+1 := by
    exact_mod_cast (min_le_left (min (p.1.1+1) (p.1.2+1))
      (min (p.2.1+1) (p.2.2+1))).trans (min_le_left _ _)
  exact h.trans (firstWeight_le_depthWeight p)

/-- Expand two alternating features into four radial monomials. -/
theorem pure_term_bound {ε C : ℝ} (hC : 0 ≤ C)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) {a x y z w : ℂ}
    (ha : ‖a‖ ≤ C * depthWeight p)
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖a * natPureFeature p.1 x y * natPureFeature p.2 z w‖ ≤
      (4*C) * depthWeight p * Real.exp (-ε * totalDepth p / 2) := by
  have h1 := kernel_monomial_bound hC p ha hx hy hz hw
  have h2 := kernel_monomial_bound hC p ha hx hy hw hz
  have h3 := kernel_monomial_bound hC p ha hy hx hz hw
  have h4 := kernel_monomial_bound hC p ha hy hx hw hz
  have he : a * natPureFeature p.1 x y * natPureFeature p.2 z w =
      (a*x^p.1.1*y^p.1.2*z^p.2.1*w^p.2.2 - a*x^p.1.1*y^p.1.2*w^p.2.1*z^p.2.2) -
        a*y^p.1.1*x^p.1.2*z^p.2.1*w^p.2.2 + a*y^p.1.1*x^p.1.2*w^p.2.1*z^p.2.2 := by
    simp only [natPureFeature]; ring
  rw [he]
  calc
    _ ≤ ((‖a*x^p.1.1*y^p.1.2*z^p.2.1*w^p.2.2‖ + ‖a*x^p.1.1*y^p.1.2*w^p.2.1*z^p.2.2‖) +
        ‖a*y^p.1.1*x^p.1.2*z^p.2.1*w^p.2.2‖) + ‖a*y^p.1.1*x^p.1.2*w^p.2.1*z^p.2.2‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))) (le_refl _))
    _ ≤ _ := by linarith

/-- Uniform majorant for the pure diagonal summands. -/
theorem diagonalSeriesTerm_bound {ε : ℝ} (p : ℕ × ℕ) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖diagonalSeriesTerm x y z w p‖ ≤
      8 * depthWeight (diagonalDepth p) * Real.exp (-ε * totalDepth (diagonalDepth p) / 2) := by
  by_cases hp : p.1 < p.2
  · simp only [diagonalSeriesTerm, hp, ite_true]
    have ha : ‖(2 : ℂ) * ((p.1 : ℂ)+1) * ((p.2 : ℂ)+1)‖ ≤
        2 * depthWeight (diagonalDepth p) := by
      have h := pairWeight_le_depthWeight (diagonalDepth p)
      simp only [norm_mul, Complex.norm_ofNat, norm_nat_add_one]
      dsimp [diagonalDepth] at h ⊢
      nlinarith
    simpa only [show (4:ℝ)*2 = 8 by norm_num, diagonalDepth] using
      pure_term_bound (C := 2) (by norm_num) (diagonalDepth p) ha hx hy hz hw
  · simp only [diagonalSeriesTerm, hp, ite_false, norm_zero]
    unfold depthWeight
    positivity

/-- Uniform majorant for all natural-depth same-gap terms. -/
theorem crossSeriesTerm_bound {ε : ℝ} (p : (ℕ × ℕ) × (ℕ × ℕ)) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖crossSeriesTerm x y z w p‖ ≤
      8 * depthWeight p * Real.exp (-ε * totalDepth p / 2) := by
  unfold crossSeriesTerm
  split_ifs
  · have ha : ‖(-2 : ℂ) * (min (p.1.1+1) (p.2.1+1) : ℕ)‖ ≤ 2 * depthWeight p := by
      have h : ((min (p.1.1+1) (p.2.1+1) : ℕ) : ℝ) ≤ depthWeight p := by
        calc
          _ ≤ (p.1.1 : ℝ)+1 := by exact_mod_cast min_le_left (p.1.1+1) (p.2.1+1)
          _ ≤ _ := firstWeight_le_depthWeight p
      simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_natCast]
      nlinarith
    simpa only [show (4:ℝ)*2 = 8 by norm_num] using
      pure_term_bound (C := 2) (by norm_num) p ha hx hy hz hw
  · simp only [norm_zero]
    unfold depthWeight
    positivity

/-- Uniform majorant for the equal-total minimum tensor. -/
theorem totalSeriesTerm_bound {ε : ℝ} (p : (ℕ × ℕ) × (ℕ × ℕ)) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖totalSeriesTerm x y z w p‖ ≤
      depthWeight p * Real.exp (-ε * totalDepth p / 2) := by
  unfold totalSeriesTerm
  split_ifs
  · simpa only [one_mul] using kernel_monomial_bound (C := 1) (by norm_num) p
      (by simpa only [Complex.norm_natCast, one_mul] using totalMinimum_le_depthWeight p)
      hx hy hz hw
  · simp only [norm_zero]
    unfold depthWeight
    positivity

/-- Uniform majorant for the mixed diagonal tensor. -/
theorem mixedDiagonalSeriesTerm_bound {ε : ℝ} (p : (ℕ × ℕ) × (ℕ × ℕ)) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖mixedDiagonalSeriesTerm x y z w p‖ ≤
      2 * depthWeight p * Real.exp (-ε * totalDepth p / 2) := by
  unfold mixedDiagonalSeriesTerm
  split_ifs
  · apply kernel_monomial_bound (C := 2) (by norm_num) p _ hx hy hz hw
    have h := pairWeight_le_depthWeight p
    simp only [norm_mul, Complex.norm_ofNat, norm_nat_add_one]
    nlinarith
  · simp only [norm_zero]
    unfold depthWeight
    positivity

/-- The mixed baseline has coefficient majorant four times the depth weight. -/
theorem mixedSeriesTerm_bound {ε : ℝ} (p : (ℕ × ℕ) × (ℕ × ℕ)) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖mixedSeriesTerm x y z w p‖ ≤
      4 * depthWeight p * Real.exp (-ε * totalDepth p / 2) := by
  have hd := mixedDiagonalSeriesTerm_bound p hx hy hz hw
  have ht := totalSeriesTerm_bound p hx hy hz hw
  calc
    _ ≤ ‖mixedDiagonalSeriesTerm x y z w p‖ + 2 * ‖totalSeriesTerm x y z w p‖ := by
      simpa only [mixedSeriesTerm, norm_mul, Complex.norm_ofNat] using
        norm_sub_le (mixedDiagonalSeriesTerm x y z w p) (2 * totalSeriesTerm x y z w p)
    _ ≤ _ := by linarith

/-- A radial point with positive decay lies in the strict unit disk. -/
theorem norm_lt_one_of_radial {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε/2)) : ‖x‖ < 1 :=
  hx.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))

/-- Pure diagonal finite-to-infinite tail, in literal baseline units. -/
theorem baselineD_tail {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖baselineD m x y z w - referenceD x y z w‖ ≤
      8 * 8^8 / ε^8 * Real.exp (-ε*m/4) := by
  rw [baselineD_eq_sum]
  exact reference_tail_injective hε hε1 (by norm_num : (0:ℝ) ≤ 8) m
    diagonalDepth diagonalDepth_injective (diagonalSeriesTerm x y z w)
    (hasSum_diagonalSeriesTerm (norm_lt_one_of_radial hε hx) (norm_lt_one_of_radial hε hy)
      (norm_lt_one_of_radial hε hz) (norm_lt_one_of_radial hε hw))
    (pairBox m) (fun p hp => mem_pairBox_of_diagonalDepth_lt p hp)
    (fun p => diagonalSeriesTerm_bound p hx hy hz hw)

/-- Same-gap cross finite-to-infinite tail, including the wedge factors. -/
theorem baselineK_tail {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖baselineK m x y z w - (referenceQ x y z w - referenceD x y z w)‖ ≤
      8 * 8^8 / ε^8 * Real.exp (-ε*m/4) := by
  rw [baselineK_eq_sum]
  exact reference_tail_of_hasSum hε hε1 (by norm_num : (0:ℝ) ≤ 8) m
    (crossSeriesTerm x y z w)
    (hasSum_crossSeriesTerm (norm_lt_one_of_radial hε hx) (norm_lt_one_of_radial hε hy)
      (norm_lt_one_of_radial hε hz) (norm_lt_one_of_radial hε hw))
    (depthBox m) (fun p hp => mem_depthBox_of_totalDepth_lt p hp)
    (fun p => crossSeriesTerm_bound p hx hy hz hw)

/-- Mixed finite-to-infinite tail, with the full four-way minimum coefficient. -/
theorem baselineB_tail {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖baselineB m x y z w - referenceB x y z w‖ ≤
      4 * 8^8 / ε^8 * Real.exp (-ε*m/4) := by
  rw [baselineB_eq_sum]
  exact reference_tail_of_hasSum hε hε1 (by norm_num : (0:ℝ) ≤ 4) m
    (mixedSeriesTerm x y z w)
    (hasSum_mixedSeriesTerm (norm_lt_one_of_radial hε hx) (norm_lt_one_of_radial hε hy)
      (norm_lt_one_of_radial hε hz) (norm_lt_one_of_radial hε hw))
    (depthBox m) (fun p hp => mem_depthBox_of_totalDepth_lt p hp)
    (fun p => mixedSeriesTerm_bound p hx hy hz hw)

/-- The pure baseline tail, with its explicit geometric-tail constant. -/
theorem baselineQ_tail {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ) {x y z w : ℂ}
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖baselineQ m x y z w - referenceQ x y z w‖ ≤
      16 * 8^8 / ε^8 * Real.exp (-ε*m/4) := by
  have hd := baselineD_tail hε hε1 m hx hy hz hw
  have hk := baselineK_tail hε hε1 m hx hy hz hw
  have he : baselineQ m x y z w - referenceQ x y z w =
      (baselineD m x y z w - referenceD x y z w) +
        (baselineK m x y z w - (referenceQ x y z w - referenceD x y z w)) := by
    simp only [baselineQ, Pi.add_apply]; ring
  rw [he]
  apply (norm_add_le _ _).trans
  convert! add_le_add hd hk using 1
  ring

/-- The concrete baseline tail field, with its original uniform constants. -/
theorem baselineTail (m : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x y z w : ℂ)
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖baselineQ m x y z w - referenceQ x y z w‖ ≤
      2^30 * ε⁻¹^8 * Real.exp (-ε*m/4) ∧
    ‖baselineL m x y z w - referenceL x y z w‖ ≤
      2^30 * ε⁻¹^8 * Real.exp (-ε*m/4) := by
  have hq := baselineQ_tail hε hε1 m hx hy hz hw
  have hd := baselineD_tail hε hε1 m hx hy hz hw
  have hb := baselineB_tail hε hε1 m hx hy hz hw
  have hr := baselineQ_tail hε hε1 m hx hz hy hw
  have hA : factorA x y z w ≠ 0 := mul_ne_zero
    (one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one (norm_lt_one_of_radial hε hx)
      (norm_lt_one_of_radial hε hz)))
    (one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one (norm_lt_one_of_radial hε hy)
      (norm_lt_one_of_radial hε hw)))
  have hB : factorB x y z w ≠ 0 := mul_ne_zero
    (one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one (norm_lt_one_of_radial hε hx)
      (norm_lt_one_of_radial hε hw)))
    (one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one (norm_lt_one_of_radial hε hy)
      (norm_lt_one_of_radial hε hz)))
  have hC : factorC x y z w ≠ 0 := mul_ne_zero
    (one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one (norm_lt_one_of_radial hε hx)
      (norm_lt_one_of_radial hε hy)))
    (one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one (norm_lt_one_of_radial hε hz)
      (norm_lt_one_of_radial hε hw)))
  have he : baselineL m x y z w - referenceL x y z w =
      ((baselineB m x y z w - referenceB x y z w) +
        (baselineD m x y z w - referenceD x y z w)) +
          (baselineQ m x z y w - referenceQ x z y w) := by
    rw [← reference_cancellation x y z w hA hB hC]
    simp only [baselineL, realign, Pi.add_apply]
    ring
  have hl : ‖baselineL m x y z w - referenceL x y z w‖ ≤
      28 * 8^8 / ε^8 * Real.exp (-ε*m/4) := by
    rw [he]
    calc
      _ ≤ (‖baselineB m x y z w - referenceB x y z w‖ +
          ‖baselineD m x y z w - referenceD x y z w‖) +
            ‖baselineQ m x z y w - referenceQ x z y w‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ _ := by
        convert! add_le_add (add_le_add hb hd) hr using 1
        ring
  have hbound (c : ℝ) (hc : c ≤ 64) :
      c * 8^8 / ε^8 * Real.exp (-ε*m/4) ≤ 2^30 * ε⁻¹^8 * Real.exp (-ε*m/4) := by
    calc
      _ ≤ 64 * 8^8 / ε^8 * Real.exp (-ε*m/4) := by gcongr
      _ = _ := by norm_num [div_eq_mul_inv, inv_pow]
  exact ⟨hq.trans (hbound 16 (by norm_num)), hl.trans (hbound 28 (by norm_num))⟩

end
end ToeplitzSOS.Negative.Analytic
