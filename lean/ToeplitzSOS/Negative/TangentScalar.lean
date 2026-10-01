import ToeplitzSOS.Negative.Analytic.Nodes

/-! # Quantitative reciprocal-factor estimates for the tangent limit -/

namespace ToeplitzSOS.Negative
noncomputable section

/-- A normalized vanishing exponential factor is uniformly close to its limit. -/
theorem normalizedReciprocal_bounds {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ (2 : ℝ)⁻¹^16) {s : ℂ} (hs : 2 ≤ s.re) (hsn : ‖s‖ ≤ 1024) :
    ‖(ε : ℂ) / (1 - Complex.exp (-(ε : ℂ)*s))‖ ≤ 1 ∧
    ‖(ε : ℂ) / (1 - Complex.exp (-(ε : ℂ)*s)) - s⁻¹‖ ≤ 1024*ε := by
  let z := (ε : ℂ)*s
  let a := (1-Complex.exp (-z))/z
  have hsn0 : 2 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have hs0 : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hz0 : z ≠ 0 := mul_ne_zero hε0 hs0
  have hzn : ‖z‖ ≤ 1024*ε := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have hsmall : 1024*ε ≤ 1/2 := by norm_num at hε1; linarith
  have ha : ‖a-1‖ ≤ 1024*ε :=
    (Analytic.exponential_factor_error hz0 (by linarith)).trans hzn
  have han : 1/2 ≤ ‖a‖ := by
    have h := norm_sub_norm_le (1:ℂ) a
    rw [norm_one, norm_sub_rev] at h
    linarith
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hsInv : ‖s‖⁻¹ ≤ 1/2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < ‖s‖)]
    linarith
  have haInv : ‖a‖⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < ‖a‖)]
    linarith
  have hq : (ε : ℂ) / (1-Complex.exp (-(ε : ℂ)*s)) = s⁻¹*a⁻¹ := by
    dsimp [a,z]
    simp only [neg_mul, inv_div]
    field_simp
  constructor
  · rw [hq, norm_mul, norm_inv, norm_inv]
    calc
      _ ≤ (1/2:ℝ)*2 := mul_le_mul hsInv haInv (by positivity) (by norm_num)
      _ = 1 := by norm_num
  · rw [hq, show s⁻¹*a⁻¹-s⁻¹ = -(s⁻¹*(a-1)*a⁻¹) by field_simp; ring,
      norm_neg, norm_mul, norm_mul, norm_inv, norm_inv]
    calc
      _ ≤ (1/2)*(1024*ε)*2 := by gcongr
      _ = _ := by ring

/-- The nonvanishing exponential factors have reciprocal norm at most one. -/
theorem nonvanishingReciprocal_bound {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ (2 : ℝ)⁻¹^16) {s : ℂ} (hsn : ‖s‖ ≤ 1024) :
    ‖(1 + Complex.exp (-(ε : ℂ)*s))⁻¹‖ ≤ 1 := by
  have hz : ‖-(ε : ℂ)*s‖ ≤ 1/2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have hsmall : 1024*ε ≤ 1/2 := by norm_num at hε1; linarith
    nlinarith
  have he := Complex.norm_exp_sub_one_le (show ‖-(ε : ℂ)*s‖ ≤ 1 by linarith)
  have hh : ‖Complex.exp (-(ε : ℂ)*s)-1‖ ≤ 1 := by linarith
  have ht := norm_sub_norm_le (2:ℂ) (1+Complex.exp (-(ε : ℂ)*s))
  have hid : (2:ℂ)-(1+Complex.exp (-(ε : ℂ)*s)) = -(Complex.exp (-(ε : ℂ)*s)-1) := by ring
  rw [hid, norm_neg] at ht
  norm_num at ht
  simp only [neg_mul] at hh ⊢
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (by linarith)

/-- Two nearby bounded factors give a controlled product error. -/
theorem norm_product_error {a b c d : ℂ} {δ η : ℝ}
    (ha : ‖a‖ ≤ 1) (hd : ‖d‖ ≤ 1) (hab : ‖a-b‖ ≤ δ) (hcd : ‖c-d‖ ≤ η) :
    ‖a*c-b*d‖ ≤ δ+η := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hab
  have hη : 0 ≤ η := (norm_nonneg _).trans hcd
  calc
    _ = ‖a*(c-d)+(a-b)*d‖ := by congr 1; ring
    _ ≤ ‖a*(c-d)‖+‖(a-b)*d‖ := norm_add_le _ _
    _ = ‖a‖*‖c-d‖+‖a-b‖*‖d‖ := by rw [norm_mul,norm_mul]
    _ ≤ 1*η+δ*1 := by gcongr
    _ = _ := by ring

/-- Four bounded factors pay four times their individual error. -/
theorem norm_four_product_error {a b c d a' b' c' d' : ℂ} {δ : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hb' : ‖b'‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) (hd' : ‖d'‖ ≤ 1)
    (hea : ‖a-a'‖ ≤ δ) (heb : ‖b-b'‖ ≤ δ)
    (hec : ‖c-c'‖ ≤ δ) (hed : ‖d-d'‖ ≤ δ) :
    ‖a*b*c*d-a'*b'*c'*d'‖ ≤ 4*δ := by
  have hab : ‖a*b‖ ≤ 1 := by rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
  have habc : ‖a*b*c‖ ≤ 1 := by rw [norm_mul]; nlinarith [norm_nonneg (a*b), norm_nonneg c]
  have h1 := norm_product_error ha hb' hea heb
  have h2 := norm_product_error hab hc' h1 hec
  have h3 := norm_product_error habc hd' h2 hed
  linarith

end
end ToeplitzSOS.Negative
