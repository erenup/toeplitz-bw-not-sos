import ToeplitzSOS.Negative.TangentScalar
import ToeplitzSOS.Negative.Witness

/-! # Quantitative tangent approximation of the explicit rational reference -/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate

/-- Exponential at a scaled complex speed. -/
def expSpeed (ε : ℝ) (a : ℂ) := Complex.exp (-(ε : ℂ)*a)
/-- Normalized reciprocal of a vanishing exponential factor. -/
def reciprocalSpeed (ε : ℝ) (a : ℂ) := (ε : ℂ)/(1-expSpeed ε a)

private theorem expSpeed_add (ε : ℝ) (a b : ℂ) :
    expSpeed ε (a+b) = expSpeed ε a * expSpeed ε b := by
  simp [expSpeed, mul_add, Complex.exp_add]

private theorem phase_product (ε : ℝ) (a b : ℂ) :
    (Complex.I*expSpeed ε a)*(-Complex.I*expSpeed ε b) = expSpeed ε (a+b) := by
  rw [expSpeed_add]
  calc
    _ = -(Complex.I^2)*(expSpeed ε a * expSpeed ε b) := by ring
    _ = _ := by simp

private theorem equal_phase_product (ε : ℝ) (a b : ℂ) :
    (Complex.I*expSpeed ε a)*(Complex.I*expSpeed ε b) = -expSpeed ε (a+b) := by
  rw [expSpeed_add]
  calc
    _ = Complex.I^2*(expSpeed ε a * expSpeed ε b) := by ring
    _ = _ := by simp

private theorem negative_phase_product (ε : ℝ) (a b : ℂ) :
    (-Complex.I*expSpeed ε a)*(-Complex.I*expSpeed ε b) = -expSpeed ε (a+b) := by
  rw [show (-Complex.I*expSpeed ε a)*(-Complex.I*expSpeed ε b) =
    (Complex.I*expSpeed ε a)*(Complex.I*expSpeed ε b) by ring]
  exact equal_phase_product ε a b

/-- Exact normalized expression for the reference at the four prescribed phases. -/
theorem referenceL_normalized (ε : ℝ) (a b c d : ℂ) :
    (ε : ℂ)^4 * referenceL (Complex.I*expSpeed ε a) (-Complex.I*expSpeed ε b)
      (-Complex.I*expSpeed ε c) (Complex.I*expSpeed ε d) =
    2 * (2*(reciprocalSpeed ε (a+c))^2*(reciprocalSpeed ε (b+d))^2 +
      (reciprocalSpeed ε (a+b))^2*(reciprocalSpeed ε (c+d))^2 -
      reciprocalSpeed ε (a+c)*reciprocalSpeed ε (b+d)*
        reciprocalSpeed ε (a+b)*reciprocalSpeed ε (c+d) -
      2*(ε:ℂ)^4*((1+expSpeed ε (a+d))⁻¹)^2*((1+expSpeed ε (b+c))⁻¹)^2) := by
  have hp (s t : ℂ) : (-Complex.I*expSpeed ε s)*(Complex.I*expSpeed ε t) =
      expSpeed ε (s+t) := by
    rw [mul_comm, phase_product, add_comm]
  simp only [referenceL, factorA, factorB, factorC, phase_product, hp,
    equal_phase_product, negative_phase_product, sub_neg_eq_add,
    reciprocalSpeed, div_eq_mul_inv, mul_inv_rev, mul_pow]
  ring

private theorem speed_inverse_bound {s : ℂ} (hs : 2 ≤ s.re) : ‖s⁻¹‖ ≤ 1 := by
  have hn : 1 ≤ ‖s‖ := by linarith [Complex.re_le_norm s]
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hn

/-- The rational reference differs from its tangent by at most `2^20 ε`.
This bound is uniform on all four speed slots used in the finite witness. -/
theorem referenceL_tangent_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ (2:ℝ)⁻¹^16)
    {a b c d : ℂ} (ha : 1 ≤ a.re) (hb : 1 ≤ b.re) (hc : 1 ≤ c.re) (hd : 1 ≤ d.re)
    (han : ‖a‖ ≤ 512) (hbn : ‖b‖ ≤ 512) (hcn : ‖c‖ ≤ 512) (hdn : ‖d‖ ≤ 512) :
    ‖(ε : ℂ)^4 * referenceL (Complex.I*expSpeed ε a) (-Complex.I*expSpeed ε b)
      (-Complex.I*expSpeed ε c) (Complex.I*expSpeed ε d) - Witness.tangentKernel a b c d‖ ≤
      2^20 * ε := by
  have hs (s t : ℂ) (hs : ‖s‖ ≤ 512) (ht : ‖t‖ ≤ 512) : ‖s+t‖ ≤ 1024 :=
    (norm_add_le _ _).trans (by linarith)
  have hq (s t : ℂ) (hsr : 1 ≤ s.re) (htr : 1 ≤ t.re)
      (hsn : ‖s‖ ≤ 512) (htn : ‖t‖ ≤ 512) :
      ‖reciprocalSpeed ε (s+t)‖ ≤ 1 ∧
        ‖reciprocalSpeed ε (s+t)-(s+t)⁻¹‖ ≤ 1024*ε :=
    normalizedReciprocal_bounds hε hε1 (by simp only [Complex.add_re]; linarith) (hs s t hsn htn)
  obtain ⟨hac,eac⟩ := hq a c ha hc han hcn
  obtain ⟨hbd,ebd⟩ := hq b d hb hd hbn hdn
  obtain ⟨hab,eab⟩ := hq a b ha hb han hbn
  obtain ⟨hcd,ecd⟩ := hq c d hc hd hcn hdn
  have tac := speed_inverse_bound (s := a+c) (by simp only [Complex.add_re]; linarith)
  have tbd := speed_inverse_bound (s := b+d) (by simp only [Complex.add_re]; linarith)
  have tab := speed_inverse_bound (s := a+b) (by simp only [Complex.add_re]; linarith)
  have tcd := speed_inverse_bound (s := c+d) (by simp only [Complex.add_re]; linarith)
  have eA : ‖(reciprocalSpeed ε (a+c))^2*(reciprocalSpeed ε (b+d))^2 -
      ((a+c)⁻¹)^2*((b+d)⁻¹)^2‖ ≤ 4096*ε := by
    simpa only [pow_two, mul_assoc, show (4096:ℝ)*ε = 4*(1024*ε) by ring] using
      norm_four_product_error hac hac hbd tac tbd tbd eac eac ebd ebd
  have eC : ‖(reciprocalSpeed ε (a+b))^2*(reciprocalSpeed ε (c+d))^2 -
      ((a+b)⁻¹)^2*((c+d)⁻¹)^2‖ ≤ 4096*ε := by
    simpa only [pow_two, mul_assoc, show (4096:ℝ)*ε = 4*(1024*ε) by ring] using
      norm_four_product_error hab hab hcd tab tcd tcd eab eab ecd ecd
  have eAC := norm_four_product_error hac hbd hab tbd tab tcd eac ebd eab ecd
  have hbad := nonvanishingReciprocal_bound hε hε1 (hs a d han hdn)
  have hbbc := nonvanishingReciprocal_bound hε hε1 (hs b c hbn hcn)
  change ‖(1+expSpeed ε (a+d))⁻¹‖ ≤ 1 at hbad
  change ‖(1+expSpeed ε (b+c))⁻¹‖ ≤ 1 at hbbc
  have hB : ‖2*(ε:ℂ)^4*((1+expSpeed ε (a+d))⁻¹)^2*((1+expSpeed ε (b+c))⁻¹)^2‖ ≤ 2*ε := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    norm_num only [Complex.norm_ofNat]
    have he : ε ≤ 1 := hε1.trans (by norm_num)
    have he4 : ε^4 ≤ ε := by nlinarith [mul_self_le_mul_self hε.le he, sq_nonneg (ε^2-ε)]
    calc
      _ ≤ 2*ε^4*1^2*1^2 := by gcongr
      _ ≤ 2*ε := by nlinarith
  rw [referenceL_normalized]
  unfold Witness.tangentKernel
  simp only [div_eq_mul_inv, mul_inv_rev, mul_pow, ← inv_pow]
  calc
    _ = ‖2 * (2*((reciprocalSpeed ε (a+c))^2*(reciprocalSpeed ε (b+d))^2 -
            ((a+c)⁻¹)^2*((b+d)⁻¹)^2) +
        ((reciprocalSpeed ε (a+b))^2*(reciprocalSpeed ε (c+d))^2 -
            ((a+b)⁻¹)^2*((c+d)⁻¹)^2) -
        (reciprocalSpeed ε (a+c)*reciprocalSpeed ε (b+d)*reciprocalSpeed ε (a+b)*reciprocalSpeed ε (c+d) -
            (a+c)⁻¹*(b+d)⁻¹*(a+b)⁻¹*(c+d)⁻¹) -
        2*(ε:ℂ)^4*((1+expSpeed ε (a+d))⁻¹)^2*((1+expSpeed ε (b+c))⁻¹)^2)‖ := by congr 1; ring
    _ ≤ 2*(2*(4096*ε)+4096*ε+4*(1024*ε)+2*ε) := by
      rw [norm_mul, Complex.norm_ofNat]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine (norm_sub_le _ _).trans (add_le_add ?_ hB)
      refine (norm_sub_le _ _).trans (add_le_add ?_ eAC)
      refine (norm_add_le _ _).trans (add_le_add ?_ eC)
      simpa only [norm_mul, Complex.norm_ofNat] using
        mul_le_mul_of_nonneg_left eA (show (0:ℝ) ≤ 2 by norm_num)
    _ ≤ 2^20*ε := by nlinarith

end
end ToeplitzSOS.Negative
