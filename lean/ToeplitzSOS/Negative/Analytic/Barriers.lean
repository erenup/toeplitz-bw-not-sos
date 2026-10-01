import ToeplitzSOS.Negative.Analytic.Comparison
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Explicit sine–hyperbolic rectangle barriers -/

noncomputable section

open Set Complex Metric
namespace ToeplitzSOS.Negative.Analytic

/-- Entire extension of the rectangle's harmonic barrier. -/
def rectangleWeight (a w b : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * Complex.cos ((Real.pi / w : ℝ) * (z - a - b * Complex.I)) /
    (Real.sinh (Real.pi * b / w) : ℂ)

/-- The real-valued sine–hyperbolic barrier. -/
def rectangleBarrier (a w b : ℝ) (z : ℂ) : ℝ :=
  Real.sin (Real.pi * (z.re - a) / w) *
    Real.sinh (Real.pi * (b - z.im) / w) / Real.sinh (Real.pi * b / w)

/-- The explicit complex rectangle weight is entire. -/
theorem rectangleWeight_differentiable (a w b : ℝ) :
    Differentiable ℂ (rectangleWeight a w b) := by
  unfold rectangleWeight
  fun_prop

private theorem cos_im_formula (z : ℂ) :
    (Complex.cos z).im = -Real.sin z.re * Real.sinh z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cos_add]
  simp [Complex.cos_mul_I, Complex.sin_mul_I, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

/-- The real part of the entire weight equals the sine–hyperbolic barrier. -/
theorem rectangleWeight_re (a w b : ℝ) (z : ℂ) :
    (rectangleWeight a w b z).re = rectangleBarrier a w b z := by
  simp only [rectangleWeight, Complex.div_ofReal_re, Complex.mul_re,
    Complex.neg_re, Complex.I_re, zero_mul,
    Complex.I_im, neg_mul, one_mul, zero_sub, neg_neg, cos_im_formula]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one, add_zero]
  rw [show Real.pi / w * (z.im - b) = -(Real.pi * (b - z.im) / w) by ring,
    Real.sinh_neg]
  simp only [mul_neg, neg_neg, show Real.pi / w * (z.re - a) = Real.pi * (z.re - a) / w by ring]
  rfl

/-- On the bottom side the barrier equals its sine boundary data. -/
theorem rectangleBarrier_bottom (a w b x : ℝ) (hw : 0 < w) (hb : 0 < b) :
    rectangleBarrier a w b (x : ℂ) = Real.sin (Real.pi * (x - a) / w) := by
  have hs : Real.sinh (Real.pi * b / w) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  simp [rectangleBarrier, hs]

/-- The barrier vanishes on the top side. -/
theorem rectangleBarrier_top (a w b x : ℝ) :
    rectangleBarrier a w b (x + b * Complex.I) = 0 := by
  simp [rectangleBarrier]

/-- The barrier vanishes on the left side. -/
theorem rectangleBarrier_left (a w b y : ℝ) :
    rectangleBarrier a w b (a + y * Complex.I) = 0 := by
  simp [rectangleBarrier]

/-- The barrier vanishes on the right side. -/
theorem rectangleBarrier_right (a w b y : ℝ) (hw : w ≠ 0) :
    rectangleBarrier a w b (a + w + y * Complex.I) = 0 := by
  simp [rectangleBarrier, hw]

/-- Upper bound used for the first hyperbolic ratio, with rational slack. -/
theorem cosh_pi_div_four_lt_two : Real.cosh (Real.pi / 4) < 2 := by
  have h : Real.pi / 4 < 1 := by linarith [Real.pi_lt_four]
  have he : Real.exp (Real.pi / 4) < 3 :=
    (Real.exp_lt_exp.mpr h).trans Real.exp_one_lt_three
  have hn : Real.exp (-(Real.pi / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  rw [Real.cosh_eq]
  linarith

/-- The first weight is at least `2⁻¹²` on its target subrectangle. -/
theorem first_barrier_lower {z : ℂ} (hx : 1 ≤ z.re) (hx' : z.re ≤ 2)
    (_hy : 0 ≤ z.im) (hy' : z.im ≤ 256) :
    (2 : ℝ) ^ (-12 : ℤ) ≤ rectangleBarrier (1 / 2) 1024 512 z := by
  have hp := Real.pi_pos
  have hsin := Real.mul_le_sin
    (x := Real.pi * (z.re - 1 / 2) / 1024) (div_nonneg (mul_nonneg hp.le (by linarith)) (by norm_num))
    (by nlinarith)
  have hs : (1 : ℝ) / 1024 ≤ Real.sin (Real.pi * (z.re - 1 / 2) / 1024) := by
    have he : 2 / Real.pi * (Real.pi * (z.re - 1 / 2) / 1024) =
        (z.re - 1 / 2) / 512 := by field_simp; ring
    rw [he] at hsin
    linarith
  have hsh : Real.sinh (Real.pi / 4) ≤
      Real.sinh (Real.pi * (512 - z.im) / 1024) :=
    Real.sinh_le_sinh.mpr (by nlinarith)
  have hshpos : 0 < Real.sinh (Real.pi / 4) := Real.sinh_pos_iff.mpr (by positivity)
  have hdpos : 0 < Real.sinh (Real.pi * 512 / 1024) :=
    Real.sinh_pos_iff.mpr (by positivity)
  have hd : Real.sinh (Real.pi * 512 / 1024) ≤ 4 * Real.sinh (Real.pi / 4) := by
    rw [show Real.pi * 512 / 1024 = 2 * (Real.pi / 4) by ring,
      Real.sinh_two_mul]
    nlinarith [cosh_pi_div_four_lt_two]
  unfold rectangleBarrier
  rw [le_div_iff₀ hdpos]
  norm_num
  nlinarith [mul_le_mul hs hsh hshpos.le (by linarith : 0 ≤ Real.sin (Real.pi * (z.re - 1 / 2) / 1024))]

/-- The second weight, in the same translated sine normalization. -/
theorem second_barrier_lower {z : ℂ} (hx : |z.re| ≤ 256)
    (_hy : 0 ≤ z.im) (hy' : z.im ≤ 1 / 2) :
    (1 : ℝ) / 8 ≤ rectangleBarrier (-512) 1024 (3 / 4) z := by
  have hp := Real.pi_pos
  have hpi := Real.pi_lt_four
  have hcarg : |Real.pi * z.re / 1024| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos hp]
    norm_num
    nlinarith
  have hc : (1 : ℝ) / 2 ≤ Real.cos (Real.pi * z.re / 1024) := by
    have hsq := sq_le_sq₀ (abs_nonneg (Real.pi * z.re / 1024)) (by norm_num : (0 : ℝ) ≤ 1)
    have h := hsq.mpr hcarg
    rw [sq_abs] at h
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := Real.pi * z.re / 1024)]
  have hsine : Real.sin (Real.pi * (z.re - -512) / 1024) =
      Real.cos (Real.pi * z.re / 1024) := by
    rw [show Real.pi * (z.re - -512) / 1024 = Real.pi * z.re / 1024 + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two]
  let t := Real.pi / 4096
  have ht : 0 < t := by dsimp [t]; positivity
  have ht' : t ≤ 1 / 4 := by dsimp [t]; linarith
  have he : Real.exp t ≤ 4 / 3 := by
    calc
      Real.exp t ≤ 1 / (1 - t) := Real.exp_bound_div_one_sub_of_interval ht.le (by linarith)
      _ ≤ 4 / 3 := by rw [div_le_iff₀ (by linarith : 0 < 1 - t)]; linarith
  have he' := Real.add_one_le_exp (-t)
  have hspos : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hslt : Real.sinh t ≤ 1 / 2 := by rw [Real.sinh_eq]; linarith
  have hden : Real.sinh (Real.pi * (3 / 4) / 1024) ≤ 4 * Real.sinh t := by
    rw [show Real.pi * (3 / 4) / 1024 = 3 * t by dsimp [t]; ring,
      Real.sinh_three_mul]
    nlinarith [mul_nonneg hspos.le (show 0 ≤ (1 / 2 : ℝ) - Real.sinh t by linarith)]
  have hnum : Real.sinh t ≤ Real.sinh (Real.pi * (3 / 4 - z.im) / 1024) := by
    apply Real.sinh_le_sinh.mpr
    dsimp [t]
    nlinarith
  have hdpos : 0 < Real.sinh (Real.pi * (3 / 4) / 1024) :=
    Real.sinh_pos_iff.mpr (by positivity)
  unfold rectangleBarrier
  rw [hsine, le_div_iff₀ hdpos]
  nlinarith [mul_le_mul hc hnum hspos.le (by linarith : 0 ≤ Real.cos (Real.pi * z.re / 1024))]

/-- The open rectangle used in the maximum principle. -/
def openRectangle (a w b : ℝ) : Set ℂ := Ioo a (a + w) ×ℂ Ioo 0 b

/-- The closed rectangle, including all four sides. -/
def closedRectangle (a w b : ℝ) : Set ℂ := Icc a (a + w) ×ℂ Icc 0 b

/-- The closure of a nondegenerate open rectangle is its closed rectangle. -/
theorem closure_openRectangle {a w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    closure (openRectangle a w b) = closedRectangle a w b := by
  simp only [openRectangle, closedRectangle, closure_reProdIm,
    closure_Ioo (by linarith : a ≠ a + w), closure_Ioo (ne_of_lt hb)]

/-- Rectangle comparison with the exact explicit harmonic weight. -/
theorem rectangle_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} {a w b B ε α : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hF : DiffContOnCl ℂ F (openRectangle a w b))
    (hB : 0 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hglobal : ∀ z ∈ closedRectangle a w b, ‖F z‖ ^ 2 ≤ B)
    (hbottom : ∀ x ∈ Icc a (a + w), ‖F (x : ℂ)‖ ^ 2 ≤ B * ε ^ α)
    {z : ℂ} (hz : z ∈ closedRectangle a w b) :
    ‖F z‖ ^ 2 ≤ B * ε ^ (α * rectangleBarrier a w b z) := by
  have hcl := closure_openRectangle (a := a) hw hb
  have hfront (v : ℂ) (hv : v ∈ frontier (openRectangle a w b)) :
      v ∈ closedRectangle a w b := by rw [← hcl]; exact frontier_subset_closure hv
  have hbound : Bornology.IsBounded (openRectangle a w b) :=
    (isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)
  rw [← rectangleWeight_re]
  apply norm_sq_le_rpow_weight hbound hF (rectangleWeight_differentiable a w b)
    hB hε hε1 hα (side := {v | v.im = 0})
  · exact fun v hv => hglobal v (hfront v hv)
  · intro v hv
    have he : v = (v.re : ℂ) := Complex.ext rfl hv.2
    rw [he]
    exact hbottom v.re (hfront v hv.1).1
  · intro v hv
    rw [rectangleWeight_re, show v = (v.re : ℂ) from Complex.ext rfl hv.2,
      rectangleBarrier_bottom a w b v.re hw hb]
    exact Real.sin_le_one _
  · intro v hv
    rw [rectangleWeight_re]
    have hf := hv.1
    rw [openRectangle, frontier_reProdIm, closure_Ioo (by linarith : a ≠ a + w),
      closure_Ioo (ne_of_lt hb), frontier_Ioo (by linarith : a < a + w),
      frontier_Ioo hb] at hf
    have hn : v.im ≠ 0 := hv.2
    rcases hf with hf | hf
    · have hi : v.im = b := by simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hn] using hf.2
      simp [rectangleBarrier, hi]
    · rcases hf.1 with hleft | hright
      · simp [rectangleBarrier, hleft]
      · have hr : v.re = a + w := hright
        simp [rectangleBarrier, hr, ne_of_gt hw]
  · rwa [hcl]

/-- Reflection in the vertical midline leaves the real barrier unchanged. -/
theorem rectangleBarrier_reflect (a w b : ℝ) (hw : w ≠ 0) (z : ℂ) :
    rectangleBarrier a w b ((2 * a + w : ℝ) - z) =
      rectangleBarrier a w b (star z) := by
  unfold rectangleBarrier
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    zero_sub, Complex.star_def, Complex.conj_re, Complex.conj_im]
  congr 2
  rw [show Real.pi * (2 * a + w - z.re - a) / w =
    Real.pi - Real.pi * (z.re - a) / w by field_simp; ring,
    Real.sin_pi_sub]

/-- The same comparison on the reflected lower rectangle. -/
theorem rectangle_comparison_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} {a w b B ε α : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hF : Differentiable ℂ F)
    (hB : 0 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hglobal : ∀ z : ℂ, a ≤ z.re → z.re ≤ a + w → -b ≤ z.im → z.im ≤ 0 →
      ‖F z‖ ^ 2 ≤ B)
    (hbottom : ∀ x ∈ Icc a (a + w), ‖F (x : ℂ)‖ ^ 2 ≤ B * ε ^ α)
    {z : ℂ} (hx : a ≤ z.re) (hx' : z.re ≤ a + w)
    (hy : -b ≤ z.im) (hy' : z.im ≤ 0) :
    ‖F z‖ ^ 2 ≤ B * ε ^ (α * rectangleBarrier a w b (star z)) := by
  let G : ℂ → E := fun v => F ((2 * a + w : ℝ) - v)
  have hG : Differentiable ℂ G := hF.comp (by fun_prop)
  have h := rectangle_comparison (a := a) hw hb hG.diffContOnCl hB hε hε1 hα
    (z := (2 * a + w : ℝ) - z)
    (fun v hv => ?_) (fun x hx => ?_) ?_
  · simpa only [G, sub_sub_cancel, rectangleBarrier_reflect a w b (ne_of_gt hw) z] using h
  · apply hglobal
    all_goals simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, zero_sub]
    all_goals rcases hv with ⟨⟨h1, h2⟩, h3, h4⟩; linarith
  · dsimp [G]
    rw [← Complex.ofReal_sub]
    apply hbottom
    exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  · exact ⟨⟨by simpa using (show a ≤ 2 * a + w - z.re by linarith),
      by simpa using (show 2 * a + w - z.re ≤ a + w by linarith)⟩,
      by simpa using (show 0 ≤ -z.im by linarith),
      by simpa using (show -z.im ≤ b by linarith)⟩

end ToeplitzSOS.Negative.Analytic
