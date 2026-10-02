import ToeplitzSOS.Negative.Analytic.Barriers

/-! # The two rectangle comparisons, uniformly in the vector dimension -/

open Set Complex
namespace ToeplitzSOS.Negative.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- First continuation, including both signs of the imaginary part. -/
theorem first_continuation {F : ℂ → E} {B ε : ℝ}
    (hF : Differentiable ℂ F) (hB : 0 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hglobal : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2049 / 2 → |z.im| ≤ 512 →
      ‖F z‖ ^ 2 ≤ B)
    (hreal : ∀ x ∈ Icc (1 / 2 : ℝ) (2049 / 2), ‖F (x : ℂ)‖ ^ 2 ≤ B * ε ^ (2 : ℝ))
    {z : ℂ} (hx : 1 ≤ z.re) (hx' : z.re ≤ 2) (hy : |z.im| ≤ 256) :
    ‖F z‖ ^ 2 ≤ B * ε ^ (1 / 4096 : ℝ) := by
  have hmono (v : ℂ) (hv : 0 ≤ v.im) (hv' : v.im ≤ 256)
      (hre : 1 ≤ v.re) (hre' : v.re ≤ 2) :
      B * ε ^ (2 * rectangleBarrier (1 / 2) 1024 512 v) ≤
        B * ε ^ (1 / 4096 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1
    have hl := first_barrier_lower hre hre' hv hv'
    norm_num at hl
    linarith
  rcases le_total 0 z.im with hi | hi
  · refine (rectangle_comparison (a := 1 / 2) (w := 1024) (b := 512)
      (by norm_num) (by norm_num) hF.diffContOnCl hB hε hε1 (by norm_num : (0 : ℝ) ≤ 2)
      (fun v hv => ?_) (fun x hx => ?_) ?_).trans (hmono z hi (abs_le.mp hy).2 hx hx')
    · exact hglobal v hv.1.1 (by linarith [hv.1.2])
        (abs_le.mpr ⟨by linarith [hv.2.1], hv.2.2⟩)
    · exact hreal x ⟨hx.1, by linarith [hx.2]⟩
    · exact ⟨⟨by linarith, by linarith⟩, hi, by linarith [(abs_le.mp hy).2]⟩
  · refine (rectangle_comparison_lower (a := 1 / 2) (w := 1024) (b := 512)
      (by norm_num) (by norm_num) hF hB hε hε1 (by norm_num : (0 : ℝ) ≤ 2)
      (fun v h1 h2 h3 h4 => hglobal v h1 (by linarith) (abs_le.mpr ⟨h3, by linarith⟩))
      (fun x hx => hreal x ⟨hx.1, by linarith [hx.2]⟩)
      (by linarith) (by linarith) (by linarith [(abs_le.mp hy).1]) hi).trans ?_
    apply hmono (star z)
    all_goals simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
    all_goals linarith [(abs_le.mp hy).1]

/-- Second continuation in the narrow rectangle. -/
theorem second_continuation {F : ℂ → E} {B ε : ℝ}
    (hF : Differentiable ℂ F) (hB : 0 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hglobal : ∀ z : ℂ, |z.re| ≤ 512 → |z.im| ≤ 3 / 4 → ‖F z‖ ^ 2 ≤ B)
    (hreal : ∀ x ∈ Icc (-512 : ℝ) 512,
      ‖F (x : ℂ)‖ ^ 2 ≤ B * ε ^ (1 / 4096 : ℝ))
    {z : ℂ} (hx : |z.re| ≤ 256) (hy : |z.im| ≤ 1 / 2) :
    ‖F z‖ ^ 2 ≤ B * ε ^ (1 / 131072 : ℝ) := by
  have hmono (v : ℂ) (hv : 0 ≤ v.im) (hv' : v.im ≤ 1 / 2) (hre : |v.re| ≤ 256) :
      B * ε ^ ((1 / 4096) * rectangleBarrier (-512) 1024 (3 / 4) v) ≤
        B * ε ^ (1 / 131072 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1
    linarith [second_barrier_lower hre hv hv']
  rcases le_total 0 z.im with hi | hi
  · refine (rectangle_comparison (a := -512) (w := 1024) (b := 3 / 4)
      (by norm_num) (by norm_num) hF.diffContOnCl hB hε hε1 (by norm_num : (0 : ℝ) ≤ 1 / 4096)
      (fun v hv => ?_) (fun x hx => ?_) ?_).trans (hmono z hi (abs_le.mp hy).2 hx)
    · exact hglobal v (abs_le.mpr ⟨hv.1.1, by linarith [hv.1.2]⟩)
        (abs_le.mpr ⟨by linarith [hv.2.1], hv.2.2⟩)
    · exact hreal x ⟨hx.1, by linarith [hx.2]⟩
    · exact ⟨⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩,
        hi, by linarith [(abs_le.mp hy).2]⟩
  · refine (rectangle_comparison_lower (a := -512) (w := 1024) (b := 3 / 4)
      (by norm_num) (by norm_num) hF hB hε hε1 (by norm_num : (0 : ℝ) ≤ 1 / 4096)
      (fun v h1 h2 h3 h4 => hglobal v (abs_le.mpr ⟨h1, by linarith⟩)
        (abs_le.mpr ⟨h3, by linarith⟩))
      (fun x hx => hreal x ⟨hx.1, by linarith [hx.2]⟩)
      (by linarith [(abs_le.mp hx).1]) (by linarith [(abs_le.mp hx).2])
      (by linarith [(abs_le.mp hy).1]) hi).trans ?_
    apply hmono (star z)
    all_goals simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
    · linarith
    · linarith [(abs_le.mp hy).1]
    · exact hx

/-- The complete complex-speed bridge, in normalized form. -/
theorem two_rectangle_continuation {F : ℂ → ℂ → E} {B ε : ℝ}
    (hFu : ∀ v, Differentiable ℂ (fun u => F u v))
    (hFv : ∀ u, Differentiable ℂ (F u))
    (hB : 0 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hglobal : ∀ u v : ℂ, 1 / 4 ≤ u.re - |v.im| → ‖F u v‖ ^ 2 ≤ B)
    (hreal : ∀ x ∈ Icc (1 / 2 : ℝ) (2049 / 2), ∀ y ∈ Icc (-512 : ℝ) 512,
      ‖F (x : ℂ) (y : ℂ)‖ ^ 2 ≤ B * ε ^ (2 : ℝ))
    {u v : ℂ} (hu : 1 ≤ u.re) (hu' : u.re ≤ 2) (hui : |u.im| ≤ 256)
    (hvr : |v.re| ≤ 256) (hvi : |v.im| ≤ 1 / 2) :
    ‖F u v‖ ^ 2 ≤ B * ε ^ (1 / 131072 : ℝ) := by
  apply second_continuation (hFv u) hB hε hε1
    (fun v _ hvi => hglobal u v (by linarith)) ?_ hvr hvi
  intro y hy
  apply first_continuation (hFu (y : ℂ)) hB hε hε1
    (fun z hz _ _ => hglobal z (y : ℂ) (by simpa using (show (1 : ℝ) / 4 ≤ z.re by linarith)))
    (fun x hx => hreal x hx y hy) hu hu' hui

theorem complex_speed_bound {F : ℂ → ℂ → E} {ε : ℝ}
    (hFu : ∀ v, Differentiable ℂ (fun u => F u v))
    (hFv : ∀ u, Differentiable ℂ (F u)) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hglobal : ∀ u v : ℂ, 1 / 4 ≤ u.re - |v.im| →
      ‖F u v‖ ^ 2 ≤ 2 ^ 20 / ε ^ 4)
    (hreal : ∀ x ∈ Icc (1 / 2 : ℝ) (2049 / 2), ∀ y ∈ Icc (-512 : ℝ) 512,
      ‖F (x : ℂ) (y : ℂ)‖ ^ 2 ≤ 2 ^ 20 / ε ^ 2)
    {u v : ℂ} (hu : 1 ≤ u.re) (hu' : u.re ≤ 2) (hui : |u.im| ≤ 256)
    (hvr : |v.re| ≤ 256) (hvi : |v.im| ≤ 1 / 2) :
    ε ^ 4 * ‖F u v‖ ^ 2 ≤ 2 ^ 20 * ε ^ (1 / 131072 : ℝ) := by
  have h := two_rectangle_continuation hFu hFv (B := 2 ^ 20 / ε ^ 4)
    (by positivity) hε hε1 hglobal (fun x hx y hy => ?_) hu hu' hui hvr hvi
  · have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ ε ^ 4 by positivity)
    convert! hm using 1
    field_simp [ne_of_gt hε]
  · convert! hreal x hx y hy using 1
    rw [Real.rpow_two]
    field_simp [ne_of_gt hε]

end ToeplitzSOS.Negative.Analytic
