import ToeplitzSOS.Negative.Analytic.Tails
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Elementary conjugate-node radius and phase bounds -/

namespace ToeplitzSOS.Negative.Analytic

/-- The phase in the real rectangle stays uniformly away from a sine zero. -/
theorem cos_sq_lower {t : ℝ} (ht : |t| ≤ 1) : (1 : ℝ) / 4 ≤ Real.cos t ^ 2 := by
  have hs : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, (sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)).mpr ht]
  have hc : 1 / 2 ≤ Real.cos t := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  nlinarith

/-- Uniform radius bounds throughout the long real rectangle. -/
theorem conjugate_radius_bounds {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ (2 : ℝ)⁻¹ ^ 16)
    (hu : 1 / 2 ≤ u) (hu' : u ≤ 2049 / 2) :
    1 / 2 ≤ Real.exp (-(2 * ε * u)) ∧
      ε * u ≤ 1 - Real.exp (-(2 * ε * u)) ∧
      ε / 2 ≤ 1 - Real.exp (-(2 * ε * u)) := by
  have ht : 0 ≤ 2 * ε * u := by positivity
  have htu : 2 * ε * u ≤ 1 / 2 := by
    have hh := mul_le_mul hε1 hu' (by linarith : (0 : ℝ) ≤ u) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 16)
    norm_num at hh
    nlinarith
  have hl := Real.one_sub_le_exp_neg (2 * ε * u)
  have hd := half_le_one_sub_exp_neg ht (by linarith : 2 * ε * u ≤ 1)
  have hmul := mul_le_mul_of_nonneg_left hu hε.le
  constructor
  · linarith
  constructor <;> nlinarith

/-- The phase square in (11), where sin(phi) = cos(ε v). -/
theorem conjugate_phase_bound {ε v : ℝ} (hε : 0 < ε) (hε1 : ε ≤ (2 : ℝ)⁻¹ ^ 16)
    (hv : |v| ≤ 512) : (1 : ℝ) / 4 ≤ Real.cos (ε * v) ^ 2 := by
  apply cos_sq_lower
  rw [abs_mul, abs_of_pos hε]
  have h := mul_le_mul hε1 hv (abs_nonneg v) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 16)
  norm_num at h
  linarith

/-- The rational conjugate reference kernel is only second order in ε.
`a` is rho and `s` is sin(phi)^2; every hypothesis is supplied by the
preceding radius and phase lemmas in the comparison rectangle. -/
theorem conjugate_reference_bound {ε a s : ℝ} (hε : 0 < ε)
    (ha : 1 / 2 ≤ a) (hs : 1 / 4 ≤ s) (hrad : ε / 2 ≤ 1 - a) :
    8 * a * s / ((1 - a) ^ 2 * ((1 - a) ^ 2 + 4 * a * s) ^ 2) ≤ 16 / ε ^ 2 := by
  have has : 1 / 8 ≤ a * s := by nlinarith [mul_le_mul ha hs (by norm_num) (by linarith : 0 ≤ a)]
  have hr : 0 < 1 - a := by linarith
  have hd : 0 < (1 - a) ^ 2 + 4 * a * s := by positivity
  have h1 : 4 * a * s ≤ (1 - a) ^ 2 + 4 * a * s := by nlinarith [sq_nonneg (1 - a)]
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * a * s) h1 2
  have h3 : ε ^ 2 / 4 ≤ (1 - a) ^ 2 := by nlinarith [sq_nonneg (1 - a - ε / 2)]
  have h4 := mul_le_mul h3 h2 (by positivity : 0 ≤ (4 * a * s) ^ 2) (sq_nonneg (1 - a))
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 : a * s ≤ 8 * (a * s) ^ 2 := by nlinarith
  have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg ε)
  nlinarith

/-- Quantitative vanishing-factor control using the proved complex exponential
remainder. This is the estimate required before taking reciprocal factors. -/
theorem exponential_factor_error {z : ℂ} (hz : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖(1 - Complex.exp (-z)) / z - 1‖ ≤ ‖z‖ := by
  have he := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by simpa using hz1)
  have hid : (1 - Complex.exp (-z)) / z - 1 = -(Complex.exp (-z) - 1 - -z) / z := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg]
  apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
  simpa [norm_neg, pow_two] using he

/-- The first speed-parametrized evaluation node. -/
noncomputable def speedNode (ε : ℝ) (u v : ℂ) : ℂ :=
  Complex.I * Complex.exp (-(ε : ℂ) * (u + Complex.I * v))

/-- The second evaluation node. -/
noncomputable def speedPartner (ε : ℝ) (u v : ℂ) : ℂ :=
  -Complex.I * Complex.exp (-(ε : ℂ) * (u - Complex.I * v))

/-- The first node radius in complex speed coordinates. -/
theorem speedNode_norm (ε : ℝ) (u v : ℂ) :
    ‖speedNode ε u v‖ = Real.exp (-ε * (u.re - v.im)) := by
  simp [speedNode, Complex.norm_exp, sub_eq_add_neg]

/-- The partner node radius in complex speed coordinates. -/
theorem speedPartner_norm (ε : ℝ) (u v : ℂ) :
    ‖speedPartner ε u v‖ = Real.exp (-ε * (u.re + v.im)) := by
  simp [speedPartner, Complex.norm_exp]

/-- On the real slice the two nodes are exactly conjugate. -/
theorem speedPartner_eq_conj (ε u v : ℝ) :
    speedPartner ε (u : ℂ) (v : ℂ) = star (speedNode ε (u : ℂ) (v : ℂ)) := by
  simp [speedPartner, speedNode, map_mul, ← Complex.exp_conj, sub_eq_add_neg]

/-- Both nodes remain in the same fixed radial disk throughout the global domain. -/
theorem speed_nodes_radial {ε : ℝ} (hε : 0 ≤ ε) {u v : ℂ}
    (huv : 1 / 4 ≤ u.re - |v.im|) :
    ‖speedNode ε u v‖ ≤ Real.exp (-ε / 4) ∧
      ‖speedPartner ε u v‖ ≤ Real.exp (-ε / 4) := by
  rw [speedNode_norm, speedPartner_norm]
  constructor <;> apply Real.exp_le_exp.mpr
  · nlinarith [le_abs_self v.im]
  · nlinarith [neg_abs_le v.im]

/-- The fourth-order pure majorant becomes the uniform bound (16). -/
theorem pure_majorant_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x y : ℂ} (hx : ‖x‖ ≤ Real.exp (-ε / 4)) (hy : ‖y‖ ≤ Real.exp (-ε / 4)) :
    8 / ((1 - ‖x‖ ^ 2) ^ 2 * (1 - ‖y‖ ^ 2) ^ 2) ≤ 2 ^ 20 / ε ^ 4 := by
  have hexp : Real.exp (-ε / 4) ^ 2 = Real.exp (-ε / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hrad := half_le_one_sub_exp_neg (t := ε / 2) (by positivity) (by linarith)
  have hxx := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hyy := pow_le_pow_left₀ (norm_nonneg y) hy 2
  rw [hexp] at hxx hyy
  simp only [neg_div] at hxx hyy
  have hdx : ε / 4 ≤ 1 - ‖x‖ ^ 2 := by linarith
  have hdy : ε / 4 ≤ 1 - ‖y‖ ^ 2 := by linarith
  have hxpos : 0 < 1 - ‖x‖ ^ 2 := by linarith
  have hypos : 0 < 1 - ‖y‖ ^ 2 := by linarith
  calc
    _ ≤ 8 / ((ε / 4) ^ 2 * (ε / 4) ^ 2) := by gcongr
    _ = 2 ^ 11 / ε ^ 4 := by field_simp; ring
    _ ≤ _ := by gcongr <;> norm_num

/-- Realigned pairs of witness nodes land in the complete target speed region. -/
theorem witness_speed_region {r t j k : ℝ}
    (hr : 1 ≤ r) (hr' : r ≤ 2) (ht : 1 ≤ t) (ht' : t ≤ 2)
    (hj : |j| ≤ 256) (hk : |k| ≤ 256) :
    let u : ℂ := ((r + t) / 2 : ℝ) + ((j - k) / 2 : ℝ) * Complex.I
    let v : ℂ := ((j + k) / 2 : ℝ) - ((r - t) / 2 : ℝ) * Complex.I
    1 ≤ u.re ∧ u.re ≤ 2 ∧ |u.im| ≤ 256 ∧ |v.re| ≤ 256 ∧ |v.im| ≤ 1 / 2 := by
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero,
    zero_sub, abs_neg]
  rcases abs_le.mp hj with ⟨hj1, hj2⟩
  rcases abs_le.mp hk with ⟨hk1, hk2⟩
  refine ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The coordinates used for a realigned entry recover its two original speeds. -/
theorem witness_speed_identity (r t j k : ℝ) :
    let u : ℂ := ((r + t) / 2 : ℝ) + ((j - k) / 2 : ℝ) * Complex.I
    let v : ℂ := ((j + k) / 2 : ℝ) - ((r - t) / 2 : ℝ) * Complex.I
    u + Complex.I * v = r + j * Complex.I ∧
      u - Complex.I * v = t - k * Complex.I := by
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_ofNat]
  constructor <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end ToeplitzSOS.Negative.Analytic
