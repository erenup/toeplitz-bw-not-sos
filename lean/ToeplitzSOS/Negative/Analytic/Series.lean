import ToeplitzSOS.Negative.Analytic.Tails
import Mathlib
import ToeplitzSOS.Negative.Baseline

/-! # Generating series for the concrete baseline kernels -/

namespace ToeplitzSOS.Negative.Analytic
noncomputable section
set_option maxHeartbeats 300000

/-- The two-index minimum-kernel term. -/
def minSeriesTerm (a b : ℂ) (p : ℕ × ℕ) : ℂ :=
  (min (p.1 + 1) (p.2 + 1) : ℕ) * a ^ p.1 * b ^ p.2

/-- Absolute convergence of the double minimum series inside the unit bidisk. -/
theorem summable_minSeriesTerm {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (minSeriesTerm a b) := by
  have h1 := (hasSum_weighted_geometric (norm_nonneg a) ha).summable
  have h2 := (hasSum_weighted_geometric (norm_nonneg b) hb).summable
  have h := h1.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => by positivity)
  apply h.of_norm_bounded
  intro p
  have hc : ((min (p.1 + 1) (p.2 + 1) : ℕ) : ℝ) ≤ ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) := by
    have hmin : ((min (p.1 + 1) (p.2 + 1) : ℕ) : ℝ) ≤ (p.1 : ℝ) + 1 := by
      exact_mod_cast min_le_left (p.1 + 1) (p.2 + 1)
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p.1) (Nat.cast_nonneg (α := ℝ) p.2)]
  simp only [minSeriesTerm, norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) * ‖a‖ ^ p.1 * ‖b‖ ^ p.2 := by gcongr
    _ = _ := by ring

private theorem double_tsum_split (f : ℕ × ℕ → ℂ) (hf : Summable f) :
    (∑' p, f p) = (∑' q, f (0, q)) + (∑' p, f (p + 1, 0)) +
      ∑' p, ∑' q, f (p + 1, q + 1) := by
  rw [hf.tsum_prod, hf.prod.tsum_eq_zero_add]
  have hrow : Summable (fun p : ℕ => f (p + 1, 0)) :=
    hf.comp_injective (by intro p q hpq; simpa using congrArg Prod.fst hpq)
  have hquad : Summable (fun p : ℕ × ℕ => f (p.1 + 1, p.2 + 1)) :=
    hf.comp_injective (by
      intro p q hpq
      apply Prod.ext
      · simpa using congrArg Prod.fst hpq
      · simpa using congrArg Prod.snd hpq)
  have he (p : ℕ) : (∑' q, f (p + 1, q)) = f (p + 1, 0) + ∑' q, f (p + 1, q + 1) :=
    (hf.prod_factor (p + 1)).tsum_eq_zero_add
  simp_rw [he]
  rw [hrow.tsum_add hquad.prod]
  ring

/-- The absolutely convergent double minimum series in closed form. -/
theorem hasSum_minSeriesTerm {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (minSeriesTerm a b) (1 / ((1 - a) * (1 - b) * (1 - a * b))) := by
  have hf := summable_minSeriesTerm ha hb
  have hA : 1 - a ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h, norm_one] at ha; exact lt_irrefl _ ha)
  have hB : 1 - b ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h, norm_one] at hb; exact lt_irrefl _ hb)
  have hab : ‖a * b‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b]
  have hAB : 1 - a * b ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h, norm_one] at hab; exact lt_irrefl _ hab)
  have hgeom : Summable (fun p : ℕ × ℕ => a ^ p.1 * b ^ p.2) :=
    summable_mul_of_summable_norm
      (by simpa only [norm_pow] using (hasSum_geometric_of_lt_one (norm_nonneg a) ha).summable)
      (by simpa only [norm_pow] using (hasSum_geometric_of_lt_one (norm_nonneg b) hb).summable)
  have hrec (p q : ℕ) : minSeriesTerm a b (p + 1, q + 1) =
      a * b * (minSeriesTerm a b (p, q) + a ^ p * b ^ q) := by
    have hm : min (p + 1 + 1) (q + 1 + 1) = min (p + 1) (q + 1) + 1 := by omega
    simp only [minSeriesTerm, hm, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have h := double_tsum_split (minSeriesTerm a b) hf
  have hzero : (∑' q, minSeriesTerm a b (0, q)) = (1 - b)⁻¹ := by
    simpa [minSeriesTerm] using tsum_geometric_of_norm_lt_one hb
  have hrow : (∑' p, minSeriesTerm a b (p + 1, 0)) = a * (1 - a)⁻¹ := by
    have ht (p : ℕ) : minSeriesTerm a b (p + 1, 0) = a ^ p * a := by
      have hm : min (p + 1 + 1) (0 + 1) = 1 := by omega
      simp only [minSeriesTerm, hm, Nat.cast_one, one_mul, pow_succ, pow_zero, mul_one]
    simp_rw [ht, tsum_mul_right, tsum_geometric_of_norm_lt_one ha]
    ring
  rw [hzero, hrow] at h
  simp_rw [hrec, tsum_mul_left] at h
  have hadd : (∑' p, ∑' q, (minSeriesTerm a b (p, q) + a ^ p * b ^ q)) =
      (∑' p, minSeriesTerm a b p) + (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [← (hf.add hgeom).tsum_prod, hf.tsum_add hgeom, hgeom.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right, tsum_geometric_of_norm_lt_one ha,
      tsum_geometric_of_norm_lt_one hb]
  rw [hadd] at h
  apply hf.hasSum_iff.mpr
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hA hB) hAB)).mpr
  field_simp [hA, hB] at h
  linear_combination h

/-- Products of two strict disk points are strict disk points. -/
theorem norm_mul_lt_one {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

/-- A strict disk point cannot make its geometric denominator vanish. -/
theorem one_sub_ne_zero_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 :=
  sub_ne_zero.mpr (by intro h; rw [← h, norm_one] at ha; exact lt_irrefl _ ha)

/-- The one-dimensional positive-gap feature. -/
def gapFeature (x y z w : ℂ) (g : ℕ) : ℂ :=
  (y ^ (g + 1) - x ^ (g + 1)) * (w ^ (g + 1) - z ^ (g + 1))

/-- The positive-gap feature is a difference of four geometric series. -/
theorem hasSum_gapFeature {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (gapFeature x y z w)
      (y * w / (1 - y * w) - y * z / (1 - y * z) - x * w / (1 - x * w) +
        x * z / (1 - x * z)) := by
  have hs {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
      HasSum (fun g : ℕ => (a * b) ^ (g + 1)) (a * b / (1 - a * b)) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one (norm_mul_lt_one ha hb)).mul_left (a * b)
  convert! ((hs hy hw).sub (hs hy hz)).sub (hs hx hw) |>.add (hs hx hz) using 1
  funext g
  simp only [gapFeature, mul_pow]
  ring

/-- The infinite same-gap pure-cross summand. Depths are `p,p+g+1,r,r+g+1`. -/
def gapKernelTerm (x y z w : ℂ) (i : (ℕ × ℕ) × ℕ) : ℂ :=
  -2 * minSeriesTerm (x * y) (z * w) i.1 * gapFeature x y z w i.2

/-- The same-gap generating kernel in (5). -/
theorem hasSum_gapKernelTerm {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (gapKernelTerm x y z w) (referenceQ x y z w - referenceD x y z w) := by
  have hm := hasSum_minSeriesTerm (norm_mul_lt_one hx hy) (norm_mul_lt_one hz hw)
  have hg := hasSum_gapFeature hx hy hz hw
  have h := hm.mul hg (summable_mul_of_summable_norm hm.summable.norm hg.summable.norm)
  have hxy := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hx hy)
  have hxz := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hx hz)
  have hxw := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hx hw)
  have hyz := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hy hz)
  have hyw := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hy hw)
  have hzw := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hz hw)
  have hxyzw := one_sub_ne_zero_of_norm_lt_one
    (norm_mul_lt_one (norm_mul_lt_one hx hy) (norm_mul_lt_one hz hw))
  have htotal : 1 - x * w * y * z ≠ 0 := by
    convert! hxyzw using 1
    ring
  convert! h.mul_left (-2) using 1
  · funext i
    simp only [gapKernelTerm]
    ring
  · simp only [referenceQ, factorA, factorB, factorC]
    field_simp [hxy, hxz, hxw, hyz, hyw, hzw, hxyzw, htotal, mul_comm, mul_left_comm, mul_assoc]
    ring

/-- Complex weighted geometric series. -/
theorem hasSum_complex_weighted {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * a ^ n) ((1 - a)⁻¹ ^ 2) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one ha).add
    (hasSum_geometric_of_norm_lt_one ha)
  convert! h using 1
  · funext n; ring
  · field_simp [one_sub_ne_zero_of_norm_lt_one ha]
    ring

/-- Product of two weighted geometric series. -/
theorem hasSum_pair_weighted {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun p : ℕ × ℕ => ((p.1 : ℂ) + 1) * ((p.2 : ℂ) + 1) *
      a ^ p.1 * b ^ p.2) (((1 - a) * (1 - b))⁻¹ ^ 2) := by
  have h1 := hasSum_complex_weighted ha
  have h2 := hasSum_complex_weighted hb
  have hs := summable_mul_of_summable_norm h1.summable.norm h2.summable.norm
  have h := h1.mul h2 hs
  convert! h using 1
  · funext p; ring
  · simp only [mul_inv_rev, mul_pow]; ring

/-- Symmetry converts a zero-diagonal double series to its strict upper half. -/
theorem hasSum_strict_upper {f : ℕ × ℕ → ℂ} {R : ℂ} (hf : HasSum f R)
    (hsym : ∀ p q, f (p, q) = f (q, p)) (hdiag : ∀ p, f (p, p) = 0) :
    HasSum (fun p => if p.1 < p.2 then 2 * f p else 0) R := by
  classical
  let u : ℕ × ℕ → ℂ := fun p => if p.1 < p.2 then f p else 0
  have hu : Summable u := by
    apply hf.summable.norm.of_norm_bounded
    intro p
    by_cases h : p.1 < p.2 <;> simp [u, h]
  have hv : Summable (fun p : ℕ × ℕ => u (p.2, p.1)) :=
    hu.comp_injective (Equiv.prodComm ℕ ℕ).injective
  have he (p : ℕ × ℕ) : f p = u p + u (p.2, p.1) := by
    rcases p with ⟨p,q⟩
    rcases lt_trichotomy p q with hpq | hpq | hpq
    · simp [u, hpq, not_lt.mpr hpq.le]
    · subst q; simp [u, hdiag]
    · simp [u, hpq, not_lt.mpr hpq.le, hsym]
  have ht : (∑' p : ℕ × ℕ, u (p.2, p.1)) = ∑' p, u p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq u
  have hR : R = 2 * ∑' p, u p := by
    rw [← hf.tsum_eq]
    simp_rw [he]
    rw [hu.tsum_add hv, ht]
    ring
  rw [hR]
  convert! hu.hasSum.mul_left 2 using 1
  funext p
  by_cases h : p.1 < p.2 <;> simp [u, h]

/-- Natural-depth version of the alternating pure feature. -/
def natPureFeature (p : ℕ × ℕ) (x y : ℂ) : ℂ :=
  x ^ p.1 * y ^ p.2 - x ^ p.2 * y ^ p.1

/-- Pure diagonal series, indexed by all pairs and zero outside the strict upper half. -/
def diagonalSeriesTerm (x y z w : ℂ) (p : ℕ × ℕ) : ℂ :=
  if p.1 < p.2 then 2 * ((p.1 : ℂ) + 1) * ((p.2 : ℂ) + 1) *
    natPureFeature p x y * natPureFeature p z w else 0

/-- The increasing-pair pure diagonal has the rational reference in (5). -/
theorem hasSum_diagonalSeriesTerm {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (diagonalSeriesTerm x y z w) (referenceD x y z w) := by
  let f : ℕ × ℕ → ℂ := fun p => ((p.1 : ℂ) + 1) * ((p.2 : ℂ) + 1) *
    natPureFeature p x y * natPureFeature p z w
  have h1 := hasSum_pair_weighted (norm_mul_lt_one hx hz) (norm_mul_lt_one hy hw)
  have h2 := hasSum_pair_weighted (norm_mul_lt_one hx hw) (norm_mul_lt_one hy hz)
  have h3 := hasSum_pair_weighted (norm_mul_lt_one hy hz) (norm_mul_lt_one hx hw)
  have h4 := hasSum_pair_weighted (norm_mul_lt_one hy hw) (norm_mul_lt_one hx hz)
  have hf : HasSum f (referenceD x y z w) := by
    convert! ((h1.sub h2).sub h3).add h4 using 1
    · funext p
      simp only [f, natPureFeature, mul_pow]
      ring
    · simp only [referenceD, factorA, factorB, mul_comm]
      ring
  convert! hasSum_strict_upper hf
    (by intro p q; simp only [f, natPureFeature]; ring)
    (by intro p; simp [f, natPureFeature]) using 1
  funext p
  by_cases h : p.1 < p.2 <;> simp [diagonalSeriesTerm, f, h, mul_assoc]

/-- Depth embedding of the positive-gap parametrization. -/
def gapDepth (i : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((i.1.1, i.1.1 + i.2 + 1), (i.1.2, i.1.2 + i.2 + 1))

/-- A same-gap tuple uniquely determines its two starting depths and positive gap. -/
theorem gapDepth_injective : Function.Injective gapDepth := by
  rintro ⟨⟨p,r⟩,g⟩ ⟨⟨p',r'⟩,g'⟩ h
  simp only [gapDepth, Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  omega

/-- The literal natural-depth same-gap term. -/
def crossSeriesTerm (x y z w : ℂ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  if p.1.1 < p.1.2 ∧ p.2.1 < p.2.2 ∧ p.1.2 - p.1.1 = p.2.2 - p.2.1 then
    -2 * (min (p.1.1 + 1) (p.2.1 + 1) : ℕ) *
      natPureFeature p.1 x y * natPureFeature p.2 z w else 0

/-- Factor an increasing-pair feature into its starting monomial and gap difference. -/
theorem natPureFeature_gap (x y : ℂ) (p g : ℕ) :
    natPureFeature (p, p + g + 1) x y = (x * y) ^ p * (y ^ (g + 1) - x ^ (g + 1)) := by
  simp only [natPureFeature, show p + g + 1 = p + (g + 1) by omega, pow_add, mul_pow]
  ring

/-- The same-gap series on the literal four-depth index space. -/
theorem hasSum_crossSeriesTerm {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (crossSeriesTerm x y z w) (referenceQ x y z w - referenceD x y z w) := by
  apply (gapDepth_injective.hasSum_iff ?_).mp
  · convert! hasSum_gapKernelTerm hx hy hz hw using 1
    funext i
    have hc : i.1.1 < i.1.1 + i.2 + 1 ∧ i.1.2 < i.1.2 + i.2 + 1 ∧
        i.1.1 + i.2 + 1 - i.1.1 = i.1.2 + i.2 + 1 - i.1.2 := by omega
    simp only [Function.comp_apply, crossSeriesTerm, gapDepth, hc, and_self, ite_true,
      natPureFeature_gap, gapKernelTerm, minSeriesTerm, gapFeature]
    ring
  · intro p hp
    have hc : ¬ (p.1.1 < p.1.2 ∧ p.2.1 < p.2.2 ∧
        p.1.2 - p.1.1 = p.2.2 - p.2.1) := by
      intro h
      apply hp
      refine ⟨((p.1.1,p.2.1),p.1.2-p.1.1-1), ?_⟩
      apply Prod.ext <;> apply Prod.ext <;> dsimp [gapDepth] <;> omega
    simp [crossSeriesTerm, hc]

/-- Equal-total minimum coefficient. -/
def totalMinimum (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  min (min (p.1.1 + 1) (p.1.2 + 1)) (min (p.2.1 + 1) (p.2.2 + 1))

/-- Equal-total part of the mixed kernel, before its coefficient `-2`. -/
def totalSeriesTerm (x y z w : ℂ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  if p.1.1 + p.1.2 = p.2.1 + p.2.2 then
    (totalMinimum p : ℂ) * x ^ p.1.1 * y ^ p.1.2 * z ^ p.2.1 * w ^ p.2.2 else 0

/-- The nonnegative displacement cone, including its common boundary. -/
def totalDepthPlus (i : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((i.1.1, i.1.2 + i.2), (i.1.1 + i.2, i.1.2))

/-- The negative displacement cone, excluding the common boundary. -/
def totalDepthMinus (i : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((i.1.1 + i.2 + 1, i.1.2), (i.1.1, i.1.2 + i.2 + 1))

/-- The nonnegative displacement parametrization has no repeated depth tuples. -/
theorem totalDepthPlus_injective : Function.Injective totalDepthPlus := by
  rintro ⟨⟨a,b⟩,d⟩ ⟨⟨a',b'⟩,d'⟩ h
  simp only [totalDepthPlus, Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  omega

/-- The strict negative displacement parametrization has no repeated depth tuples. -/
theorem totalDepthMinus_injective : Function.Injective totalDepthMinus := by
  rintro ⟨⟨a,b⟩,d⟩ ⟨⟨a',b'⟩,d'⟩ h
  simp only [totalDepthMinus, Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  omega

/-- Closed series on the nonnegative displacement cone. -/
theorem hasSum_totalSeriesPlus {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun p => if p.1.1 ≤ p.2.1 then totalSeriesTerm x y z w p else 0)
      (1 / ((1 - x*z)*(1 - y*w)*(1 - x*z*(y*w))) * (1 - y*z)⁻¹) := by
  have hm := hasSum_minSeriesTerm (norm_mul_lt_one hx hz) (norm_mul_lt_one hy hw)
  have hg := hasSum_geometric_of_norm_lt_one (norm_mul_lt_one hy hz)
  have hseries := hm.mul hg (summable_mul_of_summable_norm hm.summable.norm hg.summable.norm)
  apply (totalDepthPlus_injective.hasSum_iff ?_).mp
  · apply hseries.congr_fun
    intro i
    have hm : totalMinimum (totalDepthPlus i) = min (i.1.1 + 1) (i.1.2 + 1) := by
      dsimp [totalMinimum, totalDepthPlus]; omega
    have hle : i.1.1 ≤ i.1.1 + i.2 := by omega
    have ht : i.1.1 + (i.1.2 + i.2) = i.1.1 + i.2 + i.1.2 := by omega
    simp only [Function.comp_apply, totalDepthPlus, hle, ite_true, totalSeriesTerm,
      ht, minSeriesTerm, pow_add, mul_pow]
    change (totalMinimum (totalDepthPlus i) : ℂ) * _ * _ * _ * _ = _
    rw [hm]
    ring
  · intro p hp
    by_cases hle : p.1.1 ≤ p.2.1
    · have ht : p.1.1 + p.1.2 ≠ p.2.1 + p.2.2 := by
        intro ht
        apply hp
        refine ⟨((p.1.1,p.2.2),p.2.1-p.1.1), ?_⟩
        apply Prod.ext <;> apply Prod.ext <;> dsimp [totalDepthPlus] <;> omega
      simp [hle, totalSeriesTerm, ht]
    · simp [hle]

/-- Closed series on the strict negative displacement cone. -/
theorem hasSum_totalSeriesMinus {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (fun p => if p.2.1 < p.1.1 then totalSeriesTerm x y z w p else 0)
      (1 / ((1 - x*z)*(1 - y*w)*(1 - x*z*(y*w))) * (x*w/(1 - x*w))) := by
  have hm := hasSum_minSeriesTerm (norm_mul_lt_one hx hz) (norm_mul_lt_one hy hw)
  have hg : HasSum (fun d : ℕ => (x*w)^d * (x*w)) (x*w/(1-x*w)) := by
    have h := (hasSum_geometric_of_norm_lt_one (norm_mul_lt_one hx hw)).mul_right (x*w)
    convert! h using 1
    simp only [div_eq_mul_inv]; ring
  have hs := summable_mul_of_summable_norm
    (f := minSeriesTerm (x*z) (y*w)) (g := fun d : ℕ => (x*w)^d * (x*w))
    hm.summable.norm hg.summable.norm
  have hseries := hm.mul hg hs
  apply (totalDepthMinus_injective.hasSum_iff ?_).mp
  · apply hseries.congr_fun
    intro i
    have hm : totalMinimum (totalDepthMinus i) = min (i.1.1 + 1) (i.1.2 + 1) := by
      dsimp [totalMinimum, totalDepthMinus]; omega
    have hlt : i.1.1 < i.1.1 + i.2 + 1 := by omega
    have ht : i.1.1 + i.2 + 1 + i.1.2 = i.1.1 + (i.1.2 + i.2 + 1) := by omega
    simp only [Function.comp_apply, totalDepthMinus, hlt, ite_true, totalSeriesTerm,
      ht, minSeriesTerm]
    change (totalMinimum (totalDepthMinus i) : ℂ) * _ * _ * _ * _ = _
    rw [hm]
    simp only [show i.1.1 + i.2 + 1 = i.1.1 + (i.2+1) by omega,
      show i.1.2 + i.2 + 1 = i.1.2 + (i.2+1) by omega, pow_add, mul_pow]
    ring
  · intro p hp
    by_cases hlt : p.2.1 < p.1.1
    · have ht : p.1.1 + p.1.2 ≠ p.2.1 + p.2.2 := by
        intro ht
        apply hp
        refine ⟨((p.2.1,p.1.2),p.1.1-p.2.1-1), ?_⟩
        apply Prod.ext <;> apply Prod.ext <;> dsimp [totalDepthMinus] <;> omega
      simp [hlt, totalSeriesTerm, ht]
    · simp [hlt]

/-- The complete equal-total minimum series is the product `1/(A B)`. -/
theorem hasSum_totalSeriesTerm {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (totalSeriesTerm x y z w) (factorA x y z w * factorB x y z w)⁻¹ := by
  have hp := hasSum_totalSeriesPlus hx hy hz hw
  have hm := hasSum_totalSeriesMinus hx hy hz hw
  have hxz := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hx hz)
  have hyw := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hy hw)
  have hxw := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hx hw)
  have hyz := one_sub_ne_zero_of_norm_lt_one (norm_mul_lt_one hy hz)
  have ht := one_sub_ne_zero_of_norm_lt_one
    (norm_mul_lt_one (norm_mul_lt_one hx hz) (norm_mul_lt_one hy hw))
  have hseries := hp.add hm
  convert! hseries using 1
  · funext p
    by_cases h : p.1.1 ≤ p.2.1
    · simp [h, not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
  · have ht' : 1 - z*y*x*w ≠ 0 := by
      convert! ht using 1
      ring
    have hyz' : 1 - z*y ≠ 0 := by simpa only [mul_comm] using hyz
    have ht'' : 1 - x*w*z*y ≠ 0 := by
      convert! ht using 1
      ring
    simp only [factorA, factorB]
    field_simp [hxz, hyw, hxw, hyz, ht, ht', ht'', hyz', mul_comm, mul_left_comm, mul_assoc]
    linear_combination -(mul_inv_cancel₀ ht'')

/-- Repeated-pair depth embedding. -/
def diagonalDepth (p : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) := (p,p)

/-- Repeating a pair preserves its index. -/
theorem diagonalDepth_injective : Function.Injective diagonalDepth := by
  intro p q h
  exact congrArg Prod.fst h

/-- Diagonal part of the full mixed tensor. -/
def mixedDiagonalSeriesTerm (x y z w : ℂ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  if p.1 = p.2 then 2 * ((p.1.1 : ℂ)+1) * ((p.1.2 : ℂ)+1) *
    x^p.1.1 * y^p.1.2 * z^p.2.1 * w^p.2.2 else 0

/-- The full mixed baseline term. -/
def mixedSeriesTerm (x y z w : ℂ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  mixedDiagonalSeriesTerm x y z w p - 2 * totalSeriesTerm x y z w p

/-- The mixed diagonal sums to twice the squared reciprocal of the first factor. -/
theorem hasSum_mixedDiagonalSeriesTerm {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (mixedDiagonalSeriesTerm x y z w) (2 * (factorA x y z w)⁻¹ ^ 2) := by
  have h := (hasSum_pair_weighted (norm_mul_lt_one hx hz) (norm_mul_lt_one hy hw)).mul_left 2
  apply (diagonalDepth_injective.hasSum_iff ?_).mp
  · convert! h using 1
    funext p
    simp only [Function.comp_apply, diagonalDepth, mixedDiagonalSeriesTerm, ite_true, mul_pow]
    ring
  · intro p hp
    have hne : p.1 ≠ p.2 := by
      intro h
      apply hp
      exact ⟨p.1, Prod.ext rfl h⟩
    simp [mixedDiagonalSeriesTerm, hne]

/-- The mixed baseline series has precisely the reference in (5). -/
theorem hasSum_mixedSeriesTerm {x y z w : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    HasSum (mixedSeriesTerm x y z w) (referenceB x y z w) := by
  have hd := hasSum_mixedDiagonalSeriesTerm hx hy hz hw
  have ht := (hasSum_totalSeriesTerm hx hy hz hw).mul_left 2
  convert! hd.sub ht using 1
  simp only [referenceB]
  ring

end
end ToeplitzSOS.Negative.Analytic
