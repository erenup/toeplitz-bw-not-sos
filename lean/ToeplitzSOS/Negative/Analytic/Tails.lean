import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Weighted geometric tails used in (12)–(13)

Indices are grouped into two pairs only to expose the product of four
absolutely summable scalar series. Bounds apply to arbitrary finite subsets.
-/

open Finset
namespace ToeplitzSOS.Negative.Analytic

/-- A convenient real exponential lower bound for radial denominators. -/
theorem half_le_one_sub_exp_neg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have he := Real.add_one_le_exp t
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 - t / 2 by linarith)
  have hi : Real.exp (-t) ≤ 1 - t / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos t)]
    nlinarith [mul_nonneg ht (show 0 ≤ 1 - t by linarith)]
  linarith

/-- The exact scalar series behind every four-index estimate. -/
theorem hasSum_weighted_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n) (1 / (1 - q) ^ 2) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hq hq1)
  convert! h using 1
  · ext n
    ring
  · field_simp [ne_of_gt (sub_pos.mpr hq1)]
    ring

/-- Four independent nonnegative weighted geometric series. -/
theorem hasSum_four_weighted_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      (((p.1.1 : ℝ) + 1) * q ^ p.1.1 * (((p.1.2 : ℝ) + 1) * q ^ p.1.2)) *
      (((p.2.1 : ℝ) + 1) * q ^ p.2.1 * (((p.2.2 : ℝ) + 1) * q ^ p.2.2)))
      (1 / (1 - q) ^ 8) := by
  have h := hasSum_weighted_geometric hq hq1
  have hn (n : ℕ) : 0 ≤ ((n : ℝ) + 1) * q ^ n := by positivity
  have h2 := h.mul h (h.summable.mul_of_nonneg h.summable hn hn)
  have hn2 (p : ℕ × ℕ) : 0 ≤
      (((p.1 : ℝ) + 1) * q ^ p.1) * (((p.2 : ℝ) + 1) * q ^ p.2) := by positivity
  convert! h2.mul h2 (h2.summable.mul_of_nonneg h2.summable hn2 hn2) using 1
  field_simp [ne_of_gt (sub_pos.mpr hq1)]

/-- The four-index coefficient weight. -/
def depthWeight (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ((p.1.1 : ℝ) + 1) * ((p.1.2 : ℝ) + 1) * ((p.2.1 : ℝ) + 1) * ((p.2.2 : ℝ) + 1)

/-- Total monomial degree. -/
def totalDepth (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := p.1.1 + p.1.2 + p.2.1 + p.2.2

/-- Uniform bound for any finite high-total tail. It is stronger than the
four-way union estimate, and covers a large index as well as vanishing means. -/
theorem weighted_geometric_tail {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (s : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (m : ℕ)
    (hs : ∀ p ∈ s, m ≤ totalDepth p) :
    ∑ p ∈ s, depthWeight p * q ^ (2 * totalDepth p) ≤ q ^ m / (1 - q) ^ 8 := by
  have hw (p : (ℕ × ℕ) × (ℕ × ℕ)) : 0 ≤ depthWeight p := by unfold depthWeight; positivity
  have hsum : ∑ p ∈ s, depthWeight p * q ^ totalDepth p ≤ 1 / (1 - q) ^ 8 := by
    have h := hasSum_four_weighted_geometric hq hq1
    have he (p : (ℕ × ℕ) × (ℕ × ℕ)) :
        depthWeight p * q ^ totalDepth p =
          (((p.1.1 : ℝ) + 1) * q ^ p.1.1 * (((p.1.2 : ℝ) + 1) * q ^ p.1.2)) *
          (((p.2.1 : ℝ) + 1) * q ^ p.2.1 * (((p.2.2 : ℝ) + 1) * q ^ p.2.2)) := by
      simp only [depthWeight, totalDepth, pow_add]
      ring
    simp_rw [he]
    exact sum_le_hasSum s (fun p _ => by positivity) h
  calc
    _ ≤ ∑ p ∈ s, depthWeight p * (q ^ m * q ^ totalDepth p) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hw p)
      rw [← pow_add]
      exact pow_le_pow_of_le_one hq hq1.le (by have := hs p hp; omega)
    _ = q ^ m * ∑ p ∈ s, depthWeight p * q ^ totalDepth p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ q ^ m * (1 / (1 - q) ^ 8) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The exponential form of the uniform finite tail estimate. -/
theorem weighted_exponential_tail {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (s : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (m : ℕ)
    (hs : ∀ p ∈ s, m ≤ totalDepth p) :
    ∑ p ∈ s, depthWeight p * Real.exp (-ε * totalDepth p / 2) ≤
      8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  let q := Real.exp (-ε / 4)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : ε / 8 ≤ 1 - q := by
    have h := half_le_one_sub_exp_neg (t := ε / 4) (by positivity) (by linarith)
    convert! h using 1 <;> norm_num [q, div_div, neg_div]
  have hdpos : 0 < 1 - q := sub_pos.mpr hq1
  have hinv : 1 / (1 - q) ^ 8 ≤ 8 ^ 8 / ε ^ 8 := by
    calc
      _ ≤ 1 / (ε / 8) ^ 8 := by gcongr
      _ = _ := by field_simp
  have he (n : ℕ) : q ^ n = Real.exp (-ε * n / 4) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h := weighted_geometric_tail hq.le hq1 s m hs
  calc
    _ = ∑ p ∈ s, depthWeight p * q ^ (2 * totalDepth p) := by
      apply sum_congr rfl
      intro p _
      rw [he]
      congr 2
      push_cast
      ring
    _ ≤ q ^ m / (1 - q) ^ 8 := h
    _ = (1 / (1 - q) ^ 8) * Real.exp (-ε * m / 4) := by rw [he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le

/-- A general finite complex coefficient tail, uniform in its support size. -/
theorem finite_tail_of_term_bound {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C) (s : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (m : ℕ)
    (hs : ∀ p ∈ s, m ≤ totalDepth p) (term : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ)
    (hterm : ∀ p ∈ s, ‖term p‖ ≤ C * depthWeight p * Real.exp (-ε * totalDepth p / 2)) :
    ‖∑ p ∈ s, term p‖ ≤ C * 8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  calc
    _ ≤ ∑ p ∈ s, ‖term p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, C * (depthWeight p * Real.exp (-ε * totalDepth p / 2)) := by
      apply sum_le_sum
      intro p hp
      simpa only [mul_assoc] using hterm p hp
    _ = C * ∑ p ∈ s, depthWeight p * Real.exp (-ε * totalDepth p / 2) := (mul_sum ..).symm
    _ ≤ C * (8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4)) :=
      mul_le_mul_of_nonneg_left (weighted_exponential_tail hε hε1 s m hs) hC
    _ = _ := by ring

/-- Monomial bound from a coefficient majorant and four radial bounds. -/
theorem kernel_monomial_bound {ε C : ℝ} (hC : 0 ≤ C)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) {a x y z w : ℂ}
    (ha : ‖a‖ ≤ C * depthWeight p)
    (hx : ‖x‖ ≤ Real.exp (-ε / 2)) (hy : ‖y‖ ≤ Real.exp (-ε / 2))
    (hz : ‖z‖ ≤ Real.exp (-ε / 2)) (hw : ‖w‖ ≤ Real.exp (-ε / 2)) :
    ‖a * x ^ p.1.1 * y ^ p.1.2 * z ^ p.2.1 * w ^ p.2.2‖ ≤
      C * depthWeight p * Real.exp (-ε * totalDepth p / 2) := by
  have hweight : 0 ≤ depthWeight p := by unfold depthWeight; positivity
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ C * depthWeight p * Real.exp (-ε / 2) ^ p.1.1 *
        Real.exp (-ε / 2) ^ p.1.2 * Real.exp (-ε / 2) ^ p.2.1 *
        Real.exp (-ε / 2) ^ p.2.2 := by gcongr
    _ = C * depthWeight p * (Real.exp (-ε / 2) ^ p.1.1 *
        Real.exp (-ε / 2) ^ p.1.2 * Real.exp (-ε / 2) ^ p.2.1 *
        Real.exp (-ε / 2) ^ p.2.2) := by ring
    _ = _ := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      simp only [totalDepth, Nat.cast_add]
      ring

/-- Infinite high-total tails satisfy the same bound as finite ones. A reference
kernel may be substituted for the sum after its generating-series identity is proved. -/
theorem infinite_tail_of_term_bound {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C) (m : ℕ) (term : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ)
    (hs : ∀ p, term p ≠ 0 → m ≤ totalDepth p)
    (hterm : ∀ p, ‖term p‖ ≤ C * depthWeight p * Real.exp (-ε * totalDepth p / 2)) :
    ‖∑' p, term p‖ ≤ C * 8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  classical
  by_cases ht : Summable term
  · apply le_of_tendsto' ht.hasSum.norm
    intro s
    have he : ∑ p ∈ s, term p = ∑ p ∈ s.filter (fun p => term p ≠ 0), term p := by
      simp only [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : term p = 0 <;> simp [hp]
    rw [he]
    exact finite_tail_of_term_bound hε hε1 hC _ m
      (fun p hp => hs p (mem_filter.mp hp).2) term (fun p _ => hterm p)
  · rw [tsum_eq_zero_of_not_summable ht, norm_zero]
    positivity

/-- The finite-tail estimate transported along any injective depth indexing. -/
theorem finite_tail_injective {ι : Type*} [Fintype ι] {ε C : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) (m : ℕ)
    (idx : ι → (ℕ × ℕ) × (ℕ × ℕ)) (hi : Function.Injective idx) (term : ι → ℂ)
    (hs : ∀ i, term i ≠ 0 → m ≤ totalDepth (idx i))
    (hterm : ∀ i, ‖term i‖ ≤ C * depthWeight (idx i) * Real.exp (-ε * totalDepth (idx i) / 2)) :
    ‖∑ i, term i‖ ≤ C * 8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  classical
  let s := univ.filter (fun i => term i ≠ 0)
  have he : ∑ i, term i = ∑ i ∈ s, term i := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases ht : term i = 0 <;> simp [ht]
  have hb := weighted_exponential_tail hε hε1 (s.image idx) m
    (by intro p hp; obtain ⟨i, hi', rfl⟩ := mem_image.mp hp; exact hs i (mem_filter.mp hi').2)
  rw [sum_image (by intro i _ j _ hij; exact hi hij)] at hb
  calc
    _ = ‖∑ i ∈ s, term i‖ := congrArg norm he
    _ ≤ ∑ i ∈ s, ‖term i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, C * (depthWeight (idx i) * Real.exp (-ε * totalDepth (idx i) / 2)) := by
      apply sum_le_sum
      intro i _
      simpa only [mul_assoc] using hterm i
    _ = C * ∑ i ∈ s, depthWeight (idx i) * Real.exp (-ε * totalDepth (idx i) / 2) := (mul_sum ..).symm
    _ ≤ C * (8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4)) := mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

/-- A finite principal truncation differs from its proved infinite reference by
an exponentially small tail. `hcover` says every omitted term has high total degree. -/
theorem reference_tail_of_hasSum {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C) (m : ℕ) (term : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) {R : ℂ}
    (hseries : HasSum term R) (s : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hcover : ∀ p, totalDepth p < m → p ∈ s)
    (hterm : ∀ p, ‖term p‖ ≤ C * depthWeight p * Real.exp (-ε * totalDepth p / 2)) :
    ‖(∑ p ∈ s, term p) - R‖ ≤ C * 8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  classical
  let f : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ := fun p => if p ∈ s then term p else 0
  have hf : HasSum f (∑ p ∈ s, term p) := by
    convert! hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) (s := s) (f := f)
      (by intro p hp; simp [f, hp]) using 1
    simp [f]
  have hdiff := hseries.sub hf
  have h := infinite_tail_of_term_bound hε hε1 hC m (fun p => term p - f p)
    (by
      intro p hp
      by_contra hlow
      have hp' := hcover p (Nat.lt_of_not_ge hlow)
      exact hp (by simp [f, hp']))
    (by
      intro p
      by_cases hp : p ∈ s
      · simp only [f, hp, ite_true, sub_self, norm_zero]
        exact (norm_nonneg (term p)).trans (hterm p)
      · simpa [f, hp] using hterm p)
  rw [hdiff.tsum_eq, norm_sub_rev] at h
  exact h

/-- The same infinite-tail estimate for any injective indexing of depth tuples. -/
theorem infinite_tail_injective {ι : Type*} {ε C : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) (m : ℕ)
    (idx : ι → (ℕ × ℕ) × (ℕ × ℕ)) (hi : Function.Injective idx) (term : ι → ℂ)
    (hs : ∀ i, term i ≠ 0 → m ≤ totalDepth (idx i))
    (hterm : ∀ i, ‖term i‖ ≤ C * depthWeight (idx i) * Real.exp (-ε * totalDepth (idx i) / 2)) :
    ‖∑' i, term i‖ ≤ C * 8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  classical
  by_cases ht : Summable term
  · apply le_of_tendsto' ht.hasSum.norm
    intro s
    have h := finite_tail_injective (ι := {i // i ∈ s}) hε hε1 hC m
      (fun i => idx i.1) (hi.comp Subtype.coe_injective) (fun i => term i.1)
      (fun i => hs i.1) (fun i => hterm i.1)
    simpa only [Finset.sum_coe_sort] using h
  · rw [tsum_eq_zero_of_not_summable ht, norm_zero]
    positivity

/-- A reference-series tail with injective depth indexing, useful for same-gap
and equal-total parametrizations of the baseline. -/
theorem reference_tail_injective {ι : Type*} {ε C : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) (m : ℕ)
    (idx : ι → (ℕ × ℕ) × (ℕ × ℕ)) (hi : Function.Injective idx) (term : ι → ℂ)
    {R : ℂ} (hseries : HasSum term R) (s : Finset ι)
    (hcover : ∀ i, totalDepth (idx i) < m → i ∈ s)
    (hterm : ∀ i, ‖term i‖ ≤ C * depthWeight (idx i) * Real.exp (-ε * totalDepth (idx i) / 2)) :
    ‖(∑ i ∈ s, term i) - R‖ ≤ C * 8 ^ 8 / ε ^ 8 * Real.exp (-ε * m / 4) := by
  classical
  let f : ι → ℂ := fun i => if i ∈ s then term i else 0
  have hf : HasSum f (∑ i ∈ s, term i) := by
    convert! hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ι)
      (s := s) (f := f) (by intro i hi; simp [f, hi]) using 1
    simp [f]
  have hdiff := hseries.sub hf
  have h := infinite_tail_injective hε hε1 hC m idx hi (fun i => term i - f i)
    (by
      intro i hne
      by_contra hlow
      have hi := hcover i (Nat.lt_of_not_ge hlow)
      exact hne (by simp [f, hi]))
    (by
      intro i
      by_cases hi : i ∈ s
      · simp only [f, hi, ite_true, sub_self, norm_zero]
        exact (norm_nonneg (term i)).trans (hterm i)
      · simpa [f, hi] using hterm i)
  rw [hdiff.tsum_eq, norm_sub_rev] at h
  exact h

end ToeplitzSOS.Negative.Analytic
