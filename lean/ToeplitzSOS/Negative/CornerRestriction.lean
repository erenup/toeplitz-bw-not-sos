import ToeplitzSOS.Negative.Restriction
import ToeplitzSOS.Uniform.Bridge

/-!
# The literal outer restriction and the canonical stabilized Gram

This module connects the literal polynomial substitution to the arbitrary-size
corner Gram theorem in `Uniform.Bridge`. The positive-side labels are reversed
when passing from ordered offsets to zero-based depths.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- Convert ordered corner labels to a side and a zero-based depth. -/
def depthLabel {m : ℕ} (a : Uniform.Label m) : CornerLabel m :=
  if h : a.val < m then (false, ⟨a.val, h⟩)
  else (true, ⟨2 * m - 1 - a.val, by have := a.isLt; omega⟩)

/-- The wedge on two retained corner labels. -/
def cornerWedge {m : ℕ} (a b : CornerLabel m) : MvPolynomial (CornerVariable m) ℝ :=
  MvPolynomial.X (.x, a) * MvPolynomial.X (.y, b) -
    MvPolynomial.X (.x, b) * MvPolynomial.X (.y, a)

/-- Wedges indexed by the ordered corner pairs of the canonical Gram. -/
def orderedCornerWedge {m : ℕ} (p : Uniform.Pair m) :
    MvPolynomial (CornerVariable m) ℝ := cornerWedge (depthLabel p.fst) (depthLabel p.snd)

/-- The stabilized polynomial in the canonical difference-kernel Gram. -/
def canonicalCorner (m : ℕ) : MvPolynomial (CornerVariable m) ℝ :=
  ∑ p : Uniform.Pair m, ∑ q : Uniform.Pair m,
    C (Uniform.cornerBlock m p q : ℝ) * orderedCornerWedge p * orderedCornerWedge q

/-- Retained ordered labels are sent to their literal corner variable. -/
theorem outerSubstitution_cornerEmb {m N : ℕ} (h : m + 1 ≤ N)
    (c : CoordFamily) (a : Uniform.Label m) :
    outerSubstitution m N (c, Uniform.cornerEmb m N h a) =
      MvPolynomial.X (c, depthLabel a) := by
  have ha := a.isLt
  by_cases ham : a.val < m
  · simp [outerSubstitution, Uniform.cornerEmb, depthLabel, ham]
  · have hn : ¬ a.val + 2 * (N - m) - 1 < m := by omega
    have hp : 2 * m - 1 - a.val < m := by omega
    have he : 2 * N - 2 - (a.val + 2 * (N - m) - 1) = 2 * m - 1 - a.val := by omega
    simp [outerSubstitution, Uniform.cornerEmb, depthLabel, ham, hn, hp, he]

/-- Every retained offset lies in the ordered corner embedding. -/
theorem mem_range_cornerEmb {m N : ℕ} (h : m + 1 ≤ N) (a : Fin (2 * N - 1)) :
    a ∈ Set.range (Uniform.cornerEmb m N h) ↔
      a.val < m ∨ 2 * N - 2 - a.val < m := by
  have ha := a.isLt
  constructor
  · rintro ⟨b, rfl⟩
    have hb := b.isLt
    simp only [Uniform.cornerEmb]
    split_ifs <;> omega
  · intro hmem
    rcases hmem with hmem | hmem
    · refine ⟨⟨a.val, by omega⟩, ?_⟩
      apply Fin.ext
      simp [Uniform.cornerEmb, hmem]
    · refine ⟨⟨2 * m - 1 - (2 * N - 2 - a.val), by omega⟩, ?_⟩
      apply Fin.ext
      simp only [Uniform.cornerEmb]
      split_ifs <;> omega

/-- Discarded offsets are sent to zero. -/
theorem outerSubstitution_eq_zero_of_not_mem_range {m N : ℕ} (h : m + 1 ≤ N)
    (c : CoordFamily) (a : Fin (2 * N - 1))
    (ha : a ∉ Set.range (Uniform.cornerEmb m N h)) :
    outerSubstitution m N (c, a) = 0 := by
  rw [mem_range_cornerEmb] at ha
  simp only [not_or] at ha
  simp [outerSubstitution, ha.1, ha.2]

/-- The literal substitution carries an embedded wedge to its corner wedge. -/
theorem aeval_wedge_pairEmb {m N : ℕ} (h : m + 1 ≤ N) (p : Uniform.Pair m) :
    aeval (outerSubstitution m N) (Kernel.wedge (Uniform.pairEmb h p)) =
      orderedCornerWedge p := by
  simp [Kernel.wedge, z, x, y, Uniform.pairEmb, outerSubstitution_cornerEmb,
    orderedCornerWedge, cornerWedge]

/-- A wedge outside the retained pair embedding vanishes under restriction. -/
theorem aeval_wedge_eq_zero_of_not_mem_range {m N : ℕ} (h : m + 1 ≤ N)
    (p : Kernel.W N) (hp : p ∉ Set.range (Uniform.pairEmb h)) :
    aeval (outerSubstitution m N) (Kernel.wedge p) = 0 := by
  have hnot : p.1.1 ∉ Set.range (Uniform.cornerEmb m N h) ∨
      p.1.2 ∉ Set.range (Uniform.cornerEmb m N h) := by
    by_contra hn
    push Not at hn
    obtain ⟨a, ha⟩ := hn.1
    obtain ⟨b, hb⟩ := hn.2
    have hab : a < b := (Uniform.cornerEmb_strictMono m N h).lt_iff_lt.mp (by
      rw [ha, hb]; exact p.2)
    apply hp
    refine ⟨⟨a, b, hab⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext ha hb
  rcases hnot with ha | hb
  · simp [Kernel.wedge, z, x, y, outerSubstitution_eq_zero_of_not_mem_range h _ _ ha]
  · simp [Kernel.wedge, z, x, y, outerSubstitution_eq_zero_of_not_mem_range h _ _ hb]

/-- The literal restriction is the canonical corner polynomial at every
stabilized ambient order. -/
theorem outerCorner_eq_canonicalCorner {m N : ℕ} (hN : 2 * m ≤ N) :
    outerCorner m N = canonicalCorner m := by
  classical
  by_cases h : m + 1 ≤ N
  · have hg := Uniform.gramQ0_isWedgeGram N
    unfold Kernel.IsWedgeGram at hg
    rw [outerCorner, hg]
    simp only [map_sum, map_mul, aeval_C]
    have restrict_sum (f : Kernel.W N → MvPolynomial (CornerVariable m) ℝ)
        (hf : ∀ p, p ∉ Set.range (Uniform.pairEmb h) → f p = 0) :
        ∑ p, f p = ∑ p : Uniform.Pair m, f (Uniform.pairEmb h p) :=
      (Fintype.sum_of_injective (Uniform.pairEmb h) (Uniform.pairEmb_injective h)
        _ _ hf (fun _ => rfl)).symm
    rw [restrict_sum _ (fun p hp => by
      simp only [aeval_wedge_eq_zero_of_not_mem_range h p hp, mul_zero, zero_mul, sum_const_zero])]
    unfold canonicalCorner
    apply sum_congr rfl
    intro p _
    rw [restrict_sum _ (fun q hq => by
      simp only [aeval_wedge_eq_zero_of_not_mem_range h q hq, mul_zero])]
    apply sum_congr rfl
    intro q _
    rw [Uniform.gramQ0_pairEmb_stable h hN, aeval_wedge_pairEmb, aeval_wedge_pairEmb]
    rfl
  · have hm : m = 0 := by omega
    have hn : N = 0 := by omega
    subst m N
    let : IsEmpty (Uniform.Pair 0) := ⟨fun p => Fin.elim0 p.fst⟩
    simp [outerCorner, toeplitzBW, frob, inner, canonicalCorner]

/-- The literal corner no longer depends on the ambient order once the two
outer depth intervals have separated. -/
theorem outerCorner_stable {m N N' : ℕ} (hN : 2 * m ≤ N) (hN' : 2 * m ≤ N') :
    outerCorner m N = outerCorner m N' := by
  rw [outerCorner_eq_canonicalCorner hN, outerCorner_eq_canonicalCorner hN']

end
end ToeplitzSOS.Negative
