import ToeplitzSOS.Negative.CornerRestriction
import ToeplitzSOS.Negative.Baseline

/-!
# Pure and mixed coordinates of the stabilized corner

The canonical Gram uses ordered offsets. Here its pairs are reindexed by
negative pure, positive pure, and mixed depth pairs.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- The three disjoint types of retained wedges. -/
abbrev BlockIndex (m : ℕ) := PureIndex m ⊕ (PureIndex m ⊕ (Fin m × Fin m))

/-- Increasing negative-side corner pair. -/
def negativePair {m : ℕ} (p : PureIndex m) : Uniform.Pair m :=
  ⟨⟨p.1.1.val, by have := p.1.1.isLt; omega⟩,
   ⟨p.1.2.val, by have := p.1.2.isLt; omega⟩, p.2⟩

/-- Increasing positive-side corner pair; depth order is reversed. -/
def positivePair {m : ℕ} (p : PureIndex m) : Uniform.Pair m :=
  ⟨⟨2 * m - 1 - p.1.2.val, by have := p.1.2.isLt; omega⟩,
   ⟨2 * m - 1 - p.1.1.val, by have := p.1.1.isLt; omega⟩,
   by have := p.1.1.isLt; have := p.1.2.isLt; have := p.2; simp only [Fin.lt_def] at *; omega⟩

/-- A negative-positive corner pair. -/
def mixedPair {m : ℕ} (p : Fin m × Fin m) : Uniform.Pair m :=
  ⟨⟨p.1.val, by have := p.1.isLt; omega⟩,
   ⟨2 * m - 1 - p.2.val, by have := p.2.isLt; omega⟩,
   by have := p.1.isLt; have := p.2.isLt; simp only [Fin.lt_def]; omega⟩

/-- Embed the disjoint three-block coordinates into the ordered pair type. -/
def blockPair {m : ℕ} : BlockIndex m → Uniform.Pair m
  | .inl p => negativePair p
  | .inr (.inl p) => positivePair p
  | .inr (.inr p) => mixedPair p

private theorem pair_ext {m : ℕ} {p q : Uniform.Pair m}
    (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) : p = q := by
  cases p; cases q; cases h₁; cases h₂; rfl

/-- The three coordinate types enumerate every corner wedge exactly once. -/
theorem blockPair_bijective (m : ℕ) : Function.Bijective (@blockPair m) := by
  constructor
  · intro p q hpq
    have h₁ := congrArg (fun p : Uniform.Pair m => p.fst.val) hpq
    have h₂ := congrArg (fun p : Uniform.Pair m => p.snd.val) hpq
    rcases p with p | p <;> rcases q with q | q
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Prod.ext (Fin.ext h₁) (Fin.ext h₂)
    · rcases q with q | q <;>
        simp only [blockPair, negativePair, positivePair, mixedPair] at h₁ h₂
      · have := p.1.1.isLt; have := q.1.2.isLt; omega
      · have := p.1.2.isLt; have := q.2.isLt; omega
    · rcases p with p | p <;>
        simp only [blockPair, negativePair, positivePair, mixedPair] at h₁ h₂
      · have := q.1.1.isLt; have := p.1.2.isLt; omega
      · have := q.1.2.isLt; have := p.2.isLt; omega
    · apply congrArg Sum.inr
      rcases p with p | p <;> rcases q with q | q <;>
        simp only [blockPair, positivePair, mixedPair] at h₁ h₂
      · apply congrArg Sum.inl
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext
        · have := p.1.1.isLt; have := q.1.1.isLt; omega
        · have := p.1.2.isLt; have := q.1.2.isLt; omega
      · have := p.1.2.isLt; have := q.1.isLt; omega
      · have := q.1.2.isLt; have := p.1.isLt; omega
      · apply congrArg Sum.inr
        apply Prod.ext
        · exact Fin.ext h₁
        · apply Fin.ext
          have := p.2.isLt; have := q.2.isLt; omega
  · intro p
    have hp₁ := p.fst.isLt
    have hp₂ := p.snd.isLt
    have hp := Fin.lt_def.mp p.le
    by_cases h₂ : p.snd.val < m
    · refine ⟨.inl ⟨(⟨p.fst.val, by omega⟩, ⟨p.snd.val, h₂⟩), p.le⟩, ?_⟩
      exact pair_ext rfl rfl
    · by_cases h₁ : p.fst.val < m
      · refine ⟨.inr (.inr (⟨p.fst.val, h₁⟩, ⟨2 * m - 1 - p.snd.val, by omega⟩)), ?_⟩
        apply pair_ext
        · rfl
        apply Fin.ext
        simp only [blockPair, mixedPair]
        omega
      · refine ⟨.inr (.inl ⟨(⟨2 * m - 1 - p.snd.val, by omega⟩,
          ⟨2 * m - 1 - p.fst.val, by omega⟩), by simp only [Fin.lt_def]; omega⟩), ?_⟩
        apply pair_ext <;> apply Fin.ext <;> simp only [blockPair, positivePair] <;> omega

/-- The explicit coordinate equivalence for splitting corner sums. -/
def blockPairEquiv (m : ℕ) : BlockIndex m ≃ Uniform.Pair m :=
  Equiv.ofBijective blockPair (blockPair_bijective m)

/-- Antisymmetry of the corner wedge. -/
theorem cornerWedge_swap {m : ℕ} (a b : CornerLabel m) :
    cornerWedge b a = -cornerWedge a b := by
  unfold cornerWedge
  ring

/-- The pure wedge on one side, in increasing depth order. -/
def pureWedge {m : ℕ} (side : Bool) (p : PureIndex m) :
    MvPolynomial (CornerVariable m) ℝ := cornerWedge (side, p.1.1) (side, p.1.2)

/-- The mixed wedge, negative side first. -/
def mixedWedge {m : ℕ} (p q : Fin m) : MvPolynomial (CornerVariable m) ℝ :=
  cornerWedge (false, p) (true, q)

/-- A negative ordered pair has the increasing-depth pure wedge. -/
@[simp] theorem orderedCornerWedge_negativePair {m : ℕ} (p : PureIndex m) :
    orderedCornerWedge (negativePair p) = pureWedge false p := by
  simp [orderedCornerWedge, negativePair, depthLabel, p.1.1.isLt, p.1.2.isLt, pureWedge]

/-- A positive ordered pair has the opposite increasing-depth pure wedge. -/
@[simp] theorem orderedCornerWedge_positivePair {m : ℕ} (p : PureIndex m) :
    orderedCornerWedge (positivePair p) = -pureWedge true p := by
  have h₁ := p.1.1.isLt
  have h₂ := p.1.2.isLt
  have hn₁ : ¬ 2 * m - 1 - p.1.1.val < m := by omega
  have hn₂ : ¬ 2 * m - 1 - p.1.2.val < m := by omega
  have he₁ : 2 * m - 1 - (2 * m - 1 - p.1.1.val) = p.1.1.val := by omega
  have he₂ : 2 * m - 1 - (2 * m - 1 - p.1.2.val) = p.1.2.val := by omega
  simpa [orderedCornerWedge, positivePair, depthLabel, hn₁, hn₂, he₁, he₂, pureWedge]
    using cornerWedge_swap (true, p.1.1) (true, p.1.2)

/-- The mixed ordered pair keeps the negative-positive orientation. -/
@[simp] theorem orderedCornerWedge_mixedPair {m : ℕ} (p : Fin m × Fin m) :
    orderedCornerWedge (mixedPair p) = mixedWedge p.1 p.2 := by
  have h₁ := p.1.isLt
  have h₂ := p.2.isLt
  have hn₂ : ¬ 2 * m - 1 - p.2.val < m := by omega
  have he₂ : 2 * m - 1 - (2 * m - 1 - p.2.val) = p.2.val := by omega
  simp [orderedCornerWedge, mixedPair, depthLabel, h₁, hn₂, he₂, mixedWedge]

private theorem baseEntry_eq {m : ℕ} (p q : Uniform.Pair m) :
    Uniform.baseEntry p q =
      (if p = q then 2 * (Uniform.weight p.fst : ℚ) * Uniform.weight p.snd else 0) -
      (if Uniform.mixed p ∧ Uniform.mixed q ∧ Uniform.displacement p = Uniform.displacement q
        then 2 * (min (Uniform.height p) (Uniform.height q) : ℚ) else 0) := by
  by_cases hpq : p = q
  · subst q
    rcases Uniform.sameSide_or_mixed p with hs | hm
    · simp [Uniform.baseEntry, hs, Uniform.not_mixed_of_sameSide hs]
    · have hs : ¬ Uniform.sameSide p := fun hs => Uniform.not_mixed_of_sameSide hs hm
      simp [Uniform.baseEntry, hs, hm]
  · by_cases hc : Uniform.mixed p ∧ Uniform.mixed q ∧ Uniform.displacement p = Uniform.displacement q
    · simp [Uniform.baseEntry, hpq, hc]
    · simp [Uniform.baseEntry, hpq, hc]

/-- The canonical mixed entry before the Plücker exchange: equal differences
couple, rather than equal totals. -/
def rawMixedEntry {m : ℕ} (p q r s : Fin m) : ℝ :=
  (if p = r ∧ q = s then 2 * (p.val + 1) * (q.val + 1) else 0) -
    (if p.val + s.val = r.val + q.val then
      2 * (min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) : ℕ)
    else 0)

private theorem negativePair_weights {m : ℕ} (p : PureIndex m) :
    Uniform.weight (negativePair p).fst = p.1.1.val + 1 ∧
    Uniform.weight (negativePair p).snd = p.1.2.val + 1 ∧
    ¬ Uniform.mixed (negativePair p) := by
  have h₁ := p.1.1.isLt
  have h₂ := p.1.2.isLt
  simp [negativePair, Uniform.weight, Uniform.isNegative, Uniform.mixed,
    Uniform.isPositive, h₁, h₂, Nat.not_le_of_lt h₂]

private theorem positivePair_weights {m : ℕ} (p : PureIndex m) :
    Uniform.weight (positivePair p).fst = p.1.2.val + 1 ∧
    Uniform.weight (positivePair p).snd = p.1.1.val + 1 ∧
    ¬ Uniform.mixed (positivePair p) := by
  have h₁ := p.1.1.isLt
  have h₂ := p.1.2.isLt
  have hn₁ : ¬ 2 * m - 1 - p.1.1.val < m := by omega
  have hn₂ : ¬ 2 * m - 1 - p.1.2.val < m := by omega
  simp only [positivePair, Uniform.weight, Uniform.isNegative, Uniform.mixed,
    hn₁, hn₂, ite_false, false_and, not_false_eq_true, and_true]
  omega

private theorem mixedPair_weights {m : ℕ} (p : Fin m × Fin m) :
    Uniform.weight (mixedPair p).fst = p.1.val + 1 ∧
    Uniform.weight (mixedPair p).snd = p.2.val + 1 ∧
    Uniform.mixed (mixedPair p) := by
  have h₁ := p.1.isLt
  have h₂ := p.2.isLt
  have hn₂ : ¬ 2 * m - 1 - p.2.val < m := by omega
  simp only [mixedPair, Uniform.weight, Uniform.isNegative, Uniform.mixed,
    Uniform.isPositive, h₁, hn₂, ite_true, ite_false, true_and]
  omega

/-- The canonical Gram in the disjoint pure/mixed coordinates. -/
def rawBlockEntry {m : ℕ} : BlockIndex m → BlockIndex m → ℝ
  | .inl p, .inl q => if p = q then 2 * (p.1.1.val + 1) * (p.1.2.val + 1) else 0
  | .inr (.inl p), .inr (.inl q) =>
      if p = q then 2 * (p.1.1.val + 1) * (p.1.2.val + 1) else 0
  | .inr (.inr p), .inr (.inr q) => rawMixedEntry p.1 p.2 q.1 q.2
  | _, _ => 0

/-- Explicit evaluation of every block of the canonical Gram. -/
theorem cornerBlock_blockPair {m : ℕ} (p q : BlockIndex m) :
    (Uniform.cornerBlock m (blockPair p) (blockPair q) : ℝ) = rawBlockEntry p q := by
  classical
  rw [Uniform.cornerBlock, baseEntry_eq]
  simp only [(blockPair_bijective m).1.eq_iff]
  rcases p with p | p <;> rcases q with q | q
  · obtain ⟨hp₁, hp₂, hp₃⟩ := negativePair_weights p
    simp only [blockPair, hp₁, hp₂, hp₃, rawBlockEntry, false_and, ite_false, sub_zero, Sum.inl.injEq]
    split_ifs <;> push_cast <;> rfl
  · rcases q with q | q <;>
      simp [blockPair, (negativePair_weights p).2.2, rawBlockEntry]
  · rcases p with p | p <;>
      simp [blockPair, (negativePair_weights q).2.2, rawBlockEntry]
  · rcases p with p | p <;> rcases q with q | q
    · obtain ⟨hp₁, hp₂, hp₃⟩ := positivePair_weights p
      simp only [Sum.inr.injEq, Sum.inl.injEq, blockPair, hp₁, hp₂, hp₃, false_and,
        ite_false, sub_zero, rawBlockEntry]
      split_ifs <;> push_cast <;> ring
    · simp [blockPair, (positivePair_weights p).2.2, rawBlockEntry]
    · simp [blockPair, (positivePair_weights q).2.2, rawBlockEntry]
    · obtain ⟨hp₁, hp₂, hp₃⟩ := mixedPair_weights p
      obtain ⟨hq₁, hq₂, hq₃⟩ := mixedPair_weights q
      have hd : Uniform.displacement (mixedPair p) = Uniform.displacement (mixedPair q) ↔
          p.1.val + q.2.val = q.1.val + p.2.val := by
        simp only [Uniform.displacement, hp₁, hp₂, hq₁, hq₂]
        omega
      simp only [Sum.inr.injEq, Prod.ext_iff, blockPair, hp₁, hp₂, hp₃, hq₃, true_and,
        hd, Uniform.height, hq₁, hq₂, rawBlockEntry, rawMixedEntry]
      split_ifs <;> push_cast <;> rfl

/-- The full canonical mixed polynomial and the two diagonal pure blocks. -/
def rawCorner (m : ℕ) : MvPolynomial (CornerVariable m) ℝ :=
  (∑ p : PureIndex m, C (2 * (p.1.1.val + 1) * (p.1.2.val + 1) : ℝ) *
      (pureWedge false p ^ 2 + pureWedge true p ^ 2)) +
  ∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
    C (rawMixedEntry p q r s) * mixedWedge p q * mixedWedge r s

/-- The literal canonical corner splits into its two pure diagonal blocks
and its mixed difference-kernel block. -/
theorem canonicalCorner_eq_rawCorner (m : ℕ) : canonicalCorner m = rawCorner m := by
  classical
  unfold canonicalCorner
  rw [← (blockPairEquiv m).sum_comp]
  simp_rw [← (blockPairEquiv m).sum_comp]
  change (∑ p : BlockIndex m, ∑ q : BlockIndex m,
    C (Uniform.cornerBlock m (blockPair p) (blockPair q) : ℝ) *
      orderedCornerWedge (blockPair p) * orderedCornerWedge (blockPair q)) = _
  simp_rw [cornerBlock_blockPair]
  simp only [Fintype.sum_sum_type, blockPair, rawBlockEntry,
    orderedCornerWedge_negativePair, orderedCornerWedge_positivePair, orderedCornerWedge_mixedPair]
  simp only [apply_ite C, map_zero, ite_mul, zero_mul, sum_ite_eq, sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, neg_neg, neg_zero, mem_univ, ite_true]
  simp only [rawCorner, Fintype.sum_prod_type, mul_add, sum_add_distrib, pow_two, mul_assoc]
  ring

end
end ToeplitzSOS.Negative
