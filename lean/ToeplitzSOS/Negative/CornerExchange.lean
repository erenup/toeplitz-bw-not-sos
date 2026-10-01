import ToeplitzSOS.Negative.CornerCoordinates

/-!
# Plücker exchange to the full-Gram D/K/B representative

The difference kernel of the literal canonical Gram is exchanged for the
total kernel of `Baseline`, retaining the pure cross term with its full
factor two. All identities are finite polynomial identities.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- The four-label Plücker identity in the literal corner variables. -/
theorem corner_plucker {m : ℕ} (a b c d : CornerLabel m) :
    cornerWedge a b * cornerWedge c d - cornerWedge a c * cornerWedge b d +
      cornerWedge a d * cornerWedge b c = 0 := by
  unfold cornerWedge
  ring

/-- Mixed matchings differ by the product of the two pure wedges. -/
theorem mixed_matchings {m : ℕ} (p q r s : Fin m) :
    mixedWedge p q * mixedWedge r s - mixedWedge p s * mixedWedge r q =
      cornerWedge (false, p) (false, r) * cornerWedge (true, q) (true, s) := by
  unfold mixedWedge cornerWedge
  ring

/-- The positive commutator weight supported on equal differences. -/
def differenceWeight {m : ℕ} (p q r s : Fin m) : ℝ :=
  ((if p.val + s.val = r.val + q.val then
    2 * min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1))
  else 0 : ℕ) : ℝ)

/-- Same-gap pure cross coefficient, in full Gram units. -/
def baselineCrossEntry {m : ℕ} (p q : PureIndex m) : ℝ :=
  if p.1.2.val - p.1.1.val = q.1.2.val - q.1.1.val then
    -2 * (min (p.1.1.val + 1) (q.1.1.val + 1) : ℕ)
  else 0

/-- The explicit D/K/B polynomial, with the full cross term `2 uᵀ K v`. -/
def baselinePolynomial (m : ℕ) : MvPolynomial (CornerVariable m) ℝ :=
  (∑ p : PureIndex m, C (2 * (p.1.1.val + 1) * (p.1.2.val + 1) : ℝ) *
      (pureWedge false p ^ 2 + pureWedge true p ^ 2)) +
  2 * (∑ p : PureIndex m, ∑ q : PureIndex m,
    C (baselineCrossEntry p q) * pureWedge false p * pureWedge true q) +
  ∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
    C (baselineMixedEntry p q r s) * mixedWedge p q * mixedWedge r s

/-- Summing over increasing depth pairs is a filtered double sum. -/
theorem sum_pureIndex {R : Type*} [AddCommMonoid R] (m : ℕ) (f : Fin m → Fin m → R) :
    ∑ p : PureIndex m, f p.1.1 p.1.2 = ∑ p, ∑ q, if p < q then f p q else 0 := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun pq : Fin m × Fin m => pq.1 < pq.2)
    (by simp) (fun pq => f pq.1 pq.2), Finset.sum_filter, Fintype.sum_prod_type]

/-- A symmetric zero-diagonal double sum is twice its increasing-pair sum. -/
theorem sum_depthPairs {R : Type*} [CommRing R] (m : ℕ) (f : Fin m → Fin m → R)
    (hs : ∀ p q, f p q = f q p) (hd : ∀ p, f p p = 0) :
    ∑ p, ∑ q, f p q = 2 * ∑ pq : PureIndex m, f pq.1.1 pq.1.2 := by
  classical
  have split (p q) : f p q = (if p < q then f p q else 0) +
      (if q < p then f q p else 0) := by
    rcases lt_trichotomy p q with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hd]
    · simp [h, not_lt_of_gt h, hs p q]
  have swap : (∑ p : Fin m, ∑ q : Fin m, if q < p then f q p else 0) =
      ∑ p : Fin m, ∑ q : Fin m, if p < q then f p q else 0 := sum_comm
  rw [sum_pureIndex]
  conv_lhs => arg 2; ext p; arg 2; ext q; rw [split p q]
  simp only [sum_add_distrib, swap, two_mul]

/-- The mixed total coefficient is the transposed matching of the raw
commutator coefficient. -/
theorem baselineMixedEntry_eq_differenceWeight {m : ℕ} (p q r s : Fin m) :
    baselineMixedEntry p q r s =
      (if p = r ∧ q = s then 2 * (p.val + 1) * (q.val + 1) else 0) -
        differenceWeight p s r q := by
  have he : min (min (p.val + 1) (s.val + 1)) (min (r.val + 1) (q.val + 1)) =
      min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) := by omega
  simp only [baselineMixedEntry, differenceWeight, he]

private theorem differenceWeight_swap {m : ℕ} (p q r s : Fin m) :
    differenceWeight r s p q = differenceWeight p q r s := by
  simp only [differenceWeight, min_comm (min (r.val + 1) (s.val + 1)), eq_comm]

private theorem differenceWeight_increasing {m : ℕ} (p q : PureIndex m) :
    differenceWeight p.1.1 q.1.1 p.1.2 q.1.2 = -baselineCrossEntry p q := by
  have hp := Fin.lt_def.mp p.2
  have hq := Fin.lt_def.mp q.2
  have he : p.1.1.val + q.1.2.val = p.1.2.val + q.1.1.val ↔
      p.1.2.val - p.1.1.val = q.1.2.val - q.1.1.val := by omega
  have hm : min (min (p.1.1.val + 1) (q.1.1.val + 1))
      (min (p.1.2.val + 1) (q.1.2.val + 1)) =
      min (p.1.1.val + 1) (q.1.1.val + 1) := by omega
  simp only [differenceWeight, baselineCrossEntry, he, hm]
  split_ifs <;> push_cast <;> ring

/-- A repeated corner label has zero wedge. -/
@[simp] theorem cornerWedge_self {m : ℕ} (a : CornerLabel m) : cornerWedge a a = 0 := by
  simp [cornerWedge]

private theorem sum_four_swap24 {R : Type*} [AddCommMonoid R] (m : ℕ)
    (f : Fin m → Fin m → Fin m → Fin m → R) :
    ∑ p, ∑ q, ∑ r, ∑ s, f p q r s = ∑ p, ∑ q, ∑ r, ∑ s, f p s r q := by
  apply sum_congr rfl
  intro p _
  calc
    _ = ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m, f p q r s := sum_comm
    _ = ∑ r : Fin m, ∑ s : Fin m, ∑ q : Fin m, f p q r s := by
      apply sum_congr rfl
      intro r _
      exact sum_comm
    _ = _ := sum_comm

private theorem difference_pure_sum (m : ℕ) :
    (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      C (differenceWeight p q r s) * cornerWedge (false, p) (false, r) *
        cornerWedge (true, q) (true, s)) =
      -2 * (∑ p : PureIndex m, ∑ q : PureIndex m,
        C (baselineCrossEntry p q) * pureWedge false p * pureWedge true q) := by
  let f (p r : Fin m) := ∑ q : Fin m, ∑ s : Fin m,
    C (differenceWeight p q r s) * cornerWedge (false, p) (false, r) *
      cornerWedge (true, q) (true, s)
  have hs (p r : Fin m) : f p r = f r p := by
    dsimp only [f]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro s _
    rw [differenceWeight_swap p q r s, cornerWedge_swap (false, p) (false, r),
      cornerWedge_swap (true, q) (true, s)]
    ring
  have hd (p : Fin m) : f p p = 0 := by
    simp only [f, cornerWedge_self, mul_zero, zero_mul, sum_const_zero]
  have hi (p : PureIndex m) : f p.1.1 p.1.2 =
      ∑ q : PureIndex m, C (differenceWeight p.1.1 q.1.1 p.1.2 q.1.2) *
        pureWedge false p * pureWedge true q := by
    dsimp only [f, pureWedge]
    rw [sum_pureIndex m (fun q s => C (differenceWeight p.1.1 q p.1.2 s) *
      cornerWedge (false, p.1.1) (false, p.1.2) * cornerWedge (true, q) (true, s))]
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro s _
    split_ifs with hqs
    · rfl
    · have hp := Fin.lt_def.mp p.2
      have he : ¬ p.1.1.val + s.val = p.1.2.val + q.val := by
        simp only [Fin.lt_def] at hqs
        omega
      simp only [differenceWeight, he, ite_false, Nat.cast_zero, map_zero, zero_mul]
  calc
    _ = ∑ p : Fin m, ∑ r : Fin m, f p r := by
      apply sum_congr rfl
      intro p _
      exact sum_comm
    _ = 2 * ∑ p : PureIndex m, f p.1.1 p.1.2 := sum_depthPairs m f hs hd
    _ = _ := by
      simp only [hi, differenceWeight_increasing, map_neg, neg_mul, sum_neg_distrib]
      ring

/-- Exact Plücker exchange between the raw difference coupling and the total
coupling, including the full cross-term normalization. -/
theorem difference_total_exchange (m : ℕ) :
    (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      C (differenceWeight p q r s) * mixedWedge p q * mixedWedge r s) =
    (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      C (differenceWeight p s r q) * mixedWedge p q * mixedWedge r s) -
    2 * (∑ p : PureIndex m, ∑ q : PureIndex m,
      C (baselineCrossEntry p q) * pureWedge false p * pureWedge true q) := by
  have hswap := sum_four_swap24 m (fun p q r s =>
    C (differenceWeight p s r q) * mixedWedge p q * mixedWedge r s)
  have hp := difference_pure_sum m
  have he : (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      C (differenceWeight p q r s) * mixedWedge p q * mixedWedge r s) -
      (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
        C (differenceWeight p q r s) * mixedWedge p s * mixedWedge r q) =
      ∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
        C (differenceWeight p q r s) * cornerWedge (false, p) (false, r) *
          cornerWedge (true, q) (true, s) := by
    simp only [← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro s _
    rw [mul_assoc, mul_assoc, ← mul_sub, mixed_matchings, mul_assoc]
  rw [hp, ← hswap] at he
  linear_combination he

private theorem rawMixedEntry_eq_differenceWeight {m : ℕ} (p q r s : Fin m) :
    rawMixedEntry p q r s =
      (if p = r ∧ q = s then 2 * (p.val + 1) * (q.val + 1) else 0) -
        differenceWeight p q r s := rfl

/-- The stabilized canonical polynomial is exactly the D/K/B polynomial. -/
theorem rawCorner_eq_baselinePolynomial (m : ℕ) : rawCorner m = baselinePolynomial m := by
  simp only [rawCorner, baselinePolynomial, rawMixedEntry_eq_differenceWeight,
    baselineMixedEntry_eq_differenceWeight, map_sub, sub_mul,
    sum_sub_distrib]
  rw [difference_total_exchange]
  ring

/-- Literal matrix-to-baseline bridge for every stabilized ambient order. -/
theorem outerCorner_eq_baselinePolynomial {m N : ℕ} (hN : 2 * m ≤ N) :
    outerCorner m N = baselinePolynomial m := by
  rw [outerCorner_eq_canonicalCorner hN, canonicalCorner_eq_rawCorner,
    rawCorner_eq_baselinePolynomial]

end
end ToeplitzSOS.Negative
