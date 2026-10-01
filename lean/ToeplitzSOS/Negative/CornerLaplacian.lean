import ToeplitzSOS.Negative.CornerBaselineForms

/-!
# Complete low totals of the mixed baseline

A finite tent-sum count proves the weighted Laplacian row identity. The
cutoff is exactly a complete total less than the depth; no high truncated
total is declared to vanish.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset

private theorem count_middle_interval (g h : ℕ) (hh : 2 * h ≤ g) :
    (∑ p ∈ range (g + 1), if h ≤ p ∧ p + h ≤ g then 1 else 0) = g + 1 - 2 * h := by
  have he : (range (g + 1)).filter (fun p => h ≤ p ∧ p + h ≤ g) = Icc h (g - h) := by
    ext p
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [← sum_filter, he]
  simp only [sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega

/-- The sum of a truncated integer tent has a closed quadratic formula. -/
theorem sum_min_tent (g h : ℕ) (hh : 2 * h ≤ g + 2) :
    (∑ p ∈ range (g + 1), min h (min (p + 1) (g - p + 1))) = h * (g + 2 - h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hs (p : ℕ) (hp : p ∈ range (g + 1)) :
        min (h + 1) (min (p + 1) (g - p + 1)) =
          min h (min (p + 1) (g - p + 1)) + if h ≤ p ∧ p + h ≤ g then 1 else 0 := by
      have hp' := mem_range.mp hp
      split_ifs <;> omega
    rw [sum_congr rfl hs, sum_add_distrib, ih (by omega), count_middle_interval g h (by omega)]
    have h₁ : g + 2 - h + h = g + 2 := by omega
    have h₂ : g + 2 - (h + 1) + (h + 1) = g + 2 := by omega
    have h₃ : g + 1 - 2 * h + 2 * h = g + 1 := by omega
    nlinarith

/-- Complete weighted mixed row count in zero-based depths. -/
theorem sum_min_complete_total (r s : ℕ) :
    (∑ p ∈ range (r + s + 1),
      min (min (p + 1) (r + s - p + 1)) (min (r + 1) (s + 1))) = (r + 1) * (s + 1) := by
  have h := sum_min_tent (r + s) (min (r + 1) (s + 1)) (by omega)
  simp only [min_comm (min (r + 1) (s + 1))] at h
  rw [h]
  by_cases hrs : r ≤ s
  · rw [min_eq_left (by omega)]
    have he : r + s + 2 - (r + 1) = s + 1 := by omega
    rw [he]
  · rw [min_eq_right (by omega)]
    have he : r + s + 2 - (s + 1) = r + 1 := by omega
    rw [he, mul_comm]

private theorem sum_total_range (m g h : ℕ) (hg : g < m) :
    (∑ p ∈ range m, ∑ q ∈ range m,
      if p + q = g then min (min (p + 1) (q + 1)) h else 0) =
    ∑ p ∈ range (g + 1), min (min (p + 1) (g - p + 1)) h := by
  have hi (p : ℕ) : (∑ q ∈ range m,
      if p + q = g then min (min (p + 1) (q + 1)) h else 0) =
      if p ≤ g then min (min (p + 1) (g - p + 1)) h else 0 := by
    by_cases hp : p ≤ g
    · rw [ite_eq_left hp, sum_eq_single (g - p)]
      · simp [Nat.add_sub_of_le hp]
      · intro q _ hq
        have he : p + q ≠ g := by omega
        simp [he]
      · intro hq
        simp only [mem_range] at hq
        omega
    · have he (q : ℕ) : p + q ≠ g := by omega
      simp [hp, he]
  simp_rw [hi]
  have he := sum_subset (s₁ := range (g + 1)) (s₂ := range m)
    (f := fun p => if p ≤ g then min (min (p + 1) (g - p + 1)) h else 0)
    (range_mono (by omega)) (by
      intro p _ hp
      have hp' : ¬ p ≤ g := by simpa only [mem_range, Nat.lt_succ_iff] using hp
      simp [hp'])
  rw [← he]
  apply sum_congr rfl
  intro p hp
  rw [ite_eq_left (by have := mem_range.mp hp; omega)]

/-- The min-weight count on every complete total of the finite depth square. -/
theorem sum_min_complete_fin {m : ℕ} (r s : Fin m) (hrs : r.val + s.val < m) :
    (∑ p : Fin m, ∑ q : Fin m, if p.val + q.val = r.val + s.val then
      min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) else 0) =
      (r.val + 1) * (s.val + 1) := by
  have he := sum_total_range m (r.val + s.val) (min (r.val + 1) (s.val + 1)) hrs
  rw [sum_min_complete_total] at he
  convert he using 1
  exact (Fin.sum_univ_eq_sum_range (fun p => ∑ q : Fin m,
    if p + q.val = r.val + s.val then
      min (min (p + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) else 0) m).trans
    (sum_congr rfl fun p _ => Fin.sum_univ_eq_sum_range (fun q =>
      if p + q = r.val + s.val then
        min (min (p + 1) (q + 1)) (min (r.val + 1) (s.val + 1)) else 0) m)

/-- Mixed baseline coefficients have support only on equal totals. -/
theorem baselineMixedEntry_eq_zero_of_ne {m : ℕ} (p q r s : Fin m)
    (h : p.val + q.val ≠ r.val + s.val) : baselineMixedEntry p q r s = 0 := by
  have hd : ¬ (p = r ∧ q = s) := by rintro ⟨rfl, rfl⟩; exact h rfl
  simp [baselineMixedEntry, h, hd]

/-- Every complete low-total column of the mixed baseline sums to zero. -/
theorem baselineMixedEntry_column_sum {m : ℕ} (r s : Fin m) (hrs : r.val + s.val < m) :
    ∑ p : Fin m, ∑ q : Fin m, baselineMixedEntry p q r s = 0 := by
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (sum_min_complete_fin r s hrs)
  push_cast at hc
  unfold baselineMixedEntry
  simp only [Nat.cast_ite, Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_min,
    Nat.cast_add, Nat.cast_one, sum_sub_distrib]
  have hd : (∑ p : Fin m, ∑ q : Fin m,
      if p = r ∧ q = s then (2 : ℝ) * (p.val + 1) * (q.val + 1) else 0) =
      2 * (r.val + 1) * (s.val + 1) := by simp [ite_and]
  rw [hd]
  have he : (∑ p : Fin m, ∑ q : Fin m,
      if p.val + q.val = r.val + s.val then
        (2 : ℝ) * min (min (p.val + 1 : ℝ) (q.val + 1)) (min (r.val + 1) (s.val + 1)) else 0) =
      2 * (r.val + 1) * (s.val + 1) := by
    simpa only [mul_sum, mul_ite, mul_zero, mul_assoc] using congrArg (fun x : ℝ => 2 * x) hc
  rw [he, sub_self]

/-- Every complete low-total row of the mixed baseline sums to zero. -/
theorem baselineMixedEntry_row_sum {m : ℕ} (p q : Fin m) (hpq : p.val + q.val < m) :
    ∑ r : Fin m, ∑ s : Fin m, baselineMixedEntry p q r s = 0 := by
  simp_rw [baselineMixedEntry_symm p q]
  exact baselineMixedEntry_column_sum p q hpq

end
end ToeplitzSOS.Negative
