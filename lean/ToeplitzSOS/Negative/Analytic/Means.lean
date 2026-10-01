import ToeplitzSOS.Negative.Analytic.Tails

/-! # Complete low means leave only high-total evaluations -/

open Finset
namespace ToeplitzSOS.Negative.Analytic

/-- Cancellation of complete means, without setting any incomplete mean to zero. -/
theorem sum_eq_high_of_low_means {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (A : ι → ℂ) (m : ℕ)
    (hmean : ∀ g < m, ∑ i, (if d i = g then A i else 0) = 0) (x : ℂ) :
    ∑ i, A i * x ^ d i = ∑ i, if m ≤ d i then A i * x ^ d i else 0 := by
  classical
  have hl : (∑ g ∈ range m, (∑ i, if d i = g then A i else 0) * x ^ g) = 0 := by
    apply sum_eq_zero
    intro g hg
    rw [hmean g (mem_range.mp hg), zero_mul]
  have he : (∑ g ∈ range m, (∑ i, if d i = g then A i else 0) * x ^ g) =
      ∑ i, if d i < m then A i * x ^ d i else 0 := by
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp only [ite_mul, zero_mul]
    simp [mem_range]
  rw [he] at hl
  have hs : (∑ i, A i * x ^ d i) =
      (∑ i, if m ≤ d i then A i * x ^ d i else 0) +
      (∑ i, if d i < m then A i * x ^ d i else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases h : m ≤ d i <;> simp [h, Nat.not_lt.mpr, Nat.lt_of_not_ge]
  simpa [hl] using hs

/-- Both low-total conditions remove the corresponding rows and columns. -/
theorem double_sum_eq_high_of_low_means {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (e : κ → ℕ) (A : ι → κ → ℂ) (m : ℕ)
    (hrow : ∀ g < m, ∀ j, ∑ i, (if d i = g then A i j else 0) = 0)
    (hcol : ∀ g < m, ∀ i, ∑ j, (if e j = g then A i j else 0) = 0) (x y : ℂ) :
    ∑ i, ∑ j, A i j * x ^ d i * y ^ e j =
      ∑ i, ∑ j, if m ≤ d i ∧ m ≤ e j then A i j * x ^ d i * y ^ e j else 0 := by
  classical
  calc
    _ = ∑ j, (∑ i, A i j * x ^ d i) * y ^ e j := by simp_rw [sum_mul]; rw [sum_comm]
    _ = ∑ j, (∑ i, if m ≤ d i then A i j * x ^ d i else 0) * y ^ e j := by
      congr 1
      funext j
      rw [sum_eq_high_of_low_means d (fun i => A i j) m (fun g hg => hrow g hg j) x]
    _ = ∑ i, if m ≤ d i then (∑ j, A i j * y ^ e j) * x ^ d i else 0 := by
      simp_rw [sum_mul, ite_mul, zero_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      split_ifs with hi
      · apply sum_congr rfl
        intro j _
        ring
      · simp
    _ = ∑ i, if m ≤ d i then
        (∑ j, if m ≤ e j then A i j * y ^ e j else 0) * x ^ d i else 0 := by
      apply sum_congr rfl
      intro i _
      rw [sum_eq_high_of_low_means e (A i) m (fun g hg => hcol g hg i) y]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      by_cases hi : m ≤ d i
      · simp only [hi, true_and, ite_true, sum_mul, ite_mul, zero_mul]
        apply sum_congr rfl
        intro j _
        split_ifs <;> ring
      · simp [hi]

end ToeplitzSOS.Negative.Analytic
