import ToeplitzSOS.Negative.Analytic.Means

/-! # Uniform mixed tail from complete low means

The theorem assumes a uniform coefficient bound and vanishing complete low means.
-/

open Finset ComplexConjugate
namespace ToeplitzSOS.Negative.Analytic

/-- The repeated-node mixed tail, in raw finite-sum form. -/
theorem mixed_tail_bound (m : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : Fin m → Fin m → Fin m → Fin m → ℂ)
    (hC : ∀ p q r s, ‖C p q r s‖ ≤ 4 * Real.sqrt
      ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ))
    (hrow : ∀ g < m, ∀ r s, ∑ p, ∑ q, (if p.val + q.val = g then C p q r s else 0) = 0)
    (hcol : ∀ g < m, ∀ p q, ∑ r, ∑ s, (if r.val + s.val = g then C p q r s else 0) = 0)
    (x : ℂ) (hx : ‖x‖ ≤ Real.exp (-ε / 2)) :
    ‖∑ p, ∑ q, ∑ r, ∑ s, C p q r s * x ^ p.val * x ^ q.val *
      (conj x) ^ r.val * (conj x) ^ s.val‖ ≤
      2 ^ 26 * ε⁻¹ ^ 8 * Real.exp (-ε * m / 2) := by
  classical
  let d : Fin m × Fin m → ℕ := fun p => p.1.val + p.2.val
  let A : (Fin m × Fin m) → (Fin m × Fin m) → ℂ := fun p r => C p.1 p.2 r.1 r.2
  let idx : ((Fin m × Fin m) × (Fin m × Fin m)) → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun p => ((p.1.1.val, p.1.2.val), (p.2.1.val, p.2.2.val))
  let term : ((Fin m × Fin m) × (Fin m × Fin m)) → ℂ :=
    fun p => if m ≤ d p.1 ∧ m ≤ d p.2 then A p.1 p.2 * x ^ d p.1 * (conj x) ^ d p.2 else 0
  have hid : Function.Injective idx := by
    intro p q hpq
    dsimp [idx] at hpq
    exact Prod.ext (Prod.ext (Fin.ext (congrArg (fun t => t.1.1) hpq))
      (Fin.ext (congrArg (fun t => t.1.2) hpq)))
      (Prod.ext (Fin.ext (congrArg (fun t => t.2.1) hpq))
      (Fin.ext (congrArg (fun t => t.2.2) hpq)))
  have he := double_sum_eq_high_of_low_means d d A m
    (by intro g hg r; simpa [A, d, Fintype.sum_prod_type] using hrow g hg r.1 r.2)
    (by intro g hg p; simpa [A, d, Fintype.sum_prod_type] using hcol g hg p.1 p.2) x (conj x)
  have hkernel : (∑ p, ∑ q, ∑ r, ∑ s, C p q r s * x ^ p.val * x ^ q.val *
      (conj x) ^ r.val * (conj x) ^ s.val) = ∑ p, term p := by
    rw [Fintype.sum_prod_type]
    change _ = ∑ p, ∑ r, if m ≤ d p ∧ m ≤ d r then A p r * x ^ d p * (conj x) ^ d r else 0
    rw [← he]
    simp only [A, d, Fintype.sum_prod_type, pow_add]
    congr 1
    funext p
    congr 1
    funext q
    congr 1
    funext r
    congr 1
    funext s
    ring
  rw [hkernel]
  have h := finite_tail_injective hε hε1 (by norm_num : (0 : ℝ) ≤ 4) (2 * m) idx hid term
    (by
      intro p hp
      dsimp [term] at hp
      split_ifs at hp with hhigh
      · dsimp [totalDepth, idx, d] at *
        omega
      · exact False.elim (hp rfl))
    (by
      intro p
      dsimp [term]
      split_ifs
      · have hw1 : 1 ≤ depthWeight (idx p) := by
          dsimp [depthWeight, idx]
          have h1 : (1 : ℝ) ≤ (p.1.1.val : ℝ) + 1 := by simp
          have h2 : (1 : ℝ) ≤ (p.1.2.val : ℝ) + 1 := by simp
          have h3 : (1 : ℝ) ≤ (p.2.1.val : ℝ) + 1 := by simp
          have h4 : (1 : ℝ) ≤ (p.2.2.val : ℝ) + 1 := by simp
          calc
            (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
            _ ≤ _ := by gcongr
        have hc : ‖A p.1 p.2‖ ≤ 4 * depthWeight (idx p) := by
          exact (hC p.1.1 p.1.2 p.2.1 p.2.2).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr hw1)) (by norm_num))
        have hm := kernel_monomial_bound (by norm_num : (0 : ℝ) ≤ 4) (idx p) (z := conj x) (w := conj x) hc hx hx
          (by simpa using hx) (by simpa using hx)
        convert! hm using 1
        simp only [d, idx, pow_add]
        congr 1
        ring
      · simp only [norm_zero]
        have hw : 0 ≤ depthWeight (idx p) := by dsimp [depthWeight, idx]; positivity
        positivity)
  convert! h using 1
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [show -ε * (2 * (m : ℝ)) / 4 = -ε * m / 2 by ring]
  simp only [div_eq_mul_inv, ← inv_pow]
  norm_num

end ToeplitzSOS.Negative.Analytic
