import ToeplitzSOS.ThmA.Defs
import ToeplitzSOS.ThmA.Reindex
import ToeplitzSOS.ThmA.Commutator
import Mathlib

/-!
# Same-side blocks and the residual form

Weighted Lagrange sums, their nine-block decomposition, and the
positive-side residual form together with its reflected counterpart.
-/

open Finset

noncomputable section

namespace ToeplitzSOS.ThmA

section Generic
variable {R : Type*} [CommRing R]

/-! ### `H_{n−1}` = same-side diagonal − window squares -/

/-- (positive side): `H_{n−1}(x, y) = ssdiag − ∑_{δ,k} (S⁺_{δ,k})²`. -/
theorem Hform_split (n : ℕ) (x y : ℤ → R) :
    Hform (n - 1) x y = ssdiag n x y
      - ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1), Splus n x y δ k ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Hform, ssdiag, Splus, Nat.zero_sub, Nat.cast_zero]
    rw [Icc_eq_empty (by norm_num), Icc_eq_empty (by norm_num), Icc_eq_empty (by norm_num)]
    simp
  · have hm : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have h2 : (n : ℤ) - 1 - 1 = (n : ℤ) - 2 := by ring
    unfold Hform ssdiag Splus
    rw [hm, sub_add_cancel, h2]

/-- (negative side): `H_{n−1}(x∘neg, y∘neg) = ssdiag(x∘neg, y∘neg) − ∑_{δ,k} (S⁻_{δ,k})²`. -/
theorem Hform_split_neg (n : ℕ) (x y : ℤ → R) :
    Hform (n - 1) (fun i => x (-i)) (fun i => y (-i))
      = ssdiag n (fun i => x (-i)) (fun i => y (-i))
        - ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            Sminus n x y δ k ^ 2 := by
  rw [Hform_split]
  have e : ∀ δ k, Splus n (fun i => x (-i)) (fun i => y (-i)) δ k = -Sminus n x y δ k := by
    intro δ k
    simp only [Splus, Sminus, ← sum_neg_distrib]
    refine sum_congr rfl fun p _ => ?_
    unfold wedge; ring
  simp only [e, neg_sq]

/-! ### Weighted Lagrange identity -/

private lemma frob_tmat (n : ℕ) (x : ℤ → R) :
    ToeplitzSOS.frob (tmat n x) = ∑ a ∈ Ioo (-(n : ℤ)) n, (((n : ℤ) - |a| : ℤ) : R) * x a ^ 2 := by
  simp only [ToeplitzSOS.frob, tmat]
  refine (sum_fin_fin_eq_sum_Ico n (fun a b => x (a - b) ^ 2)).trans ?_
  exact square_diag_sum (n : ℤ) (fun d => x d ^ 2)

private lemma inner_tmat (n : ℕ) (x y : ℤ → R) :
    ToeplitzSOS.inner (tmat n x) (tmat n y)
      = ∑ a ∈ Ioo (-(n : ℤ)) n, (((n : ℤ) - |a| : ℤ) : R) * (x a * y a) := by
  simp only [ToeplitzSOS.inner, tmat]
  refine (sum_fin_fin_eq_sum_Ico n (fun a b => x (a - b) * y (a - b))).trans ?_
  exact square_diag_sum (n : ℤ) (fun d => x d * y d)

/-- (weighted Lagrange identity with the diagonal weights `n − |a|`):
`2‖X‖²‖Y‖² − 2⟨X,Y⟩² = ∑_{a,b ∈ (−n,n)} (n−|a|)(n−|b|) z_ab²`. Used by `thmA_gram`, `lagrange_band`,
`Symmetric.lagrange_ext`. -/
theorem weights_lagrange (n : ℕ) (x y : ℤ → R) :
    2 * ToeplitzSOS.frob (tmat n x) * ToeplitzSOS.frob (tmat n y)
        - 2 * ToeplitzSOS.inner (tmat n x) (tmat n y) ^ 2
      = ∑ a ∈ Ioo (-(n : ℤ)) n, ∑ b ∈ Ioo (-(n : ℤ)) n,
          ((((n : ℤ) - |a|) * ((n : ℤ) - |b|) : ℤ) : R) * wedge x y a b ^ 2 := by
  rw [frob_tmat, frob_tmat, inner_tmat]
  have e : ∀ a b, ((((n : ℤ) - |a|) * ((n : ℤ) - |b|) : ℤ) : R) * wedge x y a b ^ 2
      = (((n : ℤ) - |a| : ℤ) : R) * x a ^ 2 * ((((n : ℤ) - |b| : ℤ) : R) * y b ^ 2)
        + (((n : ℤ) - |b| : ℤ) : R) * x b ^ 2 * ((((n : ℤ) - |a| : ℤ) : R) * y a ^ 2)
        - 2 * ((((n : ℤ) - |a| : ℤ) : R) * (x a * y a)
          * ((((n : ℤ) - |b| : ℤ) : R) * (x b * y b))) := by
    intro a b; rw [Int.cast_mul]; unfold wedge; ring
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => e a b]
  simp only [sum_sub_distrib, sum_add_distrib]
  rw [sum_comm (s := Ioo (-(n : ℤ)) n) (t := Ioo (-(n : ℤ)) n)
    (f := fun a b => (((n : ℤ) - |b| : ℤ) : R) * x b ^ 2 * ((((n : ℤ) - |a| : ℤ) : R) * y a ^ 2))]
  simp only [← mul_sum, ← sum_mul]
  ring

/-! ### The nine-block split -/

/-- Splitting a symmetric interval `(−n, n)` into `{0}`, the negative and the positive part. -/
theorem split_Ioo {M : Type*} [AddCommMonoid M] (n : ℤ) (hn : 1 ≤ n) (f : ℤ → M) :
    ∑ a ∈ Ioo (-n) n, f a = f 0 + ∑ P ∈ Icc 1 (n - 1), f (-P) + ∑ P ∈ Icc 1 (n - 1), f P := by
  rw [← sum_filter_add_sum_filter_not (Ioo (-n) n) (fun a => 0 < a),
    ← sum_filter_add_sum_filter_not ((Ioo (-n) n).filter (fun a => ¬ 0 < a)) (fun a => a = 0)]
  have h1 : (Ioo (-n) n).filter (fun a => 0 < a) = Icc 1 (n - 1) := by
    ext a; simp only [mem_filter, mem_Ioo, mem_Icc]; omega
  have h2 : ((Ioo (-n) n).filter (fun a => ¬ 0 < a)).filter (fun a => a = 0) = {0} := by
    ext a; simp only [mem_filter, mem_Ioo, mem_singleton]; omega
  have h3 : ∑ a ∈ ((Ioo (-n) n).filter (fun a => ¬ 0 < a)).filter (fun a => ¬ a = 0), f a
      = ∑ P ∈ Icc 1 (n - 1), f (-P) := by
    refine sum_nbij' (fun a => -a) (fun P => -P) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_filter, mem_Ioo, mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_filter, mem_Ioo, mem_Icc] at ha ⊢; omega
    · intro a _; simp
    · intro a _; simp
    · intro a _; simp
  rw [h1, h2, h3, sum_singleton, add_comm]

/-- The Lagrange summand `W(a,b) = (n−|a|)(n−|b|) z_ab²` (private abbreviation). -/
private def ssW (n : ℕ) (x y : ℤ → R) (a b : ℤ) : R :=
  ((((n : ℤ) - |a|) * ((n : ℤ) - |b|) : ℤ) : R) * wedge x y a b ^ 2

private lemma ssW_symm (n : ℕ) (x y : ℤ → R) (a b : ℤ) : ssW n x y a b = ssW n x y b a := by
  unfold ssW; rw [wedge_swap x y a b, neg_sq, mul_comm ((n : ℤ) - |b|)]

private lemma ssW_self (n : ℕ) (x y : ℤ → R) (a : ℤ) : ssW n x y a a = 0 := by
  unfold ssW; rw [wedge_self]; ring

/-- (nine-block split of the weighted Lagrange sum). -/
theorem split9 (n : ℕ) (hn : 1 ≤ n) (x y : ℤ → R) :
    ∑ a ∈ Ioo (-(n : ℤ)) n, ∑ b ∈ Ioo (-(n : ℤ)) n,
        ((((n : ℤ) - |a|) * ((n : ℤ) - |b|) : ℤ) : R) * wedge x y a b ^ 2
      = central n x y
        + 2 * ∑ A ∈ Icc (1 : ℤ) ((n : ℤ) - 1), ∑ B ∈ Icc (1 : ℤ) ((n : ℤ) - 1),
            ((((n : ℤ) - A) * ((n : ℤ) - B) : ℤ) : R) * wedge x y (-A) B ^ 2
        + 2 * ssdiag n x y + 2 * ssdiag n (fun i => x (-i)) (fun i => y (-i)) := by
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  show ∑ a ∈ Ioo (-(n : ℤ)) n, ∑ b ∈ Ioo (-(n : ℤ)) n, ssW n x y a b = _
  set I := Icc (1 : ℤ) ((n : ℤ) - 1) with hI
  rw [split_Ioo _ hn']
  simp only [split_Ioo _ hn', sum_add_distrib]
  -- the nine blocks
  have h00 : ssW n x y 0 0 = 0 := ssW_self n x y 0
  have hC : ∑ Q ∈ I, ssW n x y 0 (-Q) + ∑ Q ∈ I, ssW n x y 0 Q + ∑ P ∈ I, ssW n x y (-P) 0
      + ∑ P ∈ I, ssW n x y P 0 = central n x y := by
    unfold central
    rw [← hI]
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun P hP => ?_
    have hP0 : 0 < P := by rw [hI, mem_Icc] at hP; omega
    simp only [ssW, abs_zero, abs_neg, abs_of_pos hP0]
    push_cast
    unfold wedge; ring
  have hM : ∑ P ∈ I, ∑ Q ∈ I, ssW n x y (-P) Q + ∑ P ∈ I, ∑ Q ∈ I, ssW n x y P (-Q)
      = 2 * ∑ A ∈ I, ∑ B ∈ I, ((((n : ℤ) - A) * ((n : ℤ) - B) : ℤ) : R) * wedge x y (-A) B ^ 2 := by
    rw [sum_comm (s := I) (t := I) (f := fun P Q => ssW n x y P (-Q)), two_mul]
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun A hA => sum_congr rfl fun B hB => ?_
    have hA0 : 0 < A := by rw [hI, mem_Icc] at hA; omega
    have hB0 : 0 < B := by rw [hI, mem_Icc] at hB; omega
    rw [ssW_symm n x y B (-A)]
    simp only [ssW, abs_neg, abs_of_pos hA0, abs_of_pos hB0]
  have hS : ∑ P ∈ I, ∑ Q ∈ I, ssW n x y P Q = 2 * ssdiag n x y := by
    rw [hI, sum_symm_offdiag_Ioc _ _ (ssW_symm n x y) (ssW_self n x y)]
    unfold ssdiag
    congr 1
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    have hi0 : 0 < i := by rw [mem_Icc] at hi; omega
    have hj0 : 0 < j := by rw [mem_Ioc] at hj; omega
    simp only [ssW, abs_of_pos hi0, abs_of_pos hj0]
  have hSn : ∑ P ∈ I, ∑ Q ∈ I, ssW n x y (-P) (-Q)
      = 2 * ssdiag n (fun i => x (-i)) (fun i => y (-i)) := by
    rw [hI, sum_symm_offdiag_Ioc _ (fun P Q => ssW n x y (-P) (-Q))
      (fun P Q => ssW_symm n x y (-P) (-Q)) (fun P => ssW_self n x y (-P))]
    unfold ssdiag
    congr 1
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    have hi0 : 0 < i := by rw [mem_Icc] at hi; omega
    have hj0 : 0 < j := by rw [mem_Ioc] at hj; omega
    simp only [ssW, abs_neg, abs_of_pos hi0, abs_of_pos hj0]
    rfl
  linear_combination h00 + hC + hM + hS + hSn

/-! ### The same-side Plücker part of the tent form -/

/-- Same-side window as a τ-filter of `Dset` (gap `δ ≥ 0`, depth `k ≥ 0`). -/
private lemma ss_Icc_eq_filter (n δ k : ℤ) (hδ : 0 ≤ δ) (hk : 0 ≤ k) :
    Icc (k + 1) (n - 1 - δ - k)
      = (Dset n δ).filter (fun P => k < min (tau n P) (tau n (P + δ))) := by
  ext P; simp only [Dset, mem_filter, mem_Icc]; simp only [tau]; omega

/-- The linear reindexing `(d, P, P') ↦ (δ, p, q) = (P' − P, P + d, P)` on `P < P'`. -/
private lemma ss_reindex {M : Type*} [AddCommMonoid M] (n : ℤ) (G : ℤ → ℤ → ℤ → M) :
    ∑ d ∈ Ioo (-n) n, ∑ P ∈ Dset n d, ∑ P' ∈ (Dset n d).filter (P < ·), G d P P'
      = ∑ δ ∈ Icc 1 (n - 2), ∑ p ∈ Dset n δ, ∑ q ∈ Dset n δ, G (p - q) q (q + δ) := by
  have hL : ∀ d, ∑ P ∈ Dset n d, ∑ P' ∈ (Dset n d).filter (P < ·), G d P P'
      = ∑ a ∈ (Dset n d).sigma (fun P => (Dset n d).filter (P < ·)), G d a.1 a.2 :=
    fun d => sum_sigma' _ _ _
  simp_rw [hL, ← sum_product' (Dset n _) (Dset n _)]
  rw [sum_sigma', sum_sigma']
  refine Finset.sum_bij'
    (fun a _ => (⟨a.2.2 - a.2.1, (a.2.1 + a.1, a.2.1)⟩ : Σ _ : ℤ, ℤ × ℤ))
    (fun b _ => (⟨b.2.1 - b.2.2, ⟨b.2.2, b.2.2 + b.1⟩⟩ : Σ _ : ℤ, Σ _ : ℤ, ℤ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, P, P'⟩ h
    simp only [Dset, mem_sigma, mem_product, mem_filter, mem_Ioo, mem_Icc] at h ⊢; omega
  · rintro ⟨δ, p, q⟩ h
    simp only [Dset, mem_sigma, mem_product, mem_filter, mem_Ioo, mem_Icc] at h ⊢; omega
  · rintro ⟨d, P, P'⟩ _
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]; omega
  · rintro ⟨δ, p, q⟩ _
    simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, and_true]; omega
  · rintro ⟨d, P, P'⟩ _
    dsimp only
    rw [show P + d - P = d by ring, show P + (P' - P) = P' by ring]

/-- The same-side summand of the tent form (private abbreviation). -/
private def ssG (n : ℕ) (x y : ℤ → R) (d P P' : ℤ) : R :=
  ((tent4 n d P P' : ℤ) : R) * (wedge x y (-P) (-P') * wedge x y (P + d) (P' + d))

private lemma ssG_symm (n : ℕ) (x y : ℤ → R) (d P P' : ℤ) : ssG n x y d P P' = ssG n x y d P' P := by
  unfold ssG
  rw [tent4_comm]
  unfold wedge; ring

private lemma ssG_self (n : ℕ) (x y : ℤ → R) (d P : ℤ) : ssG n x y d P P = 0 := by
  unfold ssG; rw [wedge_self]; ring

private lemma ssG_reindexed (n : ℕ) (x y : ℤ → R) (δ p q : ℤ) :
    ssG n x y (p - q) q (q + δ)
      = -(((min (min (tau n p) (tau n (p + δ))) (min (tau n q) (tau n (q + δ))) : ℤ) : R)
          * (wedge x y p (p + δ) * wedge x y (-(q + δ)) (-q))) := by
  unfold ssG tent4
  rw [show q + (p - q) = p by ring, show q + δ + (p - q) = p + δ by ring]
  have ht : min (min (tau n q) (tau n p)) (min (tau n (q + δ)) (tau n (p + δ)))
      = min (min (tau n p) (tau n (p + δ))) (min (tau n q) (tau n (q + δ))) := by
    simp only [tau]; omega
  rw [ht, wedge_swap x y (-(q + δ)) (-q)]
  ring

/-- (same-side Plücker part of the tent form):
`∑_d ∑_{P,P' ∈ Dset d} tent4 · z(−P,−P′) z(P+d,P′+d) = −2 ∑_{δ,k} S⁺_{δ,k} S⁻_{δ,k}`. -/
theorem sameside_tent (n : ℕ) (x y : ℤ → R) :
    ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d,
        ((tent4 n d P P' : ℤ) : R) * (wedge x y (-P) (-P') * wedge x y (P + d) (P' + d))
      = -2 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
          Splus n x y δ k * Sminus n x y δ k := by
  show ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d, ssG n x y d P P' = _
  -- symmetrize, then reindex linearly
  simp only [fun d => sum_symm_offdiag (Dset n d) (ssG n x y d) (ssG_symm n x y d)
    (ssG_self n x y d), ← mul_sum]
  rw [ss_reindex (n : ℤ) (ssG n x y)]
  simp only [ssG_reindexed, sum_neg_distrib]
  -- the right side: windows are τ-filters, then the tent-kernel identity
  have hR : ∀ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2),
      ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1), Splus n x y δ k * Sminus n x y δ k
        = ∑ p ∈ Dset n δ, ∑ q ∈ Dset n δ,
            ((min (min (tau n p) (tau n (p + δ))) (min (tau n q) (tau n (q + δ))) : ℤ) : R)
              * (wedge x y p (p + δ) * wedge x y (-(q + δ)) (-q)) := by
    intro δ hδ
    rw [mem_Icc] at hδ
    have hw : ∀ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1), Splus n x y δ k * Sminus n x y δ k
        = (∑ P ∈ (Dset n δ).filter (fun P => k < min (tau n P) (tau n (P + δ))),
              wedge x y P (P + δ))
          * (∑ Q ∈ (Dset n δ).filter (fun Q => k < min (tau n Q) (tau n (Q + δ))),
              wedge x y (-(Q + δ)) (-Q)) := by
      intro k hk
      rw [mem_Ico] at hk
      unfold Splus Sminus
      rw [ss_Icc_eq_filter _ _ _ (by omega) hk.1]
    rw [sum_congr rfl hw]
    exact sum_win_mul (Dset n δ) (fun P => min (tau n P) (tau n (P + δ))) ((n : ℤ) - 1)
      (fun P hP => by simp only [Dset, tau, mem_filter, mem_Icc] at hP ⊢; omega)
      (fun P => wedge x y P (P + δ)) (fun Q => wedge x y (-(Q + δ)) (-Q))
  rw [sum_congr rfl hR]
  ring

end Generic

end ToeplitzSOS.ThmA

end
