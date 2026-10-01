import ToeplitzSOS.ThmA.Defs
import Mathlib

/-!
# Finite-sum reindexing for signed Toeplitz indices

Integer-interval and block decompositions used in the commutator identity.
-/

open Finset

noncomputable section

namespace ToeplitzSOS.ThmA

/-- Mixed wedges `z_{−P, P+d}` on the diagonal `d`: `P, P + d ∈ [1, n−1]`. -/
def Dset (n d : ℤ) : Finset ℤ := (Icc 1 (n - 1)).filter (fun P => 1 ≤ P + d ∧ P + d ≤ n - 1)

/-- A sum over `Fin n` is a sum over the integer interval `[0, n)`. -/
lemma sum_fin_eq_sum_Ico {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℤ → M) :
    ∑ i : Fin n, f (i : ℤ) = ∑ i ∈ Ico (0 : ℤ) n, f i := by
  refine Finset.sum_bij' (fun i _ => (i : ℤ)) (fun a ha => ⟨a.toNat, by simp only [mem_Ico] at ha; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro i _; simp only [mem_Ico]; omega
  · intro a _; simp
  · intro i _; apply Fin.ext; simp
  · intro a ha; simp only [mem_Ico] at ha; simp only; omega
  · intro i _; rfl

/-- , double-sum form. -/
lemma sum_fin_fin_eq_sum_Ico {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℤ → ℤ → M) :
    ∑ i : Fin n, ∑ j : Fin n, F (i : ℤ) (j : ℤ)
      = ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (0 : ℤ) n, F i j := by
  rw [← sum_fin_eq_sum_Ico n (fun i => ∑ j ∈ Ico (0 : ℤ) n, F i j)]
  refine sum_congr rfl fun i _ => ?_
  exact sum_fin_eq_sum_Ico n (fun j => F i j)

/-- A rectangle `[0, α) × [0, β)` summed along its diagonals `s = a − b`. -/
lemma rect_reindex {R : Type*} [AddCommMonoid R] (α β : ℤ) (F : ℤ → ℤ → R) :
    ∑ a ∈ Ico 0 α, ∑ b ∈ Ico 0 β, F a b =
      ∑ s ∈ Ioo (-β) α, ∑ r ∈ Ico 0 (min (α - max s 0) (β - max (-s) 0)),
        F (r + max s 0) (r + max (-s) 0) := by
  rw [← sum_product', sum_sigma']
  refine Finset.sum_bij' (fun p _ => (⟨p.1 - p.2, min p.1 p.2⟩ : Σ _ : ℤ, ℤ))
    (fun q _ => (q.2 + max q.1 0, q.2 + max (-q.1) 0)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h; simp only [mem_product, mem_Ico, mem_sigma, mem_Ioo] at h ⊢; omega
  · rintro ⟨s, r⟩ h; simp only [mem_product, mem_Ico, mem_sigma, mem_Ioo] at h ⊢; omega
  · rintro ⟨a, b⟩ _; simp only [Prod.mk.injEq]; omega
  · rintro ⟨s, r⟩ _; simp only [Sigma.mk.injEq, heq_eq_eq]; omega
  · rintro ⟨a, b⟩ _; dsimp only; congr 1 <;> omega

/-- The diagonal lengths of an `α × β` rectangle add up to `αβ`. -/
lemma rect_count (α β : ℤ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∑ s ∈ Ioo (-β) α, min (α - max s 0) (β - max (-s) 0) = α * β := by
  have key : ∀ s ∈ Ioo (-β) α, min (α - max s 0) (β - max (-s) 0)
      = ∑ _r ∈ Ico 0 (min (α - max s 0) (β - max (-s) 0)), (1 : ℤ) := by
    intro s hs; simp only [mem_Ioo] at hs
    rw [sum_const, Int.card_Ico, nsmul_eq_mul, mul_one, sub_zero, Int.toNat_of_nonneg (by omega)]
  rw [sum_congr rfl key]
  have h := rect_reindex α β (fun _ _ => (1 : ℤ))
  rw [← h]
  simp only [sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul, mul_one, Int.toNat_of_nonneg hα,
    Int.toNat_of_nonneg hβ]

/-- `∑_{a,b<n} f(a − b) = ∑_{|d|<n} (n − |d|) f(d)`. -/
lemma square_diag_sum {R : Type*} [CommRing R] (n : ℤ) (f : ℤ → R) :
    ∑ a ∈ Ico 0 n, ∑ b ∈ Ico 0 n, f (a - b) = ∑ d ∈ Ioo (-n) n, ((n - |d| : ℤ) : R) * f d := by
  rw [rect_reindex]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [mem_Ioo] at hd
  have e : ∀ r, r + max d 0 - (r + max (-d) 0) = d := fun r => by omega
  simp only [e, sum_const, Int.card_Ico, nsmul_eq_mul]
  congr 1
  have : min (n - max d 0) (n - max (-d) 0) - 0 = n - |d| := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  have hnn : 0 ≤ n - |d| := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  rw [this, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]

/-- (counting): `#{0 ≤ k < K : k < a ∧ k < b} = min(a, b)` for `0 ≤ a ≤ K`, `0 ≤ b`. -/
lemma card_filter_lt_min (K a b : ℤ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (haK : a ≤ K) :
    ((Ico 0 K).filter (fun k => k < a ∧ k < b)).card = (min a b).toNat := by
  have : (Ico 0 K).filter (fun k => k < a ∧ k < b) = Ico 0 (min a b) := by
    ext k; simp only [mem_filter, mem_Ico]; omega
  rw [this, Int.card_Ico, sub_zero]

/-- (nested windows): `∑_k (∑_{φP>k} u_P)(∑_{φQ>k} v_Q) = ∑_{P,Q} min(φP, φQ) u_P v_Q`. Used by `frob_comm_tent`, `sameside_tent`,
`Symmetric.adPart_expand`. -/
lemma sum_win_mul {R : Type*} [CommRing R] (D : Finset ℤ) (φ : ℤ → ℤ) (K : ℤ)
    (hφ : ∀ P ∈ D, 0 ≤ φ P ∧ φ P ≤ K) (u v : ℤ → R) :
    ∑ k ∈ Ico 0 K, (∑ P ∈ D.filter (fun P => k < φ P), u P) *
        (∑ Q ∈ D.filter (fun Q => k < φ Q), v Q)
      = ∑ P ∈ D, ∑ Q ∈ D, ((min (φ P) (φ Q) : ℤ) : R) * (u P * v Q) := by
  simp_rw [sum_filter, sum_mul_sum, ite_zero_mul_ite_zero]
  rw [sum_comm]
  refine sum_congr rfl fun P hP => ?_
  rw [sum_comm]
  refine sum_congr rfl fun Q hQ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul,
    card_filter_lt_min K _ _ (hφ P hP).1 (hφ Q hQ).1 (hφ P hP).2]
  congr 1
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_min (hφ P hP).1 (hφ Q hQ).1)]

/-- Reindexing `(d, P, P')` over `Dset n d` by the antidiagonal `σ` of the mixed
σ-blocks. -/
lemma diag_to_sigma {M : Type*} [AddCommMonoid M] (n : ℤ) (F : ℤ → ℤ → ℤ → M) :
    ∑ d ∈ Ioo (-n) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d, F d P P' =
      ∑ σ ∈ Icc 2 (2 * n - 2), ∑ A ∈ blk n σ, ∑ A' ∈ blk n σ, F (σ - A - A') A A' := by
  simp_rw [← sum_product' (Dset n _) (Dset n _), ← sum_product' (blk n _) (blk n _)]
  rw [sum_sigma', sum_sigma']
  refine Finset.sum_bij' (fun p _ => (⟨p.2.1 + p.2.2 + p.1, (p.2.1, p.2.2)⟩ : Σ _ : ℤ, ℤ × ℤ))
    (fun q _ => (⟨q.1 - q.2.1 - q.2.2, (q.2.1, q.2.2)⟩ : Σ _ : ℤ, ℤ × ℤ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, P, P'⟩ h
    simp only [Dset, blk, mem_sigma, mem_product, mem_filter, mem_Ioo, mem_Icc] at h ⊢; omega
  · rintro ⟨σ, A, A'⟩ h
    simp only [Dset, blk, mem_sigma, mem_product, mem_filter, mem_Ioo, mem_Icc] at h ⊢; omega
  · rintro ⟨d, P, P'⟩ _; simp only [Sigma.mk.injEq, heq_eq_eq, and_true]; omega
  · rintro ⟨σ, A, A'⟩ _; simp only [Sigma.mk.injEq, heq_eq_eq, and_true]; omega
  · rintro ⟨d, P, P'⟩ _; dsimp only; congr 1; omega

/-- A sum over `[1, n−1]²` regrouped by the antidiagonal `σ = A + B`. -/
lemma AB_to_sigma {M : Type*} [AddCommMonoid M] (n : ℤ) (f : ℤ → ℤ → M) :
    ∑ A ∈ Icc 1 (n - 1), ∑ B ∈ Icc 1 (n - 1), f A B =
      ∑ σ ∈ Icc 2 (2 * n - 2), ∑ A ∈ blk n σ, f A (σ - A) := by
  rw [← sum_product' (Icc 1 (n - 1)) (Icc 1 (n - 1))]
  rw [sum_sigma']
  refine Finset.sum_bij' (fun p _ => (⟨p.1 + p.2, p.1⟩ : Σ _ : ℤ, ℤ))
    (fun q _ => (q.2, q.1 - q.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, B⟩ h
    simp only [blk, mem_sigma, mem_product, mem_Icc] at h ⊢; omega
  · rintro ⟨σ, A⟩ h
    simp only [blk, mem_sigma, mem_product, mem_Icc] at h ⊢; omega
  · rintro ⟨A, B⟩ _; simp
  · rintro ⟨σ, A⟩ _; simp only [Sigma.mk.injEq, heq_eq_eq, and_true]; omega
  · rintro ⟨A, B⟩ _; simp

/-- Expansion of a symmetric Laplacian form `∑_{u,v} c_{uv} (f_u − f_v)²`. -/
lemma laplacian_sum {R : Type*} [CommRing R] (S : Finset ℤ) (c : ℤ → ℤ → R)
    (hc : ∀ u v, c u v = c v u) (f : ℤ → R) :
    ∑ u ∈ S, ∑ v ∈ S, c u v * (f u - f v) ^ 2
      = 2 * ∑ u ∈ S, (∑ v ∈ S, c u v) * f u ^ 2 - 2 * ∑ u ∈ S, ∑ v ∈ S, c u v * (f u * f v) := by
  have e : ∀ u v, c u v * (f u - f v) ^ 2
      = c u v * f u ^ 2 + c u v * f v ^ 2 - 2 * (c u v * (f u * f v)) := fun u v => by ring
  simp_rw [e, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  have hswap : ∑ u ∈ S, ∑ v ∈ S, c u v * f v ^ 2 = ∑ u ∈ S, ∑ v ∈ S, c u v * f u ^ 2 := by
    rw [sum_comm]; simp_rw [hc]
  rw [hswap]; simp_rw [sum_mul]; ring

/-- A symmetric double sum with zero diagonal is twice its strict upper part. -/
lemma sum_symm_offdiag {R : Type*} [CommRing R] (S : Finset ℤ) (f : ℤ → ℤ → R)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    ∑ i ∈ S, ∑ j ∈ S, f i j = 2 * ∑ i ∈ S, ∑ j ∈ S.filter (i < ·), f i j := by
  have h1 : ∀ i, ∑ j ∈ S, f i j
      = ∑ j ∈ S.filter (i < ·), f i j + ∑ j ∈ S.filter (fun j => j < i), f i j := by
    intro i
    rw [← sum_filter_add_sum_filter_not S (fun j => i < j)]
    congr 1
    rw [← sum_filter_add_sum_filter_not (S.filter (fun j => ¬ i < j)) (fun j => j < i)]
    have h0 : ∑ j ∈ (S.filter (fun j => ¬ i < j)).filter (fun j => ¬ j < i), f i j = 0 := by
      refine sum_eq_zero fun j hj => ?_
      simp only [mem_filter] at hj
      have : j = i := by omega
      rw [this, hd]
    rw [h0, add_zero, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext j; simp only [mem_filter]; exact and_congr_right fun _ => by omega
  simp_rw [h1]
  rw [sum_add_distrib, two_mul]
  congr 1
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  rw [hs]

/-- `{j ∈ [1, m] : i < j} = (i, m]` for `i ∈ [1, m]`. -/
lemma filter_Icc_lt_eq_Ioc (m i : ℤ) (hi : i ∈ Icc 1 m) : (Icc 1 m).filter (i < ·) = Ioc i m := by
  simp only [mem_Icc] at hi
  ext j; simp only [mem_filter, mem_Icc, mem_Ioc]; omega

/-- On `[1, m]`, with the strict upper part written over `Ioc i m`. -/
lemma sum_symm_offdiag_Ioc {R : Type*} [CommRing R] (m : ℤ) (f : ℤ → ℤ → R)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    ∑ i ∈ Icc 1 m, ∑ j ∈ Icc 1 m, f i j = 2 * ∑ i ∈ Icc 1 m, ∑ j ∈ Ioc i m, f i j := by
  rw [sum_symm_offdiag _ f hs hd]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [filter_Icc_lt_eq_Ioc m i hi]

end ToeplitzSOS.ThmA

end
