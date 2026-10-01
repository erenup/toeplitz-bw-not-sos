import ToeplitzSOS.ThmA.Defs
import ToeplitzSOS.ThmA.Reindex
import Mathlib

/-!
# Mixed blocks of the Toeplitz quartic

The Plücker identity, row sums, and mixed-block decomposition.
-/

open Finset

noncomputable section

namespace ToeplitzSOS.ThmA

/-- (Plücker, diagonal form): the only non-formal step of the residual-form decomposition,
`z_{−P,P+d} z_{−P',P'+d} = z_{−P,P'+d} z_{−P',P+d} + z_{−P,−P'} z_{P+d,P'+d}`. Used by `frob_comm_split`. -/
lemma plucker_diag {R : Type*} [CommRing R] (x y : ℤ → R) (P P' d : ℤ) :
    wedge x y (-P) (P + d) * wedge x y (-P') (P' + d)
      = wedge x y (-P) (P' + d) * wedge x y (-P') (P + d)
        + wedge x y (-P) (-P') * wedge x y (P + d) (P' + d) := by
  unfold wedge; ring

/-- Row sums of the mixed σ-blocks: `∑_{A'} g = (n−A)(n−B) − n·max(n−σ, 0)`. -/
lemma rowsum (n σ A : ℤ) (hA : A ∈ blk n σ) :
    ∑ A' ∈ blk n σ, gcoef n σ A A' = (n - A) * (n - (σ - A)) - n * max (n - σ) 0 := by
  simp only [blk, mem_Icc] at hA
  have hre : ∑ A' ∈ blk n σ, gcoef n σ A A'
      = ∑ s ∈ Ioo (-(min (σ - A) (n - A))) (min A (n - (σ - A))),
          min (min A (n - (σ - A)) - max s 0) (min (σ - A) (n - A) - max (-s) 0) := by
    refine Finset.sum_nbij' (fun A' => A - A') (fun s => A - s) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [blk, mem_Icc, mem_Ioo] at ha ⊢; omega
    · intro a ha; simp only [blk, mem_Icc, mem_Ioo] at ha ⊢; omega
    · intro a _; ring
    · intro a _; ring
    · intro a ha; simp only [blk, mem_Icc] at ha; simp only [gcoef, tau]; omega
  rw [hre, rect_count _ _ (by omega) (by omega)]
  rcases le_total n σ with h | h
  · rw [min_eq_right (by omega : n - (σ - A) ≤ A), min_eq_right (by omega : n - A ≤ σ - A),
      max_eq_right (by omega : n - σ ≤ 0)]; ring
  · rw [min_eq_left (by omega : A ≤ n - (σ - A)), min_eq_left (by omega : σ - A ≤ n - A),
      max_eq_left (by omega : 0 ≤ n - σ)]; ring

/-- The Laplacian weight `gcoef` is symmetric in `A, A'`. -/
lemma gcoef_symm (n σ A A' : ℤ) : gcoef n σ A A' = gcoef n σ A' A := by
  unfold gcoef; omega

/-- Slack rewritten over σ-blocks. -/
private lemma slack_eq_sigma {R : Type*} [CommRing R] (n : ℕ) (x y : ℤ → R) :
    slack n x y = ∑ σ ∈ Icc (2 : ℤ) (2 * (n : ℤ) - 2), ∑ A ∈ blk n σ,
      ((2 * (n : ℤ) * max ((n : ℤ) - σ) 0 : ℤ) : R) * wedge x y (-A) (σ - A) ^ 2 := by
  have h0 := AB_to_sigma ((n : ℤ)) (fun A B =>
    ((2 * (n : ℤ) * max ((n : ℤ) - (A + B)) 0 : ℤ) : R) * wedge x y (-A) B ^ 2)
  simp only [add_sub_cancel] at h0
  rw [← h0]
  unfold slack
  refine sum_congr rfl fun A hA => ?_
  simp only [mem_Icc] at hA
  have hsub : Icc (1 : ℤ) ((n : ℤ) - 1 - A) ⊆ Icc (1 : ℤ) ((n : ℤ) - 1) := by
    intro B hB; simp only [mem_Icc] at hB ⊢; omega
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun B hB => ?_
    simp only [mem_Icc] at hB
    rw [max_eq_left (by omega)]
    congr 2; ring
  · intro B hB hB'
    simp only [mem_Icc] at hB hB'
    rw [max_eq_right (by omega)]; simp

/-- (Theorem B, `mixed_block`): the mixed diagonal minus the σ-block form equals
Laplacian plus slack, `lap n x y + slack n x y`. Used by `thmA_gram`. -/
theorem mixed_block {R : Type*} [CommRing R] (n : ℕ) (x y : ℤ → R) :
    2 * ∑ A ∈ Icc (1 : ℤ) ((n : ℤ) - 1), ∑ B ∈ Icc (1 : ℤ) ((n : ℤ) - 1),
        ((((n : ℤ) - A) * ((n : ℤ) - B) : ℤ) : R) * wedge x y (-A) B ^ 2
      - 2 * ∑ σ ∈ Icc (2 : ℤ) (2 * (n : ℤ) - 2), ∑ A ∈ blk n σ, ∑ A' ∈ blk n σ,
          ((gcoef n σ A A' : ℤ) : R) * (wedge x y (-A) (σ - A) * wedge x y (-A') (σ - A'))
      = lap n x y + slack n x y := by
  rw [AB_to_sigma ((n : ℤ)) (fun A B =>
    ((((n : ℤ) - A) * ((n : ℤ) - B) : ℤ) : R) * wedge x y (-A) B ^ 2)]
  rw [slack_eq_sigma]
  unfold lap
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun σ _ => ?_
  rw [laplacian_sum (blk n σ) (fun A A' => ((gcoef n σ A A' : ℤ) : R)) (fun u v => by
    rw [gcoef_symm]) (fun A => wedge x y (-A) (σ - A))]
  have hrow : ∑ A ∈ blk n σ, (∑ A' ∈ blk n σ, ((gcoef n σ A A' : ℤ) : R)) * wedge x y (-A) (σ - A) ^ 2
      = ∑ A ∈ blk n σ, ((((n : ℤ) - A) * ((n : ℤ) - (σ - A)) : ℤ) : R) * wedge x y (-A) (σ - A) ^ 2
        - ∑ A ∈ blk n σ, ((n * max ((n : ℤ) - σ) 0 : ℤ) : R) * wedge x y (-A) (σ - A) ^ 2 := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun A hA => ?_
    rw [← Int.cast_sum, rowsum _ _ _ hA, ← sub_mul]
    push_cast; ring
  have hs : 2 * ∑ A ∈ blk n σ, ((n * max ((n : ℤ) - σ) 0 : ℤ) : R) * wedge x y (-A) (σ - A) ^ 2
      = ∑ A ∈ blk n σ, ((2 * (n : ℤ) * max ((n : ℤ) - σ) 0 : ℤ) : R) * wedge x y (-A) (σ - A) ^ 2 := by
    rw [mul_sum]; refine sum_congr rfl fun A _ => ?_; push_cast; ring
  linear_combination (-2) * hrow + hs

end ToeplitzSOS.ThmA

end
