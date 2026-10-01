import ToeplitzSOS.ThmA.Commutator
import ToeplitzSOS.ThmA.Mixed
import ToeplitzSOS.ThmA.SameSide
import ToeplitzSOS.ThmA.Poly
import Mathlib

/-!
# Assembly of the residual-form decomposition

The commutator, mixed-block, same-side, and polynomial identities express
the Toeplitz quartic as explicit squares plus two residual forms.
Consequently an SOS certificate for the residual form gives one for the quartic.
-/

open Finset

noncomputable section

namespace ToeplitzSOS.ThmA

section Generic
variable {R : Type*} [CommRing R]

/-- The commutator tent form split into its mixed σ-block part and its same-side part
`−4 ∑_{δ,k} S⁺_{δ,k} S⁻_{δ,k}` (Plücker `plucker_diag` on the tent form). Used by `thmA_gram`. -/
theorem frob_comm_split (n : ℕ) (x y : ℤ → R) :
    ToeplitzSOS.frob (tmat n x * tmat n y - tmat n y * tmat n x)
      = 2 * ∑ σ ∈ Icc (2 : ℤ) (2 * (n : ℤ) - 2), ∑ A ∈ blk n σ, ∑ A' ∈ blk n σ,
          ((gcoef n σ A A' : ℤ) : R) *
            (wedge x y (-A) (σ - A) * wedge x y (-A') (σ - A'))
        - 4 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            Splus n x y δ k * Sminus n x y δ k := by
  rw [frob_comm_tent]
  have hmixed :
      ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d,
          ((tent4 n d P P' : ℤ) : R) *
            (wedge x y (-P) (P' + d) * wedge x y (-P') (P + d))
        = ∑ σ ∈ Icc (2 : ℤ) (2 * (n : ℤ) - 2), ∑ A ∈ blk n σ, ∑ A' ∈ blk n σ,
            ((gcoef n σ A A' : ℤ) : R) *
              (wedge x y (-A) (σ - A) * wedge x y (-A') (σ - A')) := by
    rw [diag_to_sigma]
    refine sum_congr rfl fun σ _ => sum_congr rfl fun A _ => sum_congr rfl fun A' _ => ?_
    have ht : tent4 (n : ℤ) (σ - A - A') A A' = gcoef n σ A A' := by
      unfold tent4 gcoef
      rw [show A + (σ - A - A') = σ - A' by ring,
        show A' + (σ - A - A') = σ - A by ring]
      omega
    rw [ht]
    rw [show A' + (σ - A - A') = σ - A by ring,
      show A + (σ - A - A') = σ - A' by ring]
  have hsplit :
      ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d,
          ((tent4 n d P P' : ℤ) : R) *
            (wedge x y (-P) (P + d) * wedge x y (-P') (P' + d))
        = (∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d,
            ((tent4 n d P P' : ℤ) : R) *
              (wedge x y (-P) (P' + d) * wedge x y (-P') (P + d)))
          + ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d,
              ((tent4 n d P P' : ℤ) : R) *
                (wedge x y (-P) (-P') * wedge x y (P + d) (P' + d)) := by
    simp_rw [plucker_diag]
    simp only [mul_add, sum_add_distrib]
  rw [hsplit, hmixed, sameside_tent]
  ring

/-- Residual-form decomposition in Gram form (`n ≥ 1`, any commutative ring):
`F_n = central + lap + slack + 2 ssdiag(x, y) + 2 ssdiag(x̃, ỹ) + 4 ∑_{δ,k} S⁺ S⁻`,
`x̃_i = x_{−i}`. Used by `thmA`. -/
theorem thmA_gram (n : ℕ) (hn : 1 ≤ n) (x y : ℤ → R) :
    bw n x y = central n x y + lap n x y + slack n x y
      + 2 * ssdiag n x y + 2 * ssdiag n (fun i => x (-i)) (fun i => y (-i))
      + 4 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
          Splus n x y δ k * Sminus n x y δ k := by
  have hweights := weights_lagrange n x y
  have hsplit := split9 n hn x y
  have hmixed := mixed_block n x y
  have hcomm := frob_comm_split n x y
  unfold bw
  linear_combination hweights + hsplit + hmixed - hcomm

/-- The all-order identity over an arbitrary commutative ring, for
every `n ≥ 1`: `F_n = explicitPart + 2 H_{n−1}(x̃, ỹ) + 2 H_{n−1}(x, y)` with `x̃_i = x_{−i}`. Used by `toeplitzBW_thmA`. -/
theorem thmA (n : ℕ) (hn : 1 ≤ n) (x y : ℤ → R) :
    bw n x y = explicitPart n x y
      + 2 * Hform (n - 1) (fun i => x (-i)) (fun i => y (-i)) + 2 * Hform (n - 1) x y := by
  have hgram := thmA_gram n hn x y
  have hplus := Hform_split n x y
  have hminus := Hform_split_neg n x y
  have hcross : cross n x y
      = 2 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            Splus n x y δ k ^ 2
        + 2 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            Sminus n x y δ k ^ 2
        + 4 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            Splus n x y δ k * Sminus n x y δ k := by
    have hsum :
        ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            (Splus n x y δ k + Sminus n x y δ k) ^ 2
          = (∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
              Splus n x y δ k ^ 2)
            + (∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
                Sminus n x y δ k ^ 2)
            + 2 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
                Splus n x y δ k * Sminus n x y δ k := by
      calc
        _ = ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
            (Splus n x y δ k ^ 2 + Sminus n x y δ k ^ 2
              + 2 * (Splus n x y δ k * Sminus n x y δ k)) := by
                refine sum_congr rfl fun δ _ => sum_congr rfl fun k _ => ?_
                ring
        _ = _ := by simp only [sum_add_distrib, ← mul_sum]
    unfold cross
    rw [hsum]
    ring
  unfold explicitPart
  linear_combination hgram - 2 * hminus - 2 * hplus - hcross

end Generic

/-- The residual-form decomposition specialized to the catalogue polynomial:
`toeplitzBW n = explicitPart + 2 ι₋(Hpoly (n−1)) + 2 ι₊(Hpoly (n−1))` (`n ≥ 1`). Used by `isSumSqHomQuad_of_Hpoly`. -/
theorem toeplitzBW_thmA (n : ℕ) (hn : 1 ≤ n) :
    ToeplitzSOS.toeplitzBW n = explicitPart n (sv n .x) (sv n .y)
      + 2 * MvPolynomial.rename (ιminus n) (Hpoly (n - 1))
      + 2 * MvPolynomial.rename (ιplus n) (Hpoly (n - 1)) := by
  rw [toeplitzBW_eq_bw, thmA n hn, rename_Hpoly_minus, rename_Hpoly_plus]

/-- Per-order reduction from an SOS certificate for `H_{n-1}` to one for `F_n`
(`n ≥ 2`). Used by the generated certificates `N10`–`N20`. -/
theorem isSumSqHomQuad_of_Hpoly (n : ℕ) (hn : 2 ≤ n)
    (h : ToeplitzSOS.IsSumSqHomQuad (Hpoly (n - 1))) :
    ToeplitzSOS.IsSumSqHomQuad (ToeplitzSOS.toeplitzBW n) := by
  rw [toeplitzBW_thmA n (by omega), ← mem_sosCone_iff]
  have hexp : explicitPart n (sv n .x) (sv n .y) ∈ sosCone (ToeplitzSOS.V n) :=
    mem_sosCone_iff.mpr (explicitPart_isSumSqHomQuad n)
  have hminus : MvPolynomial.rename (ιminus n) (Hpoly (n - 1)) ∈ sosCone (ToeplitzSOS.V n) :=
    mem_sosCone_iff.mpr (h.rename (ιminus n))
  have hplus : MvPolynomial.rename (ιplus n) (Hpoly (n - 1)) ∈ sosCone (ToeplitzSOS.V n) :=
    mem_sosCone_iff.mpr (h.rename (ιplus n))
  have h2minus : 2 * MvPolynomial.rename (ιminus n) (Hpoly (n - 1)) ∈ sosCone (ToeplitzSOS.V n) := by
    rw [two_mul]
    exact sosCone_add hminus hminus
  have h2plus : 2 * MvPolynomial.rename (ιplus n) (Hpoly (n - 1)) ∈ sosCone (ToeplitzSOS.V n) := by
    rw [two_mul]
    exact sosCone_add hplus hplus
  exact sosCone_add (sosCone_add hexp h2minus) h2plus

end ToeplitzSOS.ThmA

end
