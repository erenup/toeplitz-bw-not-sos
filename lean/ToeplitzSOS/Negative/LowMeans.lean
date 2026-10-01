import Mathlib

/-!
# The finite least-degree argument for complete low means

If a real sum of polynomial squares has no coefficient below degree `2m`,
then every square root polynomial has no coefficient below degree `m`.
It constrains only complete low means, never incomplete high means.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Polynomial Finset

/-- At the first potentially nonzero degree, a square has the square of the
corresponding coefficient. No higher coefficient can contribute. -/
theorem coeff_sq_of_low_zero (q : Polynomial ℝ) (g : ℕ)
    (hq : ∀ k < g, q.coeff k = 0) :
    (q ^ 2).coeff (2 * g) = q.coeff g ^ 2 := by
  rw [pow_two, Polynomial.coeff_mul]
  rw [sum_eq_single (g, g)]
  · simp [pow_two]
  · intro ab hab hne
    have hs : ab.1 + ab.2 = 2 * g := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hlt : ab.1 < g ∨ ab.2 < g := by
      by_contra h
      push Not at h
      have he : ab = (g, g) := Prod.ext (by omega) (by omega)
      exact hne he
    rcases hlt with hlt | hlt
    · rw [hq _ hlt, zero_mul]
    · rw [hq _ hlt, mul_zero]
  · intro hnot
    exact (hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega))).elim

/-- Complete low coefficients of every summand vanish whenever the sum of
squares has no terms below twice the cutoff. -/
theorem sum_squares_low_coefficients {ι : Type*} [Fintype ι]
    (q : ι → Polynomial ℝ) (m : ℕ)
    (hq : ∀ k < 2 * m, (∑ j, q j ^ 2).coeff k = 0) :
    ∀ g < m, ∀ j, (q j).coeff g = 0 := by
  intro g
  induction g using Nat.strong_induction_on with
  | h g ih =>
    intro hg j
    have hc := hq (2 * g) (by omega)
    have he : (∑ j, q j ^ 2).coeff (2 * g) = ∑ j, (q j).coeff g ^ 2 := by
      rw [Polynomial.finsetSum_coeff]
      exact sum_congr rfl fun k _ => coeff_sq_of_low_zero (q k) g
        (fun d hd => ih d hd (by omega) k)
    rw [he] at hc
    have hj := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ((q k).coeff g))).mp hc j (mem_univ j)
    exact (pow_eq_zero_iff two_ne_zero).mp hj

end
end ToeplitzSOS.Negative
