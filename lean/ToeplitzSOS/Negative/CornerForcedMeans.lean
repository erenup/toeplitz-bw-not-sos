import ToeplitzSOS.Negative.CornerLaplacian
import ToeplitzSOS.Negative.LowMeans

/-!
# Forced complete low means of every SOS row

A one-variable substitution kills both pure sectors. The complete Laplacian
row sums remove every coefficient below degree twice the corner depth.
Positivity of a real sum of squares then kills each mixed row's low means.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- Restrict to separated geometric vectors, with a formal real parameter. -/
def lowMeanSubstitution {m : ℕ} : CornerVariable m → Polynomial ℝ
  | (.x, false, p) => Polynomial.X ^ p.val
  | (.y, true, p) => Polynomial.X ^ p.val
  | _ => 0

/-- The polynomial whose coefficients are complete mixed means. -/
def mixedDiagonalPolynomial {m : ℕ} (c : Fin m → Fin m → ℝ) : Polynomial ℝ :=
  ∑ p, ∑ q, Polynomial.C (c p q) * Polynomial.X ^ (p.val + q.val)

/-- The baseline on separated geometric vectors. -/
def baselineDiagonalPolynomial (m : ℕ) : Polynomial ℝ :=
  ∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
    Polynomial.C (baselineMixedEntry p q r s) * Polynomial.X ^ (p.val + q.val + r.val + s.val)

/-- On the separated substitution only the complete mixed row survives. -/
theorem aeval_cornerLinear_low {m : ℕ} (a b : PureIndex m → ℝ) (c : Fin m → Fin m → ℝ) :
    aeval lowMeanSubstitution (cornerLinear a b c) = mixedDiagonalPolynomial c := by
  simp [cornerLinear, pureWedge, mixedWedge, cornerWedge, lowMeanSubstitution,
    mixedDiagonalPolynomial, pow_add]

/-- The baseline substitution has the explicit univariate mixed expansion. -/
theorem aeval_baseline_low (m : ℕ) :
    aeval lowMeanSubstitution (baselinePolynomial m) = baselineDiagonalPolynomial m := by
  simp [baselinePolynomial, pureWedge, mixedWedge, cornerWedge, lowMeanSubstitution,
    baselineDiagonalPolynomial, pow_add, mul_assoc]

/-- The coefficient of a mixed row is its entire finite antidiagonal mean. -/
theorem mixedDiagonalPolynomial_coeff {m : ℕ} (c : Fin m → Fin m → ℝ) (g : ℕ) :
    (mixedDiagonalPolynomial c).coeff g = ∑ p, ∑ q, if p.val + q.val = g then c p q else 0 := by
  simp [mixedDiagonalPolynomial, eq_comm]

/-- The complete low totals remove every baseline coefficient below `2m`. -/
theorem baselineDiagonalPolynomial_low_coeff (m k : ℕ) (hk : k < 2 * m) :
    (baselineDiagonalPolynomial m).coeff k = 0 := by
  simp only [baselineDiagonalPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  apply sum_eq_zero
  intro p _
  apply sum_eq_zero
  intro q _
  have he (r s : Fin m) :
      (if k = p.val + q.val + r.val + s.val then baselineMixedEntry p q r s else 0) =
      if k = 2 * (p.val + q.val) then baselineMixedEntry p q r s else 0 := by
    by_cases ht : p.val + q.val = r.val + s.val
    · have hi : (k = p.val + q.val + r.val + s.val) ↔ k = 2 * (p.val + q.val) := by omega
      simp only [hi]
    · rw [baselineMixedEntry_eq_zero_of_ne p q r s ht]
      simp
  simp_rw [he]
  by_cases hpq : k = 2 * (p.val + q.val)
  · simp only [hpq, ite_true]
    exact baselineMixedEntry_row_sum p q (by omega)
  · simp [hpq]

/-- Every mixed coefficient row in an arbitrary corner SOS has vanishing
complete low means; no incomplete high mean is asserted to vanish. -/
theorem corner_sos_low_means {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) :
    ∀ g < m, ∀ j, ∑ p, ∑ q, (if p.val + q.val = g then c j p q else 0) = 0 := by
  have he := congrArg (aeval (lowMeanSubstitution (m := m))) h
  rw [aeval_baseline_low] at he
  simp only [map_sum, map_pow, aeval_cornerLinear_low] at he
  have hlow := sum_squares_low_coefficients (fun j => mixedDiagonalPolynomial (c j)) m
    (fun k hk => by rw [← he]; exact baselineDiagonalPolynomial_low_coeff m k hk)
  simpa only [mixedDiagonalPolynomial_coeff] using hlow

/-- The mixed baseline itself has exactly the complete low row means. -/
theorem baselineMixedEntry_low_column {m : ℕ} (g : ℕ) (hg : g < m) (r s : Fin m) :
    ∑ p, ∑ q, (if p.val + q.val = g then baselineMixedEntry p q r s else 0) = 0 := by
  by_cases hrs : r.val + s.val = g
  · have he (p q : Fin m) :
        (if p.val + q.val = g then baselineMixedEntry p q r s else 0) = baselineMixedEntry p q r s := by
      split_ifs with hpq
      · rfl
      · rw [baselineMixedEntry_eq_zero_of_ne p q r s (by omega)]
    simp_rw [he]
    exact baselineMixedEntry_column_sum r s (by omega)
  · apply sum_eq_zero
    intro p _
    apply sum_eq_zero
    intro q _
    split_ifs with hpq
    · exact baselineMixedEntry_eq_zero_of_ne p q r s (by omega)
    · rfl

/-- Symmetry gives the complete low column means of the baseline as well. -/
theorem baselineMixedEntry_low_row {m : ℕ} (g : ℕ) (hg : g < m) (p q : Fin m) :
    ∑ r, ∑ s, (if r.val + s.val = g then baselineMixedEntry p q r s else 0) = 0 := by
  simp_rw [baselineMixedEntry_symm p q]
  exact baselineMixedEntry_low_column g hg p q

end
end ToeplitzSOS.Negative
