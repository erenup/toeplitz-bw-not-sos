import ToeplitzSOS.Defs
import ToeplitzSOS.Negative.ExplicitStatement

/-!
# Sufficient-order non-SOS statement

The polynomial, variables, real coefficient field, and finite homogeneous
quadratic SOS predicate are those of `ToeplitzSOS.Defs`.
The bound `2^33554433` is retained as a weaker corollary of the theorem at
`2^9961475` in `SharpStatement` and `Resolution`.
Symbolic powers prevent expansion of the enormous natural-number bounds.
-/

namespace ToeplitzSOS.Negative

/-- A power of two represented without forcing the kernel to expand its numeral.
The equality `symbolicTwoPow_eq` identifies it with ordinary natural exponentiation. -/
noncomputable def symbolicTwoPow (k : ℕ) : ℕ :=
  Classical.choose (show ∃ n : ℕ, n = 2 ^ k from ⟨_, rfl⟩)

/-- The symbolic representation is exactly the usual power of two. -/
theorem symbolicTwoPow_eq (k : ℕ) : symbolicTwoPow k = 2 ^ k :=
  Classical.choose_spec (show ∃ n : ℕ, n = 2 ^ k from ⟨_, rfl⟩)

/-- The explicit sufficient ambient order in the negative proof. -/
noncomputable def orderThreshold : ℕ := symbolicTwoPow 33554433

/-- The threshold has the exact integer value in the theorem. -/
theorem orderThreshold_eq : orderThreshold = 2 ^ 33554433 :=
  symbolicTwoPow_eq _

/-- The literal negation of the existing finite homogeneous quadratic SOS
statement, at every order above the sufficient threshold. -/
def NegativeResolution : Prop :=
  ∀ N ≥ orderThreshold, ¬ IsSumSqHomQuad (toeplitzBW N)

/-- Expanding the existing SOS predicate exposes all quantifiers: arbitrary
finite square count, real coefficients, and degree-two homogeneity. -/
theorem negativeResolution_iff_explicit : NegativeResolution ↔
    ∀ N ≥ 2 ^ 33554433,
      ¬ ∃ (s : ℕ) (q : Fin s → MvPolynomial (V N) ℝ),
        (∀ j, (q j).IsHomogeneous 2) ∧ toeplitzBW N = ∑ j, q j ^ 2 :=
by
  unfold NegativeResolution IsSumSqHomQuad
  rw [orderThreshold_eq]

/-- The threshold is within the range quantified by MI-15. -/
theorem two_le_orderThreshold : 2 ≤ orderThreshold := by
  have h : ∀ k, 1 ≤ k → 2 ≤ symbolicTwoPow k := by
    intro k hk
    rw [symbolicTwoPow_eq]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hk
  exact h _ (by omega)

/-- The all-larger-order negative target implies the negation of MI-15. -/
theorem not_MI15_of_negativeResolution (h : NegativeResolution) : ¬ MI15 := by
  intro hpos
  exact h orderThreshold le_rfl (hpos orderThreshold two_le_orderThreshold)

/-- Equivalence with the explicit real homogeneous-quadratic quantifiers. -/
theorem negativeResolution_iff_explicitStatement :
    NegativeResolution ↔ ExplicitStatement.NonSOSAboveBound :=
  negativeResolution_iff_explicit

/-- Equivalence with the explicit negation of universal SOS representability. -/
theorem not_MI15_iff_explicitStatement : (¬ MI15) ↔ ExplicitStatement.NotUniversalSOS := Iff.rfl

end ToeplitzSOS.Negative
