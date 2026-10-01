import ToeplitzSOS.Defs

/-! # Explicit real homogeneous-quadratic quantifiers

The variables are `V n = CoordFamily × Fin (2 * n - 1)`, so for `n ≥ 1`
there are `4n - 2` real coordinates. The SOS clause allows any finite
number of squares, including zero, and requires a polynomial identity.

The bound `2^33554433` is retained as a weaker corollary of the theorem at
`2^9961475`; neither bound is asserted to be the first non-SOS order.
-/

namespace ToeplitzSOS.Negative.ExplicitStatement

/-- Above the stated sufficient bound there is no finite representation by
squares of real homogeneous quadratic polynomials. -/
def NonSOSAboveBound : Prop :=
  ∀ n : ℕ, n ≥ 2 ^ 33554433 →
    ¬ ∃ (N : ℕ) (q : Fin N → MvPolynomial (ToeplitzSOS.V n) ℝ),
      (∀ j, (q j).IsHomogeneous 2) ∧ ToeplitzSOS.toeplitzBW n = ∑ j, q j ^ 2

/-- The literal negation of universal SOS representability at every order
`n ≥ 2`, with the real coefficients and homogeneity condition written out. -/
def NotUniversalSOS : Prop :=
  ¬ ∀ n : ℕ, n ≥ 2 →
    ∃ (N : ℕ) (q : Fin N → MvPolynomial (ToeplitzSOS.V n) ℝ),
      (∀ j, (q j).IsHomogeneous 2) ∧ ToeplitzSOS.toeplitzBW n = ∑ j, q j ^ 2

example : NonSOSAboveBound ↔
    ∀ n : ℕ, n ≥ 2 ^ 33554433 → ¬ ToeplitzSOS.IsSumSqHomQuad (ToeplitzSOS.toeplitzBW n) :=
  Iff.rfl

example : NotUniversalSOS ↔ ¬ ToeplitzSOS.MI15 := Iff.rfl

end ToeplitzSOS.Negative.ExplicitStatement
