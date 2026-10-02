import ToeplitzSOS.Negative.CornerObstruction
import ToeplitzSOS.Negative.CornerExtraction

/-! # The faithful negative resolution of the Toeplitz SOS conjecture

The proof starts with the original polynomial and arbitrary finite real
homogeneous quadratic squares, extracts the complete algebraic corner,
and contradicts the checked finite obstruction. The sufficient bound
`2^9961475` is exported directly, with the weaker `2^33554433` bound and the
catalogue-conjecture negation retained as corollaries.
-/

namespace ToeplitzSOS.Negative

/-- Corner extraction and the finite obstruction yield non-SOS from the stated analytic estimates. -/
theorem sharpNegativeResolution_of_analyticInputs (hA : AnalyticInputs) :
    SharpNegativeResolution := by
  intro N hN hSOS
  exact no_cornerGram hA (cornerGram_of_sos (corner_fits hN) hSOS)

/-- The original real Toeplitz quartic is not SOS at any order `N ≥ 2^9961475`. -/
theorem sharpNegativeResolution : SharpNegativeResolution :=
  sharpNegativeResolution_of_analyticInputs Analytic.analyticInputs

/-- Direct non-SOS statement about the original Toeplitz polynomial. -/
theorem not_isSumSqHomQuad_of_large_order {N : ℕ} (hN : 2^9961475 ≤ N) :
    ¬ IsSumSqHomQuad (toeplitzBW N) := by
  apply sharpNegativeResolution N
  rwa [sharpOrderThreshold_eq]

/-- For every `N ≥ 2^9961475`, no finite family of real homogeneous quadratic
polynomials has squares summing to the original Toeplitz quartic. -/
theorem sharp_negative_explicit :
    ∀ N ≥ 2^9961475,
      ¬ ∃ (s : ℕ) (q : Fin s → MvPolynomial (V N) ℝ),
        (∀ j, (q j).IsHomogeneous 2) ∧ toeplitzBW N = ∑ j, q j^2 :=
  sharpNegativeResolution_iff_explicit.mp sharpNegativeResolution

/-- The sufficient bound 2^33554433 follows as a weaker corollary. -/
theorem negativeResolution : NegativeResolution :=
  negativeResolution_of_sharp sharpNegativeResolution

/-- The weaker sufficient-bound corollary with all real SOS quantifiers explicit. -/
theorem nonSOSAboveBound : ExplicitStatement.NonSOSAboveBound :=
  negativeResolution_iff_explicitStatement.mp negativeResolution

/-- The catalogue conjecture is false for its original polynomial and SOS predicate. -/
theorem not_MI15 : ¬ MI15 := not_MI15_of_negativeResolution negativeResolution

end ToeplitzSOS.Negative
