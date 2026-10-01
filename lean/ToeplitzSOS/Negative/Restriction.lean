import ToeplitzSOS.Negative.Constants
import ToeplitzSOS.SOS.LinearSubstitution

/-!
# Literal restriction to the two outer depth intervals

Variables outside the retained corner are set to zero by a homogeneous
linear substitution, so arbitrary homogeneous quadratic SOS representations
restrict faithfully. The stabilization identity identifying this restriction
with the explicit baseline is proved in `CornerRestriction`.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open MvPolynomial

/-- Corner labels: the two outer sides and a zero-based depth. -/
abbrev CornerLabel (m : ℕ) := Bool × Fin m

/-- Two independent real symbol families on the corner labels. -/
abbrev CornerVariable (m : ℕ) := CoordFamily × CornerLabel m

/-- Keep the outermost `m` labels of each side and set all others to zero.
In offset coordinates the negative-side depth is `k`, the positive-side
depth is `2N-2-k`. Under `N ≥ 2m` the intervals are disjoint. -/
def outerSubstitution (m N : ℕ) (v : V N) : MvPolynomial (CornerVariable m) ℝ :=
  if h : v.2.val < m then MvPolynomial.X (v.1, false, ⟨v.2.val, h⟩)
  else if h' : 2 * N - 2 - v.2.val < m then
    MvPolynomial.X (v.1, true, ⟨2 * N - 2 - v.2.val, h'⟩)
  else 0

/-- Every variable is sent to a degree-one homogeneous polynomial, including zero. -/
theorem outerSubstitution_isHomogeneous (m N : ℕ) (v : V N) :
    (outerSubstitution m N v).IsHomogeneous 1 := by
  unfold outerSubstitution
  split_ifs
  · exact MvPolynomial.isHomogeneous_X _ _
  · exact MvPolynomial.isHomogeneous_X _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/-- The literal catalogue polynomial after the outer-corner substitution. -/
def outerCorner (m N : ℕ) : MvPolynomial (CornerVariable m) ℝ :=
  aeval (outerSubstitution m N) (toeplitzBW N)

/-- No SOS is lost by discarding the other variables, even if individual
quadratic summands couple retained and discarded symbols. -/
theorem outerCorner_isSumSq_of {m N : ℕ} (h : IsSumSqHomQuad (toeplitzBW N)) :
    IsSumSqHomQuad (outerCorner m N) :=
  h.aeval _ (outerSubstitution_isHomogeneous m N)

/-- An obstruction to the literal corner obstructs the original polynomial. -/
theorem not_isSumSq_of_outerCorner {m N : ℕ}
    (h : ¬ IsSumSqHomQuad (outerCorner m N)) :
    ¬ IsSumSqHomQuad (toeplitzBW N) := fun hp => h (outerCorner_isSumSq_of hp)

/-- A fixed non-SOS corner and its literal stabilization imply the exact
headline statement. This theorem isolates the required stabilization identity;
it does not assert that identity as an analytic input. -/
theorem sharpNegativeResolution_of_stabilized_corner
    (p : MvPolynomial (CornerVariable cornerDepth) ℝ)
    (hstable : ∀ N, 2 * cornerDepth ≤ N → outerCorner cornerDepth N = p)
    (hbad : ¬ IsSumSqHomQuad p) : SharpNegativeResolution := by
  intro N hN
  apply not_isSumSq_of_outerCorner (m := cornerDepth)
  rw [hstable N (corner_fits hN)]
  exact hbad

/-- The original larger-threshold conclusion is retained as a corollary. -/
theorem negativeResolution_of_stabilized_corner
    (p : MvPolynomial (CornerVariable cornerDepth) ℝ)
    (hstable : ∀ N, 2 * cornerDepth ≤ N → outerCorner cornerDepth N = p)
    (hbad : ¬ IsSumSqHomQuad p) : NegativeResolution :=
  negativeResolution_of_sharp (sharpNegativeResolution_of_stabilized_corner p hstable hbad)

end
end ToeplitzSOS.Negative
