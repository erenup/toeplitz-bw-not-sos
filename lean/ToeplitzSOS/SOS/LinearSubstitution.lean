import ToeplitzSOS.Defs

/-! # Homogeneous quadratic sums of squares under linear substitution -/

namespace ToeplitzSOS

open MvPolynomial

noncomputable section

/-- Substituting linear forms (homogeneous of degree one, e.g. variables or `0`) for the
variables preserves sums of quadratic squares. -/
theorem IsSumSqHomQuad.aeval {σ τ : Type*} {p : MvPolynomial σ ℝ} (hp : IsSumSqHomQuad p)
    (g : σ → MvPolynomial τ ℝ) (hg : ∀ i, (g i).IsHomogeneous 1) :
    IsSumSqHomQuad (MvPolynomial.aeval g p) := by
  obtain ⟨N, q, hq, rfl⟩ := hp
  refine ⟨N, fun j => MvPolynomial.aeval g (q j), fun j => ?_, by simp [map_sum]⟩
  simpa using (hq j).aeval g hg

end

end ToeplitzSOS
