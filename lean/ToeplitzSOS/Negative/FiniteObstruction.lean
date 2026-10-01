import ToeplitzSOS.Negative.Witness
import ToeplitzSOS.Negative.ContinuationApplication

/-!
# The checked finite dual contradiction

The fixed
witness, all rational arithmetic, the complex-node realignment, and the
finite error payments are proved. The theorem `no_feasible_evaluation`
exposes exactly what a corner/analytic assembly must supply. It is not
by itself the catalogue non-SOS theorem.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate

/-- Scaled real part of a finite kernel evaluated on all witness node pairs. -/
def scaledKernel (K : FourKernel) : Fin 1024 → Fin 1024 → ℝ := fun i j =>
  epsilon^4 * (K (witnessNode epsilon i) (conj (witnessNode epsilon i))
    (conj (witnessNode epsilon j)) (witnessNode epsilon j)).re

/-- Scaling and node evaluation preserve kernel addition. -/
theorem scaledKernel_add (K L : FourKernel) : scaledKernel (K + L) = scaledKernel K + scaledKernel L := by
  funext i j
  simp [scaledKernel, mul_add]

/-- The scaled realignment is the entry paid for by the continuation estimate. -/
theorem scaledKernel_realign (P : FourKernel) :
    scaledKernel (realign P) = scaledRealignedEntry P := rfl

/-- Exact cancellation survives finite node evaluation and scaling. -/
theorem scaled_cancellation (m : ℕ) (E T : FourKernel) (hE : realign E = -E) :
    scaledKernel (mixedBlock (baselineB m) T +
      pureMean (baselineD m) (baselineK m) E T) +
      scaledRealignedEntry (plusBlock (baselineD m) (baselineK m) E T) =
      scaledKernel (baselineL m) := by
  rw [← scaledKernel_realign, ← scaledKernel_add]
  exact congrArg scaledKernel (cancellation (baselineD m) (baselineK m) (baselineB m) E T hE)

/-- The exact finite witness rules out every nonnegative Gram pairing with
the cancellation and entry-error bounds. -/
theorem no_feasible_evaluation (H L R : Fin 1024 → Fin 1024 → ℝ)
    (hcancel : H + R = L)
    (hpos : 0 ≤ pairing Witness.realCoefficient H)
    (hlimit : ∀ i j, |L i j - Witness.tangentEntry i j| ≤ 2^30 * epsilon)
    (hrealign : ∀ i j, |R i j| ≤ realignedBound) : False := by
  exact finite_separation Witness.realCoefficient H L R Witness.tangentEntry
    (2^30 * epsilon) realignedBound (3*2^58) (2^42)
    hcancel hpos Witness.coefficientMass_sq_le_sharp
    (mul_nonneg (by positivity) epsilon_pos.le) (by norm_num [realignedBound])
    hlimit hrealign Witness.tangent_pairing_lt final_budget

/-- Specialized infeasibility of the evaluated repaired baseline. Both repairs
are arbitrary, except for the genuine four-form identity used by cancellation. -/
theorem no_feasible_repaired_kernels (m : ℕ) (E T : FourKernel)
    (hE : realign E = -E)
    (hpos : 0 ≤ pairing Witness.realCoefficient
      (scaledKernel (mixedBlock (baselineB m) T + pureMean (baselineD m) (baselineK m) E T)))
    (hlimit : ∀ i j, |scaledKernel (baselineL m) i j - Witness.tangentEntry i j| ≤
      2^30 * epsilon)
    (hrealign : ∀ i j,
      |scaledRealignedEntry (plusBlock (baselineD m) (baselineK m) E T) i j| ≤
        realignedBound) : False :=
  no_feasible_evaluation _ _ _ (scaled_cancellation m E T hE) hpos hlimit hrealign

end
end ToeplitzSOS.Negative
