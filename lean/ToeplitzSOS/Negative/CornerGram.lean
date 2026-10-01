import ToeplitzSOS.Negative.AnalyticInputs

/-!
# Finite algebraic data of the stabilized corner

A `CornerGram m` records arbitrary finite real Gram factors for both pure
signs and the mixed block, the repair identities, and vanishing complete
low means. `cornerGram_of_sos` in `CornerExtraction` constructs these data
from an SOS of the original Toeplitz polynomial.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset

/-- A real linear combination of geometric pure-wedge features. -/
def pureLinear {m : ℕ} (c : PureIndex m → ℝ) (x y : ℂ) : ℂ :=
  ∑ pq, (c pq : ℂ) * pureFeature pq x y

/-- A real linear combination of geometric mixed features. -/
def mixedLinear {m : ℕ} (c : Fin m → Fin m → ℝ) (x y : ℂ) : ℂ :=
  ∑ p, ∑ q, (c p q : ℂ) * x^p.val * y^q.val

/-- A finite real Gram factor in the pure-wedge frame. -/
def pureGramKernel {m r : ℕ} (c : Fin r → PureIndex m → ℝ) : FourKernel :=
  fun x y z w => ∑ j, pureLinear (c j) x y * pureLinear (c j) z w

/-- A finite real Gram factor in the mixed frame. -/
def mixedGramKernel {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) : FourKernel :=
  fun x y z w => ∑ j, mixedLinear (c j) x y * mixedLinear (c j) z w

/-- The unrestricted finite algebraic output required of the literal-corner
bridge. The three ranks and all real coefficients are arbitrary. -/
structure CornerGram (m : ℕ) where
  /-- Pure four-form repair. -/
  E : FourKernel
  /-- Pure cross repair, with its full Gram normalization. -/
  T : FourKernel
  /-- Arbitrary finite rank of the plus Gram factor. -/
  plusRank : ℕ
  /-- Arbitrary finite rank of the minus Gram factor. -/
  minusRank : ℕ
  /-- Arbitrary finite rank of the mixed Gram factor. -/
  mixedRank : ℕ
  /-- Real rows of the plus pure Gram. -/
  plusRows : Fin plusRank → PureIndex m → ℝ
  /-- Real rows of the minus pure Gram. -/
  minusRows : Fin minusRank → PureIndex m → ℝ
  /-- Real rows of the mixed Gram. -/
  mixedRows : Fin mixedRank → Fin m → Fin m → ℝ
  /-- Exact plus factorization, uniformly on all four complex slots. -/
  plus_eq : plusBlock (baselineD m) (baselineK m) E T = pureGramKernel plusRows
  /-- Exact minus factorization, uniformly on all four complex slots. -/
  minus_eq : minusBlock (baselineD m) (baselineK m) E T = pureGramKernel minusRows
  /-- Exact mixed factorization, including the negative realignment transport. -/
  mixed_eq : mixedBlock (baselineB m) T = mixedGramKernel mixedRows
  /-- Four-form antisymmetry under the realignment swap. -/
  realign_E : realign E = -E
  /-- Four-form antisymmetry under the partial-conjugation swap. -/
  swap_E : ∀ x y z w, E x w z y = -E x y z w
  /-- The cross kernel alternates in its second wedge. -/
  swap_T : ∀ x y z w, T x y w z = -T x y z w
  /-- Actual finite coefficients of the mixed correction `M-B`. -/
  correction : Fin m → Fin m → Fin m → Fin m → ℂ
  /-- The coefficients represent the actual correction, with the correct sign. -/
  correction_eq : mixedBlock (baselineB m) T - baselineB m = mixedKernel correction
  /-- The forced complete low means, in both variables. -/
  low_means : CompleteLowMeans correction
  /-- Cauchy--Schwarz payment from the fixed mixed diagonals, (9). -/
  correction_bound : ∀ p q r s, ‖correction p q r s‖ ≤ 4 * Real.sqrt
    ((p.val + 1) * (q.val + 1) * (r.val + 1) * (s.val + 1) : ℝ)

end
end ToeplitzSOS.Negative
