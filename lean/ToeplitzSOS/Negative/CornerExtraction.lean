import ToeplitzSOS.Negative.CornerCoefficientBound

/-!
# The complete literal-corner algebraic bridge

An arbitrary homogeneous quadratic SOS of the catalogue polynomial produces
exactly the `CornerGram` consumed by the negative theorem. The literal D/K/B
identity, both averages, four-form polarization, explicit real factors,
complete low means and coefficient payment have all been proved separately.
No analytic estimate occurs in the producer theorem.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- The pure repair kernel obtained from the averaged rows. -/
def extractedPureRepair {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : FourKernel :=
  fun x y z w => pureRepairForm a b (geometricVector m x) (geometricVector m y)
    (geometricVector m z) (geometricVector m w)

/-- The pure cross repair kernel obtained from the averaged rows. -/
def extractedCrossRepair {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : FourKernel :=
  fun x y z w => crossRepairForm a b (geometricVector m x) (geometricVector m y)
    (geometricVector m z) (geometricVector m w)

/-- A complete, unrestricted wedge SOS supplies every field of the algebraic
producer/consumer interface. -/
theorem cornerGram_of_wedge_sos {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) :
    Nonempty (CornerGram m) := by
  let E := extractedPureRepair a b
  let T := extractedCrossRepair a b
  refine ⟨{
    E := E
    T := T
    plusRank := r + r
    minusRank := r + r
    mixedRank := (r + r) + (r + r)
    plusRows := averagedPlusRows a b
    minusRows := averagedMinusRows a b
    mixedRows := averagedMixedRows c
    plus_eq := ?_
    minus_eq := ?_
    mixed_eq := ?_
    realign_E := ?_
    swap_E := ?_
    swap_T := ?_
    correction := fun p q u v => (mixedCorrectionEntry c p q u v : ℂ)
    correction_eq := ?_
    low_means := mixedCorrectionEntry_low_means a b c h
    correction_bound := mixedCorrectionEntry_bound a b c h
  }⟩
  · funext x y z w
    have hf := averagedPlusRows_factor a b (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
    rw [pureFour_geometric] at hf
    simp only [plusBlock, Pi.add_apply, E, T, extractedPureRepair, extractedCrossRepair,
      pureRepairForm, crossRepairForm, diagonalForm_geometric, crossForm_geometric]
    linear_combination -hf
  · funext x y z w
    have hf := averagedMinusRows_factor a b (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
    rw [pureFour_geometric] at hf
    simp only [minusBlock, Pi.add_apply, Pi.sub_apply, E, T, extractedPureRepair, extractedCrossRepair,
      pureRepairForm, crossRepairForm, diagonalForm_geometric, crossForm_geometric]
    linear_combination -hf
  · funext x y z w
    have ht := mixedRepairForm_transport a b c h (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
    have hf := averagedMixedRows_factor c (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
    rw [mixedFour_geometric] at hf
    simp only [mixedRepairForm, mixedBaselineForm_geometric] at ht
    simp only [mixedBlock, realign, Pi.sub_apply, T, extractedCrossRepair]
    linear_combination -ht - hf
  · funext x y z w
    exact pureRepairForm_swap23 a b c h (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
  · intro x y z w
    exact pureRepairForm_swap24 a b c h (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
  · intro x y z w
    exact crossRepairForm_swap34 a b (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
  · funext x y z w
    rw [mixedCorrectionEntry_kernel]
    have ht := mixedRepairForm_transport a b c h (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w)
    simp only [mixedBlock, realign, Pi.sub_apply, T, extractedCrossRepair]
    linear_combination -ht

theorem cornerGram_of_baseline_sos {m : ℕ} (h : IsSumSqHomQuad (baselinePolynomial m)) :
    Nonempty (CornerGram m) := by
  obtain ⟨r, a, b, c, he⟩ := baseline_exists_wedge_sos h
  exact cornerGram_of_wedge_sos a b c he

/-- The literal stabilized-corner bridge consumed by the negative theorem:
every unrestricted catalogue SOS supplies the full finite `CornerGram` at
any depth whose two outer intervals fit. -/
theorem cornerGram_of_sos {m N : ℕ} (hN : 2 * m ≤ N)
    (hSOS : IsSumSqHomQuad (toeplitzBW N)) : Nonempty (CornerGram m) := by
  obtain ⟨r, a, b, c, h⟩ := toeplitzBW_exists_corner_wedge_sos hN hSOS
  exact cornerGram_of_wedge_sos a b c h

end
end ToeplitzSOS.Negative
