import ToeplitzSOS.Negative.Statement

/-! # The sharper negative threshold -/

namespace ToeplitzSOS.Negative

/-- The sharper sufficient ambient order. -/
noncomputable def sharpOrderThreshold : ℕ := symbolicTwoPow 9961475

/-- The symbolic threshold equals the stated natural power. -/
theorem sharpOrderThreshold_eq : sharpOrderThreshold = 2^9961475 := symbolicTwoPow_eq _

/-- The faithful catalogue-negative target at the sharper threshold. -/
def SharpNegativeResolution : Prop :=
  ∀ N ≥ sharpOrderThreshold, ¬ IsSumSqHomQuad (toeplitzBW N)

/-- The sharp target uses exactly the original real homogeneous SOS quantifiers. -/
theorem sharpNegativeResolution_iff_explicit : SharpNegativeResolution ↔
    ∀ N ≥ 2^9961475,
      ¬ ∃ (s : ℕ) (q : Fin s → MvPolynomial (V N) ℝ),
        (∀ j, (q j).IsHomogeneous 2) ∧ toeplitzBW N = ∑ j, q j^2 := by
  unfold SharpNegativeResolution IsSumSqHomQuad
  rw [sharpOrderThreshold_eq]

/-- The sufficient bound 2^33554433 is a weaker corollary of the 2^9961475 bound. -/
theorem negativeResolution_of_sharp (h : SharpNegativeResolution) : NegativeResolution := by
  have hm : ∀ k l : ℕ, k ≤ l → symbolicTwoPow k ≤ symbolicTwoPow l := by
    intro k l hkl
    simp only [symbolicTwoPow_eq]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hkl
  have hle : sharpOrderThreshold ≤ orderThreshold := hm _ _ (by omega)
  intro N hN
  exact h N (hle.trans hN)

end ToeplitzSOS.Negative
