import ToeplitzSOS.Negative.CornerEvaluation

/-!
# The two finite symmetry averages

Averaging the negative-side sign and exchanging the two sides gives the
common pure diagonal block, a symmetric pure cross block, and the averaged
mixed block, for arbitrary real SOS rows.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- Transpose every mixed coefficient row. -/
def transposeRows {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) : Fin r → Fin m → Fin m → ℝ :=
  fun j p q => c j q p

/-- Transposing a mixed row interchanges its two vector slots. -/
theorem mixedForm_transpose {m : ℕ} (c : Fin m → Fin m → ℝ) (U V : DepthVector m) :
    mixedForm (fun p q => c q p) U V = mixedForm c V U := by
  unfold mixedForm
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  ring

/-- Pure forms are unchanged when both vectors change sign. -/
theorem pureForm_neg_neg {m : ℕ} (c : PureIndex m → ℝ) (U V : DepthVector m) :
    pureForm c (-U) (-V) = pureForm c U V := by
  simp only [pureForm, vectorWedge, Pi.neg_apply, neg_mul_neg]

/-- Mixed forms change sign in their first vector. -/
theorem mixedForm_neg_left {m : ℕ} (c : Fin m → Fin m → ℝ) (U V : DepthVector m) :
    mixedForm c (-U) V = -mixedForm c U V := by
  simp only [mixedForm, Pi.neg_apply, mul_neg, neg_mul, sum_neg_distrib]

/-- Mixed forms change sign in their second vector. -/
theorem mixedForm_neg_right {m : ℕ} (c : Fin m → Fin m → ℝ) (U V : DepthVector m) :
    mixedForm c U (-V) = -mixedForm c U V := by
  simp only [mixedForm, Pi.neg_apply, mul_neg, sum_neg_distrib]

/-- Transpose-invariant mixed coefficients permit exchanging the slots in
both vector pairs. -/
theorem mixedTensor_transpose {m : ℕ} (G : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hG : ∀ p q r s, G q p s r = G p q r s) (U V W Z : DepthVector m) :
    mixedTensor G V U Z W = mixedTensor G U V W Z := by
  simp only [mixedTensor, Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  rw [hG p q r s]
  ring

/-- The baseline is invariant under changing the sign of the negative side. -/
theorem baselineValue_neg (m : ℕ) (U V W Z : DepthVector m) :
    baselineValue m (-U) (-V) W Z = baselineValue m U V W Z := by
  simp only [baselineValue, diagonalForm, crossForm, pureTensor, vectorWedge,
    mixedBaselineForm, mixedTensor, Pi.neg_apply, mul_neg, neg_mul, neg_neg]

/-- The baseline is invariant under exchanging its two sides. -/
theorem baselineValue_swap (m : ℕ) (U V W Z : DepthVector m) :
    baselineValue m W Z U V = baselineValue m U V W Z := by
  unfold baselineValue crossForm mixedBaselineForm
  rw [pureTensor_pairs baselineCrossEntry baselineCrossEntry_symm W Z U V,
    mixedTensor_transpose baselineMixedEntry baselineMixedEntry_transpose V W V W,
    mixedTensor_transpose baselineMixedEntry baselineMixedEntry_transpose U Z U Z,
    mixedTensor_transpose baselineMixedEntry baselineMixedEntry_transpose V W U Z,
    mixedTensor_pairs baselineMixedEntry baselineMixedEntry_symm V W U Z]
  ring

/-- The common pure diagonal block after side exchange. -/
def meanPure {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : VectorFourForm m :=
  fun U V W Z => (pureFour a a U V W Z + pureFour b b U V W Z) / 2

/-- The symmetric pure cross block after side exchange. -/
def meanCross {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : VectorFourForm m :=
  fun U V W Z => (pureFour a b U V W Z + pureFour b a U V W Z) / 2

/-- The mixed block after side exchange. -/
def meanMixed {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) : VectorFourForm m :=
  fun U V W Z => (mixedFour c U V W Z + mixedFour (transposeRows c) U V W Z) / 2

/-- The value of the three averaged blocks on a decomposable two-vector input. -/
def averagedValue {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ) (U V W Z : DepthVector m) : ℂ :=
  meanPure a b U V U V + meanPure a b W Z W Z + 2 * meanCross a b U V W Z +
    meanMixed c U Z U Z + meanMixed c V W V W - 2 * meanMixed c U Z V W

/-- Both finite symmetry averages preserve the complete polynomial identity. -/
theorem averagedValue_eq_baseline {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (U V W Z : DepthVector m) : averagedValue a b c U V W Z = baselineValue m U V W Z := by
  have h₁ := corner_sos_value a b c h U V W Z
  have h₂ := corner_sos_value a b c h (-U) (-V) W Z
  have h₃ := corner_sos_value a b c h W Z U V
  have h₄ := corner_sos_value a b c h (-W) (-Z) U V
  rw [baselineValue_neg] at h₂ h₄
  rw [baselineValue_swap m U V W Z] at h₃ h₄
  simp only [pureForm_neg_neg, mixedForm_neg_left, sub_neg_eq_add] at h₂ h₄
  have he : 4 * averagedValue a b c U V W Z =
      (∑ j, (pureForm (a j) U V + pureForm (b j) W Z + mixedForm (c j) U Z - mixedForm (c j) V W) ^ 2) +
      (∑ j, (pureForm (a j) U V + pureForm (b j) W Z + -mixedForm (c j) U Z + mixedForm (c j) V W) ^ 2) +
      (∑ j, (pureForm (a j) W Z + pureForm (b j) U V + mixedForm (c j) W V - mixedForm (c j) Z U) ^ 2) +
      (∑ j, (pureForm (a j) W Z + pureForm (b j) U V + -mixedForm (c j) W V + mixedForm (c j) Z U) ^ 2) := by
    simp only [averagedValue, meanPure, meanCross, meanMixed, pureFour, mixedFour,
      div_eq_mul_inv, mul_add, mul_sub,
      sum_mul, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [show transposeRows c j = (fun p q => c j q p) from rfl]
    simp only [mixedForm_transpose]
    ring
  linear_combination (he - h₁ - h₂ - h₃ - h₄) / 4

end
end ToeplitzSOS.Negative
