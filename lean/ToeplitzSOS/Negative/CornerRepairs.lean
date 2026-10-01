import ToeplitzSOS.Negative.CornerAveraging

/-!
# Polarization of the complete averaged repair

The two averages and the complete polynomial identity force the pure repair
to be a four-form and identify the mixed correction as minus the realigned
pure cross repair. No classification of relations is used.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- A four-additive form vanishes when its first slot is zero. -/
theorem FourAdditive.zero1 {m : ℕ} {F : VectorFourForm m} (h : FourAdditive F)
    (a b c : DepthVector m) : F 0 a b c = 0 := by
  have he := h.add1 0 0 a b c
  rw [zero_add] at he
  linear_combination -he

/-- A four-additive form vanishes when its second slot is zero. -/
theorem FourAdditive.zero2 {m : ℕ} {F : VectorFourForm m} (h : FourAdditive F)
    (a b c : DepthVector m) : F a 0 b c = 0 := by
  have he := h.add2 a 0 0 b c
  rw [zero_add] at he
  linear_combination -he

/-- A four-additive form vanishes when its third slot is zero. -/
theorem FourAdditive.zero3 {m : ℕ} {F : VectorFourForm m} (h : FourAdditive F)
    (a b c : DepthVector m) : F a b 0 c = 0 := by
  have he := h.add3 a b 0 0 c
  rw [zero_add] at he
  linear_combination -he

/-- A four-additive form vanishes when its fourth slot is zero. -/
theorem FourAdditive.zero4 {m : ℕ} {F : VectorFourForm m} (h : FourAdditive F)
    (a b c : DepthVector m) : F a b c 0 = 0 := by
  have he := h.add4 a b c 0 0
  rw [zero_add] at he
  linear_combination -he

/-- Subtracting four-additive forms preserves four-additivity. -/
theorem FourAdditive.sub {m : ℕ} {F G : VectorFourForm m}
    (hF : FourAdditive F) (hG : FourAdditive G) :
    FourAdditive (fun a b c d => F a b c d - G a b c d) := by
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using hF.linearCombination hG 1 (-1)

/-- Averaging two four-additive forms preserves four-additivity. -/
theorem FourAdditive.mean {m : ℕ} {F G : VectorFourForm m}
    (hF : FourAdditive F) (hG : FourAdditive G) :
    FourAdditive (fun a b c d => (F a b c d + G a b c d) / 2) := by
  have he : (fun a b c d => (F a b c d + G a b c d) / 2) =
      (fun a b c d => (1 / 2 : ℂ) * F a b c d + (1 / 2 : ℂ) * G a b c d) := by
    funext a b c d
    ring
  rw [he]
  exact hF.linearCombination hG _ _

/-- The pure repair before specialization to geometric vectors. -/
def pureRepairForm {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : VectorFourForm m :=
  fun U V W Z => meanPure a b U V W Z - diagonalForm m U V W Z

/-- The pure cross repair before specialization to geometric vectors. -/
def crossRepairForm {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : VectorFourForm m :=
  fun U V W Z => meanCross a b U V W Z - crossForm m U V W Z

/-- The actual mixed correction before geometric specialization. -/
def mixedRepairForm {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) : VectorFourForm m :=
  fun U V W Z => meanMixed c U V W Z - mixedBaselineForm m U V W Z

/-- The pure repair is four-additive. -/
theorem pureRepairForm_additive {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) :
    FourAdditive (pureRepairForm a b) :=
  ((pureFour_additive a a).mean (pureFour_additive b b)).sub
    (pureTensor_additive baselineDiagonalEntry)

/-- The cross repair is four-additive. -/
theorem crossRepairForm_additive {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) :
    FourAdditive (crossRepairForm a b) :=
  ((pureFour_additive a b).mean (pureFour_additive b a)).sub
    (pureTensor_additive baselineCrossEntry)

/-- The mixed correction is four-additive. -/
theorem mixedRepairForm_additive {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) :
    FourAdditive (mixedRepairForm c) :=
  ((mixedFour_additive c).mean (mixedFour_additive (transposeRows c))).sub
    (mixedTensor_additive baselineMixedEntry)

/-- The pure repair is symmetric in its two wedges. -/
theorem pureRepairForm_pairs {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) (U V W Z : DepthVector m) :
    pureRepairForm a b U V W Z = pureRepairForm a b W Z U V := by
  unfold pureRepairForm meanPure diagonalForm
  rw [pureFour_pairs a a U V W Z, pureFour_pairs b b U V W Z,
    pureTensor_pairs baselineDiagonalEntry baselineDiagonalEntry_symm U V W Z]

/-- The mixed correction is symmetric in its two mixed pairs. -/
theorem mixedRepairForm_pairs {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (U V W Z : DepthVector m) :
    mixedRepairForm c U V W Z = mixedRepairForm c W Z U V := by
  unfold mixedRepairForm meanMixed mixedBaselineForm
  rw [mixedFour_pairs c U V W Z, mixedFour_pairs (transposeRows c) U V W Z,
    mixedTensor_pairs baselineMixedEntry baselineMixedEntry_symm U V W Z]

/-- The pure repair alternates in its last wedge. -/
theorem pureRepairForm_swap34 {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) (U V W Z : DepthVector m) :
    pureRepairForm a b U V Z W = -pureRepairForm a b U V W Z := by
  unfold pureRepairForm meanPure diagonalForm
  rw [pureFour_swap a a U V W Z, pureFour_swap b b U V W Z,
    pureTensor_swap baselineDiagonalEntry U V W Z]
  ring

/-- The cross repair alternates in its last wedge. -/
theorem crossRepairForm_swap34 {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) (U V W Z : DepthVector m) :
    crossRepairForm a b U V Z W = -crossRepairForm a b U V W Z := by
  unfold crossRepairForm meanCross crossForm
  rw [pureFour_swap a b U V W Z, pureFour_swap b a U V W Z,
    pureTensor_swap baselineCrossEntry U V W Z]
  ring

/-- The difference of the averaged and baseline identities is the complete
repair relation, with the mixed transport sign visible. -/
theorem repair_value_zero {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (U V W Z : DepthVector m) :
    pureRepairForm a b U V U V + pureRepairForm a b W Z W Z +
      2 * crossRepairForm a b U V W Z + mixedRepairForm c U Z U Z +
      mixedRepairForm c V W V W - 2 * mixedRepairForm c U Z V W = 0 := by
  have he := averagedValue_eq_baseline a b c h U V W Z
  dsimp only [averagedValue, baselineValue] at he
  dsimp only [pureRepairForm, crossRepairForm, mixedRepairForm]
  linear_combination he

/-- Pure diagonal values of the repair vanish on all decomposable vectors. -/
theorem pureRepairForm_diagonal_zero {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (U V : DepthVector m) : pureRepairForm a b U V U V = 0 := by
  have he := repair_value_zero a b c h U V 0 0
  simpa only [(pureRepairForm_additive a b).zero1, (crossRepairForm_additive a b).zero3,
    (mixedRepairForm_additive c).zero2, (mixedRepairForm_additive c).zero4,
    mul_zero, add_zero, sub_zero] using he

/-- Mixed diagonal values of the correction vanish on all rank-one vectors. -/
theorem mixedRepairForm_diagonal_zero {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (U V : DepthVector m) : mixedRepairForm c U V U V = 0 := by
  have he := repair_value_zero a b c h U 0 0 V
  simpa only [(pureRepairForm_additive a b).zero1, (pureRepairForm_additive a b).zero2,
    (crossRepairForm_additive a b).zero2, (mixedRepairForm_additive c).zero1,
    (mixedRepairForm_additive c).zero3, mul_zero, zero_add, add_zero, sub_zero] using he

/-- Pure four-form alternation under realignment, obtained by polarization. -/
theorem pureRepairForm_swap23 {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) :
    ∀ U V W Z, pureRepairForm a b U W V Z = -pureRepairForm a b U V W Z :=
  four_swap23_of_diagonal_zero _ (pureRepairForm_additive a b) (pureRepairForm_pairs a b)
    (pureRepairForm_swap34 a b) (pureRepairForm_diagonal_zero a b c h)

/-- Pure four-form alternation for the partial-conjugation swap. -/
theorem pureRepairForm_swap24 {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) :
    ∀ U V W Z, pureRepairForm a b U Z W V = -pureRepairForm a b U V W Z :=
  four_swap24_of_diagonal_zero _ (pureRepairForm_additive a b) (pureRepairForm_pairs a b)
    (pureRepairForm_diagonal_zero a b c h)

/-- The actual mixed correction is minus the realigned pure cross repair. -/
theorem mixedRepairForm_transport {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (U V W Z : DepthVector m) : mixedRepairForm c U V W Z = -crossRepairForm a b U W V Z := by
  have he := repair_value_zero a b c h U W V Z
  simp only [pureRepairForm_diagonal_zero a b c h, mixedRepairForm_diagonal_zero a b c h,
    zero_add, add_zero] at he
  have h24 := four_swap24_of_diagonal_zero _ (mixedRepairForm_additive c)
    (mixedRepairForm_pairs c) (mixedRepairForm_diagonal_zero a b c h) U V W Z
  linear_combination (1 / 2 : ℂ) * he + h24

end
end ToeplitzSOS.Negative
