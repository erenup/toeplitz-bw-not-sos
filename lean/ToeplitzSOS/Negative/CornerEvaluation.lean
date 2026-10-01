import ToeplitzSOS.Negative.CornerBaselineForms

/-!
# Complex evaluation of the corner polynomial

The polynomial identity is evaluated on four independently chosen complex
depth vectors, keeping the two symbol families and both sides explicit.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- Assign independent complex vectors to the four corner coordinate families. -/
def cornerAssignment {m : ℕ} (U V W Z : DepthVector m) : CornerVariable m → ℂ
  | (.x, false, p) => U p
  | (.y, false, p) => V p
  | (.x, true, p) => W p
  | (.y, true, p) => Z p

/-- Evaluate a real corner polynomial on four independent complex vectors. -/
def cornerEval {m : ℕ} (p : MvPolynomial (CornerVariable m) ℝ)
    (U V W Z : DepthVector m) : ℂ := eval₂ (algebraMap ℝ ℂ) (cornerAssignment U V W Z) p

private theorem eval_pure_false {m : ℕ} (p : PureIndex m) (U V W Z : DepthVector m) :
    cornerEval (pureWedge false p) U V W Z = vectorWedge p U V := by
  simp [cornerEval, pureWedge, cornerWedge, vectorWedge, cornerAssignment]

private theorem eval_pure_true {m : ℕ} (p : PureIndex m) (U V W Z : DepthVector m) :
    cornerEval (pureWedge true p) U V W Z = vectorWedge p W Z := by
  simp [cornerEval, pureWedge, cornerWedge, vectorWedge, cornerAssignment]

private theorem eval_mixed {m : ℕ} (p q : Fin m) (U V W Z : DepthVector m) :
    cornerEval (mixedWedge p q) U V W Z = U p * Z q - V p * W q := by
  simp only [cornerEval, mixedWedge, cornerWedge, eval₂_sub, eval₂_mul, eval₂_X, cornerAssignment]
  ring

/-- Complex evaluation of one complete three-sector row. -/
theorem cornerEval_linear {m : ℕ} (a b : PureIndex m → ℝ) (c : Fin m → Fin m → ℝ)
    (U V W Z : DepthVector m) :
    cornerEval (cornerLinear a b c) U V W Z =
      pureForm a U V + pureForm b W Z + mixedForm c U Z - mixedForm c V W := by
  unfold cornerLinear cornerEval
  simp only [eval₂_add, eval₂_sum, eval₂_mul, eval₂_C]
  change (∑ p, (a p : ℂ) * cornerEval (pureWedge false p) U V W Z) +
    (∑ p, (b p : ℂ) * cornerEval (pureWedge true p) U V W Z) +
    (∑ p, ∑ q, (c p q : ℂ) * cornerEval (mixedWedge p q) U V W Z) = _
  simp only [eval_pure_false, eval_pure_true, eval_mixed, mul_sub, sum_sub_distrib,
    pureForm, mixedForm, mul_assoc]
  ring

/-- Expanding a symmetric mixed tensor on the difference of two rank-one
vectors yields its diagonal terms and twice its polarized term. -/
theorem mixedTensor_wedge {m : ℕ} (G : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hG : ∀ p q r s, G p q r s = G r s p q) (U V W Z : DepthVector m) :
    (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      (G p q r s : ℂ) * (U p * Z q - V p * W q) * (U r * Z s - V r * W s)) =
    mixedTensor G U Z U Z + mixedTensor G V W V W - 2 * mixedTensor G U Z V W := by
  have he : (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      (G p q r s : ℂ) * (U p * Z q - V p * W q) * (U r * Z s - V r * W s)) =
      mixedTensor G U Z U Z + mixedTensor G V W V W -
        mixedTensor G U Z V W - mixedTensor G V W U Z := by
    simp only [mixedTensor, Fintype.sum_prod_type, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro s _
    ring
  rw [he, mixedTensor_pairs G hG V W U Z]
  ring

/-- The D/K/B polynomial evaluated on four independent vectors. -/
def baselineValue (m : ℕ) (U V W Z : DepthVector m) : ℂ :=
  diagonalForm m U V U V + diagonalForm m W Z W Z + 2 * crossForm m U V W Z +
    mixedBaselineForm m U Z U Z + mixedBaselineForm m V W V W -
      2 * mixedBaselineForm m U Z V W

/-- The literal baseline polynomial has the stated four-vector value. -/
theorem cornerEval_baseline (m : ℕ) (U V W Z : DepthVector m) :
    cornerEval (baselinePolynomial m) U V W Z = baselineValue m U V W Z := by
  unfold baselinePolynomial cornerEval
  simp only [eval₂_add, eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_ofNat]
  change (∑ p : PureIndex m, ((2 * (p.1.1.val + 1) * (p.1.2.val + 1) : ℝ) : ℂ) *
      (cornerEval (pureWedge false p) U V W Z ^ 2 + cornerEval (pureWedge true p) U V W Z ^ 2)) +
    2 * (∑ p : PureIndex m, ∑ q : PureIndex m,
      (baselineCrossEntry p q : ℂ) * cornerEval (pureWedge false p) U V W Z *
        cornerEval (pureWedge true q) U V W Z) +
    (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      (baselineMixedEntry p q r s : ℂ) * cornerEval (mixedWedge p q) U V W Z *
        cornerEval (mixedWedge r s) U V W Z) = _
  simp only [eval_pure_false, eval_pure_true, eval_mixed]
  rw [mixedTensor_wedge baselineMixedEntry baselineMixedEntry_symm]
  simp only [baselineValue, diagonalForm_eq, crossForm, pureTensor,
    mixedBaselineForm, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Complex.ofReal_one, mul_add, sum_add_distrib, pow_two, mul_assoc]
  ring

/-- The complete polynomial SOS identity holds on all complex depth vectors. -/
theorem corner_sos_value {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2)
    (U V W Z : DepthVector m) :
    baselineValue m U V W Z = ∑ j,
      (pureForm (a j) U V + pureForm (b j) W Z + mixedForm (c j) U Z - mixedForm (c j) V W) ^ 2 := by
  have he := congrArg (fun p => cornerEval p U V W Z) h
  rw [cornerEval_baseline] at he
  simpa only [cornerEval, eval₂_sum, eval₂_pow, ← cornerEval_linear] using he

end
end ToeplitzSOS.Negative
