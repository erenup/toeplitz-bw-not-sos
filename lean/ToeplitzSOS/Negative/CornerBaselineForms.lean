import ToeplitzSOS.Negative.CornerForms

/-!
# The baseline as forms on arbitrary complex depth vectors

The finite D/K/B coefficients are extended multilinearly. Specializing the
vectors to geometric sequences gives exactly the kernels of `Baseline`.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- The pure coefficient matrix evaluated on arbitrary depth vectors. -/
def pureTensor {m : ℕ} (G : PureIndex m → PureIndex m → ℝ) : VectorFourForm m :=
  fun U V W Z => ∑ p, ∑ q, (G p q : ℂ) * vectorWedge p U V * vectorWedge q W Z

/-- The mixed coefficient tensor evaluated on arbitrary depth vectors. -/
def mixedTensor {m : ℕ} (G : Fin m → Fin m → Fin m → Fin m → ℝ) : VectorFourForm m :=
  fun U V W Z => ∑ p : Fin m × Fin m, ∑ q : Fin m × Fin m,
    (G p.1 p.2 q.1 q.2 : ℂ) * U p.1 * V p.2 * W q.1 * Z q.2

private theorem vectorWedge_add_left {m : ℕ} (p : PureIndex m) (U V W : DepthVector m) :
    vectorWedge p (U + V) W = vectorWedge p U W + vectorWedge p V W := by
  simp only [vectorWedge, Pi.add_apply]
  ring

private theorem vectorWedge_add_right {m : ℕ} (p : PureIndex m) (U V W : DepthVector m) :
    vectorWedge p U (V + W) = vectorWedge p U V + vectorWedge p U W := by
  simp only [vectorWedge, Pi.add_apply]
  ring

/-- Any pure coefficient matrix defines a four-additive form. -/
theorem pureTensor_additive {m : ℕ} (G : PureIndex m → PureIndex m → ℝ) :
    FourAdditive (pureTensor G) := by
  constructor <;> intros <;>
    simp only [pureTensor, vectorWedge_add_left, vectorWedge_add_right,
      add_mul, mul_add, sum_add_distrib]

/-- Any mixed coefficient tensor defines a four-additive form. -/
theorem mixedTensor_additive {m : ℕ} (G : Fin m → Fin m → Fin m → Fin m → ℝ) :
    FourAdditive (mixedTensor G) := by
  constructor <;> intros <;>
    simp only [mixedTensor, Pi.add_apply, add_mul, mul_add, sum_add_distrib]

/-- Symmetric pure coefficients give symmetry of the two vector pairs. -/
theorem pureTensor_pairs {m : ℕ} (G : PureIndex m → PureIndex m → ℝ)
    (hG : ∀ p q, G p q = G q p) (U V W Z : DepthVector m) :
    pureTensor G U V W Z = pureTensor G W Z U V := by
  unfold pureTensor
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [hG q p]
  ring

/-- Symmetric mixed coefficients give symmetry of the two vector pairs. -/
theorem mixedTensor_pairs {m : ℕ} (G : Fin m → Fin m → Fin m → Fin m → ℝ)
    (hG : ∀ p q r s, G p q r s = G r s p q) (U V W Z : DepthVector m) :
    mixedTensor G U V W Z = mixedTensor G W Z U V := by
  unfold mixedTensor
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [hG q.1 q.2 p.1 p.2]
  ring

/-- Every pure tensor alternates in the last pair. -/
theorem pureTensor_swap {m : ℕ} (G : PureIndex m → PureIndex m → ℝ) (U V W Z : DepthVector m) :
    pureTensor G U V Z W = -pureTensor G U V W Z := by
  unfold pureTensor
  simp only [← sum_neg_distrib]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  unfold vectorWedge
  ring

/-- The pure diagonal matrix in full Gram units. -/
def baselineDiagonalEntry {m : ℕ} (p q : PureIndex m) : ℝ :=
  if p = q then 2 * (p.1.1.val + 1) * (p.1.2.val + 1) else 0

/-- Symmetry of the pure diagonal coefficients. -/
theorem baselineDiagonalEntry_symm {m : ℕ} (p q : PureIndex m) :
    baselineDiagonalEntry p q = baselineDiagonalEntry q p := by
  by_cases h : p = q
  · subst q; rfl
  · simp [baselineDiagonalEntry, h, Ne.symm h]

/-- Symmetry of the pure cross coefficients. -/
theorem baselineCrossEntry_symm {m : ℕ} (p q : PureIndex m) :
    baselineCrossEntry p q = baselineCrossEntry q p := by
  simp only [baselineCrossEntry, eq_comm, min_comm]

/-- Symmetry of the mixed baseline coefficients. -/
theorem baselineMixedEntry_symm {m : ℕ} (p q r s : Fin m) :
    baselineMixedEntry p q r s = baselineMixedEntry r s p q := by
  unfold baselineMixedEntry
  by_cases h : p = r ∧ q = s
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · have h' : ¬ (r = p ∧ s = q) := by tauto
    simp [h, eq_comm, min_comm]

/-- Transposing both mixed pairs preserves the baseline coefficient. -/
theorem baselineMixedEntry_transpose {m : ℕ} (p q r s : Fin m) :
    baselineMixedEntry q p s r = baselineMixedEntry p q r s := by
  have hc : q.val + p.val = s.val + r.val ↔ p.val + q.val = r.val + s.val := by omega
  have hm : min (min (q.val + 1) (p.val + 1)) (min (s.val + 1) (r.val + 1)) =
      min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) := by omega
  simp only [baselineMixedEntry, and_comm, hc, hm]
  split_ifs <;> push_cast <;> ring

/-- The diagonal baseline form. -/
def diagonalForm (m : ℕ) : VectorFourForm m := pureTensor baselineDiagonalEntry

/-- The pure cross baseline form. -/
def crossForm (m : ℕ) : VectorFourForm m := pureTensor baselineCrossEntry

/-- The mixed baseline form. -/
def mixedBaselineForm (m : ℕ) : VectorFourForm m := mixedTensor baselineMixedEntry

/-- The diagonal form as a single weighted wedge sum. -/
theorem diagonalForm_eq (m : ℕ) (U V W Z : DepthVector m) :
    diagonalForm m U V W Z = ∑ p : PureIndex m,
      (2 * (p.1.1.val + 1) * (p.1.2.val + 1) : ℂ) * vectorWedge p U V * vectorWedge p W Z := by
  classical
  simp only [diagonalForm, pureTensor, baselineDiagonalEntry,
    apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero, ite_mul, zero_mul,
    sum_ite_eq, mem_univ, ite_true]
  apply sum_congr rfl
  intro p _
  push_cast
  rfl

/-- A geometric depth vector with a specified complex node. -/
def geometricVector (m : ℕ) (x : ℂ) : DepthVector m := fun p => x ^ p.val

/-- Pure coefficient forms specialize to the geometric feature rows. -/
theorem pureForm_geometric {m : ℕ} (c : PureIndex m → ℝ) (x y : ℂ) :
    pureForm c (geometricVector m x) (geometricVector m y) = pureLinear c x y := rfl

/-- Mixed coefficient forms specialize to the geometric feature rows. -/
theorem mixedForm_geometric {m : ℕ} (c : Fin m → Fin m → ℝ) (x y : ℂ) :
    mixedForm c (geometricVector m x) (geometricVector m y) = mixedLinear c x y := rfl

/-- Specializing the pure diagonal form gives exactly `baselineD`. -/
theorem diagonalForm_geometric (m : ℕ) (x y z w : ℂ) :
    diagonalForm m (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w) = baselineD m x y z w := by
  rw [diagonalForm_eq]
  rfl

/-- Specializing the pure cross form gives exactly `baselineK`. -/
theorem crossForm_geometric (m : ℕ) (x y z w : ℂ) :
    crossForm m (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w) = baselineK m x y z w := by
  unfold crossForm pureTensor baselineK
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  simp only [baselineCrossEntry, vectorWedge, geometricVector, pureFeature]
  split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.ofReal_zero, zero_mul]

/-- Specializing the mixed form gives exactly `baselineB`. -/
theorem mixedBaselineForm_geometric (m : ℕ) (x y z w : ℂ) :
    mixedBaselineForm m (geometricVector m x) (geometricVector m y)
      (geometricVector m z) (geometricVector m w) = baselineB m x y z w := by
  simp only [mixedBaselineForm, mixedTensor, Fintype.sum_prod_type,
    geometricVector, baselineB, mixedKernel]

end
end ToeplitzSOS.Negative
