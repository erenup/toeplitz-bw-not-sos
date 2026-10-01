import ToeplitzSOS.Negative.CornerFactors
import ToeplitzSOS.Negative.CornerForcedMeans

/-!
# The actual finite mixed correction tensor

The correction is the Gram coefficient tensor of the explicit mixed rows
minus the baseline. Its generating kernel and both complete low means are
proved from the full SOS identity.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset MvPolynomial

/-- The real Gram coefficients of arbitrary mixed rows. -/
def mixedRowGram {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (p q u v : Fin m) : ℝ :=
  ∑ j, c j p q * c j u v

/-- The actual real coefficient tensor of the averaged mixed correction. -/
def mixedCorrectionEntry {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ)
    (p q u v : Fin m) : ℝ :=
  mixedRowGram (averagedMixedRows c) p q u v - baselineMixedEntry p q u v

private theorem mixedForm_pair_sum {m : ℕ} (c : Fin m → Fin m → ℝ) (U V : DepthVector m) :
    mixedForm c U V = ∑ p : Fin m × Fin m, (c p.1 p.2 : ℂ) * U p.1 * V p.2 := by
  rw [Fintype.sum_prod_type]
  rfl

/-- A mixed row Gram has exactly its displayed coefficient tensor. -/
theorem mixedFour_eq_tensor {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (U V W Z : DepthVector m) :
    mixedFour c U V W Z = mixedTensor (mixedRowGram c) U V W Z := by
  simp only [mixedFour, mixedForm_pair_sum, mixedTensor, mixedRowGram,
    Complex.ofReal_sum, Complex.ofReal_mul, sum_mul, mul_sum]
  conv_rhs => rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j _
  ring

/-- Subtracting coefficient tensors subtracts their four-vector forms. -/
theorem mixedTensor_sub {m : ℕ} (F G : Fin m → Fin m → Fin m → Fin m → ℝ)
    (U V W Z : DepthVector m) :
    mixedTensor (fun p q r s => F p q r s - G p q r s) U V W Z =
      mixedTensor F U V W Z - mixedTensor G U V W Z := by
  simp only [mixedTensor, Complex.ofReal_sub, sub_mul, sum_sub_distrib]

/-- The real correction tensor represents the actual averaged correction. -/
theorem mixedCorrectionEntry_form {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (U V W Z : DepthVector m) :
    mixedTensor (mixedCorrectionEntry c) U V W Z = mixedRepairForm c U V W Z := by
  unfold mixedCorrectionEntry
  rw [mixedTensor_sub, ← mixedFour_eq_tensor, averagedMixedRows_factor]
  rfl

/-- The correction's geometric tensor is exactly its four-slot generating kernel. -/
theorem mixedCorrectionEntry_kernel {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (x y z w : ℂ) :
    mixedKernel (fun p q u v => (mixedCorrectionEntry c p q u v : ℂ)) x y z w =
      mixedRepairForm c (geometricVector m x) (geometricVector m y)
        (geometricVector m z) (geometricVector m w) := by
  rw [← mixedCorrectionEntry_form]
  simp only [mixedTensor, Fintype.sum_prod_type, geometricVector, mixedKernel]

/-- Every mixed Gram coefficient tensor is symmetric. -/
theorem mixedRowGram_symm {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (p q u v : Fin m) :
    mixedRowGram c p q u v = mixedRowGram c u v p q := by
  unfold mixedRowGram
  apply sum_congr rfl
  intro j _
  ring

/-- The actual correction coefficient tensor is symmetric. -/
theorem mixedCorrectionEntry_symm {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (p q u v : Fin m) :
    mixedCorrectionEntry c p q u v = mixedCorrectionEntry c u v p q := by
  rw [mixedCorrectionEntry, mixedCorrectionEntry, mixedRowGram_symm,
    baselineMixedEntry_symm p q u v]

/-- Finite rational factors retain all complete low row means. -/
theorem averagedMixedRows_low_means {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) :
    ∀ g < m, ∀ j, ∑ p, ∑ q, (if p.val + q.val = g then averagedMixedRows c j p q else 0) = 0 := by
  intro g hg
  have hc := corner_sos_low_means a b c h g hg
  have ht (j : Fin r) : (∑ p : Fin m, ∑ q : Fin m, if p.val + q.val = g then c j q p else 0) = 0 := by
    rw [sum_comm]
    simpa only [add_comm] using hc j
  have hhalf (j : Fin r) : (∑ p : Fin m, ∑ q : Fin m,
      if p.val + q.val = g then (1 / 2 : ℝ) * c j p q else 0) = 0 := by
    simpa only [mul_sum, mul_ite, mul_zero] using congrArg (fun x : ℝ => (1 / 2) * x) (hc j)
  have hhalfT (j : Fin r) : (∑ p : Fin m, ∑ q : Fin m,
      if p.val + q.val = g then (1 / 2 : ℝ) * c j q p else 0) = 0 := by
    simpa only [mul_sum, mul_ite, mul_zero] using congrArg (fun x : ℝ => (1 / 2) * x) (ht j)
  have hab : ∀ j : Fin (r + r), ∑ p : Fin m, ∑ q : Fin m,
      (if p.val + q.val = g then
        (Fin.addCases (motive := fun _ => Fin m → Fin m → ℝ) (fun j p q => (1 / 2 : ℝ) * c j p q)
          (fun j p q => (1 / 2 : ℝ) * c j q p) j) p q else 0) = 0 := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [Fin.addCases_left] using hhalf i
    · intro i
      simpa only [Fin.addCases_right] using hhalfT i
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa only [averagedMixedRows, duplicateRows, Fin.addCases_left] using hab i
  · intro i
    simpa only [averagedMixedRows, duplicateRows, Fin.addCases_right] using hab i

/-- Vanishing low row means imply vanishing low means of their Gram coefficients. -/
theorem mixedRowGram_low_column {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ)
    (g : ℕ) (hc : ∀ j, ∑ p, ∑ q, (if p.val + q.val = g then c j p q else 0) = 0)
    (u v : Fin m) : ∑ p, ∑ q, (if p.val + q.val = g then mixedRowGram c p q u v else 0) = 0 := by
  have he (p q : Fin m) : (if p.val + q.val = g then mixedRowGram c p q u v else 0) =
      ∑ j, (if p.val + q.val = g then c j p q else 0) * c j u v := by
    by_cases hpq : p.val + q.val = g <;> simp [mixedRowGram, hpq]
  simp_rw [he]
  calc
    _ = ∑ p : Fin m, ∑ j : Fin r, ∑ q : Fin m,
        (if p.val + q.val = g then c j p q else 0) * c j u v := by
      apply sum_congr rfl
      intro p _
      exact sum_comm
    _ = ∑ j : Fin r, ∑ p : Fin m, ∑ q : Fin m,
        (if p.val + q.val = g then c j p q else 0) * c j u v := sum_comm
    _ = 0 := by
      simp only [← sum_mul, hc, zero_mul, sum_const_zero]

/-- Both complete low means of the actual mixed correction vanish. -/
theorem mixedCorrectionEntry_low_means {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) :
    CompleteLowMeans (fun p q u v => (mixedCorrectionEntry c p q u v : ℂ)) := by
  have hcol (g : ℕ) (hg : g < m) (u v : Fin m) :
      ∑ p, ∑ q, (if p.val + q.val = g then mixedCorrectionEntry c p q u v else 0) = 0 := by
    have hm := mixedRowGram_low_column (averagedMixedRows c) g (averagedMixedRows_low_means a b c h g hg) u v
    have hb := baselineMixedEntry_low_column g hg u v
    have he (p q : Fin m) : (if p.val + q.val = g then mixedCorrectionEntry c p q u v else 0) =
        (if p.val + q.val = g then mixedRowGram (averagedMixedRows c) p q u v else 0) -
        (if p.val + q.val = g then baselineMixedEntry p q u v else 0) := by
      split_ifs <;> simp [mixedCorrectionEntry]
    simp only [he, sum_sub_distrib, hm, hb, sub_self]
  constructor
  · intro g hg u v
    simpa only [Complex.ofReal_sum, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) (hcol g hg u v)
  · intro g hg p q
    simp_rw [mixedCorrectionEntry_symm c p q]
    simpa only [Complex.ofReal_sum, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) (hcol g hg p q)

/-- A mixed form on two coordinate vectors is its corresponding coefficient. -/
theorem mixedForm_basis {m : ℕ} (c : Fin m → Fin m → ℝ) (p q : Fin m) :
    mixedForm c (Pi.single p 1) (Pi.single q 1) = (c p q : ℂ) := by
  simp [mixedForm, Pi.single_apply]

/-- A mixed tensor on four coordinate vectors is its corresponding entry. -/
theorem mixedTensor_basis {m : ℕ} (G : Fin m → Fin m → Fin m → Fin m → ℝ) (p q u v : Fin m) :
    mixedTensor G (Pi.single p 1) (Pi.single q 1) (Pi.single u 1) (Pi.single v 1) = (G p q u v : ℂ) := by
  simp [mixedTensor, Fintype.sum_prod_type, Pi.single_apply]

/-- The averaged mixed Gram has the baseline diagonal, for every arbitrary SOS. -/
theorem averagedMixedRows_diagonal {m r : ℕ} (a b : Fin r → PureIndex m → ℝ)
    (c : Fin r → Fin m → Fin m → ℝ)
    (h : baselinePolynomial m = ∑ j, cornerLinear (a j) (b j) (c j) ^ 2) (p q : Fin m) :
    mixedRowGram (averagedMixedRows c) p q p q = baselineMixedEntry p q p q := by
  have he := mixedRepairForm_diagonal_zero a b c h (Pi.single p 1) (Pi.single q 1)
  change meanMixed c (Pi.single p 1) (Pi.single q 1) (Pi.single p 1) (Pi.single q 1) -
    mixedTensor baselineMixedEntry (Pi.single p 1) (Pi.single q 1) (Pi.single p 1) (Pi.single q 1) = 0 at he
  rw [← averagedMixedRows_factor, mixedFour_eq_tensor, mixedTensor_basis, mixedTensor_basis] at he
  exact_mod_cast sub_eq_zero.mp he

end
end ToeplitzSOS.Negative
