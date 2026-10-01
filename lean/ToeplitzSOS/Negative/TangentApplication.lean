import ToeplitzSOS.Negative.TangentReference
import ToeplitzSOS.Negative.SliceBound

/-! # The finite-versus-tangent entry bound (27) -/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate

/-- Every witness speed is in the uniform disk used by the reciprocal estimates. -/
theorem witnessSpeed_norm_le (i : Fin 1024) : ‖witnessSpeed i‖ ≤ 512 := by
  have hr := witnessRealSpeed_bounds i
  have hi := witnessImagSpeed_abs_le i
  have h := Complex.norm_le_abs_re_add_abs_im (witnessSpeed i)
  change ‖witnessSpeed i‖ ≤ |witnessRealSpeed i| + |witnessImagSpeed i| at h
  rw [abs_of_nonneg (by linarith : 0 ≤ witnessRealSpeed i)] at h
  linarith

/-- Every witness node is in the radial disk required by the two finite tails. -/
theorem witnessNode_radial {ε : ℝ} (hε : 0 < ε) (i : Fin 1024) :
    ‖witnessNode ε i‖ ≤ Real.exp (-ε/2) := by
  have hr := (witnessRealSpeed_bounds i).1
  simp only [witnessNode, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]
  apply Real.exp_le_exp.mpr
  change -ε*witnessRealSpeed i ≤ -ε/2
  nlinarith

/-- The scaled rational reference has the tangent entry as its explicit approximation. -/
theorem reference_tangent_entry_bound (i j : Fin 1024) :
    |scaledKernel referenceL i j - Witness.tangentEntry i j| ≤ 2^20*epsilon := by
  have h := referenceL_tangent_bound epsilon_pos epsilon_le_small
    (a := witnessSpeed i) (b := conj (witnessSpeed i))
    (c := conj (witnessSpeed j)) (d := witnessSpeed j)
    (witnessRealSpeed_bounds i).1 (by simpa [witnessSpeed] using (witnessRealSpeed_bounds i).1)
    (by simpa [witnessSpeed] using (witnessRealSpeed_bounds j).1) (witnessRealSpeed_bounds j).1
    (witnessSpeed_norm_le i) (by simpa using witnessSpeed_norm_le i)
    (by simpa using witnessSpeed_norm_le j) (witnessSpeed_norm_le j)
  have ht : Witness.tangentKernel (witnessSpeed i) (conj (witnessSpeed i))
      (conj (witnessSpeed j)) (witnessSpeed j) = (Witness.tangentEntry i j : ℂ) :=
    Witness.tangentKernel_at_witness i j
  rw [ht] at h
  have h' : ‖(epsilon : ℂ)^4 * referenceL (witnessNode epsilon i) (conj (witnessNode epsilon i))
      (conj (witnessNode epsilon j)) (witnessNode epsilon j) - (Witness.tangentEntry i j : ℂ)‖ ≤
      2^20*epsilon := by
    simpa only [witnessNode, expSpeed, map_mul, map_neg, Complex.conj_I,
      ← Complex.exp_conj, Complex.conj_ofReal] using h
  have hr := Complex.abs_re_le_norm ((epsilon : ℂ)^4 * referenceL
    (witnessNode epsilon i) (conj (witnessNode epsilon i))
    (conj (witnessNode epsilon j)) (witnessNode epsilon j) - (Witness.tangentEntry i j : ℂ))
  apply le_trans _ h'
  simpa only [scaledKernel, ← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

/-- The finite baseline tail costs at most epsilon after scaling. -/
theorem baseline_reference_entry_bound (hA : AnalyticInputs) (i j : Fin 1024) :
    |scaledKernel (baselineL cornerDepth) i j - scaledKernel referenceL i j| ≤ epsilon := by
  have hi := witnessNode_radial epsilon_pos i
  have hj := witnessNode_radial epsilon_pos j
  have ht := (hA.baselineTail cornerDepth epsilon epsilon_pos
    (epsilon_le_small.trans (by norm_num)) (witnessNode epsilon i) (conj (witnessNode epsilon i))
    (conj (witnessNode epsilon j)) (witnessNode epsilon j) hi (by simpa using hi)
    (by simpa using hj) hj).2
  have hbudget := Analytic.scaled_tail_budget epsilon_pos epsilon_le_small cornerDepth_cast
  have hnonneg : 0 ≤ epsilon^4 := pow_nonneg epsilon_pos.le _
  have he := Complex.abs_re_le_norm (baselineL cornerDepth (witnessNode epsilon i)
    (conj (witnessNode epsilon i)) (conj (witnessNode epsilon j)) (witnessNode epsilon j) -
    referenceL (witnessNode epsilon i) (conj (witnessNode epsilon i))
      (conj (witnessNode epsilon j)) (witnessNode epsilon j))
  rw [Complex.sub_re] at he
  unfold scaledKernel
  rw [← mul_sub, abs_mul, abs_of_nonneg hnonneg]
  calc
    _ ≤ epsilon^4 * ‖baselineL cornerDepth (witnessNode epsilon i) (conj (witnessNode epsilon i))
        (conj (witnessNode epsilon j)) (witnessNode epsilon j) -
        referenceL (witnessNode epsilon i) (conj (witnessNode epsilon i))
          (conj (witnessNode epsilon j)) (witnessNode epsilon j)‖ := mul_le_mul_of_nonneg_left he hnonneg
    _ ≤ epsilon^4 * (2^30 * epsilon⁻¹^8 * Real.exp (-epsilon*cornerDepth/4)) :=
      mul_le_mul_of_nonneg_left ht hnonneg
    _ ≤ epsilon^4 * (2^32 * epsilon⁻¹^8 * Real.exp (-epsilon*cornerDepth/4)) := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (inv_nonneg.mpr epsilon_pos.le) 8)
    _ ≤ epsilon := hbudget

/-- The exact finite-versus-limit estimate (27) on every pair of witness nodes. -/
theorem baseline_tangent_entry_bound (hA : AnalyticInputs) (i j : Fin 1024) :
    |scaledKernel (baselineL cornerDepth) i j - Witness.tangentEntry i j| ≤ 2^30*epsilon := by
  have h1 := baseline_reference_entry_bound hA i j
  have h2 := reference_tangent_entry_bound i j
  have h := abs_sub_le (scaledKernel (baselineL cornerDepth) i j)
    (scaledKernel referenceL i j) (Witness.tangentEntry i j)
  have hp := epsilon_pos
  norm_num at h1 h2 ⊢
  linarith

/-- Concrete continuation bound for every algebraic corner Gram. -/
theorem CornerGram.realigned_bound (g : CornerGram cornerDepth) (hA : AnalyticInputs)
    (i j : Fin 1024) :
    |scaledRealignedEntry (plusBlock (baselineD cornerDepth) (baselineK cornerDepth) g.E g.T) i j| ≤
      realignedBound := by
  exact scaledRealignedEntry_bound hA _ g.plusRank (g.plusVector epsilon)
    (g.plusVector_norm epsilon) (g.plusVector_differentiable_left epsilon)
    (g.plusVector_differentiable_right epsilon)
    (g.plusVector_global epsilon_pos (epsilon_le_small.trans (by norm_num)))
    (g.plusVector_slice hA) i j

/-- The analytic inputs rule out the complete unrestricted algebraic corner interface. -/
theorem no_cornerGram (hA : AnalyticInputs) : ¬ Nonempty (CornerGram cornerDepth) := by
  rintro ⟨g⟩
  exact no_feasible_repaired_kernels cornerDepth g.E g.T g.realign_E
    (g.pairing_nonneg Witness.realCoefficient) (baseline_tangent_entry_bound hA) (g.realigned_bound hA)

end
end ToeplitzSOS.Negative
