import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Vector-valued weighted maximum modulus

The quantitative continuation comparison follows by multiplying the vector
by a holomorphic exponential. This formulation works at zeros and in arbitrary
complex normed spaces; no logarithm of the vector norm is needed.
-/

open Set Complex

namespace ToeplitzSOS.Negative.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Maximum modulus with a holomorphic exponential weight. -/
theorem norm_le_exp_weight {U : Set ℂ} (hU : Bornology.IsBounded U)
    {F : ℂ → E} {H : ℂ → ℂ} (hF : DiffContOnCl ℂ F U)
    (hH : Differentiable ℂ H) {C t : ℝ}
    (hb : ∀ z ∈ frontier U, ‖F z‖ ≤ C * Real.exp (t * (H z).re))
    {z : ℂ} (hz : z ∈ closure U) :
    ‖F z‖ ≤ C * Real.exp (t * (H z).re) := by
  let G : ℂ → E := fun w => Complex.exp (-(t : ℂ) * H w) • F w
  have hd : DiffContOnCl ℂ G U :=
    ((hH.const_mul (-(t : ℂ))).cexp.diffContOnCl).smul hF
  have hn (w : ℂ) : ‖G w‖ = Real.exp (-(t * (H w).re)) * ‖F w‖ := by
    simp [G, norm_smul, Complex.norm_exp]
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le hU hd
    (C := C) (fun w hw => ?_) hz
  · rw [hn] at h
    calc
      ‖F z‖ = (Real.exp (-(t * (H z).re)) * ‖F z‖) *
          Real.exp (t * (H z).re) := by
        rw [mul_right_comm, ← Real.exp_add]
        simp
      _ ≤ C * Real.exp (t * (H z).re) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  · rw [hn]
    calc
      _ ≤ Real.exp (-(t * (H w).re)) *
          (C * Real.exp (t * (H w).re)) :=
        mul_le_mul_of_nonneg_left (hb w hw) (Real.exp_pos _).le
      _ = C := by rw [mul_left_comm, ← Real.exp_add]; simp

/-- The squared-norm comparison in the normalization used by the negative proof. -/
theorem norm_sq_le_exp_weight {U : Set ℂ} (hU : Bornology.IsBounded U)
    {F : ℂ → E} {H : ℂ → ℂ} (hF : DiffContOnCl ℂ F U)
    (hH : Differentiable ℂ H) {B t : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z ∈ frontier U, ‖F z‖ ^ 2 ≤ B * Real.exp (t * (H z).re))
    {z : ℂ} (hz : z ∈ closure U) :
    ‖F z‖ ^ 2 ≤ B * Real.exp (t * (H z).re) := by
  have he (w : ℂ) : (Real.sqrt B * Real.exp (t / 2 * (H w).re)) ^ 2 =
      B * Real.exp (t * (H w).re) := by
    rw [mul_pow, Real.sq_sqrt hB, ← Real.exp_nat_mul]
    congr 2
    ring
  have h := norm_le_exp_weight hU hF hH (C := Real.sqrt B) (t := t / 2)
    (fun w hw => ?_) hz
  · rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  · have hb' := hb w hw
    rw [← he] at hb'
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B)
      (Real.exp_pos _).le)).mp hb'

/-- One distinguished boundary piece improves the interior bound by its weight.
The real part of `H` is zero off that piece, and lies in `[0,1]` on it. -/
theorem norm_sq_le_rpow_weight {U side : Set ℂ} (hU : Bornology.IsBounded U)
    {F : ℂ → E} {H : ℂ → ℂ} (hF : DiffContOnCl ℂ F U)
    (hH : Differentiable ℂ H) {B ε α : ℝ} (hB : 0 ≤ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hglobal : ∀ z ∈ frontier U, ‖F z‖ ^ 2 ≤ B)
    (hside : ∀ z ∈ frontier U ∩ side, ‖F z‖ ^ 2 ≤ B * ε ^ α)
    (hweight : ∀ z ∈ frontier U ∩ side, (H z).re ≤ 1)
    (hzero : ∀ z ∈ frontier U \ side, (H z).re = 0)
    {z : ℂ} (hz : z ∈ closure U) :
    ‖F z‖ ^ 2 ≤ B * ε ^ (α * (H z).re) := by
  rw [Real.rpow_def_of_pos hε]
  apply norm_sq_le_exp_weight hU hF hH hB (t := α * Real.log ε) ?_ hz |>.trans_eq
    (by congr 2; ring)
  intro w hw
  by_cases hs : w ∈ side
  · calc
      ‖F w‖ ^ 2 ≤ B * ε ^ α := hside w ⟨hw, hs⟩
      _ ≤ B * Real.exp (α * Real.log ε * (H w).re) := by
        apply mul_le_mul_of_nonneg_left _ hB
        rw [Real.rpow_def_of_pos hε]
        apply Real.exp_le_exp.mpr
        have ht : α * Real.log ε ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hα (Real.log_nonpos hε.le hε1)
        nlinarith [hweight w ⟨hw, hs⟩]
  · simpa [hzero w ⟨hw, hs⟩] using hglobal w hw

end ToeplitzSOS.Negative.Analytic
