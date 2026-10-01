import ToeplitzSOS.Negative.SharpStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact scales and the final error budget

The exponents are manipulated symbolically. No giant natural power is
expanded.
-/

namespace ToeplitzSOS.Negative
noncomputable section

/-- The selected radial scale, expressed by real exponentiation. -/
def epsilon : ℝ := (2 : ℝ) ^ (-4980737 : ℝ)

/-- The stabilized corner depth used in the proof. -/
def cornerDepth : ℕ := symbolicTwoPow 9961474

/-- The chosen scale is strictly positive. -/
theorem epsilon_pos : 0 < epsilon := Real.rpow_pos_of_pos (by norm_num) _

/-- The ambient threshold is twice the corner depth, exactly. -/
theorem two_mul_cornerDepth : 2 * cornerDepth = sharpOrderThreshold := by
  have h : ∀ k, 2 * symbolicTwoPow k = symbolicTwoPow (k + 1) := by
    intro k
    simp only [symbolicTwoPow_eq, pow_succ]
    omega
  exact h _

/-- Every order in the headline range contains the selected depth corner. -/
theorem corner_fits {N : ℕ} (hN : sharpOrderThreshold ≤ N) : 2 * cornerDepth ≤ N := by
  rwa [two_mul_cornerDepth]

/-- The elementary tail exponent estimate, uniformly for all `k ≥ 16`. -/
theorem tail_exponent (k : ℕ) (hk : 16 ≤ k) : 8 * k + 40 ≤ 2 ^ (k - 2) := by
  have h : ∀ t : ℕ, 8 * (t + 16) + 40 ≤ 2 ^ (t + 14) := by
    intro t
    induction t with
    | zero => norm_num
    | succ t ih =>
      rw [Nat.succ_add, pow_succ]
      omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  convert h t using 1 <;> congr 1 <;> omega

/-- Entry budget for realigned terms at the sharper scale. -/
def realignedBound : ℝ := (2 : ℝ)⁻¹ ^ 18

/-- The interpolation gain at the sharper scale is at most `2^-18`. -/
theorem interpolation_constant :
    2^20 * epsilon ^ (1 / 131072 : ℝ) ≤ realignedBound := by
  have he : epsilon ^ (1 / 131072 : ℝ) ≤ (2 : ℝ)^(-38 : ℝ) := by
    unfold epsilon
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  have h := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2^20 by positivity)
  norm_num [realignedBound] at h ⊢
  exact h

/-- The selected epsilon satisfies the smallness condition of the analytic interface. -/
theorem epsilon_le_small : epsilon ≤ (2 : ℝ)⁻¹ ^ 16 := by
  have he : epsilon ≤ (2 : ℝ)^(-16 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  norm_num at he ⊢
  exact he

/-- The finite-vs-limit payment after the `2^60` coefficient budget is at most one. -/
theorem tangent_error_budget : (2 : ℝ)^90 * epsilon ≤ 1 := by
  have he : epsilon ≤ (2 : ℝ)^(-90 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2^90)
  norm_num at h ⊢
  exact h

/-- The two absolute error payments are far below the exact negative margin. -/
theorem final_budget :
    (3 * (2 : ℝ)^58) * (2^30 * epsilon) + (3 * 2^58) * realignedBound ≤ 2^42 := by
  have h := tangent_error_budget
  norm_num [realignedBound] at h ⊢
  linarith

end
end ToeplitzSOS.Negative
