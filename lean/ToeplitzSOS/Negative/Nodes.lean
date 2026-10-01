import ToeplitzSOS.Negative.AnalyticInputs
import ToeplitzSOS.Negative.WitnessArithmetic

/-!
# Exact complex speed coordinates of the finite witness

Every one of the 1024² realigned node pairs lies in the rectangle covered
by the continuation estimate. This is a uniform symbolic proof, rather
than a numerical enumeration.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open ComplexConjugate

/-- Real speed of a witness point. -/
def witnessRealSpeed (i : Fin 1024) : ℝ := Witness.radius i.val

/-- Signed imaginary speed of a witness point. -/
def witnessImagSpeed (i : Fin 1024) : ℝ := Witness.sign i.val * Witness.frequency i.val

/-- The first speed of the conjugate pair in (22). -/
def witnessSpeed (i : Fin 1024) : ℂ := ⟨witnessRealSpeed i, witnessImagSpeed i⟩

/-- First continuation coordinate of a realigned node pair. -/
def pairU (i j : Fin 1024) : ℂ :=
  ⟨(witnessRealSpeed i + witnessRealSpeed j) / 2,
    (witnessImagSpeed i - witnessImagSpeed j) / 2⟩

/-- Second continuation coordinate of a realigned node pair. -/
def pairV (i j : Fin 1024) : ℂ :=
  ⟨(witnessImagSpeed i + witnessImagSpeed j) / 2,
    -(witnessRealSpeed i - witnessRealSpeed j) / 2⟩

/-- Every real speed is between one and two. -/
theorem witnessRealSpeed_bounds (i : Fin 1024) :
    1 ≤ witnessRealSpeed i ∧ witnessRealSpeed i ≤ 2 := by
  have hi := i.isLt
  have h : 1 ≤ i.val / 512 + 1 ∧ i.val / 512 + 1 ≤ 2 := by omega
  simpa only [witnessRealSpeed, Witness.radius, Int.cast_natCast] using
    (show (1 : ℝ) ≤ (i.val / 512 + 1 : ℕ) ∧ (i.val / 512 + 1 : ℕ) ≤ (2 : ℝ) by
      exact_mod_cast h)

/-- The imaginary speed has absolute value at most 256. -/
theorem witnessImagSpeed_abs_le (i : Fin 1024) : |witnessImagSpeed i| ≤ 256 := by
  have hf : (i.val / 2 % 256 + 1 : ℕ) ≤ 256 := by omega
  have hs : |(Witness.sign i.val : ℝ)| = 1 := by
    unfold Witness.sign
    split_ifs <;> norm_num
  unfold witnessImagSpeed
  rw [abs_mul, hs, one_mul]
  unfold Witness.frequency
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hf

/-- All 1024² speed pairs lie in the closed target region, with endpoints included. -/
theorem pair_mem_speedRegion (i j : Fin 1024) : SpeedRegion (pairU i j) (pairV i j) := by
  obtain ⟨hi1, hi2⟩ := witnessRealSpeed_bounds i
  obtain ⟨hj1, hj2⟩ := witnessRealSpeed_bounds j
  obtain ⟨hi3, hi4⟩ := abs_le.mp (witnessImagSpeed_abs_le i)
  obtain ⟨hj3, hj4⟩ := abs_le.mp (witnessImagSpeed_abs_le j)
  dsimp [SpeedRegion, pairU, pairV]
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩ <;>
    rw [abs_le] <;> constructor <;> linarith

/-- Recover the first speed from the continuation coordinates. -/
theorem pairU_add_I_pairV (i j : Fin 1024) :
    pairU i j + Complex.I * pairV i j = witnessSpeed i := by
  apply Complex.ext <;> simp [pairU, pairV, witnessSpeed, Complex.mul_re, Complex.mul_im] <;> ring

/-- Recover the conjugated second speed from the continuation coordinates. -/
theorem pairU_sub_I_pairV (i j : Fin 1024) :
    pairU i j - Complex.I * pairV i j = conj (witnessSpeed j) := by
  apply Complex.ext <;> simp [pairU, pairV, witnessSpeed, Complex.mul_re, Complex.mul_im] <;> ring

/-- The first finite geometric node in (25); the second is its conjugate. -/
def witnessNode (ε : ℝ) (i : Fin 1024) : ℂ :=
  Complex.I * Complex.exp (-(ε : ℂ) * witnessSpeed i)

/-- The first realigned node has the precise two-variable analytic parametrization. -/
theorem witnessNode_pair (ε : ℝ) (i j : Fin 1024) :
    witnessNode ε i = Complex.I * Complex.exp (-(ε : ℂ) * (pairU i j + Complex.I * pairV i j)) := by
  rw [pairU_add_I_pairV]
  rfl

/-- The conjugated second realigned node has the matching parametrization. -/
theorem conj_witnessNode_pair (ε : ℝ) (i j : Fin 1024) :
    conj (witnessNode ε j) =
      -Complex.I * Complex.exp (-(ε : ℂ) * (pairU i j - Complex.I * pairV i j)) := by
  rw [pairU_sub_I_pairV]
  simp [witnessNode, ← Complex.exp_conj]

/-- The first tangent denominator at a conjugate speed pair is the positive
integer `A₀` used by the exact checker. -/
theorem witness_denomA (i j : Fin 1024) :
    (witnessSpeed i + conj (witnessSpeed j)) *
      (conj (witnessSpeed i) + witnessSpeed j) = (Witness.denomA i.val j.val : ℂ) := by
  apply Complex.ext
  all_goals simp [witnessSpeed, witnessRealSpeed, witnessImagSpeed, Witness.denomA,
    pow_two, Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- The second tangent denominator is exactly `C₀ = 4 r t`. -/
theorem witness_denomC (i j : Fin 1024) :
    (witnessSpeed i + conj (witnessSpeed i)) *
      (conj (witnessSpeed j) + witnessSpeed j) = (Witness.denomC i.val j.val : ℂ) := by
  apply Complex.ext
  all_goals simp [witnessSpeed, witnessRealSpeed, witnessImagSpeed, Witness.denomC,
    Complex.mul_re, Complex.mul_im]
  all_goals ring

end
end ToeplitzSOS.Negative
