import ToeplitzSOS.Negative.WitnessCertificate
import ToeplitzSOS.Negative.Pairing
import ToeplitzSOS.Negative.Nodes

/-!
# The exact finite Hermitian tangent witness

The integer certificate is connected to the real rational kernel, and
hence to its finite quadratic pairing. There are exactly 1024 indices, including both signs.
-/

namespace ToeplitzSOS.Negative.Witness
noncomputable section
set_option maxRecDepth 10000
open Finset

/-- The four-slot tangent kernel (20), with the second node already conjugated. -/
def tangentKernel : FourKernel := fun a b c d =>
  2 * (2 / ((a + c) * (b + d))^2 + 1 / ((a + b) * (c + d))^2 -
    1 / (((a + c) * (b + d)) * ((a + b) * (c + d))))

/-- Real coefficients of the full 1024-point witness. -/
def realCoefficient (i : Fin 1024) : ℝ := coefficient i.val

/-- The real Hermitian entry of the tangent kernel at the signed speed points. -/
def tangentEntry (i j : Fin 1024) : ℝ :=
  2 * (2 / (denomA i.val j.val : ℝ)^2 + 1 / (denomC i.val j.val : ℝ)^2 -
    1 / ((denomA i.val j.val : ℝ) * (denomC i.val j.val : ℝ)))

/-- The real entry checked by integer arithmetic is exactly the complex
Hermitian tangent entry at the specified speeds, with no speed-sum factor. -/
theorem tangentKernel_at_witness (i j : Fin 1024) :
    tangentKernel (witnessSpeed i) (star (witnessSpeed i))
      (star (witnessSpeed j)) (witnessSpeed j) = (tangentEntry i j : ℂ) := by
  simp only [Complex.star_def]
  unfold tangentKernel
  rw [witness_denomA, witness_denomC]
  simp [tangentEntry]

private theorem radius_pos (i : ℕ) : 0 < radius i := by unfold radius; positivity

private theorem denomA_pos (i j : ℕ) : 0 < denomA i j := by
  have hi := radius_pos i
  have hj := radius_pos j
  unfold denomA
  nlinarith [sq_nonneg (sign i * frequency i - sign j * frequency j)]

private theorem denomC_pos (i j : ℕ) : 0 < denomC i j := by
  have hi := radius_pos i
  have hj := radius_pos j
  unfold denomC
  positivity

private theorem entryDenominator_pos (i j : ℕ) : 0 < entryDenominator i j := by
  have ha := denomA_pos i j
  have hc := denomC_pos i j
  unfold entryDenominator
  positivity

private theorem div_lt_ediv_add_one (a d : ℤ) (hd : 0 < d) :
    (a : ℝ) / (d : ℝ) < ((a / d + 1 : ℤ) : ℝ) := by
  have hr := Int.emod_lt_of_pos a hd
  have he := Int.emod_add_mul_ediv a d
  have hi : a < (a / d + 1) * d := by nlinarith
  apply (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast hi

private theorem weightedEntry_eq (i j : Fin 1024) :
    realCoefficient i * realCoefficient j * tangentEntry i j =
      (entryNumerator i.val j.val : ℝ) / (entryDenominator i.val j.val : ℝ) := by
  have ha : (denomA i.val j.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (denomA_pos _ _))
  have hc : (denomC i.val j.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (denomC_pos _ _))
  unfold realCoefficient tangentEntry entryNumerator entryDenominator
  push_cast
  field_simp

private theorem weightedEntry_le_upper (i j : Fin 1024) :
    realCoefficient i * realCoefficient j * tangentEntry i j ≤
      (upperEntry i.val j.val : ℝ) / 2^64 := by
  rw [weightedEntry_eq]
  have h := div_lt_ediv_add_one (2^64 * entryNumerator i.val j.val)
    (entryDenominator i.val j.val) (entryDenominator_pos _ _)
  change _ < (upperEntry i.val j.val : ℝ) at h
  push_cast at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^64)).mpr
  convert h.le using 1
  ring

private theorem list_range_sum_eq (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

private theorem sum_range_blocks (f : ℕ → ℤ) (k n : ℕ) :
    ∑ i ∈ range (k * n), f i = ∑ b ∈ range n, ∑ r ∈ range k, f (k * b + r) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

private theorem fullUpper_eq : fullUpper =
    ∑ i : Fin 1024, ∑ j : Fin 1024, upperEntry i.val j.val := by
  simp only [fullUpper, upperBlock, list_range_sum_eq]
  rw [← sum_range_blocks (fun i => ∑ j ∈ range 1024, upperEntry i j) 16 64]
  symm
  calc
    (∑ i : Fin 1024, ∑ j : Fin 1024, upperEntry i.val j.val) =
        ∑ i : Fin 1024, ∑ j ∈ range 1024, upperEntry i.val j :=
      sum_congr rfl fun i _ => Fin.sum_univ_eq_sum_range (upperEntry i.val) 1024
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range 1024, upperEntry i j) 1024

/-- The full real pairing lies below the directed, kernel-checked upper enclosure. -/
theorem pairing_le_fullUpper :
    pairing realCoefficient tangentEntry ≤ (fullUpper : ℝ) / 2^64 := by
  have h := sum_le_sum (s := (univ : Finset (Fin 1024))) fun i _ =>
    sum_le_sum (s := (univ : Finset (Fin 1024))) fun j _ => weightedEntry_le_upper i j
  simpa only [pairing, ← sum_div, ← Int.cast_sum, ← fullUpper_eq] using h

/-- The exact 1024-point real Hermitian pairing is below `-2^42`. -/
theorem tangent_pairing_lt : pairing realCoefficient tangentEntry < -(2 : ℝ)^42 := by
  apply lt_of_le_of_lt pairing_le_fullUpper
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2^64)).mpr
  exact_mod_cast fullUpper_lt

/-- Exact integer l1 mass of the witness, before casting to the reals. -/
def integerMass : ℤ := ((List.range 1024).map (fun i => |coefficient i|)).sum

/-- The integer coefficient budget is checked by kernel reduction. -/
theorem integerMass_eq : integerMass = 859652168 := by decide +kernel

/-- The full real coefficient mass is exactly the value. -/
theorem coefficientMass_eq : coefficientMass realCoefficient = 859652168 := by
  have h : ∑ i : Fin 1024, |coefficient i.val| = (859652168 : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => |coefficient i|) 1024, ← list_range_sum_eq]
    exact integerMass_eq
  have hc := congrArg (fun z : ℤ => (z : ℝ)) h
  simpa only [Int.cast_sum, Int.cast_abs, Int.cast_ofNat, coefficientMass,
    realCoefficient] using hc

/-- The squared coefficient mass is below the `2^60` payment budget. -/
theorem coefficientMass_sq_le : coefficientMass realCoefficient ^ 2 ≤ (2 : ℝ)^60 := by
  rw [coefficientMass_eq]
  norm_num

/-- The exact mass leaves ample room in the sharper-scale payment. -/
theorem coefficientMass_sq_le_sharp : coefficientMass realCoefficient ^ 2 ≤ 3*(2 : ℝ)^58 := by
  rw [coefficientMass_eq]
  norm_num

end
end ToeplitzSOS.Negative.Witness
