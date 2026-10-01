import Mathlib

/-!
# Finite dual pairings and entrywise error payments

The real coefficient vector is unrestricted. The squared l1 norm pays
for uniform entry bounds, including realigned entries whose array need
not be positive semidefinite.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset

/-- Real quadratic pairing of a matrix with a finite real coefficient vector. -/
def pairing {ι : Type*} [Fintype ι] (c : ι → ℝ) (A : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * A i j

/-- The coefficient budget used to pay for uniform entrywise errors. -/
def coefficientMass {ι : Type*} [Fintype ι] (c : ι → ℝ) : ℝ := ∑ i, |c i|

/-- The coefficient budget is nonnegative. -/
theorem coefficientMass_nonneg {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    0 ≤ coefficientMass c := sum_nonneg fun _ _ => abs_nonneg _

/-- Pairing is additive in the matrix. -/
theorem pairing_add {ι : Type*} [Fintype ι] (c : ι → ℝ) (A B : ι → ι → ℝ) :
    pairing c (A + B) = pairing c A + pairing c B := by
  simp [pairing, mul_add, sum_add_distrib]

/-- Pairing commutes with subtraction of matrices. -/
theorem pairing_sub {ι : Type*} [Fintype ι] (c : ι → ℝ) (A B : ι → ι → ℝ) :
    pairing c (A - B) = pairing c A - pairing c B := by
  simp [pairing, mul_sub, sum_sub_distrib]

/-- A uniform absolute entry bound is paid for by the squared l1 mass. -/
theorem abs_pairing_le {ι : Type*} [Fintype ι] (c : ι → ℝ) (A : ι → ι → ℝ)
    (δ : ℝ) (hA : ∀ i j, |A i j| ≤ δ) :
    |pairing c A| ≤ coefficientMass c ^ 2 * δ := by
  calc
    |pairing c A| ≤ ∑ i, |∑ j, c i * c j * A i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |c i * c j * A i j| :=
      sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (|c i| * |c j|) * δ := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = coefficientMass c ^ 2 * δ := by
      simp only [coefficientMass, pow_two, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Uniform approximation controls the error in the finite dual pairing. -/
theorem abs_pairing_sub_le {ι : Type*} [Fintype ι] (c : ι → ℝ) (A B : ι → ι → ℝ)
    (δ : ℝ) (h : ∀ i j, |A i j - B i j| ≤ δ) :
    |pairing c A - pairing c B| ≤ coefficientMass c ^ 2 * δ := by
  rw [← pairing_sub]
  exact abs_pairing_le c (A - B) δ h

/-- The final separation argument, independent of the origin of its matrices.
`H` is the nonnegative Gram pairing, `L` the fixed baseline, and `R` the
realigned remainder. Their exact cancellation is an explicit premise. -/
theorem finite_separation {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (H L R S : ι → ι → ℝ) (δ ρ C a : ℝ)
    (hcancel : H + R = L) (hpos : 0 ≤ pairing c H)
    (hmass : coefficientMass c ^ 2 ≤ C)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hlimit : ∀ i j, |L i j - S i j| ≤ δ)
    (hrealign : ∀ i j, |R i j| ≤ ρ)
    (hneg : pairing c S < -a) (hbudget : C * δ + C * ρ ≤ a) : False := by
  have he := abs_pairing_sub_le c L S δ hlimit
  have hr := abs_pairing_le c R ρ hrealign
  have hc : pairing c H + pairing c R = pairing c L := by
    rw [← pairing_add, hcancel]
  have he' := (abs_le.mp he).2
  have hr' := (abs_le.mp hr).1
  have hδ' := mul_le_mul_of_nonneg_right hmass hδ
  have hρ' := mul_le_mul_of_nonneg_right hmass hρ
  linarith

/-- A real rank-one Gram matrix has the expected squared pairing. -/
theorem pairing_rankOne {ι : Type*} [Fintype ι] (c f : ι → ℝ) :
    pairing c (fun i j => f i * f j) = (∑ i, c i * f i)^2 := by
  simp only [pairing, pow_two, sum_mul, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- Pairing commutes with a finite sum of matrices. -/
theorem pairing_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (A : κ → ι → ι → ℝ) :
    pairing c (fun i j => ∑ k, A k i j) = ∑ k, pairing c (A k) := by
  simp only [pairing, mul_sum]
  calc
    (∑ i, ∑ j, ∑ k, c i * c j * A k i j) =
        ∑ i, ∑ k, ∑ j, c i * c j * A k i j :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ k, ∑ i, ∑ j, c i * c j * A k i j := sum_comm

/-- Real part of a complex Gram matrix, in real coordinates. -/
def realGram {ι κ : Type*} [Fintype κ] (f : κ → ι → ℂ) : ι → ι → ℝ :=
  fun i j => ∑ k, ((f k i).re * (f k j).re + (f k i).im * (f k j).im)

/-- A finite complex Gram has nonnegative pairing against every real vector. -/
theorem pairing_realGram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (f : κ → ι → ℂ) : 0 ≤ pairing c (realGram f) := by
  unfold realGram
  rw [pairing_sum]
  refine sum_nonneg fun k _ => ?_
  change 0 ≤ pairing c ((fun i j => (f k i).re * (f k j).re) +
    (fun i j => (f k i).im * (f k j).im))
  rw [pairing_add, pairing_rankOne, pairing_rankOne]
  positivity

end
end ToeplitzSOS.Negative
