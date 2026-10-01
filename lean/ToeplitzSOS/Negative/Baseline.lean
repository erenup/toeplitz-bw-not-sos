import ToeplitzSOS.Negative.Kernels

/-!
# Literal formulas for the finite stabilized-corner baseline

The definitions use the full Gram normalization of the stabilized corner.
Pure indices are increasing zero-based depth pairs. No infinite completion
or restriction of the repair space is part of these definitions.
The rational reference kernels are `referenceD` and `referenceK`.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset

/-- Increasing pairs of depths for a pure wedge block. -/
abbrev PureIndex (m : ℕ) := {pq : Fin m × Fin m // pq.1 < pq.2}

/-- The geometric wedge feature at an increasing depth pair. -/
def pureFeature {m : ℕ} (pq : PureIndex m) (x y : ℂ) : ℂ :=
  x ^ pq.1.1.val * y ^ pq.1.2.val - x ^ pq.1.2.val * y ^ pq.1.1.val

/-- Finite pure diagonal kernel, with diagonal weight `2(p+1)(q+1)`. -/
def baselineD (m : ℕ) : FourKernel := fun x y z w =>
  ∑ pq : PureIndex m, (2 * (pq.1.1.val + 1) * (pq.1.2.val + 1) : ℂ) *
    pureFeature pq x y * pureFeature pq z w

/-- The signed same-gap pure cross kernel from (1). -/
def baselineK (m : ℕ) : FourKernel := fun x y z w =>
  ∑ pq : PureIndex m, ∑ rs : PureIndex m,
    if pq.1.2.val - pq.1.1.val = rs.1.2.val - rs.1.1.val then
      (-2 * (min (pq.1.1.val + 1) (rs.1.1.val + 1) : ℕ) : ℂ) *
        pureFeature pq x y * pureFeature rs z w
    else 0

/-- The baseline mixed coefficient in full Gram units. -/
def baselineMixedEntry {m : ℕ} (p q r s : Fin m) : ℝ :=
  (if p = r ∧ q = s then 2 * (p.val + 1) * (q.val + 1) else 0) -
    (if p.val + q.val = r.val + s.val then
      2 * (min (min (p.val + 1) (q.val + 1)) (min (r.val + 1) (s.val + 1)) : ℕ)
    else 0)

/-- The generating polynomial of a finite mixed coefficient tensor. -/
def mixedKernel {m : ℕ} (C : Fin m → Fin m → Fin m → Fin m → ℂ) : FourKernel :=
  fun x y z w => ∑ p, ∑ q, ∑ r, ∑ s,
    C p q r s * x ^ p.val * y ^ q.val * z ^ r.val * w ^ s.val

/-- The finite mixed baseline kernel from (1). -/
def baselineB (m : ℕ) : FourKernel :=
  mixedKernel (fun p q r s : Fin m => (baselineMixedEntry p q r s : ℂ))

/-- The finite pure reference `D+K`. -/
def baselineQ (m : ℕ) : FourKernel := baselineD m + baselineK m

/-- The fixed finite cancellation kernel (3). -/
def baselineL (m : ℕ) : FourKernel := baselineB m + baselineD m + realign (baselineQ m)

/-- The first vanishing denominator. -/
def factorA (x y z w : ℂ) : ℂ := (1 - x * z) * (1 - y * w)

/-- The denominator that stays nonzero at the conjugate phase used in the proof. -/
def factorB (x y z w : ℂ) : ℂ := (1 - x * w) * (1 - y * z)

/-- The second vanishing denominator. -/
def factorC (x y z w : ℂ) : ℂ := (1 - x * y) * (1 - z * w)

/-- Rational infinite reference for the pure diagonal kernel, (5). -/
def referenceD : FourKernel := fun x y z w =>
  2 * ((factorA x y z w)⁻¹ ^ 2 - (factorB x y z w)⁻¹ ^ 2)

/-- Rational infinite reference for the mixed kernel, (5). -/
def referenceB : FourKernel := fun x y z w =>
  2 * ((factorA x y z w)⁻¹ ^ 2 - (factorA x y z w * factorB x y z w)⁻¹)

/-- Rational infinite reference for `D+K`, (5). -/
def referenceQ : FourKernel := fun x y z w =>
  referenceD x y z w - 2 * (factorB x y z w - factorA x y z w) /
    (factorA x y z w * factorB x y z w * factorC x y z w)

/-- Simplified rational reference for the fixed cancellation kernel, (6). -/
def referenceL : FourKernel := fun x y z w =>
  2 * (2 * (factorA x y z w)⁻¹ ^ 2 + (factorC x y z w)⁻¹ ^ 2 -
    (factorA x y z w * factorC x y z w)⁻¹ - 2 * (factorB x y z w)⁻¹ ^ 2)

/-- Realignment interchanges `A` and `C` and fixes `B`. -/
theorem realign_factors : realign factorA = factorC ∧
    realign factorC = factorA ∧ realign factorB = factorB := by
  refine ⟨rfl, rfl, ?_⟩
  funext x y z w
  simp only [realign, factorB]
  ring

/-- The rational cancellation identity (6), with its necessary nonzero
factor hypotheses made explicit. -/
theorem reference_cancellation (x y z w : ℂ)
    (hA : factorA x y z w ≠ 0) (hB : factorB x y z w ≠ 0)
    (hC : factorC x y z w ≠ 0) :
    referenceB x y z w + referenceD x y z w + realign referenceQ x y z w =
      referenceL x y z w := by
  have hB' : factorB x z y w = factorB x y z w := by
    simp only [factorB]; ring
  simp only [referenceB, referenceD, referenceQ, referenceL, realign,
    show factorA x z y w = factorC x y z w from rfl,
    show factorC x z y w = factorA x y z w from rfl, hB']
  field_simp
  ring

/-- The repeated-node rational simplification underlying the conjugate
formula (11), before substituting polar coordinates. -/
theorem referenceQ_repeated (x y : ℂ)
    (hA : factorA x y y x ≠ 0) (hB : factorB x y y x ≠ 0) :
    referenceQ x y y x = 2 * (factorB x y y x - factorA x y y x) /
      (factorA x y y x * factorB x y y x ^ 2) := by
  unfold referenceQ referenceD
  rw [show factorC x y y x = factorA x y y x from rfl]
  field_simp
  ring

end
end ToeplitzSOS.Negative
