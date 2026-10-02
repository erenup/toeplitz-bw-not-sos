import Mathlib

/-!
# Algebra of the stabilized-corner kernels

All kernels use four bilinear slots; realignment swaps slots two and three.
The cancellation and partial-conjugation identities are algebraic: the
positivity of the blocks is not a premise of those identities.
-/

namespace ToeplitzSOS.Negative

noncomputable section
open ComplexConjugate

/-- A generating kernel, with four complex bilinear arguments. -/
abbrev FourKernel := ℂ → ℂ → ℂ → ℂ → ℂ

/-- Realignment exchanges exactly slots two and three. -/
def realign (F : FourKernel) : FourKernel := fun x y z w => F x z y w

/-- Realignment is an involution. -/
@[simp] theorem realign_realign (F : FourKernel) : realign (realign F) = F := rfl

/-- Realignment preserves addition. -/
@[simp] theorem realign_add (F G : FourKernel) : realign (F + G) = realign F + realign G := rfl

/-- Realignment preserves subtraction. -/
@[simp] theorem realign_sub (F G : FourKernel) : realign (F - G) = realign F - realign G := rfl

/-- The plus pure block of an averaged repaired Gram. -/
def plusBlock (D K E T : FourKernel) : FourKernel := D + E + K + T

/-- The minus pure block of an averaged repaired Gram. -/
def minusBlock (D K E T : FourKernel) : FourKernel := D + E - K - T

/-- The mixed block, including its minus transport sign. -/
def mixedBlock (B T : FourKernel) : FourKernel := B - realign T

/-- The mean of the two pure signs. -/
def pureMean (D K E T : FourKernel) : FourKernel :=
  fun x y z w => (plusBlock D K E T x y z w + minusBlock D K E T x y z w) / 2

/-- The pure mean eliminates the cross repair. -/
theorem pureMean_eq (D K E T : FourKernel) : pureMean D K E T = D + E := by
  funext x y z w
  simp only [pureMean, plusBlock, minusBlock, Pi.add_apply, Pi.sub_apply]
  ring

/-- Complete cancellation of both repairs, with no positivity premise. -/
theorem cancellation (D K B E T : FourKernel) (hE : realign E = -E) :
    mixedBlock B T + pureMean D K E T + realign (plusBlock D K E T) =
      B + D + realign (D + K) := by
  rw [pureMean_eq]
  simp only [mixedBlock, plusBlock, realign_add, hE]
  abel

/-- Hermitian diagonal of a bilinear generating kernel. -/
def hermitianDiagonal (F : FourKernel) (x y : ℂ) : ℂ := F x y (conj x) (conj y)

/-- Four-form alternation cancels the two partially conjugated pure means,
before using any PSD inequalities. -/
theorem partial_conjugation (D K E T : FourKernel)
    (hE : ∀ x y z w, E x w z y = - E x y z w) (x y : ℂ) :
    hermitianDiagonal (plusBlock D K E T) x y +
      hermitianDiagonal (minusBlock D K E T) x y +
      hermitianDiagonal (plusBlock D K E T) x (conj y) +
      hermitianDiagonal (minusBlock D K E T) x (conj y) =
      2 * hermitianDiagonal D x y + 2 * hermitianDiagonal D x (conj y) := by
  simp only [hermitianDiagonal, plusBlock, minusBlock, Pi.add_apply, Pi.sub_apply,
    starRingEnd_self_apply, hE x y (conj x) (conj y)]
  ring

/-- A repeated middle slot kills every realignment-antisymmetric four-form. -/
theorem repeated_fourForm_eq_zero (E : FourKernel) (hE : realign E = -E) (x y : ℂ) :
    E x y y x = 0 := by
  have h := congrFun (congrFun (congrFun (congrFun hE x) y) y) x
  change E x y y x = - E x y y x at h
  linear_combination (1 / 2 : ℂ) * h

/-- The repeated-node transport has a plus sign. -/
theorem repeated_node (D K B E T : FourKernel) (hE : realign E = -E)
    (hT : ∀ x y z w, T x y w z = - T x y z w) (x y : ℂ) :
    plusBlock D K E T x y y x =
      (D + K) x y y x + (mixedBlock B T - B) x x y y := by
  simp only [plusBlock, mixedBlock, realign, Pi.add_apply, Pi.sub_apply,
    repeated_fourForm_eq_zero E hE, hT x y x y]
  ring

/-- On conjugate node pairs, a realigned entry is a genuine Hermitian
diagonal of the original kernel. -/
theorem realigned_entry_eq_diagonal (F : FourKernel) (x z : ℂ) :
    realign F x (conj x) (conj z) z = hermitianDiagonal F x (conj z) := by
  simp [realign, hermitianDiagonal]

end
end ToeplitzSOS.Negative
