import ToeplitzSOS.Negative.CornerFrame
import ToeplitzSOS.Negative.CornerGram

/-!
# Multilinear polarization for the averaged corner

Four-slot forms are evaluated on arbitrary complex depth vectors. Their
additivity lets diagonal polynomial equalities recover all repair identities
without a classification of the Plücker relation space.
-/

namespace ToeplitzSOS.Negative
noncomputable section
open Finset

/-- A complex depth vector. -/
abbrev DepthVector (m : ℕ) := Fin m → ℂ

/-- A form in four complex depth vectors. -/
abbrev VectorFourForm (m : ℕ) := DepthVector m → DepthVector m → DepthVector m → DepthVector m → ℂ

/-- Additivity in each of the four slots. -/
structure FourAdditive {m : ℕ} (F : VectorFourForm m) : Prop where
  /-- Additivity in slot one. -/
  add1 : ∀ a b c d e, F (a + b) c d e = F a c d e + F b c d e
  /-- Additivity in slot two. -/
  add2 : ∀ a b c d e, F a (b + c) d e = F a b d e + F a c d e
  /-- Additivity in slot three. -/
  add3 : ∀ a b c d e, F a b (c + d) e = F a b c e + F a b d e
  /-- Additivity in slot four. -/
  add4 : ∀ a b c d e, F a b c (d + e) = F a b c d + F a b c e

/-- Four-additivity is preserved under linear combinations. -/
theorem FourAdditive.linearCombination {m : ℕ} {F G : VectorFourForm m}
    (hF : FourAdditive F) (hG : FourAdditive G) (a b : ℂ) :
    FourAdditive (fun u v w z => a * F u v w z + b * G u v w z) := by
  constructor <;> intros <;>
    simp only [hF.add1, hF.add2, hF.add3, hF.add4, hG.add1, hG.add2, hG.add3, hG.add4] <;> ring

/-- Polarization of a pair-symmetric four-additive form with vanishing
rank-one diagonal makes the second and fourth slots alternate. -/
theorem four_swap24_of_diagonal_zero {m : ℕ} (F : VectorFourForm m) (hF : FourAdditive F)
    (hs : ∀ a b c d, F a b c d = F c d a b)
    (hd : ∀ a b, F a b a b = 0) : ∀ a b c d, F a d c b = -F a b c d := by
  have hrep (a b d) : F a b a d = 0 := by
    have h := hd a (b + d)
    simp only [hF.add2, hF.add4, hd] at h
    rw [hs a d a b] at h
    linear_combination (1 / 2 : ℂ) * h
  intro a b c d
  have h := hrep (a + c) b d
  simp only [hF.add1, hF.add3, hrep] at h
  rw [hs c b a d] at h
  linear_combination h

/-- For a pure-wedge form, diagonal polarization also gives the realignment
antisymmetry: interchange slots two and three. -/
theorem four_swap23_of_diagonal_zero {m : ℕ} (F : VectorFourForm m) (hF : FourAdditive F)
    (hs : ∀ a b c d, F a b c d = F c d a b)
    (ha : ∀ a b c d, F a b d c = -F a b c d)
    (hd : ∀ a b, F a b a b = 0) : ∀ a b c d, F a c b d = -F a b c d := by
  have h24 := four_swap24_of_diagonal_zero F hF hs hd
  intro a b c d
  rw [h24 a d b c, ha a d c b, neg_neg, h24 a b c d]

/-- Wedge coordinates of two arbitrary complex depth vectors. -/
def vectorWedge {m : ℕ} (p : PureIndex m) (U V : DepthVector m) : ℂ :=
  U p.1.1 * V p.1.2 - U p.1.2 * V p.1.1

/-- A real pure coefficient row extended to complex depth vectors. -/
def pureForm {m : ℕ} (c : PureIndex m → ℝ) (U V : DepthVector m) : ℂ :=
  ∑ p, (c p : ℂ) * vectorWedge p U V

/-- A real mixed coefficient row extended to complex depth vectors. -/
def mixedForm {m : ℕ} (c : Fin m → Fin m → ℝ) (U V : DepthVector m) : ℂ :=
  ∑ p, ∑ q, (c p q : ℂ) * U p * V q

/-- Additivity of a pure form in its first vector. -/
theorem pureForm_add_left {m : ℕ} (c : PureIndex m → ℝ) (U V W : DepthVector m) :
    pureForm c (U + V) W = pureForm c U W + pureForm c V W := by
  unfold pureForm vectorWedge
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  simp only [Pi.add_apply]
  ring

/-- Additivity of a pure form in its second vector. -/
theorem pureForm_add_right {m : ℕ} (c : PureIndex m → ℝ) (U V W : DepthVector m) :
    pureForm c U (V + W) = pureForm c U V + pureForm c U W := by
  unfold pureForm vectorWedge
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  simp only [Pi.add_apply]
  ring

/-- Antisymmetry of every pure coefficient form. -/
theorem pureForm_swap {m : ℕ} (c : PureIndex m → ℝ) (U V : DepthVector m) :
    pureForm c V U = -pureForm c U V := by
  unfold pureForm vectorWedge
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro p _
  ring

/-- Additivity of a mixed form in its first vector. -/
theorem mixedForm_add_left {m : ℕ} (c : Fin m → Fin m → ℝ) (U V W : DepthVector m) :
    mixedForm c (U + V) W = mixedForm c U W + mixedForm c V W := by
  simp only [mixedForm, Pi.add_apply, mul_add, add_mul, sum_add_distrib]

/-- Additivity of a mixed form in its second vector. -/
theorem mixedForm_add_right {m : ℕ} (c : Fin m → Fin m → ℝ) (U V W : DepthVector m) :
    mixedForm c U (V + W) = mixedForm c U V + mixedForm c U W := by
  simp only [mixedForm, Pi.add_apply, mul_add, sum_add_distrib]

/-- Product sum of two arbitrary families of pure forms. -/
def pureFour {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) : VectorFourForm m :=
  fun U V W Z => ∑ j, pureForm (a j) U V * pureForm (b j) W Z

/-- Gram form of arbitrary mixed coefficient rows. -/
def mixedFour {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) : VectorFourForm m :=
  fun U V W Z => ∑ j, mixedForm (c j) U V * mixedForm (c j) W Z

/-- Pure product sums are additive in all four vector slots. -/
theorem pureFour_additive {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) :
    FourAdditive (pureFour a b) := by
  constructor <;> intros <;>
    simp only [pureFour, pureForm_add_left, pureForm_add_right, add_mul, mul_add, sum_add_distrib]

/-- Mixed Gram forms are additive in all four vector slots. -/
theorem mixedFour_additive {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) :
    FourAdditive (mixedFour c) := by
  constructor <;> intros <;>
    simp only [mixedFour, mixedForm_add_left, mixedForm_add_right, add_mul, mul_add, sum_add_distrib]

/-- Swapping the two pure pairs transposes the coefficient families. -/
theorem pureFour_pairs {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) (U V W Z : DepthVector m) :
    pureFour a b U V W Z = pureFour b a W Z U V := by
  unfold pureFour
  apply sum_congr rfl
  intro j _
  ring

/-- A mixed Gram form is symmetric in its two vector pairs. -/
theorem mixedFour_pairs {m r : ℕ} (c : Fin r → Fin m → Fin m → ℝ) (U V W Z : DepthVector m) :
    mixedFour c U V W Z = mixedFour c W Z U V := by
  unfold mixedFour
  apply sum_congr rfl
  intro j _
  ring

/-- Pure product sums alternate in the last wedge. -/
theorem pureFour_swap {m r : ℕ} (a b : Fin r → PureIndex m → ℝ) (U V W Z : DepthVector m) :
    pureFour a b U V Z W = -pureFour a b U V W Z := by
  simp only [pureFour, pureForm_swap (b _) W Z, mul_neg, sum_neg_distrib]

end
end ToeplitzSOS.Negative
