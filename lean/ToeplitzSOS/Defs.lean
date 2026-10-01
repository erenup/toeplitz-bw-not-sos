import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

namespace ToeplitzSOS

noncomputable section

/-- The two independent families of Toeplitz coordinates. -/
inductive CoordFamily
  | x
  | y
  deriving DecidableEq

/-- The two letters form a finite type (used for sums over all variables). -/
instance : Fintype CoordFamily :=
  ⟨{CoordFamily.x, CoordFamily.y}, fun c => by cases c <;> simp⟩

/--
The `4n - 2` variables at order `n`.

The second component uses the offset encoding
`0, ..., 2n-2 ↔ -(n-1), ..., n-1`; the first component selects `x` or `y`.
-/
abbrev V (n : ℕ) := CoordFamily × Fin (2 * n - 1)

/-- The offset encoding of the signed diagonal index `i - j`. -/
def diagIndex {n : ℕ} (i j : Fin n) : Fin (2 * n - 1) :=
  ⟨i.1 + (n - 1 - j.1), by omega⟩

/-- The indeterminate `x_a`, where `a` is offset-encoded. -/
def x {n : ℕ} (a : Fin (2 * n - 1)) : MvPolynomial (V n) ℝ :=
  MvPolynomial.X (.x, a)

/-- The indeterminate `y_a`, where `a` is offset-encoded. -/
def y {n : ℕ} (a : Fin (2 * n - 1)) : MvPolynomial (V n) ℝ :=
  MvPolynomial.X (.y, a)

/-- The generic `n × n` Toeplitz matrix with entries `x_(i-j)`. -/
def X (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (V n) ℝ) :=
  fun i j ↦ x (diagIndex i j)

/-- The generic `n × n` Toeplitz matrix with entries `y_(i-j)`. -/
def Y (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (V n) ℝ) :=
  fun i j ↦ y (diagIndex i j)

/-- The square of the Frobenius norm, algebraically over any commutative semiring. -/
def frob {R : Type*} [CommSemiring R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i, ∑ j, A i j ^ 2

/-- The entrywise inner product, algebraically over any commutative semiring.
(Not Mathlib's `inner`; write `ToeplitzSOS.inner` outside this namespace.) -/
def inner {R : Type*} [CommSemiring R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i, ∑ j, A i j * B i j

def toeplitzBW (n : ℕ) : MvPolynomial (V n) ℝ :=
  2 * frob (X n) * frob (Y n) - 2 * inner (X n) (Y n) ^ 2 -
    frob (X n * Y n - Y n * X n)

def IsSumSqHomQuad {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∃ (N : ℕ) (q : Fin N → MvPolynomial σ ℝ),
    (∀ j, (q j).IsHomogeneous 2) ∧ p = ∑ j, q j ^ 2

def MI15 : Prop :=
  ∀ n ≥ 2, IsSumSqHomQuad (toeplitzBW n)

/-- The basic Plücker/wedge quadratic `x_a y_b - x_b y_a`. -/
def z {n : ℕ} (a b : Fin (2 * n - 1)) : MvPolynomial (V n) ℝ :=
  x a * y b - x b * y a

private lemma x_isHomogeneous {n : ℕ} (a : Fin (2 * n - 1)) :
    (x a).IsHomogeneous 1 := by
  exact MvPolynomial.isHomogeneous_X _ _

private lemma y_isHomogeneous {n : ℕ} (a : Fin (2 * n - 1)) :
    (y a).IsHomogeneous 1 := by
  exact MvPolynomial.isHomogeneous_X _ _

private lemma frob_isHomogeneous {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial (V n) ℝ))
    (hA : ∀ i j, (A i j).IsHomogeneous d) :
    (frob A).IsHomogeneous (d * 2) := by
  classical
  unfold frob
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (hA i j).pow 2

private lemma inner_isHomogeneous {n d e : ℕ}
    (A B : Matrix (Fin n) (Fin n) (MvPolynomial (V n) ℝ))
    (hA : ∀ i j, (A i j).IsHomogeneous d)
    (hB : ∀ i j, (B i j).IsHomogeneous e) :
    (inner A B).IsHomogeneous (d + e) := by
  classical
  unfold inner
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (hA i j).mul (hB i j)

private lemma matrix_mul_isHomogeneous {n d e : ℕ}
    (A B : Matrix (Fin n) (Fin n) (MvPolynomial (V n) ℝ))
    (hA : ∀ i j, (A i j).IsHomogeneous d)
    (hB : ∀ i j, (B i j).IsHomogeneous e) :
    ∀ i j, ((A * B) i j).IsHomogeneous (d + e) := by
  classical
  intro i j
  rw [Matrix.mul_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact (hA i k).mul (hB k j)

/-- Smoke test: the catalogue polynomial is homogeneous of degree four. -/
theorem toeplitzBW_isHomogeneous (n : ℕ) :
    (toeplitzBW n).IsHomogeneous 4 := by
  let hX : ∀ i j, ((X n) i j).IsHomogeneous 1 := fun i j ↦ x_isHomogeneous _
  let hY : ∀ i j, ((Y n) i j).IsHomogeneous 1 := fun i j ↦ y_isHomogeneous _
  have hfX : (frob (X n)).IsHomogeneous 2 := by
    simpa using frob_isHomogeneous (X n) hX
  have hfY : (frob (Y n)).IsHomogeneous 2 := by
    simpa using frob_isHomogeneous (Y n) hY
  have hi : (inner (X n) (Y n)).IsHomogeneous 2 :=
    inner_isHomogeneous (X n) (Y n) hX hY
  have hXY := matrix_mul_isHomogeneous (X n) (Y n) hX hY
  have hYX := matrix_mul_isHomogeneous (Y n) (X n) hY hX
  have hc : ∀ i j, ((X n * Y n - Y n * X n) i j).IsHomogeneous 2 := by
    intro i j
    exact (hXY i j).sub (hYX i j)
  have hcomm : (frob (X n * Y n - Y n * X n)).IsHomogeneous 4 := by
    simpa using frob_isHomogeneous (X n * Y n - Y n * X n) hc
  unfold toeplitzBW
  have hfirst : (2 * frob (X n) * frob (Y n)).IsHomogeneous 4 := by
    simpa only [two_mul, add_mul] using (hfX.mul hfY).add (hfX.mul hfY)
  have hsecond : (2 * inner (X n) (Y n) ^ 2).IsHomogeneous 4 := by
    simpa only [two_mul] using (hi.pow 2).add (hi.pow 2)
  exact hfirst.sub hsecond |>.sub hcomm

theorem toeplitzBW_two_isSumSq : IsSumSqHomQuad (toeplitzBW 2) := by
  let q : Fin 2 → MvPolynomial (V 2) ℝ := ![
    2 * z (n := 2) ⟨0, by decide⟩ ⟨1, by decide⟩,
    2 * z (n := 2) ⟨1, by decide⟩ ⟨2, by decide⟩]
  refine ⟨2, q, ?_, ?_⟩
  · intro j
    fin_cases j
    · change (2 * z (n := 2) (0 : Fin 3) (1 : Fin 3)).IsHomogeneous 2
      rw [two_mul]
      let hz := (x_isHomogeneous (n := 2) ⟨0, by decide⟩).mul
        (y_isHomogeneous ⟨1, by decide⟩) |>.sub
          ((x_isHomogeneous ⟨1, by decide⟩).mul (y_isHomogeneous ⟨0, by decide⟩))
      exact hz.add hz
    · change (2 * z (n := 2) (1 : Fin 3) (2 : Fin 3)).IsHomogeneous 2
      rw [two_mul]
      let hz := (x_isHomogeneous (n := 2) ⟨1, by decide⟩).mul
        (y_isHomogeneous ⟨2, by decide⟩) |>.sub
          ((x_isHomogeneous ⟨2, by decide⟩).mul (y_isHomogeneous ⟨1, by decide⟩))
      exact hz.add hz
  · simp [q, toeplitzBW, frob, inner, Matrix.mul_apply, X, Y, diagIndex, z, x, y]
    ring

end

end ToeplitzSOS
