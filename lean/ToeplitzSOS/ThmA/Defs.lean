import ToeplitzSOS.Defs
import Mathlib

/-!
# Signed-index Toeplitz quartics and the residual form

Definitions of the wedge, weighted blocks, explicit quadratic squares,
and the residual form used by the fixed-order certificates.
-/

open Finset

noncomputable section

namespace ToeplitzSOS.ThmA

/-! ## 1. Generic objects (any commutative ring `R`, signed indices `ℤ`) -/

section Generic
variable {R : Type*} [CommRing R]

/-- Wedge `z_ab = x_a y_b − x_b y_a` on signed indices. -/
def wedge (x y : ℤ → R) (a b : ℤ) : R := x a * y b - x b * y a

/-- The Toeplitz matrix `(x_{i−j})_{i,j<n}`; the difference is taken in `ℤ`. -/
def tmat (n : ℕ) (x : ℤ → R) : Matrix (Fin n) (Fin n) R := fun i j => x ((i : ℤ) - (j : ℤ))

/-- `F_n` for generic Toeplitz data: the three terms of `Defs.toeplitzBW`, verbatim. -/
def bw (n : ℕ) (x y : ℤ → R) : R :=
  2 * ToeplitzSOS.frob (tmat n x) * ToeplitzSOS.frob (tmat n y)
    - 2 * ToeplitzSOS.inner (tmat n x) (tmat n y) ^ 2
    - ToeplitzSOS.frob (tmat n x * tmat n y - tmat n y * tmat n x)

/-- `τ(i) = min(i, n − i)`, the distance of `i` from `{0, n}` (window depth). -/
def tau (n i : ℤ) : ℤ := min i (n - i)

/-- Nodes `A` of the mixed σ-block: `A ∈ [1, n−1]` and `σ − A ∈ [1, n−1]`. -/
def blk (n σ : ℤ) : Finset ℤ := Icc (max 1 (σ - (n - 1))) (min (n - 1) (σ - 1))

/-- Laplacian weight between mixed nodes `(A, σ−A)` and `(A', σ−A')`. -/
def gcoef (n σ A A' : ℤ) : ℤ :=
  min (min (tau n A) (tau n (σ - A))) (min (tau n A') (tau n (σ - A')))

/-- Same-side window sums `S⁺_{δ,k} = ∑_{p=k+1}^{n−1−δ−k} z_{p,p+δ}`. -/
def Splus (n : ℕ) (x y : ℤ → R) (δ k : ℤ) : R :=
  ∑ p ∈ Icc (k + 1) ((n : ℤ) - 1 - δ - k), wedge x y p (p + δ)

def Sminus (n : ℕ) (x y : ℤ → R) (δ k : ℤ) : R :=
  ∑ p ∈ Icc (k + 1) ((n : ℤ) - 1 - δ - k), wedge x y (-(p + δ)) (-p)

/-- Central squares `2n ∑_{P} (n−P) (z_{0,P}² + z_{0,−P}²)`. -/
def central (n : ℕ) (x y : ℤ → R) : R :=
  ∑ P ∈ Icc (1 : ℤ) ((n : ℤ) - 1),
    ((2 * (n : ℤ) * ((n : ℤ) - P) : ℤ) : R) * (wedge x y 0 P ^ 2 + wedge x y 0 (-P) ^ 2)

/-- Mixed Laplacian squares, ordered pairs of nodes of each σ-block. -/
def lap (n : ℕ) (x y : ℤ → R) : R :=
  ∑ σ ∈ Icc (2 : ℤ) (2 * (n : ℤ) - 2), ∑ A ∈ blk n σ, ∑ A' ∈ blk n σ,
    ((gcoef n σ A A' : ℤ) : R) * (wedge x y (-A) (σ - A) - wedge x y (-A') (σ - A')) ^ 2

/-- Mixed diagonal slack `2n (n − A − B) z_{−A,B}²` for `A + B < n`. -/
def slack (n : ℕ) (x y : ℤ → R) : R :=
  ∑ A ∈ Icc (1 : ℤ) ((n : ℤ) - 1), ∑ B ∈ Icc (1 : ℤ) ((n : ℤ) - 1 - A),
    ((2 * (n : ℤ) * ((n : ℤ) - A - B) : ℤ) : R) * wedge x y (-A) B ^ 2

/-- Same-side coupling squares `2 ∑_{δ,k} (S⁺ + S⁻)²`. -/
def cross (n : ℕ) (x y : ℤ → R) : R :=
  2 * ∑ δ ∈ Icc (1 : ℤ) ((n : ℤ) - 2), ∑ k ∈ Ico (0 : ℤ) ((n : ℤ) - 1),
    (Splus n x y δ k + Sminus n x y δ k) ^ 2

/-- The explicit SOS part of the residual-form decomposition. -/
def explicitPart (n : ℕ) (x y : ℤ → R) : R :=
  central n x y + lap n x y + slack n x y + cross n x y

/-- Same-side diagonal `∑_{1≤i<j≤n−1} (n−i)(n−j) z_{ij}²` (used by the Gram form A′). -/
def ssdiag (n : ℕ) (x y : ℤ → R) : R :=
  ∑ i ∈ Icc (1 : ℤ) ((n : ℤ) - 1), ∑ j ∈ Ioc i ((n : ℤ) - 1),
    ((((n : ℤ) - i) * ((n : ℤ) - j) : ℤ) : R) * wedge x y i j ^ 2

def Hform (m : ℕ) (x y : ℤ → R) : R :=
  (∑ i ∈ Icc (1 : ℤ) m, ∑ j ∈ Ioc i (m : ℤ),
      ((((m : ℤ) + 1 - i) * ((m : ℤ) + 1 - j) : ℤ) : R) * wedge x y i j ^ 2)
    - ∑ δ ∈ Icc (1 : ℤ) ((m : ℤ) - 1), ∑ k ∈ Ico (0 : ℤ) m,
        (∑ p ∈ Icc (k + 1) ((m : ℤ) - δ - k), wedge x y p (p + δ)) ^ 2

end Generic

/-! ## 2. Bridge to `Defs.lean` (offset encoding `Fin (2n−1)`) and the polynomial statements -/

/-- Signed-index view of the `Defs` variables (`0` outside `(-n, n)`). -/
def sv (n : ℕ) (c : CoordFamily) (a : ℤ) : MvPolynomial (V n) ℝ :=
  if h : -(n : ℤ) < a ∧ a < n then MvPolynomial.X (c, ⟨(a + ((n : ℤ) - 1)).toNat, by omega⟩)
  else 0

/-- Variables of `H_m`: `x_1..x_m, y_1..y_m`, encoded `(c, i) ↦ c_{i+1}`. -/
abbrev HV (m : ℕ) := CoordFamily × Fin m

/-- Signed-index view of the variables of `H_m`: `hv m c i = c_i` for `1 ≤ i ≤ m`, else `0`. -/
def hv (m : ℕ) (c : CoordFamily) (i : ℤ) : MvPolynomial (HV m) ℝ :=
  if h : 1 ≤ i ∧ i ≤ m then MvPolynomial.X (c, ⟨(i - 1).toNat, by omega⟩) else 0

/-- `H_m` as a polynomial in its own `2m` variables (the object of statement (R_m)). -/
def Hpoly (m : ℕ) : MvPolynomial (HV m) ℝ := Hform m (hv m .x) (hv m .y)

/-- Positive-side embedding `x_i ↦ x_i` (`i = 1..n−1`). -/
def ιplus (n : ℕ) : HV (n - 1) → V n := fun v => (v.1, ⟨v.2.1 + n, by omega⟩)

/-- Negative-side embedding `x_i ↦ x_{−i}` (`i = 1..n−1`). -/
def ιminus (n : ℕ) : HV (n - 1) → V n := fun v => (v.1, ⟨n - 2 - v.2.1, by omega⟩)

end ToeplitzSOS.ThmA

end
