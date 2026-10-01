import Mathlib

/-!
# The finite corner language of the stabilized Toeplitz quartic

This file deliberately keeps the corner objects independent of the Toeplitz
polynomial.  The labels are the ordered corner labels
`N₁,…,N_w,P_w,…,P₁`; all coefficients are rational, so that later exact
certificate files can be transported to `ℝ` without an approximation step.

**Scope.**  Nothing in this file mentions `toeplitzBW` or a Gram matrix of
`F_n`; `finiteCornerBlock_eq_cornerBlock` is only the stabilisation of the
corner *formula* for `n ≥ 2w`.  That `finiteCornerBlock w n` is the corner of
the canonical Gram `Q0 = 2·diag(w_a w_b) - CᵀC` of `F_n` is proved in `Uniform/Bridge.lean` (`cornerGramBridge`, every
`n ≥ w + 1`).
-/

namespace ToeplitzSOS.Uniform

noncomputable section

/-- The quadratic form `xᵀ A x` of a square matrix. -/
def MatrixQuadratic {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (A : Matrix ι ι R) (x : ι → R) : R :=
  ∑ i, ∑ j, A i j * x i * x j

/-- The `2w` ordered corner labels `N₁, …, N_w, P_w, …, P₁`: label `a < w` is `N_{a+1}`
(negative side), label `a ≥ w` is `P_{2w−a}` (positive side). -/
abbrev Label (w : ℕ) := Fin (2 * w)

/-- A corner pair: two labels `fst < snd`, indexing the wedge `z_{fst,snd}`. -/
structure Pair (w : ℕ) where
  /-- The smaller label. -/
  fst : Label w
  /-- The larger label. -/
  snd : Label w
  /-- The labels are strictly increasing. -/
  le : fst < snd
deriving DecidableEq

/-- Corner pairs form a finite type (they inject into `Label w × Label w`). -/
instance (w : ℕ) : Fintype (Pair w) :=
  Fintype.ofInjective (fun p : Pair w ↦ (p.fst, p.snd)) (by
    intro p q h
    cases p
    cases q
    simp_all)

/-- The pair `(a, b)` from a proof of `a < b`. -/
def mkPair {w : ℕ} (a b : Label w) (h : a < b) : Pair w := ⟨a, b, h⟩

/-- The label is on the negative side (`N_1, …, N_w`, i.e. `a < w`). -/
def isNegative {w : ℕ} (a : Label w) : Prop := a.1 < w

/-- `isNegative` is decidable. -/
instance {w : ℕ} (a : Label w) : Decidable (isNegative a) := by
  unfold isNegative
  infer_instance

/-- The label is on the positive side (`P_w, …, P_1`, i.e. `a ≥ w`). -/
def isPositive {w : ℕ} (a : Label w) : Prop := w ≤ a.1

/-- `isPositive` is decidable. -/
instance {w : ℕ} (a : Label w) : Decidable (isPositive a) := by
  unfold isPositive
  infer_instance

/-- The weight of a label, i.e. its index: `N_r ↦ r`, `P_s ↦ s` (`a + 1` for `a < w`,
`2w − a` otherwise). -/
def weight {w : ℕ} (a : Label w) : ℕ :=
  if isNegative a then a.1 + 1 else 2 * w - a.1

/-- Both labels of the pair are on the same side. -/
def sameSide {w : ℕ} (p : Pair w) : Prop :=
  (isNegative p.fst ∧ isNegative p.snd) ∨ (isPositive p.fst ∧ isPositive p.snd)

/-- `sameSide` is decidable. -/
instance {w : ℕ} (p : Pair w) : Decidable (sameSide p) := by
  unfold sameSide
  infer_instance

/-- A mixed pair `(N_r, P_s)`: negative first label, positive second label. -/
def mixed {w : ℕ} (p : Pair w) : Prop :=
  isNegative p.fst ∧ isPositive p.snd

/-- `mixed` is decidable. -/
instance {w : ℕ} (p : Pair w) : Decidable (mixed p) := by
  unfold mixed
  infer_instance

/-- The displacement `d = r − s` of a pair with weights `r = weight fst`, `s = weight snd`. -/
def displacement {w : ℕ} (p : Pair w) : ℤ :=
  (weight p.fst : ℤ) - weight p.snd

/-- The height `h = min(r, s)` of a pair with weights `r`, `s`. -/
def height {w : ℕ} (p : Pair w) : ℕ := min (weight p.fst) (weight p.snd)

/-- The entries of the stabilised corner block `B_w`: on the diagonal
`2 r s` for same-side pairs and `2 r s − 2h` for mixed pairs; off the diagonal
`−2 min(h, h')` between mixed pairs of equal displacement; `0` otherwise. -/
def baseEntry {w : ℕ} (p q : Pair w) : ℚ :=
  if p = q then
    if sameSide p then 2 * (weight p.fst : ℚ) * weight p.snd
    else if mixed p then
      2 * (weight p.fst : ℚ) * weight p.snd - 2 * height p
    else 0
  else if mixed p ∧ mixed q ∧ displacement p = displacement q then
    -2 * (min (height p) (height q) : ℚ)
  else 0

/-- The stabilised corner matrix `B_w`. -/
def cornerBlock (w : ℕ) : Matrix (Pair w) (Pair w) ℚ := baseEntry

/-- The finite-`n` correction:
`2·1[d = d']·max(0, h + h' + |d| - n)` on mixed pairs of equal displacement
(truncated subtraction gives the `max(0, ·)`). It vanishes when `2 * w ≤ n`
by `finiteCorrection_eq_zero`. -/
def finiteCorrection {w n : ℕ} (p q : Pair w) : ℚ :=
  if mixed p ∧ mixed q ∧ displacement p = displacement q then
    2 * (Nat.sub (height p + height q +
      min (Int.natAbs (displacement p)) (Int.natAbs (displacement q))) n : ℚ)
  else 0

/-- The finite-`n` corner block: `baseEntry` plus `finiteCorrection`.
By `cornerGramBridge` (`Uniform/Bridge.lean`) it is the corner of the canonical wedge Gram
`gramQ0 n` of `F_n` for every `n ≥ w + 1`. -/
def finiteCornerBlock (w n : ℕ) : Matrix (Pair w) (Pair w) ℚ :=
  fun p q ↦ baseEntry p q + finiteCorrection (n := n) p q

/-- On a mixed pair, `h + |d| = max(r, s) ≤ w` and `h ≤ w`. -/
lemma height_add_natAbs_le {w : ℕ} {p : Pair w} (hp : mixed p) :
    height p ≤ w ∧ height p + Int.natAbs (displacement p) ≤ w := by
  obtain ⟨h1, h2⟩ := hp
  have hs := p.snd.2
  have hn2 : ¬ isNegative p.snd := by unfold isNegative; unfold isPositive at h2; omega
  have e1 : weight p.fst = p.fst.1 + 1 := by simp [weight, h1]
  have e2 : weight p.snd = 2 * w - p.snd.1 := by simp [weight, hn2]
  unfold isNegative at h1
  unfold isPositive at h2
  simp only [height, displacement, e1, e2]
  omega

/-- The finite-`n` correction vanishes for `n ≥ 2w`, because
`h + h' + min(|d|,|d'|) ≤ 2w` on mixed pairs. -/
lemma finiteCorrection_eq_zero {w n : ℕ} (hn : 2 * w ≤ n) (p q : Pair w) :
    finiteCorrection (w := w) (n := n) p q = 0 := by
  unfold finiteCorrection
  split_ifs with h
  · obtain ⟨hp, hq, -⟩ := h
    have a := height_add_natAbs_le hp
    have b := height_add_natAbs_le hq
    have : height p + height q +
        min (Int.natAbs (displacement p)) (Int.natAbs (displacement q)) - n = 0 := by
      omega
    simp [this]
  · rfl

/-- Stabilisation of the corner formula: for `n ≥ 2w` the finite-`n` corner
formula (2) equals the stabilised block `B_w` of (1).  This is a statement
about the two formulas only (not about the Gram of `F_n`). -/
theorem finiteCornerBlock_eq_cornerBlock {w n : ℕ} (hn : 2 * w ≤ n) :
    finiteCornerBlock w n = cornerBlock w := by
  ext p q
  simp [finiteCornerBlock, cornerBlock, finiteCorrection_eq_zero hn]

end
end ToeplitzSOS.Uniform
