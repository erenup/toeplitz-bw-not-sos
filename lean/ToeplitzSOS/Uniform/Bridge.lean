import ToeplitzSOS.Uniform.Corner
import ToeplitzSOS.Kernel.Basic
import ToeplitzSOS.ThmA.Reindex

/-!
# Bridge: the corner language and the canonical wedge Gram of `F_n`

This file connects the corner language of `Uniform/Corner.lean` (which does not mention
`toeplitzBW`) to the polynomial `F_n = toeplitzBW n`.

1. *The canonical wedge Gram.*  `commCoeff n` is the matrix `C` of the commutator in the
   wedge basis, `(XY - YX)_{ij} = ∑_p C[(i,j),p] z_p` (`comm_entry`), and
   `gramQ0 n = 2·diag(w_a w_b) - CᵀC` with `w_a = n - |a|` (`offsetWeight`).
   `gramQ0_isWedgeGram : IsWedgeGram n (gramQ0 n)` for every `n`, i.e.
   `toeplitzBW n = ∑_{p,q} gramQ0 n p q · z_p z_q`.
2. *The corner embedding.*  For `w + 1 ≤ n`, `cornerEmb w n h` sends the label `a < w`
   (`N_{a+1}`) to the offset `a` and the label `a ≥ w` (`P_{2w-a}`) to the offset
   `a + 2(n-w) - 1`; it is strictly monotone (`cornerEmb_strictMono`), lifts to the
   injective `pairEmb h : Pair w → W n`, and preserves weights (`offsetWeight_cornerEmb`).
3. *The bridge.*  `cornerGramBridge : CornerGramBridge`: for all `w, n` with `w + 1 ≤ n`
   and all corner pairs `p, q`,
   `gramQ0 n (pairEmb h p) (pairEmb h q) = finiteCornerBlock w n p q`
   (unguarded finite correction, every `n ≥ w + 1`).  Matrix form:
   `gramQ0_submatrix_pairEmb`.  Stabilised form (`n ≥ 2w`): `gramQ0_pairEmb_stable`,
   the corner is `cornerBlock w`.

Route: the column closed form `commCoeff_eq_col`
(`C[(i,j),(A,B)] = [i-j = A+B]([0 ≤ i-A < n] - [0 ≤ i-B < n])` in signed indices);
same-sign columns vanish (`col_eq_zero_of_sameSign`); the Gram of two mixed columns is
a sum of four interval counts (`colSum_mixed`), giving `commGram_pairEmb`.

Scope: this identifies a principal submatrix of the one Gram matrix `gramQ0 n`; it says
nothing about the other Gram matrices of `F_n` (which differ from `gramQ0 n` by kernel
directions) and nothing about positive semidefiniteness.
-/

namespace ToeplitzSOS.Uniform

open Finset ToeplitzSOS.Kernel

noncomputable section

/-! ## 1. The canonical wedge Gram `Q0` of `F_n` -/

/-- The signed Toeplitz index `a - (n - 1)` of an offset-encoded diagonal `a`. -/
def signedIdx {n : ℕ} (a : Fin (2 * n - 1)) : ℤ := (a : ℤ) - ((n : ℤ) - 1)

/-- The weight `w_a = n - |a|` (signed `a`), the length of the Toeplitz diagonal `a`. -/
def offsetWeight (n : ℕ) (a : Fin (2 * n - 1)) : ℤ := n - |signedIdx a|

/-- Coefficient of the wedge `p` in `z_ab = x_a y_b - x_b y_a` (arbitrary offsets `a, b`):
`[p = (a,b)] - [p = (b,a)]`. -/
def wedgeCoeff {n : ℕ} (a b : Fin (2 * n - 1)) (p : W n) : ℤ :=
  (if p.1 = (a, b) then 1 else 0) - (if p.1 = (b, a) then 1 else 0)

/-- The matrix `C` of the commutator in wedges:
`C[(i,j),(a,b)] = #{k : (i-k, k-j) = (a,b)} - #{k : (i-k, k-j) = (b,a)}`. -/
def commCoeff (n : ℕ) (ij : Fin n × Fin n) (p : W n) : ℤ :=
  ∑ k : Fin n, wedgeCoeff (diagIndex ij.1 k) (diagIndex k ij.2) p

/-- The canonical wedge Gram `Q0 = 2·diag(w_a w_b) - CᵀC` of `F_n`. -/
def gramQ0 (n : ℕ) : Matrix (W n) (W n) ℝ := fun p q ↦
  (if p = q then 2 * (offsetWeight n p.1.1 : ℝ) * offsetWeight n p.1.2 else 0) -
    ∑ ij : Fin n × Fin n, (commCoeff n ij p : ℝ) * commCoeff n ij q

/-- `z_ab` expanded in the wedge basis. -/
theorem z_eq_sum {n : ℕ} (a b : Fin (2 * n - 1)) :
    z a b = ∑ p : W n, MvPolynomial.C ((wedgeCoeff a b p : ℤ) : ℝ) * wedge p := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [Finset.sum_eq_single (⟨(a, b), h⟩ : W n)]
    · have hne : (a, b) ≠ (b, a) := by
        intro e
        simp only [Prod.mk.injEq] at e
        exact absurd e.1 (ne_of_lt h)
      simp [wedgeCoeff, wedge, hne]
    · intro p _ hp
      have h1 : p.1 ≠ (a, b) := fun e ↦ hp (Subtype.ext e)
      have h2 : p.1 ≠ (b, a) := by
        intro e
        have := p.2
        rw [e] at this
        exact absurd (lt_trans h this) (lt_irrefl _)
      simp [wedgeCoeff, h1, h2]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · simp [wedgeCoeff, z]
  · rw [Finset.sum_eq_single (⟨(b, a), h⟩ : W n)]
    · have hne : (b, a) ≠ (a, b) := by
        intro e
        simp only [Prod.mk.injEq] at e
        exact absurd e.1 (ne_of_lt h)
      simp only [wedgeCoeff, wedge, hne]
      simp [z]
    · intro p _ hp
      have h1 : p.1 ≠ (b, a) := fun e ↦ hp (Subtype.ext e)
      have h2 : p.1 ≠ (a, b) := by
        intro e
        have := p.2
        rw [e] at this
        exact absurd (lt_trans h this) (lt_irrefl _)
      simp [wedgeCoeff, h1, h2]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

/-- The commutator entry `(XY - YX)_{ij} = ∑_p C[(i,j),p] z_p`. -/
theorem comm_entry (n : ℕ) (ij : Fin n × Fin n) :
    (X n * Y n - Y n * X n) ij.1 ij.2 =
      ∑ p : W n, MvPolynomial.C ((commCoeff n ij p : ℤ) : ℝ) * wedge p := by
  have h1 : (X n * Y n - Y n * X n) ij.1 ij.2 =
      ∑ k : Fin n, z (diagIndex ij.1 k) (diagIndex k ij.2) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, X, Y, z]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [h1]
  simp_rw [z_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Finset.sum_mul]
  simp [commCoeff, map_sum]

/-- `‖XY - YX‖² = ∑_{p,q} (CᵀC)_{pq} z_p z_q`. -/
theorem frob_comm (n : ℕ) :
    frob (X n * Y n - Y n * X n) =
      ∑ p : W n, ∑ q : W n, MvPolynomial.C (∑ ij : Fin n × Fin n,
        (commCoeff n ij p : ℝ) * commCoeff n ij q) * wedge p * wedge q := by
  calc frob (X n * Y n - Y n * X n)
      = ∑ ij : Fin n × Fin n, ∑ p : W n, ∑ q : W n,
          MvPolynomial.C ((commCoeff n ij p : ℝ) * commCoeff n ij q) * wedge p * wedge q := by
        unfold frob
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun ij _ ↦ ?_
        rw [comm_entry, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        rw [map_mul]
        ring
    _ = ∑ p : W n, ∑ ij : Fin n × Fin n, ∑ q : W n,
          MvPolynomial.C ((commCoeff n ij p : ℝ) * commCoeff n ij q) * wedge p * wedge q :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [map_sum, Finset.sum_mul, Finset.sum_mul]

/-- Diagonal count: `#{(i,j) : i - j = a} = n - |a|`. -/
theorem card_diagIndex (n : ℕ) (a : Fin (2 * n - 1)) :
    (∑ i : Fin n, ∑ j : Fin n, if diagIndex i j = a then (1 : ℤ) else 0) =
      offsetWeight n a := by
  have key : ∀ i j : Fin n, (diagIndex i j = a) ↔ ((i : ℤ) - j = signedIdx a) := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Fin.ext_iff]
    simp only [diagIndex, signedIdx]
    omega
  simp only [key]
  have h : (∑ i : Fin n, ∑ j : Fin n, if (i : ℤ) - j = signedIdx a then (1 : ℤ) else 0) =
      ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (0 : ℤ) n, if i - j = signedIdx a then (1 : ℤ) else 0 :=
    ThmA.sum_fin_fin_eq_sum_Ico n (fun i j ↦ if i - j = signedIdx a then (1 : ℤ) else 0)
  have h2 := ThmA.square_diag_sum (R := ℤ) (n : ℤ)
    (fun d : ℤ ↦ if d = signedIdx a then (1 : ℤ) else 0)
  rw [h, h2]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_Ioo, Int.cast_id]
  have ha := a.isLt
  have hmem : -(n : ℤ) < signedIdx a ∧ signedIdx a < n := by
    simp only [signedIdx]
    omega
  rw [ite_eq_left hmem]
  rfl

/-- Weighted diagonal sums: `∑_{i,j} g(i - j) = ∑_a w_a g(a)`. -/
theorem sum_diagIndex {R : Type*} [CommRing R] (n : ℕ) (g : Fin (2 * n - 1) → R) :
    ∑ i : Fin n, ∑ j : Fin n, g (diagIndex i j) = ∑ a, (offsetWeight n a : R) * g a := by
  calc ∑ i : Fin n, ∑ j : Fin n, g (diagIndex i j)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ a, if diagIndex i j = a then g a else 0 := by
        simp
    _ = ∑ i : Fin n, ∑ a, ∑ j : Fin n, if diagIndex i j = a then g a else 0 := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ i : Fin n, ∑ j : Fin n, if diagIndex i j = a then g a else 0 :=
        Finset.sum_comm
    _ = ∑ a, (offsetWeight n a : R) * g a := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← card_diagIndex n a]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp

/-- Sums over wedges as filtered double sums. -/
theorem sum_W {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Fin (2 * n - 1) → Fin (2 * n - 1) → M) :
    ∑ p : W n, f p.1.1 p.1.2 = ∑ a, ∑ b, if a < b then f a b else 0 := by
  rw [← Finset.sum_subtype (univ.filter fun ab : Fin (2 * n - 1) × Fin (2 * n - 1) ↦ ab.1 < ab.2)
    (by simp) (fun ab ↦ f ab.1 ab.2), Finset.sum_filter, Fintype.sum_prod_type]

/-- A symmetric double sum with zero diagonal is twice the sum over wedges. -/
theorem sum_sum_symm {R : Type*} [CommRing R] (n : ℕ)
    (f : Fin (2 * n - 1) → Fin (2 * n - 1) → R)
    (hsymm : ∀ a b, f a b = f b a) (hdiag : ∀ a, f a a = 0) :
    ∑ a, ∑ b, f a b = 2 * ∑ p : W n, f p.1.1 p.1.2 := by
  have hsplit : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f b a else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hdiag]
    · simp [h, not_lt_of_gt h, hsymm a b]
  have hswap : ∑ a, ∑ b, (if b < a then f b a else 0) =
      ∑ a, ∑ b, (if a < b then f a b else 0) := Finset.sum_comm
  rw [sum_W]
  calc ∑ a, ∑ b, f a b
      = ∑ a, ∑ b, ((if a < b then f a b else 0) + (if b < a then f b a else 0)) := by
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hsplit a b
    _ = _ := by
        simp only [Finset.sum_add_distrib, hswap]
        ring

/-- The weighted Lagrange identity in wedges. -/
theorem lagrange_weighted (n : ℕ) (c : Fin (2 * n - 1) → ℝ) :
    2 * (∑ a, MvPolynomial.C (c a) * x a ^ 2) * (∑ a, MvPolynomial.C (c a) * y a ^ 2)
      - 2 * (∑ a, MvPolynomial.C (c a) * (x a * y a)) ^ 2
      = ∑ p : W n, MvPolynomial.C (2 * c p.1.1 * c p.1.2) * wedge p * wedge p := by
  have hfull : 2 * (∑ a, MvPolynomial.C (c a) * x a ^ 2) *
        (∑ a, MvPolynomial.C (c a) * y a ^ 2)
      - 2 * (∑ a, MvPolynomial.C (c a) * (x a * y a)) ^ 2
      = ∑ a, ∑ b, MvPolynomial.C (c a) * MvPolynomial.C (c b) * z a b ^ 2 := by
    have e1 : ∑ a, ∑ b, MvPolynomial.C (c a) * MvPolynomial.C (c b) * z a b ^ 2 =
        ∑ a, ∑ b, (MvPolynomial.C (c a) * x a ^ 2) * (MvPolynomial.C (c b) * y b ^ 2)
        + ∑ a, ∑ b, (MvPolynomial.C (c b) * x b ^ 2) * (MvPolynomial.C (c a) * y a ^ 2)
        - 2 * ∑ a, ∑ b, (MvPolynomial.C (c a) * (x a * y a)) *
            (MvPolynomial.C (c b) * (x b * y b)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      simp only [z]
      ring
    have e2 : ∑ a, ∑ b, (MvPolynomial.C (c b) * x b ^ 2) * (MvPolynomial.C (c a) * y a ^ 2) =
        ∑ a, ∑ b, (MvPolynomial.C (c a) * x a ^ 2) * (MvPolynomial.C (c b) * y b ^ 2) :=
      Finset.sum_comm
    rw [e1, e2, sq (∑ a, MvPolynomial.C (c a) * (x a * y a)), Finset.sum_mul_sum,
      mul_assoc 2, Finset.sum_mul_sum]
    ring
  rw [hfull, sum_sum_symm n (fun a b ↦ MvPolynomial.C (c a) * MvPolynomial.C (c b) * z a b ^ 2)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [wedge, map_mul, map_ofNat]
    ring
  · intro a b
    simp only [z]
    ring
  · intro a
    simp [z]

/-- `Q0 = 2·diag(w_a w_b) − CᵀC` is a wedge Gram matrix of `F_n`, for every
`n`: `toeplitzBW n = ∑_{p,q} Q0[p,q] z_p z_q`. -/
theorem gramQ0_isWedgeGram (n : ℕ) : IsWedgeGram n (gramQ0 n) := by
  unfold IsWedgeGram
  have hX : frob (X n) = ∑ a, MvPolynomial.C (offsetWeight n a : ℝ) * x a ^ 2 := by
    unfold frob
    have h := sum_diagIndex n (fun a ↦ x a ^ 2)
    simp only [X]
    rw [h]
    simp [map_intCast]
  have hY : frob (Y n) = ∑ a, MvPolynomial.C (offsetWeight n a : ℝ) * y a ^ 2 := by
    unfold frob
    have h := sum_diagIndex n (fun a ↦ y a ^ 2)
    simp only [Y]
    rw [h]
    simp [map_intCast]
  have hI : inner (X n) (Y n) =
      ∑ a, MvPolynomial.C (offsetWeight n a : ℝ) * (x a * y a) := by
    unfold inner
    have h := sum_diagIndex n (fun a ↦ x a * y a)
    simp only [X, Y]
    rw [h]
    simp [map_intCast]
  calc toeplitzBW n
      = (2 * frob (X n) * frob (Y n) - 2 * inner (X n) (Y n) ^ 2) -
          frob (X n * Y n - Y n * X n) := rfl
    _ = ∑ p : W n, MvPolynomial.C (2 * (offsetWeight n p.1.1 : ℝ) * offsetWeight n p.1.2) *
            wedge p * wedge p -
          ∑ p : W n, ∑ q : W n, MvPolynomial.C (∑ ij : Fin n × Fin n,
            (commCoeff n ij p : ℝ) * commCoeff n ij q) * wedge p * wedge q := by
        rw [hX, hY, hI, lagrange_weighted, frob_comm]
    _ = _ := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        simp only [gramQ0, map_sub, sub_mul, Finset.sum_sub_distrib]
        congr 1
        simp [apply_ite MvPolynomial.C, ite_mul, Finset.sum_ite_eq]

/-! ## 2. Closed form of the commutator columns -/

/-- The column of `C` at the signed wedge `(A, B)`, with integer row indices `(i, j)`:
`[i - j = A + B]·([0 ≤ i - A < n] - [0 ≤ i - B < n])`.
Protected (avoids a clash with `Matrix.col` under `open Matrix`): write
`Uniform.col`. -/
protected def col (n : ℕ) (A B i j : ℤ) : ℤ :=
  if i - j = A + B then
    (if 0 ≤ i - A ∧ i - A < n then 1 else 0) - (if 0 ≤ i - B ∧ i - B < n then 1 else 0)
  else 0

/-- A single admissible summation index. -/
theorem sum_fin_indicator (n : ℕ) (c : ℤ) (Q : Prop) [Decidable Q] :
    (∑ k : Fin n, if (k : ℤ) = c ∧ Q then (1 : ℤ) else 0) =
      if Q ∧ 0 ≤ c ∧ c < n then 1 else 0 := by
  have h : (∑ k : Fin n, if (k : ℤ) = c ∧ Q then (1 : ℤ) else 0) =
      ∑ k ∈ Ico (0 : ℤ) n, if k = c ∧ Q then (1 : ℤ) else 0 :=
    ThmA.sum_fin_eq_sum_Ico n (fun k ↦ if k = c ∧ Q then (1 : ℤ) else 0)
  rw [h]
  simp only [ite_and]
  rw [Finset.sum_ite_eq']
  simp only [mem_Ico]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Column closed form of the commutator coefficients in signed indices. -/
theorem commCoeff_eq_col (n : ℕ) (ij : Fin n × Fin n) (p : W n) :
    commCoeff n ij p = Uniform.col n (signedIdx p.1.1) (signedIdx p.1.2) ij.1 ij.2 := by
  have e1 : ∀ k : Fin n, p.1 = (diagIndex ij.1 k, diagIndex k ij.2) ↔
      ((k : ℤ) = ij.1 - signedIdx p.1.1 ∧
        (ij.1 : ℤ) - ij.2 = signedIdx p.1.1 + signedIdx p.1.2) := by
    intro k
    rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
    simp only [diagIndex, signedIdx]
    omega
  have e2 : ∀ k : Fin n, p.1 = (diagIndex k ij.2, diagIndex ij.1 k) ↔
      ((k : ℤ) = ij.1 - signedIdx p.1.2 ∧
        (ij.1 : ℤ) - ij.2 = signedIdx p.1.1 + signedIdx p.1.2) := by
    intro k
    rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
    simp only [diagIndex, signedIdx]
    omega
  unfold commCoeff wedgeCoeff Uniform.col
  rw [Finset.sum_sub_distrib]
  simp only [e1, e2, sum_fin_indicator]
  split_ifs <;> omega

/-- The integer Gram `CᵀC` of the commutator part. -/
def commGram (n : ℕ) (p q : W n) : ℤ :=
  ∑ ij : Fin n × Fin n, commCoeff n ij p * commCoeff n ij q

/-- `CᵀC` as a double sum of column products over integer row indices. -/
theorem commGram_eq (n : ℕ) (p q : W n) :
    commGram n p q = ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (0 : ℤ) n,
      Uniform.col n (signedIdx p.1.1) (signedIdx p.1.2) i j *
        Uniform.col n (signedIdx q.1.1) (signedIdx q.1.2) i j := by
  unfold commGram
  simp only [commCoeff_eq_col]
  rw [Fintype.sum_prod_type]
  exact ThmA.sum_fin_fin_eq_sum_Ico n (fun i j ↦
    Uniform.col n (signedIdx p.1.1) (signedIdx p.1.2) i j *
      Uniform.col n (signedIdx q.1.1) (signedIdx q.1.2) i j)

/-- Wedges with both indices of the same sign have zero commutator column. -/
theorem col_eq_zero_of_sameSign (n : ℕ) (A B i j : ℤ)
    (hs : (A ≤ 0 ∧ B ≤ 0) ∨ (0 ≤ A ∧ 0 ≤ B))
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) : Uniform.col n A B i j = 0 := by
  unfold Uniform.col
  split_ifs <;> omega

/-- Counting the integers of `[0, n)` in an interval `[L, U)`. -/
theorem sum_ind_Ico (n : ℤ) (P : ℤ → Prop) [DecidablePred P] (L U : ℤ)
    (hL : 0 ≤ L) (hU : U ≤ n)
    (hP : ∀ i, 0 ≤ i → i < n → (P i ↔ L ≤ i ∧ i < U)) :
    ∑ i ∈ Ico (0 : ℤ) n, (if P i then (1 : ℤ) else 0) = max 0 (U - L) := by
  rw [Finset.sum_boole]
  have hset : (Ico (0 : ℤ) n).filter P = Ico L U := by
    ext i
    simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h0, hn⟩, hp⟩
      exact (hP i h0 hn).1 hp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, (hP i (by omega) (by omega)).2 ⟨h1, h2⟩⟩
  rw [hset, Int.card_Ico, Int.toNat_eq_max]
  omega

/-- Summing out `j` against the diagonal constraint `i - j = σ`. -/
theorem sum_diag_j (n : ℕ) (σ i c : ℤ) :
    ∑ j ∈ Ico (0 : ℤ) n, (if i - j = σ then c else 0) =
      if 0 ≤ i - σ ∧ i - σ < n then c else 0 := by
  have e : ∀ j : ℤ, (i - j = σ) ↔ (j = i - σ) := fun j ↦ by omega
  simp only [e]
  rw [Finset.sum_ite_eq']
  simp only [mem_Ico]

/-- Expanding `[G]·([a] - [b])·([c] - [d])` into four indicators. -/
theorem ind_expand (G a b c d : Prop) [Decidable G] [Decidable a] [Decidable b]
    [Decidable c] [Decidable d] :
    (if G then ((if a then (1 : ℤ) else 0) - (if b then 1 else 0)) *
        ((if c then 1 else 0) - (if d then 1 else 0)) else 0) =
      (if G ∧ a ∧ c then 1 else 0) - (if G ∧ a ∧ d then 1 else 0) -
        (if G ∧ b ∧ c then 1 else 0) + (if G ∧ b ∧ d then 1 else 0) := by
  by_cases hG : G <;> by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;>
    by_cases hd : d <;> simp [*]

/-- Mixed-wedge Gram entry: for `(A, B) = (-n + r, n - s)` and `(A', B') = (-n + r', n - s')`,
`(CᵀC) = [r - s = r' - s']·(2 min(h, h') - 2 max(0, r + s' - n))`, `h = min(r, s)`. -/
theorem colSum_mixed (n : ℕ) (r s r' s' : ℤ) (hr : 1 ≤ r) (hrn : r ≤ n) (hs : 1 ≤ s)
    (hsn : s ≤ n) (hr' : 1 ≤ r') (hrn' : r' ≤ n) (hs' : 1 ≤ s') (hsn' : s' ≤ n) :
    ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (0 : ℤ) n,
        Uniform.col n (-n + r) (n - s) i j * Uniform.col n (-n + r') (n - s') i j =
      if r - s = r' - s' then 2 * min (min r s) (min r' s') - 2 * max 0 (r + s' - n)
      else 0 := by
  by_cases hσ : r - s = r' - s'
  · rw [ite_eq_left hσ]
    have e1 : -(n : ℤ) + r + (n - s) = r - s := by ring
    have e2 : -(n : ℤ) + r' + (n - s') = r - s := by rw [hσ]; ring
    have hj : ∀ i j : ℤ,
        Uniform.col n (-n + r) (n - s) i j * Uniform.col n (-n + r') (n - s') i j =
        if i - j = r - s then
          ((if 0 ≤ i - (-n + r) ∧ i - (-n + r) < n then (1 : ℤ) else 0) -
            (if 0 ≤ i - (n - s) ∧ i - (n - s) < n then 1 else 0)) *
          ((if 0 ≤ i - (-n + r') ∧ i - (-n + r') < n then (1 : ℤ) else 0) -
            (if 0 ≤ i - (n - s') ∧ i - (n - s') < n then 1 else 0))
        else 0 := by
      intro i j
      unfold Uniform.col
      rw [e1, e2]
      split_ifs <;> simp
    simp only [hj]
    simp only [sum_diag_j]
    simp only [ind_expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_ind_Ico n _ (max 0 (r - s)) (min r r') (by omega) (by omega) (fun i _ _ ↦ by omega),
      sum_ind_Ico n _ (n - s') r (by omega) (by omega) (fun i _ _ ↦ by omega),
      sum_ind_Ico n _ (n - s) r' (by omega) (by omega) (fun i _ _ ↦ by omega),
      sum_ind_Ico n _ (n - min s s') (n + min 0 (r - s)) (by omega) (by omega)
        (fun i _ _ ↦ by omega)]
    omega
  · rw [ite_eq_right hσ]
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
    unfold Uniform.col
    split_ifs <;> omega

/-! ## 3. The corner embedding -/

/-- The corner embedding `Label w → Fin (2n-1)`: the label `a < w` (`N_{a+1}`) goes to the
offset `a` (signed index `-(n - (a+1))`), the label `a ≥ w` (`P_{2w-a}`) to the offset
`a + 2(n-w) - 1` (signed index `n - (2w-a)`). -/
def cornerEmb (w n : ℕ) (h : w + 1 ≤ n) (a : Label w) : Fin (2 * n - 1) :=
  ⟨if a.1 < w then a.1 else a.1 + 2 * (n - w) - 1, by
    have := a.2
    split_ifs <;> omega⟩

/-- The corner embedding of labels into offsets is strictly monotone. -/
theorem cornerEmb_strictMono (w n : ℕ) (h : w + 1 ≤ n) : StrictMono (cornerEmb w n h) := by
  intro a b hab
  rw [Fin.lt_def] at hab ⊢
  have ha := a.2
  have hb := b.2
  simp only [cornerEmb]
  split_ifs <;> omega

/-- The corner embedding is injective. -/
theorem cornerEmb_injective (w n : ℕ) (h : w + 1 ≤ n) :
    Function.Injective (cornerEmb w n h) :=
  (cornerEmb_strictMono w n h).injective

/-- The lift of `cornerEmb` to ordered pairs (wedges). -/
def pairEmb {w n : ℕ} (h : w + 1 ≤ n) (p : Pair w) : W n :=
  ⟨(cornerEmb w n h p.fst, cornerEmb w n h p.snd), cornerEmb_strictMono w n h p.le⟩

/-- `pairEmb` embeds the first label by `cornerEmb`. -/
theorem pairEmb_fst {w n : ℕ} (h : w + 1 ≤ n) (p : Pair w) :
    (pairEmb h p).1.1 = cornerEmb w n h p.fst := rfl

/-- `pairEmb` embeds the second label by `cornerEmb`. -/
theorem pairEmb_snd {w n : ℕ} (h : w + 1 ≤ n) (p : Pair w) :
    (pairEmb h p).1.2 = cornerEmb w n h p.snd := rfl

/-- The pair embedding is injective. -/
theorem pairEmb_injective {w n : ℕ} (h : w + 1 ≤ n) :
    Function.Injective (pairEmb (w := w) (n := n) h) := by
  intro p q e
  have e1 : cornerEmb w n h p.fst = cornerEmb w n h q.fst := by
    rw [← pairEmb_fst h p, ← pairEmb_fst h q, e]
  have e2 : cornerEmb w n h p.snd = cornerEmb w n h q.snd := by
    rw [← pairEmb_snd h p, ← pairEmb_snd h q, e]
  obtain ⟨a, b, hab⟩ := p
  obtain ⟨c, d, hcd⟩ := q
  have f1 : a = c := cornerEmb_injective w n h e1
  have f2 : b = d := cornerEmb_injective w n h e2
  subst f1 f2
  rfl

/-- Weight of a negative label `a`: `a + 1`. -/
theorem weight_eq_of_neg {w : ℕ} {a : Label w} (ha : isNegative a) : weight a = a.1 + 1 := by
  simp [weight, ha]

/-- Weight of a positive label `a`: `2w − a`. -/
theorem weight_eq_of_not_neg {w : ℕ} {a : Label w} (ha : ¬ isNegative a) :
    weight a = 2 * w - a.1 := by
  simp [weight, ha]

/-- Every label has weight in `[1, w]`. -/
theorem weight_bounds {w : ℕ} (a : Label w) : 1 ≤ weight a ∧ weight a ≤ w := by
  have := a.2
  by_cases ha : isNegative a
  · rw [weight_eq_of_neg ha]
    unfold isNegative at ha
    omega
  · rw [weight_eq_of_not_neg ha]
    unfold isNegative at ha
    omega

/-- A negative label of weight `r` sits at signed index `−n + r`. -/
theorem signedIdx_cornerEmb_neg {w n : ℕ} (h : w + 1 ≤ n) {a : Label w}
    (ha : isNegative a) : signedIdx (cornerEmb w n h a) = -(n : ℤ) + weight a := by
  rw [weight_eq_of_neg ha]
  unfold isNegative at ha
  simp only [signedIdx, cornerEmb]
  split_ifs
  omega

/-- A positive label of weight `s` sits at signed index `n − s`. -/
theorem signedIdx_cornerEmb_pos {w n : ℕ} (h : w + 1 ≤ n) {a : Label w}
    (ha : isPositive a) : signedIdx (cornerEmb w n h a) = (n : ℤ) - weight a := by
  have hn : ¬ isNegative a := by unfold isNegative; unfold isPositive at ha; omega
  rw [weight_eq_of_not_neg hn]
  unfold isPositive at ha
  have := a.2
  simp only [signedIdx, cornerEmb]
  split_ifs <;> omega

/-- Signed index of an embedded label: `−n + r` (negative side) or `n − s` (positive side). -/
theorem signedIdx_cornerEmb {w n : ℕ} (h : w + 1 ≤ n) (a : Label w) :
    signedIdx (cornerEmb w n h a) =
      if isNegative a then -(n : ℤ) + weight a else (n : ℤ) - weight a := by
  split_ifs with ha
  · exact signedIdx_cornerEmb_neg h ha
  · exact signedIdx_cornerEmb_pos h (by unfold isNegative at ha; unfold isPositive; omega)

/-- The Toeplitz weight `n - |a|` of an embedded label is its corner weight. -/
theorem offsetWeight_cornerEmb {w n : ℕ} (h : w + 1 ≤ n) (a : Label w) :
    offsetWeight n (cornerEmb w n h a) = weight a := by
  have hb := weight_bounds a
  unfold offsetWeight
  rw [signedIdx_cornerEmb h a, abs_eq_max_neg]
  split_ifs <;> omega

/-! ## 4. Sides of a corner pair -/

/-- Every corner pair is same-side or mixed. -/
theorem sameSide_or_mixed {w : ℕ} (p : Pair w) : sameSide p ∨ mixed p := by
  have := Fin.lt_def.mp p.le
  unfold sameSide mixed isNegative isPositive
  omega

/-- A same-side pair is not mixed. -/
theorem not_mixed_of_sameSide {w : ℕ} {p : Pair w} (hp : sameSide p) : ¬ mixed p := by
  unfold sameSide at hp
  unfold mixed isNegative isPositive at *
  omega

/-- The signed indices of an embedded same-side pair have one sign. -/
theorem sameSign_of_sameSide {w n : ℕ} (h : w + 1 ≤ n) {p : Pair w} (hp : sameSide p) :
    (signedIdx (pairEmb h p).1.1 ≤ 0 ∧ signedIdx (pairEmb h p).1.2 ≤ 0) ∨
      (0 ≤ signedIdx (pairEmb h p).1.1 ∧ 0 ≤ signedIdx (pairEmb h p).1.2) := by
  have b1 := weight_bounds p.fst
  have b2 := weight_bounds p.snd
  rw [pairEmb_fst, pairEmb_snd]
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [signedIdx_cornerEmb_neg h h1, signedIdx_cornerEmb_neg h h2]
    omega
  · right
    rw [signedIdx_cornerEmb_pos h h1, signedIdx_cornerEmb_pos h h2]
    omega

/-! ## 5. The corner of `CᵀC` -/

/-- Closed form of the corner of `CᵀC` (integer): nonzero only on mixed pairs of equal
displacement, where it is `2 min(h, h') - 2 max(0, h + h' + min(|d|, |d'|) - n)`. -/
def mixedGram {w : ℕ} (n : ℕ) (p q : Pair w) : ℤ :=
  if mixed p ∧ mixed q ∧ displacement p = displacement q then
    2 * ((min (height p) (height q) : ℕ) : ℤ) -
      2 * ((Nat.sub (height p + height q +
        min (Int.natAbs (displacement p)) (Int.natAbs (displacement q))) n : ℕ) : ℤ)
  else 0

/-- The commutator Gram vanishes on an embedded same-side pair (left argument). -/
theorem commGram_pairEmb_of_sameSide_left {w n : ℕ} (h : w + 1 ≤ n) {p : Pair w}
    (hp : sameSide p) (q : Pair w) : commGram n (pairEmb h p) (pairEmb h q) = 0 := by
  rw [commGram_eq]
  refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j hj ↦ ?_
  rw [col_eq_zero_of_sameSign n _ _ i j (sameSign_of_sameSide h hp) (mem_Ico.mp hi)
    (mem_Ico.mp hj), zero_mul]

/-- The commutator Gram vanishes on an embedded same-side pair (right argument). -/
theorem commGram_pairEmb_of_sameSide_right {w n : ℕ} (h : w + 1 ≤ n) (p : Pair w)
    {q : Pair w} (hq : sameSide q) : commGram n (pairEmb h p) (pairEmb h q) = 0 := by
  rw [commGram_eq]
  refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j hj ↦ ?_
  rw [col_eq_zero_of_sameSign n _ _ i j (sameSign_of_sameSide h hq) (mem_Ico.mp hi)
    (mem_Ico.mp hj), mul_zero]

/-- **The corner of `CᵀC`.** -/
theorem commGram_pairEmb {w n : ℕ} (h : w + 1 ≤ n) (p q : Pair w) :
    commGram n (pairEmb h p) (pairEmb h q) = mixedGram n p q := by
  rcases sameSide_or_mixed p with hp | hp
  · rw [commGram_pairEmb_of_sameSide_left h hp, mixedGram,
      ite_eq_right (fun hc ↦ not_mixed_of_sameSide hp hc.1)]
  rcases sameSide_or_mixed q with hq | hq
  · rw [commGram_pairEmb_of_sameSide_right h p hq, mixedGram,
      ite_eq_right (fun hc ↦ not_mixed_of_sameSide hq hc.2.1)]
  have b1 := weight_bounds p.fst
  have b2 := weight_bounds p.snd
  have b3 := weight_bounds q.fst
  have b4 := weight_bounds q.snd
  rw [commGram_eq, pairEmb_fst, pairEmb_snd, pairEmb_fst, pairEmb_snd,
    signedIdx_cornerEmb_neg h hp.1, signedIdx_cornerEmb_pos h hp.2,
    signedIdx_cornerEmb_neg h hq.1, signedIdx_cornerEmb_pos h hq.2,
    colSum_mixed n _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
  simp only [mixedGram, hp, hq, true_and, displacement, height, Nat.sub_eq]
  split_ifs <;> omega

/-- The canonical Gram at embedded pairs, as an integer. -/
theorem gramQ0_pairEmb {w n : ℕ} (h : w + 1 ≤ n) (p q : Pair w) :
    gramQ0 n (pairEmb h p) (pairEmb h q) =
      (((if p = q then 2 * (weight p.fst : ℤ) * weight p.snd else 0) -
        commGram n (pairEmb h p) (pairEmb h q) : ℤ) : ℝ) := by
  unfold gramQ0 commGram
  simp only [(pairEmb_injective h).eq_iff, pairEmb_fst, pairEmb_snd, offsetWeight_cornerEmb]
  push_cast
  split_ifs <;> ring

/-- `finiteCornerBlock` in the same integer form. -/
theorem finiteCornerBlock_eq_int {w n : ℕ} (p q : Pair w) :
    finiteCornerBlock w n p q =
      (((if p = q then 2 * (weight p.fst : ℤ) * weight p.snd else 0) -
        mixedGram n p q : ℤ) : ℚ) := by
  unfold finiteCornerBlock baseEntry finiteCorrection mixedGram
  by_cases hpq : p = q
  · subst hpq
    rcases sameSide_or_mixed p with hs | hm
    · simp [hs, not_mixed_of_sameSide hs]
    · have hns : ¬ sameSide p := fun hs ↦ not_mixed_of_sameSide hs hm
      simp [hm, hns]
      ring
  · by_cases hc : mixed p ∧ mixed q ∧ displacement p = displacement q
    · simp [hpq, hc]
      ring
    · simp [hpq, hc]

/-! ## 6. The bridge -/

/-- **Corner–Gram bridge.** For `w + 1 ≤ n`, the corner of the canonical wedge Gram
`Q0 = gramQ0 n` of `F_n` at the embedded corner pairs is `finiteCornerBlock w n`. -/
def CornerGramBridge : Prop :=
  ∀ (w n : ℕ) (h : w + 1 ≤ n) (p q : Pair w),
    gramQ0 n (pairEmb h p) (pairEmb h q) = (finiteCornerBlock w n p q : ℝ)

/-- **The corner–Gram bridge holds** (every `n ≥ w + 1`, no stabilisation guard): the
corner of the canonical wedge Gram `gramQ0 n` of `F_n` at the embedded pairs is
`finiteCornerBlock w n`. -/
theorem cornerGramBridge : CornerGramBridge := by
  intro w n h p q
  rw [gramQ0_pairEmb, commGram_pairEmb, finiteCornerBlock_eq_int, Rat.cast_intCast]

/-- Matrix form of the bridge. -/
theorem gramQ0_submatrix_pairEmb {w n : ℕ} (h : w + 1 ≤ n) :
    (gramQ0 n).submatrix (pairEmb h) (pairEmb h) =
      (finiteCornerBlock w n).map (fun x : ℚ ↦ (x : ℝ)) := by
  ext p q
  exact cornerGramBridge w n h p q

/-- Stabilised corner: for `n ≥ 2w` (and `w + 1 ≤ n`) the corner of `Q0` is `B_w`
(`cornerBlock w`). -/
theorem gramQ0_pairEmb_stable {w n : ℕ} (h : w + 1 ≤ n) (hn : 2 * w ≤ n) (p q : Pair w) :
    gramQ0 n (pairEmb h p) (pairEmb h q) = (cornerBlock w p q : ℝ) := by
  rw [cornerGramBridge w n h p q, finiteCornerBlock_eq_cornerBlock hn]

end

end ToeplitzSOS.Uniform
