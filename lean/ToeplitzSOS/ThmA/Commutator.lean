import ToeplitzSOS.ThmA.Defs
import ToeplitzSOS.ThmA.Reindex
import Mathlib

/-!
# Commutator windows and their quadratic form

The commutator entries are differences of finite windows. Summing their
squares gives the tent-kernel formula, uniformly in the matrix order.
-/

open Finset

noncomputable section

namespace ToeplitzSOS.ThmA

/-! ### Index objects of the commutator -/

/-- τ-filter window `k` of the diagonal (or gap) `e`:
`P ∈ [1, n−1]` with `k < τ(P)` and `k < τ(P + e)`. -/
def win (n e k : ℤ) : Finset ℤ :=
  (Icc 1 (n - 1)).filter (fun P => k < tau n P ∧ k < tau n (P + e))

/-- Tent coefficient `min(τP, τ(P+d), τP', τ(P'+d))` of the diagonal `d`. -/
def tent4 (n d P P' : ℤ) : ℤ :=
  min (min (tau n P) (tau n (P + d))) (min (tau n P') (tau n (P' + d)))

/-- The tent coefficient is symmetric in `P, P'`. -/
theorem tent4_comm (n d P P' : ℤ) : tent4 n d P P' = tent4 n d P' P := by
  unfold tent4; omega

/-! ### The τ-windows -/

/-- The window `k` is empty once `n − |e| ≤ 2k + 1`. -/
theorem win_eq_empty (n e k : ℤ) (hk : n - |e| ≤ 2 * k + 1) : win n e k = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [win, Finset.mem_filter, Finset.mem_Icc] at hP
  simp only [tau] at hP
  rcases le_total 0 e with h | h
  · rw [abs_of_nonneg h] at hk; omega
  · rw [abs_of_nonpos h] at hk; omega

/-- For `k ≥ 0` the window `k` is the interval
`[k + 1 + max(−e, 0), n − 1 − k − max(e, 0)]`. -/
theorem win_eq_Icc (n e k : ℤ) (hk : 0 ≤ k) :
    win n e k = Icc (k + 1 + max (-e) 0) (n - 1 - k - max e 0) := by
  ext P; simp only [win, mem_filter, mem_Icc]; simp only [tau]; omega

/-- For `k ≥ 0` the window `k` is the τ-filter `k < min(τP, τ(P+e))` of `Dset n e`. -/
theorem win_eq_filter_Dset (n e k : ℤ) (hk : 0 ≤ k) :
    win n e k = (Dset n e).filter (fun P => k < min (tau n P) (tau n (P + e))) := by
  ext P; simp only [win, Dset, mem_filter, mem_Icc]; simp only [tau]; omega

section Generic
variable {R : Type*} [CommRing R]

/-- `z_aa = 0`. -/
@[simp] theorem wedge_self (x y : ℤ → R) (a : ℤ) : wedge x y a a = 0 := by
  unfold wedge; ring

/-- `z_ba = −z_ab`. -/
theorem wedge_swap (x y : ℤ → R) (a b : ℤ) : wedge x y b a = -wedge x y a b := by
  unfold wedge; ring

/-- Commutator entry `(XY − YX)_{ij} = ∑_{h<n} z(i−h, h−j)`, with `ℤ` indices. -/
def cEntry (n : ℤ) (x y : ℤ → R) (i j : ℤ) : R :=
  ∑ h ∈ Ico 0 n, wedge x y (i - h) (h - j)

/-! ### The commutator entry -/

/-- The `(i, j)` entry of the commutator of two generic Toeplitz matrices is
`cEntry n x y i j = ∑_{h<n} z(i−h, h−j)`. -/
theorem comm_apply (n : ℕ) (x y : ℤ → R) (i j : Fin n) :
    (tmat n x * tmat n y - tmat n y * tmat n x) i j = cEntry n x y i j := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, ← sum_sub_distrib, cEntry,
    ← sum_fin_eq_sum_Ico n (fun h => wedge x y ((i : ℤ) - h) (h - (j : ℤ)))]
  refine sum_congr rfl fun k _ => ?_
  simp only [tmat, wedge]; ring

/-! ### The middle block cancels (pairing `h ↦ lo + hi − 1 − h`) -/

/-- A block of `∑_h z(i−h, h−j)` that is symmetric under `h ↦ lo + hi − 1 − h`
(`lo + hi − 1 = i + j`) cancels. -/
theorem sum_Ico_wedge_reflect (x y : ℤ → R) (i j lo hi : ℤ) (hs : lo + hi - 1 = i + j) :
    ∑ h ∈ Ico lo hi, wedge x y (i - h) (h - j) = 0 := by
  refine Finset.sum_involution (fun h _ => lo + hi - 1 - h) ?_ ?_ ?_ ?_
  · intro a _
    have e1 : i - (lo + hi - 1 - a) = a - j := by omega
    have e2 : lo + hi - 1 - a - j = i - a := by omega
    rw [e1, e2, wedge_swap]; ring
  · intro a _ hne heq
    apply hne
    have : i - a = a - j := by omega
    rw [this, wedge_self]
  · intro a ha; simp only [mem_Ico] at ha ⊢; omega
  · intro a _; ring

/-! ### Commutator entry as a difference of two prefix sums of the diagonal `d = i − j` -/

/-- The commutator entry as a difference of two prefix sums of the diagonal
`d = i − j`. -/
theorem cEntry_eq_prefix (n : ℤ) (x y : ℤ → R) (i j : ℤ)
    (hi : 0 ≤ i) (hi' : i < n) (hj : 0 ≤ j) (hj' : j < n) :
    cEntry n x y i j =
      (∑ P ∈ Icc (max (j - i) 0 + 1) (n - 1 - i), wedge x y (-P) (P + (i - j)))
      - ∑ P ∈ Icc (max (j - i) 0 + 1) j, wedge x y (-P) (P + (i - j)) := by
  unfold cEntry
  set r := min i j with hr
  set Rm := max i j with hR
  have h1 : Ico (0:ℤ) n = Ico 0 r ∪ Ico r n := (Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have h2 : Ico r n = Ico r (Rm + 1) ∪ Ico (Rm + 1) n :=
    (Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  rw [h1, sum_union (Ico_disjoint_Ico_consecutive _ _ _), h2,
    sum_union (Ico_disjoint_Ico_consecutive _ _ _),
    sum_Ico_wedge_reflect x y i j r (Rm + 1) (by omega), zero_add]
  have hright : ∑ h ∈ Ico (Rm + 1) n, wedge x y (i - h) (h - j)
      = ∑ P ∈ Icc (max (j - i) 0 + 1) (n - 1 - i), wedge x y (-P) (P + (i - j)) := by
    refine Finset.sum_nbij' (fun h => h - i) (fun P => P + i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico, mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico, mem_Icc] at ha ⊢; omega
    · intro a _; ring
    · intro a _; ring
    · intro a _; congr 1 <;> ring
  have hleft : ∑ h ∈ Ico 0 r, wedge x y (i - h) (h - j)
      = -∑ P ∈ Icc (max (j - i) 0 + 1) j, wedge x y (-P) (P + (i - j)) := by
    rw [← sum_neg_distrib]
    refine Finset.sum_nbij' (fun h => j - h) (fun P => j - P) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico, mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico, mem_Icc] at ha ⊢; omega
    · intro a _; ring
    · intro a _; ring
    · intro a _
      rw [← wedge_swap]; congr 1 <;> ring
  rw [hright, hleft]; ring

/-! ### The entry `(r + d⁺, r + d⁻)` is `Win_r − Win_{L−r}` -/

/-- Difference of two interval sums with a common lower endpoint. Both
upper endpoints are at least the common lower endpoint. -/
theorem sum_Icc_sub_Icc (a b c : ℤ) (f : ℤ → R) (hab : a ≤ b) (hac : a ≤ c) :
    ∑ i ∈ Icc (a + 1) b, f i - ∑ i ∈ Icc (a + 1) c, f i
      = ∑ i ∈ Icc (c + 1) b, f i - ∑ i ∈ Icc (b + 1) c, f i := by
  rcases le_total c b with h | h
  · have e1 : Icc (a + 1) b = Icc (a + 1) c ∪ Icc (c + 1) b := by
      ext i; simp only [mem_union, mem_Icc]; omega
    have hdis : Disjoint (Icc (a + 1) c) (Icc (c + 1) b) := by
      rw [disjoint_left]; intro i h1 h2; simp only [mem_Icc] at h1 h2; omega
    rw [e1, sum_union hdis, Icc_eq_empty (by omega : ¬ b + 1 ≤ c), sum_empty]; ring
  · have e1 : Icc (a + 1) c = Icc (a + 1) b ∪ Icc (b + 1) c := by
      ext i; simp only [mem_union, mem_Icc]; omega
    have hdis : Disjoint (Icc (a + 1) b) (Icc (b + 1) c) := by
      rw [disjoint_left]; intro i h1 h2; simp only [mem_Icc] at h1 h2; omega
    rw [e1, sum_union hdis, Icc_eq_empty (by omega : ¬ c + 1 ≤ b), sum_empty]; ring

/-- The commutator entry at `(r + d⁺, r + d⁻)` is `Win_r − Win_{L−r}`,
`L = n − 1 − |d|`. -/
theorem cEntry_eq_win (n d r : ℤ) (x y : ℤ → R) (_hd : |d| < n) (hr : 0 ≤ r)
    (hr' : r ≤ n - 1 - |d|) :
    cEntry n x y (r + max d 0) (r + max (-d) 0)
      = ∑ P ∈ win n d r, wedge x y (-P) (P + d)
        - ∑ P ∈ win n d (n - 1 - |d| - r), wedge x y (-P) (P + d) := by
  have habs : |d| = max d 0 + max (-d) 0 := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  rw [habs] at hr' ⊢
  have e1 : r + max d 0 - (r + max (-d) 0) = d := by omega
  have e2 : max (r + max (-d) 0 - (r + max d 0)) 0 = max (-d) 0 := by omega
  have w1 : win n d r = Icc (r + max (-d) 0 + 1) (n - 1 - (r + max d 0)) := by
    rw [win_eq_Icc _ _ _ hr]; congr 1 <;> ring
  have w2 : win n d (n - 1 - (max d 0 + max (-d) 0) - r)
      = Icc (n - 1 - (r + max d 0) + 1) (r + max (-d) 0) := by
    rw [win_eq_Icc _ _ _ (by omega)]; congr 1 <;> ring
  rw [cEntry_eq_prefix n x y _ _ (by omega) (by omega) (by omega) (by omega), e1, e2, w1, w2]
  exact sum_Icc_sub_Icc _ _ _ _ (by omega) (by omega)

/-! ### Folding the `n − |d|` entries of a diagonal onto the nested windows -/

/-- Folding the `n − |d|` entries of a diagonal onto the nested windows:
`∑_r (Win_r − Win_{L−r})² = 2 ∑_k Win_k²`. Protected (avoids a clash with
`Finset.fold` under `open Finset`): write `ThmA.fold`. -/
protected theorem fold (n d : ℤ) (_hd : |d| < n) (v : ℤ → R) :
    ∑ r ∈ Ico 0 (n - |d|),
        ((∑ P ∈ win n d r, v P) - ∑ P ∈ win n d (n - 1 - |d| - r), v P) ^ 2
      = 2 * ∑ k ∈ Ico 0 n, (∑ P ∈ win n d k, v P) ^ 2 := by
  set L := n - 1 - |d| with hL
  have hcross : ∀ r ∈ Ico 0 (n - |d|),
      ((∑ P ∈ win n d r, v P) - ∑ P ∈ win n d (L - r), v P) ^ 2
        = (∑ P ∈ win n d r, v P) ^ 2 + (∑ P ∈ win n d (L - r), v P) ^ 2 := by
    intro r hr; simp only [mem_Ico] at hr
    rcases le_total (2 * r) L with h | h
    · rw [win_eq_empty n d (L - r) (by omega)]; simp
    · rw [win_eq_empty n d r (by omega)]; simp
  rw [sum_congr rfl hcross, sum_add_distrib]
  have hrefl : ∑ r ∈ Ico 0 (n - |d|), (∑ P ∈ win n d (L - r), v P) ^ 2
      = ∑ r ∈ Ico 0 (n - |d|), (∑ P ∈ win n d r, v P) ^ 2 := by
    refine Finset.sum_nbij' (fun r => L - r) (fun r => L - r) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [mem_Ico] at ha ⊢; omega
    · intro a _; ring
    · intro a _; ring
    · intro a _; rfl
  have hext : ∑ k ∈ Ico 0 n, (∑ P ∈ win n d k, v P) ^ 2
      = ∑ k ∈ Ico 0 (n - |d|), (∑ P ∈ win n d k, v P) ^ 2 := by
    have hsub : Ico 0 (n - |d|) ⊆ Ico 0 n := by
      intro k hk; simp only [mem_Ico] at hk ⊢; have := abs_nonneg d; omega
    rw [← sum_subset hsub]
    intro k hk hk'; simp only [mem_Ico, not_and, not_lt] at hk hk'
    rw [win_eq_empty n d k (by have := abs_nonneg d; omega)]; simp
  rw [hrefl, hext]; ring

/-! ### `‖C‖² = 2 ∑_d ∑_k Win_k²` -/

/-- (window formula): `‖XY − YX‖² = 2 ∑_{|d|<n} ∑_{0≤k<n} (∑_{P ∈ Win_k(d)} z_{−P,P+d})²`
for generic Toeplitz data over any commutative ring. Used by `frob_comm_tent`. -/
theorem frob_comm_windows (n : ℕ) (x y : ℤ → R) :
    ToeplitzSOS.frob (tmat n x * tmat n y - tmat n y * tmat n x)
      = 2 * ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ k ∈ Ico (0 : ℤ) n,
          (∑ P ∈ win n d k, wedge x y (-P) (P + d)) ^ 2 := by
  unfold ToeplitzSOS.frob
  simp_rw [comm_apply]
  rw [sum_fin_fin_eq_sum_Ico n (fun i j => cEntry (n : ℤ) x y i j ^ 2), rect_reindex, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  simp only [mem_Ioo] at hd
  have hdn : |d| < n := abs_lt.mpr ⟨by omega, by omega⟩
  have hmin : min ((n : ℤ) - max d 0) ((n : ℤ) - max (-d) 0) = n - |d| := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  rw [hmin, ← ThmA.fold (n : ℤ) d hdn]
  refine sum_congr rfl fun r hr => ?_
  simp only [mem_Ico] at hr
  rw [cEntry_eq_win (n : ℤ) d r x y hdn hr.1 (by omega)]

/-! ### `‖C‖² = 2 ∑_d ∑_{P,P' ∈ Dset d} tent4 · v_P v_{P'}` -/

/-- (tent form): `‖XY − YX‖² = 2 ∑_d ∑_{P,P' ∈ Dset d} tent4(d,P,P') z_{−P,P+d} z_{−P',P'+d}`. Used by `frob_comm_split`, `Symmetric.frob_comm_ext`. -/
theorem frob_comm_tent (n : ℕ) (x y : ℤ → R) :
    ToeplitzSOS.frob (tmat n x * tmat n y - tmat n y * tmat n x)
      = 2 * ∑ d ∈ Ioo (-(n : ℤ)) n, ∑ P ∈ Dset n d, ∑ P' ∈ Dset n d,
          ((tent4 n d P P' : ℤ) : R) * (wedge x y (-P) (P + d) * wedge x y (-P') (P' + d)) := by
  rw [frob_comm_windows]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  have h1 : ∀ k ∈ Ico (0 : ℤ) n, (∑ P ∈ win n d k, wedge x y (-P) (P + d)) ^ 2
      = (∑ P ∈ (Dset n d).filter (fun P => k < min (tau n P) (tau n (P + d))),
            wedge x y (-P) (P + d)) *
        (∑ Q ∈ (Dset n d).filter (fun Q => k < min (tau n Q) (tau n (Q + d))),
            wedge x y (-Q) (Q + d)) := by
    intro k hk; simp only [mem_Ico] at hk; rw [sq, win_eq_filter_Dset _ _ _ hk.1]
  rw [sum_congr rfl h1, sum_win_mul (Dset n d) (fun P => min (tau n P) (tau n (P + d))) n ?_]
  · rfl
  · intro P hP; simp only [Dset, mem_filter, mem_Icc] at hP; simp only [tau]; omega

end Generic

end ToeplitzSOS.ThmA

end
