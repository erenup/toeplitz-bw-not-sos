import ToeplitzSOS.Negative.Analytic.Series

/-! # Principal truncations of the literal baseline kernels -/

namespace ToeplitzSOS.Negative.Analytic
noncomputable section
open Finset

/-- The square of natural depths below the cutoff. -/
def pairBox (m : ℕ) : Finset (ℕ × ℕ) := range m ×ˢ range m

/-- The four-dimensional principal depth box. -/
def depthBox (m : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := pairBox m ×ˢ pairBox m

/-- Replace finite coordinates by their natural-depth square. -/
theorem sum_fin_pair (m : ℕ) (f : ℕ × ℕ → ℂ) :
    (∑ p : Fin m, ∑ q : Fin m, f (p.val,q.val)) = ∑ p ∈ pairBox m, f p := by
  simp only [pairBox, sum_product]
  rw [Fin.sum_univ_eq_sum_range (fun p => ∑ q : Fin m, f (p,q.val)) m]
  apply sum_congr rfl
  intro p _
  exact Fin.sum_univ_eq_sum_range (fun q => f (p,q)) m

/-- Replace four finite coordinates by their natural-depth box. -/
theorem sum_fin_four (m : ℕ) (f : (ℕ × ℕ) × (ℕ × ℕ) → ℂ) :
    (∑ p : Fin m, ∑ q : Fin m, ∑ r : Fin m, ∑ s : Fin m,
      f ((p.val,q.val),(r.val,s.val))) = ∑ p ∈ depthBox m, f p := by
  simp only [depthBox, sum_product]
  calc
    _ = ∑ p : Fin m, ∑ q : Fin m, ∑ r ∈ pairBox m, f ((p.val,q.val),r) := by
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro q _
      exact sum_fin_pair m (fun r => f ((p.val,q.val),r))
    _ = _ := sum_fin_pair m (fun p => ∑ r ∈ pairBox m, f (p,r))

/-- A pure-index sum is exactly the strict upper part of the principal square. -/
theorem sum_pureIndex (m : ℕ) (f : ℕ × ℕ → ℂ) :
    (∑ p : PureIndex m, f (p.1.1.val,p.1.2.val)) =
      ∑ p ∈ pairBox m, if p.1 < p.2 then f p else 0 := by
  have h := sum_subtype (F := inferInstance) (p := fun p : Fin m × Fin m => p.1 < p.2) (univ.filter (fun p : Fin m × Fin m => p.1 < p.2))
    (by intro p; simp) (fun p => f (p.1.val,p.2.val))
  rw [← h, sum_filter, Fintype.sum_prod_type]
  exact sum_fin_pair m (fun p => if p.1 < p.2 then f p else 0)

/-- The finite diagonal is the principal truncation of its proved series. -/
theorem baselineD_eq_sum (m : ℕ) (x y z w : ℂ) :
    baselineD m x y z w = ∑ p ∈ pairBox m, diagonalSeriesTerm x y z w p := by
  unfold baselineD
  convert! sum_pureIndex m (fun p => 2 * ((p.1 : ℂ) + 1) * ((p.2 : ℂ) + 1) *
    natPureFeature p x y * natPureFeature p z w) using 1

/-- The finite cross kernel is the principal truncation of the same-gap series. -/
theorem baselineK_eq_sum (m : ℕ) (x y z w : ℂ) :
    baselineK m x y z w = ∑ p ∈ depthBox m, crossSeriesTerm x y z w p := by
  have he : baselineK m x y z w = ∑ p : PureIndex m, ∑ r : PureIndex m,
      crossSeriesTerm x y z w ((p.1.1.val,p.1.2.val),(r.1.1.val,r.1.2.val)) := by
    unfold baselineK
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro r _
    have hp : p.1.1.val < p.1.2.val := p.2
    have hr : r.1.1.val < r.1.2.val := r.2
    simp only [crossSeriesTerm, hp, hr, true_and, natPureFeature, pureFeature]
  rw [he]
  calc
    _ = ∑ p : PureIndex m, ∑ r ∈ pairBox m,
        if r.1 < r.2 then crossSeriesTerm x y z w ((p.1.1.val,p.1.2.val),r) else 0 := by
      apply sum_congr rfl
      intro p _
      exact sum_pureIndex m (fun r => crossSeriesTerm x y z w ((p.1.1.val,p.1.2.val),r))
    _ = ∑ p ∈ pairBox m, if p.1 < p.2 then ∑ r ∈ pairBox m,
        if r.1 < r.2 then crossSeriesTerm x y z w (p,r) else 0 else 0 :=
      sum_pureIndex m (fun p => ∑ r ∈ pairBox m,
        if r.1 < r.2 then crossSeriesTerm x y z w (p,r) else 0)
    _ = _ := by
      simp only [depthBox, sum_product]
      apply sum_congr rfl
      intro p _
      by_cases hp : p.1 < p.2
      · simp only [hp, ite_true]
        apply sum_congr rfl
        intro r _
        by_cases hr : r.1 < r.2 <;> simp [crossSeriesTerm, hp, hr]
      · simp [crossSeriesTerm, hp]

/-- The finite mixed kernel is the principal truncation of its literal tensor series. -/
theorem baselineB_eq_sum (m : ℕ) (x y z w : ℂ) :
    baselineB m x y z w = ∑ p ∈ depthBox m, mixedSeriesTerm x y z w p := by
  rw [← sum_fin_four]
  unfold baselineB mixedKernel
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  simp only [mixedSeriesTerm, mixedDiagonalSeriesTerm, totalSeriesTerm,
    totalMinimum, baselineMixedEntry, Prod.mk.injEq, ← Fin.ext_iff]
  split_ifs <;> simp only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] <;> ring

/-- Every omitted box index has total degree at least the cutoff. -/
theorem mem_depthBox_of_totalDepth_lt {m : ℕ} (p : (ℕ × ℕ) × (ℕ × ℕ))
    (hp : totalDepth p < m) : p ∈ depthBox m := by
  simp only [depthBox, pairBox, mem_product, mem_range]
  dsimp [totalDepth] at hp
  omega

/-- A repeated-pair term of low total degree lies inside the principal square. -/
theorem mem_pairBox_of_diagonalDepth_lt {m : ℕ} (p : ℕ × ℕ)
    (hp : totalDepth (diagonalDepth p) < m) : p ∈ pairBox m := by
  simp only [pairBox, mem_product, mem_range]
  dsimp [totalDepth, diagonalDepth] at hp
  omega

end
end ToeplitzSOS.Negative.Analytic
