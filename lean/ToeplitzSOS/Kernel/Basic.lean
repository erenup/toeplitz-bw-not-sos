import ToeplitzSOS.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Wedge indices and the high-gap indicator vectors

The diagonal indices are offset encoded, as in `ToeplitzSOS.Defs`.  Thus the
difference of two offsets is the difference of the corresponding signed indices.
-/

namespace ToeplitzSOS.Kernel

noncomputable section
open Matrix

/-- Pairs of strictly increasing Toeplitz diagonal indices. -/
abbrev W (n : ℕ) := {ab : Fin (2 * n - 1) × Fin (2 * n - 1) // ab.1 < ab.2}

/-- Difference between the two offsets of a wedge. -/
def gap {n : ℕ} (w : W n) : ℕ := w.val.2.val - w.val.1.val

/-- The indicator of the wedges with gap `s`. -/
def u (n s : ℕ) : W n → ℝ := fun w ↦ if gap w = s then 1 else 0

/-- A wedge polynomial indexed by `W n`. -/
def wedge {n : ℕ} (w : W n) : MvPolynomial (V n) ℝ := z w.1.1 w.1.2

/-- The exact polynomial identity required of a wedge Gram matrix. -/
def IsWedgeGram (n : ℕ) (Q : Matrix (W n) (W n) ℝ) : Prop :=
  toeplitzBW n = ∑ p, ∑ q, MvPolynomial.C (Q p q) * wedge p * wedge q

/-- The target of the forced-kernel theorem, recorded as a proposition independently of its proof. -/
def ForcedKernelStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ Q : Matrix (W n) (W n) ℝ,
    Q.PosSemidef → IsWedgeGram n Q →
      ∀ s, n ≤ s → s ≤ 2 * n - 2 → Q *ᵥ u n s = 0

/-- The quadratic form of a PSD real matrix vanishes exactly on its kernel. -/
theorem posSemidef_mulVec_eq_zero_iff {n : ℕ} (Q : Matrix (W n) (W n) ℝ)
    (hQ : Q.PosSemidef) (v : W n → ℝ) :
    v ⬝ᵥ (Q *ᵥ v) = 0 ↔ Q *ᵥ v = 0 := by
  simpa using hQ.dotProduct_mulVec_zero_iff v

/-- The high gaps are naturally indexed by `Fin (n - 1)`. -/
def highGap (n : ℕ) (k : Fin (n - 1)) : ℕ := n + k.val

/-- A representative wedge for a high gap, with first endpoint zero. -/
def highWedge (n : ℕ) (k : Fin (n - 1)) : W n :=
  ⟨(⟨0, by have := k.isLt; omega⟩, ⟨n + k.val, by have := k.isLt; omega⟩),
    by
      change 0 < n + k.val
      have := k.isLt
      omega⟩

/-- The representative wedge of a high gap has that gap. -/
@[simp] theorem gap_highWedge (n : ℕ) (k : Fin (n - 1)) :
    gap (highWedge n k) = highGap n k := by
  rfl

/-- The high-gap indicators evaluated at the representative wedges form the identity. -/
@[simp] theorem u_highWedge (n : ℕ) (i j : Fin (n - 1)) :
    u n (highGap n i) (highWedge n j) = if i = j then 1 else 0 := by
  classical
  simp [u, gap_highWedge, highGap, Fin.ext_iff, eq_comm]

/-- Distinct high-gap indicator vectors are linearly independent. -/
theorem highGap_independent (n : ℕ) :
    LinearIndependent ℝ (fun k : Fin (n - 1) ↦ u n (highGap n k)) := by
  classical
  rw [linearIndependent_iff']
  intro s g h i hi
  have hval := congrArg (fun v : W n → ℝ ↦ v (highWedge n i)) h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    u_highWedge] at hval
  simpa [Finset.sum_ite_eq', hi] using hval

/-- The rank consequence of the high-gap kernel, for an arbitrary real matrix. -/
theorem rank_le_of_highGap_kernel {n : ℕ} (hn : 2 ≤ n)
    (Q : Matrix (W n) (W n) ℝ)
    (hker : ∀ s, n ≤ s → s ≤ 2 * n - 2 → Q *ᵥ u n s = 0) :
    Q.rank ≤ Fintype.card (W n) - (n - 1) := by
  classical
  let v : Fin (n - 1) → (LinearMap.ker Q.mulVecLin) := fun k ↦
    ⟨u n (highGap n k), by
      change Q *ᵥ u n (highGap n k) = 0
      apply hker
      · simp [highGap]
      · have := k.isLt
        dsimp [highGap]
        omega⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (Submodule.subtype _)
    simpa [Function.comp_def, v] using highGap_independent n
  have hkerdim : n - 1 ≤ Module.finrank ℝ (LinearMap.ker Q.mulVecLin) := by
    simpa using hv.fintype_card_le_finrank
  have hrank : Q.rank = Module.finrank ℝ (LinearMap.range Q.mulVecLin) := by
    rw [Q.rank_eq_finrank_range_toLin (Pi.basisFun ℝ (W n)) (Pi.basisFun ℝ (W n))]
    simp only [Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
    rfl
  have hnullity := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
  rw [← hrank, Module.finrank_pi] at hnullity
  omega

/-- Corollary K' follows directly from the forced-kernel statement. -/
theorem forcedKernel_implies_rank (hK : ForcedKernelStatement)
    (n : ℕ) (hn : 2 ≤ n) (Q : Matrix (W n) (W n) ℝ)
    (hQ : Q.PosSemidef) (hgram : IsWedgeGram n Q) :
    Q.rank ≤ Fintype.card (W n) - (n - 1) := by
  exact rank_le_of_highGap_kernel hn Q (hK n hn Q hQ hgram)

end

end ToeplitzSOS.Kernel
