import ToeplitzSOS.Defs
import Mathlib

/-!
# The moment-functional obstruction: quadratic polarization
-/

namespace ToeplitzSOS.General

noncomputable section

open MvPolynomial Finset

/-- Point evaluation of the two letters: `x_a ↦ U a`, `y_a ↦ V a`. -/
def pt {P : Type*} (U V : P → ℝ) : CoordFamily × P → ℝ
  | (.x, a) => U a
  | (.y, a) => V a

/-- The point `pt U V` evaluates the `x`-variables by `U`. -/
@[simp] theorem pt_x {P : Type*} (U V : P → ℝ) (a : P) : pt U V (.x, a) = U a := rfl
/-- The point `pt U V` evaluates the `y`-variables by `V`. -/
@[simp] theorem pt_y {P : Type*} (U V : P → ℝ) (a : P) : pt U V (.y, a) = V a := rfl

/-- Euler's identity, twice: a homogeneous quadratic polynomial is a quadratic form. -/
theorem exists_quadForm {σ : Type*} [Fintype σ] {q : MvPolynomial σ ℝ}
    (hq : q.IsHomogeneous 2) :
    ∃ c : σ → σ → ℝ, ∀ w : σ → ℝ, eval w q = ∑ a, ∑ b, c a b * (w a * w b) := by
  have h1 : ∀ a, (pderiv a q).IsHomogeneous 1 := fun a => hq.pderiv
  have h0 : ∀ a b, (pderiv b (pderiv a q)).IsHomogeneous 0 := fun a b => (h1 a).pderiv
  have hC : ∀ a b, pderiv b (pderiv a q) = C ((pderiv b (pderiv a q)).coeff 0) := by
    intro a b
    exact totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous σ).mpr (h0 a b))
  refine ⟨fun a b => (pderiv b (pderiv a q)).coeff 0 / 2, fun w => ?_⟩
  have e2 := congrArg (eval w) hq.sum_X_mul_pderiv
  have e1 : ∀ a, eval w (pderiv a q) =
      ∑ b, w b * (pderiv b (pderiv a q)).coeff 0 := by
    intro a
    have := congrArg (eval w) (h1 a).sum_X_mul_pderiv
    simp only [map_sum, map_mul, eval_X, one_smul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hC a b, eval_C, coeff_zero_C]
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, Nat.cast_ofNat, e1, map_ofNat] at e2
  have : eval w q = (∑ a, w a * ∑ b, w b * (pderiv b (pderiv a q)).coeff 0) / 2 := by
    rw [e2]; ring
  rw [this, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## Polarization of a quadratic form -/

/-- The quadratic form with coefficients `c`. -/
def quadF {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (w : σ → ℝ) : ℝ :=
  ∑ a, ∑ b, c a b * (w a * w b)

/-- Its polarization. -/
def polar {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (w w' : σ → ℝ) : ℝ :=
  ∑ a, ∑ b, c a b * (w a * w' b + w' a * w b)

/-- `quadF c (w + w') = quadF c w + quadF c w' + polar c w w'`. -/
theorem quadF_add {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (w w' : σ → ℝ) :
    quadF c (w + w') = quadF c w + quadF c w' + polar c w w' := by
  simp only [quadF, polar, Pi.add_apply, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `polar c` is additive in its first argument. -/
theorem polar_add_left {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (w₁ w₂ w' : σ → ℝ) :
    polar c (w₁ + w₂) w' = polar c w₁ w' + polar c w₂ w' := by
  simp only [polar, Pi.add_apply, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `polar c` is homogeneous in its first argument. -/
theorem polar_smul_left {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (r : ℝ) (w w' : σ → ℝ) :
    polar c (r • w) w' = r * polar c w w' := by
  simp only [polar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `polar c` is additive in its second argument. -/
theorem polar_add_right {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (w w₁ w₂ : σ → ℝ) :
    polar c w (w₁ + w₂) = polar c w w₁ + polar c w w₂ := by
  simp only [polar, Pi.add_apply, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `polar c` is homogeneous in its second argument. -/
theorem polar_smul_right {σ : Type*} [Fintype σ] (c : σ → σ → ℝ) (r : ℝ) (w w' : σ → ℝ) :
    polar c w (r • w') = r * polar c w w' := by
  simp only [polar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `pt` is additive. -/
theorem pt_add {P : Type*} (U U' V V' : P → ℝ) : pt (U + U') (V + V') = pt U V + pt U' V' := by
  funext v; rcases v with ⟨_ | _, a⟩ <;> rfl

/-- `pt` commutes with scalar multiplication. -/
theorem pt_smul {P : Type*} (r : ℝ) (U V : P → ℝ) : pt (r • U) (r • V) = r • pt U V := by
  funext v; rcases v with ⟨_ | _, a⟩ <;> rfl

/-- `pt U V = pt U 0 + pt 0 V`. -/
theorem pt_split {P : Type*} (U V : P → ℝ) : pt U V = pt U 0 + pt 0 V := by
  rw [← pt_add, add_zero, zero_add]

/-- The bilinear form `(U, V) ↦ polar c (pt U 0) (pt 0 V)`. -/
def bil {P : Type*} [Fintype (CoordFamily × P)] (c : CoordFamily × P → CoordFamily × P → ℝ) :
    (P → ℝ) →ₗ[ℝ] (P → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun U V => polar c (pt U 0) (pt 0 V))
    (fun U₁ U₂ V => by
      rw [← polar_add_left, ← pt_add, add_zero])
    (fun r U V => by
      rw [smul_eq_mul, ← polar_smul_left, ← pt_smul, smul_zero])
    (fun U V₁ V₂ => by
      rw [← polar_add_right, ← pt_add, add_zero])
    (fun r U V => by
      rw [smul_eq_mul, ← polar_smul_right, ← pt_smul, smul_zero])

/-- Definition of `bil` as a polarisation (`rfl`). -/
theorem bil_apply {P : Type*} [Fintype (CoordFamily × P)]
    (c : CoordFamily × P → CoordFamily × P → ℝ) (U V : P → ℝ) :
    bil c U V = polar c (pt U 0) (pt 0 V) := rfl

/-- A quadratic form vanishing on `x = 0`, on `y = 0` and on `x = y` is an alternating
bilinear form in `(x, y)`. -/
theorem quadF_pt_eq_bil {P : Type*} [Fintype (CoordFamily × P)]
    (c : CoordFamily × P → CoordFamily × P → ℝ)
    (hx : ∀ U, quadF c (pt U 0) = 0) (hy : ∀ V, quadF c (pt 0 V) = 0) (U V : P → ℝ) :
    quadF c (pt U V) = bil c U V := by
  rw [pt_split, quadF_add, hx, hy, zero_add, zero_add, bil_apply]

/-- Under the vanishing hypotheses on `quadF c`, `bil c` is antisymmetric: `bil c U V = −bil c V U`. -/
theorem bil_alt {P : Type*} [Fintype (CoordFamily × P)]
    (c : CoordFamily × P → CoordFamily × P → ℝ)
    (hx : ∀ U, quadF c (pt U 0) = 0) (hy : ∀ V, quadF c (pt 0 V) = 0)
    (hd : ∀ U, quadF c (pt U U) = 0) (U V : P → ℝ) :
    bil c U V = - bil c V U := by
  have h := hd (U + V)
  rw [quadF_pt_eq_bil c hx hy] at h
  have hU := hd U
  have hV := hd V
  rw [quadF_pt_eq_bil c hx hy] at hU hV
  simp only [map_add, LinearMap.add_apply] at h
  linarith

/-! ## The functional -/

/-- The mixed second difference `Σ_{s,t=±1} s t Φ(A + s A', B + t B')`. -/
def pol4 {P : Type*} (Φ : (P → ℝ) → (P → ℝ) → ℝ) (A A' B B' : P → ℝ) : ℝ :=
  Φ (A + A') (B + B') - Φ (A + A') (B - B') - Φ (A - A') (B + B') + Φ (A - A') (B - B')

def momentSum {P ι : Type*} [Fintype ι] (Φ : (P → ℝ) → (P → ℝ) → ℝ)
    (u : ι → ι → P → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, pol4 Φ (u i j) (u k l) (u j k) (u l i)

/-- Moving the fourth summation index to the front. -/
theorem sum4_rotate {ι : Type*} [Fintype ι] (g : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, g l i j k = ∑ i, ∑ j, ∑ k, ∑ l, g i j k l :=
  calc ∑ i, ∑ j, ∑ k, ∑ l, g l i j k = ∑ i, ∑ j, ∑ l, ∑ k, g l i j k :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, g l i j k := sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, ∑ k, g l i j k := Finset.sum_comm

/-- `momentSum` is additive over a finite sum of functionals. -/
theorem momentSum_sum {P ι κ : Type*} [Fintype ι] [Fintype κ]
    (Φ : κ → (P → ℝ) → (P → ℝ) → ℝ) (u : ι → ι → P → ℝ) :
    momentSum (fun U V => ∑ m, Φ m U V) u = ∑ m, momentSum (Φ m) u := by
  have hpol : ∀ A A' B B' : P → ℝ,
      pol4 (fun U V => ∑ m, Φ m U V) A A' B B' = ∑ m, pol4 (Φ m) A A' B B' := by
    intro A A' B B'
    simp only [pol4, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [momentSum, hpol]
  symm
  calc ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, pol4 (Φ m) (u i j) (u k l) (u j k) (u l i)
      = ∑ i, ∑ m, ∑ j, ∑ k, ∑ l, pol4 (Φ m) (u i j) (u k l) (u j k) (u l i) :=
        Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ m, ∑ k, ∑ l, pol4 (Φ m) (u i j) (u k l) (u j k) (u l i) :=
        sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ m, ∑ l, pol4 (Φ m) (u i j) (u k l) (u j k) (u l i) :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, ∑ m, pol4 (Φ m) (u i j) (u k l) (u j k) (u l i) :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
          Finset.sum_comm

/-- **Positivity on squares of alternating bilinear forms.**  With `D_ik = Σ_j B(u_ij, u_jk)`,
the functional of `B²` equals `-16 Σ_{i,k} D_ik²`. -/
theorem momentSum_sq {P ι : Type*} [Fintype ι] (B : (P → ℝ) →ₗ[ℝ] (P → ℝ) →ₗ[ℝ] ℝ)
    (hB : ∀ U V, B U V = - B V U) (u : ι → ι → P → ℝ) (ε : ℝ) (hε : ε * ε = 1)
    (hu : ∀ i j, u j i = ε • u i j) :
    momentSum (fun U V => (B U V) ^ 2) u = -16 * ∑ i, ∑ k, (∑ j, B (u i j) (u j k)) ^ 2 := by
  set D : ι → ι → ℝ := fun i k => ∑ j, B (u i j) (u j k) with hD
  have hDanti : ∀ i k, (∑ l, B (u k l) (u l i)) = - D i k := by
    intro i k
    rw [hD, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [hu l k, hu i l]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hε, one_mul, hB]
  have hterm : ∀ i j k l, pol4 (fun U V => (B U V) ^ 2) (u i j) (u k l) (u j k) (u l i) =
      8 * (B (u i j) (u j k) * B (u k l) (u l i)) +
        8 * (B (u l i) (u i j) * B (u j k) (u k l)) := by
    intro i j k l
    simp only [pol4, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hB (u i j) (u l i), hB (u k l) (u j k)]
    ring
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, B (u i j) (u j k) * B (u k l) (u l i)) =
      - ∑ i, ∑ k, D i k ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    have : (∑ j, ∑ l, B (u i j) (u j k) * B (u k l) (u l i)) =
        D i k * ∑ l, B (u k l) (u l i) := by
      rw [hD, Finset.sum_mul_sum]
    rw [this, hDanti]; ring
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l, B (u l i) (u i j) * B (u j k) (u k l)) =
      - ∑ i, ∑ k, D i k ^ 2 := by
    rw [← h1]
    exact sum4_rotate (fun i j k l => B (u i j) (u j k) * B (u k l) (u l i))
  have hsplit : momentSum (fun U V => (B U V) ^ 2) u =
      8 * (∑ i, ∑ j, ∑ k, ∑ l, B (u i j) (u j k) * B (u k l) (u l i)) +
        8 * (∑ i, ∑ j, ∑ k, ∑ l, B (u l i) (u i j) * B (u j k) (u k l)) := by
    simp only [momentSum, hterm, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit, h1, h2]
  ring

/-! ## The obstruction -/

/-- **Generic moment obstruction.**  Let `p` be a polynomial in two families of variables
indexed by `P`, whose values `Φ U V = p(x := U, y := V)` vanish at `U = 0`, at `V = 0` and at
`U = V`.  If for some family `u` with `u j i = ε • u i j` (`ε² = 1`) the functional
`momentSum Φ u` is positive, then `p` is not a sum of squares of quadratic forms. -/
theorem not_isSumSqHomQuad_of_moment {P ι : Type*} [Fintype P] [Fintype ι]
    (p : MvPolynomial (CoordFamily × P) ℝ) (Φ : (P → ℝ) → (P → ℝ) → ℝ)
    (hp : ∀ U V, eval (pt U V) p = Φ U V)
    (hx : ∀ U, Φ U 0 = 0) (hy : ∀ V, Φ 0 V = 0) (hd : ∀ U, Φ U U = 0)
    (u : ι → ι → P → ℝ) (ε : ℝ) (hε : ε * ε = 1) (hu : ∀ i j, u j i = ε • u i j)
    (hpos : 0 < momentSum Φ u) : ¬ IsSumSqHomQuad p := by
  rintro ⟨N, q, hq, rfl⟩
  choose c hc using fun j => exists_quadForm (hq j)
  have hΦ : ∀ U V, Φ U V = ∑ j, (quadF (c j) (pt U V)) ^ 2 := by
    intro U V
    rw [← hp]
    simp only [map_sum, map_pow, hc, quadF]
  have hzero : ∀ U V, Φ U V = 0 → ∀ j, quadF (c j) (pt U V) = 0 := by
    intro U V h j
    rw [hΦ] at h
    exact pow_eq_zero_iff two_ne_zero |>.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h j (mem_univ _))
  have hxj : ∀ j U, quadF (c j) (pt U 0) = 0 := fun j U => hzero U 0 (hx U) j
  have hyj : ∀ j V, quadF (c j) (pt 0 V) = 0 := fun j V => hzero 0 V (hy V) j
  have hdj : ∀ j U, quadF (c j) (pt U U) = 0 := fun j U => hzero U U (hd U) j
  have hΦ' : Φ = fun U V => ∑ j, (bil (c j) U V) ^ 2 := by
    funext U V
    rw [hΦ]
    exact sum_congr rfl fun j _ => by rw [quadF_pt_eq_bil (c j) (hxj j) (hyj j)]
  rw [hΦ', momentSum_sum] at hpos
  have hle : ∀ j, momentSum (fun U V => (bil (c j) U V) ^ 2) u ≤ 0 := by
    intro j
    rw [momentSum_sq (bil (c j)) (bil_alt (c j) (hxj j) (hyj j) (hdj j)) u ε hε hu]
    have : 0 ≤ ∑ i, ∑ k, (∑ l, bil (c j) (u i l) (u l k)) ^ 2 :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have := Finset.sum_nonpos fun j (_ : j ∈ (univ : Finset (Fin N))) => hle j
  linarith

end

end ToeplitzSOS.General
