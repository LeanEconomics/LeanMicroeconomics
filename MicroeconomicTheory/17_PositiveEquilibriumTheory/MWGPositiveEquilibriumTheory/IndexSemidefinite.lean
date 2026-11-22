/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.UniquenessInstances
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue

/-!
# Index `+1` under negative semidefiniteness; dominant diagonals (MWG Exercises 17.F.11-17.F.12)

* A negative semidefinite (`v·Mv ≤ 0` for all `v`, not necessarily symmetric) nonsingular
  `m × m` matrix has `sign |M| = (-1)^m` (`isd_det_sign_of_nsd`): the determinant of
  `sM - (1 - s)I` never vanishes on `[0, 1]` (it is negative definite for `s < 1`), and equals
  `(-1)^m` at `s = 0` (the homotopy of the proof of Theorem M.D.5(ii)).
* **Exercise 17.F.11** (`exercise_17_F_11`, matrix form `isd_minor_sign`): at an equilibrium with
  `rank Dz(p) = L - 1` and `Dz(p)` negative semidefinite, every principal `(L - 1) × (L - 1)`
  minor (delete row and column `ℓ`) has sign `(-1)^{L-1}`; nonsingularity is footnote 14 /
  Theorem M.D.4(i) (`footnote_17_14`). Hence the index is `+1` (`exercise_17_F_11_index`).
  Instance of the hypotheses: `isd_instance`.
* **Definition M.D.2** (`NegDominantDiagonal`). **Exercise 17.F.12** (`exercise_17_F_12`, matrix
  form `isd_gs_minor`): with the gross substitute sign pattern and `Dz(p)p = 0`,
  `pᵀDz(p) = 0`, every principal `(L - 1) × (L - 1)` submatrix has a negative dominant diagonal
  (weights `p`) and is negative definite.
* **Footnote 51** (p. 617) / Theorem M.D.4(ii)-(iii): when `Ap = 0` and `pᵀA = 0` (`p ≫ 0`), the
  submatrix obtained by deleting row and column `k` is negative definite iff `x·Ax < 0` for every
  `x` not proportional to `p` (`isd_nd_iff`); so negative definiteness does not depend on which
  commodity is the numeraire (`footnote_17_51`).
-/

namespace MWG.PositiveEquilibriumTheory

variable {n : ℕ}

/-! ### Negative semidefinite nonsingular matrices -/

/-- `v·v > 0` for `v ≠ 0`. -/
theorem isd_dot_self_pos {m : ℕ} {v : Fin m → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have h1 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h2 : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.1 h)
  exact lt_of_le_of_ne h1 (Ne.symm h2)

/-- A negative semidefinite matrix (`v·Mv ≤ 0` for every `v`; `M` need not be symmetric) that
is nonsingular has `(-1)^m |M| > 0` (MWG, Section M.D; the homotopy of Theorem M.D.5(ii)). -/
theorem isd_det_sign_of_nsd {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ v, v ⬝ᵥ A.mulVec v ≤ 0) (hdet : A.det ≠ 0) : 0 < (-1) ^ m * A.det := by
  set M : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun s => s • A - (1 - s) • (1 : Matrix (Fin m) (Fin m) ℝ) with hM
  set f : ℝ → ℝ := fun s => (-1) ^ m * (M s).det with hf
  have hcont : Continuous f := by
    refine continuous_const.mul (Continuous.matrix_det ?_)
    simp only [hM]
    fun_prop
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≠ 0 := by
    intro s hs
    have hpow : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · subst h1
      simpa [hf, hM, hpow] using hdet
    · intro h0
      have hdet0 : (M s).det = 0 := (mul_eq_zero.1 h0).resolve_left hpow
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
      have hq : v ⬝ᵥ (M s).mulVec v = s * (v ⬝ᵥ A.mulVec v) - (1 - s) * (v ⬝ᵥ v) := by
        simp [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
      rw [hv, dotProduct_zero] at hq
      have hvv := isd_dot_self_pos hv0
      nlinarith [hA v, hs.1, mul_nonneg hs.1 (neg_nonneg.2 (hA v))]
  have h0 : f 0 = 1 := by
    have : M 0 = -1 := by simp [hM]
    simp only [hf, this, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one]
    rw [← mul_pow]
    norm_num
  have h1 : f 1 = (-1) ^ m * A.det := by simp [hf, hM]
  by_contra hneg
  rw [not_lt, ← h1] at hneg
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f 1) (f 0) by rw [h0]; exact ⟨hneg, zero_le_one⟩)
  exact hne s hs hfs

/-- The quadratic form of the submatrix obtained by deleting row and column `k` is the quadratic
form of `A` at the vector completed by a `0` in coordinate `k`. -/
theorem isd_quad_submatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : Fin (n + 1))
    (w : Fin n → ℝ) :
    w ⬝ᵥ (A.submatrix k.succAbove k.succAbove).mulVec w =
      Fin.insertNth k 0 w ⬝ᵥ A.mulVec (Fin.insertNth k 0 w) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same, zero_mul, zero_add, Fin.insertNth_apply_succAbove]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succAbove _ k]
  simp

/-- **Exercise 17.F.11**, matrix form (MWG, p. 646). Let `A` be `L × L` (`L = n + 1`) with
`A p = 0`, `pᵀ A = 0` for some `p ≫ 0`, `rank A = L - 1` and `A` negative semidefinite. Then for
every `ℓ` the matrix obtained by deleting row and column `ℓ` has determinant of sign
`(-1)^{L-1}`. -/
theorem isd_minor_sign {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p : Fin (n + 1) → ℝ}
    (hp : ∀ l, 0 < p l) (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0) (hrank : A.rank = n)
    (hnsd : ∀ v, v ⬝ᵥ A.mulVec v ≤ 0) (k : Fin (n + 1)) :
    0 < (-1) ^ n * (A.submatrix k.succAbove k.succAbove).det :=
  isd_det_sign_of_nsd _ (fun w => by rw [isd_quad_submatrix]; exact hnsd _)
    ((footnote_17_14 hp hAp hpA hrank).1 k)

/-- In coordinates, `Dz(p) p = 0` and `pᵀ Dz(p) = 0` at an equilibrium. -/
theorem isd_mat_eqm {L : ℕ} {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {p : Fin L → ℝ} (hp : IsEqmPrice z p)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p) :
    (LinearMap.toMatrix' (D : (Fin L → ℝ) →ₗ[ℝ] (Fin L → ℝ))).mulVec p = 0 ∧
      Matrix.vecMul p (LinearMap.toMatrix' (D : (Fin L → ℝ) →ₗ[ℝ] (Fin L → ℝ))) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    exact euler_fderiv hH hp.1 hd
  · funext k
    have h := walras_fderiv hW hp.1 hd (Pi.single k 1)
    rw [hp.2, dotProduct_zero, zero_add] at h
    simp only [Matrix.vecMul, dotProduct, LinearMap.toMatrix'_apply, Pi.zero_apply]
    simpa [dotProduct] using h

/-- **Exercise 17.F.11** (MWG, p. 646). If `z(p) = 0`, `rank Dz(p) = L - 1` and `Dz(p)` is
negative semidefinite, then for any `ℓ` the `(L - 1) × (L - 1)` matrix obtained from `Dz(p)` by
deleting the `ℓ`th row and column has a determinant of sign `(-1)^{L-1}`. (`z` is an excess
demand function: homogeneous of degree zero, Walras' law; it is differentiable at `p`.) -/
theorem exercise_17_F_11 {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {p : Fin (n + 1) → ℝ} (hp : IsEqmPrice z p)
    {D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hd : HasFDerivAt z D p)
    (hrank : (LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))).rank = n)
    (hnsd : ∀ v, v ⬝ᵥ D v ≤ 0) (k : Fin (n + 1)) :
    0 < (-1) ^ n * ((LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ]
      (Fin (n + 1) → ℝ))).submatrix k.succAbove k.succAbove).det := by
  obtain ⟨hAp, hpA⟩ := isd_mat_eqm hH hW hp hd
  exact isd_minor_sign hp.1 hAp hpA hrank
    (fun v => by rw [LinearMap.toMatrix'_mulVec]; exact hnsd v) k

/-- `(-1)^n d > 0` gives `(-1)^n sign d = 1`. -/
theorem isd_index_of_pos {d : ℝ} (h : 0 < (-1) ^ n * d) :
    (-1 : ℤ) ^ n * ((SignType.sign d : SignType) : ℤ) = 1 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul] at h ⊢
    simp [sign_pos h]
  · rw [ho.neg_one_pow] at h ⊢
    have hd : d < 0 := by linarith
    simp [sign_neg hd]

/-- **Exercise 17.F.11** and p. 615 (MWG). At a normalized equilibrium `(p̂, 1)` with
`rank Dz(p) = L - 1` and `Dz(p)` negative semidefinite, the equilibrium is regular and its index
is `+1`. -/
theorem exercise_17_F_11_index {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hH : EDHomogeneous z) (hW : EDWalrasLaw z) {q : Fin n → ℝ} (heq : IsNormEqm z q)
    {D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hd : HasFDerivAt z D (normPrice q))
    (hrank : (LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))).rank = n)
    (hnsd : ∀ v, v ⬝ᵥ D v ≤ 0) : IsRegularEqm z q ∧ eqmIndex z q = 1 := by
  refine ⟨isRegularEqm_of_rank hH hW heq hd hrank, ?_⟩
  obtain ⟨hD, hmat⟩ := normED_hasFDerivAt hd
  have h := exercise_17_F_11 hH hW heq hd hrank hnsd (Fin.last n)
  rw [← hmat] at h
  rw [eqmIndex, hD.fderiv, ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  exact isd_index_of_pos h

/-- Instance of the hypotheses of Exercise 17.F.11 (matrix form):
`A = [[-1, 1], [1, -1]]`, `p = (1, 1)`: `Ap = 0`, `pᵀA = 0`, `rank A = 1`, `A` negative
semidefinite; the `1 × 1` minors are `-1`. -/
theorem isd_instance :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, -1]
    A.mulVec ![1, 1] = 0 ∧ Matrix.vecMul ![1, 1] A = 0 ∧ A.rank = 1 ∧
      (∀ v, v ⬝ᵥ A.mulVec v ≤ 0) ∧ ∀ k : Fin 2, 0 < (-1) ^ 1 * (A.submatrix k.succAbove
        k.succAbove).det := by
  intro A
  have hAp : A.mulVec ![1, 1] = 0 := by
    funext i; fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hpA : Matrix.vecMul ![1, 1] A = 0 := by
    funext i; fin_cases i <;> simp [A, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hA : A = Matrix.vecMulVec ![1, -1] ![-1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  have hrank : A.rank = 1 := by
    rw [hA]
    exact rank_wealthEffectMatrix_eq_one (by intro h; simpa using congrFun h 0)
      (by intro h; simpa using congrFun h 0)
  have hnsd : ∀ v, v ⬝ᵥ A.mulVec v ≤ 0 := by
    intro v
    have : v ⬝ᵥ A.mulVec v = -(v 0 - v 1) ^ 2 := by
      simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
    rw [this]; nlinarith [sq_nonneg (v 0 - v 1)]
  exact ⟨hAp, hpA, hrank, hnsd, isd_minor_sign (p := ![1, 1])
    (fun l => by fin_cases l <;> simp) hAp hpA hrank hnsd⟩

/-! ### Exercise 17.F.12: dominant diagonals -/

/-- **Definition M.D.2** (MWG, p. 939), with negative diagonal. The `m × m` matrix `M` has a
negative dominant diagonal: `mₖₖ < 0` for every `k`, and there are weights `p ≫ 0` with
`|pₖ mₖₖ| > ∑_{j ≠ k} |pⱼ mₖⱼ|` for every `k`. -/
def NegDominantDiagonal {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (∀ k, M k k < 0) ∧ ∃ p : Fin m → ℝ, (∀ k, 0 < p k) ∧
    ∀ k, ∑ j ∈ Finset.univ.erase k, |p j * M k j| < |p k * M k k|

/-- The quadratic form is unchanged by adding multiples of `p` when `Ap = 0` and `pᵀA = 0`. -/
theorem isd_quad_shift {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} {p : Fin m → ℝ}
    (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0) (x : Fin m → ℝ) (c : ℝ) :
    (x + c • p) ⬝ᵥ A.mulVec (x + c • p) = x ⬝ᵥ A.mulVec x := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAp, smul_zero, add_zero, add_dotProduct,
    smul_dotProduct, Matrix.dotProduct_mulVec p, hpA, zero_dotProduct, smul_zero, add_zero]

/-- The gross substitute sign pattern with `Ap = 0`, `pᵀA = 0`, `p ≫ 0` makes `x·Ax < 0` for every
`x` not proportional to `p` (the matrix form of Proposition 17.F.4). -/
theorem isd_gs_quad_neg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} {p : Fin m → ℝ}
    (hp : ∀ l, 0 < p l) (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0)
    (hsign : ∀ k l, k ≠ l → 0 < A k l) {x : Fin m → ℝ} (hprop : ∀ α : ℝ, x ≠ α • p) :
    x ⬝ᵥ A.mulVec x < 0 := by
  have hrow : ∀ k, ∑ l, A k l * p l = 0 := fun k => by
    simpa [Matrix.mulVec, dotProduct] using congrFun hAp k
  have hcol : ∀ l, ∑ k, p k * A k l = 0 := fun l => by
    simpa [Matrix.vecMul, dotProduct] using congrFun hpA l
  have hq : x ⬝ᵥ A.mulVec x = ∑ k, ∑ l, x k * A k l * x l := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hq, gs_quad_identity (fun k l => A k l) (fun k => (hp k).ne') hrow hcol]
  rcases isEmpty_or_nonempty (Fin m) with hL | ⟨⟨k0⟩⟩
  · exact absurd (funext fun l => isEmptyElim l) (hprop 0)
  obtain ⟨k1, hk1⟩ : ∃ k, x k / p k ≠ x k0 / p k0 := by
    by_contra hcon
    push Not at hcon
    apply hprop (x k0 / p k0)
    funext k
    have := hcon k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← this]
    field_simp [(hp k).ne']
  have hk10 : k1 ≠ k0 := fun h => hk1 (by rw [h])
  have hnn : ∀ k l, 0 ≤ A k l * p k * p l * (x k / p k - x l / p l) ^ 2 := fun k l => by
    by_cases hkl : k = l
    · subst hkl; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hsign k l hkl).le (hp k).le) (hp l).le)
        (sq_nonneg _)
  have hpos : 0 < ∑ k, ∑ l, A k l * p k * p l * (x k / p k - x l / p l) ^ 2 := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      fun l _ => hnn k l) (Finset.mem_univ k1))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun l _ => hnn k1 l) (Finset.mem_univ k0))
    exact mul_pos (mul_pos (mul_pos (hsign k1 k0 hk10) (hp k1)) (hp k0))
      (sq_pos_of_ne_zero (sub_ne_zero.2 hk1))
  linarith

/-- A vector with `xₖ = 0`, `x ≠ 0`, is not proportional to `p ≫ 0`. -/
theorem isd_not_prop {p : Fin (n + 1) → ℝ} (hp : ∀ l, 0 < p l) (k : Fin (n + 1))
    {w : Fin n → ℝ} (hw : w ≠ 0) : ∀ α : ℝ, Fin.insertNth k 0 w ≠ α • p := by
  intro α h
  have hk := congrFun h k
  simp only [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul] at hk
  have hα : α = 0 := (mul_eq_zero.1 hk.symm).resolve_right (hp k).ne'
  apply hw
  funext j
  have := congrFun h (k.succAbove j)
  simpa [hα] using this

/-- **Exercise 17.F.12**, matrix form (MWG, p. 646). If the `L × L` matrix `A` has the gross
substitute sign pattern (positive off-diagonal entries), `A p = 0` and `pᵀ A = 0` for some
`p ≫ 0`, then for every `ℓ` the matrix obtained by deleting row and column `ℓ` has a negative
dominant diagonal (with weights `p` restricted) and is negative definite. -/
theorem isd_gs_minor {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p : Fin (n + 1) → ℝ}
    (hp : ∀ l, 0 < p l) (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0)
    (hsign : ∀ k l, k ≠ l → 0 < A k l) (ℓ : Fin (n + 1)) :
    NegDominantDiagonal (A.submatrix ℓ.succAbove ℓ.succAbove) ∧
      ∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ (A.submatrix ℓ.succAbove ℓ.succAbove).mulVec w < 0 := by
  have hrow : ∀ i : Fin n, A (ℓ.succAbove i) ℓ * p ℓ +
      (p (ℓ.succAbove i) * A (ℓ.succAbove i) (ℓ.succAbove i) +
        ∑ j ∈ Finset.univ.erase i, p (ℓ.succAbove j) * A (ℓ.succAbove i) (ℓ.succAbove j)) = 0 := by
    intro i
    have h := congrFun hAp (ℓ.succAbove i)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h
    rw [Fin.sum_univ_succAbove _ ℓ, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    linarith [mul_comm (A (ℓ.succAbove i) (ℓ.succAbove i)) (p (ℓ.succAbove i)),
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ.erase i) =>
        mul_comm (A (ℓ.succAbove i) (ℓ.succAbove j)) (p (ℓ.succAbove j))]
  have hoff : ∀ i j : Fin n, j ≠ i → 0 < A (ℓ.succAbove i) (ℓ.succAbove j) :=
    fun i j hji => hsign _ _ (fun h => hji (Fin.succAbove_right_injective h).symm)
  have hpos : ∀ i : Fin n, 0 < A (ℓ.succAbove i) ℓ * p ℓ :=
    fun i => mul_pos (hsign _ _ (Fin.succAbove_ne ℓ i)) (hp ℓ)
  have hsum : ∀ i : Fin n,
      0 ≤ ∑ j ∈ Finset.univ.erase i, p (ℓ.succAbove j) * A (ℓ.succAbove i) (ℓ.succAbove j) :=
    fun i => Finset.sum_nonneg fun j hj =>
      mul_nonneg (hp _).le (hoff i j (Finset.ne_of_mem_erase hj)).le
  refine ⟨⟨fun i => ?_, fun j => p (ℓ.succAbove j), fun j => hp _, fun i => ?_⟩, fun w hw => ?_⟩
  · have h := hrow i
    have := hp (ℓ.succAbove i)
    simp only [Matrix.submatrix_apply]
    nlinarith [hpos i, hsum i]
  · simp only [Matrix.submatrix_apply]
    have habs : ∑ j ∈ Finset.univ.erase i, |p (ℓ.succAbove j) * A (ℓ.succAbove i) (ℓ.succAbove j)|
        = ∑ j ∈ Finset.univ.erase i, p (ℓ.succAbove j) * A (ℓ.succAbove i) (ℓ.succAbove j) :=
      Finset.sum_congr rfl fun j hj => abs_of_nonneg
        (mul_nonneg (hp _).le (hoff i j (Finset.ne_of_mem_erase hj)).le)
    have hdiag : p (ℓ.succAbove i) * A (ℓ.succAbove i) (ℓ.succAbove i) < 0 := by
      linarith [hrow i, hpos i, hsum i]
    rw [habs, abs_of_neg hdiag]
    linarith [hrow i, hpos i]
  · rw [isd_quad_submatrix]
    exact isd_gs_quad_neg hp hAp hpA hsign (isd_not_prop hp ℓ hw)

/-- **Exercise 17.F.12** (MWG, p. 646). If `z(p) = 0` and `Dz(p)` has the gross substitute sign
pattern, then for every `ℓ` the `(L - 1) × (L - 1)` matrix obtained from `Dz(p)` by deleting the
`ℓ`th row and column has a negative dominant diagonal and is negative definite. -/
theorem exercise_17_F_12 {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {p : Fin (n + 1) → ℝ} (hp : IsEqmPrice z p)
    {D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hd : HasFDerivAt z D p)
    (hsign : ∀ k l, k ≠ l → 0 < D (Pi.single l 1) k) (ℓ : Fin (n + 1)) :
    NegDominantDiagonal ((LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ]
        (Fin (n + 1) → ℝ))).submatrix ℓ.succAbove ℓ.succAbove) ∧
      ∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ ((LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ]
        (Fin (n + 1) → ℝ))).submatrix ℓ.succAbove ℓ.succAbove).mulVec w < 0 := by
  obtain ⟨hAp, hpA⟩ := isd_mat_eqm hH hW hp hd
  exact isd_gs_minor hp.1 hAp hpA (fun k l hkl => by
    rw [LinearMap.toMatrix'_apply]; exact hsign k l hkl) ℓ

/-! ### Footnote 51 and Theorem M.D.4 -/

/-- Every `x` is `insertNth k (xₖ) (x ∘ succAbove k)`. -/
theorem isd_eq_insertNth (x : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    x = Fin.insertNth k (x k) (fun j => x (k.succAbove j)) := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
  · simp
  · simp

/-- **Theorem M.D.4(ii)-(iii)** (MWG, p. 939). If `A p = 0` and `pᵀA = 0` with `p ≫ 0`, the matrix
obtained by deleting row and column `k` is negative definite iff `x·Ax < 0` for every `x` not
proportional to `p`. -/
theorem isd_nd_iff {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p : Fin (n + 1) → ℝ}
    (hp : ∀ l, 0 < p l) (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0) (k : Fin (n + 1)) :
    (∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ (A.submatrix k.succAbove k.succAbove).mulVec w < 0) ↔
      ∀ x : Fin (n + 1) → ℝ, (∀ α : ℝ, x ≠ α • p) → x ⬝ᵥ A.mulVec x < 0 := by
  constructor
  · intro h x hx
    set y := x + (-(x k / p k)) • p with hy
    have hyk : y k = 0 := by
      simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [(hp k).ne']
      ring
    have hw : (fun j => y (k.succAbove j)) ≠ 0 := by
      intro h0
      apply hx (x k / p k)
      have hy0 : y = 0 := by
        rw [isd_eq_insertNth y k, hyk, h0]
        funext i
        rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩ <;> simp
      funext i
      have := congrFun hy0 i
      simp only [hy, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Pi.smul_apply, smul_eq_mul]
      linarith
    have hyeq : Fin.insertNth k 0 (fun j => y (k.succAbove j)) = y := by
      rw [← hyk]; exact (isd_eq_insertNth y k).symm
    have := h _ hw
    rw [isd_quad_submatrix, hyeq, hy, isd_quad_shift hAp hpA] at this
    exact this
  · intro h w hw
    rw [isd_quad_submatrix]
    exact h _ (isd_not_prop hp k hw)

/-- **Footnote 51** (MWG, p. 617). The negative definiteness of `D_p ẑ` does not depend on which
commodity has been labeled `L`: if `Ap = 0` and `pᵀA = 0` (`p ≫ 0`), the matrix obtained by
deleting row and column `k` is negative definite iff the one obtained by deleting row and
column `k'` is. -/
theorem footnote_17_51 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p : Fin (n + 1) → ℝ}
    (hp : ∀ l, 0 < p l) (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0) (k k' : Fin (n + 1)) :
    (∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ (A.submatrix k.succAbove k.succAbove).mulVec w < 0) ↔
      ∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ (A.submatrix k'.succAbove k'.succAbove).mulVec w < 0 := by
  rw [isd_nd_iff hp hAp hpA k, isd_nd_iff hp hAp hpA k']

end MWG.PositiveEquilibriumTheory
