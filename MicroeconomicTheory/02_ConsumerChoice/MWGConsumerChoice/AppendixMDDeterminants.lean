/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDBasic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue

/-!
# Determinantal tests for negative (semi)definiteness

MWG, Mathematical Appendix, Theorem M.D.2 (p. 936) with footnote 8, and Exercise 2.F.9(a)
(p. 38).

For an `N × N` matrix `M`, `ₜMₜ` is the leading `r × r` submatrix (first `r` rows and
columns), and `M^π` is `M` with rows and columns permuted by `π`.

* Principal submatrices of negative (semi)definite matrices are negative (semi)definite.
* A (possibly nonsymmetric) positive definite matrix has positive determinant (proved by
  deforming it to the identity through positive definite matrices).
* Theorem M.D.2(iii): a negative definite matrix has `(-1)^r |ₜM^πₜ| > 0` for every `r` and
  every permutation `π`; equivalently `-M` is a P-matrix (footnote 8).
* Theorem M.D.2(i) (Sylvester's criterion): a symmetric `M` is negative definite iff
  `(-1)^r |ₜMₜ| > 0` for `r = 1, …, N`. The book does not carry out the sufficiency proof; it is
  proved here by induction with the Schur complement.
* Exercise 2.F.9(a): definiteness of `A` and of `A + Aᵀ` agree, the leading-minor condition is
  necessary in the nonsymmetric case, and it is not sufficient (`A = [[-1, 4], [0, -1]]`).
-/

namespace MWG.ConsumerChoice

open Matrix

/-- Summing `y·g` for the extension by zero `y` of `z` along an injection `e` gives `∑ zᵢ g(eᵢ)`.
-/
theorem sum_extend_mul {m n : Type*} [Fintype m] [Fintype n] {e : m → n}
    (he : Function.Injective e) (z : m → ℝ) (g : n → ℝ) :
    ∑ j, Function.extend e z 0 j * g j = ∑ i, z i * g (e i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) (fun j _ hj => ?_)]
  · rw [Finset.sum_image fun a _ b _ h => he h]
    exact Finset.sum_congr rfl fun i _ => by rw [he.extend_apply]
  · have : ¬ ∃ a, e a = j := fun ⟨a, ha⟩ => hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, zero_mul]

/-- The quadratic form of a principal submatrix is the quadratic form of `M` at the extension by
zero. -/
theorem quadratic_submatrix {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix n n ℝ) {e : m → n} (he : Function.Injective e) (z : m → ℝ) :
    z ⬝ᵥ (M.submatrix e e).mulVec z =
      Function.extend e z 0 ⬝ᵥ M.mulVec (Function.extend e z 0) := by
  simp only [dotProduct, mulVec]
  rw [sum_extend_mul he]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [show (∑ x, M (e i) x * Function.extend e z 0 x) =
      ∑ x, Function.extend e z 0 x * M (e i) x from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, sum_extend_mul he]
  exact Finset.sum_congr rfl fun k _ => by simp [submatrix_apply, mul_comm]

/-- **Section M.D** (MWG, p. 937). Principal submatrices of a negative definite matrix are
negative definite. -/
theorem NegDef.submatrix {m n : Type*} [Fintype m] [Fintype n] {M : Matrix n n ℝ}
    (h : NegDef M) {e : m → n} (he : Function.Injective e) : NegDef (M.submatrix e e) := by
  classical
  intro z hz
  rw [quadratic_submatrix M he]
  apply h
  intro h0
  apply hz
  funext i
  have := congrFun h0 (e i)
  rwa [he.extend_apply] at this

/-- Principal submatrices of a negative semidefinite matrix are negative semidefinite. -/
theorem NegSemidef.submatrix {m n : Type*} [Fintype m] [Fintype n] {M : Matrix n n ℝ}
    (h : NegSemidef M) {e : m → n} (he : Function.Injective e) :
    NegSemidef (M.submatrix e e) := by
  classical
  intro z
  rw [quadratic_submatrix M he]
  exact h _

/-- A matrix positive definite in MWG's sense is nonsingular. -/
theorem PosDefMWG.det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ}
    (h : PosDefMWG B) : B.det ≠ 0 := by
  have := ((posDefMWG_iff_neg B).mp h).det_ne_zero
  rw [Matrix.det_neg] at this
  intro h0
  rw [h0, mul_zero] at this
  exact this rfl

/-- **Section M.D** (MWG, p. 937). A (possibly nonsymmetric) positive definite matrix has
positive determinant: the path `t ↦ (1 - t)I + tB` stays positive definite, hence nonsingular,
and starts at `det I = 1`. -/
theorem PosDefMWG.det_pos {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ}
    (h : PosDefMWG B) : 0 < B.det := by
  set f : ℝ → ℝ := fun t => ((1 - t) • (1 : Matrix n n ℝ) + t • B).det with hf
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht
    apply PosDefMWG.det_ne_zero
    intro z hz
    rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hzz := dotProduct_self_pos_of_ne_zero hz
    have hzB := h z hz
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]; simp [hzz]
    · nlinarith [ht.2, mul_pos h0 hzB]
  have h0 : f 0 = 1 := by simp [hf]
  have h1 : f 1 = B.det := by simp [hf]
  by_contra hc
  push Not at hc
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by rw [h1]; exact hc, by rw [h0]; norm_num⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn hmem
  exact hne t ht hft

/-- **Section M.D** (MWG, p. 936). The leading principal `r × r` submatrix `ₜMₜ`. -/
def leadingMinorMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (r : ℕ) (h : r ≤ N) :
    Matrix (Fin r) (Fin r) ℝ :=
  M.submatrix (Fin.castLE h) (Fin.castLE h)

/-- **Section M.D** (MWG, p. 936). `M^π`: rows and columns permuted by `π`. -/
def permuteMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (π : Equiv.Perm (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  M.submatrix π π

/-- **Theorem M.D.2(iii)** (MWG, p. 936). If `M` is negative definite (not necessarily
symmetric), then `(-1)^r |ₜM^πₜ| > 0` for every `r = 1, …, N` and every permutation `π`. -/
theorem theorem_M_D_2_iii {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : NegDef M) (r : ℕ)
    (h : r ≤ N) (π : Equiv.Perm (Fin N)) :
    0 < (-1) ^ r * (leadingMinorMatrix (permuteMatrix M π) r h).det := by
  have hsub : NegDef (leadingMinorMatrix (permuteMatrix M π) r h) :=
    hM.submatrix (e := π ∘ Fin.castLE h) (π.injective.comp (Fin.castLE_injective h))
  have hpos := ((posDefMWG_iff_neg _).mpr (by rwa [neg_neg])).det_pos
  rw [det_neg_eq_pow] at hpos
  exact hpos

/-- **Footnote 8** (MWG, p. 936). A P-matrix: every principal minor `|ₜM^πₜ|` is positive. -/
def IsPMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), 1 ≤ r →
    0 < (leadingMinorMatrix (permuteMatrix M π) r h).det

/-- **Footnote 8** (MWG, p. 936). If `M` is negative definite, `-M` is a P-matrix. -/
theorem negDef_neg_isPMatrix {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : NegDef M) :
    IsPMatrix (-M) := by
  intro r h π _
  have := theorem_M_D_2_iii hM r h π
  have e : leadingMinorMatrix (permuteMatrix (-M) π) r h =
      -leadingMinorMatrix (permuteMatrix M π) r h := rfl
  rw [e, det_neg_eq_pow]
  exact this

/-! ### Sylvester's criterion -/

/-- The leading minors of the top-left `N × N` block are leading minors of `A`. -/
theorem leadingMinorMatrix_castSucc {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (r : ℕ)
    (h : r ≤ N) :
    leadingMinorMatrix (A.submatrix Fin.castSucc Fin.castSucc) r h =
      leadingMinorMatrix A r (h.trans (Nat.le_succ N)) := rfl

/-- Splitting the quadratic form of a symmetric `(N+1) × (N+1)` matrix along the last
coordinate: `z·Az = y·A'y + 2s (b·y) + c s²`. -/
theorem quadratic_castSucc_split {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsSymm) (z : Fin (N + 1) → ℝ) :
    z ⬝ᵥ A *ᵥ z = (fun i : Fin N => z i.castSucc) ⬝ᵥ
        (A.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun i : Fin N => z i.castSucc) +
      2 * z (Fin.last N) *
        ((fun i : Fin N => A i.castSucc (Fin.last N)) ⬝ᵥ (fun i : Fin N => z i.castSucc)) +
      A (Fin.last N) (Fin.last N) * z (Fin.last N) ^ 2 := by
  have hsym : ∀ i : Fin N, A (Fin.last N) i.castSucc = A i.castSucc (Fin.last N) :=
    fun i => hA.apply i.castSucc (Fin.last N)
  simp only [dotProduct, mulVec, Fin.sum_univ_castSucc, submatrix_apply, mul_add,
    Finset.sum_add_distrib, hsym]
  have h2 : ∑ i : Fin N, z i.castSucc * (A i.castSucc (Fin.last N) * z (Fin.last N)) =
      z (Fin.last N) * ∑ i : Fin N, A i.castSucc (Fin.last N) * z i.castSucc := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  ring

/-- Sylvester's criterion (positive definite form): a symmetric matrix whose leading principal
minors are all positive is positive definite. -/
theorem sylvester_posDef : ∀ {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}, A.IsSymm →
    (∀ r (h : r ≤ N), 1 ≤ r → 0 < (leadingMinorMatrix A r h).det) → PosDefMWG A
  | 0, A, _, _ => fun z hz => absurd (Subsingleton.elim z 0) hz
  | N + 1, A, hA, hmin => by
    set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'
    have hA'symm : A'.IsSymm := by
      ext i j
      simp only [transpose_apply, hA', submatrix_apply]
      exact hA.apply _ _
    have hA'pd : PosDefMWG A' := sylvester_posDef hA'symm (fun r h hr => by
      rw [leadingMinorMatrix_castSucc]
      exact hmin r _ hr)
    have hdetA' : A'.det ≠ 0 := hA'pd.det_ne_zero
    have hUA' : IsUnit A'.det := isUnit_iff_ne_zero.mpr hdetA'
    set b : Fin N → ℝ := fun i => A i.castSucc (Fin.last N) with hb
    set c : ℝ := A (Fin.last N) (Fin.last N) with hc
    set u : Fin N → ℝ := A'⁻¹ *ᵥ b with hu
    have hA'u : A' *ᵥ u = b := by rw [hu, mulVec_mulVec, mul_nonsing_inv _ hUA', one_mulVec]
    -- the determinant factorises through the Schur complement
    have hdet : A.det = A'.det * (c - b ⬝ᵥ u) := by
      let _inst : Invertible A' := A'.invertibleOfIsUnitDet hUA'
      have h11 : (A.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = A' := by
        ext i j
        rfl
      rw [← det_submatrix_equiv_self finSumFinEquiv A,
        ← fromBlocks_toBlocks (A.submatrix finSumFinEquiv finSumFinEquiv), h11,
        det_fromBlocks₁₁, invOf_eq_nonsing_inv]
      congr 1
      rw [det_unique]
      have hl : Fin.natAdd N (default : Fin 1) = Fin.last N := by ext; simp
      simp only [toBlocks₂₂, toBlocks₂₁, toBlocks₁₂, Matrix.sub_apply, Matrix.mul_apply,
        of_apply, submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, hl]
      rw [hu]
      simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have e1 : A (Fin.last N) (Fin.castAdd 1 i) = b i := hA.apply _ _
      have e2 : A (Fin.castAdd 1 j) (Fin.last N) = b j := rfl
      rw [e1, e2]
      ring
    have hschur : 0 < c - b ⬝ᵥ u := by
      have hApos := hmin (N + 1) le_rfl (Nat.le_add_left 1 N)
      have hA'pos : 0 < A'.det := by
        have := hmin N (Nat.le_succ N)
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · subst h0
          simp
        · exact this h0
      have e : leadingMinorMatrix A (N + 1) le_rfl = A := by
        ext i j
        rfl
      rw [e, hdet] at hApos
      exact pos_of_mul_pos_right hApos hA'pos.le
    -- the quadratic form splits as `(y + s u)·A'(y + s u) + s²(c - b·u)`
    intro z hz
    set y : Fin N → ℝ := fun i => z i.castSucc with hy
    set s : ℝ := z (Fin.last N) with hs
    have hquad : z ⬝ᵥ A *ᵥ z = y ⬝ᵥ A' *ᵥ y + 2 * s * (b ⬝ᵥ y) + c * s ^ 2 :=
      quadratic_castSucc_split A hA z
    have hsplit : z ⬝ᵥ A *ᵥ z =
        (y + s • u) ⬝ᵥ A' *ᵥ (y + s • u) + s ^ 2 * (c - b ⬝ᵥ u) := by
      have hA'sym : ∀ v w : Fin N → ℝ, v ⬝ᵥ A' *ᵥ w = w ⬝ᵥ A' *ᵥ v := by
        intro v w
        rw [dotProduct_mulVec, ← mulVec_transpose, hA'symm.eq, dotProduct_comm]
      have e1 : (y + s • u) ⬝ᵥ A' *ᵥ (y + s • u) =
          y ⬝ᵥ A' *ᵥ y + 2 * s * (b ⬝ᵥ y) + s ^ 2 * (b ⬝ᵥ u) := by
        rw [mulVec_add, mulVec_smul, hA'u, add_dotProduct, dotProduct_add, dotProduct_add,
          smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hA'sym u y, hA'u]
        simp only [smul_eq_mul]
        rw [dotProduct_comm y b, dotProduct_comm u b]
        ring
      rw [hquad, e1]
      ring
    rw [hsplit]
    by_cases hs0 : s = 0
    · have hy0 : y ≠ 0 := by
        intro h0
        apply hz
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact hs0
        · exact congrFun h0 j
      rw [hs0, zero_smul, add_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
      exact hA'pd y hy0
    · have h1 : 0 ≤ (y + s • u) ⬝ᵥ A' *ᵥ (y + s • u) := by
        by_cases hv : y + s • u = 0
        · rw [hv, mulVec_zero, dotProduct_zero]
        · exact (hA'pd _ hv).le
      have h2 : 0 < s ^ 2 * (c - b ⬝ᵥ u) := mul_pos (pow_pos (abs_pos.mpr hs0) 2 |>.trans_eq
        (sq_abs s)) hschur
      linarith

/-- **Theorem M.D.2(i)** (MWG, p. 936), Sylvester's criterion. A symmetric `N × N` matrix is
negative definite iff `(-1)^r |ₜMₜ| > 0` for every `r = 1, …, N`. -/
theorem theorem_M_D_2_i {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm) :
    NegDef M ↔ ∀ r (h : r ≤ N), 1 ≤ r → 0 < (-1) ^ r * (leadingMinorMatrix M r h).det := by
  constructor
  · intro hND r h _
    have := theorem_M_D_2_iii hND r h 1
    simpa [permuteMatrix] using this
  · intro h
    have hneg : (-M).IsSymm := by
      ext i j
      simp [hM.apply i j]
    have hpd := sylvester_posDef hneg (fun r hr h1 => by
      have e : leadingMinorMatrix (-M) r hr = -leadingMinorMatrix M r hr := rfl
      rw [e, det_neg_eq_pow]
      exact h r hr h1)
    have := (posDefMWG_iff_neg (-M)).mp hpd
    rwa [neg_neg] at this

/-! ### Exercise 2.F.9(a) -/

/-- **Exercise 2.F.9(a)** (MWG, p. 38). An arbitrary matrix `A` is negative definite
(semidefinite) iff `A + Aᵀ` is; the leading-minor condition `(-1)^k |A_kk| > 0` is necessary
for negative definiteness of `A`; and it is not sufficient: `A = [[-1, 4], [0, -1]]` satisfies
it but `(1, 1)·A(1, 1) = 2 > 0`. -/
theorem exercise_2_F_9a :
    (∀ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ), (NegDef A ↔ NegDef (A + Aᵀ)) ∧
      (NegSemidef A ↔ NegSemidef (A + Aᵀ)) ∧
      (NegDef A → ∀ k (h : k ≤ N), 1 ≤ k → 0 < (-1) ^ k * (leadingMinorMatrix A k h).det)) ∧
    (∀ k (h : k ≤ 2), 1 ≤ k →
      0 < (-1) ^ k * (leadingMinorMatrix !![-1, 4; 0, -1] k h).det) ∧
    ¬ NegDef !![(-1 : ℝ), 4; 0, -1] := by
  refine ⟨fun A => ⟨theorem_M_D_1_i A, theorem_M_D_1_i_semidef A, fun hA k h _ => ?_⟩,
    fun k h hk => ?_, fun hA => ?_⟩
  · simpa [permuteMatrix] using theorem_M_D_2_iii hA k h 1
  · interval_cases k
    · simp [leadingMinorMatrix]
    · simp [leadingMinorMatrix, Matrix.det_fin_two]
  · have := hA ![1, 1] (by intro h0; simpa using congrFun h0 0)
    simp [dotProduct, mulVec, Fin.sum_univ_two] at this
    norm_num at this

end MWG.ConsumerChoice
