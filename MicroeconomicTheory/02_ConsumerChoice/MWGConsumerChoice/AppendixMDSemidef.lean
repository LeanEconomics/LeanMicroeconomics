/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDDeterminants
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Finset.Sort

/-!
# The determinantal test for negative semidefiniteness

MWG, Mathematical Appendix, Theorem M.D.2(ii) (p. 936) and its discussion (p. 937).

A symmetric `M` is negative semidefinite iff `(-1)^r |ₜM^πₜ| ≥ 0` for every `r = 1, …, N` and
every permutation `π`. The book does not prove sufficiency; here every principal minor of
`-M` is obtained as a permuted leading minor, the coefficients of `det(I + t(-M))` are sums of
principal minors (Mathlib's `coeff_det_one_add_X_smul_eq_sum_minors`), so this determinant is
at least 1 for `t ≥ 0`, which rules out a negative eigenvalue of `-M`.

The book's example (p. 937) that permutations are needed: `[[0, 0], [0, 1]]` satisfies the
leading-minor conditions but is not negative semidefinite.
-/

namespace MWG.ConsumerChoice

open Matrix Polynomial

/-- Every injection `Fin r → Fin N` is the restriction of a permutation to the first `r`
indices. -/
theorem exists_perm_extend {N r : ℕ} (h : r ≤ N) (f : Fin r → Fin N)
    (hf : Function.Injective f) : ∃ π : Equiv.Perm (Fin N), ∀ i, π (Fin.castLE h i) = f i := by
  classical
  let e : {x // x ∈ Set.range (Fin.castLE h)} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective _ (Fin.castLE_injective h)).symm.trans (Equiv.ofInjective f hf)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e _ ⟨i, rfl⟩]
  simp only [e, Equiv.trans_apply]
  have : (Equiv.ofInjective _ (Fin.castLE_injective h)).symm ⟨Fin.castLE h i, ⟨i, rfl⟩⟩ = i :=
    Equiv.ofInjective_symm_apply (Fin.castLE_injective h) i
  rw [this]
  rfl

/-- Each principal minor (indexed by a set of rows and columns) is a permuted leading minor. -/
theorem principalMinor_eq_permuted {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (s : Finset (Fin N)) :
    ∃ π : Equiv.Perm (Fin N),
      (M.submatrix (Subtype.val : s → Fin N) Subtype.val).det =
        (leadingMinorMatrix (permuteMatrix M π) s.card (Finset.card_le_univ s |>.trans
          (by simp))).det := by
  have hr : s.card ≤ N := (Finset.card_le_univ s).trans (by simp)
  obtain ⟨π, hπ⟩ := exists_perm_extend hr (s.orderEmbOfFin rfl)
    (s.orderEmbOfFin rfl).injective
  refine ⟨π, ?_⟩
  have e1 : leadingMinorMatrix (permuteMatrix M π) s.card hr =
      (M.submatrix (Subtype.val : s → Fin N) Subtype.val).submatrix
        (s.orderIsoOfFin rfl).toEquiv (s.orderIsoOfFin rfl).toEquiv := by
    ext i j
    simp only [leadingMinorMatrix, permuteMatrix, submatrix_apply, hπ,
      RelIso.coe_fn_toEquiv, Finset.coe_orderIsoOfFin_apply]
  rw [e1, det_submatrix_equiv_self]

/-- A symmetric real matrix all of whose principal minors are nonnegative is positive
semidefinite. -/
theorem posSemidef_of_principal_minors {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hmin : ∀ s : Finset n, 0 ≤ (A.submatrix (Subtype.val : s → n) Subtype.val).det) :
    PosSemidefMWG A := by
  have hH : A.IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, hA.apply i j]
  rw [posSemidefMWG_iff_posSemidef hA, hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hneg
  push Not at hneg
  have hneg' : hH.eigenvalues i < 0 := hneg
  set μ := hH.eigenvalues i
  set v := hH.eigenvectorBasis i
  have hv := hH.mulVec_eigenvectorBasis i
  have hv0 : (⇑v : n → ℝ) ≠ 0 := by
    intro h0
    have := (hH.eigenvectorBasis).orthonormal.ne_zero i
    apply this
    ext j
    simpa using congrFun h0 j
  set t : ℝ := -μ⁻¹
  have ht : 0 < t := by simp only [t]; exact neg_pos.mpr (inv_lt_zero.mpr hneg')
  have hμ : μ ≠ 0 := hneg'.ne
  -- `I + tA` is singular
  have hsing : (1 + t • A).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨⇑v, hv0, ?_⟩
    rw [add_mulVec, one_mulVec, smul_mulVec, hv, smul_smul]
    have : t * μ = -1 := by simp only [t]; rw [neg_mul, inv_mul_cancel₀ hμ]
    rw [this, neg_one_smul, add_neg_cancel]
  -- but `det(I + tA) ≥ 1`
  set P : ℝ[X] := det (1 + (X : ℝ[X]) • A.map C) with hP
  have heval : P.eval t = (1 + t • A).det := by
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
      ring
    · simp [hab]
      ring
  have hcoeff : ∀ k, 0 ≤ P.coeff k := by
    intro k
    rw [hP, coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_nonneg fun s _ => hmin s
  have hcoeff0 : P.coeff 0 = 1 := by
    rw [hP, coeff_det_one_add_X_smul_eq_sum_minors, Finset.powersetCard_zero]
    simp only [Finset.sum_singleton]
    have : IsEmpty ((∅ : Finset n) : Set n) := by simp
    exact det_isEmpty
  have hge : 1 ≤ P.eval t := by
    rw [eval_eq_sum_range]
    calc (1 : ℝ) = P.coeff 0 * t ^ 0 := by rw [hcoeff0]; simp
      _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * t ^ k :=
        Finset.single_le_sum (f := fun k => P.coeff k * t ^ k)
          (fun k _ => mul_nonneg (hcoeff k) (pow_nonneg ht.le k))
          (Finset.mem_range.mpr (Nat.succ_pos _))
  rw [heval, hsing] at hge
  linarith

/-- **Theorem M.D.2(ii)** (MWG, p. 936). A symmetric `N × N` matrix is negative semidefinite
iff `(-1)^r |ₜM^πₜ| ≥ 0` for every `r = 1, …, N` and every permutation `π`. -/
theorem theorem_M_D_2_ii {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm) :
    NegSemidef M ↔ ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), 1 ≤ r →
      0 ≤ (-1) ^ r * (leadingMinorMatrix (permuteMatrix M π) r h).det := by
  constructor
  · intro hND r h π _
    set S := leadingMinorMatrix (permuteMatrix M π) r h
    have hS : NegSemidef S :=
      hND.submatrix (e := π ∘ Fin.castLE h) (π.injective.comp (Fin.castLE_injective h))
    have hSsymm : (-S).IsSymm := by
      ext i j
      simp [S, leadingMinorMatrix, permuteMatrix, hM.apply]
    have hpsd : PosSemidefMWG (-S) := by
      rw [posSemidefMWG_iff_neg, neg_neg]
      exact hS
    rw [posSemidefMWG_iff_posSemidef hSsymm] at hpsd
    have := hpsd.det_nonneg
    rwa [det_neg_eq_pow] at this
  · intro h
    have hneg : (-M).IsSymm := by
      ext i j
      simp [hM.apply i j]
    have hpsd := posSemidef_of_principal_minors hneg (fun s => by
      obtain ⟨π, hπ⟩ := principalMinor_eq_permuted (-M) s
      rw [hπ]
      rcases Nat.eq_zero_or_pos s.card with h0 | h0
      · have : IsEmpty (Fin s.card) := by rw [h0]; infer_instance
        rw [det_isEmpty]
        exact zero_le_one
      · have e : leadingMinorMatrix (permuteMatrix (-M) π) s.card
            ((Finset.card_le_univ s).trans (by simp)) =
            -leadingMinorMatrix (permuteMatrix M π) s.card
              ((Finset.card_le_univ s).trans (by simp)) := rfl
        rw [e, det_neg_eq_pow]
        exact h _ _ π h0)
    rw [posSemidefMWG_iff_neg, neg_neg] at hpsd
    exact hpsd

/-- **Section M.D** (MWG, p. 937). Permutations are needed in Theorem M.D.2(ii): the matrix
`[[0, 0], [0, 1]]` satisfies `(-1)^r |ₜMₜ| ≥ 0` for `r = 1, 2` but is not negative
semidefinite. -/
theorem theorem_M_D_2_ii_permutations_needed :
    (∀ r (h : r ≤ 2), 1 ≤ r →
      0 ≤ (-1) ^ r * (leadingMinorMatrix !![(0 : ℝ), 0; 0, 1] r h).det) ∧
    ¬ NegSemidef !![(0 : ℝ), 0; 0, 1] := by
  refine ⟨fun r h hr => ?_, fun hns => ?_⟩
  · interval_cases r
    · simp [leadingMinorMatrix]
    · simp [leadingMinorMatrix, Matrix.det_fin_two]
  · have := hns ![0, 1]
    simp [dotProduct, mulVec, Fin.sum_univ_two] at this
    linarith

end MWG.ConsumerChoice
