/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDDeterminants
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Definiteness on the hyperplane orthogonal to a positive vector

MWG, Mathematical Appendix, Theorem M.D.4 (p. 939). Let `M` be `N × N` with `Mp = 0` and
`Mᵀp = 0` for some `p ≫ 0`; `T_p = {z : p·z = 0}`; `M̂` deletes row and column `k`.

* (i) If `rank M = N - 1` then `rank M̂ = N - 1`.
* (ii) If `M` is negative definite on `T_p`, then `z·Mz < 0` for every `z` not proportional
  to `p`.
* (iii) `M` is negative definite on `T_p` iff `M̂` is negative definite.

Here `N = n + 1` and the deleted index is `k : Fin (n + 1)`, with `M̂ = M.submatrix k.succAbove
k.succAbove`. In (ii) only `p ≠ 0` is used.
-/

namespace MWG.ConsumerChoice

open Matrix

/-- Removing a multiple of `p` does not change the quadratic form when `Mp = 0` and
`Mᵀp = 0`. -/
theorem quadratic_sub_smul {n : Type*} [Fintype n] {M : Matrix n n ℝ} {p : n → ℝ}
    (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0) (z : n → ℝ) (α : ℝ) :
    (z - α • p) ⬝ᵥ M *ᵥ (z - α • p) = z ⬝ᵥ M *ᵥ z := by
  have h2' : p ⬝ᵥ M *ᵥ z = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h2, zero_dotProduct]
  rw [mulVec_sub, mulVec_smul, h1, smul_zero, sub_zero, sub_dotProduct, smul_dotProduct, h2',
    smul_zero, sub_zero]

/-- **Theorem M.D.4(ii)** (MWG, p. 939). If `Mp = Mᵀp = 0` (`p ≠ 0`) and `z·Mz < 0` for all
nonzero `z ∈ T_p`, then `z·Mz < 0` for every `z` not proportional to `p`. -/
theorem theorem_M_D_4_ii {n : Type*} [Fintype n] {M : Matrix n n ℝ} {p : n → ℝ} (hp : p ≠ 0)
    (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0)
    (hT : ∀ z : n → ℝ, p ⬝ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0) (z : n → ℝ)
    (hz : ∀ α : ℝ, z ≠ α • p) : z ⬝ᵥ M *ᵥ z < 0 := by
  have hpp := dotProduct_self_pos_of_ne_zero hp
  set α := (p ⬝ᵥ z) / (p ⬝ᵥ p)
  rw [← quadratic_sub_smul h1 h2 z α]
  apply hT
  · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    simp only [α]
    field_simp
    ring
  · intro h0
    exact hz α (sub_eq_zero.mp h0)

/-- Extension by zero along `succAbove k` vanishes at `k`. -/
theorem extend_succAbove_self {n : ℕ} (k : Fin (n + 1)) (y : Fin n → ℝ) :
    Function.extend k.succAbove y 0 k = 0 := by
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨i, hi⟩
    exact Fin.succAbove_ne k i hi

/-- A vector vanishing at `k` is the extension by zero of its restriction. -/
theorem extend_succAbove_restrict {n : ℕ} (k : Fin (n + 1)) {z : Fin (n + 1) → ℝ}
    (hz : z k = 0) : Function.extend k.succAbove (fun i => z (k.succAbove i)) 0 = z := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
  · rw [h, extend_succAbove_self, hz]
  · rw [(Fin.succAbove_right_injective).extend_apply]

/-- **Theorem M.D.4(iii)** (MWG, p. 939). With `p ≫ 0`, `Mp = 0` and `Mᵀp = 0`, `M` is negative
definite on `T_p` iff `M̂` (delete row and column `k`) is negative definite. -/
theorem theorem_M_D_4_iii {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {p : Fin (n + 1) → ℝ} (hp : ∀ i, 0 < p i) (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0)
    (k : Fin (n + 1)) :
    (∀ z : Fin (n + 1) → ℝ, p ⬝ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0) ↔
      NegDef (M.submatrix k.succAbove k.succAbove) := by
  have hp0 : p ≠ 0 := fun h => by have := hp k; rw [h] at this; exact lt_irrefl _ this
  constructor
  · intro hT y hy
    rw [quadratic_submatrix M Fin.succAbove_right_injective]
    apply theorem_M_D_4_ii hp0 h1 h2 hT
    intro α hα
    have hk := congrFun hα k
    rw [extend_succAbove_self, Pi.smul_apply, smul_eq_mul] at hk
    have hα0 : α = 0 := by
      rcases mul_eq_zero.mp hk.symm with h | h
      · exact h
      · exact absurd h (hp k).ne'
    apply hy
    funext i
    have := congrFun hα (k.succAbove i)
    rwa [Fin.succAbove_right_injective.extend_apply, hα0, zero_smul] at this
  · intro hND z' hpz hz'
    set α := z' k / p k
    set z := z' - α • p with hzdef
    have hzk : z k = 0 := by
      simp only [hzdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, α]
      field_simp [(hp k).ne']
      ring
    have hz0 : (fun i => z (k.succAbove i)) ≠ 0 := by
      intro h0
      have hz : z = 0 := by
        rw [← extend_succAbove_restrict k hzk, h0]
        funext j
        rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
        · rw [h, extend_succAbove_self]
          rfl
        · rw [Fin.succAbove_right_injective.extend_apply]
          rfl
      have hz'eq : z' = α • p := sub_eq_zero.mp hz
      have hpp := dotProduct_self_pos_of_ne_zero hp0
      rw [hz'eq, dotProduct_smul, smul_eq_mul] at hpz
      have hα : α = 0 := by
        rcases mul_eq_zero.mp hpz with h | h
        · exact h
        · linarith
      apply hz'
      rw [hz'eq, hα, zero_smul]
    have := hND _ hz0
    rw [quadratic_submatrix M Fin.succAbove_right_injective, extend_succAbove_restrict k hzk,
      hzdef, quadratic_sub_smul h1 h2] at this
    exact this

/-- The rank of a square matrix with two linearly independent kernel vectors is at most its size
minus two. -/
theorem rank_le_of_two_kernel_vectors {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) {u v : Fin N → ℝ}
    (hu : M *ᵥ u = 0) (hv : M *ᵥ v = 0) (hind : LinearIndependent ℝ ![u, v]) :
    M.rank + 2 ≤ N := by
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hspan : Submodule.span ℝ (Set.range ![u, v]) ≤ LinearMap.ker M.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hu
    · simpa using hv
  have h2 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hind, Fintype.card_fin] at h2
  rw [Matrix.rank]
  omega

/-- **Theorem M.D.4(i)** (MWG, p. 939). With `p ≫ 0`, `Mp = 0` and `Mᵀp = 0`: if
`rank M = N - 1`, then `rank M̂ = N - 1`. -/
theorem theorem_M_D_4_i {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {p : Fin (n + 1) → ℝ} (hp : ∀ i, 0 < p i) (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0)
    (hrank : M.rank = n) (k : Fin (n + 1)) :
    (M.submatrix k.succAbove k.succAbove).rank = n := by
  set Mh := M.submatrix k.succAbove k.succAbove
  have hdet : Mh.det ≠ 0 := by
    intro hdet
    obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z := Function.extend k.succAbove y 0 with hz
    have hzk : z k = 0 := extend_succAbove_self k y
    have hzsA : ∀ i, z (k.succAbove i) = y i := fun i =>
      Fin.succAbove_right_injective.extend_apply _ _ _
    -- rows other than `k`
    have hrows : ∀ i, (M *ᵥ z) (k.succAbove i) = 0 := by
      intro i
      have := congrFun hMy i
      simp only [mulVec, dotProduct, Pi.zero_apply, Mh, submatrix_apply] at this ⊢
      rw [Fin.sum_univ_succAbove _ k, hzk, mul_zero, zero_add]
      simpa only [hzsA] using this
    -- row `k`, from `pᵀM = 0`
    have hrowk : (M *ᵥ z) k = 0 := by
      have hpz : p ⬝ᵥ M *ᵥ z = 0 := by
        rw [dotProduct_mulVec, ← mulVec_transpose, h2, zero_dotProduct]
      rw [dotProduct, Fin.sum_univ_succAbove _ k] at hpz
      simp only [hrows, mul_zero, Finset.sum_const_zero, add_zero] at hpz
      rcases mul_eq_zero.mp hpz with h | h
      · exact absurd h (hp k).ne'
      · exact h
    have hMz : M *ᵥ z = 0 := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
      · rw [h]; exact hrowk
      · exact hrows i
    have hind : LinearIndependent ℝ ![z, p] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hk := congrFun hst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzk, mul_zero, zero_add,
        Pi.zero_apply] at hk
      have ht : t = 0 := by
        rcases mul_eq_zero.mp hk with h | h
        · exact h
        · exact absurd h (hp k).ne'
      refine ⟨?_, ht⟩
      rw [ht, zero_smul, add_zero] at hst
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hy (funext hc)
      have := congrFun hst (k.succAbove i)
      rw [Pi.smul_apply, hzsA, smul_eq_mul, Pi.zero_apply] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hi
    have := rank_le_of_two_kernel_vectors M hMz h1 hind
    omega
  have hU : IsUnit Mh := (Matrix.isUnit_iff_isUnit_det Mh).mpr (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.rank_of_isUnit Mh hU, Fintype.card_fin]

end MWG.ConsumerChoice
