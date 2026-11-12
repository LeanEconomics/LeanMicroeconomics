/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.AppendixMDDeterminants
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Bordered matrices: Theorem M.D.3 and Example M.D.2

MWG, Mathematical Appendix, Theorem M.D.3 and Example M.D.2 (p. 938–939).

The book's subspace `{z ∈ ℝ^N : Bz = 0}` does not typecheck for an `N × S` matrix `B`; the
intended subspace (as in Example M.D.2, where `B = ∇f(x)`) is `{z : Bᵀz = 0}`. The bordered
matrix of order `r` is `[[ₜMₜ, ₜB], [(ₜB)ᵀ, 0]]`, with `ₜB` the first `r` rows of `B`.

* Theorem M.D.3(i) is false as printed (rank `B = S` is not enough): with `N = 3`, `S = 1`,
  `M = -I` and `B = e₃`, `M` is negative definite on `{z₃ = 0}` but the bordered determinant of
  order `r = 2` vanishes. The corrected statement (top `S × S` block of
  `B` nonsingular) is `theorem_M_D_3_i` in `AppendixMDBorderedTests`.
* Example M.D.2 (`N = 2`, `S = 1`, `B = ∇f`): the bordered determinant equals
  `2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁` (also after permuting), and for `∇f ≠ 0` the Hessian is negative
  definite (semidefinite) on `{z : ∇f·z = 0}` iff it is `> 0` (`≥ 0`). For `f = x₁x₂` it is
  `2x₁x₂`.
-/

namespace MWG.ConsumerChoice

open Matrix

/-- **Theorem M.D.3** (MWG, p. 938). The bordered matrix of order `r`:
`[[ₜMₜ, ₜB], [(ₜB)ᵀ, 0]]`. -/
def borderedMatrix {N S : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin N) (Fin S) ℝ)
    (r : ℕ) (h : r ≤ N) : Matrix (Fin r ⊕ Fin S) (Fin r ⊕ Fin S) ℝ :=
  Matrix.fromBlocks (leadingMinorMatrix M r h) (B.submatrix (Fin.castLE h) id)
    (B.submatrix (Fin.castLE h) id)ᵀ 0

/-- **Theorem M.D.3(i)** (MWG, p. 938), counterexample to the printed statement. For `N = 3`,
`S = 1`, `M = -I` and `B = (0, 0, 1)ᵀ` (rank 1), `M` is negative definite on `{z : Bᵀz = 0}`, but
`(-1)^r |bordered_r| > 0` fails at `r = 2` (the determinant is `0`). -/
theorem theorem_M_D_3_i_counterexample :
    Matrix.rank (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ) = 1 ∧
      (∀ z : Fin 3 → ℝ, (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ)ᵀ *ᵥ z = 0 → z ≠ 0 →
        z ⬝ᵥ (-(1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ z < 0) ∧
      ¬ ∀ r (h : r ≤ 3), 2 ≤ r →
        0 < (-1) ^ r * (borderedMatrix (-(1 : Matrix (Fin 3) (Fin 3) ℝ))
          (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ) r h).det := by
  refine ⟨?_, fun z _ hz => ?_, fun h => ?_⟩
  · apply le_antisymm ((Matrix.rank_le_width _).trans (by norm_num))
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Matrix.rank, Submodule.finrank_eq_zero] at h0
    have hmem := LinearMap.mem_range_self
      (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ).mulVecLin (fun _ => 1)
    rw [h0, Submodule.mem_bot] at hmem
    have := congrFun hmem 2
    simp [mulVec, dotProduct] at this
  · rw [neg_mulVec, one_mulVec, dotProduct_neg, neg_neg_iff_pos]
    exact dotProduct_self_pos_of_ne_zero hz
  · have h2 := h 2 (by norm_num) le_rfl
    have hC : ((!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ).submatrix (Fin.castLE
        (by norm_num : 2 ≤ 3)) id)ᵀ = 0 := by
      ext i j
      fin_cases i; fin_cases j <;> rfl
    rw [borderedMatrix, hC, det_fromBlocks_zero₂₁] at h2
    simp at h2

/-- **Example M.D.2** (MWG, p. 938). The `3 × 3` bordered Hessian
`[[f₁₁, f₁₂, f₁], [f₁₂, f₂₂, f₂], [f₁, f₂, 0]]` has determinant
`2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁`; so does its permutation (p. 939). -/
theorem example_M_D_2_det (f1 f2 f11 f12 f22 : ℝ) :
    (!![f11, f12, f1; f12, f22, f2; f1, f2, 0] : Matrix (Fin 3) (Fin 3) ℝ).det =
        2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 ∧
      (!![f22, f12, f2; f12, f11, f1; f2, f1, 0] : Matrix (Fin 3) (Fin 3) ℝ).det =
        2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 := by
  constructor <;> rw [det_fin_three] <;> simp <;> ring

/-- On the line `{z : f₁z₁ + f₂z₂ = 0}` (with `∇f ≠ 0`) every vector is a multiple of
`(f₂, -f₁)`, and the Hessian form there is `-t² · (bordered determinant)`. -/
theorem example_M_D_2_line {f1 f2 f11 f12 f22 : ℝ} (hf : f1 ≠ 0 ∨ f2 ≠ 0) (z : Fin 2 → ℝ)
    (hz : f1 * z 0 + f2 * z 1 = 0) :
    ∃ t : ℝ, z = t • ![f2, -f1] ∧
      z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z =
        -(t ^ 2 * (2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11)) := by
  have hn : 0 < f1 ^ 2 + f2 ^ 2 := by
    rcases hf with h | h
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg f2]
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg f1]
  set t := (f2 * z 0 - f1 * z 1) / (f1 ^ 2 + f2 ^ 2)
  have hzt : z = t • ![f2, -f1] := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, t]
      field_simp
      linear_combination f1 * hz
    · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
        smul_eq_mul, t]
      field_simp
      linear_combination f2 * hz
  refine ⟨t, hzt, ?_⟩
  rw [hzt, quadratic_two_by_two]
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

/-- **Example M.D.2** (MWG, p. 938). With `∇f ≠ 0`, the Hessian is negative definite on
`{z ∈ ℝ² : ∇f·z = 0}` iff `2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁ > 0`. -/
theorem example_M_D_2_negDef {f1 f2 f11 f12 f22 : ℝ} (hf : f1 ≠ 0 ∨ f2 ≠ 0) :
    (∀ z : Fin 2 → ℝ, f1 * z 0 + f2 * z 1 = 0 → z ≠ 0 →
        z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z < 0) ↔
      0 < 2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 := by
  constructor
  · intro h
    have hw : f1 * f2 + f2 * -f1 = 0 := by ring
    have hne : (![f2, -f1] : Fin 2 → ℝ) ≠ 0 := by
      intro h0
      have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero]
        at e0 e1
      rcases hf with h' | h'
      · exact h' e1
      · exact h' e0
    have := h ![f2, -f1] (by simpa using hw) hne
    obtain ⟨t, ht, hq⟩ := example_M_D_2_line hf ![f2, -f1] (by simpa using hw)
    rw [hq] at this
    have ht1 : t = 1 := by
      have e := congrFun ht 0
      have e' := congrFun ht 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
        at e e'
      rcases hf with h' | h'
      · have : f1 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
      · have : f2 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
    rw [ht1] at this
    linarith
  · intro hd z hz hz0
    obtain ⟨t, ht, hq⟩ := example_M_D_2_line hf z hz
    rw [hq]
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ht
      exact hz0 ht
    have := pow_pos (abs_pos.mpr ht0) 2
    rw [sq_abs] at this
    nlinarith

/-- **Example M.D.2** (MWG, p. 939). With `∇f ≠ 0`, the Hessian is negative semidefinite on
`{z : ∇f·z = 0}` iff `2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁ ≥ 0`. -/
theorem example_M_D_2_negSemidef {f1 f2 f11 f12 f22 : ℝ} (hf : f1 ≠ 0 ∨ f2 ≠ 0) :
    (∀ z : Fin 2 → ℝ, f1 * z 0 + f2 * z 1 = 0 →
        z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z ≤ 0) ↔
      0 ≤ 2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 := by
  constructor
  · intro h
    have hw : f1 * f2 + f2 * -f1 = 0 := by ring
    have := h ![f2, -f1] (by simpa using hw)
    obtain ⟨t, ht, hq⟩ := example_M_D_2_line hf ![f2, -f1] (by simpa using hw)
    rw [hq] at this
    have ht1 : t = 1 := by
      have e := congrFun ht 0
      have e' := congrFun ht 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
        at e e'
      rcases hf with h' | h'
      · have : f1 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
      · have : f2 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
    rw [ht1] at this
    linarith
  · intro hd z hz
    obtain ⟨t, -, hq⟩ := example_M_D_2_line hf z hz
    rw [hq]
    nlinarith [sq_nonneg t]

/-- **Example M.D.2** (MWG, p. 938). For `f(x₁, x₂) = x₁x₂` (`f₁ = x₂`, `f₂ = x₁`, `f₁₁ = f₂₂ = 0`,
`f₁₂ = 1`) the bordered determinant is `2x₁x₂`, positive on `ℝ²₊₊`. -/
theorem example_M_D_2_product (x1 x2 : ℝ) (h1 : 0 < x1) (h2 : 0 < x2) :
    (!![0, 1, x2; 1, 0, x1; x2, x1, 0] : Matrix (Fin 3) (Fin 3) ℝ).det = 2 * x1 * x2 ∧
      0 < 2 * x1 * x2 := by
  refine ⟨?_, by positivity⟩
  rw [det_fin_three]
  simp
  ring

end MWG.ConsumerChoice
