/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Real.Basic

/-!
# Negative and positive (semi)definite matrices

MWG, Mathematical Appendix, Definition M.D.1 (p. 935), and footnote 11 of Chapter 2 (p. 34):
definiteness does not presuppose symmetry. A real square matrix `M` is negative semidefinite
if `z·Mz ≤ 0` for all `z`, negative definite if `z·Mz < 0` for all `z ≠ 0`, and positive
(semi)definite with the inequalities reversed. `M` is positive (semi)definite iff `-M` is
negative (semi)definite (p. 935). For symmetric matrices the notions agree with Mathlib's
`Matrix.PosDef` and `Matrix.PosSemidef` (bridges below).
-/

namespace MWG.ConsumerChoice

variable {n : Type*} [Fintype n]

/-- **Definition M.D.1** (MWG, p. 935). `M` is negative semidefinite: `z·Mz ≤ 0` for all `z`.
-/
def NegSemidef (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, z ⬝ᵥ M.mulVec z ≤ 0

/-- **Definition M.D.1** (MWG, p. 935). `M` is negative definite: `z·Mz < 0` for all `z ≠ 0`.
-/
def NegDef (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, z ≠ 0 → z ⬝ᵥ M.mulVec z < 0

/-- **Definition M.D.1** (MWG, p. 935). `M` is positive semidefinite: `z·Mz ≥ 0` for all `z`.
-/
def PosSemidefMWG (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, 0 ≤ z ⬝ᵥ M.mulVec z

/-- **Definition M.D.1** (MWG, p. 935). `M` is positive definite: `z·Mz > 0` for all `z ≠ 0`.
-/
def PosDefMWG (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ M.mulVec z

/-- **Section M.D** (MWG, p. 935). `M` is positive semidefinite iff `-M` is negative
semidefinite. -/
theorem posSemidefMWG_iff_neg (M : Matrix n n ℝ) : PosSemidefMWG M ↔ NegSemidef (-M) := by
  simp only [PosSemidefMWG, NegSemidef, Matrix.neg_mulVec, dotProduct_neg, neg_nonpos]

/-- **Section M.D** (MWG, p. 935). `M` is positive definite iff `-M` is negative definite. -/
theorem posDefMWG_iff_neg (M : Matrix n n ℝ) : PosDefMWG M ↔ NegDef (-M) := by
  simp only [PosDefMWG, NegDef, Matrix.neg_mulVec, dotProduct_neg, neg_neg_iff_pos]

/-- Negative definite matrices are negative semidefinite. -/
theorem NegDef.negSemidef {M : Matrix n n ℝ} (h : NegDef M) : NegSemidef M := by
  intro z
  by_cases hz : z = 0
  · simp [hz]
  · exact (h z hz).le

/-- Bridge to Mathlib: a symmetric matrix is positive semidefinite in MWG's sense iff it is
`Matrix.PosSemidef`. -/
theorem posSemidefMWG_iff_posSemidef {M : Matrix n n ℝ} (hM : M.IsSymm) :
    PosSemidefMWG M ↔ M.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hH : M.IsHermitian := by simpa [Matrix.IsHermitian] using hM.eq
  simp only [PosSemidefMWG, star_trivial]
  exact ⟨fun h => ⟨hH, h⟩, fun h => h.2⟩

/-- Bridge to Mathlib: a symmetric matrix is positive definite in MWG's sense iff it is
`Matrix.PosDef`. -/
theorem posDefMWG_iff_posDef {M : Matrix n n ℝ} (hM : M.IsSymm) :
    PosDefMWG M ↔ M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hH : M.IsHermitian := by simpa [Matrix.IsHermitian] using hM.eq
  simp only [PosDefMWG, star_trivial]
  exact ⟨fun h => ⟨hH, h⟩, fun h => h.2⟩

end MWG.ConsumerChoice
