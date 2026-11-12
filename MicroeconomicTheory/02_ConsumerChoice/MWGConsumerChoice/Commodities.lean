/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ConsumerDemand.BudgetSets
import Mathlib.Analysis.Convex.Basic

/-!
# Commodities and consumption sets

MWG, Sections 2.B and 2.C, pp. 17–20. A commodity vector is a point of `ℝ^L`, encoded as
`Fin L → ℝ`. The standard consumption set is the nonnegative orthant `ℝ^L_+`; it is convex
(p. 19). The six consumption sets drawn in Figures 2.C.1–2.C.6 are defined for `L = 2`
(good `0` is the horizontal axis, good `1` the vertical axis), and the text's claims on
p. 20 are proved: the sets of Figures 2.C.1, 2.C.4, 2.C.5 and 2.C.6 are convex, and those of
Figures 2.C.2 and 2.C.3 are not.

The orthant is bridged to Kreps' `NonnegativeOrthant` subtype (Kreps I, Chapter 3).
-/

namespace MWG.ConsumerChoice

/-- **Section 2.C** (MWG, p. 19). The consumption set `ℝ^L_+ = {x ∈ ℝ^L : x_ℓ ≥ 0}`. -/
def nonnegOrthant (L : ℕ) : Set (Fin L → ℝ) := {x | ∀ l, 0 ≤ x l}

/-- Membership in `ℝ^L_+` is the pointwise order `0 ≤ x`. -/
theorem mem_nonnegOrthant_iff {L : ℕ} (x : Fin L → ℝ) : x ∈ nonnegOrthant L ↔ 0 ≤ x :=
  Iff.rfl

/-- Bridge: MWG's `ℝ^L_+` is exactly the carrier of Kreps' `NonnegativeOrthant L`. -/
theorem range_val_nonnegativeOrthant (L : ℕ) :
    Set.range (Subtype.val : Kreps.ConsumerDemand.NonnegativeOrthant L → Fin L → ℝ) =
      nonnegOrthant L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **Footnote 2** (MWG, p. 19). The `ℓ`th entry of `αx + (1-α)x'` is `αx_ℓ + (1-α)x'_ℓ`. -/
theorem convexCombination_apply {L : ℕ} (x x' : Fin L → ℝ) (a : ℝ) (l : Fin L) :
    (a • x + (1 - a) • x') l = a * x l + (1 - a) * x' l := by
  simp [smul_eq_mul]

/-- **Section 2.C** (MWG, p. 19). The consumption set `ℝ^L_+` is convex. -/
theorem convex_nonnegOrthant (L : ℕ) : Convex ℝ (nonnegOrthant L) := by
  intro x hx y hy a b ha hb _ l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l))

/-- **Figure 2.C.1** (MWG, p. 19). Bread (good `0`) and leisure (good `1`): both nonnegative
and at most 24 hours of leisure. -/
def figure_2_C_1_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ 24}

/-- **Figure 2.C.2** (MWG, p. 19). Good `0` divisible, good `1` in nonnegative integer
amounts. -/
def figure_2_C_2_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ ∃ n : ℕ, x 1 = n}

/-- **Figure 2.C.3** (MWG, p. 19). Bread in Washington or bread in New York at noon, but not
both: one of the two coordinates is zero. -/
def figure_2_C_3_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ (x 0 = 0 ∨ x 1 = 0)}

/-- **Figure 2.C.4** (MWG, p. 19). Survival needs: at least four slices of bread in total. -/
def figure_2_C_4_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 4 ≤ x 0 + x 1}

/-- **Figure 2.C.5** (MWG, p. 20). At most 16 hours of work, so leisure lies in `[8, 24]`. -/
def figure_2_C_5_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 8 ≤ x 1 ∧ x 1 ≤ 24}

/-- **Figure 2.C.6** (MWG, p. 20). The consumption set `ℝ²_+`. -/
def figure_2_C_6_set : Set (Fin 2 → ℝ) := nonnegOrthant 2

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.1 is convex. -/
theorem convex_figure_2_C_1 : Convex ℝ figure_2_C_1_set := by
  intro x hx y hy a b ha hb hab
  simp only [figure_2_C_1_set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.4 is convex. -/
theorem convex_figure_2_C_4 : Convex ℝ figure_2_C_4_set := by
  intro x hx y hy a b ha hb hab
  simp only [figure_2_C_4_set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.5 is convex. -/
theorem convex_figure_2_C_5 : Convex ℝ figure_2_C_5_set := by
  intro x hx y hy a b ha hb hab
  simp only [figure_2_C_5_set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.6 is convex. -/
theorem convex_figure_2_C_6 : Convex ℝ figure_2_C_6_set := convex_nonnegOrthant 2

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.2 is not convex: the
midpoint of `(0,0)` and `(0,1)` has half a unit of the indivisible good. -/
theorem not_convex_figure_2_C_2 : ¬ Convex ℝ figure_2_C_2_set := by
  intro h
  have h0 : (![0, 0] : Fin 2 → ℝ) ∈ figure_2_C_2_set := ⟨le_rfl, 0, by simp⟩
  have h1 : (![0, 1] : Fin 2 → ℝ) ∈ figure_2_C_2_set := ⟨le_rfl, 1, by simp⟩
  have hm := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  obtain ⟨_, n, hn⟩ := hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hn
  norm_num at hn
  rcases Nat.lt_or_ge n 1 with h' | h'
  · have : n = 0 := by omega
    subst this
    norm_num at hn
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h'
    linarith

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.3 is not convex: the
midpoint of `(1,0)` and `(0,1)` consumes both goods. -/
theorem not_convex_figure_2_C_3 : ¬ Convex ℝ figure_2_C_3_set := by
  intro h
  have h0 : (![1, 0] : Fin 2 → ℝ) ∈ figure_2_C_3_set := by
    refine ⟨by simp, by simp, Or.inr (by simp)⟩
  have h1 : (![0, 1] : Fin 2 → ℝ) ∈ figure_2_C_3_set := by
    refine ⟨by simp, by simp, Or.inl (by simp)⟩
  have hm := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  obtain ⟨_, _, hm⟩ := hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hm
  norm_num at hm

end MWG.ConsumerChoice
