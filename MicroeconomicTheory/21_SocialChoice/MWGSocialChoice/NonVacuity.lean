/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.GradientCycles
import MWGSocialChoice.EuclideanExercises
import MWGSocialChoice.ArrowConditions
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Instances of the hypotheses of the chapter's theorems

Concrete instances showing that the hypothesis sets of Proposition 21.D.1, Example 21.D.6,
Exercise 21.D.7 and Exercise 21.D.13 are satisfiable (the other results carry their instances
next to them: `proposition_21_C_1_nonvacuous`, `dictatorial_strict_spec`,
`smallestTopLabel_noIncentive`, `exercise_21_C_2b`, `exercise_21_D_9e_instance`, the
Exercise 21.D.10 applications of Example 21.D.4 and Proposition 21.D.1, and so on).
-/

namespace MWG.SocialChoice

open Finset MeasureTheory

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Proposition 21.D.1**, instance. Three agents on `{0, 1, 2}` with peaks `0, 2, 2`; agent 1
(peak `2`) is a median agent, so `2` is the Condorcet winner. -/
theorem proposition_21_D_1_instance :
    let p : Profile (Fin 3) (Fin 3) := fun i => natPref (![![2, 1, 0], ![0, 1, 2], ![0, 1, 2]] i)
    (∀ i, IsPeak (p i) (![0, 2, 2] i)) ∧ IsMedianAgent (![0, 2, 2] : Fin 3 → Fin 3) 1 ∧
      IsCondorcetWinner p 2 := by
  intro p
  have hpk : ∀ i, IsPeak (p i) (![0, 2, 2] i) := by
    intro i
    simp only [IsPeak, p, natPref_strict_iff]
    fin_cases i <;> decide
  have hmed : IsMedianAgent (![0, 2, 2] : Fin 3 → Fin 3) 1 := by
    unfold IsMedianAgent
    decide
  exact ⟨hpk, hmed, (proposition_21_D_1 hpk hmed).1⟩

/-- **Example 21.D.6**, instance. The point mass at `x` has `x` as a median, hence as a Condorcet
winner. -/
theorem example_21_D_6_instance (x : ℂ) :
    IsMedianPoint (Measure.dirac x) x ∧ IsCondorcetWinnerMeasure (Measure.dirac x) x := by
  have hmed : IsMedianPoint (Measure.dirac x) x := by
    intro q _
    rw [Measure.dirac_apply' _ (measurableSet_openHalfSpace x q)]
    simp [openHalfSpace]
  exact ⟨hmed, (example_21_D_6 _ x).1 hmed⟩

/-- The linear utility `v ↦ ⟪g, v⟫` has gradient `g` at `0`. -/
theorem hasGradientAt_inner_const (g : ℂ) : HasGradientAt (fun v : ℂ => ⟪g, v⟫) g 0 := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (InnerProductSpace.toDual ℝ ℂ g : ℂ →L[ℝ] ℝ).hasFDerivAt (x := 0)
  convert h using 1
  funext v
  simp [InnerProductSpace.toDual_apply_apply]

/-- **Exercise 21.D.7**, instance. The linear utilities with gradients `1`, `I`, `-1 - I` on
`X = ℂ`: the cone of the gradients is the whole plane. -/
theorem exercise_21_D_7_instance :
    (∀ i, HasGradientAt (fun v : ℂ => ⟪![1, Complex.I, -1 - Complex.I] i, v⟫)
      (![1, Complex.I, -1 - Complex.I] i) 0) ∧
      ∀ v : ℂ, ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧
        v = ∑ i, μ i • (![1, Complex.I, -1 - Complex.I] : Fin 3 → ℂ) i := by
  refine ⟨fun i => hasGradientAt_inner_const _, fun v => ?_⟩
  set M := |v.re| + |v.im|
  refine ⟨![v.re + M, v.im + M, M], fun i => ?_, ?_⟩
  · fin_cases i <;> simp [M] <;> linarith [neg_abs_le v.re, neg_abs_le v.im, abs_nonneg v.re,
      abs_nonneg v.im]
  · apply Complex.ext <;> simp [Fin.sum_univ_three, M] <;> ring

/-- **Exercise 21.D.13(a)**, instance. Three types of equal mass with collinear peaks `-1, 0, 1`:
the middle peak `0` is a Condorcet winner. -/
theorem exercise_21_D_13a_instance :
    IsTypeCondorcetWinner ![(-1 : ℂ), 0, 1] (fun _ => 1) 0 := by
  intro z
  unfold typeMass
  simp only [sum_filter, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have tri : ‖(-1 : ℂ) - z‖ + ‖(1 : ℂ) - z‖ ≥ 2 := by
    have := norm_sub_le ((1 : ℂ) - z) ((-1 : ℂ) - z)
    have e : (1 : ℂ) - z - (-1 - z) = 2 := by ring
    rw [e] at this
    simp only [Complex.norm_ofNat] at this
    linarith [norm_sub_rev ((-1 : ℂ) - z) 0]
  have h1 : ‖(-1 : ℂ) - 0‖ = 1 := by simp
  have h2 : ‖(1 : ℂ) - 0‖ = 1 := by simp
  have h0 : ‖(0 : ℂ) - 0‖ = 0 := by simp
  have hz := norm_nonneg ((0 : ℂ) - z)
  by_cases hA : ‖(-1 : ℂ) - z‖ < ‖(-1 : ℂ) - 0‖ <;>
    by_cases hB : ‖(0 : ℂ) - z‖ < ‖(0 : ℂ) - 0‖ <;>
    by_cases hC : ‖(1 : ℂ) - z‖ < ‖(1 : ℂ) - 0‖ <;>
    by_cases hA' : ‖(-1 : ℂ) - 0‖ < ‖(-1 : ℂ) - z‖ <;>
    by_cases hB' : ‖(0 : ℂ) - 0‖ < ‖(0 : ℂ) - z‖ <;>
    by_cases hC' : ‖(1 : ℂ) - 0‖ < ‖(1 : ℂ) - z‖ <;>
    simp only [hA, hB, hC, hA', hB', hC', ↓reduceIte] <;> linarith

/-- **Exercise 21.D.13(b)**, instance. Peaks `0, 1, I` (in general position), masses
`1/2, 1/4, 1/4`; the dominant type's peak `0` is a Condorcet winner. -/
theorem exercise_21_D_13b_instance :
    GeneralPosition ![(0 : ℂ), 1, Complex.I] ∧
      IsTypeCondorcetWinner ![(0 : ℂ), 1, Complex.I] ![1 / 2, 1 / 4, 1 / 4] 0 := by
  refine ⟨fun i j k hij hik hjk => ?_, fun z => ?_⟩
  · rw [inner_I_mul]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  · unfold typeMass
    simp only [sum_filter, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    by_cases hz : z = 0
    · subst hz
      simp
    · have hpos : 0 < ‖(0 : ℂ) - z‖ := by simpa using hz
      have hn : ¬‖(0 : ℂ) - z‖ < ‖(0 : ℂ) - 0‖ := by simp
      have hy : ‖(0 : ℂ) - 0‖ < ‖(0 : ℂ) - z‖ := by simpa using hpos
      simp only [hn, hy, ↓reduceIte]
      by_cases hA : ‖(1 : ℂ) - z‖ < ‖(1 : ℂ) - 0‖ <;>
        by_cases hB : ‖Complex.I - z‖ < ‖Complex.I - 0‖ <;>
        by_cases hA' : ‖(1 : ℂ) - 0‖ < ‖(1 : ℂ) - z‖ <;>
        by_cases hB' : ‖Complex.I - 0‖ < ‖Complex.I - z‖ <;>
        simp only [hA, hB, hA', hB', ↓reduceIte] <;> norm_num

end MWG.SocialChoice
