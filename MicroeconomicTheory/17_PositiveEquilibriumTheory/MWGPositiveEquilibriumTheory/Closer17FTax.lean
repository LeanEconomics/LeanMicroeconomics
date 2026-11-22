/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17FMore

/-!
# Exercise 17.F.15: preferences generating the demand path (MWG p. 646)

`exercise_17_F_15_normality` shows that without normality the equilibrium with taxes need not
be unique, using the wealth-expansion path `taxPath` at the consumer prices `p = (1, 1/2)`. Here
continuous, monotone, convex preferences with exactly that demand are constructed.

The path `P(W) = taxPath W` satisfies `P₀(W) = max(0, min(2W - 1, W))` and
`P₀(W) + (3/4)P₁(W) = min(3W/2, max((W + 1)/2, W))` (`taxPath_zero`, `taxPath_comb`), both
nondecreasing. The utility `u(y) = min(A(y₀), B(y₀ + (3/4)y₁))` with the upper inverses
`A(a) = max((1 + a)/2, a)` and `B(b) = max(2b/3, min(2b - 1, b))` (`fn15U`) has the upper contour
sets `{y : u(y) ≥ W} = P(W) + C`, `C = {c : c₀ ≥ 0, c₀ + (3/4)c₁ ≥ 0}` (`fn15U_ge_iff`), a cone on
which `p` is strictly positive away from `0`; hence `P(W)` is the unique maximizer on the budget
set (`fn15U_demand`). The preferences are continuous, weakly monotone and convex
(`fn15U_continuous`, `fn15U_monotone`, `fn15U_quasiconcave`), and with them the two distinct
equilibria of `exercise_17_F_15_normality` are equilibria of an economy with preferences
(`exercise_17_F_15_preferences`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples

/-- **Exercise 17.F.15** (MWG, p. 646). The utility generating `taxPath` at prices `(1, 1/2)`:
`u(y) = min(max((1 + y₀)/2, y₀), max(2b/3, min(2b - 1, b)))` with `b = y₀ + (3/4)y₁`. -/
noncomputable def fn15U (y : Fin 2 → ℝ) : ℝ :=
  min (max ((1 + y 0) / 2) (y 0))
    (max (2 * (y 0 + 3 / 4 * y 1) / 3) (min (2 * (y 0 + 3 / 4 * y 1) - 1) (y 0 + 3 / 4 * y 1)))

/-- The first coordinate of the path: `P₀(W) = max(0, min(2W - 1, W))`. -/
theorem taxPath_zero (W : ℝ) : taxPath W 0 = max 0 (min (2 * W - 1) W) := by
  simp only [taxPath, Matrix.cons_val_zero]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- `P₀(W) + (3/4)P₁(W) = min(3W/2, max((W + 1)/2, W))`. -/
theorem taxPath_comb (W : ℝ) :
    taxPath W 0 + 3 / 4 * taxPath W 1 = min (3 * W / 2) (max ((W + 1) / 2) W) := by
  simp only [taxPath, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The upper contour sets of `fn15U`: for every `W` and `y` with `y₀ ≥ 0`, `W ≤ u(y)` iff
`y₀ ≥ P₀(W)` and
`y₀ + (3/4)y₁ ≥ P₀(W) + (3/4)P₁(W)`. -/
theorem fn15U_ge_iff {W : ℝ} {y : Fin 2 → ℝ} (hy : 0 ≤ y 0) :
    W ≤ fn15U y ↔ taxPath W 0 ≤ y 0 ∧
      taxPath W 0 + 3 / 4 * taxPath W 1 ≤ y 0 + 3 / 4 * y 1 := by
  rw [taxPath_comb, taxPath_zero, fn15U, le_min_iff, le_max_iff, le_max_iff, le_min_iff,
    max_le_iff, min_le_iff, min_le_iff, max_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hy, ?_⟩, ?_⟩
    · rcases h1 with h | h
      · left; linarith
      · right; exact h
    · rcases h2 with h | ⟨h, h'⟩
      · left; linarith
      · right; constructor <;> linarith
  · rintro ⟨⟨-, h1⟩, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · left; linarith
      · right; exact h
    · rcases h2 with h | ⟨h, h'⟩
      · left; linarith
      · right; constructor <;> linarith

/-- **Exercise 17.F.15** (MWG, p. 646). At the consumer prices `(1, 1/2)` and every wealth
`W ≥ 0`, the demand of `fn15U` on `ℝ²₊` is exactly `taxPath W`. -/
theorem fn15U_demand {W : ℝ} (hW : 0 ≤ W) :
    walrasianDemandOn (nonnegOrthant 2) fn15U ![1, 1 / 2] W = {taxPath W} := by
  have hdot : ∀ y : Fin 2 → ℝ, (![1, 1 / 2] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + y 1 / 2 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
    ring
  have hP := exercise_17_F_15_normality.2.1 W hW
  have hPw : taxPath W 0 + taxPath W 1 / 2 = W := by
    have := exercise_17_F_15_normality.1 W
    have hp : taxConsumerPrice ![1] ![0, -1 / 2] = ![1, 1 / 2] := by
      funext l; fin_cases l <;> norm_num [taxConsumerPrice, taxProducerPrice]
    rw [hp, hdot] at this
    exact this
  -- `u(P(W)) ≥ W`
  have hPu : W ≤ fn15U (taxPath W) := (fn15U_ge_iff (hP 0)).2 ⟨le_rfl, le_rfl⟩
  -- every affordable bundle has utility at most `W`
  have hle : ∀ y ∈ budgetSetOn (nonnegOrthant 2) ![1, 1 / 2] W, fn15U y ≤ W := by
    rintro y ⟨hy, hb⟩
    rw [hdot] at hb
    by_contra hlt
    push Not at hlt
    have hW' : 0 ≤ fn15U y := hW.trans hlt.le
    obtain ⟨h1, h2⟩ := (fn15U_ge_iff (hy 0)).1 le_rfl
    have hP' := exercise_17_F_15_normality.2.1 _ hW'
    have hsum : taxPath (fn15U y) 0 + taxPath (fn15U y) 1 / 2 = fn15U y := by
      have := exercise_17_F_15_normality.1 (fn15U y)
      have hp : taxConsumerPrice ![1] ![0, -1 / 2] = ![1, 1 / 2] := by
        funext l; fin_cases l <;> norm_num [taxConsumerPrice, taxProducerPrice]
      rw [hp, hdot] at this
      exact this
    linarith
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hb⟩, hmax⟩
    rw [hdot] at hb
    have hu := hPu.trans (hmax _ ⟨fun l => hP l, by rw [hdot, hPw]⟩)
    obtain ⟨h1, h2⟩ := (fn15U_ge_iff (hy 0)).1 hu
    have hd1 : taxPath W 1 ≤ y 1 := by linarith
    have hd0 : y 0 = taxPath W 0 := by linarith
    have hd1' : y 1 = taxPath W 1 := by linarith
    funext l
    fin_cases l
    · exact hd0
    · exact hd1'
  · rintro rfl
    exact ⟨⟨fun l => hP l, by rw [hdot, hPw]⟩, fun y hy => (hle y hy).trans hPu⟩

/-- `fn15U` is continuous. -/
theorem fn15U_continuous : Continuous fn15U := by
  unfold fn15U
  fun_prop

/-- `fn15U` is (weakly) monotone. -/
theorem fn15U_monotone {y y' : Fin 2 → ℝ} (h : y ≤ y') : fn15U y ≤ fn15U y' := by
  have h0 := h 0
  have h1 := h 1
  unfold fn15U
  gcongr

/-- `fn15U` is quasiconcave: its upper contour sets are convex (on `ℝ²₊`, they are translates of
the convex cone `C` intersected with `ℝ²₊`). -/
theorem fn15U_quasiconcave : QuasiconcaveOn ℝ (nonnegOrthant 2) fn15U := by
  intro r
  rcases lt_or_ge r 0 with hr | hr
  · -- below `0` the upper contour set is all of `ℝ²₊`
    have : {y ∈ nonnegOrthant 2 | r ≤ fn15U y} = nonnegOrthant 2 := by
      ext y
      simp only [Set.mem_sep_iff, and_iff_left_iff_imp]
      intro hy
      have : (0 : ℝ) ≤ fn15U y := (fn15U_ge_iff (hy 0)).2 (by
        rw [taxPath_comb, taxPath_zero]
        have := hy 0
        have := hy 1
        constructor
        · simpa using hy 0
        · norm_num; positivity)
      linarith
    rw [this]
    exact convex_nonnegOrthant 2
  · have : {y ∈ nonnegOrthant 2 | r ≤ fn15U y} =
        {y ∈ nonnegOrthant 2 | taxPath r 0 ≤ y 0 ∧
          taxPath r 0 + 3 / 4 * taxPath r 1 ≤ y 0 + 3 / 4 * y 1} := by
      ext y
      simp only [Set.mem_sep_iff]
      constructor
      · rintro ⟨hy, h⟩
        exact ⟨hy, (fn15U_ge_iff (hy 0)).1 h⟩
      · rintro ⟨hy, h⟩
        exact ⟨hy, (fn15U_ge_iff (hy 0)).2 h⟩
    rw [this]
    intro a ha b hb s t hs ht hst
    refine ⟨convex_nonnegOrthant 2 ha.1 hb.1 hs ht hst, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e1 := mul_le_mul_of_nonneg_left ha.2.1 hs
      have e2 := mul_le_mul_of_nonneg_left hb.2.1 ht
      have : s * taxPath r 0 + t * taxPath r 0 = taxPath r 0 := by rw [← add_mul, hst, one_mul]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e1 := mul_le_mul_of_nonneg_left ha.2.2 hs
      have e2 := mul_le_mul_of_nonneg_left hb.2.2 ht
      have : s * (taxPath r 0 + 3 / 4 * taxPath r 1) + t * (taxPath r 0 + 3 / 4 * taxPath r 1) =
          taxPath r 0 + 3 / 4 * taxPath r 1 := by rw [← add_mul, hst, one_mul]
      linarith

/-- **Exercise 17.F.15** (MWG, p. 646): normality is indispensable, with preferences. The consumer
with the continuous, monotone, convex utility `fn15U` (consumption set `ℝ²₊`) has at the consumer
prices the demand path `taxPath` (`fn15U_demand`), and the Leontief economy with the subsidy
`t₁ = -1/2` has two distinct equilibria: `(s, T) = (1/2, -1/4)` and `(1/4, -1/8)`. -/
theorem exercise_17_F_15_preferences :
    (∀ W, 0 ≤ W →
      walrasianDemandOn (nonnegOrthant 2) fn15U (taxConsumerPrice ![1] ![0, -1 / 2]) W =
        {taxPath W}) ∧
      IsLeontiefTaxEqm ![1] ![0, -1 / 2] ![1, 0] taxPath ![1 / 2] (-1 / 4) ∧
      IsLeontiefTaxEqm ![1] ![0, -1 / 2] ![1, 0] taxPath ![1 / 4] (-1 / 8) := by
  have hp : taxConsumerPrice ![1] ![0, -1 / 2] = ![1, 1 / 2] := by
    funext l; fin_cases l <;> norm_num [taxConsumerPrice, taxProducerPrice]
  refine ⟨fun W hW => ?_, exercise_17_F_15_normality.2.2.2.1,
    exercise_17_F_15_normality.2.2.2.2⟩
  rw [hp]
  exact fn15U_demand hW

end MWG.PositiveEquilibriumTheory
