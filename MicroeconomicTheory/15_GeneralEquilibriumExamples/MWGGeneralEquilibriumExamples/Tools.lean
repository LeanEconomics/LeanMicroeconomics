/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Exchange
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Deriv

/-!
# Analytic tools for Chapter 15

Small lemmas used throughout the chapter.

* `exists_pos_continuous_lt`: along a continuous path in `ℝ^L₊` starting at a point where a
  continuous utility exceeds `c`, the utility still exceeds `c` a little way along the path.
* `eventually_gt_of_deriv_pos`, `exists_pos_deriv_pos`: a function with positive derivative at
  `0` exceeds its value at `0` at small `t > 0` satisfying any eventual side condition.
* `quasiconcave_of_prefConvex`: convex preferences (Definition 3.B.4) give quasiconcave
  utilities in the form `min (u y) (u z) ≤ u (a y + b z)`.
* `dotProduct_pos_of_strictlyPositive`: `p ≫ 0`, `x ≥ 0`, `x ≠ 0` imply `p·x > 0`.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- Along a continuous path `g` in `ℝ^L₊` (on `[0, 1]`) starting at `a`, a utility that is
continuous on `ℝ^L₊` and exceeds `c` at `a` still exceeds `c` at some `g t`, `0 < t ≤ 1`. -/
theorem exists_pos_continuous_lt {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    {g : ℝ → Fin L → ℝ} (hg : Continuous g)
    (hgmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant L) {c : ℝ} (hca : c < u (g 0)) :
    ∃ t, 0 < t ∧ t ≤ 1 ∧ c < u (g t) := by
  have h1 : ContinuousWithinAt (u ∘ g) (Set.Icc 0 1) 0 :=
    (hc.comp hg.continuousOn fun t ht => hgmem t ht) 0 ⟨le_rfl, zero_le_one⟩
  have h2 : ∀ᶠ t in 𝓝[Set.Icc 0 1] (0 : ℝ), c < (u ∘ g) t := h1.eventually (lt_mem_nhds hca)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨ε, hε, hball⟩ := h2
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, ?_⟩
  refine hball ?_ ⟨(lt_min (half_pos hε) one_pos).le, min_le_right _ _⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (half_pos hε) one_pos)]
  exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)

/-- A function with positive derivative at `0` exceeds `f 0` at all small `t > 0`. -/
theorem eventually_gt_of_deriv_pos {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f 0 < f t := by
  have hs := hf.tendsto_slope_zero_right
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (f (0 + t) - f 0) := hs.eventually (lt_mem_nhds hd)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [h1, h2] with t ht1 ht2
  rw [zero_add, smul_eq_mul] at ht1
  have := (mul_pos_iff_of_pos_left (inv_pos.2 ht2)).1 ht1
  linarith

/-- A function with positive derivative at `0` exceeds `f 0` at some small `t > 0` at which a
given eventual property also holds. -/
theorem exists_pos_deriv_pos {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : 0 < d)
    {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ t, 0 < t ∧ P t ∧ f 0 < f t := by
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht1, ht2, ht3⟩ := ((eventually_gt_of_deriv_pos hf hd).and (h2.and hP)).exists
  exact ⟨t, ht2, ht3, ht1⟩

/-- A function with negative derivative at `0` falls below `f 0` at some small `t > 0` at which a
given eventual property also holds. -/
theorem exists_pos_deriv_neg {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (hd : d < 0)
    {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) : ∃ t, 0 < t ∧ P t ∧ f t < f 0 := by
  obtain ⟨t, ht, hPt, hlt⟩ := exists_pos_deriv_pos hf.neg (neg_pos.2 hd) hP
  exact ⟨t, ht, hPt, by simpa using hlt⟩

/-- Convex preferences (Definition 3.B.4) represented by `u` on `ℝ^L₊`: `u` is quasiconcave,
`min (u y) (u z) ≤ u (a y + b z)` for `a, b ≥ 0`, `a + b = 1`. -/
theorem quasiconcave_of_prefConvex {u : (Fin L → ℝ) → ℝ}
    (h : PrefConvex (nonnegOrthant L) (utilityPref u)) {y z : Fin L → ℝ}
    (hy : y ∈ nonnegOrthant L) (hz : z ∈ nonnegOrthant L) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : min (u y) (u z) ≤ u (a • y + b • z) := by
  rcases le_total (u y) (u z) with hyz | hyz
  · rw [min_eq_left hyz]
    have := h y hy (⟨hy, le_refl (u y)⟩ : y ∈ upperContour _ (utilityPref u) y)
      (⟨hz, hyz⟩ : z ∈ upperContour _ (utilityPref u) y) ha hb hab
    exact this.2
  · rw [min_eq_right hyz]
    have := h z hz (⟨hy, hyz⟩ : y ∈ upperContour _ (utilityPref u) z)
      (⟨hz, le_refl (u z)⟩ : z ∈ upperContour _ (utilityPref u) z) ha hb hab
    exact this.2

/-- `p ≫ 0`, `x ≥ 0` and `x ≠ 0` imply `p·x > 0`. -/
theorem dotProduct_pos_of_strictlyPositive {p x : Fin L → ℝ} (hp : StrictlyPositive p)
    (hx : x ∈ nonnegOrthant L) (hne : x ≠ 0) : 0 < p ⬝ᵥ x := by
  obtain ⟨l, hl⟩ : ∃ l, x l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (funext h)
  have hpos : 0 < p l * x l := mul_pos (hp l) (lt_of_le_of_ne (hx l) (Ne.symm hl))
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => p k * x k)
    (fun k _ => mul_nonneg (hp k).le (hx k)) (Finset.mem_univ l))

/-- `p ≥ 0` and `x ≥ 0` imply `p·x ≥ 0`. -/
theorem dotProduct_nonneg_of_nonneg {p x : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l)
    (hx : x ∈ nonnegOrthant L) : 0 ≤ p ⬝ᵥ x :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (hx l)

/-- `p ≫ 0`, `x ≥ 0` and `p·x ≤ 0` imply `x = 0`. -/
theorem eq_zero_of_dotProduct_nonpos {p x : Fin L → ℝ} (hp : StrictlyPositive p)
    (hx : x ∈ nonnegOrthant L) (h : p ⬝ᵥ x ≤ 0) : x = 0 := by
  by_contra hne
  exact absurd h (not_le.2 (dotProduct_pos_of_strictlyPositive hp hx hne))

/-- The tangent line of a concave function lies above its graph: if `f` is concave on `S` and
differentiable at `a ∈ S`, then `f z ≤ f a + f'(a) (z - a)` for `z ∈ S`. -/
theorem concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} {f' a z : ℝ} (hfc : ConcaveOn ℝ S f)
    (ha : a ∈ S) (hz : z ∈ S) (hf : HasDerivAt f f' a) : f z ≤ f a + f' * (z - a) := by
  rcases lt_trichotomy z a with hlt | heq | hgt
  · have h := hfc.le_slope_of_hasDerivAt hz ha hlt hf
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · rw [heq]; simp
  · have h := hfc.slope_le_of_hasDerivAt ha hz hgt hf
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

end MWG.GeneralEquilibriumExamples
