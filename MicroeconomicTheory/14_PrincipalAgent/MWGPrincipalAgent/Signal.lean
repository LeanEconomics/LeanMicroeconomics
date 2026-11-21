/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# An additional signal of effort

MWG, Section 14.B (small type), pp. 487-488, condition (14.B.11).

A signal `y` with joint density `f(π, y | e)` is available. Condition (14.B.11) reads
`1 / v'(w(π, y)) = γ + μ [1 - f(π, y | e_L) / f(π, y | e_H)]`.

* `signal_ratio_indep`, `signal_ratio_suffstat`: if `f(π, y | e) = f₁(π | e) f₂(y)`, or more
  generally `f₁(π | e) f₂(y | π)` (`π` a sufficient statistic), the `f₂` terms cancel.
* `signal_foc_indep`: then a scheme satisfying (14.B.11) does not depend on `y`.
* `signal_depends`: conversely, where the likelihood ratio depends on `y`, so do wages.
* `signal_jensen`: the certain payment `w̃(π)` with `v(w̃(π)) = E[v(w(π, y)) | π]` costs at most
  `E[w(π, y) | π]`, strictly less unless `w(π, ·)` is constant.
* `signal_same_utility`, `signal_lower_cost`: integrating over `π` (Fubini), `w̃` gives the
  manager the same expected utility as `w` under every effort and costs the owner no more.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- **p. 487**: with `f(π, y | e) = f₁(π | e) f₂(y)` the likelihood ratio does not involve `y`. -/
theorem signal_ratio_indep (f1L f1H f2 : ℝ) (h2 : f2 ≠ 0) :
    f1L * f2 / (f1H * f2) = f1L / f1H := mul_div_mul_right _ _ h2

/-- **p. 488**: with `f(π, y | e) = f₁(π | e) f₂(y | π)` (`π` a sufficient statistic for `y` with
respect to `e`) the likelihood ratio does not involve `y`. -/
theorem signal_ratio_suffstat (f1 : ℝ → ℝ → ℝ) (f2 : ℝ → ℝ → ℝ) {eL eH x y : ℝ}
    (h2 : f2 y x ≠ 0) : f1 x eL * f2 y x / (f1 x eH * f2 y x) = f1 x eL / f1 x eH :=
  mul_div_mul_right _ _ h2

/-- **(14.B.11)** (MWG, p. 487). If the likelihood ratio at `(π, y)` and `(π, y')` coincides
(as in `signal_ratio_indep`, `signal_ratio_suffstat`) and `v'` is strictly decreasing, a scheme
satisfying (14.B.11) pays the same at `(π, y)` and `(π, y')`. -/
theorem signal_foc_indep {dv : ℝ → ℝ} (hda : StrictAnti dv) {w : ℝ × ℝ → ℝ}
    {r : ℝ × ℝ → ℝ} {γ μ : ℝ} (hfoc : ∀ z, 1 / dv (w z) = γ + μ * (1 - r z)) {x y y' : ℝ}
    (hr : r (x, y) = r (x, y')) : w (x, y) = w (x, y') := by
  have h := (hfoc (x, y)).trans ((hfoc (x, y')).trans (by rw [hr])).symm
  have : dv (w (x, y)) = dv (w (x, y')) := by simpa using h
  exact hda.injective this

/-- **p. 488, the converse direction** (Holmstrom 1979): where the likelihood ratio depends on `y`
and `μ ≠ 0`, a scheme satisfying (14.B.11) depends on `y`. -/
theorem signal_depends {dv : ℝ → ℝ} {w : ℝ × ℝ → ℝ} {r : ℝ × ℝ → ℝ} {γ μ : ℝ} (hμ : μ ≠ 0)
    (hfoc : ∀ z, 1 / dv (w z) = γ + μ * (1 - r z)) {x y y' : ℝ} (hr : r (x, y) ≠ r (x, y')) :
    w (x, y) ≠ w (x, y') := by
  intro h
  have := (hfoc (x, y)).symm.trans ((congrArg (fun t => 1 / dv t) h).trans (hfoc (x, y')))
  apply hr
  have : μ * (r (x, y') - r (x, y)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hμ
  · linarith

/-- **p. 487-488 (Jensen)**: for a fixed profit level, the certain payment `w̃` with
`v(w̃) = ∫ v(w(π, y)) f₂(y) dy` satisfies `w̃ ≤ ∫ w(π, y) f₂(y) dy`, with strict inequality if
`v` is strictly concave and `w(π, ·)` is not almost everywhere constant. -/
theorem signal_jensen {ν : Measure ℝ} {p u : ℝ → ℝ} {v dv : ℝ → ℝ}
    (hv : ConcaveOn ℝ univ v) (hdv : ∀ m, HasDerivAt v (dv m) m) (hmono : StrictMono v)
    (hp0 : ∀ y, 0 < p y) (hp : Integrable p ν) (hp1 : ∫ y, p y ∂ν = 1)
    (hu : Integrable (fun y => u y * p y) ν) (hvu : Integrable (fun y => v (u y) * p y) ν)
    {wt : ℝ} (hwt : v wt = ∫ y, v (u y) * p y ∂ν) :
    wt ≤ ∫ y, u y * p y ∂ν ∧
      (StrictConcaveOn ℝ univ v → ¬ (∀ᵐ y ∂ν, u y = ∫ y, u y * p y ∂ν) →
        wt < ∫ y, u y * p y ∂ν) := by
  have hJ := tpa_jensen hv hdv (fun y => (hp0 y).le) hp hp1 hu hvu
  refine ⟨hmono.le_iff_le.1 (hwt ▸ hJ), fun hsc hne => ?_⟩
  rcases (hmono.le_iff_le.1 (hwt ▸ hJ)).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    exact tpa_jensen_eq hsc hdv hp0 hp hp1 hu hvu (by rw [← hwt, h])

/-- **p. 488**: under `w̃`, defined profit level by profit level by
`v(w̃(π)) = ∫ v(w(π, y)) f₂(y) dy`, the manager's expected utility of income under any effort (with
profit density `f₁`) equals that under `w`. -/
theorem signal_same_utility {ν1 ν2 : Measure ℝ} [SFinite ν1] [SFinite ν2] {v : ℝ → ℝ}
    {w : ℝ × ℝ → ℝ} {wt f1 f2 : ℝ → ℝ}
    (hwt : ∀ x, v (wt x) = ∫ y, v (w (x, y)) * f2 y ∂ν2)
    (hint : Integrable (fun z : ℝ × ℝ => v (w z) * (f1 z.1 * f2 z.2)) (ν1.prod ν2)) :
    ∫ x, v (wt x) * f1 x ∂ν1 = ∫ z, v (w z) * (f1 z.1 * f2 z.2) ∂(ν1.prod ν2) := by
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hwt]
  rw [← integral_mul_const]
  congr 1; funext y; ring

/-- **p. 488**: the owner's expected wage under `w̃` is at most that under `w` (Jensen at each
profit level, then integration over profits). -/
theorem signal_lower_cost {ν1 ν2 : Measure ℝ} [SFinite ν1] [SFinite ν2] {v dv : ℝ → ℝ}
    (hv : ConcaveOn ℝ univ v) (hdv : ∀ m, HasDerivAt v (dv m) m) (hmono : StrictMono v)
    {w : ℝ × ℝ → ℝ} {wt f1 f2 : ℝ → ℝ} (hf1 : ∀ x, 0 ≤ f1 x) (hf2 : ∀ y, 0 < f2 y)
    (hf2i : Integrable f2 ν2) (hf21 : ∫ y, f2 y ∂ν2 = 1)
    (hu : ∀ x, Integrable (fun y => w (x, y) * f2 y) ν2)
    (hvu : ∀ x, Integrable (fun y => v (w (x, y)) * f2 y) ν2)
    (hwt : ∀ x, v (wt x) = ∫ y, v (w (x, y)) * f2 y ∂ν2)
    (hwti : Integrable (fun x => wt x * f1 x) ν1)
    (hint : Integrable (fun z : ℝ × ℝ => w z * (f1 z.1 * f2 z.2)) (ν1.prod ν2)) :
    ∫ x, wt x * f1 x ∂ν1 ≤ ∫ z, w z * (f1 z.1 * f2 z.2) ∂(ν1.prod ν2) := by
  rw [integral_prod _ hint]
  have hin : Integrable (fun x => ∫ y, w (x, y) * (f1 x * f2 y) ∂ν2) ν1 := hint.integral_prod_left
  refine integral_mono hwti hin fun x => ?_
  have hJ := (signal_jensen hv hdv hmono hf2 hf2i hf21 (hu x) (hvu x) (hwt x)).1
  have : ∫ y, w (x, y) * (f1 x * f2 y) ∂ν2 = (∫ y, w (x, y) * f2 y ∂ν2) * f1 x := by
    rw [← integral_mul_const]; congr 1; funext y; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hJ (hf1 x)

end MWG.PrincipalAgent
