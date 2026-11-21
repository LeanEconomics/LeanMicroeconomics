/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.HiddenInfo
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exercise 14.C.9 (monopoly insurance)

MWG, Exercise 14.C.9, p. 510.

Wealth `W`, loss `L` with probability `θ`; a contract `(c₁, c₂)` gives wealth `c₁` without and
`c₂` with the loss; the insurer's expected profit is `(1 - θ)(W - c₁) + θ(W - L - c₂)`; the
individual's alternative is no insurance.

* `exercise_14_C_9a`: with `θ` observable the optimal contract is full insurance at the certainty
  equivalent of the endowment, and it is the unique optimum.
* `exercise_14_C_9b`: with `θ ∈ {θ_L, θ_H}` unobservable, written in utility levels
  `x = u(c₁)`, `y = u(c₂)` with `c = φ(·)` (`φ = u⁻¹` convex), a menu satisfying the Kuhn-Tucker
  conditions (with the low-risk participation and high-risk self-selection constraints as the
  only active ones) is optimal; its first-order conditions give full insurance for the high-risk
  type and partial insurance (`c₂ < c₁`) for the low-risk type (`exercise_14_C_9b_shape`). At such
  a contract the low-risk individual is rationed: she would buy more insurance at fair odds
  (`exercise_14_C_9b_rationed`).
* `exercise_14_C_9b_instance`: `u = √c`, `W = 25`, `L = 24`, `θ_L = 1/4`, `θ_H = 1/2`,
  `λ = 1/2`: the optimal menu is `(9, 9)` for the high-risk and `(25, 1)` for the low-risk type.
* Part (c) (comparison with the competitive model of Exercise 13.D.2) is verbal.
-/

namespace MWG.PrincipalAgent

open Set

/-- **Exercise 14.C.9(a)** (MWG, p. 510). With `θ` observable, `u` strictly concave and strictly
increasing, and `c*` the certainty equivalent of the endowment
(`u(c*) = (1 - θ) u(W) + θ u(W - L)`), every contract acceptable to the individual earns at most
`W - θL - c*`, and only full insurance at `c*` attains it. -/
theorem exercise_14_C_9a {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ univ u) (hmono : StrictMono u)
    {θ W L cstar : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hc : u cstar = (1 - θ) * u W + θ * u (W - L)) {c1 c2 : ℝ}
    (hIR : (1 - θ) * u W + θ * u (W - L) ≤ (1 - θ) * u c1 + θ * u c2) :
    (1 - θ) * (W - c1) + θ * (W - L - c2) ≤ W - θ * L - cstar ∧
      ((1 - θ) * (W - c1) + θ * (W - L - c2) = W - θ * L - cstar → c1 = cstar ∧ c2 = cstar) := by
  have hJ := tpa_jensen_two hu.concaveOn (by linarith : 0 ≤ 1 - θ) (by linarith) c1 c2
  have hle : cstar ≤ (1 - θ) * c1 + (1 - (1 - θ)) * c2 :=
    hmono.le_iff_le.1 (by rw [hc]; simp only [sub_sub_cancel] at hJ ⊢; linarith)
  refine ⟨by nlinarith, fun heq => ?_⟩
  have hsum : (1 - θ) * c1 + θ * c2 = cstar := by linarith
  have hc12 : c1 = c2 := by
    by_contra hne
    have hJs := tpa_jensen_two_lt hu (by linarith : 0 < 1 - θ) (by linarith) hne
    simp only [sub_sub_cancel] at hJs
    rw [hsum, hc] at hJs
    linarith
  subst hc12
  constructor <;> linarith

/-- The insurer's expected profit from a type-`θ` individual with utility levels `(x, y)`. -/
def c9Profit (φ : ℝ → ℝ) (W L θ x y : ℝ) : ℝ := W - θ * L - ((1 - θ) * φ x + θ * φ y)

/-- **Exercise 14.C.9(b)** (MWG, p. 510), sufficiency. In utility levels, with `φ` convex and
differentiable (wealth `φ(x)` gives utility `x`), consider menus `(x_L, y_L)`, `(x_H, y_H)` for the
low- and high-risk types (probabilities `λ`, `1 - λ`), subject to the low-risk participation
constraint `(1 - θ_L) x_L + θ_L y_L ≥ r_L` and the high-risk self-selection constraint. If the
candidate satisfies the first-order conditions `(1 - λ) φ'(x_H) = (1 - λ) φ'(y_H) = β`,
`λ (1 - θ_L) φ'(x_L) = α (1 - θ_L) - β (1 - θ_H)`, `λ θ_L φ'(y_L) = α θ_L - β θ_H` with
`α, β ≥ 0` and complementary slackness, then no menu satisfying these two constraints earns more;
in particular it is optimal among all menus satisfying all participation and self-selection
constraints. -/
theorem exercise_14_C_9b {φ dφ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hdφ : ∀ x, HasDerivAt φ (dφ x) x) {W L θL θH lam rL α β : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) {xL yL xH yH : ℝ}
    (fH1 : (1 - lam) * dφ xH = β) (fH2 : (1 - lam) * dφ yH = β)
    (fL1 : lam * ((1 - θL) * dφ xL) = α * (1 - θL) - β * (1 - θH))
    (fL2 : lam * (θL * dφ yL) = α * θL - β * θH)
    (cs1 : α * ((1 - θL) * xL + θL * yL - rL) = 0)
    (cs2 : β * ((1 - θH) * xH + θH * yH - ((1 - θH) * xL + θH * yL)) = 0)
    {xL' yL' xH' yH' : ℝ} (hIR : rL ≤ (1 - θL) * xL' + θL * yL')
    (hIC : (1 - θH) * xL' + θH * yL' ≤ (1 - θH) * xH' + θH * yH')
    (hθH0 : 0 ≤ θH) (hθH1 : θH ≤ 1) (hθL0 : 0 ≤ θL) (hθL1 : θL ≤ 1) :
    lam * c9Profit φ W L θL xL' yL' + (1 - lam) * c9Profit φ W L θH xH' yH' ≤
      lam * c9Profit φ W L θL xL yL + (1 - lam) * c9Profit φ W L θH xH yH := by
  have t1 := tpa_tangent_ge_convex hφ (mem_univ xL) (mem_univ xL') (hdφ xL).hasDerivWithinAt
  have t2 := tpa_tangent_ge_convex hφ (mem_univ yL) (mem_univ yL') (hdφ yL).hasDerivWithinAt
  have t3 := tpa_tangent_ge_convex hφ (mem_univ xH) (mem_univ xH') (hdφ xH).hasDerivWithinAt
  have t4 := tpa_tangent_ge_convex hφ (mem_univ yH) (mem_univ yH') (hdφ yH).hasDerivWithinAt
  have a1 := mul_le_mul_of_nonneg_left t1 (mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1 - θL))
  have a2 := mul_le_mul_of_nonneg_left t2 (mul_nonneg hl0 hθL0)
  have a3 := mul_le_mul_of_nonneg_left t3
    (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (by linarith : (0:ℝ) ≤ 1 - θH))
  have a4 := mul_le_mul_of_nonneg_left t4 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) hθH0)
  have k1 : 0 ≤ α * ((1 - θL) * xL' + θL * yL' - ((1 - θL) * xL + θL * yL)) := by
    have : α * ((1 - θL) * xL' + θL * yL' - rL) ≥ 0 := mul_nonneg hα (by linarith)
    linarith
  have k2 : 0 ≤ β * ((1 - θH) * xH' + θH * yH' - ((1 - θH) * xL' + θH * yL') -
      ((1 - θH) * xH + θH * yH - ((1 - θH) * xL + θH * yL))) := by
    have : β * ((1 - θH) * xH' + θH * yH' - ((1 - θH) * xL' + θH * yL')) ≥ 0 :=
      mul_nonneg hβ (by linarith)
    linarith
  -- the first-order conditions turn the tangent terms into the constraint terms
  have e1 : lam * (1 - θL) * (dφ xL * (xL' - xL)) =
      (α * (1 - θL) - β * (1 - θH)) * (xL' - xL) := by
    rw [← fL1]; ring
  have e2 : lam * θL * (dφ yL * (yL' - yL)) = (α * θL - β * θH) * (yL' - yL) := by
    rw [← fL2]; ring
  have e3 : (1 - lam) * (1 - θH) * (dφ xH * (xH' - xH)) = β * (1 - θH) * (xH' - xH) := by
    rw [← fH1]; ring
  have e4 : (1 - lam) * θH * (dφ yH * (yH' - yH)) = β * θH * (yH' - yH) := by
    rw [← fH2]; ring
  unfold c9Profit
  linarith

/-- **Exercise 14.C.9(b)**, the shape of the solution: the first-order conditions give full
insurance for the high-risk type (`x_H = y_H` when `φ'` is injective) and, with `β > 0`,
`θ_L < θ_H`, `λ > 0` and `φ'` strictly increasing, partial insurance for the low-risk type
(`y_L < x_L`, i.e. `c₂ < c₁`). -/
theorem exercise_14_C_9b_shape {dφ : ℝ → ℝ} (hd : StrictMono dφ) {θL θH lam α β : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (hβ : 0 < β) (hθL0 : 0 < θL) (hθ : θL < θH)
    (hθH1 : θH < 1) {xL yL xH yH : ℝ}
    (fH1 : (1 - lam) * dφ xH = β) (fH2 : (1 - lam) * dφ yH = β)
    (fL1 : lam * ((1 - θL) * dφ xL) = α * (1 - θL) - β * (1 - θH))
    (fL2 : lam * (θL * dφ yL) = α * θL - β * θH) : xH = yH ∧ yL < xL := by
  refine ⟨hd.injective (by nlinarith), ?_⟩
  have key : lam * θL * (1 - θL) * (dφ xL - dφ yL) = β * (θH - θL) := by
    linear_combination θL * fL1 - (1 - θL) * fL2
  have hpos : 0 < lam * θL * (1 - θL) := by
    have : 0 < 1 - θL := by linarith
    positivity
  have : dφ yL < dφ xL := by
    have : 0 < lam * θL * (1 - θL) * (dφ xL - dφ yL) := by
      rw [key]; exact mul_pos hβ (by linarith)
    have := (pos_iff_pos_of_mul_pos this).1 hpos
    linarith
  exact hd.lt_iff_lt.1 this

/-- **Exercise 14.C.9(b)**, rationing: at a partially insured contract (`c₂ < c₁`) a strictly
risk-averse individual with loss probability `θ` gains from more insurance at fair odds: moving
`t > 0` along the fair-odds line `(c₁ - θ t, c₂ + (1 - θ) t)` raises her expected utility at the
margin, since `u'(c₂) > u'(c₁)`. -/
theorem exercise_14_C_9b_rationed {u du : ℝ → ℝ} (hu : StrictConcaveOn ℝ univ u)
    (hdu : ∀ c, HasDerivAt u (du c) c) {θ c1 c2 : ℝ} (h0 : 0 < θ) (h1 : θ < 1) (hc : c2 < c1) :
    0 < (1 - θ) * (du c1 * (-θ)) + θ * (du c2 * (1 - θ)) := by
  have := hi_deriv_anti hu (mem_univ c2) (mem_univ c1) hc (hdu c2).hasDerivWithinAt
    (hdu c1).hasDerivWithinAt
  nlinarith [mul_pos h0 (by linarith : (0:ℝ) < 1 - θ)]

/-- **Exercise 14.C.9(b), an instance** (MWG, p. 510). `u(c) = √c` (`φ(x) = x²`), `W = 25`,
`L = 24`, `θ_L = 1/4`, `θ_H = 1/2`, `λ = 1/2`. The menu with utility levels `(5, 1)` for the
low-risk type (wealth `(25, 1)`: no insurance) and `(3, 3)` for the high-risk type (full insurance
at wealth `9`) satisfies all participation and self-selection constraints and is optimal; the
multipliers are `α = 7`, `β = 3`. -/
theorem exercise_14_C_9b_instance {xL' yL' xH' yH' : ℝ}
    (hIR : 4 ≤ (1 - 1 / 4) * xL' + 1 / 4 * yL')
    (hIC : (1 - 1 / 2) * xL' + 1 / 2 * yL' ≤ (1 - 1 / 2) * xH' + 1 / 2 * yH') :
    1 / 2 * c9Profit (fun x => x ^ 2) 25 24 (1 / 4) xL' yL' +
        (1 - 1 / 2) * c9Profit (fun x => x ^ 2) 25 24 (1 / 2) xH' yH' ≤
      1 / 2 * c9Profit (fun x => x ^ 2) 25 24 (1 / 4) 5 1 +
        (1 - 1 / 2) * c9Profit (fun x => x ^ 2) 25 24 (1 / 2) 3 3 ∧
    -- the candidate satisfies all the constraints (reservation utilities `4` and `3`)
    4 ≤ (1 - 1 / 4) * 5 + 1 / 4 * (1 : ℝ) ∧ 3 ≤ (1 - 1 / 2) * 3 + 1 / 2 * (3 : ℝ) ∧
    (1 - 1 / 2) * 5 + 1 / 2 * (1 : ℝ) ≤ (1 - 1 / 2) * 3 + 1 / 2 * 3 ∧
    (1 - 1 / 4) * 3 + 1 / 4 * (3 : ℝ) ≤ (1 - 1 / 4) * 5 + 1 / 4 * 1 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  refine exercise_14_C_9b (φ := fun x => x ^ 2) (dφ := fun x => 2 * x)
    (by exact (even_two.convexOn_pow (𝕜 := ℝ)))
    (fun x => by simpa using hasDerivAt_pow 2 x) (by norm_num) (by norm_num)
    (α := 7) (β := 3) (rL := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hIR hIC (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end MWG.PrincipalAgent
