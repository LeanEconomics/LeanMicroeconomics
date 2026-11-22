/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.RiskAverse
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-!
# Exercises 14.B.2 and 14.B.3

MWG, p. 507.

* `exercise_14_B_2`: a strictly risk-averse owner with utility `U` of net profit. The first-order
  condition for the optimal scheme implementing `e_H` is
  `U'(π - w(π)) / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]`; with complementary slackness it is
  sufficient (the problem in utility levels is concave); its necessity is
  `exercise_14_B_2_necessary` (`HANecessity`).
* `exercise_14_B_3a`: with normally distributed profits (mean `e`, variance `σ²`) and a linear
  scheme `w = α + βπ`, the manager's mean-variance utility is `α + βe - φβ²σ² - g(e)`.
* `exercise_14_B_3b`: with observable effort the optimal linear contract has `β = 0`,
  `α = ū + g(e*)` and `g'(e*) = 1`.
* `exercise_14_B_3c`, `exercise_14_B_3c_beta`, `exercise_14_B_3c_sigma`: with unobservable effort
  the manager sets `g'(e) = β`; the owner's problem reduces to maximizing
  `e - g(e) - φσ² g'(e)² - ū`; at an interior optimum `β = 1/(1 + 2φσ² g''(e)) ∈ (0, 1)`; and a
  larger `σ²` gives a (weakly) smaller `β`.
-/

namespace MWG.PrincipalAgent

open MeasureTheory ProbabilityTheory Set

namespace HAModel

variable {ε : Type*}

/-- **Exercise 14.B.2** (MWG, p. 507). A risk-averse owner with a concave, nondecreasing,
differentiable utility `U` of net profit `π - w(π)`. If
`U'(π - w(π)) / v'(w(π)) = γ + μ [1 - f(π|e_L)/f(π|e_H)]` at almost every `π` with `γ, μ ≥ 0` and
complementary slackness, then `w` maximizes the owner's expected utility among the schemes
implementing `e_H`. -/
theorem exercise_14_B_2 {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) {U dU : ℝ → ℝ} (hU : ConcaveOn ℝ univ U)
    (hdU : ∀ y, HasDerivAt U (dU y) y) (hdU0 : ∀ y, 0 ≤ dU y) {w : ℝ → ℝ} (hw : M.Adm w)
    {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hfoc : ∀ᵐ x ∂M.ν, dU (x - w x) / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x))
    (hcs1 : γ * (M.EU eH w - M.ubar) = 0) (hcs2 : μ * (M.EU eH w - M.EU eL w) = 0)
    (hUi : ∀ w', M.Adm w' → Integrable (fun x => U (x - w' x) * M.f eH x) M.ν)
    {w' : ℝ → ℝ} (hw' : M.HAFeasible eH w') :
    ∫ x, U (x - w' x) * M.f eH x ∂M.ν ≤ ∫ x, U (x - w x) * M.f eH x ∂M.ν := by
  have hii' := (ha_IC_two hE w').1 hw'.2
  have hi' := hw'.1.2
  have hpt : ∀ᵐ x ∂M.ν, U (x - w' x) * M.f eH x - U (x - w x) * M.f eH x ≤
      -((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
        μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) := by
    filter_upwards [hfoc] with x hx
    have htanv := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
      (hM.v_deriv (w x)).hasDerivWithinAt
    have htanU := tpa_tangent_le hU (mem_univ (x - w x)) (mem_univ (x - w' x))
      (hdU (x - w x)).hasDerivWithinAt
    have hd := hM.dv_pos (w x)
    have hH := hM.f_pos eH x
    have hr : M.f eL x / M.f eH x * M.f eH x = M.f eL x := div_mul_cancel₀ _ hH.ne'
    -- U(π - w') - U(π - w) ≤ U'(π - w)(w - w') ≤ -U'(π - w)(v(w') - v(w))/v'(w)
    have k1 : dU (x - w x) * (w x - w' x) ≤
        -(dU (x - w x) / M.dv (w x)) * (M.v (w' x) - M.v (w x)) := by
      have : M.v (w' x) - M.v (w x) ≤ M.dv (w x) * (w' x - w x) := by linarith
      have h2 : (M.v (w' x) - M.v (w x)) / M.dv (w x) ≤ w' x - w x := by
        rw [div_le_iff₀ hd]; linarith
      have h3 : dU (x - w x) / M.dv (w x) * (M.v (w' x) - M.v (w x)) ≤
          dU (x - w x) * (w' x - w x) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hd]; nlinarith [hdU0 (x - w x)]
      have e1 : dU (x - w x) * (w x - w' x) = -(dU (x - w x) * (w' x - w x)) := by ring
      have e2 : -(dU (x - w x) / M.dv (w x)) * (M.v (w' x) - M.v (w x)) =
          -(dU (x - w x) / M.dv (w x) * (M.v (w' x) - M.v (w x))) := by ring
      rw [e1, e2]; exact neg_le_neg h3
    rw [hx] at k1
    have k2 : U (x - w' x) - U (x - w x) ≤
        -(γ + μ * (1 - M.f eL x / M.f eH x)) * (M.v (w' x) - M.v (w x)) := by
      have : (x - w' x) - (x - w x) = w x - w' x := by ring
      rw [this] at htanU; linarith
    have k3 := mul_le_mul_of_nonneg_right k2 hH.le
    have : -(γ + μ * (1 - M.f eL x / M.f eH x)) * (M.v (w' x) - M.v (w x)) * M.f eH x =
        -((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
          μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) := by
      have : -(γ + μ * (1 - M.f eL x / M.f eH x)) * (M.v (w' x) - M.v (w x)) * M.f eH x =
          -((M.v (w' x) - M.v (w x)) * (γ * M.f eH x + μ * M.f eH x -
            μ * (M.f eL x / M.f eH x * M.f eH x))) := by ring
      rw [this, hr]; ring
    linarith
  have hiH : Integrable (fun x => (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x))
      M.ν := ((hw'.1.1.2 eH).2.sub (hw.2 eH).2).const_mul (γ + μ)
  have hiL : Integrable (fun x => μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) M.ν :=
    ((hw'.1.1.2 eL).2.sub (hw.2 eL).2).const_mul μ
  have hint : ∫ x, (U (x - w' x) * M.f eH x - U (x - w x) * M.f eH x) ∂M.ν ≤
      ∫ x, -((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
        μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) ∂M.ν :=
    integral_mono_ae ((hUi w' hw'.1.1).sub (hUi w hw)) (hiH.sub hiL).neg hpt
  rw [integral_neg, integral_sub hiH hiL, integral_const_mul, integral_const_mul,
    ha_EV_sub hw hw'.1.1, ha_EV_sub hw hw'.1.1, integral_sub (hUi w' hw'.1.1) (hUi w hw)] at hint
  unfold EU at hi' hii' hcs1 hcs2
  have h1 : 0 ≤ γ * (M.EV eH w' - M.g eH - M.ubar) := mul_nonneg hγ (by linarith)
  have h2 : 0 ≤ μ * (M.EV eH w' - M.g eH - (M.EV eL w' - M.g eL)) := mul_nonneg hμ (by linarith)
  nlinarith

end HAModel

/-- **Exercise 14.B.3(a)** (MWG, p. 507). If profits are normal with mean `e` and variance `σ²`,
the linear scheme `w = α + βπ` has mean `α + βe` and variance `β²σ²`, so the manager's utility
`E[w] - φ Var(w) - g(e)` is `α + βe - φβ²σ² - g(e)`. -/
theorem exercise_14_B_3a (α β e φ : ℝ) (σ2 : NNReal) (g : ℝ → ℝ) :
    (∫ x, (α + β * x) ∂gaussianReal e σ2) - φ * Var[fun x => α + β * x; gaussianReal e σ2] -
      g e = α + β * e - φ * β ^ 2 * σ2 - g e := by
  have hint : Integrable (fun x : ℝ => x) (gaussianReal e σ2) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [integral_add (integrable_const α) (hint.const_mul β), integral_const, integral_const_mul,
    integral_id_gaussianReal, variance_const_add (by fun_prop),
    variance_const_mul, variance_fun_id_gaussianReal]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **Exercise 14.B.3(b)** (MWG, p. 507). With observable effort the owner maximizes
`e - (α + βe)` subject to `α + βe - φβ²σ² - g(e) ≥ ū` (`φσ² > 0`). If `g` is convex on `[0, ∞)` with
`g'(e*) = 1` at `e* ≥ 0`, the optimal contract is `e*`, `β = 0`, `α = ū + g(e*)`: every feasible
contract gives at most `e* - g(e*) - ū`, and only `β = 0` with a binding constraint and an effort
maximizing `e - g(e)` attains it. -/
theorem exercise_14_B_3b {g dg : ℝ → ℝ} (hg : ConvexOn ℝ (Ici 0) g)
    (hdg : ∀ e, 0 ≤ e → HasDerivWithinAt g (dg e) (Ici 0) e) {φσ2 ubar estar : ℝ}
    (hφ : 0 < φσ2) (hes : 0 ≤ estar) (hfoc : dg estar = 1) {e α β : ℝ} (he : 0 ≤ e)
    (hpart : ubar ≤ α + β * e - φσ2 * β ^ 2 - g e) :
    e - (α + β * e) ≤ estar - g estar - ubar ∧
      (e - (α + β * e) = estar - g estar - ubar → β = 0) := by
  have htan := tpa_tangent_ge_convex hg (mem_Ici.2 hes) (mem_Ici.2 he) (hdg estar hes)
  rw [hfoc] at htan
  have hb := sq_nonneg β
  refine ⟨by nlinarith, fun heq => ?_⟩
  have : φσ2 * β ^ 2 ≤ 0 := by nlinarith
  have : β ^ 2 = 0 := le_antisymm (by nlinarith) hb
  exact pow_eq_zero_iff (by norm_num) |>.1 this

/-- **Exercise 14.B.3(c)** (MWG, p. 507), the manager's choice and the reduced problem. Under a
linear scheme with `β`, the manager's effort `e > 0` (maximizing `α + βe - φβ²σ² - g(e)`) satisfies
`g'(e) = β`; given this, the owner's profit with the participation constraint binding is
`e - g(e) - φσ² g'(e)² - ū`. -/
theorem exercise_14_B_3c {g dg : ℝ → ℝ} {φσ2 ubar α β e : ℝ} (he : 0 < e)
    (hdg : HasDerivAt g (dg e) e)
    (hopt : ∀ e', 0 ≤ e' → α + β * e' - φσ2 * β ^ 2 - g e' ≤ α + β * e - φσ2 * β ^ 2 - g e)
    (hbind : α + β * e - φσ2 * β ^ 2 - g e = ubar) :
    dg e = β ∧ e - (α + β * e) = e - g e - φσ2 * dg e ^ 2 - ubar := by
  have hloc : IsLocalMax (fun e' => α + β * e' - φσ2 * β ^ 2 - g e') e :=
    Filter.mem_of_superset (Ici_mem_nhds he) fun y hy => hopt y hy
  have hd : HasDerivAt (fun e' => α + β * e' - φσ2 * β ^ 2 - g e') (β * 1 - dg e) e :=
    ((((hasDerivAt_id e).const_mul β).const_add α).sub_const (φσ2 * β ^ 2)).sub hdg
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hβ : dg e = β := by linarith
  refine ⟨hβ, ?_⟩
  rw [hβ]; linarith

/-- **Exercise 14.B.3(c)**, the optimal `β` (MWG, p. 507). If `e > 0` maximizes
`h(e) = e - g(e) - φσ² g'(e)² - ū` with `g'' > 0`, `g' ≥ 0` and `φσ² > 0`, then
`β = g'(e) = 1/(1 + 2φσ² g''(e))`, so `0 < β < 1` when `g''(e) > 0`. -/
theorem exercise_14_B_3c_beta {g dg d2g : ℝ → ℝ} {φσ2 ubar e : ℝ} (he : 0 < e) (hφ : 0 < φσ2)
    (hdg : HasDerivAt g (dg e) e) (hd2g : HasDerivAt dg (d2g e) e) (hd2 : 0 < d2g e)
    (hmax : ∀ e', 0 ≤ e' → e' - g e' - φσ2 * dg e' ^ 2 - ubar ≤ e - g e - φσ2 * dg e ^ 2 - ubar) :
    dg e = 1 / (1 + 2 * φσ2 * d2g e) ∧ 0 < dg e ∧ dg e < 1 := by
  have hloc : IsLocalMax (fun e' => e' - g e' - φσ2 * dg e' ^ 2 - ubar) e :=
    Filter.mem_of_superset (Ici_mem_nhds he) fun y hy => hmax y hy
  have hd : HasDerivAt (fun e' => e' - g e' - φσ2 * dg e' ^ 2 - ubar)
      (1 - dg e - φσ2 * (2 * dg e * d2g e)) e := by
    have h1 := ((hasDerivAt_id e).sub hdg).sub ((hd2g.pow 2).const_mul φσ2)
    have := h1.sub_const ubar
    convert this using 1
    all_goals norm_num
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hpos : 0 < 1 + 2 * φσ2 * d2g e := by positivity
  have heq : dg e = 1 / (1 + 2 * φσ2 * d2g e) := by
    rw [eq_div_iff hpos.ne']; linarith
  refine ⟨heq, by rw [heq]; positivity, ?_⟩
  rw [heq, div_lt_one hpos]; nlinarith

/-- **Exercise 14.B.3(c)**, the effect of `σ²` (MWG, p. 507). If `e₁` maximizes
`e - g(e) - φσ₁² g'(e)²` and `e₂` maximizes `e - g(e) - φσ₂² g'(e)²` with `σ₁² < σ₂²` and `g' ≥ 0`,
then the incentive intensities satisfy `β₂ = g'(e₂) ≤ β₁ = g'(e₁)`: more noise, weaker
incentives. -/
theorem exercise_14_B_3c_sigma {g dg : ℝ → ℝ} {k1 k2 e1 e2 : ℝ} (hk : k1 < k2)
    (hdg0 : ∀ e, 0 ≤ e → 0 ≤ dg e) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hm1 : ∀ e, 0 ≤ e → e - g e - k1 * dg e ^ 2 ≤ e1 - g e1 - k1 * dg e1 ^ 2)
    (hm2 : ∀ e, 0 ≤ e → e - g e - k2 * dg e ^ 2 ≤ e2 - g e2 - k2 * dg e2 ^ 2) :
    dg e2 ≤ dg e1 := by
  have a := hm1 e2 he2
  have b := hm2 e1 he1
  have hsq : dg e2 ^ 2 ≤ dg e1 ^ 2 := by nlinarith
  by_contra hc
  rw [not_le] at hc
  nlinarith [hdg0 e1 he1, hdg0 e2 he2]

end MWG.PrincipalAgent
