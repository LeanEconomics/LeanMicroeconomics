/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.RiskAversion
import UtilityForMoney.LocalRiskPremium
import UtilityForMoney.ConstantAbsoluteRisk

/-!
# The Arrow-Pratt coefficient of absolute risk aversion

MWG, Section 6.C, pp. 190-191: Definition 6.C.3, invariance under positive linear
transformations, the probability-premium characterization `r_A(x) = 4π'(0)`, recovery of `u`
from `r_A` up to two constants, and Example 6.C.4 (constant absolute risk aversion).

`arrowPratt u x = -u''(x)/u'(x)` is Kreps's `AbsoluteRiskAversion`. MWG obtains
`r_A(x) = 4π'(0)` by differentiating (6.C.4) twice under the assumption that `π` is
differentiable; we prove the limit form `π(x, ε, u)/ε → r_A(x)/4` as `ε ↓ 0` for every `u`
twice continuously differentiable at `x` with `u'(x) > 0`, without assuming anything about
`π` (and `π(x, 0, u) = 0`, so this is the right derivative of `π` at `0`).
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- **Definition 6.C.3** (MWG, p. 190). The Arrow-Pratt coefficient of absolute risk aversion
`r_A(x, u) = -u''(x)/u'(x)`. -/
noncomputable def arrowPratt (u : ℝ → ℝ) (x : ℝ) : ℝ := -(deriv (deriv u) x) / deriv u x

/-- MWG's coefficient is Kreps's `AbsoluteRiskAversion`. -/
theorem arrowPratt_eq_kreps (u : ℝ → ℝ) (x : ℝ) :
    arrowPratt u x = Kreps.UtilityForMoney.AbsoluteRiskAversion u x := rfl

/-- **p. 190**. The Arrow-Pratt coefficient is invariant under positive (indeed nonzero) linear
transformations `βu + γ` of the Bernoulli utility. -/
theorem arrowPratt_affine_invariant (u : ℝ → ℝ) {β : ℝ} (hβ : β ≠ 0) (γ x : ℝ) :
    arrowPratt (fun y => β * u y + γ) x = arrowPratt u x := by
  have h1 : deriv (fun y => β * u y + γ) = fun y => β * deriv u y := by
    funext y
    rw [deriv_add_const, deriv_const_mul_field]
  have h2 : deriv (fun y => β * deriv u y) x = β * deriv (deriv u) x := deriv_const_mul_field _
  unfold arrowPratt
  rw [h1, h2]
  by_cases hd : deriv u x = 0
  · simp [hd]
  · field_simp

/-- **p. 190**. The second derivative alone is not invariant: `(2u)'' = 2u''`. -/
theorem second_derivative_not_invariant (u : ℝ → ℝ) (x : ℝ) :
    deriv (deriv (fun y => 2 * u y)) x = 2 * deriv (deriv u) x := by
  have h1 : deriv (fun y => 2 * u y) = fun y => 2 * deriv u y := by
    funext y; exact deriv_const_mul_field _
  rw [h1]
  exact deriv_const_mul_field _

/-- **p. 190**. `r_A(x, u) = 4π'(0)`: the probability premium of a small symmetric risk divided
by its size tends to `r_A(x, u)/4`. -/
theorem arrowPratt_eq_four_probPremium_slope {u : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 u x)
    (hp : 0 < deriv u x) :
    Tendsto (fun ε => probPremium u x ε / ε) (𝓝[>] 0) (𝓝 (arrowPratt u x / 4)) := by
  have hq := (Kreps.UtilityForMoney.symmetricUtility_quotient hu).mono_left
    (nhdsGT_le_nhdsNE (0 : ℝ))
  have hd : HasDerivAt u (deriv u x) x :=
    (hu.differentiableAt (by norm_num)).hasDerivAt
  -- the symmetric difference quotient `(u(x+ε) - u(x-ε)) / ε → 2u'(x)`
  have hsym : Tendsto (fun ε : ℝ => (u (x + ε) - u (x - ε)) / ε) (𝓝[>] 0)
      (𝓝 (2 * deriv u x)) := by
    have h1 := hd.tendsto_slope_zero_right
    have h2 := hd.tendsto_slope_zero_left
    have h2' : Tendsto (fun ε : ℝ => ε⁻¹ * (u x - u (x - ε))) (𝓝[>] 0) (𝓝 (deriv u x)) := by
      have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[<] 0) := by
        have := (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero)
        exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (this.mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by simpa using hε)
      have := h2.comp hneg
      refine this.congr' (Eventually.of_forall fun ε => ?_)
      simp only [Function.comp_apply, smul_eq_mul, inv_neg, ← sub_eq_add_neg]
      ring
    have := (h1.add h2')
    simp only [smul_eq_mul] at this
    refine (this.congr' ?_).trans (by rw [two_mul])
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : ε ≠ 0 := (ne_of_gt hε)
    field_simp
    ring
  have hlim := (hq.neg).div hsym (by positivity)
  have hfin : arrowPratt u x / 4 = -(deriv (deriv u) x / 2) / (2 * deriv u x) := by
    unfold arrowPratt; field_simp; ring
  rw [hfin]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply]
  unfold probPremium Kreps.UtilityForMoney.SymmetricUtility
  by_cases hden : u (x + ε) - u (x - ε) = 0
  · simp [hden]
  · field_simp
    ring

/-- **p. 191**. The Bernoulli utility is recovered from `r_A` up to two integration constants:
two utilities with positive marginal utility and the same Arrow-Pratt coefficient on an open
interval differ by a positive linear transformation there. -/
theorem utility_determined_by_arrowPratt {S : Set ℝ} (hS : Convex ℝ S)
    {u v : ℝ → ℝ} (hu1 : ∀ x ∈ S, DifferentiableAt ℝ u x) (hv1 : ∀ x ∈ S, DifferentiableAt ℝ v x)
    (hu2 : ∀ x ∈ S, DifferentiableAt ℝ (deriv u) x) (hv2 : ∀ x ∈ S, DifferentiableAt ℝ (deriv v) x)
    (hup : ∀ x ∈ S, 0 < deriv u x) (hvp : ∀ x ∈ S, 0 < deriv v x)
    (h : ∀ x ∈ S, arrowPratt u x = arrowPratt v x) {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ β > 0, ∃ γ : ℝ, ∀ x ∈ S, v x = β * u x + γ := by
  -- the ratio of marginal utilities is constant
  have hratio (x : ℝ) (hx : x ∈ S) : HasDerivAt (fun y => deriv v y / deriv u y) 0 x := by
    have hd := (hv2 x hx).hasDerivAt.div (hu2 x hx).hasDerivAt (hup x hx).ne'
    convert hd using 1
    have hh := h x hx
    unfold arrowPratt at hh
    rw [div_eq_div_iff (hup x hx).ne' (hvp x hx).ne'] at hh
    have : deriv (deriv v) x * deriv u x - deriv v x * deriv (deriv u) x = 0 := by linarith
    rw [this, zero_div]
  set β := deriv v x₀ / deriv u x₀
  have hβ : 0 < β := div_pos (hvp x₀ hx₀) (hup x₀ hx₀)
  have hconst (x : ℝ) (hx : x ∈ S) : deriv v x = β * deriv u x := by
    have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero hS hratio hx hx₀
    change deriv v x = deriv v x₀ / deriv u x₀ * deriv u x
    rw [← this]
    field_simp [(hup x hx).ne']
  have hdiff (x : ℝ) (hx : x ∈ S) : HasDerivAt (fun y => v y - β * u y) 0 x := by
    convert (hv1 x hx).hasDerivAt.sub ((hu1 x hx).hasDerivAt.const_mul β) using 1
    rw [hconst x hx]; ring
  refine ⟨β, hβ, v x₀ - β * u x₀, fun x hx => ?_⟩
  have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero hS hdiff hx hx₀
  linarith

/-- **Example 6.C.4** (MWG, p. 191). For `u(x) = -e^{-ax}`, `r_A(x, u) = a` at every `x`. -/
theorem example_6_C_4 {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    arrowPratt (fun y => -Real.exp (-a * y)) x = a :=
  Kreps.UtilityForMoney.absoluteRiskAversion_exponential ha x

/-- **Example 6.C.4** (MWG, p. 191). A Bernoulli utility with constant `r_A = a > 0` on an open
interval has the form `u(x) = -αe^{-ax} + β` with `α > 0`. -/
theorem example_6_C_4_general {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty) {u : ℝ → ℝ}
    (h₁ : ∀ x ∈ S, DifferentiableAt ℝ u x) (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv u) x)
    (hp : ∀ x ∈ S, 0 < deriv u x) {a : ℝ} (ha : 0 < a) (hc : ∀ x ∈ S, arrowPratt u x = a) :
    ∃ α > 0, ∃ β : ℝ, ∀ x ∈ S, u x = -α * Real.exp (-a * x) + β := by
  obtain ⟨A, B, hB, h⟩ := Kreps.UtilityForMoney.proposition_6_12_exponential hS hne h₁ h₂ hp ha hc
  refine ⟨B, hB, A, fun x hx => ?_⟩
  rw [h x hx, Kreps.UtilityForMoney.ExponentialUtility]
  ring

end MWG.ChoiceUnderUncertainty
