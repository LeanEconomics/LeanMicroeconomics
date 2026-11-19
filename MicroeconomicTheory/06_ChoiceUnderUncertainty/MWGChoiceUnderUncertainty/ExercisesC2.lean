/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ExercisesC

/-!
# Exercises 6.C.12 and 6.C.18: constant relative risk aversion and square-root utility

MWG, pp. 211-212. Exercise 6.C.12 characterizes constant relative risk aversion on `x > 0`;
two printed statements are corrected (see `ExercisesC` and `docs/corrections.md`): the
strictly increasing CRRA utilities are `βx^{1-ρ}/(1-ρ) + γ` with `β > 0`, and the limit in (c)
holds for `(x^{1-ρ} - 1)/(1-ρ)`. Exercise 6.C.18 computes the Arrow-Pratt coefficients,
certainty equivalents and probability premia of `u(x) = √x`.
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- Second derivatives on `x > 0` only depend on the values there. -/
theorem deriv2_congr_Ioi {u v : ℝ → ℝ} (h : ∀ x > 0, u x = v x) {x : ℝ} (hx : 0 < x) :
    deriv u x = deriv v x ∧ deriv (deriv u) x = deriv (deriv v) x := by
  have he : u =ᶠ[𝓝 x] v := by
    filter_upwards [lt_mem_nhds hx] with y hy using h y hy
  have hd : deriv u =ᶠ[𝓝 x] deriv v := by
    filter_upwards [lt_mem_nhds hx] with y hy
    have he' : u =ᶠ[𝓝 y] v := by
      filter_upwards [lt_mem_nhds hy] with z hz using h z hz
    exact he'.deriv_eq
  exact ⟨he.deriv_eq, hd.deriv_eq⟩

/-- The relative risk aversion of `βx^{1-ρ}/(1-ρ) + γ` is `ρ` on `x > 0`. -/
theorem relativeRiskAversion_crra {ρ β γ : ℝ} (hρ : ρ ≠ 1) (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    relativeRiskAversion (fun y => β * y ^ (1 - ρ) / (1 - ρ) + γ) x = ρ := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hd1 : deriv (fun y => β * y ^ (1 - ρ) / (1 - ρ) + γ) = fun y => β * y ^ (-ρ) := by
    funext y
    rw [deriv_add_const, deriv_div_const, deriv_const_mul_field, Real.deriv_rpow_const]
    rw [show 1 - ρ - 1 = -ρ by ring]
    field_simp
  have hd2 : deriv (fun y => β * y ^ (-ρ)) x = β * (-ρ * x ^ (-ρ - 1)) := by
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
  rw [relativeRiskAversion_eq, hd1, hd2]
  have hp : 0 < x ^ (-ρ) := Real.rpow_pos_of_pos hx _
  have he : x ^ (-ρ - 1) = x ^ (-ρ) / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  rw [he]
  field_simp

/-- The relative risk aversion of `β ln x + γ` is `1` on `x > 0`. -/
theorem relativeRiskAversion_log {β γ : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    relativeRiskAversion (fun y => β * Real.log y + γ) x = 1 := by
  have hd1 : deriv (fun y => β * Real.log y + γ) = fun y => β * y⁻¹ := by
    funext y
    rw [deriv_add_const, deriv_const_mul_field, Real.deriv_log]
  rw [relativeRiskAversion_eq, hd1, deriv_const_mul_field, deriv_inv]
  field_simp

/-- Marginal utility with constant relative risk aversion `ρ` is `c x^{-ρ}`, `c > 0`. -/
theorem marginal_of_constant_relative {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) {ρ : ℝ} (hc : ∀ x > 0, relativeRiskAversion u x = ρ) :
    ∃ c > 0, ∀ x > 0, deriv u x = c * x ^ (-ρ) := by
  have hd2 (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ (deriv u) y :=
    ((hd y hy).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let F := fun x : ℝ => deriv u x * x ^ ρ
  have hF (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt F 0 x := by
    have hx' : (0 : ℝ) < x := hx
    have h := (hd2 x hx').hasDerivAt.mul (Real.hasDerivAt_rpow_const (p := ρ) (Or.inl hx'.ne'))
    convert h using 1
    have hr := hc x hx'
    rw [relativeRiskAversion_eq, div_eq_iff (hp x hx').ne'] at hr
    have he : x ^ (ρ - 1) = x ^ ρ / x := by rw [Real.rpow_sub hx', Real.rpow_one]
    rw [he]
    field_simp
    linear_combination (x ^ ρ) * hr
  refine ⟨deriv u 1, hp 1 one_pos, fun x hx => ?_⟩
  have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero (convex_Ioi 0) hF
    (mem_Ioi.mpr hx) (mem_Ioi.mpr one_pos)
  simp only [F] at this
  have hp' : 0 < x ^ ρ := Real.rpow_pos_of_pos hx _
  rw [Real.one_rpow, mul_one] at this
  rw [Real.rpow_neg hx.le, ← this]
  field_simp

/-- **Exercise 6.C.12(a)** (MWG, p. 211), corrected. A strictly increasing (`u' > 0`), twice
continuously differentiable `u` on `x > 0` has constant relative risk aversion `ρ ≠ 1` iff
`u(x) = βx^{1-ρ}/(1-ρ) + γ` with `β > 0`. -/
theorem exercise_6_C_12a {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) {ρ : ℝ} (hρ : ρ ≠ 1) :
    (∀ x > 0, relativeRiskAversion u x = ρ) ↔
      ∃ β > 0, ∃ γ : ℝ, ∀ x > 0, u x = β * x ^ (1 - ρ) / (1 - ρ) + γ := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  constructor
  · intro hc
    obtain ⟨c, hc0, hu'⟩ := marginal_of_constant_relative hd hp hc
    let G := fun x : ℝ => u x - c * x ^ (1 - ρ) / (1 - ρ)
    have hG (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt G 0 x := by
      have hx' : (0 : ℝ) < x := hx
      have h1 : HasDerivAt u (c * x ^ (-ρ)) x := by
        rw [← hu' x hx']
        exact ((hd x hx').differentiableAt (by norm_num)).hasDerivAt
      have h2 := ((Real.hasDerivAt_rpow_const (p := 1 - ρ) (Or.inl hx'.ne')).const_mul c).div_const
        (1 - ρ)
      convert h1.sub h2 using 1
      rw [show 1 - ρ - 1 = -ρ by ring]
      field_simp
      ring
    refine ⟨c, hc0, G 1, fun x hx => ?_⟩
    have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero (convex_Ioi 0) hG
      (mem_Ioi.mpr hx) (mem_Ioi.mpr one_pos)
    simp only [G] at this
    linarith
  · rintro ⟨β, hβ, γ, he⟩ x hx
    have hcg := deriv2_congr_Ioi he hx
    rw [relativeRiskAversion_eq, hcg.1, hcg.2, ← relativeRiskAversion_eq]
    exact relativeRiskAversion_crra hρ hβ hx

/-- **Exercise 6.C.12(a)**: the printed form fails for `ρ > 1`. Every `βx^{1-ρ} + γ` with
`β > 0` and `ρ > 1` is strictly decreasing on `x > 0`, while `u(x) = -1/x` is strictly
increasing with constant relative risk aversion `2`. -/
theorem exercise_6_C_12a_printed_counterexample :
    (∀ ρ : ℝ, 1 < ρ → ∀ β : ℝ, 0 < β → ∀ γ : ℝ,
      StrictAntiOn (fun x : ℝ => β * x ^ (1 - ρ) + γ) (Ioi 0)) ∧
    StrictMonoOn (fun x : ℝ => -x⁻¹) (Ioi 0) ∧
    ∀ x : ℝ, 0 < x → relativeRiskAversion (fun y : ℝ => -y⁻¹) x = 2 := by
  refine ⟨fun ρ hρ β hβ γ x hx y hy hxy => ?_, fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · have := Real.rpow_lt_rpow_of_neg hx hxy (show 1 - ρ < 0 by linarith)
    simp only
    nlinarith
  · simp only [neg_lt_neg_iff]
    exact (inv_lt_inv₀ hy hx).mpr hxy
  · have he : ∀ y : ℝ, y > 0 → -y⁻¹ = 1 * y ^ (1 - 2 : ℝ) / (1 - 2) + 0 := by
      intro y hy
      rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
      ring
    have hcg := deriv2_congr_Ioi he hx
    rw [relativeRiskAversion_eq, hcg.1, hcg.2, ← relativeRiskAversion_eq]
    exact relativeRiskAversion_crra (by norm_num) one_pos hx

/-- **Exercise 6.C.12(b)** (MWG, p. 211). A strictly increasing, twice continuously
differentiable `u` on `x > 0` has constant relative risk aversion `1` iff
`u(x) = β ln x + γ` with `β > 0`. -/
theorem exercise_6_C_12b {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) :
    (∀ x > 0, relativeRiskAversion u x = 1) ↔
      ∃ β > 0, ∃ γ : ℝ, ∀ x > 0, u x = β * Real.log x + γ := by
  constructor
  · intro hc
    obtain ⟨c, hc0, hu'⟩ := marginal_of_constant_relative hd hp hc
    let G := fun x : ℝ => u x - c * Real.log x
    have hG (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt G 0 x := by
      have hx' : (0 : ℝ) < x := hx
      have h1 : HasDerivAt u (c * x ^ (-1 : ℝ)) x := by
        rw [← hu' x hx']
        exact ((hd x hx').differentiableAt (by norm_num)).hasDerivAt
      convert h1.sub ((Real.hasDerivAt_log hx'.ne').const_mul c) using 1
      rw [Real.rpow_neg_one]; ring
    refine ⟨c, hc0, u 1, fun x hx => ?_⟩
    have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero (convex_Ioi 0) hG
      (mem_Ioi.mpr hx) (mem_Ioi.mpr one_pos)
    simp only [G, Real.log_one, mul_zero, sub_zero] at this
    linarith
  · rintro ⟨β, hβ, γ, he⟩ x hx
    have hcg := deriv2_congr_Ioi he hx
    rw [relativeRiskAversion_eq, hcg.1, hcg.2, ← relativeRiskAversion_eq]
    exact relativeRiskAversion_log hβ hx

/-- **Exercise 6.C.12(c)** (MWG, p. 211), corrected: `(x^{1-ρ} - 1)/(1-ρ) → ln x` as
`ρ → 1`, for every `x > 0`. -/
theorem exercise_6_C_12c {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ρ : ℝ => (x ^ (1 - ρ) - 1) / (1 - ρ)) (𝓝[≠] 1) (𝓝 (Real.log x)) := by
  have hd := (Real.hasStrictDerivAt_const_rpow hx 0).hasDerivAt.tendsto_slope_zero
  simp only [zero_add, Real.rpow_zero, one_mul, smul_eq_mul] at hd
  have hmap : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact sub_ne_zero.mpr (Ne.symm hρ)
  refine (hd.comp hmap).congr' (Eventually.of_forall fun ρ => ?_)
  simp only [Function.comp_apply]
  rw [div_eq_inv_mul]

/-- **Exercise 6.C.12(c)**: the printed limit fails; at `x = 1`, `x^{1-ρ}/(1-ρ) = 1/(1-ρ)` does
not tend to `ln 1 = 0`. -/
theorem exercise_6_C_12c_printed_counterexample :
    ¬Tendsto (fun ρ : ℝ => (1 : ℝ) ^ (1 - ρ) / (1 - ρ)) (𝓝[≠] 1) (𝓝 (Real.log 1)) := by
  intro h
  rw [Real.log_one] at h
  have h1 := h.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
  have h2a : Metric.ball (1 : ℝ) 1 ∈ 𝓝[≠] (1 : ℝ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ one_pos)
  have h2 : ∀ᶠ ρ in 𝓝[≠] (1 : ℝ), ρ ∈ Metric.ball (1 : ℝ) 1 := h2a
  have h3 : ∀ᶠ ρ in 𝓝[≠] (1 : ℝ), ρ ≠ 1 := self_mem_nhdsWithin
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := (h1.and (h2.and h3)).exists
  rw [Metric.mem_ball, Real.dist_eq] at hρ2
  simp only [Real.dist_eq] at hρ1
  simp only [Real.one_rpow, sub_zero] at hρ1
  have hne : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ3)
  have hlt : |1 - ρ| < 1 := by rw [abs_sub_comm]; exact hρ2
  rw [abs_div, abs_one, div_lt_one (abs_pos.mpr hne)] at hρ1
  linarith

end MWG.ChoiceUnderUncertainty
