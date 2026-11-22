/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.UtilityPossibility
import MWGWelfareBargaining.SocialWelfare
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Second-best problems

MWG, Section 22.B, pp. 819-824: the general first-order conditions of the Ramsey problem
(Example 22.B.2, Exercise 22.B.2), the compensatory distortion (Example 22.B.3,
Exercise 22.B.3), the few-instruments utility possibility set (Example 22.B.4, Exercise 22.B.4),
convexification by randomization (p. 823) and unproductive taxation (Example 22.B.6 with
footnote 7).

* `exercise_22_B_2`: at a solution of `max S₁(p₁) + S₂(p₂)` s.t. `∑ (pₗ - 1)xₗ(pₗ) ≥ R` (binding,
  with a nonvanishing constraint gradient) there is a multiplier `λ ≥ 0` with
  `λ(p̄ₗ - 1)xₗ'(p̄ₗ) = (1 - λ)xₗ(p̄ₗ)`. The existence of the multiplier is Mathlib's Lagrange
  multiplier theorem (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`); its sign comes
  from moving along the constraint gradient. `exercise_22_B_2_ramsey`: with `xₗ > 0`,
  `xₗ' < 0` and `R > 0`, `λ > 1` and (22.B.1) holds with `α = (λ - 1)/λ ∈ (0, 1)`. This is the
  corrected sign of correction 1 (the book prints `λ < 0`).
* `exercise_22_B_3`: (22.B.2), and the compensatory distortion `p̄₂ ≠ 1`.
* `exercise_22_B_4`: an explicit quasilinear economy whose second-best utility possibility set
  is not convex; `example_22_B_4_frontier`: its Pareto frontier lies on the one-parameter
  curve `p₂ ↦ (v₁(p₂) + (p₂ - 1)∑ xᵢ(p₂), v₂(p₂), …)`.
* `randomized_convex`: the ex ante utility possibility set of lotteries over policies is the
  convex hull of the deterministic one, hence convex.
* `example_22_B_6`: unproductive taxation with `u₁ = x₂₁ + a ln x₁₁`, `u₂ = x₂₂`: the locus `Q`
  is not monotone (it contains Pareto-dominated points), and only `t = 0` attains the
  first-best frontier (footnote 7).
-/

namespace MWG.WelfareBargaining


/-! ### Example 22.B.2 and Exercise 22.B.2: the Ramsey first-order conditions -/

open Filter Topology in
/-- **Exercise 22.B.2** (MWG, pp. 820, 850). Let `S₁, S₂` be the consumer surpluses of the
separable demands `x₁, x₂` (`Sₗ' = -xₗ`, Roy's identity) and let `p̄` maximize
`S₁(p₁) + S₂(p₂)` locally subject to the revenue constraint `∑ (pₗ - 1)xₗ(pₗ) ≥ R`, with the
constraint binding and its gradient `(xₗ + (p̄ₗ - 1)xₗ')ₗ` nonzero. Then there is `λ ≥ 0` with
`λ(p̄ₗ - 1)xₗ'(p̄ₗ) = (1 - λ)xₗ(p̄ₗ)` for both goods. -/
theorem exercise_22_B_2 {x₁ x₂ S₁ S₂ : ℝ → ℝ} {p₁ p₂ x₁' x₂' R : ℝ}
    (hS₁ : HasStrictDerivAt S₁ (-x₁ p₁) p₁) (hS₂ : HasStrictDerivAt S₂ (-x₂ p₂) p₂)
    (hx₁ : HasStrictDerivAt x₁ x₁' p₁) (hx₂ : HasStrictDerivAt x₂ x₂' p₂)
    (hmax : IsLocalMaxOn (fun p : ℝ × ℝ => S₁ p.1 + S₂ p.2)
      {p | R ≤ (p.1 - 1) * x₁ p.1 + (p.2 - 1) * x₂ p.2} (p₁, p₂))
    (hbind : (p₁ - 1) * x₁ p₁ + (p₂ - 1) * x₂ p₂ = R)
    (hCQ : x₁ p₁ + (p₁ - 1) * x₁' ≠ 0 ∨ x₂ p₂ + (p₂ - 1) * x₂' ≠ 0) :
    ∃ l : ℝ, 0 ≤ l ∧ l * (p₁ - 1) * x₁' = (1 - l) * x₁ p₁ ∧
      l * (p₂ - 1) * x₂' = (1 - l) * x₂ p₂ := by
  set G₁ := x₁ p₁ + (p₁ - 1) * x₁' with hG₁
  set G₂ := x₂ p₂ + (p₂ - 1) * x₂' with hG₂
  set v : ℝ × ℝ → ℝ := fun p => S₁ p.1 + S₂ p.2 with hv
  set g : ℝ × ℝ → ℝ := fun p => (p.1 - 1) * x₁ p.1 + (p.2 - 1) * x₂ p.2 with hg
  have hh₁ : HasStrictDerivAt (fun t => (t - 1) * x₁ t) G₁ p₁ := by
    have h1 : HasStrictDerivAt (fun t : ℝ => t - 1) 1 p₁ := (hasStrictDerivAt_id p₁).sub_const 1
    simpa using h1.fun_mul hx₁
  have hh₂ : HasStrictDerivAt (fun t => (t - 1) * x₂ t) G₂ p₂ := by
    have h1 : HasStrictDerivAt (fun t : ℝ => t - 1) 1 p₂ := (hasStrictDerivAt_id p₂).sub_const 1
    simpa using h1.fun_mul hx₂
  have hc₁ : HasStrictFDerivAt (fun p : ℝ × ℝ => (p.1 - 1) * x₁ p.1)
      (G₁ • ContinuousLinearMap.fst ℝ ℝ ℝ) (p₁, p₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (p₁, p₂) hh₁
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (p₁, p₂)))
    exact h
  have hc₂ : HasStrictFDerivAt (fun p : ℝ × ℝ => (p.2 - 1) * x₂ p.2)
      (G₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (p₁, p₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (p₁, p₂) hh₂
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (p₁, p₂)))
    exact h
  have hd₁ : HasStrictFDerivAt (fun p : ℝ × ℝ => S₁ p.1)
      ((-x₁ p₁) • ContinuousLinearMap.fst ℝ ℝ ℝ) (p₁, p₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (p₁, p₂) hS₁
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (p₁, p₂)))
    exact h
  have hd₂ : HasStrictFDerivAt (fun p : ℝ × ℝ => S₂ p.2)
      ((-x₂ p₂) • ContinuousLinearMap.snd ℝ ℝ ℝ) (p₁, p₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (p₁, p₂) hS₂
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (p₁, p₂)))
    exact h
  have hgd : HasStrictFDerivAt g (G₁ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      G₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (p₁, p₂) := hc₁.add hc₂
  have hvd : HasStrictFDerivAt v ((-x₁ p₁) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (-x₂ p₂) • ContinuousLinearMap.snd ℝ ℝ ℝ) (p₁, p₂) := hd₁.add hd₂
  have hext : IsLocalExtrOn v {p | g p = g (p₁, p₂)} (p₁, p₂) :=
    Or.inr (hmax.mono fun p (hp : g p = g (p₁, p₂)) => by
      change R ≤ g p
      rw [hp]
      exact hbind.ge)
  obtain ⟨a, b, hab, hlin⟩ := hext.exists_multipliers_of_hasStrictFDerivAt_1d hgd hvd
  have e1 := congrArg (fun L => L (1, 0)) hlin
  have e2 := congrArg (fun L => L (0, 1)) hlin
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    zero_apply] at e1 e2
  -- `b ≠ 0`, otherwise the constraint gradient vanishes
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := fun ha => hab (by simp [ha])
    rcases hCQ with h | h
    · exact h (by
        have : a * G₁ = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left ha)
    · exact h (by
        have : a * G₂ = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left ha)
  set μ := a / b with hμ
  have hx₁G : x₁ p₁ = μ * G₁ := by
    rw [hμ]; field_simp; linarith
  have hx₂G : x₂ p₂ = μ * G₂ := by
    rw [hμ]; field_simp; linarith
  refine ⟨μ, ?_, ?_, ?_⟩
  · -- the sign: moving along the constraint gradient keeps the constraint and would raise
    -- the surplus if `μ < 0`
    by_contra hneg
    have hneg : μ < 0 := not_le.1 hneg
    have hGpos : 0 < G₁ ^ 2 + G₂ ^ 2 := by
      rcases hCQ with h | h
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    set L : ℝ → ℝ × ℝ := fun t => (p₁, p₂) + t • (G₁, G₂) with hL
    have hLd : HasDerivAt L (G₁, G₂) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const (G₁, G₂)).const_add (p₁, p₂)
      simpa [hL] using this
    have hL0 : L 0 = (p₁, p₂) := by simp [hL]
    have hφ : HasDerivAt (v ∘ L) (-(μ * (G₁ ^ 2 + G₂ ^ 2))) 0 := by
      have := (hL0 ▸ hvd.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hLd
      convert this using 1
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, hx₁G, hx₂G]
      ring
    have hψ : HasDerivAt (g ∘ L) (G₁ ^ 2 + G₂ ^ 2) 0 := by
      have := (hL0 ▸ hgd.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hLd
      convert this using 1
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      ring
    have hφpos : 0 < -(μ * (G₁ ^ 2 + G₂ ^ 2)) := by nlinarith
    have t1 := (hφ.tendsto_slope_zero_right).eventually (lt_mem_nhds hφpos)
    have t2 := (hψ.tendsto_slope_zero_right).eventually (lt_mem_nhds hGpos)
    have hLc : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (p₁, p₂)) :=
      hL0 ▸ (hLd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have t3 := hLc.eventually (eventually_nhdsWithin_iff.1 hmax)
    obtain ⟨t, ⟨h1, h2, h3⟩, ht⟩ :=
      ((t1.and (t2.and t3)).and self_mem_nhdsWithin).exists
    have ht' : (0 : ℝ) < t := ht
    simp only [zero_add, smul_eq_mul, Function.comp] at h1 h2
    rw [hL0] at h1 h2
    have hg0 : g (p₁, p₂) = R := hbind
    have hti : 0 < t⁻¹ := inv_pos.2 ht'
    have hv' : v (p₁, p₂) < v (L t) := by
      have := (pos_of_mul_pos_right h1 hti.le); linarith
    have hg' : R < g (L t) := by
      have := (pos_of_mul_pos_right h2 hti.le); linarith
    exact absurd (h3 hg'.le) (not_le.2 hv')
  · linear_combination -hx₁G - μ * hG₁
  · linear_combination -hx₂G - μ * hG₂

/-- **Example 22.B.2** (MWG, p. 820), the Ramsey formula from the first-order conditions. If
`λ ≥ 0` satisfies the conditions of `exercise_22_B_2`, demands are positive and downward
sloping and the required revenue is positive, then `λ > 1` and, with `tₗ = (p̄ₗ - 1)/p̄ₗ`, the
elasticities `εₗ = -p̄ₗxₗ'/xₗ` and `α = (λ - 1)/λ ∈ (0, 1)`, (22.B.1) holds:
`tₗ = α/εₗ`. -/
theorem exercise_22_B_2_ramsey {p₁ p₂ x₁ x₂ x₁' x₂' R l : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hd₁ : x₁' < 0) (hd₂ : x₂' < 0) (hR : 0 < R)
    (hbind : (p₁ - 1) * x₁ + (p₂ - 1) * x₂ = R) (hl : 0 ≤ l)
    (h₁ : l * (p₁ - 1) * x₁' = (1 - l) * x₁) (h₂ : l * (p₂ - 1) * x₂' = (1 - l) * x₂) :
    1 < l ∧ 0 < (l - 1) / l ∧ (l - 1) / l < 1 ∧
      (p₁ - 1) / p₁ = (l - 1) / l / (-p₁ * x₁' / x₁) ∧
      (p₂ - 1) / p₂ = (l - 1) / l / (-p₂ * x₂' / x₂) := by
  have hl1 : 1 < l := by
    by_contra h
    have h : l ≤ 1 := not_lt.1 h
    rcases hl.lt_or_eq with hl0 | hl0
    · -- `l(p - 1)x' = (1 - l)x ≥ 0` forces `p ≤ 1` for both goods
      have e₁ : (p₁ - 1) * x₁' ≥ 0 := by
        have : l * ((p₁ - 1) * x₁') ≥ 0 := by nlinarith
        exact (mul_nonneg_iff_of_pos_left hl0).1 this
      have e₂ : (p₂ - 1) * x₂' ≥ 0 := by
        have : l * ((p₂ - 1) * x₂') ≥ 0 := by nlinarith
        exact (mul_nonneg_iff_of_pos_left hl0).1 this
      have q₁ : p₁ - 1 ≤ 0 := by nlinarith
      have q₂ : p₂ - 1 ≤ 0 := by nlinarith
      nlinarith
    · subst hl0; simp at h₁; linarith
  have hl0 : 0 < l := by linarith
  refine ⟨hl1, div_pos (by linarith) hl0, (div_lt_one hl0).2 (by linarith), ?_, ?_⟩
  · have hp₁x : 0 < -p₁ * x₁' := by nlinarith
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (by positivity),
      div_mul_eq_mul_div, div_eq_iff hp₁.ne']
    field_simp
    linear_combination -h₁
  · have hp₂x : 0 < -p₂ * x₂' := by nlinarith
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (by positivity),
      div_mul_eq_mul_div, div_eq_iff hp₂.ne']
    field_simp
    linear_combination -h₂

/-- **Exercise 22.B.2**, a concrete instance of the hypotheses (MWG, p. 820): demands
`xₗ(p) = 2 - p`, surpluses `(2 - p)²/2`, unit cost, `R = 3/8`; the optimum `p̄ = (5/4, 5/4)`
(`example_22_B_2_correction`) satisfies the conditions, with multiplier `λ = 3/2 > 1`. -/
theorem exercise_22_B_2_instance :
    ∃ l : ℝ, 0 ≤ l ∧ l * (5 / 4 - 1) * (-1) = (1 - l) * (2 - 5 / 4) ∧
      l * (5 / 4 - 1) * (-1) = (1 - l) * (2 - 5 / 4) := by
  have hS : HasStrictDerivAt ramseyCS (-(fun p : ℝ => 2 - p) (5 / 4)) (5 / 4) := by
    have h := (((hasStrictDerivAt_id (5 / 4 : ℝ)).const_sub 2).pow 2).div_const 2
    convert h using 1
    · funext p; simp [ramseyCS]
    · simp; norm_num
  have hx : HasStrictDerivAt (fun p : ℝ => 2 - p) (-1) (5 / 4) := by
    simpa using (hasStrictDerivAt_id (5 / 4 : ℝ)).const_sub 2
  refine exercise_22_B_2 (R := 3 / 8) hS hS hx hx ?_ (by norm_num) (Or.inl (by norm_num))
  have hmax : IsMaxOn (fun p : ℝ × ℝ => ramseyCS p.1 + ramseyCS p.2)
      {p | 3 / 8 ≤ (p.1 - 1) * (2 - p.1) + (p.2 - 1) * (2 - p.2)} (5 / 4, 5 / 4) :=
    fun p hp => example_22_B_2_correction.2.1 p.1 p.2 hp
  exact hmax.isLocalMaxOn

/-! ### Example 22.B.3 and Exercise 22.B.3: compensatory distortion -/

/-- **Exercise 22.B.3** (MWG, pp. 820-821, 850), (22.B.2). With `q₁` fixed, let `CS(p₂)` be the
consumer surplus as a function of `p₂` (`CS' = -x₂`, Roy's identity) and `x₁(p₂) = x₁(q₁, p₂)`,
`x₂(p₂) = x₂(q₁, p₂)`. The total surplus `CS + (q₁ - 1)x₁ + (p₂ - 1)x₂` (tax revenue returned
lump sum) has a local maximum at `p̄₂` only if
`(q₁ - 1)∂x₁/∂p₂ + (p̄₂ - 1)∂x₂/∂p₂ = 0`. -/
theorem exercise_22_B_3 {CS x₁ x₂ : ℝ → ℝ} {q₁ p₂ d₁ d₂ : ℝ}
    (hCS : HasDerivAt CS (-x₂ p₂) p₂) (hx₁ : HasDerivAt x₁ d₁ p₂) (hx₂ : HasDerivAt x₂ d₂ p₂)
    (hmax : IsLocalMax (fun q => CS q + (q₁ - 1) * x₁ q + (q - 1) * x₂ q) p₂) :
    (q₁ - 1) * d₁ + (p₂ - 1) * d₂ = 0 := by
  have h1 : HasDerivAt (fun q : ℝ => q - 1) 1 p₂ := (hasDerivAt_id p₂).sub_const 1
  have hd := (hCS.add (hx₁.const_mul (q₁ - 1))).add (h1.fun_mul hx₂)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **Example 22.B.3** (MWG, p. 821). Except in the separable case `∂x₁/∂p₂ = 0`, the
second-best price of good 2 differs from marginal cost: a compensatory distortion. -/
theorem example_22_B_3 {CS x₁ x₂ : ℝ → ℝ} {q₁ p₂ d₁ d₂ : ℝ} (hq₁ : 1 < q₁) (hd₁ : d₁ ≠ 0)
    (hCS : HasDerivAt CS (-x₂ p₂) p₂) (hx₁ : HasDerivAt x₁ d₁ p₂) (hx₂ : HasDerivAt x₂ d₂ p₂)
    (hmax : IsLocalMax (fun q => CS q + (q₁ - 1) * x₁ q + (q - 1) * x₂ q) p₂) : p₂ ≠ 1 := by
  intro h
  have := exercise_22_B_3 hCS hx₁ hx₂ hmax
  rw [h, sub_self, zero_mul, add_zero] at this
  rcases mul_eq_zero.1 this with h' | h'
  · linarith
  · exact hd₁ h'

/-- **Example 22.B.3**, a concrete instance (MWG, p. 821). The quasilinear demands
`x₁ = 3 - p₁ + p₂/2`, `x₂ = 1 - p₂ + p₁/2` (substitutes) with `q₁ = 2`: as functions of `p₂`,
`x₁ = 1 + p₂/2`, `x₂ = 2 - p₂` and `CS = (2 - p₂)²/2` up to a constant. The total surplus
`1 + 3p₂/2 - p₂²/2` is maximized at `p̄₂ = 3/2 ≠ 1`, and (22.B.2) holds there. -/
theorem example_22_B_3_instance :
    IsLocalMax (fun q : ℝ => (2 - q) ^ 2 / 2 + (2 - 1) * (1 + q / 2) + (q - 1) * (2 - q))
      (3 / 2) ∧ (2 - 1) * (1 / 2 : ℝ) + (3 / 2 - 1) * (-1) = 0 ∧ (3 / 2 : ℝ) ≠ 1 := by
  refine ⟨IsMaxOn.isLocalMax (fun (q : ℝ) _ => ?_) Filter.univ_mem, by norm_num, by norm_num⟩
  change (2 - q) ^ 2 / 2 + (2 - 1) * (1 + q / 2) + (q - 1) * (2 - q) ≤
    (2 - 3 / 2) ^ 2 / 2 + (2 - 1) * (1 + 3 / 2 / 2) + (3 / 2 - 1) * (2 - 3 / 2)
  nlinarith [sq_nonneg (q - 3 / 2)]

/-! ### Example 22.B.4 and Exercise 22.B.4: few policy instruments -/

/-- **Example 22.B.4** (MWG, p. 821). The second-best utility possibility set of a quasilinear
economy with a single instrument, the price `p₂ > 0` of good 2 (marginal cost `1`), the
surplus or deficit being absorbed by consumer `i₀`:
`U = {u : u ≤ (v_{i₀}(p₂) + (p₂ - 1)∑ᵢ xᵢ(p₂), (vᵢ(p₂))_{i ≠ i₀}) for some p₂ > 0}`. -/
def secondBestUPS {n : ℕ} (i₀ : Fin n) (v x : Fin n → ℝ → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ p : ℝ, 0 < p ∧ ∀ i, u i ≤ if i = i₀ then v i p + (p - 1) * ∑ j, x j p else v i p}

/-- **Example 22.B.4** (MWG, pp. 821-822, Figure 22.B.4). The Pareto frontier of the second-best
utility possibility set lies on the curve parametrized by the single instrument `p₂`: with
fewer than `I - 1` instruments it cannot be `(I - 1)`-dimensional. -/
theorem example_22_B_4_frontier {n : ℕ} (i₀ : Fin n) (v x : Fin n → ℝ → ℝ) {u : Fin n → ℝ}
    (hu : IsParetoFrontier (secondBestUPS i₀ v x) u) :
    ∃ p > 0, u = fun i => if i = i₀ then v i p + (p - 1) * ∑ j, x j p else v i p := by
  obtain ⟨⟨p, hp, hle⟩, hno⟩ := hu
  refine ⟨p, hp, funext fun i => ?_⟩
  by_contra hne
  exact hno ⟨_, ⟨p, hp, fun j => le_rfl⟩, hle, i, lt_of_le_of_ne (hle i) hne⟩

/-- The demand for good 2 of the unit-demand consumer of `exercise_22_B_4`: one unit if
`p₂ < 1/2`. -/
noncomputable def unitDemand (p : ℝ) : ℝ := if p < 1 / 2 then 1 else 0

/-- **Exercise 22.B.4**, the demand side (MWG, p. 850). For the quasilinear utility
`m + (1/2)·min(y, 1)` and `p₂ > 0`, buying `unitDemand p₂` units is optimal and the indirect
utility (net of wealth) is `max(1/2 - p₂, 0)`. -/
theorem exercise_22_B_4_demand {p : ℝ} (hp : 0 < p) :
    IsGreatest ((fun y => 1 / 2 * min y 1 - p * y) '' Set.Ici 0) (max (1 / 2 - p) 0) ∧
      1 / 2 * min (unitDemand p) 1 - p * unitDemand p = max (1 / 2 - p) 0 := by
  have hval : 1 / 2 * min (unitDemand p) 1 - p * unitDemand p = max (1 / 2 - p) 0 := by
    unfold unitDemand
    split_ifs with h
    · rw [max_eq_left (by linarith)]; norm_num
    · rw [max_eq_right (by linarith)]; norm_num
  refine ⟨⟨⟨unitDemand p, by unfold unitDemand; split_ifs <;> norm_num, hval⟩, ?_⟩, hval⟩
  rintro _ ⟨y, hy, rfl⟩
  simp only [Set.mem_Ici] at hy
  change 1 / 2 * min y 1 - p * y ≤ _
  rcases le_total y 1 with h | h
  · rw [min_eq_left h]
    rcases le_total p (1 / 2) with hp' | hp'
    · rw [max_eq_left (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith)]; nlinarith
  · rw [min_eq_right h]
    rcases le_total p (1 / 2) with hp' | hp'
    · rw [max_eq_left (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith)]; nlinarith

/-- **Exercise 22.B.4** (MWG, pp. 821, 850, Figure 22.B.3). The second-best utility possibility
set may not be convex. Consumer 1 has wealth `1` and no demand for good 2 and absorbs the
surplus; consumer 2 has the unit demand of `exercise_22_B_4_demand`. The points `(1, 0)`
(`p₂ = 1`) and `(1/8, 3/8)` (`p₂ = 1/8`) are in `U`, their midpoint `(9/16, 3/16)` is not. -/
theorem exercise_22_B_4 :
    ¬Convex ℝ (secondBestUPS (0 : Fin 2) (fun i p => if i = 0 then 1 else max (1 / 2 - p) 0)
      (fun i p => if i = 0 then 0 else unitDemand p)) := by
  intro hc
  have hA : (![1, 0] : Fin 2 → ℝ) ∈ secondBestUPS (0 : Fin 2)
      (fun i p => if i = 0 then 1 else max (1 / 2 - p) 0)
      (fun i p => if i = 0 then 0 else unitDemand p) :=
    ⟨1, one_pos, fun i => by fin_cases i <;> norm_num [unitDemand, Fin.sum_univ_two]⟩
  have hB : (![1 / 8, 3 / 8] : Fin 2 → ℝ) ∈ secondBestUPS (0 : Fin 2)
      (fun i p => if i = 0 then 1 else max (1 / 2 - p) 0)
      (fun i p => if i = 0 then 0 else unitDemand p) :=
    ⟨1 / 8, by norm_num, fun i => by fin_cases i <;> norm_num [unitDemand, Fin.sum_univ_two]⟩
  obtain ⟨p, hp, hle⟩ := hc hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h0 := hle 0
  have h1 := hle 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_ne_zero,
    Fin.isValue] at h0 h1
  unfold unitDemand at h0
  split_ifs at h0 with hlt
  · linarith
  · rw [max_eq_right (by linarith)] at h1; linarith

/-! ### Randomization (p. 823) -/

/-- **Section 22.B** (MWG, pp. 822-823). The ex ante utility possibility set when the policy
maker may randomize over the policies `Θs`, evaluated by expected utility: the vectors
dominated by a convex combination of the utility vectors `u(θ)` of deterministic policies. -/
def randomizedUPS {ι Θ : Type*} (Θs : Set Θ) (u : Θ → ι → ℝ) : Set (ι → ℝ) :=
  {w | ∃ z ∈ convexHull ℝ (u '' Θs), w ≤ z}

/-- **Section 22.B** (MWG, p. 823). A vector is in the randomized utility possibility set iff it
is dominated by the expected utility vector `∑ₖ αₖ u(θₖ)` of a lottery over finitely many
policies. -/
theorem mem_randomizedUPS {ι Θ : Type*} {Θs : Set Θ} {u : Θ → ι → ℝ} {w : ι → ℝ} :
    w ∈ randomizedUPS Θs u ↔ ∃ (κ : Type) (_ : Fintype κ) (α : κ → ℝ) (θ : κ → Θ),
      (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧ (∀ k, θ k ∈ Θs) ∧ w ≤ ∑ k, α k • u (θ k) := by
  constructor
  · rintro ⟨z, hz, hwz⟩
    obtain ⟨κ, hκ, α, z', hα, hα1, hz', rfl⟩ := mem_convexHull_iff_exists_fintype.1 hz
    choose θ hθ hθu using hz'
    refine ⟨κ, hκ, α, θ, hα, hα1, hθ, ?_⟩
    simpa [hθu] using hwz
  · rintro ⟨κ, hκ, α, θ, hα, hα1, hθ, hw⟩
    exact ⟨_, mem_convexHull_of_exists_fintype α (fun k => u (θ k)) hα hα1
      (fun k => ⟨θ k, hθ k, rfl⟩) rfl, hw⟩

/-- **Section 22.B** (MWG, p. 823). The randomized utility possibility set is convex and
contains the deterministic one. -/
theorem randomized_convex {ι Θ : Type*} (Θs : Set Θ) (u : Θ → ι → ℝ) :
    Convex ℝ (randomizedUPS Θs u) ∧ ups Θs (fun i θ => u θ i) ⊆ randomizedUPS Θs u := by
  refine ⟨fun w₁ hw₁ w₂ hw₂ a b ha hb hab => ?_, fun w ⟨θ, hθ, hw⟩ =>
    ⟨u θ, subset_convexHull ℝ _ ⟨θ, hθ, rfl⟩, hw⟩⟩
  obtain ⟨z₁, hz₁, h₁⟩ := hw₁
  obtain ⟨z₂, hz₂, h₂⟩ := hw₂
  refine ⟨a • z₁ + b • z₂, convex_convexHull ℝ _ hz₁ hz₂ ha hb hab, fun i => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left (h₁ i) ha, mul_le_mul_of_nonneg_left (h₂ i) hb]

/-- **Section 22.B** (MWG, p. 823), applied to Example 22.B.5: randomizing between the two
location assignments with equal probabilities gives `(1/2, 1/2)`, which no deterministic
assignment dominates. -/
theorem randomized_locations :
    (![1 / 2, 1 / 2] : Fin 2 → ℝ) ∈ randomizedUPS (Set.univ : Set Bool)
      (fun (x : Bool) (i : Fin 2) => if x then (if i = 0 then 1 else 0)
        else (if i = 0 then 0 else 1)) ∧
    (![1 / 2, 1 / 2] : Fin 2 → ℝ) ∉ ups (Set.univ : Set Bool) (fun (i : Fin 2) (x : Bool) =>
      if x then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1)) := by
  refine ⟨mem_randomizedUPS.2 ⟨Bool, inferInstance, fun _ => 1 / 2, id, fun _ => by norm_num,
    by simp, fun _ => trivial, fun i => ?_⟩, ?_⟩
  · fin_cases i <;> simp
  · rintro ⟨x, -, hx⟩
    have h0 := hx 0; have h1 := hx 1
    cases x <;> simp at h0 h1 <;> linarith

/-! ### Example 22.B.6: unproductive taxation -/

/-- **Example 22.B.6** (MWG, pp. 823-824). Consumer 1 owns one unit of labour/leisure, has
`u₁(x₁₁, x₂₁) = x₂₁ + a ln x₁₁` (`0 < a < 1`); consumer 2 has `u₂ = x₂₂`; the consumption good
is produced from labour one for one. Under the labour tax `t ∈ [0, 1 - a)` consumer 1 chooses
leisure `x₁₁(t) = a/(1 - t)`: this maximizes `a ln x + (1 - t)(1 - x)` over `x ∈ (0, 1]`. -/
theorem example_22_B_6_leisure {a t x : ℝ} (ha : 0 < a) (hta : t < 1 - a)
    (hx : 0 < x) :
    a * Real.log x + (1 - t) * (1 - x) ≤
      a * Real.log (a / (1 - t)) + (1 - t) * (1 - a / (1 - t)) ∧ a / (1 - t) ≤ 1 := by
  have h1t : 0 < 1 - t := by linarith
  have hx' : 0 < a / (1 - t) := div_pos ha h1t
  refine ⟨?_, (div_le_one h1t).2 (by linarith)⟩
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hx')
  rw [Real.log_div hx.ne' hx'.ne'] at hlog
  have e : x / (a / (1 - t)) = x * (1 - t) / a := by field_simp
  rw [e] at hlog
  have e2 : (1 - t) * (a / (1 - t)) = a := by field_simp
  have : a * (Real.log x - Real.log (a / (1 - t))) ≤ x * (1 - t) - a := by
    have h := mul_le_mul_of_nonneg_left hlog ha.le
    have e3 : a * (x * (1 - t) / a - 1) = x * (1 - t) - a := by field_simp
    linarith
  nlinarith

/-- **Example 22.B.6** (MWG, p. 824). The locus `Q(t) = (u₁(x₁(t)), u₂(t(1 - x₁₁(t))))` of
utility pairs under the tax `t`. -/
noncomputable def taxLocus (a t : ℝ) : Fin 2 → ℝ :=
  ![a * Real.log (a / (1 - t)) + (1 - t) * (1 - a / (1 - t)), t * (1 - a / (1 - t))]

/-- **Example 22.B.6** (MWG, p. 823, Figure 22.B.7). The first-best utility possibility set:
`x₁₁ ∈ (0, 1]` leisure, `x₂₁ ≥ 0` consumption of consumer 1, `1 - x₁₁ - x₂₁ ≥ 0` to consumer 2. -/
def firstBestUPS (a : ℝ) : Set (Fin 2 → ℝ) :=
  {u | ∃ x₁₁ x₂₁ : ℝ, 0 < x₁₁ ∧ 0 ≤ x₂₁ ∧ x₁₁ + x₂₁ ≤ 1 ∧ u 0 ≤ x₂₁ + a * Real.log x₁₁ ∧
    u 1 ≤ 1 - x₁₁ - x₂₁}

/-- **Example 22.B.6** (MWG, p. 823). The first-best frontier is the line
`u₁ + u₂ = 1 - a + a ln a` (quasilinearity): every first-best utility pair satisfies
`u₁ + u₂ ≤ 1 - a + a ln a`, attained at leisure `x₁₁ = a`. -/
theorem example_22_B_6_firstBest {a : ℝ} (ha : 0 < a) {u : Fin 2 → ℝ}
    (hu : u ∈ firstBestUPS a) : u 0 + u 1 ≤ 1 - a + a * Real.log a := by
  obtain ⟨x, y, hx, -, -, h0, h1⟩ := hu
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at hlog
  have : a * (Real.log x - Real.log a) ≤ x - a := by
    have h := mul_le_mul_of_nonneg_left hlog ha.le
    have e3 : a * (x / a - 1) = x - a := by field_simp
    linarith
  linarith

/-- **Example 22.B.6** (MWG, p. 824): `Q(t)` is first-best feasible, and its utilitarian total
falls short of the first-best maximum by `a(t/(1 - t) - ln(1/(1 - t)))`. -/
theorem taxLocus_mem_firstBest {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hta : t < 1 - a) :
    taxLocus a t ∈ firstBestUPS a ∧ taxLocus a t 0 + taxLocus a t 1 =
      1 - a + a * Real.log a - a * (t / (1 - t) - Real.log (1 / (1 - t))) := by
  have h1t : 0 < 1 - t := by linarith
  have hle : a / (1 - t) ≤ 1 := (div_le_one h1t).2 (by linarith)
  refine ⟨⟨a / (1 - t), (1 - t) * (1 - a / (1 - t)), div_pos ha h1t, by nlinarith, ?_, ?_, ?_⟩,
    ?_⟩
  · nlinarith
  · simp [taxLocus]; linarith
  · simp only [taxLocus, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith
  · simp only [taxLocus, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [Real.log_div ha.ne' h1t.ne', Real.log_div one_ne_zero h1t.ne', Real.log_one]
    field_simp
    ring

/-- **Example 22.B.6, footnote 7** (MWG, p. 824). The only second-best policy with a first-best
outcome is `t = 0`: for `0 < t < 1 - a`, `Q(t)` is strictly dominated by a first-best feasible
pair, while `Q(0)` is on the first-best Pareto frontier. -/
theorem footnote_22_7 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IsParetoFrontier (firstBestUPS a) (taxLocus a 0) ∧
      ∀ t, 0 < t → t < 1 - a → ¬IsParetoFrontier (firstBestUPS a) (taxLocus a t) := by
  constructor
  · obtain ⟨hmem, hsum⟩ := taxLocus_mem_firstBest ha le_rfl (by linarith)
    refine ⟨hmem, fun ⟨u, hu, hle, i, hi⟩ => ?_⟩
    have hmax := example_22_B_6_firstBest ha hu
    simp only [sub_zero, div_one, Real.log_one, sub_self, mul_zero] at hsum
    have h0 := hle 0
    have h1 := hle 1
    fin_cases i <;> simp at hi <;> linarith
  · intro t ht hta ⟨hmem, hno⟩
    obtain ⟨-, hsum⟩ := taxLocus_mem_firstBest ha ht.le hta
    have h1t : 0 < 1 - t := by linarith
    -- the gap is strictly positive since `ln s < s - 1` for `s = 1/(1 - t) ≠ 1`
    have hs : Real.log (1 / (1 - t)) < 1 / (1 - t) - 1 := Real.log_lt_sub_one_of_pos
      (div_pos one_pos h1t) (by rw [Ne, div_eq_one_iff_eq h1t.ne']; linarith)
    have hgap : 0 < a * (t / (1 - t) - Real.log (1 / (1 - t))) := by
      have : 1 / (1 - t) - 1 = t / (1 - t) := by field_simp; ring
      exact mul_pos ha (by linarith)
    -- consumer 1 keeps `Q₁(t)`, consumer 2 gets the rest of the first-best surplus
    set q := taxLocus a t 0 with hq
    have hq0 : q = a * Real.log (a / (1 - t)) + (1 - t) * (1 - a / (1 - t)) := rfl
    have hlog1 : 0 ≤ Real.log (1 / (1 - t)) :=
      Real.log_nonneg ((le_div_iff₀ h1t).2 (by linarith))
    have hlogle : Real.log (1 / (1 - t)) ≤ t / (1 - t) := by
      have : 1 / (1 - t) - 1 = t / (1 - t) := by field_simp; ring
      linarith [Real.log_le_sub_one_of_pos (div_pos one_pos h1t)]
    have hq' : q - a * Real.log a = a * Real.log (1 / (1 - t)) + (1 - t - a) := by
      rw [hq0, Real.log_div ha.ne' h1t.ne', Real.log_div one_ne_zero h1t.ne', Real.log_one]
      field_simp
      ring
    have hat : a * (t / (1 - t)) ≤ t := by
      rw [mul_div_assoc', div_le_iff₀ h1t]; nlinarith
    refine hno ⟨![q, 1 - a + a * Real.log a - q], ⟨a, q - a * Real.log a, ha, ?_, ?_, ?_, ?_⟩,
      fun i => ?_, 1, ?_⟩
    · rw [hq']; nlinarith
    · rw [hq']; nlinarith
    · simp
    · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith
    · fin_cases i
      · simp [q]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith
    · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith

/-- **Example 22.B.6** (MWG, p. 824, Figure 22.B.9). The locus `Q` is not monotone, so it does
not coincide with the Pareto set of the second-best utility possibility set: for `a = 1/4`,
raising the tax from `t = 1/2` to `t = 2/3` lowers both utilities (consumer 2 gets `1/4`, then
`1/6`). -/
theorem example_22_B_6_nonmonotone :
    taxLocus (1 / 4) (2 / 3) 0 < taxLocus (1 / 4) (1 / 2) 0 ∧
      taxLocus (1 / 4) (2 / 3) 1 < taxLocus (1 / 4) (1 / 2) 1 ∧
      taxLocus (1 / 4) (1 / 2) 1 = 1 / 4 ∧ taxLocus (1 / 4) (2 / 3) 1 = 1 / 6 := by
  simp only [taxLocus, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have h1 : (1 / 4 : ℝ) / (1 - 1 / 2) = 1 / 2 := by norm_num
  have h2 : (1 / 4 : ℝ) / (1 - 2 / 3) = 3 / 4 := by norm_num
  rw [h1, h2]
  have hl : Real.log (3 / 4) - Real.log (1 / 2) = Real.log (3 / 2) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hl2 : Real.log (3 / 2) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  refine ⟨by nlinarith, by norm_num, by norm_num, by norm_num⟩

end MWG.WelfareBargaining
