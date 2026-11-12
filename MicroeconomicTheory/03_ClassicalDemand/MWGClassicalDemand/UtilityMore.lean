/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UtilityExercises
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Leontief preferences and CES limits

MWG, Figure 3.C.3 (p. 49) and Exercise 3.C.6(b)-(c) (p. 97).

* Figure 3.C.3: no utility representing Leontief preferences `min {x₁, x₂}` on `ℝ²_+` is
  differentiable at every point of `ℝ²_{++}`. Along the kink line the gradient would have to
  vanish (`u` is constant to the right of and above each diagonal point), so `u` would be
  constant along the diagonal, contradicting strict monotonicity there.
* Exercise 3.C.6(b): as `ρ → 0`, the increasing transform `(u_ρ^ρ - (α₁ + α₂))/ρ` of the CES
  utility converges to `α₁ ln x₁ + α₂ ln x₂ = ln (x₁^{α₁} x₂^{α₂})` on `ℝ²_{++}`.
* Exercise 3.C.6(c): as `ρ → -∞`, `u_ρ(x) → min {x₁, x₂}` on `ℝ²_{++}`.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice Kreps.PreferenceProperties

/-- **Figure 3.C.3** (MWG, p. 49). The Leontief utility `min {x₁, x₂}`. -/
noncomputable def leontiefUtility (x : Fin 2 → ℝ) : ℝ := min (x 0) (x 1)

/-- A differentiable function that is constant to the right of `0` along a line has zero
derivative in that direction. -/
theorem directional_deriv_zero_of_const {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hc : ∀ s, 0 < s → g s = g 0) : d = 0 := by
  have h1 := hg.tendsto_slope_zero_right
  have h2 : Tendsto (fun t : ℝ => t⁻¹ • (g (0 + t) - g 0)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [zero_add, hc t ht, sub_self, smul_zero]
  exact tendsto_nhds_unique h1 h2

/-- **Figure 3.C.3** (MWG, p. 49). Leontief preferences cannot be represented by a utility
function that is differentiable at every strictly positive bundle. -/
theorem figure_3_C_3 :
    ¬ ∃ u : (Fin 2 → ℝ) → ℝ, RepresentsOn (nonnegOrthant 2) u (utilityPref leontiefUtility) ∧
      ∀ x : Fin 2 → ℝ, (∀ l, 0 < x l) → DifferentiableAt ℝ u x := by
  rintro ⟨u, hu, hd⟩
  set e : Fin 2 → Fin 2 → ℝ := fun i => Pi.single i 1 with he
  have hgrad : ∀ t : ℝ, 0 < t → fderiv ℝ u (fun _ => t) = 0 := by
    intro t ht
    have hdt := (hd (fun _ => t) fun _ => ht).hasFDerivAt
    have hpart : ∀ i, fderiv ℝ u (fun _ => t) (e i) = 0 := by
      intro i
      apply directional_deriv_zero_of_const (mc_line_hasDerivAt hdt (e i))
      intro s hs
      have hmem1 : ((fun _ => t) + s • e i : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
        intro l
        simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : 0 ≤ (Pi.single i (1 : ℝ) : Fin 2 → ℝ) l := by
          rw [Pi.single_apply]; split_ifs <;> norm_num
        nlinarith
      have hmem0 : ((fun _ => t) + (0 : ℝ) • e i : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
        intro l; simp [ht.le]
      apply (hu.indifferent_iff hmem1 hmem0).mp
      simp only [Indifferent, utilityPref, leontiefUtility, he]
      fin_cases i <;> simp [hs.le]
    ext v
    rw [fderiv_apply_eq_gradient_dot, zero_apply]
    have : gradientVec (fderiv ℝ u fun _ => t) = 0 := by
      funext i
      exact hpart i
    simp [this]
  -- `u` is constant along the diagonal
  have hdiag : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      HasDerivAt (fun s : ℝ => u ((0 : Fin 2 → ℝ) + s • fun _ => (1 : ℝ))) 0 t := by
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hpt : ((0 : Fin 2 → ℝ) + t • fun _ => (1 : ℝ)) = fun _ => t := by
      funext l; simp
    have hdt : HasFDerivAt u (fderiv ℝ u ((0 : Fin 2 → ℝ) + t • fun _ => (1 : ℝ)))
        ((0 : Fin 2 → ℝ) + t • fun _ => (1 : ℝ)) := by
      rw [hpt]; exact (hd _ fun _ => htp).hasFDerivAt
    have := mc_line_hasDerivAt_at hdt
    rwa [hpt, hgrad t htp, zero_apply] at this
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => u ((0 : Fin 2 → ℝ) + s • fun _ => (1 : ℝ))) (fun _ => (0 : ℝ))
    (show (1 : ℝ) < 2 by norm_num) (fun t ht => (hdiag t ht).continuousAt.continuousWithinAt)
    (fun t ht => hdiag t ⟨ht.1.le, ht.2.le⟩)
  have hg : ∀ s : ℝ, ((0 : Fin 2 → ℝ) + s • fun _ => (1 : ℝ)) = fun _ => s := by
    intro s; funext; simp
  simp only [hg] at hcs
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [h21, div_one] at hcs
  have hlt : u (fun _ => 1) < u (fun _ => 2) := by
    apply (hu.strict_iff (fun _ => by norm_num) (fun _ => by norm_num)).mp
    simp [Strict, utilityPref, leontiefUtility]
  linarith

/-- **Exercise 3.C.6(b)** (MWG, p. 97). For `ρ ≠ 0`, the map `t ↦ (t^ρ - c)/ρ` is strictly
increasing on `t > 0`, so `(u_ρ^ρ - (α₁ + α₂))/ρ` represents the same preferences as the CES
utility `u_ρ`. -/
theorem exercise_3_C_6b_transform {ρ : ℝ} (hρ : ρ ≠ 0) (c : ℝ) :
    StrictMonoOn (fun t : ℝ => (t ^ ρ - c) / ρ) (Set.Ioi 0) := by
  intro s hs t ht hst
  simp only
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have : t ^ ρ < s ^ ρ := Real.rpow_lt_rpow_of_neg hs hst hneg
    have e : ∀ a : ℝ, a / ρ = -a / -ρ := fun a => by
      rw [div_eq_div_iff hρ (neg_ne_zero.mpr hρ)]; ring
    rw [e, e (t ^ ρ - c)]
    exact div_lt_div_of_pos_right (by linarith) (neg_pos.mpr hneg)
  · have : s ^ ρ < t ^ ρ := Real.rpow_lt_rpow (le_of_lt hs) hst hpos
    exact div_lt_div_of_pos_right (by linarith) hpos

/-- For `x > 0`, `(x^ρ - 1)/ρ → ln x` as `ρ → 0`. -/
theorem rpow_sub_one_div_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ρ : ℝ => (x ^ ρ - 1) / ρ) (𝓝[≠] 0) (𝓝 (Real.log x)) := by
  have hd := (Real.hasStrictDerivAt_const_rpow hx 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope, Real.rpow_zero, one_mul] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ _
  simp [slope_def_field, Real.rpow_zero]

/-- **Exercise 3.C.6(b)** (MWG, p. 97). On `ℝ²_{++}`, as `ρ → 0`,
`(α₁x₁^ρ + α₂x₂^ρ - (α₁ + α₂))/ρ → α₁ ln x₁ + α₂ ln x₂ = ln (x₁^{α₁} x₂^{α₂})`: in the limit the
CES preferences are the (generalized) Cobb-Douglas preferences. -/
theorem exercise_3_C_6b (a₁ a₂ : ℝ) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    Tendsto (fun ρ : ℝ => (a₁ * x₁ ^ ρ + a₂ * x₂ ^ ρ - (a₁ + a₂)) / ρ) (𝓝[≠] 0)
        (𝓝 (Real.log (x₁ ^ a₁ * x₂ ^ a₂))) := by
  rw [Real.log_mul (Real.rpow_pos_of_pos hx₁ _).ne' (Real.rpow_pos_of_pos hx₂ _).ne',
    Real.log_rpow hx₁, Real.log_rpow hx₂]
  have := ((rpow_sub_one_div_tendsto hx₁).const_mul a₁).add
    ((rpow_sub_one_div_tendsto hx₂).const_mul a₂)
  apply this.congr'
  filter_upwards [self_mem_nhdsWithin] with ρ _
  ring

/-- For `c > 0`, `c^{1/ρ} → 1` as `ρ → -∞`. -/
theorem rpow_inv_tendsto_one {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => c ^ (1 / ρ)) atBot (𝓝 1) := by
  have h1 : Tendsto (fun ρ : ℝ => 1 / ρ) atBot (𝓝 0) := by
    simpa using tendsto_inv_atBot_zero
  have h2 : Tendsto (fun t : ℝ => c ^ t) (𝓝 0) (𝓝 (c ^ (0 : ℝ))) :=
    (Real.continuousAt_const_rpow hc.ne').tendsto
  rw [Real.rpow_zero] at h2
  exact h2.comp h1

/-- **Exercise 3.C.6(c)** (MWG, p. 97). On `ℝ²_{++}` with `α₁, α₂ > 0`, as `ρ → -∞` the CES
utility `(α₁x₁^ρ + α₂x₂^ρ)^{1/ρ}` converges to the Leontief utility `min {x₁, x₂}`. -/
theorem exercise_3_C_6c {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) :
    Tendsto (fun ρ : ℝ => (a₁ * x₁ ^ ρ + a₂ * x₂ ^ ρ) ^ (1 / ρ)) atBot (𝓝 (min x₁ x₂)) := by
  set m := min x₁ x₂ with hm
  have hm0 : 0 < m := lt_min hx₁ hx₂
  -- the coefficient of the smaller coordinate
  obtain ⟨a, ha, hlow⟩ : ∃ a, 0 < a ∧ ∀ ρ : ℝ, ρ < 0 → a * m ^ ρ ≤ a₁ * x₁ ^ ρ + a₂ * x₂ ^ ρ := by
    rcases le_total x₁ x₂ with h | h
    · refine ⟨a₁, ha₁, fun ρ _ => ?_⟩
      rw [hm, min_eq_left h]
      have := mul_nonneg ha₂.le (Real.rpow_nonneg hx₂.le ρ)
      linarith
    · refine ⟨a₂, ha₂, fun ρ _ => ?_⟩
      rw [hm, min_eq_right h]
      have := mul_nonneg ha₁.le (Real.rpow_nonneg hx₁.le ρ)
      linarith
  have hup : ∀ ρ : ℝ, ρ < 0 → a₁ * x₁ ^ ρ + a₂ * x₂ ^ ρ ≤ (a₁ + a₂) * m ^ ρ := by
    intro ρ hρ
    have h1 : x₁ ^ ρ ≤ m ^ ρ := Real.rpow_le_rpow_of_nonpos hm0 (min_le_left _ _) hρ.le
    have h2 : x₂ ^ ρ ≤ m ^ ρ := Real.rpow_le_rpow_of_nonpos hm0 (min_le_right _ _) hρ.le
    nlinarith
  have hpow : ∀ c : ℝ, 0 < c → ∀ ρ : ℝ, ρ < 0 → (c * m ^ ρ) ^ (1 / ρ) = c ^ (1 / ρ) * m := by
    intro c hc ρ hρ
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hm0.le _), one_div,
      Real.rpow_rpow_inv hm0.le hρ.ne]
  have hlo : Tendsto (fun ρ : ℝ => (a₁ + a₂) ^ (1 / ρ) * m) atBot (𝓝 m) := by
    simpa using (rpow_inv_tendsto_one (add_pos ha₁ ha₂)).mul_const m
  have hhi : Tendsto (fun ρ : ℝ => a ^ (1 / ρ) * m) atBot (𝓝 m) := by
    simpa using (rpow_inv_tendsto_one ha).mul_const m
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with ρ hρ
    rw [← hpow _ (add_pos ha₁ ha₂) ρ hρ]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hm0 _))
      (hlow ρ hρ)) (hup ρ hρ) (by rw [one_div]; exact (inv_neg''.mpr hρ).le)
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with ρ hρ
    rw [← hpow _ ha ρ hρ]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos ha (Real.rpow_pos_of_pos hm0 _)) (hlow ρ hρ)
      (by rw [one_div]; exact (inv_neg''.mpr hρ).le)

end MWG.ClassicalDemand
