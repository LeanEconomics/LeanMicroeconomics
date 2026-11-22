/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.CloserDemandContinuity

/-!
# Exercise 3.AA.2: the expenditure function at boundary prices

MWG, Exercise 3.AA.2, p. 95: under the conditions of Proposition 3.AA.1 (`u` continuous,
representing a locally nonsatiated `≿` on `ℝ^L_+`), `e(p, u)` is continuous "even if we replace
minimum by infimum and allow `p = 0`".

Earlier modules prove joint continuity of `e` on `{p ≫ 0, ū attainable}`
(`exercise_3_AA_2_continuous`) and continuity of `e(·, ū)` in `p` on all of `ℝ^L_+`
(`exercise_3_AA_2_inf_continuous`). Joint continuity in `(p, ū)` at a boundary price is false:
with `L = 2`, `u(x) = min(x₁, 1) + max(x₁ - 2, 0) + x₂/(1 + x₂)` (continuous, strongly
increasing in `x₂`, hence locally nonsatiated) and `p = (1, 0)`, the infimum `e((1, 0), ū)` is
`≤ 1` for every `ū < 2` close to `2`, but `= 2` at the attainable level `ū = 2`
(`exercise_3_AA_2_boundary_counterexample`): `e((1, 0), ·)` is not even continuous in `ū`.
The reason is that at `p₂ = 0` the infimum is approached by `x₂ → ∞`, and `x₂/(1 + x₂)`
never reaches its supremum `1`. (Correction F2-1.)
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice Kreps.PreferenceProperties

/-- The utility of the counterexample: `min(x₁, 1) + max(x₁ - 2, 0) + x₂/(1 + x₂)`. -/
noncomputable def econBoundaryUtility (x : Fin 2 → ℝ) : ℝ :=
  min (x 0) 1 + max (x 0 - 2) 0 + x 1 / (1 + x 1)

/-- The boundary price vector `(1, 0)`. -/
def econBoundaryPrice : Fin 2 → ℝ := ![1, 0]

/-- `econBoundaryUtility` is continuous on `ℝ²_+`. -/
theorem econBoundaryUtility_continuousOn :
    ContinuousOn econBoundaryUtility (nonnegOrthant 2) := by
  have h1 : ContinuousOn (fun x : Fin 2 → ℝ => x 1 / (1 + x 1)) (nonnegOrthant 2) :=
    (continuous_apply 1).continuousOn.div (continuous_const.add (continuous_apply 1)).continuousOn
      fun x hx => by have := hx 1; positivity
  have h0 : Continuous fun x : Fin 2 → ℝ => min (x 0) 1 + max (x 0 - 2) 0 := by fun_prop
  exact h0.continuousOn.add h1

/-- `econBoundaryUtility` is locally nonsatiated on `ℝ²_+`. -/
theorem econBoundaryUtility_lns :
    LocallyNonsatiated (nonnegOrthant 2) (utilityPref econBoundaryUtility) := by
  intro x hx ε hε
  refine ⟨x + fun _ => ε / 2, fun l => by simp only [Pi.add_apply]; linarith [hx l], ?_, ?_⟩
  · rw [euclidDist_add_const, abs_of_pos (by linarith)]
    have h2 : Real.sqrt (2 : ℕ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ ε / 2)
    linarith
  · have hx1 := hx 1
    have hlt : econBoundaryUtility x < econBoundaryUtility (x + fun _ => ε / 2) := by
      simp only [econBoundaryUtility, Pi.add_apply]
      have hm : min (x 0) 1 ≤ min (x 0 + ε / 2) 1 := min_le_min_right _ (by linarith)
      have hM : max (x 0 - 2) 0 ≤ max (x 0 + ε / 2 - 2) 0 := max_le_max_right _ (by linarith)
      have hf : x 1 / (1 + x 1) < (x 1 + ε / 2) / (1 + (x 1 + ε / 2)) := by
        rw [div_lt_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      linarith
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- `p·x = x₁` at `p = (1, 0)`. -/
theorem econBoundaryPrice_dot (x : Fin 2 → ℝ) : econBoundaryPrice ⬝ᵥ x = x 0 := by
  simp [econBoundaryPrice, dotProduct, Fin.sum_univ_two]

/-- **Exercise 3.AA.2** (MWG, p. 95), counterexample to joint continuity at boundary prices.
For the continuous, locally nonsatiated `u = econBoundaryUtility` on `ℝ²_+` and the boundary
price `p = (1, 0)`: the level `ū = 2` is attainable, `e(p, 2) ≥ 2` (in fact `= 2`, as an
infimum), but `e(p, ū) ≤ 1` for all `ū ∈ (1, 2)`; so `ū ↦ e(p, ū)` is not continuous at `2`,
and `(p, ū) ↦ e(p, ū)` is not continuous at `((1, 0), 2)`. -/
theorem exercise_3_AA_2_boundary_counterexample :
    ContinuousOn econBoundaryUtility (nonnegOrthant 2) ∧
      LocallyNonsatiated (nonnegOrthant 2) (utilityPref econBoundaryUtility) ∧
      econBoundaryPrice ∈ nonnegOrthant 2 ∧
      (∃ x ∈ nonnegOrthant 2, (2 : ℝ) ≤ econBoundaryUtility x) ∧
      2 ≤ expenditure econBoundaryUtility econBoundaryPrice 2 ∧
      (∀ ub : ℝ, 1 < ub → ub < 2 → expenditure econBoundaryUtility econBoundaryPrice ub ≤ 1) ∧
      ¬ ContinuousAt (fun ub => expenditure econBoundaryUtility econBoundaryPrice ub) 2 := by
  have hp : econBoundaryPrice ∈ nonnegOrthant 2 := by
    intro l
    fin_cases l <;> simp [econBoundaryPrice]
  have hatt : ∃ x ∈ nonnegOrthant 2, (2 : ℝ) ≤ econBoundaryUtility x := by
    refine ⟨![3, 0], fun l => by fin_cases l <;> norm_num, ?_⟩
    simp only [econBoundaryUtility]
    norm_num
  have hge : 2 ≤ expenditure econBoundaryUtility econBoundaryPrice 2 := by
    obtain ⟨x0, hx0, hux0⟩ := hatt
    refine le_supportFn (K := empConstraintSet econBoundaryUtility 2) ⟨x0, hx0, hux0⟩
      fun x hx => ?_
    rw [econBoundaryPrice_dot]
    have hx1 := hx.1 1
    have hu := hx.2
    simp only [econBoundaryUtility] at hu
    have hf : x 1 / (1 + x 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    by_contra hlt
    rw [not_le] at hlt
    have hm : min (x 0) 1 ≤ 1 := min_le_right _ _
    have hM : max (x 0 - 2) 0 = 0 := max_eq_right (by linarith)
    linarith
  have hle : ∀ ub : ℝ, 1 < ub → ub < 2 →
      expenditure econBoundaryUtility econBoundaryPrice ub ≤ 1 := by
    intro ub h1 h2
    set δ := 2 - ub with hδ
    have hδ0 : 0 < δ := by linarith
    set x : Fin 2 → ℝ := ![1, 1 / δ] with hxdef
    have hx : x ∈ empConstraintSet econBoundaryUtility ub := by
      have hx0 : x 0 = 1 := rfl
      have hx1 : x 1 = 1 / δ := rfl
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · change 0 ≤ x 0
          rw [hx0]
          norm_num
        · change 0 ≤ x 1
          rw [hx1]
          positivity
      simp only [econBoundaryUtility, x]
      norm_num
      rw [show δ⁻¹ / (1 + δ⁻¹) = 1 / (1 + δ) by field_simp; ring]
      have h3 : 1 - δ ≤ 1 / (1 + δ) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hbdd : BddBelow ((fun y => econBoundaryPrice ⬝ᵥ y) ''
        empConstraintSet econBoundaryUtility ub) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      change 0 ≤ econBoundaryPrice ⬝ᵥ y
      rw [econBoundaryPrice_dot]
      exact hy.1 0
    have := supportFn_le hbdd hx
    rw [econBoundaryPrice_dot] at this
    exact this.trans_eq (by simp [x])
  refine ⟨econBoundaryUtility_continuousOn, econBoundaryUtility_lns, hp, hatt, hge, hle, ?_⟩
  intro hc
  have hev : ∀ᶠ ub in 𝓝 (2 : ℝ),
      (3 / 2 : ℝ) < expenditure econBoundaryUtility econBoundaryPrice ub :=
    hc.eventually (lt_mem_nhds (by linarith))
  have hev' : ∀ᶠ ub in 𝓝[<] (2 : ℝ), (3 / 2 : ℝ) <
      expenditure econBoundaryUtility econBoundaryPrice ub ∧ ub ∈ Set.Ioo 1 2 :=
    (eventually_nhdsWithin_of_eventually_nhds hev).and (Ioo_mem_nhdsLT (by norm_num))
  obtain ⟨ub, hub, hub12⟩ := hev'.exists
  have := hle ub hub12.1 hub12.2
  linarith

end MWG.ClassicalDemand
