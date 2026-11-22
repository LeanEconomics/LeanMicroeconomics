/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.OfferCurves
import MWGGeneralEquilibriumExamples.Nonexistence
import MWGGeneralEquilibriumExamples.TwoConsumerProduction

/-!
# Offer curve examples (MWG Exercise 15.B.4(d), p. 541; Figure 15.B.10(b), p. 522)

* **Exercise 15.B.4(d)**, first sentence: preferences whose offer curve is not normal. The consumer
  has endowment `ω = (10, 0)` and the continuous, strongly monotone, strictly convex utility
  `u(x) = x₁ + v(4x₁ + x₂)`, `v = tcpPowFive (1595/32) (19/32)` (`ex15B4dUtility`,
  `ex15B4d_props`). At prices `(q, 1)` demand is the single bundle `(3/4, 185/4)` for `q = 5` and
  `(7, 2955/64)` for `q = 985/64` (`ex15B4d_demand_five`, `ex15B4d_demand_high`): raising the
  relative price of good 1 raises the demand for good 1 but lowers the demand for good 2, so every
  selection from this consumer's demand is a non-normal offer curve (`exercise_15_B_4d_exists`).
  Good 2 is inferior, as `exercise_15_B_4d` requires: at `q = 5` an extra unit of wealth moves
  demand by `(1, -4)` (`ex15B4d_inferior`).
* **Figure 15.B.10(b)**: the offer curve of the nonconvex consumer 1 (`x₁² + x₂²`, endowment
  `(1, 1)`) is the union of the two half-lines `{(t, 0) : t ≥ 2}` and `{(0, t) : t ≥ 2}`
  (`fig_15_B_10b_offerCurve`), which is disconnected (`fig_15_B_10b_offerCurve_not_preconnected`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

/-! ### Exercise 15.B.4(d): a non-normal offer curve -/

/-- **Exercise 15.B.4(d)** (MWG, p. 541). The utility `u(x) = x₁ + v(4x₁ + x₂)` with
`v(s) = -(K/5)(K/(s + e))⁵`, `K = 1595/32`, `e = 19/32`. -/
noncomputable def ex15B4dUtility : (Fin 2 → ℝ) → ℝ :=
  tcpAffineUtility 1 0 4 1 (tcpPowFive (1595 / 32) (19 / 32))

/-- **Exercise 15.B.4(d)** (MWG, p. 541). The consumer's demand at prices `(q, 1)` with the
endowment `ω = (10, 0)`, i.e. wealth `10q`. -/
noncomputable def ex15B4dDemand (q : ℝ) : Set (Fin 2 → ℝ) :=
  walrasianDemand ex15B4dUtility ![q, 1] (![q, 1] ⬝ᵥ ![10, 0])

/-- **Exercise 15.B.4(d)** (MWG, p. 541). The utility `ex15B4dUtility` is continuous on `ℝ²₊`,
strongly monotone and strictly convex. -/
theorem ex15B4d_props : ContinuousOn ex15B4dUtility (nonnegOrthant 2) ∧
    UtilityStronglyMonotone ex15B4dUtility ∧
    PrefStrictlyConvex (nonnegOrthant 2) (utilityPref ex15B4dUtility) := by
  have ha : (0 : ℝ) < 1595 / 32 := by norm_num
  have he : (0 : ℝ) < 19 / 32 := by norm_num
  exact ⟨tcpAffineUtility_continuousOn (by norm_num) zero_le_one (tcpPowFive_continuousOn he),
    tcpAffineUtility_stronglyMonotone zero_le_one le_rfl (by norm_num) zero_le_one
      (Or.inl one_pos) (Or.inr one_pos) (tcpPowFive_strictMonoOn ha he),
    tcpAffineUtility_strictlyConvex (by norm_num) zero_le_one (by norm_num)
      (tcpPowFive_strictConcaveOn ha he)⟩

/-- `(q, 1)·y = q y₁ + y₂`. -/
theorem ex15B4d_dot (q : ℝ) (y : Fin 2 → ℝ) : ![q, 1] ⬝ᵥ y = q * y 0 + y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The first-order condition is sufficient: at prices `(q, 1)`, `q > 4`, a bundle `x ≥ 0` on the
budget line `q x₁ + x₂ = W` with `v'(4x₁ + x₂) = 1/(q - 4)` maximizes utility on the budget set
(tangent inequality: `u(y) - u(x) ≤ v'(s)(q(y₁ - x₁) + (y₂ - x₂)) ≤ 0`). -/
theorem ex15B4d_opt {q W : ℝ} (hq : 4 < q) {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2)
    (hfoc : (1595 / 32 / (4 * x 0 + 1 * x 1 + 19 / 32)) ^ 6 = 1 / (q - 4))
    (hb : q * x 0 + x 1 = W) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2)
    (hyb : q * y 0 + y 1 ≤ W) : ex15B4dUtility y ≤ ex15B4dUtility x := by
  have hx0 := hx 0
  have hx1 := hx 1
  have hy0 := hy 0
  have hy1 := hy 1
  have ht := tcpPowFive_tangent (a := 1595 / 32) (e := 19 / 32) (s := 4 * x 0 + 1 * x 1)
    (t := 4 * y 0 + 1 * y 1) (by norm_num) (by linarith) (by linarith)
  rw [hfoc] at ht
  simp only [ex15B4dUtility, tcpAffineUtility, one_mul, zero_mul, add_zero]
  simp only [one_mul] at ht
  have hq4 : 0 < q - 4 := by linarith
  have h1 : (4 * y 0 + y 1) - (4 * x 0 + x 1) ≤ (q - 4) * (x 0 - y 0) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (one_div_pos.2 hq4).le
  have h3 : 1 / (q - 4) * ((q - 4) * (x 0 - y 0)) = x 0 - y 0 := by
    field_simp
  linarith

/-- The demand at prices `(q, 1)`, `q > 4`, is the single bundle `x` satisfying the first-order
condition and the budget identity (uniqueness from strict convexity). -/
theorem ex15B4d_demand_eq {q : ℝ} (hq : 4 < q) {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2)
    (hfoc : (1595 / 32 / (4 * x 0 + 1 * x 1 + 19 / 32)) ^ 6 = 1 / (q - 4))
    (hb : q * x 0 + x 1 = 10 * q) : ex15B4dDemand q = {x} := by
  have hW : ![q, 1] ⬝ᵥ ![10, 0] = 10 * q := by rw [ex15B4d_dot]; norm_num; ring
  have hxd : x ∈ ex15B4dDemand q := by
    refine ⟨⟨hx, ?_⟩, fun y hy => ?_⟩
    · rw [ex15B4d_dot, hW, hb]
    · have hyb := hy.2
      rw [ex15B4d_dot, hW] at hyb
      exact ex15B4d_opt hq hx hfoc hb hy.1 hyb
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact tcp_eq_of_strictlyConvex ex15B4d_props.2.2 (convex_budgetSet _ _) (fun z hz => hz.1)
      hy.1 hxd.1 hy.2 hxd.2
  · rintro rfl
    exact hxd

/-- **Exercise 15.B.4(d)** (MWG, p. 541): at `q = 5` the demand is `(3/4, 185/4)`
(`4x₁ + x₂ + e = K`, so `v' = 1 = 1/(q - 4)`). -/
theorem ex15B4d_demand_five : ex15B4dDemand 5 = {![3 / 4, 185 / 4]} :=
  ex15B4d_demand_eq (by norm_num) (fun l => by fin_cases l <;> norm_num) (by norm_num)
    (by norm_num)

/-- **Exercise 15.B.4(d)** (MWG, p. 541): at `q = 985/64` the demand is `(7, 2955/64)`
(`4x₁ + x₂ + e = 3K/2`, so `v' = (2/3)⁶ = 64/729 = 1/(q - 4)`). -/
theorem ex15B4d_demand_high : ex15B4dDemand (985 / 64) = {![7, 2955 / 64]} :=
  ex15B4d_demand_eq (by norm_num) (fun l => by fin_cases l <;> norm_num) (by norm_num)
    (by norm_num)

/-- **Exercise 15.B.4(d)** (MWG, p. 541): there are preferences giving rise to offer curves that
are not normal. For the continuous, strongly monotone, strictly convex `ex15B4dUtility` with
endowment `(10, 0)`, raising the relative price of good 1 from `5` to `985/64` raises the demand
for good 1 (`3/4 → 7`) but lowers the demand for good 2 (`2960/64 → 2955/64`); so every
selection `d` of the demand at prices `(q, 1)` is not a normal offer curve. -/
theorem exercise_15_B_4d_exists (d : ℝ → Fin 2 → ℝ) (h5 : d 5 ∈ ex15B4dDemand 5)
    (hh : d (985 / 64) ∈ ex15B4dDemand (985 / 64)) : ¬ NormalOfferCurve d := by
  rw [ex15B4d_demand_five, Set.mem_singleton_iff] at h5
  rw [ex15B4d_demand_high, Set.mem_singleton_iff] at hh
  intro hN
  have h := hN.1 5 (985 / 64) (by norm_num) (by norm_num) (by rw [h5, hh]; norm_num)
  rw [h5, hh] at h
  norm_num at h

/-- **Exercise 15.B.4(d)** (MWG, p. 541), second sentence for this example: good 2 is inferior.
At prices `(5, 1)`, wealth `50 + δ` (`-3/4 ≤ δ ≤ 185/16`) gives the demand
`(3/4 + δ, 185/4 - 4δ)`, so raising wealth lowers the demand for good 2. -/
theorem ex15B4d_inferior {δ : ℝ} (hδ : -(3 / 4) ≤ δ) (hδ' : δ ≤ 185 / 16) :
    walrasianDemand ex15B4dUtility ![5, 1] (50 + δ) = {![3 / 4 + δ, 185 / 4 - 4 * δ]} := by
  set x : Fin 2 → ℝ := ![3 / 4 + δ, 185 / 4 - 4 * δ] with hxdef
  have hx : x ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · simp [hxdef]; linarith
    · simp [hxdef]; linarith
  have hfoc : (1595 / 32 / (4 * x 0 + 1 * x 1 + 19 / 32)) ^ 6 = 1 / ((5 : ℝ) - 4) := by
    simp only [hxdef, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e : 4 * (3 / 4 + δ) + 1 * (185 / 4 - 4 * δ) + 19 / 32 = (1595 / 32 : ℝ) := by
      ring
    rw [e]
    norm_num
  have hb : 5 * x 0 + x 1 = 50 + δ := by
    simp only [hxdef, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hxd : x ∈ walrasianDemand ex15B4dUtility ![5, 1] (50 + δ) := by
    refine ⟨⟨hx, ?_⟩, fun y hy => ?_⟩
    · rw [ex15B4d_dot, hb]
    · have hyb := hy.2
      rw [ex15B4d_dot] at hyb
      exact ex15B4d_opt (by norm_num) hx hfoc hb hy.1 hyb
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact tcp_eq_of_strictlyConvex ex15B4d_props.2.2 (convex_budgetSet _ _) (fun z hz => hz.1)
      hy.1 hxd.1 hy.2 hxd.2
  · rintro rfl
    exact hxd

/-! ### Figure 15.B.10(b): a disconnected offer curve -/

/-- Consumer 1's demand in `fig10bEconomy` is the demand of `x₁² + x₂²` with wealth `p₁ + p₂`. -/
theorem fig10b_demand0 (p : Fin 2 → ℝ) :
    fig10bEconomy.demand 0 p = walrasianDemand sqUtility p (p 0 + p 1) := by
  have hw0 : p ⬝ᵥ fig10bEconomy.ω 0 = p 0 + p 1 := by
    simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
  rw [← hw0]
  rfl

/-- At `p = (1, t - 1)`, `t ≥ 2`, the `x₁² + x₂²` consumer with wealth `t` demands `(t, 0)`. -/
theorem fig10b_corner_mem {t : ℝ} (ht : 2 ≤ t) :
    ![t, 0] ∈ walrasianDemand sqUtility ![1, t - 1] (![1, t - 1] 0 + ![1, t - 1] 1) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
  · fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith
    · simp
  · simp [dotProduct, Fin.sum_univ_two]
  · obtain ⟨hy0, hb⟩ := hy
    have hb' : y 0 + (t - 1) * y 1 ≤ 1 + (t - 1) := by
      simpa [dotProduct, Fin.sum_univ_two] using hb
    have h0 := hy0 0
    have h1 := hy0 1
    have hs : y 0 + y 1 ≤ t := by nlinarith
    simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith

/-- **Figure 15.B.10(b)** (MWG, p. 522): the offer curve of consumer 1 (`x₁² + x₂²`, endowment
`(1, 1)`) consists of the two half-lines `{(t, 0) : t ≥ 2}` and `{(0, t) : t ≥ 2}`: demand at
`p ≫ 0` is a corner with `x₁ + x₂ = (p₁ + p₂)/min(p₁, p₂) ≥ 2`, and `p = (1, t - 1)` gives
`(t, 0)`, `p = (t - 1, 1)` gives `(0, t)`. -/
theorem fig_15_B_10b_offerCurve : fig10bEconomy.offerCurve 0 =
    {x | x 1 = 0 ∧ 2 ≤ x 0} ∪ {x | x 0 = 0 ∧ 2 ≤ x 1} := by
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [fig10b_demand0] at hx
    have hp0 := hp 0
    have hp1 := hp 1
    obtain ⟨hc0, hc1⟩ := sqUtility_demand_corner hp (by linarith) hx
    have hm0 : 0 < min (p 0) (p 1) := lt_min hp0 hp1
    have h2 : 2 ≤ (p 0 + p 1) / min (p 0) (p 1) := by
      rw [le_div_iff₀ hm0]
      linarith [min_le_left (p 0) (p 1), min_le_right (p 0) (p 1)]
    rcases mul_eq_zero.1 hc0 with h | h
    · right
      refine ⟨h, ?_⟩
      rw [h, zero_add] at hc1
      linarith
    · left
      refine ⟨h, ?_⟩
      rw [h, add_zero] at hc1
      linarith
  · rintro (⟨h1, h0⟩ | ⟨h0, h1⟩)
    · refine ⟨![1, x 0 - 1], fun l => ?_, ?_⟩
      · fin_cases l
        · simp
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          linarith
      rw [fig10b_demand0]
      have hx : x = ![x 0, 0] := by
        funext l
        fin_cases l
        · rfl
        · simpa using h1
      rw [hx]
      simpa using fig10b_corner_mem h0
    · refine ⟨![x 1 - 1, 1], fun l => ?_, ?_⟩
      · fin_cases l
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
          linarith
        · simp
      rw [fig10b_demand0]
      have hx : x = ![0, x 1] := by
        funext l
        fin_cases l
        · simpa using h0
        · rfl
      -- swap the two goods
      have hm := fig10b_corner_mem h1
      obtain ⟨-, hmax⟩ := hm
      rw [hx]
      refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
      · fin_cases l
        · simp
        · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          linarith
      · simp [dotProduct, Fin.sum_univ_two]
      · have := hmax ![y 1, y 0] ⟨fun l => by fin_cases l <;> simp [hy.1 0, hy.1 1], by
          have hb := hy.2
          simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
            Matrix.cons_val_one] at hb ⊢
          linarith⟩
        simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
        linarith

/-- **Figure 15.B.10(b)** (MWG, p. 522): consumer 1's offer curve is disconnected. On it
`x₁ - x₂ ≥ 2` or `x₁ - x₂ ≤ -2`, and both signs occur, so `x₁ - x₂` would have to take the value
`0` on a preconnected offer curve (intermediate value theorem). -/
theorem fig_15_B_10b_offerCurve_not_preconnected :
    ¬ IsPreconnected (fig10bEconomy.offerCurve 0) := by
  intro hc
  rw [fig_15_B_10b_offerCurve] at hc
  have ha : (![0, 2] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | x 1 = 0 ∧ 2 ≤ x 0} ∪
      {x | x 0 = 0 ∧ 2 ≤ x 1} := Or.inr ⟨by simp, by simp⟩
  have hb : (![2, 0] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | x 1 = 0 ∧ 2 ≤ x 0} ∪
      {x | x 0 = 0 ∧ 2 ≤ x 1} := Or.inl ⟨by simp, by simp⟩
  have hf : ContinuousOn (fun x : Fin 2 → ℝ => x 0 - x 1)
      ({x : Fin 2 → ℝ | x 1 = 0 ∧ 2 ≤ x 0} ∪ {x | x 0 = 0 ∧ 2 ≤ x 1}) :=
    (by fun_prop : Continuous fun x : Fin 2 → ℝ => x 0 - x 1).continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : Fin 2 → ℝ => x 0 - x 1) ![0, 2])
      ((fun x : Fin 2 → ℝ => x 0 - x 1) ![2, 0]) := by
    simp
  obtain ⟨x, hx, hx0⟩ := hc.intermediate_value ha hb hf h0
  simp only at hx0
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at hx0
    linarith
  · rw [h1] at hx0
    linarith

end MWG.GeneralEquilibriumExamples
