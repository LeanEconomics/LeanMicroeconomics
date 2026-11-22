/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Welfare
import MWGClassicalDemand.ExpCobbDouglas
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Cobb-Douglas Edgeworth boxes (MWG Example 15.B.1 and Exercise 15.B.2, pp. 519-520, 540)

Consumer `i` has the Cobb-Douglas utility `x_{1i}^{αᵢ} x_{2i}^{1-αᵢ}` (Chapter 3's
`cobbDouglasUtility 1 αᵢ`) and endowment `ωᵢ ≫ 0`.

* `cd_demand_eq`: at `p ≫ 0` consumer `i`'s offer curve is Chapter 3's Cobb-Douglas demand
  (Example 3.D.1) with wealth `p·ωᵢ`; `cd_demand_empty`: no bundle is demanded if some price is
  `≤ 0`.
* **Exercise 15.B.2**: the Walrasian equilibria are exactly the price vectors `p ≫ 0` with
  `p₁/p₂ = (αω₂₁ + βω₂₂)/((1-α)ω₁₁ + (1-β)ω₁₂)` and the demanded allocation (`exercise_15_B_2`);
  comparative statics in `ω₁₁` (`exercise_15_B_2_statics`): the price ratio falls, both consumers
  consume more of good 1, consumer 1 more and consumer 2 less of good 2.
* **Example 15.B.1** (`α = β`, `ω₁ = (1, 2)`, `ω₂ = (2, 1)`): the offer curves, the monotonicity of
  consumer 1's demands in `p₁`, and the equilibrium condition (15.B.2), `p₁/p₂ = α/(1-α)`.
* The offer curve of a Cobb-Douglas consumer passes through his endowment (p. 517), at
  `p = (α/ω₁ᵢ, (1-α)/ω₂ᵢ)` (`cd_endowment_mem_offerCurve`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

/-- **Exercise 15.B.2** (MWG, p. 540). The Cobb-Douglas Edgeworth box economy with exponents
`α, β` and endowments `ω`. -/
noncomputable def cdEconomy (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![cobbDouglasUtility 1 α, cobbDouglasUtility 1 β] ω

/-- The exponent of consumer `i`. -/
def cdExponent (α β : ℝ) : Fin 2 → ℝ := ![α, β]

theorem cdEconomy_u (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    (cdEconomy α β ω).u i = cobbDouglasUtility 1 (cdExponent α β i) := by
  fin_cases i <;> rfl

/-- A Cobb-Douglas consumer demands nothing when the price of good 1 is `≤ 0`, provided some
affordable bundle has a positive amount of good 2. -/
theorem cd_no_demand_0 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ} (hp : p 0 ≤ 0)
    {w : ℝ} {z : Fin 2 → ℝ} (hz : z ∈ budgetSet p w) (hz1 : 0 < z 1) :
    walrasianDemand (cobbDouglasUtility 1 α) p w = ∅ := by
  have h1 : 0 < 1 - α := by linarith
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hx0 := hx.1.1 0
  have hx1 := hx.1.1 1
  set y : Fin 2 → ℝ := (if 0 < x 1 then x else z) + Pi.single 0 1 with hy
  have hyb : y ∈ budgetSet p w := by
    have hb : (if 0 < x 1 then x else z) ∈ budgetSet p w := by split_ifs; exacts [hx.1, hz]
    refine ⟨fun l => add_nonneg (hb.1 l) (by simp [Pi.single_apply]; split_ifs <;> norm_num),
      ?_⟩
    have : p ⬝ᵥ y = p ⬝ᵥ (if 0 < x 1 then x else z) + p 0 := by simp [hy, dotProduct_add]
    rw [this]
    linarith [hb.2]
  have := hx.2 y hyb
  simp only [cobbDouglasUtility, one_mul, hy, Pi.add_apply] at this
  split_ifs at this with hpos
  · simp only [Pi.single_eq_same, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    have a1 : x 0 ^ α < (x 0 + 1) ^ α := Real.rpow_lt_rpow hx0 (by linarith) hα0
    have a2 : 0 < x 1 ^ (1 - α) := Real.rpow_pos_of_pos hpos _
    nlinarith
  · simp only [Pi.single_eq_same, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
      not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    have hx1' : x 1 = 0 := le_antisymm (not_lt.1 hpos) hx1
    rw [hx1', Real.zero_rpow h1.ne', mul_zero] at this
    have a1 : 0 < (z 0 + 1) ^ α := Real.rpow_pos_of_pos (by linarith [hz.1 0]) _
    have a2 : 0 < z 1 ^ (1 - α) := Real.rpow_pos_of_pos hz1 _
    nlinarith [mul_pos a1 a2]

/-- The Cobb-Douglas utility with the goods swapped. -/
theorem cobbDouglas_swap (α : ℝ) (x : Fin 2 → ℝ) :
    cobbDouglasUtility 1 α x = cobbDouglasUtility 1 (1 - α) ![x 1, x 0] := by
  simp [cobbDouglasUtility, mul_comm]

/-- A Cobb-Douglas consumer demands nothing when the price of good 2 is `≤ 0`, provided some
affordable bundle has a positive amount of good 1. -/
theorem cd_no_demand_1 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ} (hp : p 1 ≤ 0)
    {w : ℝ} {z : Fin 2 → ℝ} (hz : z ∈ budgetSet p w) (hz0 : 0 < z 0) :
    walrasianDemand (cobbDouglasUtility 1 α) p w = ∅ := by
  have hswap : ∀ v : Fin 2 → ℝ, ![(![v 1, v 0] : Fin 2 → ℝ) 1, ![v 1, v 0] 0] = v := by
    intro v
    funext l
    fin_cases l <;> rfl
  have hdot : ∀ v : Fin 2 → ℝ, (![p 1, p 0] : Fin 2 → ℝ) ⬝ᵥ ![v 1, v 0] = p ⬝ᵥ v := by
    intro v
    simp [dotProduct, Fin.sum_univ_two, add_comm]
  have hz' : (![z 1, z 0] : Fin 2 → ℝ) ∈ budgetSet ![p 1, p 0] w := by
    refine ⟨fun l => ?_, by rw [hdot]; exact hz.2⟩
    fin_cases l
    · exact hz.1 1
    · exact hz.1 0
  have hempty := cd_no_demand_0 (α := 1 - α) (by linarith) (by linarith)
    (p := ![p 1, p 0]) (by simpa using hp) hz' (by simpa using hz0)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hmem : (![x 1, x 0] : Fin 2 → ℝ) ∈ walrasianDemand (cobbDouglasUtility 1 (1 - α))
      ![p 1, p 0] w := by
    refine ⟨⟨fun l => ?_, by rw [hdot]; exact hx.1.2⟩, fun y hy => ?_⟩
    · fin_cases l
      · exact hx.1.1 1
      · exact hx.1.1 0
    · have hy' : (![y 1, y 0] : Fin 2 → ℝ) ∈ budgetSet p w := by
        refine ⟨fun l => ?_, ?_⟩
        · fin_cases l
          · exact hy.1 1
          · exact hy.1 0
        · have := hy.2
          rw [← hdot, hswap]
          exact this
      have h1 := hx.2 _ hy'
      rw [cobbDouglas_swap α, cobbDouglas_swap α x, hswap] at h1
      simpa using h1
  rw [hempty] at hmem
  exact hmem

variable {α β : ℝ} {ω : Fin 2 → Fin 2 → ℝ} {i : Fin 2}

/-- Consumer `i`'s demand in the Cobb-Douglas box at `p ≫ 0` (Example 3.D.1, p. 519): the single
bundle `(αᵢ p·ωᵢ / p₁, (1-αᵢ) p·ωᵢ / p₂)`. -/
theorem cd_demand_eq (hα : 0 < cdExponent α β i ∧ cdExponent α β i < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hω : ∀ l, 0 ≤ ω i l) :
    (cdEconomy α β ω).demand i p = {cobbDouglasDemand (cdExponent α β i) p (p ⬝ᵥ ω i)} := by
  have hw : 0 ≤ p ⬝ᵥ ω i := dotProduct_nonneg_of_nonneg (fun l => (hp l).le) hω
  have := example_3_D_1 one_pos hα.1 hα.2 hp hw
  rw [← this]
  unfold ExchangeEconomy.demand
  rw [cdEconomy_u]
  rfl

/-- If some price is `≤ 0`, a Cobb-Douglas consumer with `ωᵢ ≫ 0` demands nothing. -/
theorem cd_demand_empty (hα : 0 < cdExponent α β i ∧ cdExponent α β i < 1) {p : Fin 2 → ℝ}
    (hp : ¬ StrictlyPositive p) (hω : ∀ l, 0 < ω i l) : (cdEconomy α β ω).demand i p = ∅ := by
  have hb : ω i ∈ budgetSet p (p ⬝ᵥ ω i) := ⟨fun l => (hω l).le, le_rfl⟩
  have heq : (cdEconomy α β ω).demand i p =
      walrasianDemand (cobbDouglasUtility 1 (cdExponent α β i)) p (p ⬝ᵥ ω i) := by
    unfold ExchangeEconomy.demand
    rw [cdEconomy_u]
    rfl
  rw [heq]
  simp only [StrictlyPositive, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  fin_cases l
  · exact cd_no_demand_0 hα.1 hα.2 hl hb (hω 1)
  · exact cd_no_demand_1 hα.1 hα.2 hl hb (hω 0)

/-- The equilibrium allocation of the Cobb-Douglas box at prices `p`. -/
noncomputable def cdAllocation (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun i => cobbDouglasDemand (cdExponent α β i) p (p ⬝ᵥ ω i)

/-- **Exercise 15.B.2** (MWG, p. 540). In the Cobb-Douglas Edgeworth box with `α, β ∈ (0, 1)` and
`ωᵢ ≫ 0`, `(p, x)` is a Walrasian equilibrium if and only if `p ≫ 0`,
`p₁ ((1-α)ω₁₁ + (1-β)ω₁₂) = p₂ (αω₂₁ + βω₂₂)` and `x` is the demanded allocation. Hence the
equilibrium price ratio and allocation are unique. -/
theorem exercise_15_B_2 (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hω : ∀ i l, 0 < ω i l) (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (cdEconomy α β ω).IsDemandEqm p x ↔ StrictlyPositive p ∧
      p 0 * ((1 - α) * ω 0 0 + (1 - β) * ω 1 0) = p 1 * (α * ω 0 1 + β * ω 1 1) ∧
      x = cdAllocation α β ω p := by
  have hex : ∀ i, 0 < cdExponent α β i ∧ cdExponent α β i < 1 := by
    intro i
    fin_cases i
    · exact ⟨hα0, hα1⟩
    · exact ⟨hβ0, hβ1⟩
  have htot : ∀ l, (cdEconomy α β ω).totalEndowment l = ω 0 l + ω 1 l := by
    intro l
    simp [ExchangeEconomy.totalEndowment, cdEconomy, ExchangeEconomy.ofOrthant,
      Fin.sum_univ_two]
  constructor
  · rintro ⟨hbox, hd⟩
    have hp : StrictlyPositive p := by
      by_contra hp
      have := hd 0
      rw [cd_demand_empty (hex 0) hp (hω 0)] at this
      exact this
    have hx : x = cdAllocation α β ω p := by
      funext i
      have := hd i
      rw [cd_demand_eq (hex i) hp fun l => (hω i l).le] at this
      exact this
    refine ⟨hp, ?_, hx⟩
    have h1 := congrFun hbox.2 0
    rw [htot, Finset.sum_apply, Fin.sum_univ_two, hx] at h1
    simp only [cdAllocation, cobbDouglasDemand, cdExponent, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have hp0 := (hp 0).ne'
    field_simp at h1
    linarith
  · rintro ⟨hp, hrel, rfl⟩
    have hd : ∀ i, cdAllocation α β ω p i ∈ (cdEconomy α β ω).demand i p := by
      intro i
      rw [cd_demand_eq (hex i) hp fun l => (hω i l).le]
      rfl
    refine exercise_15_B_1b (fun i => rfl) (fun i => ?_) hp hd ?_
    · rw [cdEconomy_u]
      exact cobbDouglas_lns (hex i).1 (hex i).2
    · rw [htot, Fin.sum_univ_two]
      simp only [cdAllocation, cobbDouglasDemand, cdExponent, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      have hp0 := (hp 0).ne'
      field_simp
      linarith

/-- The equilibrium price ratio `p₁/p₂` of Exercise 15.B.2 as a function of `ω₁₁`. -/
noncomputable def cdPriceRatio (α β : ℝ) (ω : Fin 2 → Fin 2 → ℝ) (a : ℝ) : ℝ :=
  (α * ω 0 1 + β * ω 1 1) / ((1 - α) * a + (1 - β) * ω 1 0)

/-- **Exercise 15.B.2** (MWG, p. 540), comparative statics. With `p₂ = 1` and `q(ω₁₁)` the
equilibrium price of good 1, a differential increase in `ω₁₁` lowers `q`, raises both consumers'
consumption of good 1 (`x₁₁ = α(ω₁₁ + ω₂₁/q)`, `x₁₂ = β(ω₁₂ + ω₂₂/q)`), raises consumer 1's and
lowers consumer 2's consumption of good 2 (`x₂₁ = (1-α)(qω₁₁ + ω₂₁)`, `x₂₂ = (1-β)(qω₁₂ + ω₂₂)`). -/
theorem exercise_15_B_2_statics (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hω : ∀ i l, 0 < ω i l) {a : ℝ} (ha : 0 < a) :
    ∃ q' x11' x21' x12' x22' : ℝ, HasDerivAt (cdPriceRatio α β ω) q' a ∧ q' < 0 ∧
      HasDerivAt (fun t => α * (t + ω 0 1 / cdPriceRatio α β ω t)) x11' a ∧ 0 < x11' ∧
      HasDerivAt (fun t => (1 - α) * (cdPriceRatio α β ω t * t + ω 0 1)) x21' a ∧ 0 < x21' ∧
      HasDerivAt (fun t => β * (ω 1 0 + ω 1 1 / cdPriceRatio α β ω t)) x12' a ∧ 0 < x12' ∧
      HasDerivAt (fun t => (1 - β) * (cdPriceRatio α β ω t * ω 1 0 + ω 1 1)) x22' a ∧
        x22' < 0 := by
  set N := α * ω 0 1 + β * ω 1 1 with hN
  set D := (1 - α) * a + (1 - β) * ω 1 0 with hD
  have hN0 : 0 < N := by nlinarith [hω 0 1, hω 1 1]
  have hD0 : 0 < D := by nlinarith [hω 1 0]
  have hDf : HasDerivAt (fun t => (1 - α) * t + (1 - β) * ω 1 0) (1 - α) a := by
    simpa using ((hasDerivAt_id a).const_mul (1 - α)).add_const ((1 - β) * ω 1 0)
  have hq : HasDerivAt (cdPriceRatio α β ω) (-(N * (1 - α)) / D ^ 2) a := by
    have := (hasDerivAt_const a N).div hDf hD0.ne'
    have h2 : cdPriceRatio α β ω = (fun _ => N) / fun t => (1 - α) * t + (1 - β) * ω 1 0 := by
      funext t
      simp [cdPriceRatio, hN]
    rw [h2]
    convert this using 1
    simp [hD]
  set q := N / D with hqdef
  have hqa : cdPriceRatio α β ω a = q := rfl
  have hq0 : 0 < q := div_pos hN0 hD0
  have hinv : HasDerivAt (fun t => (cdPriceRatio α β ω t)⁻¹) (-(-(N * (1 - α)) / D ^ 2) / q ^ 2)
      a := by
    have := hq.inv (by rw [hqa]; exact hq0.ne')
    rw [hqa] at this
    exact this
  set r := -(-(N * (1 - α)) / D ^ 2) / q ^ 2 with hr
  have hr0 : 0 < r := by
    rw [hr, neg_div (D ^ 2), neg_neg]
    have : 0 < 1 - α := by linarith
    positivity
  have hq'0 : -(N * (1 - α)) / D ^ 2 < 0 := by
    have : 0 < 1 - α := by linarith
    have : 0 < N * (1 - α) / D ^ 2 := by positivity
    rw [neg_div]
    linarith
  have d11 : HasDerivAt (fun t => α * (t + ω 0 1 / cdPriceRatio α β ω t))
      (α * (1 + ω 0 1 * r)) a := by
    have := ((hasDerivAt_id a).add (hinv.const_mul (ω 0 1))).const_mul α
    convert this using 1
    funext t
    simp [div_eq_mul_inv]
  have d21 : HasDerivAt (fun t => (1 - α) * (cdPriceRatio α β ω t * t + ω 0 1))
      ((1 - α) * (-(N * (1 - α)) / D ^ 2 * a + q)) a := by
    have := ((hq.mul (hasDerivAt_id a)).add_const (ω 0 1)).const_mul (1 - α)
    convert this using 1
    · funext t
      simp [id]
    · rw [hqa]
      simp [id]
  have d12 : HasDerivAt (fun t => β * (ω 1 0 + ω 1 1 / cdPriceRatio α β ω t))
      (β * (ω 1 1 * r)) a := by
    have := ((hinv.const_mul (ω 1 1)).const_add (ω 1 0)).const_mul β
    convert this using 1
    funext t
    simp [div_eq_mul_inv]
  have d22 : HasDerivAt (fun t => (1 - β) * (cdPriceRatio α β ω t * ω 1 0 + ω 1 1))
      ((1 - β) * (-(N * (1 - α)) / D ^ 2 * ω 1 0)) a :=
    ((hq.mul_const (ω 1 0)).add_const (ω 1 1)).const_mul (1 - β)
  refine ⟨_, _, _, _, _, hq, hq'0, d11, ?_, d21, ?_, d12, ?_, d22, ?_⟩
  · have h01 := hω 0 1
    nlinarith [mul_pos h01 hr0]
  · rw [hqdef]
    have h10 := hω 1 0
    have key : -(N * (1 - α)) / D ^ 2 * a + N / D = N * ((1 - β) * ω 1 0) / D ^ 2 := by
      field_simp
      rw [hD]
      ring
    rw [key]
    have h1a : 0 < 1 - α := by linarith
    have h1b : 0 < 1 - β := by linarith
    have : 0 < N * ((1 - β) * ω 1 0) / D ^ 2 := by positivity
    nlinarith
  · have h11 := hω 1 1
    nlinarith [mul_pos h11 hr0]
  · have h10 := hω 1 0
    have h1b : 0 < 1 - β := by linarith
    nlinarith [mul_pos h1b h10]

/-- **Example 15.B.1** (MWG, p. 519): equal exponents `α` and endowments `ω₁ = (1, 2)`,
`ω₂ = (2, 1)`. -/
def example15B1Endowment : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![2, 1]]

/-- **Example 15.B.1** (MWG, p. 519). At `p ≫ 0` consumer 1's offer curve is
`OC₁(p) = (α(p₁ + 2p₂)/p₁, (1-α)(p₁ + 2p₂)/p₂)` and consumer 2's is
`OC₂(p) = (α(2p₁ + p₂)/p₁, (1-α)(2p₁ + p₂)/p₂)` (p. 520). -/
theorem example_15_B_1_offerCurves (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) :
    (cdEconomy α α example15B1Endowment).demand 0 p =
        {![α * (p 0 + 2 * p 1) / p 0, (1 - α) * (p 0 + 2 * p 1) / p 1]} ∧
      (cdEconomy α α example15B1Endowment).demand 1 p =
        {![α * (2 * p 0 + p 1) / p 0, (1 - α) * (2 * p 0 + p 1) / p 1]} := by
  constructor
  · rw [cd_demand_eq (i := 0) ⟨hα0, hα1⟩ hp
      (fun l => by fin_cases l <;> norm_num [example15B1Endowment])]
    congr 1
    funext l
    fin_cases l <;> simp [cobbDouglasDemand, cdExponent, example15B1Endowment, dotProduct,
      Fin.sum_univ_two, mul_comm]
  · rw [cd_demand_eq (i := 1) ⟨hα0, hα1⟩ hp
      (fun l => by fin_cases l <;> norm_num [example15B1Endowment])]
    congr 1
    funext l
    fin_cases l <;> simp [cobbDouglasDemand, cdExponent, example15B1Endowment, dotProduct,
      Fin.sum_univ_two, mul_comm]

/-- **Example 15.B.1** (MWG, p. 520). Consumer 1's demand for good 1, `α(p₁ + 2p₂)/p₁`, is strictly
decreasing and his demand for good 2, `(1-α)(p₁ + 2p₂)/p₂`, strictly increasing in `p₁`
(for fixed `p₂ > 0`). -/
theorem example_15_B_1_monotone (hα0 : 0 < α) (hα1 : α < 1) {p₂ : ℝ} (hp₂ : 0 < p₂) :
    StrictAntiOn (fun p₁ => α * (p₁ + 2 * p₂) / p₁) (Set.Ioi 0) ∧
      StrictMonoOn (fun p₁ => (1 - α) * (p₁ + 2 * p₂) / p₂) (Set.Ioi 0) := by
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    simp only
    rw [div_lt_div_iff₀ hb ha]
    nlinarith [mul_pos hα0 hp₂]
  · intro a _ b _ hab
    simp only
    rw [div_lt_div_iff_of_pos_right hp₂]
    nlinarith

/-- **Example 15.B.1** (MWG, p. 520), equation (15.B.2): the Walrasian equilibria are exactly the
prices `p ≫ 0` with `p₁/p₂ = α/(1-α)`, i.e. `p₁(1-α) = p₂α`, with the demanded allocation. -/
theorem example_15_B_1 (hα0 : 0 < α) (hα1 : α < 1) (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (cdEconomy α α example15B1Endowment).IsDemandEqm p x ↔
      StrictlyPositive p ∧ p 0 * (1 - α) = p 1 * α ∧
        x = cdAllocation α α example15B1Endowment p := by
  rw [exercise_15_B_2 hα0 hα1 hα0 hα1 (fun i l => by
    fin_cases i <;> fin_cases l <;> norm_num [example15B1Endowment])]
  have e : ∀ q : ℝ, (q * ((1 - α) * example15B1Endowment 0 0 + (1 - α) *
      example15B1Endowment 1 0) = p 1 * (α * example15B1Endowment 0 1 + α *
      example15B1Endowment 1 1)) ↔ q * (1 - α) = p 1 * α := by
    intro q
    simp only [example15B1Endowment, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith
  rw [e]

/-- **Section 15.B** (MWG, p. 517), for Cobb-Douglas consumers: the offer curve of consumer `i`
(with `ωᵢ ≫ 0`) passes through his endowment, which is demanded at `p = (αᵢ/ω₁ᵢ, (1-αᵢ)/ω₂ᵢ)`. -/
theorem cd_endowment_mem_offerCurve (hα : 0 < cdExponent α β i ∧ cdExponent α β i < 1)
    (hω : ∀ l, 0 < ω i l) : ω i ∈ (cdEconomy α β ω).offerCurve i := by
  set a := cdExponent α β i
  set p : Fin 2 → ℝ := ![a / ω i 0, (1 - a) / ω i 1] with hp
  have hpp : StrictlyPositive p := by
    intro l
    have : 0 < 1 - a := by linarith [hα.2]
    fin_cases l
    · exact div_pos hα.1 (hω 0)
    · exact div_pos this (hω 1)
  refine ⟨p, hpp, ?_⟩
  rw [cd_demand_eq hα hpp fun l => (hω l).le]
  have hw : p ⬝ᵥ ω i = 1 := by
    simp only [hp, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [(hω 0).ne', (hω 1).ne']
    ring
  rw [Set.mem_singleton_iff, hw]
  have h1a : 0 < 1 - a := by linarith [hα.2]
  funext l
  fin_cases l
  · change ω i 0 = a * 1 / (a / ω i 0)
    field_simp [(hω 0).ne', hα.1.ne']
  · change ω i 1 = (1 - a) * 1 / ((1 - a) / ω i 1)
    field_simp [(hω 1).ne', h1a.ne']

end MWG.GeneralEquilibriumExamples
