/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.CobbDouglasBox
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Nonexistence of equilibrium and failures of the second welfare theorem (MWG pp. 522, 525)

The book's Figures 15.B.10 and 15.B.14 are drawn without formulas; we give concrete economies with
the features described in the text and prove the claims.

* **Figure 15.B.10(a)** (`fig10aEconomy`): `u₁ = √x₁₁ + x₂₁`, `ω₁ = (0, 1)` (the indifference curve
  through `ω₁` has infinite slope there, yet more good 1 is strictly preferred) and `u₂ = x₁₂`,
  `ω₂ = (1, 0)`. There is no Walrasian equilibrium (`fig_15_B_10a_no_eqm`); at `p ≫ 0` consumer 2
  keeps `ω₂` and `ω₁` is never optimal for consumer 1; consumer 1 has no demand when `p₂ = 0`;
  consumer 2's preferences are not strongly monotone. The endowment is Pareto optimal but not
  supportable as an equilibrium with transfers (p. 525, `fig_15_B_10a_po_not_supportable`).
* **Figure 15.B.10(b)** (`fig10bEconomy`): consumer 1 has the nonconvex (strongly monotone,
  continuous) utility `x₁₁² + x₂₁²`, consumer 2 the Cobb-Douglas utility `x₁₂^{1/2}x₂₂^{1/2}`,
  `ω₁ = ω₂ = (1, 1)`: consumer 1 only demands corner bundles, and there is no Walrasian
  equilibrium (`fig_15_B_10b_no_eqm`).
* **Figure 15.B.14** (`fig14Economy`): `u₁ = x₁₁² + x₂₁²` and the convex, continuous and strongly
  monotone `u₂ = min(3x₁₂ + x₂₂, x₁₂ + 3x₂₂)`, `ω₁ = ω₂ = (1, 1)`: the allocation `((1,1),(1,1))`
  is Pareto optimal but not supportable as an equilibrium with transfers (`fig_15_B_14`).
* **Exercise 15.B.9** (Alphanse and Betatrix): the unique equilibrium
  (`exercise_15_B_9`: `p_P/(p_P + p_B) = a/30`, `a = (39 - √41)/2`), and with 5 units of Perrier the
  equilibria have Brie free and a continuum of allocations (`exercise_15_B_9_second`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-! ### Figure 15.B.10(a) -/

/-- Consumer 1's utility in Figure 15.B.10(a): `√x₁ + x₂`. -/
noncomputable def fig10aU1 (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + x 1

/-- Consumer 2's utility in Figure 15.B.10(a): `x₁` (he desires only good 1). -/
def fig10aU2 (x : Fin 2 → ℝ) : ℝ := x 0

/-- **Figure 15.B.10(a)** (MWG, p. 522): `u₁ = √x₁₁ + x₂₁`, `u₂ = x₁₂`, `ω₁ = (0, 1)`,
`ω₂ = (1, 0)`. -/
noncomputable def fig10aEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![fig10aU1, fig10aU2] ![![0, 1], ![1, 0]]

theorem fig10a_u0 : fig10aEconomy.u 0 = fig10aU1 := rfl
theorem fig10a_u1 : fig10aEconomy.u 1 = fig10aU2 := rfl
theorem fig10a_ω0 : fig10aEconomy.ω 0 = ![0, 1] := rfl
theorem fig10a_ω1 : fig10aEconomy.ω 1 = ![1, 0] := rfl

/-- Consumer 1's utility in Figure 15.B.10(a) is locally nonsatiated. -/
theorem fig10a_lns0 : UtilityLNS fig10aU1 :=
  exercise_3_B_1b_orthant two_pos fun x _ y _ hxy => by
    refine ⟨?_, ?_⟩ <;> simp only [utilityPref, fig10aU1, not_le] <;>
      linarith [Real.sqrt_le_sqrt (hxy 0).le, hxy 1]

/-- Consumer 2's utility in Figure 15.B.10(a) is locally nonsatiated. -/
theorem fig10a_lns1 : UtilityLNS fig10aU2 :=
  exercise_3_B_1b_orthant two_pos fun x _ y _ hxy => by
    refine ⟨?_, ?_⟩ <;> simp only [utilityPref, fig10aU2, not_le] <;> linarith [hxy 0]

/-- The utilities of `fig10aEconomy` are locally nonsatiated. -/
theorem fig10a_lns (i : Fin 2) : UtilityLNS (fig10aEconomy.u i) := by
  fin_cases i
  · exact fig10a_lns0
  · exact fig10a_lns1

/-- **Figure 15.B.10(a)** (MWG, p. 522): consumer 2's preferences are not strongly monotone. -/
theorem fig_15_B_10a_not_stronglyMonotone : ¬ UtilityStronglyMonotone (fig10aEconomy.u 1) := by
  intro h
  have := h.lt (x := 0) (y := Pi.single 1 1) (fun l => le_refl _) (fun l => by
    fin_cases l <;> simp) (fun he => by simpa using congrFun he 1)
  simp [fig10a_u1, fig10aU2] at this

theorem fig10a_dot (p z : Fin 2 → ℝ) : p ⬝ᵥ z = p 0 * z 0 + p 1 * z 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- **Figure 15.B.10(a)** (MWG, p. 522): at `p ≫ 0` consumer 2's demand is his endowment. -/
theorem fig_15_B_10a_demand1 {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    fig10aEconomy.demand 1 p = {![1, 0]} := by
  have hω : p ⬝ᵥ fig10aEconomy.ω 1 = p 0 := by simp [fig10a_ω1, Matrix.vecHead]
  have hp0 := hp 0
  have hp1 := hp 1
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hb⟩, hmax⟩
    rw [hω, fig10a_dot] at hb
    have hmem : (![1, 0] : Fin 2 → ℝ) ∈ budgetSetOn (fig10aEconomy.X 1) p
        (p ⬝ᵥ fig10aEconomy.ω 1) := ⟨fun l => by fin_cases l <;> simp, by
          rw [hω, fig10a_dot]; simp⟩
    have h1 := hmax _ hmem
    simp only [fig10a_u1, fig10aU2, Matrix.cons_val_zero] at h1
    have hy0 := hy 0
    have hy1 := hy 1
    have e0 : y 0 = 1 := by nlinarith
    have e1 : y 1 = 0 := by nlinarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    refine ⟨⟨fun l => by fin_cases l <;> simp, by rw [hω, fig10a_dot]; simp⟩, fun z hz => ?_⟩
    have hb := hz.2
    rw [hω, fig10a_dot] at hb
    simp only [fig10a_u1, fig10aU2, Matrix.cons_val_zero]
    nlinarith [hz.1 1]

/-- **Figure 15.B.10(a)** (MWG, p. 522): at `p ≫ 0` consumer 1's endowment `(0, 1)` is not optimal:
`(ε, 1 - kε)`, `k = p₁/p₂`, `ε = 1/(4(k+1)²)`, is affordable and strictly better. -/
theorem fig_15_B_10a_endowment_not_optimal {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    fig10aEconomy.ω 0 ∉ fig10aEconomy.demand 0 p := by
  rintro ⟨-, hmax⟩
  set k := p 0 / p 1 with hk
  have hk0 : 0 < k := div_pos (hp 0) (hp 1)
  set ε := 1 / (4 * (k + 1) ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hsq : Real.sqrt ε = 1 / (2 * (k + 1)) := by
    rw [hε, show 4 * (k + 1) ^ 2 = (2 * (k + 1)) ^ 2 by ring, one_div, Real.sqrt_inv,
      Real.sqrt_sq (by positivity), one_div]
  have hkε : k * ε ≤ 1 / 4 := by
    rw [hε, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcost : p 1 * (k * ε) = p 0 * ε := by
    rw [hk]
    field_simp [(hp 1).ne']
  set y : Fin 2 → ℝ := ![ε, 1 - k * ε] with hy
  have hmem : y ∈ budgetSetOn (fig10aEconomy.X 0) p (p ⬝ᵥ fig10aEconomy.ω 0) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa [hy] using hε0.le
      · simp only [hy]
        simp
        linarith
    · rw [fig10a_dot, fig10a_dot, fig10a_ω0, hy]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith
  have h1 := hmax y hmem
  rw [fig10a_u0, fig10a_ω0, hy] at h1
  simp only [fig10aU1, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_zero,
    zero_add] at h1
  rw [hsq] at h1
  have : k * ε < 1 / (2 * (k + 1)) := by
    rw [hε, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **Figure 15.B.10(a)** (MWG, p. 522): consumer 1's demand for good 2 is unbounded when
`p₂ = 0`: for `p₂ ≤ 0` he has no demand. -/
theorem fig_15_B_10a_no_demand0 {p : Fin 2 → ℝ} (hp1 : p 1 ≤ 0) :
    fig10aEconomy.demand 0 p = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hy, hb⟩, hmax⟩
  have hmem : y + Pi.single 1 1 ∈ budgetSetOn (fig10aEconomy.X 0) p
      (p ⬝ᵥ fig10aEconomy.ω 0) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using hy 0
      · simp; linarith [hy 1]
    · rw [dotProduct_add]
      simp only [dotProduct_single, mul_one]
      linarith
  have := hmax _ hmem
  simp [fig10a_u0, fig10aU1] at this
  linarith

/-- **Figure 15.B.10(a)** (MWG, p. 522): there is no Walrasian equilibrium (Definition 15.B.1). -/
theorem fig_15_B_10a_no_eqm (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    ¬ fig10aEconomy.IsWalrasEqm p x := by
  intro h
  rw [isWalrasEqm_iff_isDemandEqm (fun _ => rfl) fig10a_lns] at h
  obtain ⟨hbox, hd⟩ := h
  by_cases hp0 : 0 < p 0
  · by_cases hp1 : 0 < p 1
    · have hp : StrictlyPositive p := fun l => by fin_cases l; exacts [hp0, hp1]
      have h1 := hd 1
      rw [fig_15_B_10a_demand1 hp, Set.mem_singleton_iff] at h1
      have h0 : x 0 = fig10aEconomy.ω 0 := by
        have hs := hbox.2
        simp only [Fin.sum_univ_two, ExchangeEconomy.totalEndowment] at hs
        rw [h1, fig10a_ω0, fig10a_ω1] at hs
        rw [fig10a_ω0]
        funext l
        have := congrFun hs l
        fin_cases l <;> simp at this ⊢ <;> linarith
      exact fig_15_B_10a_endowment_not_optimal hp (h0 ▸ hd 0)
    · have := hd 0
      rw [fig_15_B_10a_no_demand0 (not_lt.1 hp1)] at this
      exact this
  · -- good 1 is free for consumer 2
    rw [not_lt] at hp0
    obtain ⟨⟨hy, hb⟩, hmax⟩ := hd 1
    have hmem : x 1 + Pi.single 0 1 ∈ budgetSetOn (fig10aEconomy.X 1) p
        (p ⬝ᵥ fig10aEconomy.ω 1) := by
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simp; linarith [hy 0]
        · simpa using hy 1
      · rw [dotProduct_add]
        simp only [dotProduct_single, mul_one]
        linarith
    have := hmax _ hmem
    simp [fig10a_u1, fig10aU2] at this
    linarith

/-- **Section 15.B** (MWG, p. 525), Figure 15.B.10(a): the endowment allocation is Pareto optimal
but cannot be supported as an equilibrium with transfers. -/
theorem fig_15_B_10a_po_not_supportable :
    fig10aEconomy.IsParetoOptimal fig10aEconomy.ω ∧
      ¬ fig10aEconomy.IsSupportable fig10aEconomy.ω := by
  have hbox : fig10aEconomy.InBox fig10aEconomy.ω :=
    ⟨fun i l => by fin_cases i <;> fin_cases l <;> simp [fig10aEconomy,
      ExchangeEconomy.ofOrthant], rfl⟩
  refine ⟨⟨hbox, ?_⟩, ?_⟩
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs := hx'.2
    have hs0 := congrFun hs 0
    have hs1 := congrFun hs 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment,
      fig10a_ω0, fig10a_ω1] at hs0 hs1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hm : ∀ j l, 0 ≤ x' j l := fun j l => hx'.1 j l
    have h1 := hle 1
    have h0 := hle 0
    rw [fig10a_u1, fig10a_ω1] at h1
    rw [fig10a_u0, fig10a_ω0] at h0
    simp only [fig10aU1, fig10aU2, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_zero,
      zero_add] at h0 h1
    have e : x' 0 0 = 0 := by linarith [hm 0 0]
    have hsq : Real.sqrt (x' 0 0) = 0 := by rw [e, Real.sqrt_zero]
    fin_cases i
    · simp only [Fin.zero_eta, fig10a_u0, fig10a_ω0, fig10aU1, Matrix.cons_val_zero,
        Matrix.cons_val_one, Real.sqrt_zero, zero_add, hsq] at hi
      linarith [hm 1 1]
    · simp only [Fin.mk_one, fig10a_u1, fig10a_ω1, fig10aU2, Matrix.cons_val_zero] at hi
      linarith [hm 0 0]
  · rintro ⟨p, T, h⟩
    have hT : ∀ i, T i = 0 := fun i => by
      have := h.wealth_eq (fun _ => rfl) fig10a_lns i
      linarith
    apply fig_15_B_10a_no_eqm p fig10aEconomy.ω
    refine ⟨hbox, fun i y hy => h.2.2 i y hy.1 ?_⟩
    rw [hT i, add_zero]
    exact hy.2

/-! ### Figure 15.B.10(b) and Figure 15.B.14: a nonconvex consumer -/

/-- The nonconvex utility `x₁² + x₂²`. -/
def sqUtility (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- On `ℝ²₊`, `x₁² + x₂²` is continuous and strongly monotone but not quasiconcave. -/
theorem sqUtility_props : ContinuousOn sqUtility (nonnegOrthant 2) ∧
    UtilityStronglyMonotone sqUtility ∧ ¬ PrefConvex (nonnegOrthant 2) (utilityPref sqUtility) :=
  by
  refine ⟨by unfold sqUtility; fun_prop, fun x hx y hy hxy hne => ⟨?_, ?_⟩, fun h => ?_⟩
  · simp only [utilityPref, sqUtility]
    nlinarith [hxy 0, hxy 1, hx 0, hx 1]
  · simp only [utilityPref, sqUtility, not_le]
    have hl : x 0 < y 0 ∨ x 1 < y 1 := by
      by_contra hall
      simp only [not_or, not_lt] at hall
      exact hne (funext fun l => by
        fin_cases l
        · exact le_antisymm hall.1 (hxy 0)
        · exact le_antisymm hall.2 (hxy 1))
    rcases hl with hl | hl
    · nlinarith [hxy 0, hxy 1, hx 0, hx 1]
    · nlinarith [hxy 0, hxy 1, hx 0, hx 1]
  · have := quasiconcave_of_prefConvex h (y := ![1, 0]) (z := ![0, 1])
      (fun l => by fin_cases l <;> simp) (fun l => by fin_cases l <;> simp)
      (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    simp [sqUtility] at this
    norm_num at this

/-- The demand of the `x₁² + x₂²` consumer at `p ≫ 0` and wealth `w ≥ 0` consists of corner
bundles: `x₁x₂ = 0` and `x₁ + x₂ = w / min p`. -/
theorem sqUtility_demand_corner {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w)
    {x : Fin 2 → ℝ} (hx : x ∈ walrasianDemand sqUtility p w) :
    x 0 * x 1 = 0 ∧ x 0 + x 1 = w / min (p 0) (p 1) := by
  set m := min (p 0) (p 1) with hm
  have hm0 : 0 < m := lt_min (hp 0) (hp 1)
  obtain ⟨⟨hx0, hb⟩, hmax⟩ := hx
  have hb' : p 0 * x 0 + p 1 * x 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hb
  -- the corner of the cheaper good
  have hcorner : (w / m) ^ 2 ≤ sqUtility x := by
    rcases le_total (p 0) (p 1) with h | h
    · have hmeq : m = p 0 := min_eq_left h
      have := hmax ![w / m, 0] ⟨fun l => by fin_cases l <;> simp [div_nonneg hw hm0.le],
        by simp [dotProduct, Fin.sum_univ_two, hmeq, mul_div_cancel₀ _ (hp 0).ne']⟩
      simpa [sqUtility] using this
    · have hmeq : m = p 1 := min_eq_right h
      have := hmax ![0, w / m] ⟨fun l => by fin_cases l <;> simp [div_nonneg hw hm0.le],
        by simp [dotProduct, Fin.sum_univ_two, hmeq, mul_div_cancel₀ _ (hp 1).ne']⟩
      simpa [sqUtility] using this
  have hsum : x 0 + x 1 ≤ w / m := by
    rw [le_div_iff₀ hm0]
    have h0 : m ≤ p 0 := min_le_left _ _
    have h1 : m ≤ p 1 := min_le_right _ _
    nlinarith [hx0 0, hx0 1]
  have hsq : sqUtility x ≤ (x 0 + x 1) ^ 2 := by
    simp only [sqUtility]
    nlinarith [hx0 0, hx0 1]
  have hpow : (x 0 + x 1) ^ 2 ≤ (w / m) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg (hx0 0) (hx0 1)) hsum 2
  have heq : (x 0 + x 1) ^ 2 = (w / m) ^ 2 := le_antisymm hpow (hcorner.trans hsq)
  refine ⟨?_, ?_⟩
  · simp only [sqUtility] at hsq hcorner
    nlinarith [hx0 0, hx0 1]
  · exact (pow_left_inj₀ (add_nonneg (hx0 0) (hx0 1)) (div_nonneg hw hm0.le)
      two_ne_zero).1 heq

/-- **Figure 15.B.10(b)** (MWG, p. 522): a nonconvex consumer 1 (`x₁₁² + x₂₁²`) and a Cobb-Douglas
consumer 2 (`x₁₂^{1/2}x₂₂^{1/2}`), both with endowment `(1, 1)`. -/
noncomputable def fig10bEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![sqUtility, cobbDouglasUtility 1 (1 / 2)] ![![1, 1], ![1, 1]]

/-- **Figure 15.B.10(b)** (MWG, p. 522): the economy with a nonconvex consumer has no Walrasian
equilibrium. -/
theorem fig_15_B_10b_no_eqm (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    ¬ fig10bEconomy.IsDemandEqm p x := by
  rintro ⟨hbox, hd⟩
  have hω : ∀ l, (0 : ℝ) < fig10bEconomy.ω 1 l := fun l => by
    fin_cases l <;> simp [fig10bEconomy, ExchangeEconomy.ofOrthant]
  have hd1 := hd 1
  have hdem1 : fig10bEconomy.demand 1 p = walrasianDemand (cobbDouglasUtility 1 (1 / 2)) p
      (p ⬝ᵥ fig10bEconomy.ω 1) := rfl
  by_cases hp : StrictlyPositive p
  · have hw : p ⬝ᵥ fig10bEconomy.ω 1 = p 0 + p 1 := by
      simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
    have hw0 : p ⬝ᵥ fig10bEconomy.ω 0 = p 0 + p 1 := by
      simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
    rw [hdem1, example_3_D_1 one_pos (by norm_num) (by norm_num) hp
      (by rw [hw]; linarith [hp 0, hp 1]), Set.mem_singleton_iff, hw] at hd1
    have hd0 : x 0 ∈ walrasianDemand sqUtility p (p 0 + p 1) := by
      rw [← hw0]
      exact hd 0
    obtain ⟨hc0, hc1⟩ := sqUtility_demand_corner hp (by linarith [hp 0, hp 1]) hd0
    have hs := hbox.2
    have hs0 := congrFun hs 0
    have hs1 := congrFun hs 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment,
      fig10bEconomy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hs0 hs1
    rw [hd1] at hs0 hs1
    simp only [cobbDouglasDemand, Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hp0 := hp 0
    have hp1 := hp 1
    have hx := (hd 0).1.1
    have hbud : p 0 * x 0 0 + p 1 * x 0 1 ≤ p 0 + p 1 := by
      have := hd0.1.2
      simpa [dotProduct, Fin.sum_univ_two] using this
    rcases le_total (p 0) (p 1) with h | h
    · rw [min_eq_left h] at hc1
      rcases mul_eq_zero.1 hc0 with h0 | h0
      · -- consumer 1 takes only good 2
        rw [h0, zero_add] at hc1
        rw [h0, zero_add] at hs0
        rw [h0] at hbud
        field_simp at hs0
        rw [hc1] at hbud
        have : p 1 * ((p 0 + p 1) / p 0) * p 0 ≤ (p 0 + p 1) * p 0 := by nlinarith
        rw [mul_assoc, div_mul_cancel₀ _ hp0.ne'] at this
        nlinarith
      · rw [h0, add_zero] at hc1
        rw [hc1] at hs0
        field_simp at hs0
        nlinarith
    · rw [min_eq_right h] at hc1
      rcases mul_eq_zero.1 hc0 with h0 | h0
      · rw [h0, zero_add] at hc1
        rw [hc1] at hs1
        field_simp at hs1
        nlinarith
      · rw [h0, add_zero] at hc1
        rw [h0, zero_add] at hs1
        rw [h0] at hbud
        field_simp at hs1
        rw [hc1] at hbud
        have : p 0 * ((p 0 + p 1) / p 1) * p 1 ≤ (p 0 + p 1) * p 1 := by nlinarith
        rw [mul_assoc, div_mul_cancel₀ _ hp1.ne'] at this
        nlinarith
  · rcases cd_demand_empty (α := 1 / 2) (β := 1 / 2) (ω := fig10bEconomy.ω) (i := 1)
      ⟨by norm_num [cdExponent], by norm_num [cdExponent]⟩ hp hω |> fun h => (by
        have e : (cdEconomy (1 / 2) (1 / 2) fig10bEconomy.ω).demand 1 p =
            fig10bEconomy.demand 1 p := rfl
        rw [← e, h] at hd1
        exact hd1 : False) with ⟨⟩

/-- **Figure 15.B.14** (MWG, p. 525): consumer 1 is nonconvex (`x₁₁² + x₂₁²`), consumer 2 has the
convex, kinked utility `min(3x₁₂ + x₂₂, x₁₂ + 3x₂₂)`; both endowments are `(1, 1)`. -/
noncomputable def fig14Economy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![sqUtility, fun x => min (3 * x 0 + x 1) (x 0 + 3 * x 1)]
    ![![1, 1], ![1, 1]]

/-- Consumer 2 of Figure 15.B.14 has continuous, convex and strongly monotone preferences. -/
theorem fig14_u2_props :
    ContinuousOn (fig14Economy.u 1) (nonnegOrthant 2) ∧
      PrefConvex (nonnegOrthant 2) (utilityPref (fig14Economy.u 1)) ∧
      UtilityStronglyMonotone (fig14Economy.u 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    fun_prop
  · intro z _ a ha b hb s t hs ht hst
    refine ⟨convex_nonnegOrthant 2 ha.1 hb.1 hs ht hst, ?_⟩
    have h1 := ha.2
    have h2 := hb.2
    simp only [utilityPref, fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, le_min_iff] at h1 h2 ⊢
    set m := min (3 * z 0 + z 1) (z 0 + 3 * z 1)
    have hm : m = s * m + t * m := by rw [← add_mul, hst, one_mul]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1.1 hs, mul_le_mul_of_nonneg_left h1.2 hs,
      mul_le_mul_of_nonneg_left h2.1 ht, mul_le_mul_of_nonneg_left h2.2 ht]
  · intro x hx y hy hxy hne
    simp only [fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    have hl : x 0 < y 0 ∨ x 1 < y 1 := by
      by_contra hall
      simp only [not_or, not_lt] at hall
      exact hne (funext fun l => by
        fin_cases l
        · exact le_antisymm hall.1 (hxy 0)
        · exact le_antisymm hall.2 (hxy 1))
    have h0 := hxy 0
    have h1 := hxy 1
    refine ⟨min_le_min (by linarith) (by linarith), ?_⟩
    exact not_le.2 <| lt_min (min_lt_of_left_lt (by rcases hl with hl | hl <;> linarith :
        3 * x 0 + x 1 < 3 * y 0 + y 1))
      (min_lt_of_right_lt (by rcases hl with hl | hl <;> linarith :
        x 0 + 3 * x 1 < y 0 + 3 * y 1))

/-- The utilities of Figure 15.B.14 are locally nonsatiated. -/
theorem fig14_lns (i : Fin 2) : UtilityLNS (fig14Economy.u i) := by
  fin_cases i
  · exact sqUtility_props.2.1.lns two_pos
  · exact fig14_u2_props.2.2.lns two_pos

/-- **Figure 15.B.14** (MWG, p. 525). The allocation `x* = ((1,1),(1,1))` is Pareto optimal, but it
is not supportable as an equilibrium with transfers: at every supporting budget line the
nonconvex consumer 1 prefers a corner bundle. All preferences are continuous and strongly
monotone and consumer 2's are convex; only the convexity of consumer 1's fails. -/
theorem fig_15_B_14 : fig14Economy.IsParetoOptimal fig14Economy.ω ∧
    ¬ fig14Economy.IsSupportable fig14Economy.ω := by
  have hω0 : fig14Economy.ω 0 = ![1, 1] := rfl
  have hω1 : fig14Economy.ω 1 = ![1, 1] := rfl
  have hu0 : fig14Economy.u 0 = sqUtility := rfl
  have hbox : fig14Economy.InBox fig14Economy.ω :=
    ⟨fun i l => by fin_cases i <;> fin_cases l <;> simp [fig14Economy,
      ExchangeEconomy.ofOrthant], rfl⟩
  refine ⟨⟨hbox, ?_⟩, ?_⟩
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs0 := congrFun hx'.2 0
    have hs1 := congrFun hx'.2 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment, hω0, hω1,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hm : ∀ j l, 0 ≤ x' j l := fun j l => hx'.1 j l
    have h1 := hle 1
    have h0 := hle 0
    simp only [fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      Matrix.cons_val_one, sqUtility, le_min_iff] at h0 h1
    norm_num at h0 h1
    set a := x' 0 0
    set b := x' 0 1
    have ha := hm 0 0
    have hb := hm 0 1
    have c1 : 3 * a + b ≤ 4 := by nlinarith [h1.1]
    have c2 : a + 3 * b ≤ 4 := by nlinarith [h1.2]
    have hu : (a + b - 2) ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - 3 * a - b) ha,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - a - 3 * b) hb]
    have hab : a + b = 2 := by nlinarith [sq_nonneg (a + b - 2)]
    have hd : (a - b) ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - 3 * a - b) ha,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - a - 3 * b) hb]
    have hab' : a = b := by nlinarith [sq_nonneg (a - b)]
    have e0 : a = 1 := by linarith
    have e1 : b = 1 := by linarith
    have f0 : x' 1 0 = 1 := by linarith
    have f1 : x' 1 1 = 1 := by linarith
    fin_cases i
    · simp only [Fin.zero_eta, fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        sqUtility] at hi
      rw [show x' 0 0 = a from rfl, show x' 0 1 = b from rfl, e0, e1] at hi
      norm_num at hi
    · simp only [Fin.mk_one, fig14Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hi
      rw [f0, f1] at hi
      norm_num at hi
  · rintro ⟨p, T, h⟩
    have hT : T 0 = 0 := by
      have := h.wealth_eq (fun _ => rfl) fig14_lns 0
      linarith
    have hopt : ∀ y ∈ nonnegOrthant 2, p 0 * y 0 + p 1 * y 1 ≤ p 0 + p 1 → sqUtility y ≤ 2 := by
      intro y hy hb
      have := h.2.2 0 y hy (by
        rw [hT, add_zero, hω0]
        simpa [dotProduct, Fin.sum_univ_two] using hb)
      rw [hu0, hω0] at this
      simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      norm_num at this
      simpa [sqUtility] using this
    by_cases hp0 : p 0 ≤ 0
    · have := hopt ![2, 1] (fun l => by fin_cases l <;> norm_num) (by simp; linarith)
      norm_num [sqUtility] at this
    by_cases hp1 : p 1 ≤ 0
    · have := hopt ![1, 2] (fun l => by fin_cases l <;> norm_num) (by simp; linarith)
      norm_num [sqUtility] at this
    rw [not_le] at hp0 hp1
    rcases le_total (p 0) (p 1) with hle | hle
    · have hk : 2 ≤ (p 0 + p 1) / p 0 := by rw [le_div_iff₀ hp0]; linarith
      have := hopt ![(p 0 + p 1) / p 0, 0]
        (fun l => by
          fin_cases l <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> positivity)
        (by simp [mul_div_cancel₀ _ hp0.ne'])
      simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      nlinarith
    · have hk : 2 ≤ (p 0 + p 1) / p 1 := by rw [le_div_iff₀ hp1]; linarith
      have := hopt ![0, (p 0 + p 1) / p 1]
        (fun l => by
          fin_cases l <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> positivity)
        (by simp [mul_div_cancel₀ _ hp1.ne'])
      simp only [sqUtility, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      nlinarith

/-! ### Exercise 15.B.9 -/

/-- Alphanse's utility `min(x_P, x_B)` (goods: Perrier, Brie). -/
def alphanseU (x : Fin 2 → ℝ) : ℝ := min (x 0) (x 1)

/-- Betatrix's utility `min(x_B, √x_P)`. -/
noncomputable def betatrixU (x : Fin 2 → ℝ) : ℝ := min (x 1) (Real.sqrt (x 0))

/-- **Exercise 15.B.9** (MWG, p. 541). Alphanse owns `e` units of Perrier, Betatrix 20 units of
Brie. -/
noncomputable def ex15B9Economy (e : ℝ) : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![alphanseU, betatrixU] ![![e, 0], ![0, 20]]

/-- Alphanse's demand at `p ≫ 0` and wealth `w ≥ 0`: the single bundle `(k, k)`,
`k = w/(p_P + p_B)`. -/
theorem alphanse_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand alphanseU p w = {![w / (p 0 + p 1), w / (p 0 + p 1)]} := by
  have hp0 := hp 0
  have hp1 := hp 1
  set k := w / (p 0 + p 1) with hk
  have hk0 : 0 ≤ k := div_nonneg hw (by linarith)
  have hkw : (p 0 + p 1) * k = w := by rw [hk]; field_simp
  have hmem : (![k, k] : Fin 2 → ℝ) ∈ budgetSet p w :=
    ⟨fun l => by fin_cases l <;> simpa, by simp [dotProduct, Fin.sum_univ_two]; linarith⟩
  have hbound : ∀ y ∈ budgetSet p w, alphanseU y ≤ k := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hy.2
    by_contra hlt
    rw [not_le, alphanseU, lt_min_iff] at hlt
    nlinarith
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    have h1 := hy.2 _ hmem
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hy.1.2
    simp only [alphanseU, Matrix.cons_val_zero, Matrix.cons_val_one, min_self, le_min_iff] at h1
    have e0 : y 0 = k := by nlinarith
    have e1 : y 1 = k := by nlinarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    have hval : alphanseU ![k, k] = k := by simp [alphanseU]
    exact ⟨hmem, fun z hz => by rw [hval]; exact hbound z hz⟩

/-- Betatrix's demand at `p ≫ 0` and wealth `w`, where `s ≥ 0` solves `p_P s² + p_B s = w`: the
single bundle `(s², s)`. -/
theorem betatrix_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w s : ℝ} (hs : 0 ≤ s)
    (hsw : p 0 * s ^ 2 + p 1 * s = w) : walrasianDemand betatrixU p w = {![s ^ 2, s]} := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hmem : (![s ^ 2, s] : Fin 2 → ℝ) ∈ budgetSet p w :=
    ⟨fun l => by fin_cases l <;> simp [hs], by
      simp [dotProduct, Fin.sum_univ_two]; linarith⟩
  have husx : betatrixU ![s ^ 2, s] = s := by
    simp [betatrixU, Real.sqrt_sq hs]
  -- every affordable bundle has `m = min(y_B, √y_P) ≤ s`
  have hbound : ∀ y ∈ budgetSet p w, betatrixU y ≤ s ∧ (betatrixU y = s → y = ![s ^ 2, s]) := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ w := by simpa [dotProduct, Fin.sum_univ_two] using hy.2
    have hy0 := hy.1 0
    have hy1 := hy.1 1
    set m := betatrixU y with hm
    have hm1 : m ≤ y 1 := min_le_left _ _
    have hm2 : m ≤ Real.sqrt (y 0) := min_le_right _ _
    have hm0 : 0 ≤ m := le_min hy1 (Real.sqrt_nonneg _)
    have hm2' : m ^ 2 ≤ y 0 := by
      calc m ^ 2 ≤ Real.sqrt (y 0) ^ 2 := pow_le_pow_left₀ hm0 hm2 2
        _ = y 0 := Real.sq_sqrt hy0
    have hcost : p 0 * m ^ 2 + p 1 * m ≤ p 0 * s ^ 2 + p 1 * s := by nlinarith
    have hms : m ≤ s := by
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos hp0 (mul_pos (by linarith : (0 : ℝ) < m - s) (by linarith : 0 < m + s))]
    refine ⟨hms, fun heq => ?_⟩
    rw [heq] at hm1 hm2'
    have e1 : y 1 = s := by nlinarith
    have e0 : y 0 = s ^ 2 := by nlinarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    have h1 := hy.2 _ hmem
    rw [husx] at h1
    exact (hbound y hy.1).2 (le_antisymm (hbound y hy.1).1 h1)
  · rintro rfl
    exact ⟨hmem, fun z hz => by rw [husx]; exact (hbound z hz).1⟩

/-- Alphanse's and Betatrix's preferences are locally nonsatiated. -/
theorem ex15B9_lns (e : ℝ) (i : Fin 2) : UtilityLNS ((ex15B9Economy e).u i) := by
  fin_cases i
  · exact exercise_3_B_1b_orthant two_pos fun x _ y _ hxy => ⟨by
      simp only [utilityPref]
      exact min_le_min (hxy 0).le (hxy 1).le, by
      simp only [utilityPref, not_le]
      exact lt_min (min_lt_of_left_lt (hxy 0)) (min_lt_of_right_lt (hxy 1))⟩
  · exact exercise_3_B_1b_orthant two_pos fun x hx y _ hxy => ⟨by
      simp only [utilityPref]
      exact min_le_min (hxy 1).le (Real.sqrt_le_sqrt (hxy 0).le), by
      simp only [utilityPref, not_le]
      exact lt_min (min_lt_of_left_lt (hxy 1))
        (min_lt_of_right_lt (Real.sqrt_lt_sqrt (hx 0) (hxy 0)))⟩

/-- In the Alphanse-Betatrix economy with `e ≤ 30` units of Perrier, equilibrium prices of
Perrier are positive: otherwise Betatrix affords `(401, 20)`, worth `20 > √30`. -/
theorem ex15B9_p0_pos {e : ℝ} (he : e ≤ 30) {p : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : (ex15B9Economy e).IsDemandEqm p x) : 0 < p 0 := by
  by_contra hp0
  rw [not_lt] at hp0
  obtain ⟨hbox, hd⟩ := h
  have hs0 := congrFun hbox.2 0
  simp only [Finset.sum_apply, Fin.sum_univ_two, ExchangeEconomy.totalEndowment,
    ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero, Matrix.cons_val_one] at hs0
  have hxa := (hd 0).1.1 0
  have hmem : (![401, 20] : Fin 2 → ℝ) ∈ budgetSetOn ((ex15B9Economy e).X 1) p
      (p ⬝ᵥ (ex15B9Economy e).ω 1) :=
    ⟨fun l => by fin_cases l <;> norm_num, by
      simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
      nlinarith⟩
  have h1 := (hd 1).2 _ hmem
  have hsq : Real.sqrt 401 ≥ 20 := by
    rw [ge_iff_le, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hval : (ex15B9Economy e).u 1 ![401, 20] = 20 := by
    simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_one,
      Matrix.cons_val_zero, betatrixU]
    exact min_eq_left hsq
  rw [hval] at h1
  have hle : (ex15B9Economy e).u 1 (x 1) ≤ Real.sqrt (x 1 0) := min_le_right _ _
  have h30 : Real.sqrt (x 1 0) ≤ Real.sqrt 30 := Real.sqrt_le_sqrt (by linarith)
  have : Real.sqrt 30 < 20 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- A nonnegative root of `a r² + b r = w` for `a > 0`, `b, w ≥ 0`. -/
theorem quad_root_nonneg {a b w : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hw : 0 ≤ w) :
    ∃ r, 0 ≤ r ∧ a * r ^ 2 + b * r = w := by
  set D := b ^ 2 + 4 * a * w with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨(-b + Real.sqrt D) / (2 * a), ?_, ?_⟩
  · apply div_nonneg _ (by linarith)
    have : b ≤ Real.sqrt D := by
      rw [Real.le_sqrt hb hD0]
      nlinarith
    linarith
  · have hsD := Real.sq_sqrt hD0
    field_simp
    nlinarith [hsD]

/-- **Exercise 15.B.9** (MWG, p. 541). With 30 units of Perrier for Alphanse the equilibrium is
unique: with `a = (39 - √41)/2 ≈ 16.3`, `p_P/(p_P + p_B) = a/30`, Alphanse consumes `(a, a)` and
Betatrix `(30 - a, 20 - a)` (where `20 - a = √(30 - a) = (1 + √41)/2`). -/
theorem exercise_15_B_9 (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (ex15B9Economy 30).IsDemandEqm p x ↔ StrictlyPositive p ∧
      30 * p 0 = (39 - Real.sqrt 41) / 2 * (p 0 + p 1) ∧
      x = ![![(39 - Real.sqrt 41) / 2, (39 - Real.sqrt 41) / 2],
        ![30 - (39 - Real.sqrt 41) / 2, 20 - (39 - Real.sqrt 41) / 2]] := by
  set a := (39 - Real.sqrt 41) / 2 with ha
  have h41 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have h41b : 6 < Real.sqrt 41 ∧ Real.sqrt 41 < 7 := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; norm_num
    · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set s := (1 + Real.sqrt 41) / 2 with hsd
  have hs0 : 0 ≤ s := by rw [hsd]; linarith [h41b.1]
  have hsq : s ^ 2 = s + 10 := by rw [hsd]; nlinarith [h41]
  have has : a = 20 - s := by rw [ha, hsd]; ring
  have hu0 : (ex15B9Economy 30).demand 0 p = walrasianDemand alphanseU p (30 * p 0) := by
    unfold ExchangeEconomy.demand
    congr 1
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have hu1 : (ex15B9Economy 30).demand 1 p = walrasianDemand betatrixU p (20 * p 1) := by
    unfold ExchangeEconomy.demand
    congr 1
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have htot : (ex15B9Economy 30).totalEndowment = ![30, 20] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, ex15B9Economy,
      ExchangeEconomy.ofOrthant]
  constructor
  · intro h
    have hp0 := ex15B9_p0_pos (by norm_num) h
    obtain ⟨hbox, hd⟩ := h
    have hs1 := congrFun hbox.2 1
    rw [htot, Finset.sum_apply, Fin.sum_univ_two] at hs1
    have hs0' := congrFun hbox.2 0
    rw [htot, Finset.sum_apply, Fin.sum_univ_two] at hs0'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs0'
    have hp1 : 0 < p 1 := by
      by_contra hp1
      rw [not_lt] at hp1
      have h1 := (hd 0).2 ![30, 30] ⟨fun l => by fin_cases l <;> norm_num, by
        simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
        nlinarith⟩
      have hb1 := (hd 1).1.1 1
      have : (ex15B9Economy 30).u 0 (x 0) ≤ x 0 1 := min_le_right _ _
      simp [ex15B9Economy, ExchangeEconomy.ofOrthant, alphanseU] at h1 this
      linarith
    have hp : StrictlyPositive p := fun l => by fin_cases l; exacts [hp0, hp1]
    have hd0 := hd 0
    rw [hu0, alphanse_demand hp (by linarith), Set.mem_singleton_iff] at hd0
    -- Betatrix's demand: solve for `t = x_B,B`
    have hd1 := hd 1
    rw [hu1] at hd1
    have ht0 := hd1.1.1 1
    obtain ⟨t, ht, hteq⟩ : ∃ t, 0 ≤ t ∧ x 1 = ![t ^ 2, t] := by
      refine ⟨x 1 1, ht0, ?_⟩
      have hopt := hd1
      -- the optimal bundle is `(t², t)` for the root `t` of `p_P t² + p_B t = 20 p_B`
      obtain ⟨r, hr, hreq⟩ := quad_root_nonneg hp0 hp1.le (by linarith : (0 : ℝ) ≤ 20 * p 1)
      rw [betatrix_demand hp hr hreq, Set.mem_singleton_iff] at hopt
      rw [hopt]
      simp
    rw [hd0, hteq] at hs1 hs0'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs0'
    -- `k + t = 20`, `k + t² = 30`
    have htq : t ^ 2 - t - 10 = 0 := by linarith
    have hts : t = s := by
      have : (t - s) * (t - (1 - Real.sqrt 41) / 2) = 0 := by
        rw [hsd]; nlinarith [h41]
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · have : t = (1 - Real.sqrt 41) / 2 := by linarith
        linarith [h41b.1]
    have hk : 30 * p 0 / (p 0 + p 1) = a := by rw [has]; linarith
    refine ⟨hp, ?_, ?_⟩
    · rw [← hk]
      field_simp
    · funext i l
      fin_cases i <;> fin_cases l <;> simp [hd0, hteq, hts] <;> linarith [hk, has, hsq]
  · rintro ⟨hp, hrel, rfl⟩
    have hp0 := hp 0
    have hp1 := hp 1
    have hk : 30 * p 0 / (p 0 + p 1) = a := by
      rw [div_eq_iff (by linarith)]
      linarith
    have hreq : p 0 * s ^ 2 + p 1 * s = 20 * p 1 := by
      rw [hsq]
      have : s = 20 - a := by linarith
      rw [this]
      nlinarith
    refine ⟨⟨fun i l => ?_, ?_⟩, fun i => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp <;> nlinarith [h41b.1, h41b.2]
    · rw [htot]
      funext l
      fin_cases l <;> simp [Fin.sum_univ_two]
    · fin_cases i
      · change ![a, a] ∈ (ex15B9Economy 30).demand 0 p
        rw [hu0, alphanse_demand hp (by linarith), hk]
        rfl
      · change ![30 - a, 20 - a] ∈ (ex15B9Economy 30).demand 1 p
        rw [hu1, betatrix_demand hp hs0 hreq, Set.mem_singleton_iff]
        funext l
        fin_cases l
        · simp [hsq, has]; ring
        · simp [has]

/-- **Exercise 15.B.9** (MWG, p. 542), second part. If Alphanse owns only 5 units of Perrier, Brie
becomes a free good: the equilibria are exactly `p_B = 0 < p_P` with Alphanse consuming `(5, b)`
and Betatrix `(0, 20 - b)` for any `b ∈ [5, 20]` (Betatrix gets utility 0). -/
theorem exercise_15_B_9_second (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    (ex15B9Economy 5).IsDemandEqm p x ↔ p 1 = 0 ∧ 0 < p 0 ∧
      ∃ b, 5 ≤ b ∧ b ≤ 20 ∧ x = ![![5, b], ![0, 20 - b]] := by
  have htot : (ex15B9Economy 5).totalEndowment = ![5, 20] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, ex15B9Economy,
      ExchangeEconomy.ofOrthant]
  have hw0 : p ⬝ᵥ (ex15B9Economy 5).ω 0 = 5 * p 0 := by
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have hw1 : p ⬝ᵥ (ex15B9Economy 5).ω 1 = 20 * p 1 := by
    simp [ex15B9Economy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two, mul_comm]
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have hp0 := ex15B9_p0_pos (by norm_num) h
    obtain ⟨hbox, hd⟩ := h
    have hs0 := congrFun hbox.2 0
    have hs1 := congrFun hbox.2 1
    rw [htot, Finset.sum_apply, Fin.sum_univ_two] at hs0 hs1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
    have hA := hd 0
    have hB := hd 1
    have hxA0 := hA.1.1 0
    have hxA1 := hA.1.1 1
    have hxB0 := hB.1.1 0
    have hxB1 := hB.1.1 1
    have huA : (ex15B9Economy 5).u 0 (x 0) ≤ x 0 0 := min_le_left _ _
    -- the price of Brie is not negative: otherwise Alphanse affords `(6, M)`
    have hp1n : 0 ≤ p 1 := by
      by_contra hp1
      rw [not_le] at hp1
      set M := 6 + p 0 / (-p 1) with hM
      have hM0 : 6 ≤ M := by rw [hM]; have : 0 < p 0 / (-p 1) := div_pos hp0 (by linarith); linarith
      have hcost : p 0 * 6 + p 1 * M ≤ 5 * p 0 := by
        have hne : p 1 ≠ 0 := hp1.ne
        have : p 1 * M = 6 * p 1 - p 0 := by rw [hM]; field_simp; ring
        rw [this]
        linarith
      have h1 := hA.2 ![6, M] ⟨fun l => by
          fin_cases l
          · norm_num
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            linarith, by
        rw [hw0, hdot]; simpa using hcost⟩
      simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        alphanseU, Matrix.cons_val_one] at h1 huA
      rw [min_eq_left hM0] at h1
      linarith
    -- and not positive: otherwise `k + t = 20`, `k + t² = 5` is impossible
    have hp1 : p 1 = 0 := by
      by_contra hne
      have hp1 : 0 < p 1 := lt_of_le_of_ne hp1n (Ne.symm hne)
      have hp : StrictlyPositive p := fun l => by fin_cases l; exacts [hp0, hp1]
      obtain ⟨r, hr, hreq⟩ := quad_root_nonneg hp0 hp1.le (by linarith : (0 : ℝ) ≤ 20 * p 1)
      have hd1 := hB
      have hu1 : (ex15B9Economy 5).demand 1 p = walrasianDemand betatrixU p (20 * p 1) := by
        unfold ExchangeEconomy.demand
        rw [hw1]
        rfl
      rw [hu1, betatrix_demand hp hr hreq, Set.mem_singleton_iff] at hd1
      have e10 : x 1 0 = r ^ 2 := by rw [hd1]; rfl
      have e11 : x 1 1 = r := by rw [hd1]; rfl
      rw [e10] at hs0
      rw [e11] at hs1
      have hd0 := hA
      have hu0 : (ex15B9Economy 5).demand 0 p = walrasianDemand alphanseU p (5 * p 0) := by
        unfold ExchangeEconomy.demand
        rw [hw0]
        rfl
      rw [hu0, alphanse_demand hp (by linarith), Set.mem_singleton_iff] at hd0
      have e00 : x 0 0 = x 0 1 := by rw [hd0]; rfl
      nlinarith [sq_nonneg (r - 1 / 2)]
    refine ⟨hp1, hp0, x 0 1, ?_, ?_, ?_⟩
    · -- Alphanse can afford `(5, 20)`
      have h1 := hA.2 ![5, 20] ⟨fun l => by fin_cases l <;> norm_num, by
        rw [hw0, hdot, hp1]; simp [mul_comm]⟩
      simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        alphanseU, Matrix.cons_val_one] at h1
      norm_num at h1
      exact h1.2
    · linarith
    · have hb := hA.1.2
      rw [hw0, hdot, hp1] at hb
      have hA0 : x 0 0 ≤ 5 := by nlinarith
      have h1 := hA.2 ![5, 20] ⟨fun l => by fin_cases l <;> norm_num, by
        rw [hw0, hdot, hp1]; simp [mul_comm]⟩
      simp only [ex15B9Economy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
        alphanseU, Matrix.cons_val_one] at h1
      norm_num at h1
      have e00 : x 0 0 = 5 := le_antisymm hA0 h1.1
      have e10 : x 1 0 = 0 := by linarith
      have e11 : x 1 1 = 20 - x 0 1 := by linarith
      funext i l
      fin_cases i <;> fin_cases l <;> simp [e00, e10, e11]
  · rintro ⟨hp1, hp0, b, hb5, hb20, rfl⟩
    refine ⟨⟨fun i l => ?_, ?_⟩, fun i => ?_⟩
    · fin_cases i <;> fin_cases l <;> simp <;> linarith
    · rw [htot]
      funext l
      fin_cases l <;> simp [Fin.sum_univ_two]
    · fin_cases i
      · change ![5, b] ∈ (ex15B9Economy 5).demand 0 p
        refine ⟨⟨fun l => by
          fin_cases l
          · norm_num
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            linarith, by
          rw [hw0, hdot, hp1]; simp [mul_comm]⟩, fun y hy => ?_⟩
        have hb := hy.2
        rw [hw0, hdot, hp1] at hb
        have hy0 : y 0 ≤ 5 := by nlinarith
        change min (y 0) (y 1) ≤ min 5 b
        rw [min_eq_left hb5]
        exact (min_le_left _ _).trans hy0
      · change ![0, 20 - b] ∈ (ex15B9Economy 5).demand 1 p
        refine ⟨⟨fun l => by
          fin_cases l
          · norm_num
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            linarith, by
          rw [hw1, hdot, hp1]; simp⟩, fun y hy => ?_⟩
        have hb := hy.2
        rw [hw1, hdot, hp1] at hb
        have hy0 : y 0 = 0 := by nlinarith [hy.1 0]
        change min (y 1) (Real.sqrt (y 0)) ≤ min (20 - b) (Real.sqrt 0)
        rw [hy0, Real.sqrt_zero, min_eq_right (hy.1 1),
          min_eq_right (by linarith : (0 : ℝ) ≤ 20 - b)]

end MWG.GeneralEquilibriumExamples
