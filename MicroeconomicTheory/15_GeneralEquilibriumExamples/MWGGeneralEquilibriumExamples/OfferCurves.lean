/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.MultipleEquilibria
import MWGGeneralEquilibriumExamples.Welfare
import MWGGeneralEquilibriumExamples.CobbDouglasBox

/-!
# Offer curves (MWG Section 15.B, pp. 517-518, and Exercise 15.B.4, p. 541)

* p. 517-518: if preferences are convex and represented by a continuous utility that is
  differentiable at `ωᵢ ≫ 0` with `∇u(ωᵢ) ≫ 0`, the endowment is demanded at the prices
  `p = ∇u(ωᵢ)`: the offer curve passes through the endowment point, where the budget line is
  tangent to the indifference curve (`endowment_mem_offerCurve`).
* **Exercise 15.B.4**. An offer curve is described by the demand `d(q)` at prices `(q, 1)`,
  `q = p₁/p₂` (demand is homogeneous of degree zero). (b) If both offer curves have the gross
  substitute property there is at most one equilibrium price ratio (`exercise_15_B_4b`), so in an
  Edgeworth box with single-valued demands the offer curves intersect at most once besides the
  endowment (`exercise_15_B_4b_offerCurves`). (e) The same holds if one offer curve is normal and
  the other has the gross substitute property (`exercise_15_B_4e`). (f) Two normal offer curves can
  intersect several times: the offer curves of Example 15.B.2 are normal
  (`exercise_15_B_4f`). (d) A strictly non-normal offer curve requires an inferior good, by the
  Slutsky decomposition along the offer curve (`exercise_15_B_4d`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

/-- **Section 15.B** (MWG, pp. 517-518). Let `u` be continuous on `ℝ^L₊`, represent convex
preferences, and be differentiable at `ω ≫ 0` with gradient `g = ∇u(ω) ≫ 0`. Then `ω` is demanded
at prices `g` (with wealth `g·ω`): the offer curve passes through the endowment, with the budget
line tangent to the indifference curve there. -/
theorem endowment_mem_offerCurve {L : ℕ} {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hconv : PrefConvex (nonnegOrthant L) (utilityPref u))
    {ω : Fin L → ℝ} (hω : StrictlyPositive ω) {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hd : HasFDerivAt u u' ω) (hg : StrictlyPositive fun l => u' (Pi.single l 1)) :
    ω ∈ walrasianDemand u (fun l => u' (Pi.single l 1)) ((fun l => u' (Pi.single l 1)) ⬝ᵥ ω) := by
  set g : Fin L → ℝ := fun l => u' (Pi.single l 1) with hgd
  have hωm : ω ∈ nonnegOrthant L := fun l => (hω l).le
  have hlin : ∀ v, u' v = g ⬝ᵥ v := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ u'.toLinearMap v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    have he : (fun j => if l = j then (1 : ℝ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [he, hgd, mul_comm]
  refine ⟨⟨hωm, le_rfl⟩, fun y hy => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  -- a strictly better bundle strictly inside the budget set
  obtain ⟨y', hy'm, hy'c, hy'u⟩ : ∃ y' ∈ nonnegOrthant L, g ⬝ᵥ y' < g ⬝ᵥ ω ∧ u ω < u y' := by
    by_cases hin : g ⬝ᵥ y < g ⬝ᵥ ω
    · exact ⟨y, hy.1, hin, hlt⟩
    · have heq : g ⬝ᵥ y = g ⬝ᵥ ω := le_antisymm hy.2 (not_lt.1 hin)
      have hpos : 0 < g ⬝ᵥ ω := by
        by_cases hL : Nonempty (Fin L)
        · obtain ⟨l⟩ := hL
          exact dotProduct_pos_of_strictlyPositive hg hωm (fun h => by
            have := congrFun h l; simp at this; linarith [hω l])
        · exfalso
          rw [not_nonempty_iff] at hL
          have : y = ω := funext fun l => isEmptyElim l
          rw [this] at hlt
          exact lt_irrefl _ hlt
      set γ : ℝ → Fin L → ℝ := fun t => (1 - t / 2) • y
      have hγc : Continuous γ := by fun_prop
      have hγm : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ nonnegOrthant L := by
        intro t ht l
        simp only [γ, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith [ht.2]) (hy.1 l)
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt hc hγc hγm (by simpa [γ] using hlt)
      refine ⟨γ t, hγm t ⟨ht0.le, ht1⟩, ?_, ht⟩
      simp only [γ, dotProduct_smul, smul_eq_mul, heq]
      nlinarith
  -- along the segment from `ω` towards `y'` utility first falls (the derivative is negative)
  set h : ℝ → ℝ := fun t => u (ω + t • (y' - ω)) with hh
  have hline : HasDerivAt (fun t : ℝ => ω + t • (y' - ω)) (y' - ω) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y' - ω)).const_add ω
  have hhd : HasDerivAt h (u' (y' - ω)) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using hd) hline
    simpa [Function.comp_def, hh] using this
  have hneg : u' (y' - ω) < 0 := by
    rw [hlin, dotProduct_sub]
    linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 1 :=
    (nhdsWithin_le_nhds (Iic_mem_nhds one_pos))
  obtain ⟨t, ht0, ht1, hlow⟩ := exists_pos_deriv_neg hhd hneg hev
  -- but quasiconcavity keeps utility at least `u(ω)` on the segment
  have hq := quasiconcave_of_prefConvex hconv hωm hy'm (a := 1 - t) (b := t) (by linarith)
    ht0.le (by ring)
  rw [min_eq_left hy'u.le] at hq
  have e : (1 - t) • ω + t • y' = ω + t • (y' - ω) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [e] at hq
  simp only [hh, zero_smul, add_zero] at hlow
  linarith

/-! ### Exercise 15.B.4 -/

/-- **Exercise 15.B.4** (MWG, p. 541). An offer curve, given by demands `d(q)` at prices `(q, 1)`,
has the gross substitute property if raising the relative price of good 1 lowers the demand for
good 1 and raises the demand for good 2. -/
def GrossSubstitute (d : ℝ → Fin 2 → ℝ) : Prop :=
  ∀ q q', 0 < q → q < q' → d q' 0 < d q 0 ∧ d q 1 < d q' 1

/-- **Exercise 15.B.4** (MWG, p. 541). An offer curve is normal if an increase in the relative price
of a commodity raises the demand for that commodity only if the demands for both commodities
rise. -/
def NormalOfferCurve (d : ℝ → Fin 2 → ℝ) : Prop :=
  (∀ q q', 0 < q → q < q' → d q 0 < d q' 0 → d q 1 < d q' 1) ∧
    ∀ q q', 0 < q' → q' < q → d q 1 < d q' 1 → d q 0 < d q' 0

/-- **Exercise 15.B.4(b)** (MWG, p. 541). If both offer curves have the gross substitute property,
the market for good 1 clears at most at one relative price. -/
theorem exercise_15_B_4b {d₁ d₂ : ℝ → Fin 2 → ℝ} (h₁ : GrossSubstitute d₁)
    (h₂ : GrossSubstitute d₂) {ω₁ q q' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    (hc : d₁ q 0 + d₂ q 0 = ω₁) (hc' : d₁ q' 0 + d₂ q' 0 = ω₁) : q = q' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · linarith [(h₁ q q' hq hlt).1, (h₂ q q' hq hlt).1]
  · linarith [(h₁ q' q hq' hlt).1, (h₂ q' q hq' hlt).1]

/-- **Exercise 15.B.4(b)** (MWG, p. 541), for offer curves. In an Edgeworth box with locally
nonsatiated consumers whose demands at prices `(q, 1)` are the single bundles `dᵢ(q)`, if both
offer curves have the gross substitute property then any two intersections of the offer curves
other than the endowment point coincide. -/
theorem exercise_15_B_4b_offerCurves {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    (hlns : ∀ i, UtilityLNS (E.u i)) {d : Fin 2 → ℝ → Fin 2 → ℝ}
    (hd : ∀ i q, 0 < q → E.demand i ![q, 1] = {d i q}) (hgs : ∀ i, GrossSubstitute (d i))
    {x x' : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) (hx' : E.InBox x') (hne : x 0 ≠ E.ω 0)
    (hne' : x' 0 ≠ E.ω 0) (h0 : x 0 ∈ E.offerCurve 0) (h1 : x 1 ∈ E.offerCurve 1)
    (h0' : x' 0 ∈ E.offerCurve 0) (h1' : x' 1 ∈ E.offerCurve 1) : x = x' := by
  -- each intersection is an equilibrium; normalize its prices to `(q, 1)`
  have key : ∀ y : Fin 2 → Fin 2 → ℝ, E.InBox y → y 0 ≠ E.ω 0 → y 0 ∈ E.offerCurve 0 →
      y 1 ∈ E.offerCurve 1 → ∃ q, 0 < q ∧ y = fun i => d i q := by
    intro y hy hyne hy0 hy1
    obtain ⟨p, hp, heq⟩ := isDemandEqm_of_offerCurves hX hlns hy hyne hy0 hy1
    have hp1 := hp 1
    refine ⟨p 0 / p 1, div_pos (hp 0) hp1, funext fun i => ?_⟩
    have hs : (p 1)⁻¹ • p = ![p 0 / p 1, 1] := by
      funext l
      fin_cases l
      · simp [div_eq_inv_mul]
      · simp [inv_mul_cancel₀ hp1.ne']
    have := heq.2 i
    rw [← E.demand_smul i p (inv_pos.2 hp1), hs, hd i _ (div_pos (hp 0) hp1)] at this
    exact this
  obtain ⟨q, hq, rfl⟩ := key x hx hne h0 h1
  obtain ⟨q', hq', rfl⟩ := key x' hx' hne' h0' h1'
  have hc := congrFun hx.2 0
  have hc' := congrFun hx'.2 0
  simp only [Finset.sum_apply, Fin.sum_univ_two] at hc hc'
  rw [exercise_15_B_4b (hgs 0) (hgs 1) hq hq' hc (hc'.trans hc.symm |>.symm ▸ hc')]

/-- **Exercise 15.B.4(e)** (MWG, p. 541). If one offer curve is normal and the other has the gross
substitute property, both markets clear at most at one relative price. -/
theorem exercise_15_B_4e {d₁ d₂ : ℝ → Fin 2 → ℝ} (h₁ : GrossSubstitute d₁)
    (h₂ : NormalOfferCurve d₂) {ω : Fin 2 → ℝ} {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q')
    (hc : ∀ l, d₁ q l + d₂ q l = ω l) (hc' : ∀ l, d₁ q' l + d₂ q' l = ω l) : q = q' := by
  by_contra hne
  -- order the two prices
  wlog hlt : q < q' generalizing q q'
  · exact this hq' hq hc' hc (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  obtain ⟨g0, g1⟩ := h₁ q q' hq hlt
  -- good 1: consumer 1 buys less, so consumer 2 buys more; normality then forces more good 2
  have hd20 : d₂ q 0 < d₂ q' 0 := by linarith [hc 0, hc' 0]
  have hd21 := h₂.1 q q' hq hlt hd20
  linarith [hc 1, hc' 1]

/-- **Exercise 15.B.4(d)** (MWG, p. 541). Along an offer curve, with endowment `ω₁` of good 1 and
demand `x`, raising `p₁` changes demands by `dx_ℓ = s_{ℓ1} + (ω₁ - x₁) ∂x_ℓ/∂w` (Slutsky), where
`s₁₁ ≤ 0 ≤ s₂₁` (negative semidefiniteness, Chapter 3). If the offer curve is (strictly) not
normal there, `dx₁ > 0 > dx₂`, then one good is inferior: `∂x₁/∂w < 0` or `∂x₂/∂w < 0`. -/
theorem exercise_15_B_4d {s₁₁ s₂₁ b₁ b₂ ω₁ x₁ : ℝ} (hs₁₁ : s₁₁ ≤ 0) (hs₂₁ : 0 ≤ s₂₁)
    (hdx₁ : 0 < s₁₁ + (ω₁ - x₁) * b₁) (hdx₂ : s₂₁ + (ω₁ - x₁) * b₂ < 0) : b₁ < 0 ∨ b₂ < 0 := by
  rcases lt_trichotomy (ω₁ - x₁) 0 with h | h | h
  · left
    by_contra hb
    rw [not_lt] at hb
    nlinarith
  · rw [h] at hdx₁; linarith
  · right
    by_contra hb
    rw [not_lt] at hb
    nlinarith

/-- The offer curves of Example 15.B.2 as functions of `q = p₁/p₂`, with `t = q^{1/9}`. -/
noncomputable def ex15B2d (i : Fin 2) (q : ℝ) : Fin 2 → ℝ :=
  ![ex15B2OC1 (q ^ ((1 : ℝ) / 9)), ex15B2OC2 (q ^ ((1 : ℝ) / 9))] i

/-- **Exercise 15.B.4(f)** (MWG, p. 541). Two normal offer curves can intersect several times: the
offer curves of Example 15.B.2 are normal (consumer 1's demand for good 2, `q^{1/9}`, rises with
`q`; consumer 2's demand for good 1, `q^{-1/9}`, falls), and they intersect at the three
equilibria `p₁/p₂ ∈ {1/2, 1, 2}` (`example_15_B_2`). -/
theorem exercise_15_B_4f : NormalOfferCurve (ex15B2d 0) ∧ NormalOfferCurve (ex15B2d 1) := by
  have hmono : ∀ q q' : ℝ, 0 < q → q < q' → q ^ ((1 : ℝ) / 9) < q' ^ ((1 : ℝ) / 9) :=
    fun q q' hq hlt => Real.rpow_lt_rpow hq.le hlt (by norm_num)
  refine ⟨⟨fun q q' hq hlt _ => ?_, fun q q' hq' hlt h => ?_⟩,
    ⟨fun q q' hq hlt h => ?_, fun q q' hq' hlt _ => ?_⟩⟩
  · simpa [ex15B2d, ex15B2OC1] using hmono q q' hq hlt
  · exfalso
    simp only [ex15B2d, ex15B2OC1, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    linarith [hmono q' q hq' hlt]
  · exfalso
    simp only [ex15B2d, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have h1 := hmono q q' hq hlt
    have h0 : 0 < q ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hq _
    have : 1 / q' ^ ((1 : ℝ) / 9) < 1 / q ^ ((1 : ℝ) / 9) := one_div_lt_one_div_of_lt h0 h1
    linarith
  · simp only [ex15B2d, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 := hmono q' q hq' hlt
    have h0 : 0 < q' ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hq' _
    exact one_div_lt_one_div_of_lt h0 h1

/-- An instance of `endowment_mem_offerCurve`: the linear utility `x₁ + x₂` (continuous, convex,
gradient `(1, 1) ≫ 0`) at `ω = (1, 1)`. -/
theorem endowment_mem_offerCurve_instance :
    ContinuousOn linearUtility (nonnegOrthant 2) ∧
      PrefConvex (nonnegOrthant 2) (utilityPref linearUtility) ∧
      ∃ u' : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt linearUtility u' ![1, 1] ∧
        StrictlyPositive fun l => u' (Pi.single l 1) := by
  refine ⟨by unfold linearUtility; fun_prop, fun x _ y hy z hz a b ha hb hab => ⟨?_, ?_⟩,
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2), ?_, ?_⟩
  · exact convex_nonnegOrthant 2 hy.1 hz.1 ha hb hab
  · have h1 := hy.2
    have h2 := hz.2
    simp only [utilityPref, linearUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have : linearUtility x = a * linearUtility x + b * linearUtility x := by
      rw [← add_mul, hab, one_mul]
    simp only [linearUtility] at this
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · have h := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (![1, 1] : Fin 2 → ℝ)).add
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (![1, 1] : Fin 2 → ℝ))
    exact h
  · intro l
    fin_cases l <;> simp

/-- The Cobb-Douglas offer curve at prices `(q, 1)` with endowment `ω ≫ 0`. -/
noncomputable def cdOffer (α : ℝ) (ω : Fin 2 → ℝ) (q : ℝ) : Fin 2 → ℝ :=
  cobbDouglasDemand α ![q, 1] (q * ω 0 + ω 1)

/-- Instances of the gross substitute property (Exercise 15.B.4): Cobb-Douglas offer curves with
`ω ≫ 0`, `α ∈ (0, 1)`. -/
theorem cdOffer_grossSubstitute {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ω : Fin 2 → ℝ}
    (hω : ∀ l, 0 < ω l) : GrossSubstitute (cdOffer α ω) := by
  intro q q' hq hlt
  have hq' : 0 < q' := by linarith
  have h1 : 0 < 1 - α := by linarith
  simp only [cdOffer, cobbDouglasDemand, Matrix.cons_val_zero, Matrix.cons_val_one, div_one]
  constructor
  · rw [div_lt_div_iff₀ hq' hq]
    nlinarith [mul_pos hα0 (hω 1), hω 0]
  · nlinarith [mul_pos h1 (hω 0)]

end MWG.GeneralEquilibriumExamples
