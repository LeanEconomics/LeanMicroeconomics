/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.TatonnementExistence

/-!
# Footnote 62 for `L = 3`: uniqueness without stability (MWG Section 17.H, p. 623)

Footnote 62: "uniqueness by itself does not imply stability, except for `L = 2`". The case
`L = 2` is `footnote_17_62_two_goods`. For `L = 3` we prove Scarf's (1960) counterexample.

* **The economy** (`scarfEconomy`): three consumers, consumption sets `ℝ³₊`, consumer `i` owns one
  unit of good `i` and has the Leontief utility `min(xᵢ, xᵢ₊₁)` (indices mod 3). At `p ≫ 0`
  consumer `i` demands exactly `pᵢ/(pᵢ + pᵢ₊₁)` units of goods `i` and `i + 1`
  (`scarf_demand_0`, `scarf_demand_1`, `scarf_demand_2`), so the aggregate excess demand is
  `scarfZ`, `zₗ(p) = pₗ₋₁/(pₗ₋₁ + pₗ) - pₗ₊₁/(pₗ + pₗ₊₁)` (`scarf_excessDemand`).
* `scarfZ` is continuous, homogeneous of degree zero, satisfies Walras' law and is bounded below
  (`scarfZ_props`), and its equilibrium price vectors are exactly the ray of `(1, 1, 1)`
  (`scarfZ_eqm_iff`): the equilibrium is unique.
* Along a tâtonnement trajectory (`c = (1, 1, 1)`) both `∑ₗ pₗ²` (Walras' law) and `p₁p₂p₃`
  (`∑ₗ zₗ(p)/pₗ = 0`, `scarfZ_dual`) are constant (`scarf_prod_const`). Trajectories exist from
  every `p(0) ≫ 0` (`scarf_tat_exists`: Picard-Lindelöf on the compact invariant set
  `{∑ pₗ² = N₀, p₁p₂p₃ = P₀}`, with `tex_picard` and `tex_glue`).
* **Counterexample** (`footnote_17_62_three_goods`): the trajectory from `p(0) = (1, 2, 2)` exists
  and converges to no equilibrium price vector: on the sphere `∑ pₗ² = 9` the only equilibrium is
  `√3(1, 1, 1)`, with product `3√3 ≠ 4`. More generally no trajectory starting off the ray
  converges to an equilibrium (`scarf_not_converge`).
* Departure: Leontief preferences are not strongly monotone, and `scarfZ` violates the boundary
  condition (v) of Proposition 17.B.2 (`scarfZ_not_boundary`): as `p₁ → 0` with `p₂ = p₃ = 1`,
  every `zₗ` stays below `1`. Footnote 62 states no hypotheses; the counterexample is an exchange
  economy with continuous, weakly monotone, convex preferences.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set Metric
open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open scoped NNReal

/-! ### The Scarf economy -/

/-- **Footnote 62** (MWG, p. 623; Scarf 1960). The utilities: consumer `i` has
`uᵢ(x) = min(xᵢ, xᵢ₊₁)` (indices mod 3). -/
noncomputable def scarfU : Fin 3 → (Fin 3 → ℝ) → ℝ :=
  ![fun x => min (x 0) (x 1), fun x => min (x 1) (x 2), fun x => min (x 2) (x 0)]

/-- **Footnote 62** (MWG, p. 623). The endowments: consumer `i` owns one unit of good `i`. -/
def scarfω : Fin 3 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

/-- **Footnote 62** (MWG, p. 623). Scarf's exchange economy, consumption sets `ℝ³₊`. -/
noncomputable def scarfEconomy : ExchangeEconomy (Fin 3) 3 :=
  ExchangeEconomy.ofOrthant scarfU scarfω

/-- **Footnote 62** (MWG, p. 623). The aggregate excess demand of Scarf's economy:
`zₗ(p) = pₗ₋₁/(pₗ₋₁ + pₗ) - pₗ₊₁/(pₗ + pₗ₊₁)`. -/
noncomputable def scarfZ (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![q 2 / (q 2 + q 0) - q 1 / (q 0 + q 1), q 0 / (q 0 + q 1) - q 2 / (q 1 + q 2),
    q 1 / (q 1 + q 2) - q 0 / (q 2 + q 0)]

/-- Demand in Scarf's economy, coordinatewise. -/
theorem scarf_demand_iff {i : Fin 3} {q x : Fin 3 → ℝ} :
    x ∈ scarfEconomy.demand i q ↔
      ((0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2) ∧ q 0 * x 0 + q 1 * x 1 + q 2 * x 2 ≤ q i) ∧
        ∀ y : Fin 3 → ℝ, (0 ≤ y 0 ∧ 0 ≤ y 1 ∧ 0 ≤ y 2) →
          q 0 * y 0 + q 1 * y 1 + q 2 * y 2 ≤ q i → scarfU i y ≤ scarfU i x := by
  have hm : ∀ z : Fin 3 → ℝ, z ∈ nonnegOrthant 3 ↔ (0 ≤ z 0 ∧ 0 ≤ z 1 ∧ 0 ≤ z 2) := fun z => by
    simp [nonnegOrthant, Fin.forall_fin_succ]
  have hd : ∀ z : Fin 3 → ℝ, q ⬝ᵥ z = q 0 * z 0 + q 1 * z 1 + q 2 * z 2 := fun z => by
    simp [dotProduct, Fin.sum_univ_three]
  have hw : q 0 * scarfω i 0 + q 1 * scarfω i 1 + q 2 * scarfω i 2 = q i := by
    fin_cases i <;> simp [scarfω]
  unfold ExchangeEconomy.demand walrasianDemandOn budgetSetOn
  simp only [scarfEconomy, ExchangeEconomy.ofOrthant, Set.mem_ofPred_eq, hm, hd, hw, and_imp]

/-- The Leontief step: with `a, b, k > 0`, the bundle `(t, t, 0)`, `t = a/(a + b)`, is the
unique maximizer of `min(x, y)` on `{x, y, w ≥ 0 : ax + by + kw ≤ a}`. -/
theorem scarf_leontief {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    (∀ x y w : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ w → a * x + b * y + k * w ≤ a →
      min x y ≤ a / (a + b)) ∧
    (∀ x y w : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ w → a * x + b * y + k * w ≤ a →
      a / (a + b) ≤ min x y → x = a / (a + b) ∧ y = a / (a + b) ∧ w = 0) := by
  have hab : 0 < a + b := add_pos ha hb
  have ht : a * (a / (a + b)) + b * (a / (a + b)) = a := by field_simp
  refine ⟨fun x y w hx hy hw hbud => ?_, fun x y w hx hy hw hbud hmin => ?_⟩
  · rw [min_le_iff]
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_left h.1 ha, mul_lt_mul_of_pos_left h.2 hb]
  · rw [le_min_iff] at hmin
    have h1 := mul_le_mul_of_nonneg_left hmin.1 ha.le
    have h2 := mul_le_mul_of_nonneg_left hmin.2 hb.le
    have h3 := mul_nonneg hk.le hw
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith

/-- **Footnote 62** (MWG, p. 623). At `p ≫ 0` consumer `1` demands exactly
`(p₁/(p₁ + p₂), p₁/(p₁ + p₂), 0)`. -/
theorem scarf_demand_0 {q : Fin 3 → ℝ} (hq : q ∈ posOrthant 3) (x : Fin 3 → ℝ) :
    x ∈ scarfEconomy.demand 0 q ↔
      x = ![q 0 / (q 0 + q 1), q 0 / (q 0 + q 1), 0] := by
  obtain ⟨h1, h2⟩ := scarf_leontief (hq 0) (hq 1) (hq 2)
  have ht0 : 0 ≤ q 0 / (q 0 + q 1) := div_nonneg (hq 0).le (add_pos (hq 0) (hq 1)).le
  rw [scarf_demand_iff]
  constructor
  · rintro ⟨⟨⟨hx0, hx1, hx2⟩, hb⟩, hmax⟩
    have hm := hmax ![q 0 / (q 0 + q 1), q 0 / (q 0 + q 1), 0] ⟨ht0, ht0, le_rfl⟩
      (by
        change q 0 * (q 0 / (q 0 + q 1)) + q 1 * (q 0 / (q 0 + q 1)) + q 2 * 0 ≤ q 0
        have key : q 0 * (q 0 / (q 0 + q 1)) + q 1 * (q 0 / (q 0 + q 1)) = q 0 := by
          field_simp [(add_pos (hq 0) (hq 1)).ne']
        linarith)
    change min (q 0 / (q 0 + q 1)) (q 0 / (q 0 + q 1)) ≤ min (x 0) (x 1) at hm
    rw [min_self] at hm
    obtain ⟨e0, e1, e2⟩ := h2 (x 0) (x 1) (x 2) hx0 hx1 hx2 (by linarith) hm
    funext l
    fin_cases l
    · exact e0
    · exact e1
    · exact e2
  · rintro rfl
    refine ⟨⟨⟨ht0, ht0, le_rfl⟩, ?_⟩, fun y ⟨hy0, hy1, hy2⟩ hb => ?_⟩
    · change q 0 * (q 0 / (q 0 + q 1)) + q 1 * (q 0 / (q 0 + q 1)) + q 2 * 0 ≤ q 0
      have key : q 0 * (q 0 / (q 0 + q 1)) + q 1 * (q 0 / (q 0 + q 1)) = q 0 := by
        field_simp [(add_pos (hq 0) (hq 1)).ne']
      linarith
    · change min (y 0) (y 1) ≤ min (q 0 / (q 0 + q 1)) (q 0 / (q 0 + q 1))
      rw [min_self]
      exact h1 (y 0) (y 1) (y 2) hy0 hy1 hy2 (by linarith)

/-- **Footnote 62** (MWG, p. 623). At `p ≫ 0` consumer `2` demands exactly
`(0, p₂/(p₂ + p₃), p₂/(p₂ + p₃))`. -/
theorem scarf_demand_1 {q : Fin 3 → ℝ} (hq : q ∈ posOrthant 3) (x : Fin 3 → ℝ) :
    x ∈ scarfEconomy.demand 1 q ↔
      x = ![0, q 1 / (q 1 + q 2), q 1 / (q 1 + q 2)] := by
  obtain ⟨h1, h2⟩ := scarf_leontief (hq 1) (hq 2) (hq 0)
  have ht0 : 0 ≤ q 1 / (q 1 + q 2) := div_nonneg (hq 1).le (add_pos (hq 1) (hq 2)).le
  rw [scarf_demand_iff]
  constructor
  · rintro ⟨⟨⟨hx0, hx1, hx2⟩, hb⟩, hmax⟩
    have hm := hmax ![0, q 1 / (q 1 + q 2), q 1 / (q 1 + q 2)] ⟨le_rfl, ht0, ht0⟩
      (by
        change q 0 * 0 + q 1 * (q 1 / (q 1 + q 2)) + q 2 * (q 1 / (q 1 + q 2)) ≤ q 1
        have key : q 1 * (q 1 / (q 1 + q 2)) + q 2 * (q 1 / (q 1 + q 2)) = q 1 := by
          field_simp [(add_pos (hq 1) (hq 2)).ne']
        linarith)
    change min (q 1 / (q 1 + q 2)) (q 1 / (q 1 + q 2)) ≤ min (x 1) (x 2) at hm
    rw [min_self] at hm
    obtain ⟨e1, e2, e0⟩ := h2 (x 1) (x 2) (x 0) hx1 hx2 hx0 (by linarith) hm
    funext l
    fin_cases l
    · exact e0
    · exact e1
    · exact e2
  · rintro rfl
    refine ⟨⟨⟨le_rfl, ht0, ht0⟩, ?_⟩, fun y ⟨hy0, hy1, hy2⟩ hb => ?_⟩
    · change q 0 * 0 + q 1 * (q 1 / (q 1 + q 2)) + q 2 * (q 1 / (q 1 + q 2)) ≤ q 1
      have key : q 1 * (q 1 / (q 1 + q 2)) + q 2 * (q 1 / (q 1 + q 2)) = q 1 := by
        field_simp [(add_pos (hq 1) (hq 2)).ne']
      linarith
    · change min (y 1) (y 2) ≤ min (q 1 / (q 1 + q 2)) (q 1 / (q 1 + q 2))
      rw [min_self]
      exact h1 (y 1) (y 2) (y 0) hy1 hy2 hy0 (by linarith)

/-- **Footnote 62** (MWG, p. 623). At `p ≫ 0` consumer `3` demands exactly
`(p₃/(p₃ + p₁), 0, p₃/(p₃ + p₁))`. -/
theorem scarf_demand_2 {q : Fin 3 → ℝ} (hq : q ∈ posOrthant 3) (x : Fin 3 → ℝ) :
    x ∈ scarfEconomy.demand 2 q ↔
      x = ![q 2 / (q 2 + q 0), 0, q 2 / (q 2 + q 0)] := by
  obtain ⟨h1, h2⟩ := scarf_leontief (hq 2) (hq 0) (hq 1)
  have ht0 : 0 ≤ q 2 / (q 2 + q 0) := div_nonneg (hq 2).le (add_pos (hq 2) (hq 0)).le
  rw [scarf_demand_iff]
  constructor
  · rintro ⟨⟨⟨hx0, hx1, hx2⟩, hb⟩, hmax⟩
    have hm := hmax ![q 2 / (q 2 + q 0), 0, q 2 / (q 2 + q 0)] ⟨ht0, le_rfl, ht0⟩
      (by
        change q 0 * (q 2 / (q 2 + q 0)) + q 1 * 0 + q 2 * (q 2 / (q 2 + q 0)) ≤ q 2
        have key : q 2 * (q 2 / (q 2 + q 0)) + q 0 * (q 2 / (q 2 + q 0)) = q 2 := by
          field_simp [(add_pos (hq 2) (hq 0)).ne']
        linarith)
    change min (q 2 / (q 2 + q 0)) (q 2 / (q 2 + q 0)) ≤ min (x 2) (x 0) at hm
    rw [min_self] at hm
    obtain ⟨e2, e0, e1⟩ := h2 (x 2) (x 0) (x 1) hx2 hx0 hx1 (by linarith) hm
    funext l
    fin_cases l
    · exact e0
    · exact e1
    · exact e2
  · rintro rfl
    refine ⟨⟨⟨ht0, le_rfl, ht0⟩, ?_⟩, fun y ⟨hy0, hy1, hy2⟩ hb => ?_⟩
    · change q 0 * (q 2 / (q 2 + q 0)) + q 1 * 0 + q 2 * (q 2 / (q 2 + q 0)) ≤ q 2
      have key : q 2 * (q 2 / (q 2 + q 0)) + q 0 * (q 2 / (q 2 + q 0)) = q 2 := by
        field_simp [(add_pos (hq 2) (hq 0)).ne']
      linarith
    · change min (y 2) (y 0) ≤ min (q 2 / (q 2 + q 0)) (q 2 / (q 2 + q 0))
      rw [min_self]
      exact h1 (y 2) (y 0) (y 1) hy2 hy0 hy1 (by linarith)

/-- **Footnote 62** (MWG, p. 623). At `p ≫ 0` every consumer's demand is a single bundle and the
aggregate excess demand of Scarf's economy is `scarfZ p`. -/
theorem scarf_excessDemand {q : Fin 3 → ℝ} (hq : q ∈ posOrthant 3) {x : Fin 3 → Fin 3 → ℝ}
    (hx : ∀ i, x i ∈ scarfEconomy.demand i q) :
    ∑ i, x i - scarfEconomy.totalEndowment = scarfZ q := by
  have e0 := (scarf_demand_0 hq _).1 (hx 0)
  have e1 := (scarf_demand_1 hq _).1 (hx 1)
  have e2 := (scarf_demand_2 hq _).1 (hx 2)
  have h01 : q 0 + q 1 ≠ 0 := (add_pos (hq 0) (hq 1)).ne'
  have h12 : q 1 + q 2 ≠ 0 := (add_pos (hq 1) (hq 2)).ne'
  have h20 : q 2 + q 0 ≠ 0 := (add_pos (hq 2) (hq 0)).ne'
  funext l
  simp only [ExchangeEconomy.totalEndowment, scarfEconomy, ExchangeEconomy.ofOrthant,
    Fin.sum_univ_three, e0, e1, e2, Pi.sub_apply, Pi.add_apply, scarfω]
  fin_cases l <;> simp [scarfZ] <;> field_simp <;> ring

/-! ### Properties of `scarfZ` -/

/-- `scarfZ` is continuous, homogeneous of degree zero, satisfies Walras' law and is bounded
below (properties (i)-(iv) of Proposition 17.B.2). -/
theorem scarfZ_props : EDContinuous scarfZ ∧ EDHomogeneous scarfZ ∧ EDWalrasLaw scarfZ ∧
    EDBoundedBelow scarfZ := by
  refine ⟨?_, fun q hq α hα => ?_, fun q hq => ?_, ⟨2, two_pos, fun q hq l => ?_⟩⟩
  · refine continuousOn_pi.2 fun l => ?_
    have hc : ∀ k, ContinuousOn (fun q : Fin 3 → ℝ => q k) (posOrthant 3) :=
      fun k => (continuous_apply k).continuousOn
    have hd : ∀ a b d : Fin 3, ContinuousOn (fun q : Fin 3 → ℝ => q a / (q b + q d))
        (posOrthant 3) := fun a b d =>
      (hc a).div ((hc b).add (hc d)) fun q hq => (add_pos (hq b) (hq d)).ne'
    fin_cases l
    · exact (hd 2 2 0).sub (hd 1 0 1)
    · exact (hd 0 0 1).sub (hd 2 1 2)
    · exact (hd 1 1 2).sub (hd 0 2 0)
  · have h01 : q 0 + q 1 ≠ 0 := (add_pos (hq 0) (hq 1)).ne'
    have h12 : q 1 + q 2 ≠ 0 := (add_pos (hq 1) (hq 2)).ne'
    have h20 : q 2 + q 0 ≠ 0 := (add_pos (hq 2) (hq 0)).ne'
    have hdiv : ∀ a b d : Fin 3, α * q a / (α * q b + α * q d) = q a / (q b + q d) := by
      intro a b d
      rw [← mul_add, mul_div_mul_left _ _ hα.ne']
    simp only [scarfZ, Pi.smul_apply, smul_eq_mul, hdiv]
  · have h01 : q 0 + q 1 ≠ 0 := (add_pos (hq 0) (hq 1)).ne'
    have h12 : q 1 + q 2 ≠ 0 := (add_pos (hq 1) (hq 2)).ne'
    have h20 : q 2 + q 0 ≠ 0 := (add_pos (hq 2) (hq 0)).ne'
    simp only [dotProduct, Fin.sum_univ_three, scarfZ]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    ring
  · have hf : ∀ a b : Fin 3, 0 ≤ q a / (q a + q b) ∧ q a / (q a + q b) ≤ 1 := fun a b =>
      ⟨div_nonneg (hq a).le (add_pos (hq a) (hq b)).le,
        (div_le_one (add_pos (hq a) (hq b))).2 (by linarith [hq b])⟩
    fin_cases l
    · have := hf 2 0
      have := hf 1 0
      have e : q 1 / (q 0 + q 1) = q 1 / (q 1 + q 0) := by rw [add_comm]
      simp only [scarfZ]
      simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, neg_lt_sub_iff_lt_add,
        gt_iff_lt]
      linarith
    · have := hf 0 1
      have := hf 2 1
      have e : q 2 / (q 1 + q 2) = q 2 / (q 2 + q 1) := by rw [add_comm]
      simp only [scarfZ]
      simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        neg_lt_sub_iff_lt_add, gt_iff_lt]
      linarith
    · have := hf 1 2
      have := hf 0 2
      have e : q 0 / (q 2 + q 0) = q 0 / (q 0 + q 2) := by rw [add_comm]
      simp only [scarfZ]
      simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, neg_lt_sub_iff_lt_add, gt_iff_lt]
      linarith

/-- **Footnote 62** (MWG, p. 623). The equilibrium is unique: `p ≫ 0` is an equilibrium price
vector of Scarf's economy iff `p₁ = p₂ = p₃`. -/
theorem scarfZ_eqm_iff {q : Fin 3 → ℝ} :
    IsEqmPrice scarfZ q ↔ q ∈ posOrthant 3 ∧ q 0 = q 1 ∧ q 1 = q 2 := by
  constructor
  · rintro ⟨hq, hz⟩
    have h01 : q 0 + q 1 ≠ 0 := (add_pos (hq 0) (hq 1)).ne'
    have h12 : q 1 + q 2 ≠ 0 := (add_pos (hq 1) (hq 2)).ne'
    have h20 : q 2 + q 0 ≠ 0 := (add_pos (hq 2) (hq 0)).ne'
    have z0 := congrFun hz 0
    have z1 := congrFun hz 1
    simp only [scarfZ, Pi.zero_apply] at z0 z1
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at z0 z1
    rw [sub_eq_zero, div_eq_div_iff h20 h01] at z0
    rw [sub_eq_zero, div_eq_div_iff h01 h12] at z1
    have a : q 0 * (q 2 - q 1) = 0 := by linarith
    have b : q 1 * (q 0 - q 2) = 0 := by linarith
    have a' := (mul_eq_zero.1 a).resolve_left (hq 0).ne'
    have b' := (mul_eq_zero.1 b).resolve_left (hq 1).ne'
    exact ⟨hq, by linarith, by linarith⟩
  · rintro ⟨hq, h1, h2⟩
    refine ⟨hq, funext fun l => ?_⟩
    fin_cases l <;> simp [scarfZ, h1, h2]

/-- Along Scarf's excess demand, `∑ₗ zₗ(p)/pₗ = 0` for `p ≫ 0`. -/
theorem scarfZ_dual {q : Fin 3 → ℝ} (hq : q ∈ posOrthant 3) :
    scarfZ q 0 * (q 1 * q 2) + q 0 * (scarfZ q 1 * q 2) + q 0 * q 1 * scarfZ q 2 = 0 := by
  have h01 : q 0 + q 1 ≠ 0 := (add_pos (hq 0) (hq 1)).ne'
  have h12 : q 1 + q 2 ≠ 0 := (add_pos (hq 1) (hq 2)).ne'
  have h20 : q 2 + q 0 ≠ 0 := (add_pos (hq 2) (hq 0)).ne'
  simp only [scarfZ]
  simp
  field_simp
  ring

/-- `scarfZ` is continuously differentiable on `ℝ³₊₊`. -/
theorem scarfZ_contDiffOn : ContDiffOn ℝ 1 scarfZ (posOrthant 3) := by
  refine contDiffOn_pi.2 fun l => ?_
  have hc : ∀ k, ContDiffOn ℝ 1 (fun q : Fin 3 → ℝ => q k) (posOrthant 3) :=
    fun k => (contDiff_apply ℝ ℝ k).contDiffOn
  have hd : ∀ a b d : Fin 3, ContDiffOn ℝ 1 (fun q : Fin 3 → ℝ => q a / (q b + q d))
      (posOrthant 3) := fun a b d =>
    (hc a).div ((hc b).add (hc d)) fun q hq => (add_pos (hq b) (hq d)).ne'
  fin_cases l
  · exact (hd 2 2 0).sub (hd 1 0 1)
  · exact (hd 0 0 1).sub (hd 2 1 2)
  · exact (hd 1 1 2).sub (hd 0 2 0)

/-! ### Conservation laws and existence of trajectories -/

/-- Along any solution of `dq/dt = z(q)` with `q(t) ≫ 0`, `d(q₁q₂q₃)/dt = 0`. -/
theorem scarf_hasDeriv_prod {α : ℝ → Fin 3 → ℝ} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (tatField (fun _ => 1) scarfZ (α t)) s t)
    (hpos : α t ∈ posOrthant 3) :
    HasDerivWithinAt (fun u => α u 0 * α u 1 * α u 2) 0 s t := by
  have hl : ∀ l, HasDerivWithinAt (fun u => α u l) (scarfZ (α t) l) s t := fun l => by
    simpa [tatField] using hasDerivWithinAt_pi.1 hα l
  have h := ((hl 0).mul (hl 1)).mul (hl 2)
  convert h using 1
  have := scarfZ_dual hpos
  simp only [Pi.mul_apply]
  linarith

/-- Along a trajectory of Scarf's economy (`c = (1, 1, 1)`), `p₁p₂p₃` is constant. -/
theorem scarf_prod_const {p : ℝ → Fin 3 → ℝ} (hp : IsTatPath (fun _ => 1) scarfZ p) {t : ℝ}
    (ht : 0 ≤ t) : p t 0 * p t 1 * p t 2 = p 0 0 * p 0 1 * p 0 2 := by
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => p s 0 * p s 1 * p s 2) 0 (Ici 0) s :=
    fun s hs => scarf_hasDeriv_prod (hp.2 s hs) (hp.1 s hs)
  have h1 := tat_monotoneOn hd (fun _ _ => le_rfl) (Set.mem_Ici.2 le_rfl) ht ht
  have h2 := tat_monotoneOn (F := fun s => -(p s 0 * p s 1 * p s 2)) (F' := fun _ => 0)
    (fun s hs => by simpa using (hd s hs).fun_neg) (fun _ _ => le_rfl)
    (Set.mem_Ici.2 le_rfl) ht ht
  simp only at h1 h2
  linarith

/-- On `{∑ qₗ² = N, q₁q₂q₃ = P}` with `q ≫ 0`, `P > 0`: `P/(N + 1)² ≤ qₗ ≤ N + 1`. -/
theorem scarf_coord_bounds {q : Fin 3 → ℝ} (hq : ∀ l, 0 < q l) {N P : ℝ}
    (hN : wNormSq (fun _ => 1) q = N) (hP : q 0 * q 1 * q 2 = P) (l : Fin 3) :
    P / (N + 1) ^ 2 ≤ q l ∧ q l ≤ N + 1 := by
  have hup : ∀ k, q k ≤ N + 1 := fun k => by
    have := sq_le_wNormSq (fun _ => one_pos) q k
    rw [hN, one_mul] at this
    nlinarith [sq_nonneg (q k - 1)]
  refine ⟨?_, hup l⟩
  have hN1 : 0 < N + 1 := lt_of_lt_of_le (hq 0) (hup 0)
  rw [div_le_iff₀ (by positivity)]
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  have u0 := hup 0
  have u1 := hup 1
  have u2 := hup 2
  fin_cases l
  · change P ≤ q 0 * (N + 1) ^ 2
    rw [← hP]
    have : q 1 * q 2 ≤ (N + 1) * (N + 1) := mul_le_mul u1 u2 h2.le hN1.le
    nlinarith [mul_le_mul_of_nonneg_left this h0.le]
  · change P ≤ q 1 * (N + 1) ^ 2
    rw [← hP]
    have : q 0 * q 2 ≤ (N + 1) * (N + 1) := mul_le_mul u0 u2 h2.le hN1.le
    nlinarith [mul_le_mul_of_nonneg_left this h1.le]
  · change P ≤ q 2 * (N + 1) ^ 2
    rw [← hP]
    have : q 0 * q 1 ≤ (N + 1) * (N + 1) := mul_le_mul u0 u1 h1.le hN1.le
    nlinarith [mul_le_mul_of_nonneg_left this h2.le]

/-- **(17.H.1)** for Scarf's economy (MWG, p. 621): from every `p(0) ≫ 0` a tâtonnement
trajectory (`c = (1, 1, 1)`) exists for all `t ≥ 0`. -/
theorem scarf_tat_exists {p0 : Fin 3 → ℝ} (hp0 : p0 ∈ posOrthant 3) :
    ∃ p : ℝ → Fin 3 → ℝ, p 0 = p0 ∧ IsTatPath (fun _ => 1) scarfZ p := by
  have hc : ∀ l : Fin 3, (0 : ℝ) < (fun _ => (1 : ℝ)) l := fun _ => one_pos
  set N0 := wNormSq (fun _ => (1 : ℝ)) p0 with hN0def
  set P0 := p0 0 * p0 1 * p0 2 with hP0def
  have hP0 : 0 < P0 := mul_pos (mul_pos (hp0 0) (hp0 1)) (hp0 2)
  have hN0 : 0 ≤ N0 := wNormSq_nonneg hc p0
  set M := N0 + 1 with hM
  have hMpos : 0 < M := by linarith
  set η1 := P0 / M ^ 2 with hη1def
  have hη1 : 0 < η1 := by positivity
  set Bx : Set (Fin 3 → ℝ) := Icc (fun _ => η1 / 2) (fun _ => M + η1 / 2) with hBx
  have hBpos : Bx ⊆ posOrthant 3 := fun q hq l => lt_of_lt_of_le (half_pos hη1) (hq.1 l)
  set v := tatField (fun _ => (1 : ℝ)) scarfZ with hvdef
  have hv : ContDiffOn ℝ 1 v (posOrthant 3) :=
    contDiffOn_pi.2 fun l => contDiffOn_const.mul (contDiffOn_pi.1 scarfZ_contDiffOn l)
  obtain ⟨K, hK⟩ := (hv.mono hBpos).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := fun _ : Fin 3 => η1 / 2)
    (b := fun _ => M + η1 / 2)).exists_bound_of_continuousOn (hv.mono hBpos).continuousOn
  set Lb : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩ with hLb
  set a : ℝ≥0 := ⟨η1 / 2, (half_pos hη1).le⟩ with ha
  set h : ℝ := (a : ℝ) / (Lb + 1) with hh
  have hhpos : 0 < h := div_pos (half_pos hη1) (by positivity)
  set R : Set (Fin 3 → ℝ) :=
    {q | wNormSq (fun _ => 1) q = N0 ∧ q 0 * q 1 * q 2 = P0 ∧ ∀ l, 0 < q l} with hR
  have hball : ∀ x ∈ R, closedBall x a ⊆ Bx := by
    intro x hx y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have hy' : ∀ l, |y l - x l| ≤ η1 / 2 := fun l => by
      have := (norm_le_pi_norm (y - x) l).trans hy
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      exact this
    refine ⟨fun l => ?_, fun l => ?_⟩
    · have h1 := hy' l
      have h2 := (scarf_coord_bounds hx.2.2 hx.1 hx.2.1 l).1
      have := neg_abs_le (y l - x l)
      change η1 / 2 ≤ y l
      linarith
    · have h1 := hy' l
      have h2 := (scarf_coord_bounds hx.2.2 hx.1 hx.2.1 l).2
      have := le_abs_self (y l - x l)
      change y l ≤ M + η1 / 2
      linarith
  have hstep : ∀ x ∈ R, ∃ α : ℝ → Fin 3 → ℝ, α 0 = x ∧ ∀ t ∈ Icc 0 h,
      HasDerivWithinAt α (v (α t)) (Icc 0 h) t ∧ α t ∈ closedBall x a := by
    intro x hx
    refine tex_picard hhpos.le (Lb := Lb) (K := K)
      (fun y hy => (hC y (hball x hx hy)).trans (le_max_left _ _)) (hK.mono (hball x hx)) ?_
    have hL0 : (0 : ℝ) ≤ Lb := Lb.2
    rw [hh, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [a.2]
  choose! φ hφ using hstep
  have hφpos : ∀ x ∈ R, ∀ t ∈ Icc 0 h, φ x t ∈ posOrthant 3 :=
    fun x hx t ht => hBpos (hball x hx ((hφ x hx).2 t ht).2)
  have hφR : ∀ x ∈ R, φ x h ∈ R := by
    intro x hx
    have hd := fun t ht => ((hφ x hx).2 t ht).1
    have hright : ∀ t ∈ Ico 0 h, HasDerivWithinAt (φ x) (v (φ x t)) (Ici t) t :=
      fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    have hcont : ContinuousOn (φ x) (Icc 0 h) := fun t ht => (hd t ht).continuousWithinAt
    have hmem : h ∈ Icc 0 h := ⟨hhpos.le, le_rfl⟩
    have hN := constant_of_has_deriv_right_zero (f := fun u => wNormSq (fun _ => 1) (φ x u))
      ((continuous_wNormSq _).comp_continuousOn hcont) (fun u hu => by
        have := tatField_hasDeriv_wNormSq hc (hright u hu)
        rwa [scarfZ_props.2.2.1 _ (hφpos x hx u (Ico_subset_Icc_self hu)), mul_zero] at this)
      h hmem
    have hcp : ContinuousOn (fun u => φ x u 0 * φ x u 1 * φ x u 2) (Icc 0 h) :=
      (((continuous_apply 0).comp_continuousOn hcont).mul
        ((continuous_apply 1).comp_continuousOn hcont)).mul
        ((continuous_apply 2).comp_continuousOn hcont)
    have hPc := constant_of_has_deriv_right_zero hcp (fun u hu =>
      scarf_hasDeriv_prod (hright u hu) (hφpos x hx u (Ico_subset_Icc_self hu))) h hmem
    refine ⟨?_, ?_, hφpos x hx h hmem⟩
    · rw [hN, (hφ x hx).1, hx.1]
    · rw [hPc, (hφ x hx).1, hx.2.1]
  have hx0 : p0 ∈ R := ⟨rfl, rfl, hp0⟩
  obtain ⟨p, hp0', hp⟩ := tex_glue (v := v) (U := posOrthant 3) hhpos φ
    (fun x hx => (hφ x hx).1) (fun x hx t ht => ((hφ x hx).2 t ht).1) hφpos hφR hx0
  exact ⟨p, hp0', fun t ht => (hp t ht).1, fun t ht => (hp t ht).2⟩

/-! ### No convergence -/

/-- **Footnote 62** (MWG, p. 623). A tâtonnement trajectory of Scarf's economy that starts off
the equilibrium ray converges to no equilibrium price vector: the sum of squares and the product
of the prices are constant, and the equilibrium with the same sum of squares has a larger
product (the strict inequality of arithmetic and geometric means). -/
theorem scarf_not_converge {p : ℝ → Fin 3 → ℝ} (hp : IsTatPath (fun _ => 1) scarfZ p)
    (hoff : ¬ (p 0 0 = p 0 1 ∧ p 0 1 = p 0 2)) :
    ¬ ∃ q, IsEqmPrice scarfZ q ∧ Tendsto p atTop (𝓝 q) := by
  rintro ⟨q, hq, hlim⟩
  obtain ⟨hqpos, hq01, hq12⟩ := scarfZ_eqm_iff.1 hq
  have hev : ∀ᶠ t in atTop, (0 : ℝ) ≤ t := eventually_ge_atTop 0
  have hN : wNormSq (fun _ => 1) q = wNormSq (fun _ => 1) (p 0) := by
    have h1 : Tendsto (fun t => wNormSq (fun _ => 1) (p t)) atTop
        (𝓝 (wNormSq (fun _ => 1) q)) := ((continuous_wNormSq _).tendsto q).comp hlim
    have h2 : Tendsto (fun t => wNormSq (fun _ => 1) (p t)) atTop
        (𝓝 (wNormSq (fun _ => 1) (p 0))) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht =>
        (tat_wNormSq_const (fun _ => one_pos) scarfZ_props.2.2.1 hp ht).symm)
    exact tendsto_nhds_unique h1 h2
  have hP : q 0 * q 1 * q 2 = p 0 0 * p 0 1 * p 0 2 := by
    have hc : Continuous fun r : Fin 3 → ℝ => r 0 * r 1 * r 2 := by fun_prop
    have h1 := (hc.tendsto q).comp hlim
    have h2 : Tendsto (fun t => p t 0 * p t 1 * p t 2) atTop
        (𝓝 (p 0 0 * p 0 1 * p 0 2)) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (scarf_prod_const hp ht).symm)
    exact tendsto_nhds_unique h1 h2
  simp only [wNormSq, Fin.sum_univ_three, div_one] at hN
  rw [← hq12, ← hq01] at hN
  rw [← hq12, ← hq01] at hP
  have hp0 := hp.1 0 le_rfl
  have a := hp0 0
  have b := hp0 1
  have c := hp0 2
  set x := p 0 0 ^ 2
  set y := p 0 1 ^ 2
  set w := p 0 2 ^ 2
  -- `27 xyw = (x + y + w)³` forces `x = y = w`
  have hcube : 27 * (x * y * w) = (x + y + w) ^ 3 := by
    have e1 : (x + y + w) ^ 3 = 27 * (q 0 ^ 2) ^ 3 := by rw [← hN]; ring
    have e2 : x * y * w = (q 0 ^ 2) ^ 3 := by
      change p 0 0 ^ 2 * p 0 1 ^ 2 * p 0 2 ^ 2 = _
      rw [show p 0 0 ^ 2 * p 0 1 ^ 2 * p 0 2 ^ 2 = (p 0 0 * p 0 1 * p 0 2) ^ 2 by ring, ← hP]
      ring
    rw [e1, e2]
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hw : 0 < w := by positivity
  have hxy : x = y ∧ y = w := by
    have key : (x + y + w) * ((x - y) ^ 2 + (y - w) ^ 2 + (w - x) ^ 2) +
        3 * (x * (y - w) ^ 2 + y * (w - x) ^ 2 + w * (x - y) ^ 2) = 0 := by
      nlinarith [hcube]
    have s1 : 0 ≤ (x + y + w) * ((x - y) ^ 2 + (y - w) ^ 2 + (w - x) ^ 2) := by positivity
    have s2 : 0 ≤ x * (y - w) ^ 2 + y * (w - x) ^ 2 + w * (x - y) ^ 2 := by positivity
    have s3 : (x + y + w) * ((x - y) ^ 2 + (y - w) ^ 2 + (w - x) ^ 2) = 0 := by linarith
    have s4 : (x - y) ^ 2 + (y - w) ^ 2 + (w - x) ^ 2 = 0 :=
      (mul_eq_zero.1 s3).resolve_left (by positivity)
    constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (y - w), sq_nonneg (w - x)]
  apply hoff
  obtain ⟨e1, e2⟩ := hxy
  refine ⟨?_, ?_⟩
  · have : (p 0 0 - p 0 1) * (p 0 0 + p 0 1) = 0 := by
      change p 0 0 ^ 2 = p 0 1 ^ 2 at e1
      nlinarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (by positivity))
  · have : (p 0 1 - p 0 2) * (p 0 1 + p 0 2) = 0 := by
      change p 0 1 ^ 2 = p 0 2 ^ 2 at e2
      nlinarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (by positivity))

/-- **Footnote 62** (MWG, p. 623): "uniqueness by itself does not imply stability", for `L = 3`.
In Scarf's economy the equilibrium is unique (the ray `p₁ = p₂ = p₃`, `scarfZ_eqm_iff`), and the
tâtonnement trajectory from `p(0) = (1, 2, 2)` exists and converges to no equilibrium price
vector. -/
theorem footnote_17_62_three_goods :
    (∀ q, IsEqmPrice scarfZ q ↔ q ∈ posOrthant 3 ∧ q 0 = q 1 ∧ q 1 = q 2) ∧
      ∃ p : ℝ → Fin 3 → ℝ, p 0 = ![1, 2, 2] ∧ IsTatPath (fun _ => 1) scarfZ p ∧
        ¬ ∃ q, IsEqmPrice scarfZ q ∧ Tendsto p atTop (𝓝 q) := by
  refine ⟨fun q => scarfZ_eqm_iff, ?_⟩
  have h0 : (![1, 2, 2] : Fin 3 → ℝ) ∈ posOrthant 3 := fun l => by
    fin_cases l <;> norm_num
  obtain ⟨p, hp0, hp⟩ := scarf_tat_exists h0
  refine ⟨p, hp0, hp, scarf_not_converge hp ?_⟩
  rw [hp0]
  norm_num

/-- Scarf's excess demand violates the boundary condition (v) of Proposition 17.B.2: along
`pⁿ = (1/(n + 1), 1, 1) → (0, 1, 1)` every `zₗ(pⁿ)` stays below `1`. -/
theorem scarfZ_not_boundary : ¬ EDBoundary scarfZ := by
  intro h
  set ps : ℕ → Fin 3 → ℝ := fun n => ![1 / ((n : ℝ) + 1), 1, 1] with hps
  have hpos : ∀ n, ps n ∈ posOrthant 3 := fun n l => by
    fin_cases l
    · change 0 < 1 / ((n : ℝ) + 1)
      positivity
    · change (0 : ℝ) < 1
      exact one_pos
    · change (0 : ℝ) < 1
      exact one_pos
  have hlim : Tendsto ps atTop (𝓝 ![0, 1, 1]) := by
    refine tendsto_pi_nhds.2 fun l => ?_
    fin_cases l
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have hne : (![0, 1, 1] : Fin 3 → ℝ) ≠ 0 := fun h0 => by
    have := congrFun h0 1
    simp at this
  obtain ⟨n, l, hl⟩ := (h ps _ hpos hlim hne ⟨0, rfl⟩ 1).exists
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hf : ∀ a b : ℝ, 0 < a → 0 < b → a / (a + b) ≤ 1 ∧ 0 ≤ a / (a + b) := fun a b ha hb =>
    ⟨(div_le_one (add_pos ha hb)).2 (by linarith), div_nonneg ha.le (add_pos ha hb).le⟩
  have h1 := hf 1 ε one_pos hε
  have h2 := hf ε 1 hε one_pos
  have h3 := hf 1 1 one_pos one_pos
  fin_cases l
  · change 1 < 1 / (1 + ε) - 1 / (ε + 1) at hl
    have := div_nonneg zero_le_one (add_pos hε one_pos).le
    linarith
  · change 1 < ε / (ε + 1) - 1 / (1 + 1) at hl
    linarith
  · change 1 < 1 / (1 + 1) - ε / (1 + ε) at hl
    have := div_nonneg hε.le (add_pos one_pos hε).le
    linarith

end MWG.PositiveEquilibriumTheory
