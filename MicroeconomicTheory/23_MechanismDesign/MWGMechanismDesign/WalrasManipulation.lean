/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Example 23.B.2: manipulating the Walrasian social choice function

MWG, Section 23.B, Example 23.B.2 and Figure 23.B.1 (pp. 860-861). A two-consumer, two-good
exchange economy; consumer 1 has one possible type, consumer 2 has all individualistic,
monotone, convex preferences. The social choice function that selects the Walrasian equilibrium
allocation for each announced profile is ex post efficient, but consumer 2 can gain by
misreporting. MWG argue with offer curves in Figure 23.B.1; we make the example concrete.

Endowments `ω₁ = (0, 1)`, `ω₂ = (1, 0)`; consumer 1 has `u₁(x, y) = xy`; consumer 2's true type
`θ₂'` has `u₂(x, y) = xy` and the misreported type `θ₂''` has the (monotone, convex) Leontief
preference `min(x, 3y/2)`. Prices are `p = (p₁, p₂) ≫ 0`.

* Demands: `xy` demands `(w/(2p₁), w/(2p₂))` (`wm_cd_opt_iff`); `min(x, βy)` demands
  `(βw/(βp₁ + p₂), w/(βp₁ + p₂))` (`wm_leontief_opt_iff`), uniquely.
* With the true preferences the unique Walrasian equilibrium allocation gives each consumer
  `(1/2, 1/2)` (prices `p₁ = p₂`, `example_23_B_2_truthful`); with consumer 2 announcing `θ₂''`
  it gives consumer 1 `(1/4, 1/2)` and consumer 2 `(3/4, 1/2)` (prices `p₂ = p₁/2`,
  `example_23_B_2_misreport`).
* `example_23_B_2`: the Walrasian social choice function is well defined (unique equilibria)
  and consumer 2 of true type `θ₂'` strictly prefers the allocation he gets by announcing `θ₂''`
  (`3/8 > 1/4`): truth telling is not optimal for him.
* `wm_first_welfare`: the first welfare theorem in this setting, so the Walrasian social choice
  function is ex post efficient (`example_23_B_2_efficient`).
-/

namespace MWG.MechanismDesign

/-- **Example 23.B.2** (MWG, p. 860): `z` is an optimal bundle for utility `u` at prices
`p ≫ 0` and wealth `w`: `z ≥ 0`, `p · z ≤ w`, and `u(z') ≤ u(z)` for every affordable `z' ≥ 0`. -/
def WmOpt (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (w : ℝ) (z : ℝ × ℝ) : Prop :=
  0 ≤ z.1 ∧ 0 ≤ z.2 ∧ p.1 * z.1 + p.2 * z.2 ≤ w ∧
    ∀ z' : ℝ × ℝ, 0 ≤ z'.1 → 0 ≤ z'.2 → p.1 * z'.1 + p.2 * z'.2 ≤ w → u z' ≤ u z

/-- **Example 23.B.2** (MWG, p. 860): a Walrasian equilibrium of the two-consumer exchange
economy with utilities `u₁`, `u₂` and endowments `ω₁`, `ω₂`: prices `p ≫ 0`, each consumer's
bundle optimal given the value of his endowment, and markets clear. -/
def WmEq (u1 u2 : ℝ × ℝ → ℝ) (ω1 ω2 p z1 z2 : ℝ × ℝ) : Prop :=
  0 < p.1 ∧ 0 < p.2 ∧ z1.1 + z2.1 = ω1.1 + ω2.1 ∧ z1.2 + z2.2 = ω1.2 + ω2.2 ∧
    WmOpt u1 p (p.1 * ω1.1 + p.2 * ω1.2) z1 ∧ WmOpt u2 p (p.1 * ω2.1 + p.2 * ω2.2) z2

/-- Cobb-Douglas utility `u(x, y) = xy`. -/
def wmCD (z : ℝ × ℝ) : ℝ := z.1 * z.2

/-- Leontief utility `u(x, y) = min(x, βy)`. -/
noncomputable def wmLeontief (β : ℝ) (z : ℝ × ℝ) : ℝ := min z.1 (β * z.2)

/-- With `u = xy`, prices `p ≫ 0` and wealth `w > 0`, the optimal bundle is unique:
`(w/(2p₁), w/(2p₂))`. -/
theorem wm_cd_opt_iff {p : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2) {w : ℝ} (hw : 0 < w)
    (z : ℝ × ℝ) : WmOpt wmCD p w z ↔ z = (w / (2 * p.1), w / (2 * p.2)) := by
  have bound : ∀ z' : ℝ × ℝ, 0 ≤ z'.1 → 0 ≤ z'.2 → p.1 * z'.1 + p.2 * z'.2 ≤ w →
      4 * (p.1 * p.2) * (z'.1 * z'.2) ≤ w ^ 2 := by
    intro z' h1 h2 hb
    have hs : 0 ≤ p.1 * z'.1 + p.2 * z'.2 := by positivity
    nlinarith [sq_nonneg (p.1 * z'.1 - p.2 * z'.2)]
  have hval : 4 * (p.1 * p.2) * (w / (2 * p.1) * (w / (2 * p.2))) = w ^ 2 := by
    field_simp; ring
  have hpp : 0 < 4 * (p.1 * p.2) := by positivity
  constructor
  · rintro ⟨h1, h2, hb, hmax⟩
    have hge := hmax (w / (2 * p.1), w / (2 * p.2)) (by positivity) (by positivity)
      (by simp only; field_simp; linarith)
    simp only [wmCD] at hge
    have hle := bound z h1 h2 hb
    have heq : 4 * (p.1 * p.2) * (z.1 * z.2) = w ^ 2 := by nlinarith
    have hs : 0 ≤ p.1 * z.1 + p.2 * z.2 := by positivity
    have hd : (p.1 * z.1 - p.2 * z.2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (p.1 * z.1 - p.2 * z.2)]
    have hd' : p.1 * z.1 = p.2 * z.2 := by
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hd
      linarith
    have hsum : p.1 * z.1 + p.2 * z.2 = w := by nlinarith
    obtain ⟨a, b⟩ := z
    simp only at hd' hsum ⊢
    refine Prod.ext ?_ ?_
    · simp only; field_simp; linarith
    · simp only; field_simp; linarith
  · rintro rfl
    refine ⟨by positivity, by positivity, by simp only; field_simp; linarith,
      fun z' h1 h2 hb => ?_⟩
    have := bound z' h1 h2 hb
    simp only [wmCD]
    nlinarith

/-- With `u = min(x, βy)`, `β > 0`, prices `p ≫ 0` and wealth `w ≥ 0`, the optimal bundle is
unique: `(βw/(βp₁ + p₂), w/(βp₁ + p₂))`. -/
theorem wm_leontief_opt_iff {β : ℝ} (hβ : 0 < β) {p : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    {w : ℝ} (hw : 0 ≤ w) (z : ℝ × ℝ) :
    WmOpt (wmLeontief β) p w z ↔ z = (β * w / (β * p.1 + p.2), w / (β * p.1 + p.2)) := by
  have hD : 0 < β * p.1 + p.2 := by positivity
  set m := β * w / (β * p.1 + p.2) with hm
  have hm' : m * (β * p.1 + p.2) = β * w := by rw [hm]; field_simp
  have bound : ∀ z' : ℝ × ℝ, 0 ≤ z'.1 → 0 ≤ z'.2 → p.1 * z'.1 + p.2 * z'.2 ≤ w →
      wmLeontief β z' ≤ m := by
    intro z' h1 h2 hb
    simp only [wmLeontief]
    set k := min z'.1 (β * z'.2)
    have k1 : k ≤ z'.1 := min_le_left _ _
    have k2 : k ≤ β * z'.2 := min_le_right _ _
    have : k * (β * p.1 + p.2) ≤ β * w := by
      nlinarith [mul_le_mul_of_nonneg_left k1 (mul_nonneg hβ.le hp1.le),
        mul_le_mul_of_nonneg_left k2 hp2.le, mul_le_mul_of_nonneg_left hb hβ.le]
    rw [hm, le_div_iff₀ hD]
    linarith
  constructor
  · rintro ⟨h1, h2, hb, hmax⟩
    have hge := hmax (m, w / (β * p.1 + p.2)) (by positivity) (by positivity)
      (by simp only; rw [hm]; field_simp; linarith)
    have hval : wmLeontief β (m, w / (β * p.1 + p.2)) = m := by
      simp only [wmLeontief]
      rw [min_eq_left (le_of_eq (by rw [hm]; field_simp))]
    rw [hval] at hge
    simp only [wmLeontief] at hge
    have k1 : m ≤ z.1 := hge.trans (min_le_left _ _)
    have k2 : m ≤ β * z.2 := hge.trans (min_le_right _ _)
    have s : β * p.1 * (z.1 - m) + p.2 * (β * z.2 - m) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hb hβ.le]
    have t1 : 0 ≤ β * p.1 * (z.1 - m) := mul_nonneg (by positivity) (by linarith)
    have t2 : 0 ≤ p.2 * (β * z.2 - m) := mul_nonneg hp2.le (by linarith)
    have e1 : z.1 = m := by
      by_contra hne
      have : 0 < β * p.1 * (z.1 - m) :=
        mul_pos (by positivity) (by rcases lt_or_gt_of_ne hne with h | h <;> linarith)
      linarith
    have e2 : β * z.2 = m := by
      by_contra hne
      have : 0 < p.2 * (β * z.2 - m) :=
        mul_pos hp2 (by rcases lt_or_gt_of_ne hne with h | h <;> linarith)
      linarith
    obtain ⟨a, b⟩ := z
    simp only at e1 e2 ⊢
    refine Prod.ext e1 ?_
    simp only
    rw [hm] at e2
    field_simp at e2 ⊢
    nlinarith
  · rintro rfl
    refine ⟨by positivity, by positivity, by simp only; rw [hm]; field_simp; linarith,
      fun z' h1 h2 hb => ?_⟩
    have hval : wmLeontief β (m, w / (β * p.1 + p.2)) = m := by
      simp only [wmLeontief]
      rw [min_eq_left (le_of_eq (by rw [hm]; field_simp))]
    rw [hval]
    exact bound z' h1 h2 hb

/-- Consumer 2's utility by type: `true` is his true type `θ₂'` (`xy`), `false` the
misreported type `θ₂''` (`min(x, 3y/2)`). -/
noncomputable def wmU2 (b : Bool) : ℝ × ℝ → ℝ := if b then wmCD else wmLeontief (3 / 2)

/-- **Example 23.B.2** (MWG, pp. 860-861), the truthful profile: with both consumers having
`u = xy` and endowments `(0, 1)`, `(1, 0)`, prices `(1, 1)` and the allocation
`((1/2, 1/2), (1/2, 1/2))` are a Walrasian equilibrium, and every Walrasian equilibrium has this
allocation. -/
theorem example_23_B_2_truthful :
    WmEq wmCD (wmU2 true) (0, 1) (1, 0) (1, 1) (1 / 2, 1 / 2) (1 / 2, 1 / 2) ∧
      ∀ p z1 z2, WmEq wmCD (wmU2 true) (0, 1) (1, 0) p z1 z2 →
        z1 = (1 / 2, 1 / 2) ∧ z2 = (1 / 2, 1 / 2) := by
  simp only [wmU2, ite_true]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩, ?_⟩
  · rw [wm_cd_opt_iff (p := (1, 1)) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rw [wm_cd_opt_iff (p := (1, 1)) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rintro ⟨p1, p2⟩ z1 z2 ⟨hp1, hp2, hc1, hc2, ho1, ho2⟩
    rw [wm_cd_opt_iff (p := (p1, p2)) hp1 hp2 (by simp only; linarith)] at ho1 ho2
    subst ho1 ho2
    have h1 : (p1 * 0 + p2 * 1) / (2 * p2) = 1 / 2 := by field_simp; ring
    have h2 : (p1 * 1 + p2 * 0) / (2 * p2) = 1 / 2 := by linarith
    rw [div_eq_iff (by positivity)] at h2
    have e : p1 = p2 := by linarith
    subst e
    refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> field_simp <;> ring

/-- **Example 23.B.2** (MWG, pp. 860-861), the misreported profile: with consumer 2 announcing
the Leontief type `min(x, 3y/2)`, prices `(2, 1)` and the allocation `((1/4, 1/2), (3/4, 1/2))`
are a Walrasian equilibrium, and every Walrasian equilibrium has this allocation. -/
theorem example_23_B_2_misreport :
    WmEq wmCD (wmU2 false) (0, 1) (1, 0) (2, 1) (1 / 4, 1 / 2) (3 / 4, 1 / 2) ∧
      ∀ p z1 z2, WmEq wmCD (wmU2 false) (0, 1) (1, 0) p z1 z2 →
        z1 = (1 / 4, 1 / 2) ∧ z2 = (3 / 4, 1 / 2) := by
  simp only [wmU2, Bool.false_eq_true, ite_false]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩, ?_⟩
  · rw [wm_cd_opt_iff (p := (2, 1)) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rw [wm_leontief_opt_iff (by norm_num) (p := (2, 1)) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rintro ⟨p1, p2⟩ z1 z2 ⟨hp1, hp2, hc1, hc2, ho1, ho2⟩
    rw [wm_cd_opt_iff (p := (p1, p2)) hp1 hp2 (by simp only; linarith)] at ho1
    rw [wm_leontief_opt_iff (by norm_num) (p := (p1, p2)) hp1 hp2
      (by simp only; linarith)] at ho2
    subst ho1 ho2
    have hD : 0 < 3 / 2 * p1 + p2 := by positivity
    have h1 : (p1 * 0 + p2 * 1) / (2 * p2) = 1 / 2 := by field_simp; ring
    have h2 : (p1 * 1 + p2 * 0) / (3 / 2 * p1 + p2) = 1 / 2 := by linarith
    rw [div_eq_iff hD.ne'] at h2
    have e : p2 = p1 / 2 := by linarith
    subst e
    refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> field_simp <;> ring

/-- **Example 23.B.2** (MWG, pp. 860-861; Figure 23.B.1). The Walrasian social choice function
`f(θ₂)` (the unique Walrasian equilibrium allocation for the announced profile) is not truthfully
implementable: when consumer 2's true type is `θ₂'` (`u₂ = xy`), announcing `θ₂''` gives him
`(3/4, 1/2)`, which he strictly prefers (`3/8 > 1/4`) to his truthful allocation `(1/2, 1/2)`. -/
theorem example_23_B_2 :
    (∀ p z1 z2, WmEq wmCD (wmU2 true) (0, 1) (1, 0) p z1 z2 → z2 = (1 / 2, 1 / 2)) ∧
      (∀ p z1 z2, WmEq wmCD (wmU2 false) (0, 1) (1, 0) p z1 z2 → z2 = (3 / 4, 1 / 2)) ∧
      wmU2 true (1 / 2, 1 / 2) < wmU2 true (3 / 4, 1 / 2) :=
  ⟨fun p z1 z2 h => (example_23_B_2_truthful.2 p z1 z2 h).2,
    fun p z1 z2 h => (example_23_B_2_misreport.2 p z1 z2 h).2,
    by simp only [wmU2, ite_true, wmCD]; norm_num⟩

/-- Local nonsatiation in the form used: adding `δ > 0` of both goods to a bundle `z ≥ 0` makes
the consumer strictly better off. -/
def WmLNS (u : ℝ × ℝ → ℝ) : Prop :=
  ∀ z : ℝ × ℝ, 0 ≤ z.1 → 0 ≤ z.2 → ∀ δ : ℝ, 0 < δ → u z < u (z.1 + δ, z.2 + δ)

/-- If `z'` is affordable or strictly cheaper and `u` is locally nonsatiated, an optimal bundle
`z` with `u(z') ≥ u(z)` forces `p · z' ≥ w`, and `u(z') > u(z)` forces `p · z' > w`. -/
theorem wm_cost_ge {u : ℝ × ℝ → ℝ} (hu : WmLNS u) {p : ℝ × ℝ} (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    {w : ℝ} {z z' : ℝ × ℝ} (hz : WmOpt u p w z) (h1 : 0 ≤ z'.1) (h2 : 0 ≤ z'.2) :
    (u z ≤ u z' → w ≤ p.1 * z'.1 + p.2 * z'.2) ∧
      (u z < u z' → w < p.1 * z'.1 + p.2 * z'.2) := by
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · by_contra hc
    rw [not_le] at hc
    set δ := (w - (p.1 * z'.1 + p.2 * z'.2)) / (p.1 + p.2) with hδ
    have hpp : 0 < p.1 + p.2 := by linarith
    have hδ0 : 0 < δ := div_pos (by linarith) hpp
    have hcost : p.1 * (z'.1 + δ) + p.2 * (z'.2 + δ) ≤ w := by
      have : δ * (p.1 + p.2) = w - (p.1 * z'.1 + p.2 * z'.2) := by
        rw [hδ]; field_simp
      nlinarith
    have := hz.2.2.2 (z'.1 + δ, z'.2 + δ) (by simp only; linarith) (by simp only; linarith)
      hcost
    have := hu z' h1 h2 δ hδ0
    linarith
  · by_contra hc
    rw [not_lt] at hc
    have := hz.2.2.2 z' h1 h2 hc
    linarith

/-- **Example 23.B.2** (MWG, p. 860), "this social choice function is ex post efficient": the
first welfare theorem for the two-consumer exchange economy with locally nonsatiated utilities.
A Walrasian equilibrium allocation is Pareto optimal: no feasible allocation makes one consumer
better off and the other strictly better off. -/
theorem wm_first_welfare {u1 u2 : ℝ × ℝ → ℝ} (hu1 : WmLNS u1) (hu2 : WmLNS u2)
    {ω1 ω2 p z1 z2 : ℝ × ℝ} (h : WmEq u1 u2 ω1 ω2 p z1 z2) :
    ¬∃ y1 y2 : ℝ × ℝ, 0 ≤ y1.1 ∧ 0 ≤ y1.2 ∧ 0 ≤ y2.1 ∧ 0 ≤ y2.2 ∧
      y1.1 + y2.1 ≤ ω1.1 + ω2.1 ∧ y1.2 + y2.2 ≤ ω1.2 + ω2.2 ∧
      u1 z1 ≤ u1 y1 ∧ u2 z2 ≤ u2 y2 ∧ (u1 z1 < u1 y1 ∨ u2 z2 < u2 y2) := by
  obtain ⟨hp1, hp2, -, -, ho1, ho2⟩ := h
  rintro ⟨y1, y2, a1, a2, b1, b2, c1, c2, d1, d2, hs⟩
  have k1 := wm_cost_ge hu1 hp1 hp2 ho1 a1 a2
  have k2 := wm_cost_ge hu2 hp1 hp2 ho2 b1 b2
  have f1 : p.1 * (y1.1 + y2.1) ≤ p.1 * (ω1.1 + ω2.1) := mul_le_mul_of_nonneg_left c1 hp1.le
  have f2 : p.2 * (y1.2 + y2.2) ≤ p.2 * (ω1.2 + ω2.2) := mul_le_mul_of_nonneg_left c2 hp2.le
  rcases hs with hs | hs
  · have := k1.2 hs
    have := k2.1 d2
    nlinarith
  · have := k1.1 d1
    have := k2.2 hs
    nlinarith

/-- `xy` is locally nonsatiated on `z ≥ 0`. -/
theorem wm_cd_lns : WmLNS wmCD := fun z h1 h2 δ hδ => by
  simp only [wmCD]; nlinarith [mul_pos hδ hδ]

/-- `min(x, βy)`, `β > 0`, is locally nonsatiated. -/
theorem wm_leontief_lns {β : ℝ} (hβ : 0 < β) : WmLNS (wmLeontief β) := fun z _ _ δ hδ => by
  simp only [wmLeontief]
  rcases le_total z.1 (β * z.2) with h | h
  · rw [min_eq_left h]
    refine lt_min (by linarith) ?_
    nlinarith
  · rw [min_eq_right h]
    refine lt_min (by linarith) ?_
    nlinarith

/-- **Example 23.B.2** (MWG, p. 860): the Walrasian social choice function is ex post efficient at
both announced profiles. -/
theorem example_23_B_2_efficient (b : Bool) {p z1 z2 : ℝ × ℝ}
    (h : WmEq wmCD (wmU2 b) (0, 1) (1, 0) p z1 z2) :
    ¬∃ y1 y2 : ℝ × ℝ, 0 ≤ y1.1 ∧ 0 ≤ y1.2 ∧ 0 ≤ y2.1 ∧ 0 ≤ y2.2 ∧
      y1.1 + y2.1 ≤ (0 : ℝ) + 1 ∧ y1.2 + y2.2 ≤ (1 : ℝ) + 0 ∧
      wmCD z1 ≤ wmCD y1 ∧ wmU2 b z2 ≤ wmU2 b y2 ∧
      (wmCD z1 < wmCD y1 ∨ wmU2 b z2 < wmU2 b y2) := by
  have hu2 : WmLNS (wmU2 b) := by
    cases b
    · simp only [wmU2, Bool.false_eq_true, ite_false]; exact wm_leontief_lns (by norm_num)
    · simp only [wmU2, ite_true]; exact wm_cd_lns
  exact wm_first_welfare wm_cd_lns hu2 h

end MWG.MechanismDesign
