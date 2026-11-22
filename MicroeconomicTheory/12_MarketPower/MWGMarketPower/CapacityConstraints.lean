/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.DifferentiatedProducts
import Mathlib.Analysis.Convex.Function

/-!
# Capacity constraints in price competition

MWG, Section 12.C, pp. 394-395, and Exercise 12.C.11 (p. 432).

Two firms with capacities `q₁, q₂` and constant unit cost `c` name prices. Demand `x(·)` is strictly
decreasing at every price where it is positive (`x p' < x p` whenever `p < p'` and `x p' > 0`).
Sales follow the rationing rule of Exercise 12.C.11 (the high-valuation consumers buy first):
for `p_j > p_i`, `x_i = min{q_i, x(p_i)}` and `x_j = min{q_j, max{x(p_j) − q_i, 0}}`; at equal
prices
`x_i = min{q_i, max{x(p)/2, x(p) − q_j}}` (`capSales`). `IsCapNE` is a pure strategy Nash
equilibrium. `p(·)` is the inverse demand (`x(p(Q)) = Q` for `Q > 0`), and `b_c(q)` a Cournot best
response with marginal cost `c` (`IsCournotBRc`).

* `capacity_bertrand_not_eqm`, `capacity_bertrand_not_eqm_three_quarters` (p. 394): with
  `0 < q̄ < x(c)` (in particular `q̄ = ¾x(c)`), `p₁ = p₂ = c` is not an equilibrium.
* `capacity_assured_sales` (pp. 394-395): any `p₁ ∈ (c, p(q̄))` gives firm 1 strictly positive sales
  whatever firm 2 charges; when firm 2 charges less they are `min{q̄, x(p₁) − q̄}`, which is
  `x(p₁) − q̄` when `x(p₁) ≤ 2q̄` (correction 23).
* `exercise_12_C_11a`: with `x` concave where positive, `q₁ < b_c(q₂)` and `q₂ < b_c(q₁)`, the
  prices `p₁ = p₂ = p(q₁ + q₂)` form a Nash equilibrium; `capacity_unique` (p. 395): with positive
  capacities and continuous demand it is the only one.
* `exercise_12_C_11b`: if `q₁ > b_c(q₂) > 0` (or symmetrically), both capacities are positive and
  demand is continuous, no pure strategy equilibrium exists. As printed (b) is false:
  `exercise_12_C_11b_counterexample_zero_capacity` (`q₂ = 0`) and
  `exercise_12_C_11b_counterexample_zero_br` (`b_c(q₂) = 0`) have equilibria (correction 24).

The Kreps-Scheinkman theorem (p. 395) is cited by MWG without proof and is not formalized.
-/

namespace MWG.MarketPower

open Filter Topology

/-- **Sales under capacity constraints** (MWG, Exercise 12.C.11, p. 432): the sales of a firm
with capacity `qi` charging `pi` when its rival has capacity `qj` and charges `pj`. -/
noncomputable def capSales (x : ℝ → ℝ) (qi qj pi pj : ℝ) : ℝ :=
  if pi < pj then min qi (x pi)
  else if pj < pi then min qi (max (x pi - qj) 0) else min qi (max (x pi / 2) (x pi - qj))

/-- The profit `(p_i − c)x_i(p_i, p_j)` of a capacity-constrained firm. -/
noncomputable def capProfit (x : ℝ → ℝ) (c qi qj pi pj : ℝ) : ℝ :=
  (pi - c) * capSales x qi qj pi pj

/-- A pure strategy Nash equilibrium of the capacity-constrained pricing game. -/
def IsCapNE (x : ℝ → ℝ) (c q1 q2 p1 p2 : ℝ) : Prop :=
  (∀ p, capProfit x c q1 q2 p p2 ≤ capProfit x c q1 q2 p1 p2) ∧
    ∀ p, capProfit x c q2 q1 p p1 ≤ capProfit x c q2 q1 p2 p1

/-- `b` is a Cournot best response to the rival output `r` for a firm with constant marginal cost
`c` facing the inverse demand `P` (MWG, Exercise 12.C.11: `b_c(·)`). -/
def IsCournotBRc (P : ℝ → ℝ) (c r b : ℝ) : Prop :=
  0 ≤ b ∧ ∀ y, 0 ≤ y → (P (y + r) - c) * y ≤ (P (b + r) - c) * b

theorem capSales_lt {x : ℝ → ℝ} {qi qj pi pj : ℝ} (h : pi < pj) :
    capSales x qi qj pi pj = min qi (x pi) := by
  unfold capSales; simp only [h, ↓reduceIte]

theorem capSales_gt {x : ℝ → ℝ} {qi qj pi pj : ℝ} (h : pj < pi) :
    capSales x qi qj pi pj = min qi (max (x pi - qj) 0) := by
  unfold capSales; simp only [not_lt.2 h.le, h, ↓reduceIte]

theorem capSales_eq {x : ℝ → ℝ} {qi qj p : ℝ} :
    capSales x qi qj p p = min qi (max (x p / 2) (x p - qj)) := by
  unfold capSales; simp only [lt_irrefl, ↓reduceIte]

theorem capSales_nonneg {x : ℝ → ℝ} (hnn : ∀ p, 0 ≤ x p) {qi qj pi pj : ℝ} (hqi : 0 ≤ qi) :
    0 ≤ capSales x qi qj pi pj := by
  unfold capSales
  split_ifs
  · exact le_min hqi (hnn _)
  · exact le_min hqi (le_max_right _ _)
  · exact le_min hqi (le_trans (div_nonneg (hnn _) zero_le_two) (le_max_left _ _))

variable {x P : ℝ → ℝ}

/-- The inverse demand inverts `x` where demand is positive. -/
theorem cap_P_x (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hP : ∀ Q, 0 < Q → x (P Q) = Q) {p : ℝ} (hp : 0 < x p) : P (x p) = p := by
  have h := hP _ hp
  rcases lt_trichotomy (P (x p)) p with h1 | h1 | h1
  · have := hanti _ _ h1 hp; linarith
  · exact h1
  · have := hanti _ _ h1 (by rw [h]; exact hp); linarith

/-- The inverse demand is strictly decreasing on positive quantities. -/
theorem cap_P_anti (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hP : ∀ Q, 0 < Q → x (P Q) = Q) {Q1 Q2 : ℝ} (hQ1 : 0 < Q1) (h12 : Q1 < Q2) :
    P Q2 < P Q1 := by
  have e1 := hP Q1 hQ1
  have e2 := hP Q2 (by linarith)
  rcases lt_or_ge (P Q2) (P Q1) with h | h
  · exact h
  · exfalso
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h'] at e1; linarith
    · have := hanti _ _ h' (by rw [e2]; linarith); linarith

/-- If demand is concave where positive, the inverse demand is concave on positive quantities
(stated for three points `Q₁ < Q < Q₂`). -/
theorem cap_P_concave (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {Q1 Q Q2 : ℝ}
    (hQ1 : 0 < Q1) (h1 : Q1 < Q) (h2 : Q < Q2) :
    (Q2 - Q) * P Q1 + (Q - Q1) * P Q2 ≤ (Q2 - Q1) * P Q := by
  have hd : 0 < Q2 - Q1 := by linarith
  have ha : 0 ≤ (Q2 - Q) / (Q2 - Q1) := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (Q - Q1) / (Q2 - Q1) := div_nonneg (by linarith) hd.le
  have hab : (Q2 - Q) / (Q2 - Q1) + (Q - Q1) / (Q2 - Q1) = 1 := by field_simp; ring
  have m1 : P Q1 ∈ {p | 0 < x p} := by change 0 < x (P Q1); rw [hP Q1 hQ1]; exact hQ1
  have m2 : P Q2 ∈ {p | 0 < x p} := by
    change 0 < x (P Q2); rw [hP Q2 (by linarith)]; linarith
  have hc := hconc.2 m1 m2 ha hb hab
  simp only [smul_eq_mul] at hc
  rw [hP Q1 hQ1, hP Q2 (by linarith)] at hc
  have hQ : (Q2 - Q) / (Q2 - Q1) * Q1 + (Q - Q1) / (Q2 - Q1) * Q2 = Q := by field_simp; ring
  rw [hQ] at hc
  have hr : (Q2 - Q) / (Q2 - Q1) * P Q1 + (Q - Q1) / (Q2 - Q1) * P Q2 ≤ P Q := by
    by_contra hlt
    push Not at hlt
    have := hanti _ _ hlt (by linarith)
    rw [hP Q (by linarith)] at this
    linarith
  have e : (Q2 - Q1) * ((Q2 - Q) / (Q2 - Q1) * P Q1 + (Q - Q1) / (Q2 - Q1) * P Q2) =
      (Q2 - Q) * P Q1 + (Q - Q1) * P Q2 := by field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left hr hd.le

/-- Strict concavity of the Cournot profit `π(y) = (p(y + r) − c)y` at three outputs
`0 < u < w < z`. -/
theorem cap_pi_three (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c r u w z : ℝ}
    (hr : 0 ≤ r) (hu : 0 < u) (huw : u < w) (hwz : w < z) :
    (z - w) * ((P (u + r) - c) * u) + (w - u) * ((P (z + r) - c) * z) <
      (z - u) * ((P (w + r) - c) * w) := by
  have hc := cap_P_concave hanti hconc hP (Q1 := u + r) (Q := w + r) (Q2 := z + r)
    (by linarith) (by linarith) (by linarith)
  have hm : P (z + r) < P (u + r) := cap_P_anti hanti hP (by linarith) (by linarith)
  have e1 : z + r - (w + r) = z - w := by ring
  have e2 : w + r - (u + r) = w - u := by ring
  have e3 : z + r - (u + r) = z - u := by ring
  rw [e1, e2, e3] at hc
  nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ w by linarith),
    mul_pos (mul_pos (show 0 < z - w by linarith) (show 0 < w - u by linarith))
      (show 0 < P (u + r) - P (z + r) by linarith)]

/-- A positive Cournot best response earns a strictly positive profit. -/
theorem cap_pi_pos (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c r b : ℝ} (hr : 0 ≤ r) (hb : IsCournotBRc P c r b)
    (hb0 : 0 < b) : 0 < (P (b + r) - c) * b := by
  have h := hb.2 (b / 2) (by linarith)
  have hm : P (b + r) < P (b / 2 + r) := cap_P_anti hanti hP (by linarith) (by linarith)
  nlinarith

/-! ### The claims of pp. 394-395 -/

/-- **Capacity constraints** (MWG, p. 394). If `0 < q̄ < x(c)` and demand is continuous, the
Bertrand outcome `p₁ = p₂ = c` is not an equilibrium: firm 1 earns `0` there but earns a strictly
positive profit at some price slightly above `c`. -/
theorem capacity_bertrand_not_eqm (hcont : Continuous x) {c qbar : ℝ} (hq : 0 < qbar)
    (hqx : qbar < x c) :
    capProfit x c qbar qbar c c = 0 ∧ (∃ p, 0 < capProfit x c qbar qbar p c) ∧
      ¬ IsCapNE x c qbar qbar c c := by
  have h0 : capProfit x c qbar qbar c c = 0 := by unfold capProfit; ring
  have hev : ∀ᶠ p in 𝓝[>] c, qbar < x p :=
    nhdsWithin_le_nhds (hcont.continuousAt.eventually (lt_mem_nhds hqx))
  obtain ⟨p, hp, hpc⟩ := (hev.and self_mem_nhdsWithin).exists
  have hpos : 0 < capProfit x c qbar qbar p c := by
    unfold capProfit
    rw [capSales_gt hpc]
    apply mul_pos (sub_pos.2 hpc)
    exact lt_min hq (lt_max_of_lt_left (by linarith))
  refine ⟨h0, ⟨p, hpos⟩, fun hne => ?_⟩
  have := hne.1 p
  linarith

/-- **Capacity constraints** (MWG, p. 394), with the book's capacity `q̄ = ¾x(c)` and
`x(c) > 0`. -/
theorem capacity_bertrand_not_eqm_three_quarters (hcont : Continuous x) {c : ℝ} (hxc : 0 < x c) :
    ¬ IsCapNE x c (3 / 4 * x c) (3 / 4 * x c) c c :=
  (capacity_bertrand_not_eqm hcont (by positivity) (by linarith)).2.2

/-- **Capacity constraints** (MWG, pp. 394-395). If `0 < q̄ < x(c)` and `x(p(q̄)) = q̄`, then
`c < p(q̄)`, and any price `p₁ ∈ (c, p(q̄))` gives firm 1 sales of at least
`min{q̄, x(p₁) − q̄} > 0` whatever firm 2 charges; when firm 2 charges less, the sales are exactly
`min{q̄, x(p₁) − q̄}`, which equals `x(p₁) − q̄` when `x(p₁) ≤ 2q̄`. -/
theorem capacity_assured_sales
    (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p) {c qbar phat : ℝ} (hq : 0 < qbar)
    (hqx : qbar < x c) (hphat : x phat = qbar) :
    c < phat ∧ ∀ p1, c < p1 → p1 < phat →
      0 < min qbar (x p1 - qbar) ∧ (∀ p2, min qbar (x p1 - qbar) ≤ capSales x qbar qbar p1 p2) ∧
      (∀ p2, p2 < p1 → capSales x qbar qbar p1 p2 = min qbar (x p1 - qbar)) ∧
      (x p1 ≤ 2 * qbar → min qbar (x p1 - qbar) = x p1 - qbar) := by
  have hcp : c < phat := by
    rcases lt_trichotomy c phat with h | h | h
    · exact h
    · rw [h] at hqx; linarith
    · have := hanti _ _ h (by linarith); linarith
  refine ⟨hcp, fun p1 _ hp1 => ?_⟩
  have hx1 : qbar < x p1 := by have := hanti _ _ hp1 (by linarith); linarith
  have hpos : 0 < min qbar (x p1 - qbar) := lt_min hq (by linarith)
  refine ⟨hpos, fun p2 => ?_, fun p2 h2 => ?_, fun h => min_eq_right (by linarith)⟩
  · rcases lt_trichotomy p1 p2 with h | h | h
    · rw [capSales_lt h]; exact min_le_min le_rfl (by linarith)
    · rw [← h, capSales_eq]; exact min_le_min le_rfl (le_max_right _ _)
    · rw [capSales_gt h, max_eq_left (by linarith)]
  · rw [capSales_gt h2, max_eq_left (by linarith)]

/-! ### Exercise 12.C.11(a) -/

/-- One firm's half of Exercise 12.C.11(a): if `q₁ < b` for a Cournot best response `b` to `q₂`,
then `p(q₁ + q₂) > c` and firm 1 cannot gain by deviating from `p(q₁ + q₂)` when firm 2 charges
`p(q₁ + q₂)`. -/
theorem cap_eqm_side (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c q1 q2 b : ℝ}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hs : 0 < q1 + q2) (hb : IsCournotBRc P c q2 b)
    (hqb : q1 < b) :
    c < P (q1 + q2) ∧
      ∀ p, capProfit x c q1 q2 p (P (q1 + q2)) ≤
        capProfit x c q1 q2 (P (q1 + q2)) (P (q1 + q2)) := by
  have hb0 : 0 < b := by linarith
  have hpib := cap_pi_pos hanti hP hq2 hb hb0
  have hcb : c < P (b + q2) := by
    by_contra h; push Not at h
    have : (P (b + q2) - c) * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hb0.le
    linarith
  have hanti' : P (b + q2) < P (q1 + q2) := cap_P_anti hanti hP hs (by linarith)
  have hcs : c < P (q1 + q2) := by linarith
  have hxs : x (P (q1 + q2)) = q1 + q2 := hP _ hs
  have hcur : capProfit x c q1 q2 (P (q1 + q2)) (P (q1 + q2)) = (P (q1 + q2) - c) * q1 := by
    unfold capProfit
    rw [capSales_eq, hxs, min_eq_left (le_max_of_le_right (by linarith))]
  refine ⟨hcs, fun p => ?_⟩
  rw [hcur]
  rcases lt_trichotomy p (P (q1 + q2)) with h | h | h
  · unfold capProfit
    rw [capSales_lt h]
    have := hanti _ _ h (by rw [hxs]; exact hs)
    rw [hxs] at this
    rw [min_eq_left (by linarith)]
    exact mul_le_mul_of_nonneg_right (by linarith) hq1
  · rw [h, ← hcur]
  · unfold capProfit
    rw [capSales_gt h]
    by_cases hx : x p ≤ q2
    · rw [max_eq_right (by linarith), min_eq_right hq1, mul_zero]
      exact mul_nonneg (by linarith) hq1
    · push Not at hx
      have hxp : x p < q1 + q2 := by have := hanti _ _ h (by linarith); linarith
      rw [max_eq_left (by linarith), min_eq_right (by linarith)]
      have hPp : P (x p - q2 + q2) = p := by
        rw [sub_add_cancel]; exact cap_P_x hanti hP (by linarith)
      have h3 := cap_pi_three hanti hconc hP (c := c) hq2 (u := x p - q2) (w := q1) (z := b)
        (by linarith) (by linarith) hqb
      have hbr := hb.2 (x p - q2) (by linarith)
      rw [hPp] at h3 hbr
      nlinarith

/-- **Exercise 12.C.11(a)** (MWG, p. 432). Suppose demand is strictly decreasing where positive
and concave where positive, `p(·)` is its inverse, and the capacities `q₁, q₂ ≥ 0` (not both zero)
satisfy `q₁ < b_c(q₂)` and `q₂ < b_c(q₁)`. Then `p₁* = p₂* = p(q₁ + q₂)` is a Nash equilibrium of
the capacity-constrained pricing game, and it lies above cost. -/
theorem exercise_12_C_11a (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c q1 q2 b1 b2 : ℝ}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hs : 0 < q1 + q2) (hb1 : IsCournotBRc P c q2 b1)
    (hqb1 : q1 < b1) (hb2 : IsCournotBRc P c q1 b2) (hqb2 : q2 < b2) :
    c < P (q1 + q2) ∧ IsCapNE x c q1 q2 (P (q1 + q2)) (P (q1 + q2)) := by
  obtain ⟨hc, h1⟩ := cap_eqm_side hanti hconc hP hq1 hq2 hs hb1 hqb1
  obtain ⟨_, h2⟩ := cap_eqm_side hanti hconc hP hq2 hq1 (by linarith) hb2 hqb2
  rw [add_comm q2 q1] at h2
  exact ⟨hc, h1, h2⟩

/-! ### Equilibria with positive profit -/

/-- Undercutting at equal prices: if `0 < x(p₀) < q_i + q_j`, `q_j > 0`, `x(p₀)/2 < q_i` and
`p₀ > c`, firm `i` gains by a small price cut. -/
theorem cap_undercut (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p) {c qi qj p0 : ℝ}
    (hqj : 0 < qj) (hX : 0 < x p0) (hXq : x p0 < qi + qj) (hhalf : x p0 / 2 < qi)
    (hp0 : c < p0) : ∃ p, capProfit x c qi qj p0 p0 < capProfit x c qi qj p p0 := by
  set X := x p0 with hXdef
  set M := max (X / 2) (X - qj) with hM
  have hMX : M < X := max_lt (by linarith) (by linarith)
  have hMq : M < qi := max_lt hhalf (by linarith)
  set m := min qi X with hm
  have hmpos : 0 < m := lt_min (by linarith) hX
  have hMm : M < m := lt_min hMq hMX
  have hMpos : 0 < M := lt_max_of_lt_left (by linarith)
  have hcur : capProfit x c qi qj p0 p0 = (p0 - c) * M := by
    unfold capProfit; rw [capSales_eq, ← hXdef, ← hM, min_eq_right hMq.le]
  set p' := c + (p0 - c) * (m + M) / (2 * m) with hp'
  have hp'e : p' - c = (p0 - c) * (m + M) / (2 * m) := by rw [hp']; ring
  have hp'c : 0 < p' - c := by
    rw [hp'e]
    exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hp'p : p' < p0 := by
    rw [hp']
    have : (p0 - c) * (m + M) / (2 * m) < p0 - c := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  have hxp' : X < x p' := hanti _ _ hp'p hX
  refine ⟨p', ?_⟩
  rw [hcur]
  unfold capProfit
  rw [capSales_lt hp'p]
  have hmin : m ≤ min qi (x p') := min_le_min le_rfl hxp'.le
  have hval : (p' - c) * m = (p0 - c) * (m + M) / 2 := by rw [hp']; field_simp; ring
  have : (p' - c) * m ≤ (p' - c) * min qi (x p') := mul_le_mul_of_nonneg_left hmin hp'c.le
  nlinarith

/-- In a pure Nash equilibrium of the capacity game in which firm 1 earns a strictly positive
profit (positive capacities, continuous nonnegative demand), the two prices are equal and demand
at that price equals total capacity. -/
theorem capNE_eq (hcont : Continuous x) (hnn : ∀ p, 0 ≤ x p)
    (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p) {c q1 q2 p1 p2 : ℝ} (hq1 : 0 < q1)
    (hq2 : 0 < q2) (hne : IsCapNE x c q1 q2 p1 p2) (hpos : 0 < capProfit x c q1 q2 p1 p2) :
    p1 = p2 ∧ x p1 = q1 + q2 := by
  have hs1nn : 0 ≤ capSales x q1 q2 p1 p2 := capSales_nonneg hnn hq1.le
  have hboth : c < p1 ∧ 0 < capSales x q1 q2 p1 p2 := by
    unfold capProfit at hpos
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with h | h
    · exact ⟨by linarith [h.1], h.2⟩
    · linarith [h.2]
  obtain ⟨hp1c, hs1⟩ := hboth
  rcases lt_trichotomy p1 p2 with h | h | h
  · exfalso
    rw [capSales_lt h] at hs1
    have hx1 : 0 < x p1 := (lt_min_iff.1 hs1).2
    by_cases hx : q1 < x p1
    · have hev : ∀ᶠ p in 𝓝[>] p1, q1 < x p ∧ p < p2 :=
        nhdsWithin_le_nhds ((hcont.continuousAt.eventually (lt_mem_nhds hx)).and
          (Iio_mem_nhds h))
      obtain ⟨p, ⟨hxp, hp2⟩, hp1⟩ := (hev.and self_mem_nhdsWithin).exists
      have := hne.1 p
      unfold capProfit at this
      rw [capSales_lt hp2, capSales_lt h, min_eq_left hxp.le, min_eq_left hx.le] at this
      have hp1' : p1 < p := hp1
      nlinarith
    · push Not at hx
      have hs2 : capSales x q2 q1 p2 p1 = 0 := by
        rw [capSales_gt h]
        have : x p2 ≤ q1 := by
          rcases lt_or_eq_of_le (hnn p2) with h0 | h0
          · have := hanti _ _ h h0; linarith
          · linarith
        rw [max_eq_right (by linarith), min_eq_right hq2.le]
      have hdev := hne.2 ((c + p1) / 2)
      unfold capProfit at hdev
      rw [hs2, mul_zero, capSales_lt (show (c + p1) / 2 < p1 by linarith)] at hdev
      have hxd : x p1 < x ((c + p1) / 2) := hanti _ _ (by linarith) hx1
      have : 0 < ((c + p1) / 2 - c) * min q2 (x ((c + p1) / 2)) :=
        mul_pos (by linarith) (lt_min hq2 (by linarith))
      linarith
  · refine ⟨h, ?_⟩
    rw [← h, capSales_eq] at hs1
    have hX : 0 < x p1 := by
      have h' := (lt_min_iff.1 hs1).2
      rcases lt_max_iff.1 h' with h'' | h''
      · linarith
      · linarith
    rcases lt_trichotomy (x p1) (q1 + q2) with hX' | hX' | hX'
    · exfalso
      rcases lt_or_ge (x p1 / 2) q1 with hh | hh
      · obtain ⟨p, hp⟩ := cap_undercut hanti hq2 hX hX' hh hp1c
        have := hne.1 p
        rw [← h] at this
        linarith
      · obtain ⟨p, hp⟩ := cap_undercut hanti (qi := q2) hq1 hX (by linarith) (by linarith) hp1c
        have := hne.2 p
        rw [← h] at this
        linarith
    · exact hX'
    · exfalso
      have hev : ∀ᶠ p in 𝓝[>] p1, q1 + q2 < x p :=
        nhdsWithin_le_nhds (hcont.continuousAt.eventually (lt_mem_nhds hX'))
      obtain ⟨p, hxp, hp1⟩ := (hev.and self_mem_nhdsWithin).exists
      have hp1' : p1 < p := hp1
      have := hne.1 p
      unfold capProfit at this
      rw [← h, capSales_gt hp1', capSales_eq, max_eq_left (by linarith),
        min_eq_left (show q1 ≤ x p - q2 by linarith),
        min_eq_left (le_max_of_le_right (show q1 ≤ x p1 - q2 by linarith))] at this
      nlinarith
  · exfalso
    rw [capSales_gt h] at hs1
    have hx1 : q2 < x p1 := by
      have h' := (lt_min_iff.1 hs1).2
      rcases lt_max_iff.1 h' with h'' | h''
      · linarith
      · linarith
    have hx2 : x p1 < x p2 := hanti _ _ h (by linarith)
    have hdev := hne.2 ((p2 + p1) / 2)
    unfold capProfit at hdev
    have hxm : x p1 < x ((p2 + p1) / 2) := hanti _ _ (by linarith) (by linarith)
    rw [capSales_lt h, capSales_lt (show (p2 + p1) / 2 < p1 by linarith),
      min_eq_left (show q2 ≤ x p2 by linarith),
      min_eq_left (show q2 ≤ x ((p2 + p1) / 2) by linarith)] at hdev
    nlinarith

/-- **Uniqueness** (MWG, p. 395: "the unique equilibrium of the pricing subgame involves both
firms setting their prices equal to `p(q̄₁ + q̄₂)`"). Under the hypotheses of Exercise 12.C.11(a),
with positive capacities and continuous nonnegative demand, every pure strategy Nash equilibrium
has `p₁ = p₂ = p(q₁ + q₂)`. -/
theorem capacity_unique (hcont : Continuous x) (hnn : ∀ p, 0 ≤ x p)
    (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c q1 q2 b1 : ℝ}
    (hq1 : 0 < q1) (hq2 : 0 < q2) (hb1 : IsCournotBRc P c q2 b1) (hqb1 : q1 < b1) {p1 p2 : ℝ}
    (hne : IsCapNE x c q1 q2 p1 p2) : p1 = P (q1 + q2) ∧ p2 = P (q1 + q2) := by
  obtain ⟨hc, _⟩ := cap_eqm_side hanti hconc hP hq1.le hq2.le (by linarith) hb1 hqb1
  have hxs : x (P (q1 + q2)) = q1 + q2 := hP _ (by linarith)
  -- firm 1 can sell `q₁` at `p(q₁ + q₂)` whatever firm 2 charges
  have hguar : (P (q1 + q2) - c) * q1 ≤ capProfit x c q1 q2 (P (q1 + q2)) p2 := by
    unfold capProfit
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rcases lt_trichotomy (P (q1 + q2)) p2 with h | h | h
    · rw [capSales_lt h, hxs, min_eq_left (by linarith)]
    · rw [← h, capSales_eq, hxs, min_eq_left (le_max_of_le_right (by linarith))]
    · rw [capSales_gt h, hxs, max_eq_left (by linarith), min_eq_left (by linarith)]
  have hpos : 0 < capProfit x c q1 q2 p1 p2 :=
    lt_of_lt_of_le (mul_pos (by linarith) hq1) (hguar.trans (hne.1 _))
  obtain ⟨h12, hx⟩ := capNE_eq hcont hnn hanti hq1 hq2 hne hpos
  have := cap_P_x hanti hP (p := p1) (by rw [hx]; linarith)
  rw [hx] at this
  exact ⟨this.symm, h12 ▸ this.symm⟩

/-! ### Exercise 12.C.11(b) -/

/-- One firm's half of Exercise 12.C.11(b): if `0 < b < q₁` for a Cournot best response `b` to
`q₂ > 0`, there is no pure strategy equilibrium. -/
theorem cap_no_eqm_side (hcont : Continuous x) (hnn : ∀ p, 0 ≤ x p)
    (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c q1 q2 b : ℝ}
    (hq2 : 0 < q2) (hb : IsCournotBRc P c q2 b) (hb0 : 0 < b) (hbq : b < q1) {p1 p2 : ℝ}
    (hne : IsCapNE x c q1 q2 p1 p2) : False := by
  have hq1 : 0 < q1 := by linarith
  have hpib := cap_pi_pos hanti hP hq2.le hb hb0
  have hxb : x (P (b + q2)) = b + q2 := hP _ (by linarith)
  -- firm 1 can assure itself `π(b) > 0` by charging `p(b + q₂)`
  have hguar : (P (b + q2) - c) * b ≤ capProfit x c q1 q2 (P (b + q2)) p2 := by
    unfold capProfit
    have hcb : 0 < P (b + q2) - c := by
      by_contra h; push Not at h
      have : (P (b + q2) - c) * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hb0.le
      linarith
    apply mul_le_mul_of_nonneg_left _ hcb.le
    rcases lt_trichotomy (P (b + q2)) p2 with h | h | h
    · rw [capSales_lt h, hxb]; exact le_min hbq.le (by linarith)
    · rw [← h, capSales_eq, hxb]; exact le_min hbq.le (le_max_of_le_right (by linarith))
    · rw [capSales_gt h, hxb, show b + q2 - q2 = b by ring, max_eq_left hb0.le,
        min_eq_right hbq.le]
  have hpos : 0 < capProfit x c q1 q2 p1 p2 := lt_of_lt_of_le hpib (hguar.trans (hne.1 _))
  obtain ⟨h12, hx⟩ := capNE_eq hcont hnn hanti hq1 hq2 hne hpos
  subst h12
  have hp1 : P (q1 + q2) = p1 := by rw [← hx]; exact cap_P_x hanti hP (by rw [hx]; linarith)
  -- raising the price to `p(y + q₂)`, `y = (b + q₁)/2`, sells `y` and earns `π(y) > π(q₁)`
  set y := (b + q1) / 2 with hy
  have hpy : P (q1 + q2) < P (y + q2) := cap_P_anti hanti hP (by linarith) (by linarith)
  have hxy : x (P (y + q2)) = y + q2 := hP _ (by linarith)
  have hdev := hne.1 (P (y + q2))
  unfold capProfit at hdev
  rw [capSales_gt (show p1 < P (y + q2) by rw [← hp1]; exact hpy), hxy, capSales_eq, hx,
    show y + q2 - q2 = y by ring, max_eq_left (by linarith), min_eq_right (by linarith),
    min_eq_left (le_max_of_le_right (by linarith))] at hdev
  have h3 := cap_pi_three hanti hconc hP (c := c) hq2.le (u := b) (w := y) (z := q1) hb0
    (by linarith) (by linarith)
  have hbr := hb.2 q1 hq1.le
  rw [hp1] at h3 hbr
  nlinarith

/-- **Exercise 12.C.11(b)** (MWG, p. 432), corrected. With positive capacities, continuous
nonnegative demand that is strictly decreasing and concave where positive, and inverse demand
`p(·)`: if `q₁ > b_c(q₂) > 0` or `q₂ > b_c(q₁) > 0`, no pure strategy Nash equilibrium exists. -/
theorem exercise_12_C_11b (hcont : Continuous x) (hnn : ∀ p, 0 ≤ x p)
    (hanti : ∀ p p', p < p' → 0 < x p' → x p' < x p)
    (hconc : ConcaveOn ℝ {p | 0 < x p} x) (hP : ∀ Q, 0 < Q → x (P Q) = Q) {c q1 q2 : ℝ}
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (h : (∃ b, IsCournotBRc P c q2 b ∧ 0 < b ∧ b < q1) ∨
      ∃ b, IsCournotBRc P c q1 b ∧ 0 < b ∧ b < q2) :
    ¬ ∃ p1 p2, IsCapNE x c q1 q2 p1 p2 := by
  rintro ⟨p1, p2, hne⟩
  rcases h with ⟨b, hb, hb0, hbq⟩ | ⟨b, hb, hb0, hbq⟩
  · exact cap_no_eqm_side hcont hnn hanti hconc hP hq2 hb hb0 hbq hne
  · exact cap_no_eqm_side hcont hnn hanti hconc hP hq1 hb hb0 hbq ⟨hne.2, hne.1⟩

/-! ### The linear instance and the counterexamples -/

/-- The demand `x(p) = max{0, 1 − p}`. -/
noncomputable def capDemandEx (p : ℝ) : ℝ := max 0 (1 - p)

theorem capDemandEx_cont : Continuous capDemandEx :=
  continuous_const.max (continuous_const.sub continuous_id)

theorem capDemandEx_nonneg (p : ℝ) : 0 ≤ capDemandEx p := le_max_left _ _

theorem capDemandEx_anti :
    ∀ p p', p < p' → 0 < capDemandEx p' → capDemandEx p' < capDemandEx p := by
  intro p p' h h'
  unfold capDemandEx at *
  have : 0 < 1 - p' := by
    rcases lt_max_iff.1 h' with h'' | h''
    · exact absurd h'' (lt_irrefl 0)
    · exact h''
  rw [max_eq_right this.le, max_eq_right (by linarith)]; linarith

theorem capDemandEx_concave : ConcaveOn ℝ {p | 0 < capDemandEx p} capDemandEx := by
  have hs : {p | 0 < capDemandEx p} = Set.Iio 1 := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, capDemandEx, lt_max_iff, lt_irrefl, false_or]
    constructor <;> intro h <;> linarith
  rw [hs]
  refine ⟨convex_Iio 1, fun a ha b hb u v hu hv huv => ?_⟩
  simp only [Set.mem_Iio] at ha hb
  simp only [smul_eq_mul, capDemandEx]
  have : u * a + v * b ≤ 1 := by nlinarith
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  nlinarith

theorem capDemandEx_inv : ∀ Q, 0 < Q → capDemandEx ((fun Q => 1 - Q) Q) = Q := by
  intro Q hQ
  simp only [capDemandEx, sub_sub_cancel, max_eq_right hQ.le]

/-- The hypotheses of Exercise 12.C.11(a) and of `capacity_unique` are satisfiable: demand
`max{0, 1 − p}`, `c = 0`, `q₁ = q₂ = 1/4 < b_c(1/4) = 3/8`. -/
theorem exercise_12_C_11a_instance :
    IsCournotBRc (fun Q => 1 - Q) 0 (1 / 4) (3 / 8) ∧ (1 / 4 : ℝ) < 3 / 8 ∧
      IsCapNE capDemandEx 0 (1 / 4) (1 / 4) (1 / 2) (1 / 2) := by
  have hbr : IsCournotBRc (fun Q => 1 - Q) 0 (1 / 4) (3 / 8) :=
    ⟨by norm_num, fun y _ => by nlinarith [sq_nonneg (y - 3 / 8)]⟩
  refine ⟨hbr, by norm_num, ?_⟩
  have h := (exercise_12_C_11a capDemandEx_anti capDemandEx_concave capDemandEx_inv
    (by norm_num) (by norm_num) (by norm_num) hbr (by norm_num) hbr (by norm_num)).2
  convert h using 2 <;> norm_num

/-- The hypotheses of the corrected Exercise 12.C.11(b) are satisfiable: demand `max{0, 1 − p}`,
`c = 0`, `q₁ = 1/2 > b_c(1/4) = 3/8 > 0`, `q₂ = 1/4`; there is no pure equilibrium. -/
theorem exercise_12_C_11b_instance :
    IsCournotBRc (fun Q => 1 - Q) 0 (1 / 4) (3 / 8) ∧
      ¬ ∃ p1 p2, IsCapNE capDemandEx 0 (1 / 2) (1 / 4) p1 p2 := by
  have hbr : IsCournotBRc (fun Q => 1 - Q) 0 (1 / 4) (3 / 8) :=
    ⟨by norm_num, fun y _ => by nlinarith [sq_nonneg (y - 3 / 8)]⟩
  exact ⟨hbr, exercise_12_C_11b capDemandEx_cont capDemandEx_nonneg capDemandEx_anti
    capDemandEx_concave capDemandEx_inv (by norm_num) (by norm_num)
    (Or.inl ⟨3 / 8, hbr, by norm_num, by norm_num⟩)⟩

/-- **Exercise 12.C.11(b)** (MWG, p. 432): false as printed when a capacity is zero. With
`x(p) = max{0, 1 − p}`, `c = 0`, `q₁ = 1 > b_c(0) = 1/2`, `q₂ = 0`, the prices
`p₁ = p₂ = 1/2` form a Nash equilibrium (firm 1 is an unconstrained monopolist). -/
theorem exercise_12_C_11b_counterexample_zero_capacity :
    IsCournotBRc (fun Q => 1 - Q) 0 0 (1 / 2) ∧ (1 / 2 : ℝ) < 1 ∧
      IsCapNE capDemandEx 0 1 0 (1 / 2) (1 / 2) := by
  refine ⟨⟨by norm_num, fun y _ => by nlinarith [sq_nonneg (y - 1 / 2)]⟩, by norm_num, ?_, ?_⟩
  · intro p
    have hs : ∀ p', capSales capDemandEx 1 0 p' (1 / 2) = min 1 (capDemandEx p') := by
      intro p'
      have h0 := capDemandEx_nonneg p'
      rcases lt_trichotomy p' (1 / 2) with h | h | h
      · rw [capSales_lt h]
      · rw [h, capSales_eq, sub_zero,
          max_eq_right (by linarith [capDemandEx_nonneg (1 / 2)])]
      · rw [capSales_gt h, sub_zero, max_eq_left h0]
    unfold capProfit
    rw [hs, hs]
    have e : min 1 (capDemandEx (1 / 2)) = 1 / 2 := by norm_num [capDemandEx]
    rw [e]
    unfold capDemandEx
    rcases le_total (1 - p) 0 with h | h
    · rw [max_eq_left h, min_eq_right zero_le_one]; norm_num
    · rw [max_eq_right h]
      rcases le_total p 0 with h' | h'
      · have : 0 ≤ min 1 (1 - p) := le_min zero_le_one h
        nlinarith
      · rw [min_eq_right (by linarith)]; nlinarith [sq_nonneg (p - 1 / 2)]
  · intro p
    have hz : ∀ p', capSales capDemandEx 0 1 p' (1 / 2) = 0 := by
      intro p'
      have h0 := capDemandEx_nonneg p'
      rcases lt_trichotomy p' (1 / 2) with h | h | h
      · rw [capSales_lt h, min_eq_left h0]
      · rw [h, capSales_eq,
          min_eq_left (le_max_of_le_left (by linarith [capDemandEx_nonneg (1 / 2)]))]
      · rw [capSales_gt h, min_eq_left (le_max_right _ _)]
    unfold capProfit
    rw [hz, hz]
    simp

/-- **Exercise 12.C.11(b)** (MWG, p. 432): false as printed when `b_c(q₂) = 0`. With
`x(p) = max{0, 1 − p}`, `c = 1/2` and `q₁ = q₂ = 3/5`, `b_c(3/5) = 0 < q₁`, yet
`p₁ = p₂ = c` is a Nash equilibrium (no residual demand is profitable). -/
theorem exercise_12_C_11b_counterexample_zero_br :
    IsCournotBRc (fun Q => 1 - Q) (1 / 2) (3 / 5) 0 ∧
      IsCapNE capDemandEx (1 / 2) (3 / 5) (3 / 5) (1 / 2) (1 / 2) := by
  have hside : ∀ p, capProfit capDemandEx (1 / 2) (3 / 5) (3 / 5) p (1 / 2) ≤
      capProfit capDemandEx (1 / 2) (3 / 5) (3 / 5) (1 / 2) (1 / 2) := by
    intro p
    have hcur : capProfit capDemandEx (1 / 2) (3 / 5) (3 / 5) (1 / 2) (1 / 2) = 0 := by
      unfold capProfit; ring
    rw [hcur]
    unfold capProfit
    rcases lt_or_ge p (1 / 2) with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (capSales_nonneg capDemandEx_nonneg (by norm_num))
    · rcases eq_or_lt_of_le h with h' | h'
      · rw [← h']; ring_nf; exact le_rfl
      · rw [capSales_gt h']
        have : capDemandEx p ≤ 1 / 2 := by
          unfold capDemandEx; exact max_le (by norm_num) (by linarith)
        rw [max_eq_right (by linarith), min_eq_right (by norm_num), mul_zero]
  exact ⟨⟨le_rfl, fun y hy => by nlinarith⟩, hside, hside⟩

end MWG.MarketPower
