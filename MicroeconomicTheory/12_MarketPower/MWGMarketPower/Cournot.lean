/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Monopoly
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FinCases

/-!
# Quantity competition: the Cournot model

MWG, Section 12.C, pp. 389-393, and Exercises 12.C.6 and 12.C.7.

Firms `j ∈ ι` choose quantities `q_j ≥ 0`; the price is `p(Q)`, `Q = ∑ q_k`, and each firm has
unit cost `c`. Firm `j` earns `p(Q)q_j − cq_j` (`cournotProfit`); `IsCournotNE` is a pure strategy
Nash equilibrium. The inverse demand is differentiable within `[0, ∞)` with derivative `p'`.

* `cournot_foc`: conditions (12.C.2)-(12.C.4).
* `footnote_12_12`: with `p' < 0` and `p(0) > c` every equilibrium is interior (`q_j > 0`), for
  any number of firms (the argument of footnote 12, which MWG gives for two firms).
* `eq_12_C_5`, `eq_12_C_6`: summing the first-order conditions, `p'(Q)Q/J + p(Q) = c`.
* `proposition_12_C_2`: with two firms the equilibrium price lies strictly between `c` and the
  monopoly price.
* `cournot_competitive_limit`: `p(Q_J) → c` as `J → ∞` (p. 393); `eq_12_C_6_one`: with `J = 1`,
  (12.C.6) is the monopoly condition.
* `example_12_C_1`, `exercise_12_C_6`: the linear duopoly: best responses, the unique equilibrium
  `q_j = (a − c)/(3b)`, the price `(a + 2c)/3 ∈ (c, pᵐ)`, and the joint monopoly point
  `((a − c)/(4b), (a − c)/(4b))` as each firm's best point on the ray `q₁ = q₂`.
* `exercise_12_C_7`: the linear model with `J` firms.
-/

namespace MWG.MarketPower

open MWG.CompetitiveMarkets Set Function Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Firm `j`'s Cournot profit `p(Q)q_j − cq_j` (problem (12.C.1), MWG, p. 390). -/
def cournotProfit (p : ℝ → ℝ) (c : ℝ) (q : ι → ℝ) (j : ι) : ℝ := p (∑ k, q k) * q j - c * q j

/-- A pure strategy Nash equilibrium of the Cournot model (MWG, p. 390): every `q_j ≥ 0` is a
best response, `q_j ∈ b_j(q_{-j})`. -/
def IsCournotNE (p : ℝ → ℝ) (c : ℝ) (q : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ ∀ j y, 0 ≤ y → cournotProfit p c (update q j y) j ≤ cournotProfit p c q j

/-- The total output after firm `j` changes its quantity to `y`. -/
theorem sum_update_eq (q : ι → ℝ) (j : ι) (y : ℝ) :
    ∑ k, update q j y k = y + (∑ k, q k - q j) := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase]
  ring

/-- **Conditions (12.C.2)-(12.C.4)** (MWG, p. 390). In a Cournot equilibrium,
`p'(Q)q_j + p(Q) ≤ c` for every firm, with equality if `q_j > 0`. -/
theorem cournot_foc {p p' : ℝ → ℝ} {c : ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) {q : ι → ℝ}
    (hq : IsCournotNE p c q) (j : ι) :
    p' (∑ k, q k) * q j + p (∑ k, q k) ≤ c ∧
      (0 < q j → p' (∑ k, q k) * q j + p (∑ k, q k) = c) := by
  set R := ∑ k, q k - q j with hR
  have hR0 : 0 ≤ R := by
    rw [hR, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [add_sub_cancel_left]
    exact Finset.sum_nonneg fun k _ => hq.1 k
  have hQ : ∑ k, q k = q j + R := by rw [hR]; ring
  set f : ℝ → ℝ := fun y => p (y + R) * y - c * y with hf
  have hfeq : ∀ y, cournotProfit p c (update q j y) j = f y := by
    intro y; simp only [cournotProfit, update_self, sum_update_eq]; rfl
  have hfq : cournotProfit p c q j = f (q j) := by
    rw [← hfeq, update_eq_self]
  have hd : HasDerivWithinAt f (p' (q j + R) * 1 * q j + p (q j + R) * 1 - c * 1) (Ici 0)
      (q j) := by
    have hin : HasDerivWithinAt (fun y => y + R) 1 (Ici 0) (q j) :=
      (hasDerivWithinAt_id _ _).add_const R
    have hcomp := (hp (q j + R) (by simp; linarith [hq.1 j])).comp (q j) hin
      (fun y (hy : y ∈ Ici (0 : ℝ)) => show y + R ∈ Ici 0 by simp at hy ⊢; linarith)
    exact (hcomp.mul (hasDerivWithinAt_id _ _)).sub ((hasDerivWithinAt_id _ _).const_mul c)
  obtain ⟨h1, h2⟩ := foc_max_necessary hd (hq.1 j) fun y hy => by
    rw [← hfeq, ← hfq]; exact hq.2 j y hy
  rw [hQ]
  exact ⟨by linarith, fun h => by linarith [h2 h]⟩

/-- **Footnote 12** (MWG, p. 390), for any number of firms. If `p' < 0` and `p(0) > c`, every
firm produces a strictly positive quantity in every Cournot equilibrium. -/
theorem footnote_12_12 {p p' : ℝ → ℝ} {c : ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) (hp' : ∀ z, 0 ≤ z → p' z < 0)
    (hp0 : c < p 0) {q : ι → ℝ} (hq : IsCournotNE p c q) (j : ι) : 0 < q j := by
  have hQ0 : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq.1 k
  by_contra hj
  have hj0 : q j = 0 := le_antisymm (not_lt.1 hj) (hq.1 j)
  have h1 := (cournot_foc hp hq j).1
  rw [hj0, mul_zero, zero_add] at h1
  -- every firm then produces nothing
  have hall : ∀ k, q k = 0 := by
    intro k
    by_contra hk
    have hkpos : 0 < q k := lt_of_le_of_ne (hq.1 k) (Ne.symm hk)
    have h2 := (cournot_foc hp hq k).2 hkpos
    have := mul_neg_of_neg_of_pos (hp' _ hQ0) hkpos
    linarith
  have hsum : ∑ k, q k = 0 := Finset.sum_eq_zero fun k _ => hall k
  rw [hsum] at h1
  linarith

/-- **Condition (12.C.6)** (MWG, p. 393; (12.C.5) for `J = 2`, p. 390). Adding the first-order
conditions of the `J` firms: `p'(Q*)Q*/J + p(Q*) = c`. -/
theorem eq_12_C_6 {p p' : ℝ → ℝ} {c : ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) (hp' : ∀ z, 0 ≤ z → p' z < 0)
    (hp0 : c < p 0) [Nonempty ι] {q : ι → ℝ} (hq : IsCournotNE p c q) :
    p' (∑ k, q k) * ((∑ k, q k) / Fintype.card ι) + p (∑ k, q k) = c := by
  have hJ : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ j, (p' (∑ k, q k) * q j + p (∑ k, q k)) = ∑ _j : ι, c :=
    Finset.sum_congr rfl fun j _ => (cournot_foc hp hq j).2 (footnote_12_12 hp hp' hp0 hq j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul] at hsum
  field_simp
  linarith

/-- **Condition (12.C.5)** (MWG, p. 390): with two firms,
`p'(q₁* + q₂*)(q₁* + q₂*)/2 + p(q₁* + q₂*) = c`. -/
theorem eq_12_C_5 {p p' : ℝ → ℝ} {c : ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) (hp' : ∀ z, 0 ≤ z → p' z < 0)
    (hp0 : c < p 0) {q : Fin 2 → ℝ} (hq : IsCournotNE p c q) :
    p' (q 0 + q 1) * ((q 0 + q 1) / 2) + p (q 0 + q 1) = c := by
  have := eq_12_C_6 hp hp' hp0 hq
  simpa [Fin.sum_univ_two] using this

/-- **Condition (12.C.6) with `J = 1`** (MWG, p. 393): it is the monopoly condition (12.B.4). -/
theorem eq_12_C_6_one {p p' : ℝ → ℝ} {c Q : ℝ} :
    p' Q * (Q / 1) + p Q = c ↔ p' Q * Q + p Q = c := by
  rw [div_one]

/-- `p' < 0` on `[0, ∞)` makes `p` strictly decreasing there. -/
theorem strictAntiOn_of_deriv_neg' {p p' : ℝ → ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) (hp' : ∀ z, 0 ≤ z → p' z < 0) :
    StrictAntiOn p (Ici 0) :=
  strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0) (foc_continuousOn hp)
    (foc_hasDerivWithin_interior hp subset_rfl)
    (fun z hz => hp' z (interior_subset hz))

/-- **Proposition 12.C.2** (MWG, p. 390). In any Nash equilibrium of the Cournot duopoly with
`c > 0`, `p' < 0` and `p(0) > c`, the market price is greater than `c` and smaller than the
monopoly price `p(qᵐ)`, for any solution `qᵐ` of the monopoly problem (12.B.2) with cost `cq`. -/
theorem proposition_12_C_2 {p p' : ℝ → ℝ} {c : ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) (hp' : ∀ z, 0 ≤ z → p' z < 0)
    (hp0 : c < p 0) {q : Fin 2 → ℝ} (hq : IsCournotNE p c q) {qm : ℝ}
    (hqm : IsMonopolyOptimum p (fun z => c * z) qm) :
    c < p (q 0 + q 1) ∧ p (q 0 + q 1) < p qm := by
  have h5 := eq_12_C_5 hp hp' hp0 hq
  have hq0 := footnote_12_12 hp hp' hp0 hq 0
  have hq1 := footnote_12_12 hp hp' hp0 hq 1
  have hQ : 0 < q 0 + q 1 := by linarith
  have hanti := strictAntiOn_of_deriv_neg' hp hp'
  refine ⟨by nlinarith [hp' _ hQ.le], ?_⟩
  -- the monopoly condition (12.B.4)
  have hc' : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt (fun z => c * z) ((fun _ => c) z) (Ici 0) z :=
    fun z _ => ((hasDerivWithinAt_id z _).const_mul c).congr_deriv (by simp)
  obtain ⟨hqmpos, h4⟩ := eq_12_B_4 (c' := fun _ => c) (hp qm hqm.1) (hc' qm hqm.1) hqm hp0
  -- first, `Q* ≥ qᵐ`
  have hge : qm ≤ q 0 + q 1 := by
    by_contra hlt
    push Not at hlt
    -- firm 0 raises its output to `qᵐ − q₁*`
    have hdev := hq.2 0 (qm - q 1) (by linarith)
    have hsum : ∑ k, update q 0 (qm - q 1) k = qm := by
      rw [sum_update_eq, Fin.sum_univ_two]; ring
    have hmon := hqm.2 (q 0 + q 1) hQ.le
    simp only [cournotProfit, update_self, hsum, Fin.sum_univ_two] at hdev
    unfold monopolyProfit at hmon
    have hpl : p qm < p (q 0 + q 1) := hanti (mem_Ici.2 hQ.le) (mem_Ici.2 hqmpos.le) hlt
    have : p qm * q 1 < p (q 0 + q 1) * q 1 := mul_lt_mul_of_pos_right hpl hq1
    nlinarith
  rcases eq_or_lt_of_le hge with heq | hlt
  · exfalso
    rw [← heq] at h5
    have : p' qm * qm = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith [hp' qm hqm.1]
    · linarith
  · exact hanti (mem_Ici.2 hqm.1) (mem_Ici.2 hQ.le) hlt

/-- **The competitive limit of the Cournot model** (MWG, p. 393). Suppose `p' < 0` and `p'` is
continuous on `[0, ∞)`, `p(0) > c` and `p(q°) = c` with `q° > 0`. If for each `J ≥ 1`, `Q_J > 0`
satisfies (12.C.6), `p'(Q_J)Q_J/J + p(Q_J) = c`, then `Q_J < q°` and `p(Q_J) → c` as `J → ∞`. -/
theorem cournot_competitive_limit {p p' : ℝ → ℝ} {c q0 : ℝ}
    (hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' z) (Ici 0) z) (hp' : ∀ z, 0 ≤ z → p' z < 0)
    (hcont : ContinuousOn p' (Ici 0)) (hq0 : 0 ≤ q0) (hpq0 : p q0 = c) {Q : ℕ → ℝ}
    (hQ : ∀ J : ℕ, 0 < Q (J + 1) ∧ p' (Q (J + 1)) * (Q (J + 1) / (J + 1 : ℕ)) + p (Q (J + 1)) = c) :
    (∀ J : ℕ, Q (J + 1) < q0) ∧ Tendsto (fun J : ℕ => p (Q (J + 1))) atTop (𝓝 c) := by
  have hanti := strictAntiOn_of_deriv_neg' hp hp'
  have hlt : ∀ J : ℕ, Q (J + 1) < q0 := by
    intro J
    obtain ⟨hpos, heq⟩ := hQ J
    have hJ : (0 : ℝ) < (J + 1 : ℕ) := by positivity
    have : 0 < -(p' (Q (J + 1)) * (Q (J + 1) / (J + 1 : ℕ))) := by
      have := mul_neg_of_neg_of_pos (hp' _ hpos.le) (div_pos hpos hJ)
      linarith
    have hgt : c < p (Q (J + 1)) := by linarith
    by_contra hge; push Not at hge
    rcases eq_or_lt_of_le hge with h | h
    · rw [← h] at hgt; linarith
    · linarith [hanti (mem_Ici.2 hq0) (mem_Ici.2 hpos.le) h]
  refine ⟨hlt, ?_⟩
  -- `p'` is bounded on `[0, q°]`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := q0)).exists_bound_of_continuousOn
    (hcont.mono fun z hz => hz.1)
  have hbound : ∀ J : ℕ, |p (Q (J + 1)) - c| ≤ M * q0 / (J + 1 : ℕ) := by
    intro J
    obtain ⟨hpos, heq⟩ := hQ J
    have hJ : (0 : ℝ) < (J + 1 : ℕ) := by positivity
    have hmem : Q (J + 1) ∈ Icc 0 q0 := ⟨hpos.le, (hlt J).le⟩
    have h1 : p (Q (J + 1)) - c = -(p' (Q (J + 1)) * (Q (J + 1) / (J + 1 : ℕ))) := by linarith
    rw [h1, abs_neg, abs_mul, abs_of_pos (div_pos hpos hJ), mul_div_assoc]
    have hM' := hM _ hmem
    rw [Real.norm_eq_abs] at hM'
    exact mul_le_mul hM' (div_le_div_of_nonneg_right (hlt J).le hJ.le)
      (div_nonneg hpos.le hJ.le) ((abs_nonneg _).trans hM')
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun J : ℕ => M * q0 / ((J + 1 : ℕ) : ℝ)) (fun J => dist_nonneg)
    (fun J => by rw [Real.dist_eq]; exact hbound J) ?_
  have : Tendsto (fun J : ℕ => M * q0 * (1 / ((J : ℝ) + 1))) atTop (𝓝 (M * q0 * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at this
  refine this.congr fun J => ?_
  push_cast; ring

/-! ### The linear model -/

/-- **Example 12.C.1** (MWG, pp. 391-393). With `p(q) = a − bq`, `a > c ≥ 0`, `b > 0`, firm `j`'s
best response to `q_k ≥ 0` is `b_j(q_k) = max{0, (a − c − bq_k)/(2b)}`: it is the unique
maximizer of `(a − b(q_j + q_k))q_j − cq_j` over `q_j ≥ 0`. -/
theorem example_12_C_1_br {a b c qk : ℝ} (hb : 0 < b) (hqk : 0 ≤ qk) :
    0 ≤ max 0 ((a - c - b * qk) / (2 * b)) ∧
    ∀ y, 0 ≤ y → y ≠ max 0 ((a - c - b * qk) / (2 * b)) →
      (a - b * (y + qk)) * y - c * y <
        (a - b * (max 0 ((a - c - b * qk) / (2 * b)) + qk)) *
          max 0 ((a - c - b * qk) / (2 * b)) - c * max 0 ((a - c - b * qk) / (2 * b)) := by
  have _ := hqk
  refine ⟨le_max_left _ _, fun y hy hne => ?_⟩
  set r := (a - c - b * qk) / (2 * b) with hr
  have hkey : ∀ z, (a - b * (z + qk)) * z - c * z = b * r ^ 2 - b * (z - r) ^ 2 := by
    intro z; rw [hr]; field_simp; ring
  rcases le_total r 0 with h | h
  · rw [max_eq_left h] at hne ⊢
    rw [hkey]
    have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
    nlinarith [mul_pos hb (mul_pos hy' (show 0 < y - 2 * r by linarith))]
  · rw [max_eq_right h] at hne ⊢
    rw [hkey, hkey, sub_self]
    have : 0 < (y - r) ^ 2 := by positivity
    nlinarith

/-- **Example 12.C.1 and Exercise 12.C.6** (MWG, pp. 391-393). In the linear Cournot duopoly the
unique Nash equilibrium is `q₁* = q₂* = (a − c)/(3b)`, with total output `2(a − c)/(3b)` and price
`(a + 2c)/3`, which lies strictly between `c` and the monopoly price `pᵐ = (a + c)/2`. -/
theorem example_12_C_1 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    IsCournotNE (fun z => a - b * z) c (fun _ : Fin 2 => (a - c) / (3 * b)) ∧
    (∀ q, IsCournotNE (fun z => a - b * z) c q → q = fun _ : Fin 2 => (a - c) / (3 * b)) ∧
    a - b * ((a - c) / (3 * b) + (a - c) / (3 * b)) = (a + 2 * c) / 3 ∧
    c < (a + 2 * c) / 3 ∧ (a + 2 * c) / 3 < (a + c) / 2 := by
  have hq : 0 < (a - c) / (3 * b) := div_pos (by linarith) (by positivity)
  have hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt (fun z => a - b * z) ((fun _ => -b) z) (Ici 0) z :=
    fun z _ => (((hasDerivWithinAt_id z _).const_mul b).const_sub a).congr_deriv (by simp)
  refine ⟨⟨fun _ => hq.le, fun j y hy => ?_⟩, fun q hq' => ?_, by field_simp; ring,
    by linarith, by linarith⟩
  · simp only [cournotProfit, update_self, sum_update_eq, Fin.sum_univ_two]
    have := example_12_C_1_br (a := a) (b := b) (c := c) (qk := (a - c) / (3 * b)) hb hq.le
    have hmax : max 0 ((a - c - b * ((a - c) / (3 * b))) / (2 * b)) = (a - c) / (3 * b) := by
      rw [max_eq_right]; · field_simp; ring
      · field_simp; linarith
    rw [hmax] at this
    by_cases hyq : y = (a - c) / (3 * b)
    · rw [hyq]; ring_nf; exact le_rfl
    · have := this.2 y hy hyq
      ring_nf at this ⊢; linarith
  · -- uniqueness from the first-order conditions
    have hp' : ∀ z : ℝ, 0 ≤ z → (fun _ => -b) z < 0 := fun _ _ => by
      simp only [Left.neg_neg_iff]; exact hb
    have h0 := (cournot_foc hp hq' 0).2 (footnote_12_12 hp hp' (by simpa) hq' 0)
    have h1 := (cournot_foc hp hq' 1).2 (footnote_12_12 hp hp' (by simpa) hq' 1)
    simp only [Fin.sum_univ_two] at h0 h1
    have e0 : q 0 = (a - c) / (3 * b) := by field_simp; nlinarith
    have e1 : q 1 = (a - c) / (3 * b) := by field_simp; nlinarith
    funext j; fin_cases j
    · exact e0
    · exact e1

/-- **Example 12.C.1, the joint monopoly point** (MWG, pp. 392-393). On the ray `q₁ = q₂ = q`,
firm 1's profit `(a − 2bq − c)q` is uniquely maximized at `q = qᵐ/2 = (a − c)/(4b)`. -/
theorem example_12_C_1_joint {a b c : ℝ} (hb : 0 < b) :
    ∀ q, q ≠ (a - c) / (4 * b) →
      (a - b * (q + q) - c) * q < (a - b * ((a - c) / (4 * b) + (a - c) / (4 * b)) - c) *
        ((a - c) / (4 * b)) := by
  intro q hq
  have key : (a - b * ((a - c) / (4 * b) + (a - c) / (4 * b)) - c) * ((a - c) / (4 * b)) -
      (a - b * (q + q) - c) * q = 2 * b * (q - (a - c) / (4 * b)) ^ 2 := by field_simp; ring
  have : 0 < (q - (a - c) / (4 * b)) ^ 2 := by
    have : q - (a - c) / (4 * b) ≠ 0 := sub_ne_zero.2 hq
    positivity
  nlinarith

/-- **Exercise 12.C.6** (MWG, p. 393): the computations of Example 12.C.1 (an alias). -/
theorem exercise_12_C_6 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    IsCournotNE (fun z => a - b * z) c (fun _ : Fin 2 => (a - c) / (3 * b)) ∧
    (∀ q, IsCournotNE (fun z => a - b * z) c q → q = fun _ : Fin 2 => (a - c) / (3 * b)) ∧
    a - b * ((a - c) / (3 * b) + (a - c) / (3 * b)) = (a + 2 * c) / 3 ∧
    c < (a + 2 * c) / 3 ∧ (a + 2 * c) / 3 < (a + c) / 2 :=
  example_12_C_1 hac hb

/-- **Exercise 12.C.7** (MWG, p. 393). In the linear Cournot model with `J ≥ 1` identical firms,
the unique Nash equilibrium has `q_j = (a − c)/(b(J + 1))`, aggregate output
`Q_J = J(a − c)/(b(J + 1))` and price `p_J = (a + Jc)/(J + 1)`. -/
theorem exercise_12_C_7 {a b c : ℝ} (hac : c < a) (hb : 0 < b) [Nonempty ι] :
    IsCournotNE (fun z => a - b * z) c (fun _ : ι => (a - c) / (b * (Fintype.card ι + 1))) ∧
    (∀ q, IsCournotNE (fun z => a - b * z) c q →
      q = fun _ : ι => (a - c) / (b * (Fintype.card ι + 1))) ∧
    a - b * (∑ _k : ι, (a - c) / (b * (Fintype.card ι + 1))) =
      (a + Fintype.card ι * c) / (Fintype.card ι + 1) := by
  set J : ℝ := (Fintype.card ι : ℝ) with hJ
  have hJpos : (0 : ℝ) < J := by rw [hJ]; exact_mod_cast Fintype.card_pos
  have hq : 0 < (a - c) / (b * (J + 1)) := div_pos (by linarith) (by positivity)
  have hp : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt (fun z => a - b * z) ((fun _ => -b) z) (Ici 0) z :=
    fun z _ => (((hasDerivWithinAt_id z _).const_mul b).const_sub a).congr_deriv (by simp)
  have hsumc : ∑ _k : ι, (a - c) / (b * (J + 1)) = J * ((a - c) / (b * (J + 1))) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨⟨fun _ => hq.le, fun j y hy => ?_⟩, fun q hq' => ?_, by rw [hsumc]; field_simp; ring⟩
  · simp only [cournotProfit, update_self, sum_update_eq, hsumc]
    set r := (a - c) / (b * (J + 1)) with hr
    have key : (a - b * (r + (J * r - r))) * r - c * r - ((a - b * (y + (J * r - r))) * y - c * y)
        = b * (y - r) ^ 2 := by rw [hr]; field_simp; ring
    nlinarith [mul_nonneg hb.le (sq_nonneg (y - r))]
  · have hp' : ∀ z : ℝ, 0 ≤ z → (fun _ => -b) z < 0 := fun _ _ => by
      simp only [Left.neg_neg_iff]; exact hb
    have hfoc : ∀ j, -b * q j + (a - b * ∑ k, q k) = c := fun j => by
      have := (cournot_foc hp hq' j).2 (footnote_12_12 hp hp' (by simpa) hq' j)
      linarith
    set Q := ∑ k, q k with hQdef
    have hqj : ∀ j, q j = (a - c - b * Q) / b := fun j => by
      field_simp; linarith [hfoc j]
    have hQ : Q = J * ((a - c - b * Q) / b) := by
      calc Q = ∑ k, q k := rfl
        _ = ∑ _k : ι, (a - c - b * Q) / b := Finset.sum_congr rfl fun j _ => hqj j
        _ = J * ((a - c - b * Q) / b) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 : Q * b = J * (a - c - b * Q) := by
      conv_lhs => rw [hQ]
      field_simp
    have hQv : Q = J * (a - c) / (b * (J + 1)) := by
      rw [eq_div_iff (by positivity)]; linarith
    funext j
    rw [hqj j, hQv]; field_simp; ring

/-- **Exercise 12.C.7, comparative statics and limits** (MWG, p. 393). With `J = 1` the price
is the monopoly price `(a + c)/2`; the price `(a + Jc)/(J + 1)` strictly decreases and the output
`J(a − c)/(b(J + 1))` strictly increases in `J`; as `J → ∞` they converge to the competitive levels
`c` and `(a − c)/b`. -/
theorem exercise_12_C_7_limits {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (a + (1 : ℕ) * c) / ((1 : ℕ) + 1) = (a + c) / 2 ∧
    StrictAnti (fun J : ℕ => (a + J * c) / (J + 1)) ∧
    StrictMono (fun J : ℕ => J * (a - c) / (b * (J + 1))) ∧
    Tendsto (fun J : ℕ => (a + J * c) / (J + 1)) atTop (𝓝 c) ∧
    Tendsto (fun J : ℕ => J * (a - c) / (b * (J + 1))) atTop (𝓝 ((a - c) / b)) := by
  have hpJ : ∀ J : ℕ, (a + J * c) / (J + 1) = c + (a - c) * (1 / ((J : ℝ) + 1)) := by
    intro J; field_simp; ring
  have hQJ : ∀ J : ℕ, J * (a - c) / (b * (J + 1)) =
      (a - c) / b - (a - c) / b * (1 / ((J : ℝ) + 1)) := by
    intro J; field_simp; ring
  have hinv : StrictAnti fun J : ℕ => 1 / ((J : ℝ) + 1) := by
    intro m n hmn
    have : (m : ℝ) < n := by exact_mod_cast hmn
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hA : 0 < a - c := by linarith
  have hAb : 0 < (a - c) / b := div_pos hA hb
  refine ⟨by push_cast; ring, fun m n hmn => ?_, fun m n hmn => ?_, ?_, ?_⟩
  · simp only [hpJ]; nlinarith [hinv hmn]
  · simp only [hQJ]; nlinarith [hinv hmn]
  · simp only [hpJ]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (a - c)).const_add c
    simpa using this
  · simp only [hQJ]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((a - c) / b)).const_sub
      ((a - c) / b)
    simpa using this

end MWG.MarketPower
