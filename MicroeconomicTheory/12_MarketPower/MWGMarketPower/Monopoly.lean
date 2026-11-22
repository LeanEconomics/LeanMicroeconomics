/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.FOCTools
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact

/-!
# Monopoly pricing

MWG, Section 12.B, pp. 384-387.

The monopolist faces the inverse demand function `p(q)` and the cost function `c(q)` and solves
(12.B.2) `max_{q ≥ 0} p(q)q − c(q)`. Derivatives are taken within `[0, ∞)` (one-sided at `0`),
which is MWG's differentiability "at all `q ≥ 0`".

* `eq_12_B_3`, `eq_12_B_4`: the Kuhn-Tucker condition (12.B.3); with `p(0) > c'(0)` every
  optimum is interior and marginal revenue equals marginal cost (12.B.4).
* `monopoly_price_gt_mc`, `monopoly_quantity_lt`: with `p'(qᵐ) < 0` the price exceeds marginal
  cost, and the output is below the socially optimal `q°`.
* `footnote_12_5`: existence of an optimum in `[0, q°]` when `p' ≤ 0` and `p < c'` beyond `q°`.
  `footnote_12_5_counterexample`: with only the printed hypotheses (a unique `q°` with
  `p(q°) = c'(q°)`) there may be no optimum (correction 1).
* `footnote_12_6`: the Kuhn-Tucker condition is sufficient when the objective is concave on
  `[0, q°]`; `footnote_12_6_not_concave`: a convex cost and a convex demand can give a
  non-concave objective.
* `deadweight_loss_pos`: the deadweight loss `∫_{qᵐ}^{q°} (p − c') > 0`.
* `flat_demand_no_distortion`: with `p' = 0` the monopolist sells `q°`.
* `example_12_B_1`: linear inverse demand and constant returns.
* `perfect_discrimination`: take-it-or-leave-it offers extract `uᵢ(qᵢ)`, so the monopolist solves
  (12.B.5), the aggregate surplus problem.
-/

namespace MWG.MarketPower

open MWG.CompetitiveMarkets Set

/-- The monopolist's profit `p(q)q − c(q)` (problem (12.B.2), MWG, p. 385). -/
def monopolyProfit (p c : ℝ → ℝ) (q : ℝ) : ℝ := p q * q - c q

/-- `qm` solves the monopolist's problem (12.B.2) (MWG, p. 385). -/
def IsMonopolyOptimum (p c : ℝ → ℝ) (qm : ℝ) : Prop :=
  0 ≤ qm ∧ ∀ q, 0 ≤ q → monopolyProfit p c q ≤ monopolyProfit p c qm

/-- The derivative of the monopolist's profit: marginal revenue minus marginal cost. -/
theorem hasDerivWithinAt_monopolyProfit {p c p' c' : ℝ → ℝ} {q : ℝ}
    (hp : HasDerivWithinAt p (p' q) (Ici 0) q) (hc : HasDerivWithinAt c (c' q) (Ici 0) q) :
    HasDerivWithinAt (monopolyProfit p c) (p' q * q + p q - c' q) (Ici 0) q := by
  have h := (hp.mul (hasDerivWithinAt_id q (Ici 0))).sub hc
  simp only [id, mul_one] at h
  exact h

/-- **Condition (12.B.3)** (MWG, p. 385). At an optimum `qᵐ`,
`p'(qᵐ)qᵐ + p(qᵐ) ≤ c'(qᵐ)`, with equality if `qᵐ > 0`. -/
theorem eq_12_B_3 {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) :
    p' qm * qm + p qm ≤ c' qm ∧ (0 < qm → p' qm * qm + p qm = c' qm) := by
  obtain ⟨h1, h2⟩ := foc_max_necessary (hasDerivWithinAt_monopolyProfit hp hc) hqm.1 hqm.2
  exact ⟨by linarith, fun h => by linarith [h2 h]⟩

/-- **Condition (12.B.4)** (MWG, p. 385). If `p(0) > c'(0)`, every optimum is strictly
positive and marginal revenue equals marginal cost there. -/
theorem eq_12_B_4 {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) :
    0 < qm ∧ p' qm * qm + p qm = c' qm := by
  have hfoc := eq_12_B_3 hp hc hqm
  have hpos : 0 < qm := by
    rcases eq_or_lt_of_le hqm.1 with h | h
    · subst h
      have := hfoc.1
      simp only [mul_zero, zero_add] at this
      linarith
    · exact h
  exact ⟨hpos, hfoc.2 hpos⟩

/-- **The monopoly price exceeds marginal cost** (MWG, p. 385). If `p(0) > c'(0)` and
`p'(qᵐ) < 0`, then `p(qᵐ) > c'(qᵐ)`. -/
theorem monopoly_price_gt_mc {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) (hneg : p' qm < 0) :
    c' qm < p qm := by
  obtain ⟨hpos, heq⟩ := eq_12_B_4 hp hc hqm h0
  nlinarith

/-- **The monopoly output is below the socially optimal output** (MWG, p. 385). If, in addition,
`p(q) < c'(q)` for every `q > q°` (the fact used in footnote 5) and `p(q°) = c'(q°)`, then
`qᵐ < q°`. -/
theorem monopoly_quantity_lt {p c p' c' : ℝ → ℝ} {qm q0 : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) (hneg : p' qm < 0)
    (hq0 : p q0 = c' q0) (hbeyond : ∀ q, q0 < q → p q < c' q) : qm < q0 := by
  have hgt := monopoly_price_gt_mc hp hc hqm h0 hneg
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · rw [← h] at hgt; linarith
  · linarith [hbeyond qm h]

/-- **Footnote 5** (MWG, p. 385). If `p` and `c` are differentiable on `[0, ∞)`, `p' ≤ 0`, and
`p(q) < c'(q)` for all `q > q°` (with `q° ≥ 0`), the monopolist's problem (12.B.2) has a solution,
and it lies in `[0, q°]`. -/
theorem footnote_12_5 {p c p' c' : ℝ → ℝ} {q0 : ℝ} (hq0 : 0 ≤ q0)
    (hp : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' q) (Ici 0) q)
    (hc : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' q) (Ici 0) q)
    (hp' : ∀ q, 0 ≤ q → p' q ≤ 0) (hbeyond : ∀ q, q0 < q → p q < c' q) :
    ∃ qm, qm ≤ q0 ∧ IsMonopolyOptimum p c qm := by
  have hd : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt (monopolyProfit p c) (p' q * q + p q - c' q)
      (Ici 0) q := fun q hq => hasDerivWithinAt_monopolyProfit (hp q hq) (hc q hq)
  have hcont := foc_continuousOn hd
  obtain ⟨qm, hqm, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := q0)).exists_isMaxOn
    ⟨0, le_rfl, hq0⟩ (hcont.mono fun x hx => hx.1)
  have hsub : Ici q0 ⊆ Ici (0 : ℝ) := fun x hx => hq0.trans hx
  have hanti : AntitoneOn (monopolyProfit p c) (Ici q0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici q0) (hcont.mono hsub)
      (foc_hasDerivWithin_interior hd hsub) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 ≤ x := hq0.trans hx.le
    have := hbeyond x hx
    nlinarith [hp' x hx0]
  refine ⟨qm, hqm.2, hqm.1, fun q hq => ?_⟩
  rcases le_total q q0 with h | h
  · exact hmax ⟨hq, h⟩
  · exact (hanti (mem_Ici.2 le_rfl) h h).trans (hmax ⟨hq0, le_rfl⟩)

/-- The inverse demand of the counterexample to footnote 5: `p(q) = 1 + 1/(1 + q)²`. -/
noncomputable def cexP (q : ℝ) : ℝ := 1 + 1 / (1 + q) ^ 2

/-- The cost of the counterexample to footnote 5: `c(q) = arctan(q − 1) − 1/(1 + q)`, so that
`c'(q) = 1/(1 + (q − 1)²) + 1/(1 + q)² > 0`. -/
noncomputable def cexC (q : ℝ) : ℝ := Real.arctan (q - 1) - 1 / (1 + q)

/-- The marginal cost of the counterexample. -/
noncomputable def cexMC (q : ℝ) : ℝ := 1 / (1 + (q - 1) ^ 2) + 1 / (1 + q) ^ 2

/-- The slope of the counterexample's inverse demand. -/
noncomputable def cexDP (q : ℝ) : ℝ := -2 / (1 + q) ^ 3

theorem cexC_hasDerivAt {q : ℝ} (hq : 0 ≤ q) : HasDerivAt cexC (cexMC q) q := by
  have h1 := ((hasDerivAt_id q).sub_const 1).arctan
  have hne : (1 + q) ≠ 0 := by positivity
  have h2 := ((hasDerivAt_id q).const_add 1).inv hne
  have h := h1.sub h2
  change HasDerivAt (fun x => Real.arctan (x - 1) - 1 / (1 + x)) (cexMC q) q
  simp only [one_div]
  refine h.congr_deriv ?_
  unfold cexMC
  simp only [id]
  field_simp
  ring

theorem cexP_hasDerivAt {q : ℝ} (hq : 0 ≤ q) : HasDerivAt cexP (cexDP q) q := by
  have hne : (1 + q) ≠ 0 := by positivity
  have h : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + q)) q := by
    convert ((hasDerivAt_id q).const_add 1).pow 2 using 1
    · funext x; simp
    · simp
  have h2 := (h.inv (pow_ne_zero 2 hne)).const_add 1
  change HasDerivAt (fun x => 1 + 1 / (1 + x) ^ 2) (cexDP q) q
  simp only [one_div]
  refine h2.congr_deriv ?_
  unfold cexDP
  field_simp

/-- **Footnote 5 and the existence claim of p. 385 as printed are false** (MWG, p. 385;
correction 1). For `p(q) = 1 + 1/(1+q)²` and `c(q) = arctan(q − 1) − 1/(1 + q)`, both smooth on
`[0, ∞)`, `p' < 0`, `c' > 0`, `p(0) > c'(0)`, and `q° = 1` is the unique `q ≥ 0` with
`p(q) = c'(q)`; yet the monopolist's problem (12.B.2) has no solution (profit is unbounded),
because `p > c'` on both sides of `q°`. -/
theorem footnote_12_5_counterexample :
    (∀ q, 0 ≤ q → HasDerivAt cexP (cexDP q) q ∧ HasDerivAt cexC (cexMC q) q) ∧
    (∀ q, 0 ≤ q → cexDP q < 0 ∧ 0 < cexMC q) ∧ cexMC 0 < cexP 0 ∧
    (∀ q, 0 ≤ q → (cexP q = cexMC q ↔ q = 1)) ∧
    ¬ ∃ qm, IsMonopolyOptimum cexP cexC qm := by
  refine ⟨fun q hq => ⟨cexP_hasDerivAt hq, cexC_hasDerivAt hq⟩, fun q hq => ⟨?_, ?_⟩, ?_,
    fun q hq => ?_, ?_⟩
  · unfold cexDP
    have : 0 < (1 + q) ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (by norm_num) this
  · unfold cexMC; positivity
  · unfold cexMC cexP; norm_num
  · unfold cexP cexMC
    have h1 : (0 : ℝ) < 1 + (q - 1) ^ 2 := by positivity
    constructor
    · intro h
      have h' : 1 = 1 / (1 + (q - 1) ^ 2) := by linarith
      rw [eq_div_iff h1.ne'] at h'
      nlinarith [sq_nonneg (q - 1)]
    · rintro rfl; norm_num
  · rintro ⟨qm, hqm0, hmax⟩
    have hbd : ∀ q, 0 ≤ q → q - 2 ≤ monopolyProfit cexP cexC q ∧
        monopolyProfit cexP cexC q ≤ q + 4 := by
      intro q hq
      unfold monopolyProfit cexP cexC
      have ha := Real.arctan_lt_pi_div_two (q - 1)
      have hb := Real.neg_pi_div_two_lt_arctan (q - 1)
      have hpi := Real.pi_le_four
      have h1 : 0 ≤ 1 / (1 + q) ^ 2 * q := by positivity
      have h2 : 1 / (1 + q) ^ 2 * q ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        nlinarith
      have h3 : 0 ≤ 1 / (1 + q) := by positivity
      have h4 : 1 / (1 + q) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      constructor <;> nlinarith
    have h1 := (hbd qm hqm0).2
    have h2 := (hbd (qm + 7) (by linarith)).1
    have := hmax (qm + 7) (by linarith)
    linarith

/-- **Footnote 6** (MWG, p. 385). If the derivative of the profit, `p'(q)q + p(q) − c'(q)`, is
antitone on `[0, q°]` (the objective is concave there), `p' ≤ 0`, `p < c'` beyond `q°`, and
`qᵐ ∈ [0, q°]` satisfies the Kuhn-Tucker condition (12.B.3), then `qᵐ` solves (12.B.2). -/
theorem footnote_12_6 {p c p' c' : ℝ → ℝ} {q0 qm : ℝ} (hq0 : 0 ≤ q0)
    (hp : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' q) (Ici 0) q)
    (hc : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' q) (Ici 0) q)
    (hp' : ∀ q, 0 ≤ q → p' q ≤ 0) (hbeyond : ∀ q, q0 < q → p q < c' q)
    (hconc : AntitoneOn (fun q => p' q * q + p q - c' q) (Icc 0 q0))
    (hqm : qm ∈ Icc 0 q0)
    (hfoc : p' qm * qm + p qm ≤ c' qm ∧ (0 < qm → p' qm * qm + p qm = c' qm)) :
    IsMonopolyOptimum p c qm := by
  have hd : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt (monopolyProfit p c) (p' q * q + p q - c' q)
      (Ici 0) q := fun q hq => hasDerivWithinAt_monopolyProfit (hp q hq) (hc q hq)
  have hcont := foc_continuousOn hd
  have hsub : Ici q0 ⊆ Ici (0 : ℝ) := fun x hx => hq0.trans hx
  have hanti : AntitoneOn (monopolyProfit p c) (Ici q0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici q0) (hcont.mono hsub)
      (foc_hasDerivWithin_interior hd hsub) ?_
    intro x hx
    rw [interior_Ici] at hx
    have := hbeyond x hx
    have := mul_nonpos_of_nonpos_of_nonneg (hp' x (hq0.trans hx.le)) (hq0.trans hx.le)
    linarith
  have hR : AntitoneOn (monopolyProfit p c) (Icc qm q0) := by
    have hs : Icc qm q0 ⊆ Ici (0 : ℝ) := fun x hx => hqm.1.trans hx.1
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc qm q0) (hcont.mono hs)
      (foc_hasDerivWithin_interior hd hs) ?_
    intro x hx
    rw [interior_Icc] at hx
    have := hconc ⟨hqm.1, hqm.2⟩ ⟨hqm.1.trans hx.1.le, hx.2.le⟩ hx.1.le
    simp only at this
    linarith [hfoc.1]
  have hL : MonotoneOn (monopolyProfit p c) (Icc 0 qm) := by
    have hs : Icc 0 qm ⊆ Ici (0 : ℝ) := fun x hx => hx.1
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 qm) (hcont.mono hs)
      (foc_hasDerivWithin_interior hd hs) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hpos : 0 < qm := hx.1.trans hx.2
    have := hconc ⟨hx.1.le, hx.2.le.trans hqm.2⟩ ⟨hqm.1, hqm.2⟩ hx.2.le
    simp only at this
    linarith [hfoc.2 hpos]
  refine ⟨hqm.1, fun q hq => ?_⟩
  rcases le_total q qm with h | h
  · exact hL ⟨hq, h⟩ ⟨hqm.1, le_rfl⟩ h
  rcases le_total q q0 with h' | h'
  · exact hR ⟨le_rfl, hqm.2⟩ ⟨h, h'⟩ h
  · exact (hanti (mem_Ici.2 le_rfl) h' h').trans (hR ⟨le_rfl, hqm.2⟩ ⟨hqm.2, le_rfl⟩ hqm.2)

/-- **Footnote 6, the non-concavity remark** (MWG, p. 385). With the convex cost `c(q) = q/16`
and the inverse demand `p(q) = 1/(1 + q)²` (demand `x(p) = p^{-1/2} − 1`, a convex function of
price), `q° = 3` and the monopolist's objective is not concave on `[0, q°]`: its value at
`5/2` lies strictly below the chord between `2` and `3`. -/
theorem footnote_12_6_not_concave :
    (1 / (1 + (3 : ℝ)) ^ 2 = 1 / 16) ∧
    monopolyProfit (fun q => 1 / (1 + q) ^ 2) (fun q => q / 16) (5 / 2) <
      (monopolyProfit (fun q => 1 / (1 + q) ^ 2) (fun q => q / 16) 2 +
        monopolyProfit (fun q => 1 / (1 + q) ^ 2) (fun q => q / 16) 3) / 2 := by
  unfold monopolyProfit
  norm_num

/-- **The deadweight loss of monopoly is positive** (MWG, p. 386). If `p − c'` is continuous on
`[0, ∞)`, `p(0) > c'(0)`, `q°` is the unique `q ≥ 0` with `p(q) = c'(q)`, and `0 ≤ qᵐ < q°`, then
`∫_{qᵐ}^{q°} [p(s) − c'(s)] ds > 0`. -/
theorem deadweight_loss_pos {p c' : ℝ → ℝ} {qm q0 : ℝ}
    (hcont : ContinuousOn (fun q => p q - c' q) (Ici 0)) (h0 : c' 0 < p 0)
    (huniq : ∀ q, 0 ≤ q → p q = c' q → q = q0) (hqm : 0 ≤ qm) (hlt : qm < q0) :
    0 < ∫ s in qm..q0, (p s - c' s) := by
  have hpos : ∀ q, 0 ≤ q → q < q0 → 0 < p q - c' q := by
    intro q hq hqq
    by_contra hle
    push Not at hle
    have hsub : Icc 0 q ⊆ Ici (0 : ℝ) := fun x hx => hx.1
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hq (hcont.mono hsub)
      (show (0 : ℝ) ∈ Icc (p q - c' q) (p 0 - c' 0) from ⟨hle, by linarith⟩)
    have := huniq r hr.1 (by simp only at hr0; linarith)
    linarith [hr.2]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx =>
    hpos x (hqm.trans hx.1.le) hx.2) hlt
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlt.le]
  exact hcont.mono fun x hx => hqm.trans hx.1

/-- **The case `p'(q) = 0`** (MWG, p. 386, Figure 12.B.2). If `p(q) = p̄` for all `q` and `q°`
is the unique `q ≥ 0` with `p̄ = c'(q)`, with `p̄ > c'(0)`, then the monopolist sells exactly the
competitive quantity `q°`. -/
theorem flat_demand_no_distortion {c c' : ℝ → ℝ} {pbar qm q0 : ℝ}
    (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum (fun _ => pbar) c qm) (h0 : c' 0 < pbar)
    (huniq : ∀ q, 0 ≤ q → pbar = c' q → q = q0) : qm = q0 := by
  have hp : HasDerivWithinAt (fun _ : ℝ => pbar) ((fun _ => (0 : ℝ)) qm) (Ici 0) qm :=
    hasDerivWithinAt_const _ _ _
  obtain ⟨hpos, heq⟩ := eq_12_B_4 (p' := fun _ => 0) hp hc hqm h0
  exact huniq qm hpos.le (by simpa using heq)

/-- **Example 12.B.1** (MWG, p. 386). With `p(q) = a − bq` and `c(q) = cq`, `a > c ≥ 0`, `b > 0`:
the objective is concave, `qᵐ = (a − c)/(2b)` is the (unique) optimum with price
`pᵐ = (a + c)/2`, while `q° = (a − c)/b` and `p(q°) = c`. -/
theorem example_12_B_1 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    ConcaveOn ℝ (Ici 0) (monopolyProfit (fun q => a - b * q) (fun q => c * q)) ∧
    IsMonopolyOptimum (fun q => a - b * q) (fun q => c * q) ((a - c) / (2 * b)) ∧
    (∀ q, IsMonopolyOptimum (fun q => a - b * q) (fun q => c * q) q → q = (a - c) / (2 * b)) ∧
    a - b * ((a - c) / (2 * b)) = (a + c) / 2 ∧ a - b * ((a - c) / b) = c := by
  have hqm : 0 ≤ (a - c) / (2 * b) := div_nonneg (by linarith) (by positivity)
  have key : ∀ q, monopolyProfit (fun q => a - b * q) (fun q => c * q) q =
      monopolyProfit (fun q => a - b * q) (fun q => c * q) ((a - c) / (2 * b)) -
        b * (q - (a - c) / (2 * b)) ^ 2 := by
    intro q; unfold monopolyProfit; field_simp; ring
  refine ⟨⟨convex_Ici 0, fun x _ y _ α β hα hβ hαβ => ?_⟩, ⟨hqm, fun q _ => ?_⟩,
    fun q hq => ?_, by field_simp; ring, by field_simp; ring⟩
  · simp only [monopolyProfit, smul_eq_mul]
    have : β = 1 - α := by linarith
    subst this
    nlinarith [mul_nonneg hα hβ, sq_nonneg (x - y), mul_nonneg (mul_nonneg hα hβ) hb.le,
      mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (x - y))]
  · rw [key q]; nlinarith [sq_nonneg (q - (a - c) / (2 * b))]
  · have h1 := hq.2 ((a - c) / (2 * b)) hqm
    rw [key q] at h1
    have : b * (q - (a - c) / (2 * b)) ^ 2 ≤ 0 := by linarith
    have h2 : (q - (a - c) / (2 * b)) ^ 2 = 0 := le_antisymm
      (by nlinarith [sq_nonneg (q - (a - c) / (2 * b))]) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    linarith

/-- **Perfect price discrimination** (MWG, p. 387, (12.B.5)). Consumer `i` accepts the offer
`(qᵢ, Tᵢ)` iff `uᵢ(qᵢ) − Tᵢ ≥ 0`. Any profile of accepted offers earns at most
`∑ᵢ uᵢ(qᵢ) − c(∑ᵢ qᵢ)`, and the offers `Tᵢ = uᵢ(qᵢ)` are accepted and attain it, leaving each
consumer a surplus of exactly zero. Hence the monopolist's optimal quantities solve (12.B.5),
which is the aggregate surplus problem. -/
theorem perfect_discrimination {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ) (c : ℝ → ℝ)
    (q T : ι → ℝ) (hacc : ∀ i, 0 ≤ u i (q i) - T i) :
    (∑ i, T i) - c (∑ i, q i) ≤ (∑ i, u i (q i)) - c (∑ i, q i) ∧
    (∀ i, 0 ≤ u i (q i) - u i (q i)) ∧ (∀ i, u i (q i) - u i (q i) = 0) := by
  refine ⟨?_, fun i => by simp, fun i => by simp⟩
  have : ∑ i, T i ≤ ∑ i, u i (q i) := Finset.sum_le_sum fun i _ => by linarith [hacc i]
  linarith

/-- **Perfect discrimination is efficient** (MWG, p. 387). If `q` solves (12.B.5) then the
offers `(qᵢ, uᵢ(qᵢ))` are optimal among all profiles of accepted offers. -/
theorem perfect_discrimination_optimal {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ) (c : ℝ → ℝ)
    (q : ι → ℝ) (hq : ∀ q' : ι → ℝ, (∀ i, 0 ≤ q' i) →
      (∑ i, u i (q' i)) - c (∑ i, q' i) ≤ (∑ i, u i (q i)) - c (∑ i, q i))
    (q' T : ι → ℝ) (hq' : ∀ i, 0 ≤ q' i) (hacc : ∀ i, 0 ≤ u i (q' i) - T i) :
    (∑ i, T i) - c (∑ i, q' i) ≤ (∑ i, u i (q i)) - c (∑ i, q i) :=
  ((perfect_discrimination u c q' T hacc).1).trans (hq q' hq')

end MWG.MarketPower
