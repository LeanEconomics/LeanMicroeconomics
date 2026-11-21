import MWGCompetitiveMarkets.FOCTools
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import MWGDynamicGames.OneShotDeviation
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MWGSimultaneousMoveGames.Existence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.Interval.Finset.Fin
import MWGSimultaneousMoveGames.Cournot
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 12.B.1-12.B.10

MWG, Exercises 12.B.1-12.B.10, pp. 428-430.

* 12.B.1: the Lerner index equals the inverse elasticity; with positive marginal cost demand is
  elastic at the monopoly price.
* 12.B.2: constant-elasticity demand `x(p) = αp^{-ε}`: no optimal price when `ε ≤ 1`; for
  `ε > 1` the optimal price `pᵐ = εc/(ε − 1)`, output, margin `1/ε` and the deadweight loss.
* 12.B.3: comparative statics by the implicit function theorem (cost and demand shifts).
* 12.B.4: revealed preference: the monopoly price is nondecreasing in cost.
* 12.B.6: the per-unit subsidy `−p'(q°)q°` makes the monopolist efficient.
* 12.B.7: men's and women's demands: competition, uniform monopoly price, the efficient split
  of output, discrimination and welfare.
* 12.B.8: learning by doing; 12.B.9: investment in cost reduction; 12.B.10: quality choice.

Exercises 12.B.2(c) and 12.B.5 are in `MonopolyExercises3`.
-/

namespace MWG.MarketPower

open MWG.CompetitiveMarkets Set Filter Topology

/-! ### Exercise 12.B.1 -/

/-- The price elasticity of demand at output `q`, `ε = −(dx/dp)(p/x)`, written with the inverse
demand: since `dx/dp = 1/p'(q)` and `x = q`, `ε = −p(q)/(p'(q)q)`. -/
noncomputable def priceElasticity (p p' : ℝ → ℝ) (q : ℝ) : ℝ := -(p q) / (p' q * q)

/-- The elasticity written with the demand slope `x' = 1/p'(q)` and `x = q`. -/
theorem priceElasticity_eq_demand (p p' : ℝ → ℝ) (q : ℝ) :
    priceElasticity p p' q = -(1 / p' q) * (p q / q) := by
  unfold priceElasticity
  rw [neg_div, neg_mul, div_mul_div_comm, one_mul]

/-- **Exercise 12.B.1(a)** (MWG, p. 428). The monopolist's price-cost margin equals the inverse
of the price elasticity of demand at `pᵐ`: `(pᵐ − c'(qᵐ))/pᵐ = 1/ε`. -/
theorem exercise_12_B_1a {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) :
    (p qm - c' qm) / p qm = 1 / priceElasticity p p' qm := by
  obtain ⟨hpos, heq⟩ := eq_12_B_4 hp hc hqm h0
  unfold priceElasticity
  rw [one_div_div, div_neg, ← neg_div]
  congr 1
  linarith

/-- **Exercise 12.B.1(b)** (MWG, p. 428). If marginal cost is positive (and `p'(qᵐ) < 0`),
demand is elastic at the monopoly price: `ε > 1`. -/
theorem exercise_12_B_1b {p c p' c' : ℝ → ℝ} {qm : ℝ}
    (hp : HasDerivWithinAt p (p' qm) (Ici 0) qm) (hc : HasDerivWithinAt c (c' qm) (Ici 0) qm)
    (hqm : IsMonopolyOptimum p c qm) (h0 : c' 0 < p 0) (hneg : p' qm < 0)
    (hmc : 0 < c' qm) : 1 < priceElasticity p p' qm := by
  obtain ⟨hpos, heq⟩ := eq_12_B_4 hp hc hqm h0
  have hgt := monopoly_price_gt_mc hp hc hqm h0 hneg
  unfold priceElasticity
  have hd : 0 < -(p' qm * qm) := by nlinarith
  rw [neg_div, ← div_neg, lt_div_iff₀ hd]
  linarith

/-! ### Exercise 12.B.2 -/

/-- Profit at price `p` with constant-elasticity demand `x(p) = αp^{-ε}` and unit cost `c`. -/
noncomputable def ceProfit (α ε c p : ℝ) : ℝ := (p - c) * (α * p ^ (-ε))

theorem ceProfit_eq {α ε c p : ℝ} (hp : 0 < p) :
    ceProfit α ε c p = α * (p ^ (1 - ε) - c * p ^ (-ε)) := by
  unfold ceProfit
  have : p ^ (1 - ε) = p ^ (-ε) * p := by
    rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  rw [this]; ring

/-- **Exercise 12.B.2(a)** (MWG, p. 429). With `x(p) = αp^{-ε}`, `0 < ε ≤ 1` and `c > 0`, the
monopolist's optimal price is not well defined: every price is beaten by a higher one. -/
theorem exercise_12_B_2a {α ε c : ℝ} (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) :
    ∀ p, 0 < p → ∃ p', 0 < p' ∧ ceProfit α ε c p < ceProfit α ε c p' := by
  intro p hp
  rcases le_or_gt p c with hpc | hpc
  · refine ⟨c + 1, by linarith, ?_⟩
    unfold ceProfit
    have h1 : 0 < α * (c + 1) ^ (-ε) := mul_pos hα (Real.rpow_pos_of_pos (by linarith) _)
    have h2 : 0 ≤ α * p ^ (-ε) := (mul_pos hα (Real.rpow_pos_of_pos hp _)).le
    nlinarith
  · refine ⟨p + 1, by linarith, ?_⟩
    rw [ceProfit_eq hp, ceProfit_eq (by linarith)]
    have h1 : p ^ (1 - ε) ≤ (p + 1) ^ (1 - ε) :=
      Real.rpow_le_rpow hp.le (by linarith) (by linarith)
    have h2 : (p + 1) ^ (-ε) < p ^ (-ε) :=
      Real.rpow_lt_rpow_of_neg hp (by linarith) (by linarith)
    have h3 := mul_lt_mul_of_pos_left h2 hc
    exact mul_lt_mul_of_pos_left (by linarith) hα

/-- The derivative of the constant-elasticity profit: `α p^{-ε-1}((1 − ε)p + εc)`. -/
theorem ceProfit_hasDerivAt {α ε c p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε)))
      (α * (p ^ (-ε - 1) * ((1 - ε) * p + ε * c))) p := by
  have h1 := Real.hasDerivAt_rpow_const (x := p) (p := 1 - ε) (Or.inl hp.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := p) (p := -ε) (Or.inl hp.ne')
  have h := ((h1.sub (h2.const_mul c)).const_mul α)
  refine h.congr_deriv ?_
  have e1 : p ^ (1 - ε - 1) = p ^ (-ε - 1) * p := by
    rw [show 1 - ε - 1 = -ε - 1 + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  rw [e1]; ring

/-- **Exercise 12.B.2(b)** (MWG, p. 429). With `ε > 1` the optimal price is
`pᵐ = εc/(ε − 1)`: it is the unique maximizer of profit over `p > 0`; the output is
`qᵐ = α(pᵐ)^{-ε}` and the price-cost margin `(pᵐ − c)/pᵐ` is `1/ε`. -/
theorem exercise_12_B_2b {α ε c : ℝ} (hα : 0 < α) (hε : 1 < ε) (hc : 0 < c) :
    (∀ p, 0 < p → p ≠ ε * c / (ε - 1) → ceProfit α ε c p < ceProfit α ε c (ε * c / (ε - 1))) ∧
    (ε * c / (ε - 1) - c) / (ε * c / (ε - 1)) = 1 / ε := by
  set pm := ε * c / (ε - 1) with hpm
  have hε1 : 0 < ε - 1 := by linarith
  have hpm0 : 0 < pm := by positivity
  have hD : ∀ p, 0 < p → (0 < (1 - ε) * p + ε * c ↔ p < pm) := by
    intro p hp
    rw [hpm, lt_div_iff₀ hε1]
    constructor <;> intro h <;> linarith
  have hderiv : ∀ x, 0 < x → HasDerivAt (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε)))
      (α * (x ^ (-ε - 1) * ((1 - ε) * x + ε * c))) x := fun x hx => ceProfit_hasDerivAt hx
  have hcont : ContinuousOn (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε))) (Ioi 0) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε))) (Ioc 0 pm) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc 0 pm)
      (f' := fun x => α * (x ^ (-ε - 1) * ((1 - ε) * x + ε * c)))
      (hcont.mono Ioc_subset_Ioi_self) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioc] at hx; exact (hderiv x hx.1).hasDerivWithinAt
    · rw [interior_Ioc] at hx
      have := (hD x hx.1).2 hx.2
      exact mul_pos hα (mul_pos (Real.rpow_pos_of_pos hx.1 _) this)
  have hanti : StrictAntiOn (fun r => α * (r ^ (1 - ε) - c * r ^ (-ε))) (Ici pm) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici pm)
      (f' := fun x => α * (x ^ (-ε - 1) * ((1 - ε) * x + ε * c)))
      (hcont.mono fun x hx => lt_of_lt_of_le hpm0 hx) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ici] at hx; exact (hderiv x (hpm0.trans hx)).hasDerivWithinAt
    · rw [interior_Ici] at hx
      have hx0 : 0 < x := hpm0.trans hx
      have : ¬ (0 < (1 - ε) * x + ε * c) := fun h => absurd ((hD x hx0).1 h) (not_lt.2 hx.le)
      push Not at this
      have h3 : (1 - ε) * x + ε * c < 0 := by
        rcases eq_or_lt_of_le this with h | h
        · exfalso; have : x = pm := by rw [hpm]; field_simp; linarith
          exact (ne_of_gt hx) this
        · exact h
      exact mul_neg_of_pos_of_neg hα (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hx0 _) h3)
  have hm : ε * c / (ε - 1) - c = c / (ε - 1) := by field_simp; ring
  refine ⟨fun p hp hne => ?_, ?_⟩
  swap
  · rw [hpm, hm, div_div_div_cancel_right₀ hε1.ne', div_mul_cancel_right₀ hc.ne', one_div]
  rw [ceProfit_eq hp, ceProfit_eq hpm0]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hmono ⟨hp, h.le⟩ ⟨hpm0, le_rfl⟩ h
  · exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h

/-- **Exercise 12.B.2(b), the deadweight loss** (MWG, pp. 386 and 429). The inverse demand of
`x(p) = αp^{-ε}` is `p(s) = (s/α)^{-1/ε} = α^{1/ε}s^{-1/ε}`; with `0 < qᵐ < q°` the deadweight loss
`∫_{qᵐ}^{q°} (p(s) − c) ds` equals
`α^{1/ε}((q°)^{1-1/ε} − (qᵐ)^{1-1/ε})/(1 − 1/ε) − c(q° − qᵐ)`. -/
theorem exercise_12_B_2b_dwl {α ε c qm q0 : ℝ} (hα : 0 < α) (hε : 1 < ε) (hqm : 0 < qm)
    (hlt : qm < q0) :
    (∀ s, 0 < s → (s / α) ^ (-(1 / ε)) = α ^ (1 / ε) * s ^ (-(1 / ε))) ∧
    ∫ s in qm..q0, (α ^ (1 / ε) * s ^ (-(1 / ε)) - c) =
      α ^ (1 / ε) * (q0 ^ (1 - 1 / ε) - qm ^ (1 - 1 / ε)) / (1 - 1 / ε) - c * (q0 - qm) := by
  have hε0 : 0 < ε := by linarith
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [Real.div_rpow hs.le hα.le, Real.rpow_neg hs.le, Real.rpow_neg hα.le, div_eq_mul_inv,
      inv_inv, mul_comm]
  have hr : -1 < -(1 / ε) := by
    have : 1 / ε < 1 := by rw [div_lt_one hε0]; exact hε
    linarith
  have hint : IntervalIntegrable (fun s : ℝ => α ^ (1 / ε) * s ^ (-(1 / ε))) MeasureTheory.volume
      qm q0 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlt.le]
    exact continuousOn_const.mul (fun x hx => (Real.continuousAt_rpow_const x _
      (Or.inl (hqm.trans_le hx.1).ne')).continuousWithinAt)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr), intervalIntegral.integral_const,
    smul_eq_mul]
  rw [show -(1 / ε) + 1 = 1 - 1 / ε by ring]
  ring

/-! ### Exercise 12.B.3 -/

/-- The slope of an implicitly defined function: if `G(q(t), t) = 0` near `t₀`, `G` has
derivative `L` at `(q(t₀), t₀)` and `q` has derivative `q'` at `t₀`, then
`G_q q' + G_t = 0`, i.e. `q' = −G_t/G_q`. -/
theorem implicit_slope {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {q : ℝ → ℝ} {q' t₀ : ℝ}
    (hG : HasFDerivAt G L (q t₀, t₀)) (hq : HasDerivAt q q' t₀)
    (hzero : ∀ᶠ t in 𝓝 t₀, G (q t, t) = 0) : L (1, 0) * q' + L (0, 1) = 0 := by
  have hf : HasDerivAt (fun t => (q t, t)) (q', 1) t₀ := hq.prodMk (hasDerivAt_id t₀)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t => (q t, t)) t₀ hG hf
  have h0 : HasDerivAt (G ∘ fun t => (q t, t)) 0 t₀ :=
    (hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq (hzero.mono fun t ht => ht)
  have heq := hcomp.unique h0
  have hsplit : ((q', 1) : ℝ × ℝ) = q' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at heq
  linarith

/-- **Exercise 12.B.3, a cost shift** (MWG, p. 429). Let the monopolist's optimal output `q(φ)`
satisfy the first-order condition `G(q(φ), φ) = 0` near `φ₀`, where
`G(q, φ) = p'(q)q + p(q) − c_q(q, φ)` has partial derivatives `G_q < 0` (second-order
condition) and `G_φ = −c_{qφ}`. Then `q'(φ₀) = −c_{qφ}/G_q · (−1)`, i.e. `G_q q' = c_{qφ}`, and the
price `p(q(φ))` (with `p' < 0`) increases (has positive derivative) iff `c_{qφ} > 0`. -/
theorem exercise_12_B_3_cost {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {q p : ℝ → ℝ}
    {q' φ₀ dp cqφ : ℝ} (hG : HasFDerivAt G L (q φ₀, φ₀)) (hq : HasDerivAt q q' φ₀)
    (hzero : ∀ᶠ φ in 𝓝 φ₀, G (q φ, φ) = 0) (hsoc : L (1, 0) < 0) (hGφ : L (0, 1) = -cqφ)
    (hp : HasDerivAt p dp (q φ₀)) (hdp : dp < 0) :
    L (1, 0) * q' = cqφ ∧ HasDerivAt (fun φ => p (q φ)) (dp * q') φ₀ ∧
      (0 < dp * q' ↔ 0 < cqφ) := by
  have h := implicit_slope hG hq hzero
  have h1 : L (1, 0) * q' = cqφ := by linarith
  refine ⟨h1, hp.comp φ₀ hq, ?_⟩
  constructor
  · intro hpos
    have hq' : q' < 0 := by
      by_contra hge; push Not at hge; nlinarith
    nlinarith
  · intro hpos
    have hq' : q' < 0 := by
      by_contra hge; push Not at hge; nlinarith
    nlinarith

/-- **Exercise 12.B.3, a demand shift** (MWG, p. 429). With `G(q, θ) = P_q(q, θ)q + P(q, θ) − c'(q)`
and `G_q < 0`, the output responds by `q' = −G_θ/G_q`, and the price `P(q(θ), θ)` changes at the
rate `P_θ + P_q q'`; it rises iff `P_θ G_q < P_q G_θ`. -/
theorem exercise_12_B_3_demand {G P : ℝ × ℝ → ℝ} {L M : ℝ × ℝ →L[ℝ] ℝ} {q : ℝ → ℝ}
    {q' θ₀ : ℝ} (hG : HasFDerivAt G L (q θ₀, θ₀)) (hq : HasDerivAt q q' θ₀)
    (hzero : ∀ᶠ θ in 𝓝 θ₀, G (q θ, θ) = 0) (hsoc : L (1, 0) < 0)
    (hP : HasFDerivAt P M (q θ₀, θ₀)) :
    q' = -L (0, 1) / L (1, 0) ∧
    HasDerivAt (fun θ => P (q θ, θ)) (M (1, 0) * q' + M (0, 1)) θ₀ ∧
    (0 < M (1, 0) * q' + M (0, 1) ↔ M (0, 1) * L (1, 0) < M (1, 0) * L (0, 1)) := by
  have h := implicit_slope hG hq hzero
  have hne : L (1, 0) ≠ 0 := hsoc.ne
  have hq'eq : q' = -L (0, 1) / L (1, 0) := by
    rw [eq_div_iff hne]; linarith
  have hf : HasDerivAt (fun t => (q t, t)) (q', 1) θ₀ := hq.prodMk (hasDerivAt_id θ₀)
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t => (q t, t)) θ₀ hP hf
  have hsplit : ((q', 1) : ℝ × ℝ) = q' • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at hcomp
  refine ⟨hq'eq, by rw [mul_comm]; exact hcomp, ?_⟩
  have hval : M (1, 0) * q' + M (0, 1) =
      (M (0, 1) * L (1, 0) - M (1, 0) * L (0, 1)) / L (1, 0) := by
    rw [hq'eq]; field_simp; ring
  rw [hval, lt_div_iff_of_neg hsoc, zero_mul]
  constructor <;> intro h <;> linarith

/-! ### Exercise 12.B.4 -/

/-- **Exercise 12.B.4, constant unit cost** (MWG, p. 429). If `pᵢ` is a monopoly price at unit
cost `cᵢ` and `c₁ < c₂`, then `x(p₂) ≤ x(p₁)` (revealed preference); with demand strictly
decreasing where positive, `p₁ ≤ p₂` whenever `x(p₂) > 0`. -/
theorem exercise_12_B_4_cost (x : ℝ → ℝ) {c₁ c₂ p₁ p₂ : ℝ} (hc : c₁ < c₂)
    (h₁ : ∀ r, (r - c₁) * x r ≤ (p₁ - c₁) * x p₁) (h₂ : ∀ r, (r - c₂) * x r ≤ (p₂ - c₂) * x p₂)
    (hdec : ∀ r s, r < s → 0 < x r → x s < x r) :
    x p₂ ≤ x p₁ ∧ (0 < x p₂ → p₁ ≤ p₂) := by
  have a := h₁ p₂
  have b := h₂ p₁
  have hx : x p₂ ≤ x p₁ := by nlinarith
  refine ⟨hx, fun hpos => ?_⟩
  by_contra hlt
  push Not at hlt
  linarith [hdec p₂ p₁ hlt hpos]

/-- **Exercise 12.B.4, a cost parameter** (MWG, p. 429). Let the cost `C(q, φ)` have strictly
increasing differences: `C(q'', φ) − C(q', φ)` is strictly increasing in `φ` for `q'' > q'`.
If `pᵢ` maximizes `r x(r) − C(x(r), φᵢ)` and `φ₁ < φ₂`, then `x(p₂) ≤ x(p₁)`, and so the monopoly
price is nondecreasing in `φ` (`p₁ ≤ p₂` when `x(p₂) > 0`). In terms of Exercise 12.B.3 the
condition is `c_{qφ} > 0`. -/
theorem exercise_12_B_4_param (x : ℝ → ℝ) (C : ℝ → ℝ → ℝ) {φ₁ φ₂ p₁ p₂ : ℝ} (hφ : φ₁ < φ₂)
    (hinc : ∀ q'' q', q' < q'' → C q'' φ₁ - C q' φ₁ < C q'' φ₂ - C q' φ₂)
    (h₁ : ∀ r, r * x r - C (x r) φ₁ ≤ p₁ * x p₁ - C (x p₁) φ₁)
    (h₂ : ∀ r, r * x r - C (x r) φ₂ ≤ p₂ * x p₂ - C (x p₂) φ₂)
    (hdec : ∀ r s, r < s → 0 < x r → x s < x r) :
    x p₂ ≤ x p₁ ∧ (0 < x p₂ → p₁ ≤ p₂) := by
  have _ := hφ
  have hx : x p₂ ≤ x p₁ := by
    by_contra hlt
    push Not at hlt
    have := hinc (x p₂) (x p₁) hlt
    linarith [h₁ p₂, h₂ p₁]
  refine ⟨hx, fun hpos => ?_⟩
  by_contra hlt
  push Not at hlt
  linarith [hdec p₂ p₁ hlt hpos]

/-! ### Exercise 12.B.6 -/

/-- **Exercise 12.B.6** (MWG, p. 429). Let `p(q)q − c(q)` be concave (antitone derivative) and
let `q° > 0` be efficient, `p(q°) = c'(q°)`. A per-unit subsidy `s` makes `q°` optimal for the
monopolist (who then maximizes `p(q)q − c(q) + sq`) if and only if `s = −p'(q°)q°`. -/
theorem exercise_12_B_6 {p c p' c' : ℝ → ℝ} {q0 : ℝ} (hq0 : 0 < q0)
    (hp : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt p (p' q) (Ici 0) q)
    (hc : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' q) (Ici 0) q)
    (hconc : AntitoneOn (fun q => p' q * q + p q - c' q) (Ici 0)) (heff : p q0 = c' q0)
    (s : ℝ) :
    (∀ q, 0 ≤ q → monopolyProfit p c q + s * q ≤ monopolyProfit p c q0 + s * q0) ↔
      s = -(p' q0 * q0) := by
  have hd : ∀ q ∈ Ici (0 : ℝ), HasDerivWithinAt (fun q => monopolyProfit p c q + s * q)
      (p' q * q + p q - c' q + s) (Ici 0) q := by
    intro q hq
    exact ((hasDerivWithinAt_monopolyProfit (hp q hq) (hc q hq)).add
      ((hasDerivWithinAt_id q (Ici 0)).const_mul s)).congr_deriv (by simp)
  have hanti : AntitoneOn (fun q => p' q * q + p q - c' q + s) (Ici 0) :=
    fun a ha b hb hab => by simpa using hconc ha hb hab
  rw [foc_max_iff hd hanti hq0.le]
  constructor
  · rintro ⟨_, h⟩; have := h hq0; linarith
  · intro hs; refine ⟨by rw [hs]; linarith, fun _ => by rw [hs]; linarith⟩

/-! ### Exercise 12.B.7 -/

/-- The gross benefit `∫₀ˣ (a − s)/θ ds = (ax − x²/2)/θ` of a group with demand `a − θp`. -/
noncomputable def groupBenefit (a θ x : ℝ) : ℝ := (a * x - x ^ 2 / 2) / θ

/-- Marshallian aggregate surplus when men consume `xm`, women `xw` and unit cost is `c`. -/
noncomputable def widgetWelfare (a θm θw c xm xw : ℝ) : ℝ :=
  groupBenefit a θm xm + groupBenefit a θw xw - c * (xm + xw)

/-- **Exercise 12.B.7(a)** (MWG, p. 429). In the competitive equilibrium the price is `c`,
men buy `a − θₘc` and women `a − θ_wc`; this maximizes aggregate surplus. -/
theorem exercise_12_B_7a {a θm θw c : ℝ} (hm : 0 < θm) (hw : 0 < θw) :
    ∀ xm xw, widgetWelfare a θm θw c xm xw ≤
      widgetWelfare a θm θw c (a - θm * c) (a - θw * c) := by
  intro xm xw
  unfold widgetWelfare groupBenefit
  rw [div_add_div _ _ hm.ne' hw.ne', div_add_div _ _ hm.ne' hw.ne', div_sub' (by positivity),
    div_sub' (by positivity), div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg hw.le (sq_nonneg (xm - (a - θm * c))),
    mul_nonneg hm.le (sq_nonneg (xw - (a - θw * c)))]

/-- **Exercise 12.B.7(b)** (MWG, p. 429). Let `θ_w < θₘ` and `Θ = θₘ + θ_w`. On prices
`p ≤ a/θₘ` both groups buy and profit `(p − c)(2a − Θp)` is at most its value at
`p* = (2a + Θc)/(2Θ)`; on `[a/θₘ, a/θ_w]` only women buy and profit `(p − c)(a − θ_wp)` is at most
its value at `(a/θ_w + c)/2`. Hence the profit-maximizing uniform price is `p*` or
`(a/θ_w + c)/2`, and both groups consume when `p* < a/θₘ` and `p*` gives the larger profit. -/
theorem exercise_12_B_7b {a θm θw c : ℝ} (hm : 0 < θm) (hw : 0 < θw) (hθ : θw < θm) :
    (∀ p, (p - c) * (2 * a - (θm + θw) * p) ≤
      ((2 * a + (θm + θw) * c) / (2 * (θm + θw)) - c) *
        (2 * a - (θm + θw) * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))))) ∧
    (∀ p, (p - c) * (a - θw * p) ≤ ((a / θw + c) / 2 - c) * (a - θw * ((a / θw + c) / 2))) ∧
    (∀ p, 0 ≤ p → p ≤ a / θm →
      max (a - θm * p) 0 + max (a - θw * p) 0 = 2 * a - (θm + θw) * p) ∧
    (∀ p, a / θm ≤ p → p ≤ a / θw → max (a - θm * p) 0 + max (a - θw * p) 0 = a - θw * p) := by
  have hΘ : 0 < θm + θw := by linarith
  refine ⟨fun p => ?_, fun p => ?_, fun p hp0 hp => ?_, fun p hp1 hp2 => ?_⟩
  · have key : ((2 * a + (θm + θw) * c) / (2 * (θm + θw)) - c) *
        (2 * a - (θm + θw) * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) -
        (p - c) * (2 * a - (θm + θw) * p) =
        (θm + θw) * (p - (2 * a + (θm + θw) * c) / (2 * (θm + θw))) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg hΘ.le (sq_nonneg (p - (2 * a + (θm + θw) * c) / (2 * (θm + θw))))]
  · have key : ((a / θw + c) / 2 - c) * (a - θw * ((a / θw + c) / 2)) - (p - c) * (a - θw * p) =
        θw * (p - (a / θw + c) / 2) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg hw.le (sq_nonneg (p - (a / θw + c) / 2))]
  · have h1 : 0 ≤ a - θm * p := by
      have := mul_le_mul_of_nonneg_left hp hm.le
      rw [mul_div_cancel₀ _ hm.ne'] at this; linarith
    have h2 : 0 ≤ a - θw * p := by nlinarith
    rw [max_eq_left h1, max_eq_left h2]; ring
  · have h1 : a - θm * p ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hp1 hm.le
      rw [mul_div_cancel₀ _ hm.ne'] at this; linarith
    have h2 : 0 ≤ a - θw * p := by
      have := mul_le_mul_of_nonneg_left hp2 hw.le
      rw [mul_div_cancel₀ _ hw.ne'] at this; linarith
    rw [max_eq_right h1, max_eq_left h2]; ring

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 12.B.7(c)-(d), 12.B.8-12.B.10

MWG, Exercises 12.B.7-12.B.10, pp. 429-430.

* 12.B.7(c): the welfare-maximizing split of a total output `X` between men and women equalizes
  marginal valuations; (d): discrimination charges `(a/θₖ + c)/2`, leaves total output unchanged
  when both groups are served, and then lowers welfare; when the uniform price serves only
  women, discrimination raises welfare.
* 12.B.8: learning by doing: the monopolist's outputs, the planner's outputs (price equals
  marginal cost net of the learning benefit), and the planner's wish for more period-1 output.
* 12.B.9: investment in cost reduction: first-order conditions of the monopolist and of the
  planner, and the first- and second-best comparisons.
* 12.B.10: given its price, a monopolist does not over-provide quality, and under-provides it at
  an interior optimum.
-/

namespace MWG.MarketPower

open Set Filter Topology

/-! ### Exercise 12.B.7(c)-(d) -/

/-- **Exercise 12.B.7(c)** (MWG, p. 429). Of all splits `xₘ + x_w = X`, gross benefit is
maximized at `xₘ* = (Xθₘ − a(θₘ − θ_w))/(θₘ + θ_w)`, where marginal valuations are equal:
`(a − xₘ*)/θₘ = (a − x_w*)/θ_w`; so (with a common cost) this split maximizes welfare. -/
theorem exercise_12_B_7c {a θm θw X : ℝ} (hm : 0 < θm) (hw : 0 < θw) :
    (∀ xm, groupBenefit a θm xm + groupBenefit a θw (X - xm) ≤
      groupBenefit a θm ((X * θm - a * (θm - θw)) / (θm + θw)) +
        groupBenefit a θw (X - (X * θm - a * (θm - θw)) / (θm + θw))) ∧
    (a - (X * θm - a * (θm - θw)) / (θm + θw)) / θm =
      (a - (X - (X * θm - a * (θm - θw)) / (θm + θw))) / θw := by
  have hΘ : 0 < θm + θw := by linarith
  refine ⟨fun xm => ?_, by field_simp; ring⟩
  set s := (X * θm - a * (θm - θw)) / (θm + θw) with hs
  have key : groupBenefit a θm s + groupBenefit a θw (X - s) -
      (groupBenefit a θm xm + groupBenefit a θw (X - xm)) =
      (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by
    unfold groupBenefit; rw [hs]; field_simp; ring
  have : 0 ≤ (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by positivity
  linarith

/-- **Exercise 12.B.7(d)** (MWG, pp. 429-430). With discrimination the monopolist charges
`pₖ = (a/θₖ + c)/2` in each market (each maximizes `(p − c)(a − θₖp)`). If both groups are
served under the uniform price `p* = (2a + Θc)/(2Θ)`, total output is the same,
`(a − θₘc)/2 + (a − θ_wc)/2 = 2a − Θp*`, and aggregate surplus is strictly lower under
discrimination (when `θ_w < θₘ`), since the same output is split with unequal marginal
valuations (compare (c)). -/
theorem exercise_12_B_7d {a θm θw c : ℝ} (ha : 0 < a) (hm : 0 < θm) (hw : 0 < θw) (hθ : θw < θm) :
    (∀ p, (p - c) * (a - θm * p) ≤ ((a / θm + c) / 2 - c) * (a - θm * ((a / θm + c) / 2))) ∧
    (a - θm * ((a / θm + c) / 2)) + (a - θw * ((a / θw + c) / 2)) =
      2 * a - (θm + θw) * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))) ∧
    widgetWelfare a θm θw c (a - θm * ((a / θm + c) / 2)) (a - θw * ((a / θw + c) / 2)) <
      widgetWelfare a θm θw c (a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))))
        (a - θw * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) := by
  have hΘ : 0 < θm + θw := by linarith
  refine ⟨fun p => ?_, by field_simp; ring, ?_⟩
  · have key : ((a / θm + c) / 2 - c) * (a - θm * ((a / θm + c) / 2)) - (p - c) * (a - θm * p) =
        θm * (p - (a / θm + c) / 2) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hm.le (sq_nonneg (p - (a / θm + c) / 2))]
  · set X := (a - θm * ((a / θm + c) / 2)) + (a - θw * ((a / θw + c) / 2)) with hX
    obtain ⟨h1, _⟩ := exercise_12_B_7c (a := a) (X := X) hm hw
    have hsplit : (X * θm - a * (θm - θw)) / (θm + θw) =
        a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))) := by
      rw [hX]; field_simp; ring
    have hsplit2 : X - (a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) =
        a - θw * ((2 * a + (θm + θw) * c) / (2 * (θm + θw))) := by
      rw [hX]; field_simp; ring
    have hdisc : X - (a - θm * ((a / θm + c) / 2)) = a - θw * ((a / θw + c) / 2) := by
      rw [hX]; ring
    unfold widgetWelfare
    have hstrict : groupBenefit a θm (a - θm * ((a / θm + c) / 2)) +
        groupBenefit a θw (X - (a - θm * ((a / θm + c) / 2))) <
        groupBenefit a θm ((X * θm - a * (θm - θw)) / (θm + θw)) +
          groupBenefit a θw (X - (X * θm - a * (θm - θw)) / (θm + θw)) := by
      set s := (X * θm - a * (θm - θw)) / (θm + θw) with hs
      set xm := a - θm * ((a / θm + c) / 2) with hxm
      have key : groupBenefit a θm s + groupBenefit a θw (X - s) -
          (groupBenefit a θm xm + groupBenefit a θw (X - xm)) =
          (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by
        unfold groupBenefit; rw [hs]; field_simp; ring
      have hdiff : xm - s = a * (θm - θw) / (2 * (θm + θw)) := by
        rw [hsplit, hxm]; field_simp; ring
      have hne : xm - s ≠ 0 := by
        rw [hdiff]; have : 0 < θm - θw := by linarith
        positivity
      have : 0 < (θm + θw) / (2 * θm * θw) * (xm - s) ^ 2 := by positivity
      linarith
    rw [hdisc, hsplit, hsplit2] at hstrict
    have hcost : (a - θm * ((a / θm + c) / 2)) + (a - θw * ((a / θw + c) / 2)) =
        (a - θm * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) +
          (a - θw * ((2 * a + (θm + θw) * c) / (2 * (θm + θw)))) := by
      field_simp; ring
    rw [hcost]
    linarith

/-- **Exercise 12.B.7(d), one group served** (MWG, p. 430). If the uniform price serves only
women, discrimination leaves the women's market unchanged (same price `(a/θ_w + c)/2`) and opens
the men's market with `xₘ = (a − θₘc)/2 > 0` units, which adds the strictly positive surplus
`groupBenefit a θₘ xₘ − c xₘ`. -/
theorem exercise_12_B_7d_one_served {a θm c : ℝ} (hm : 0 < θm) (hmc : θm * c < a) :
    0 < groupBenefit a θm (a - θm * ((a / θm + c) / 2)) - c * (a - θm * ((a / θm + c) / 2)) := by
  unfold groupBenefit
  have e : a - θm * ((a / θm + c) / 2) = (a - θm * c) / 2 := by field_simp; ring
  rw [e]
  have h1 : 0 < a - θm * c := by linarith
  rw [show (a * ((a - θm * c) / 2) - ((a - θm * c) / 2) ^ 2 / 2) / θm - c * ((a - θm * c) / 2) =
    3 * (a - θm * c) ^ 2 / (8 * θm) by field_simp; ring]
  positivity

/-! ### Exercise 12.B.8 -/

/-- The monopolist's two-period profit with learning by doing: `c₂ = c₁ − mq₁`. -/
def lbdProfit (a b c1 m q1 q2 : ℝ) : ℝ :=
  (a - b * q1 - c1) * q1 + (a - b * q2 - (c1 - m * q1)) * q2

/-- Two-period aggregate surplus with learning by doing. -/
noncomputable def lbdWelfare (a b c1 m q1 q2 : ℝ) : ℝ :=
  (a * q1 - b * q1 ^ 2 / 2 - c1 * q1) + (a * q2 - b * q2 ^ 2 / 2 - (c1 - m * q1) * q2)

/-- **Exercise 12.B.8(a)** (MWG, p. 430). With `0 < m < b` and `a > c₁`, the monopolist
produces `q₁ = q₂ = (a − c₁)/(2b − m)`; this is its unique optimal plan, and the period-2 output
is the monopoly output `(a − c₂)/(2b)` at the learned cost `c₂ = c₁ − mq₁`. -/
theorem exercise_12_B_8a {a b c1 m : ℝ} (hm : 0 < m) (hmb : m < b) :
    (∀ q1 q2, lbdProfit a b c1 m q1 q2 ≤
      lbdProfit a b c1 m ((a - c1) / (2 * b - m)) ((a - c1) / (2 * b - m))) ∧
    (a - c1) / (2 * b - m) = (a - (c1 - m * ((a - c1) / (2 * b - m)))) / (2 * b) := by
  have hd : 0 < 2 * b - m := by linarith
  have hb : 0 < b := by linarith
  have hd' : 2 * b - m ≠ 0 := hd.ne'
  have hd'' : b * 2 - m ≠ 0 := by linarith
  refine ⟨fun q1 q2 => ?_, by field_simp; ring⟩
  set Q := (a - c1) / (2 * b - m) with hQ
  have key : lbdProfit a b c1 m Q Q - lbdProfit a b c1 m q1 q2 =
      b * (q1 - Q) ^ 2 + b * (q2 - Q) ^ 2 - m * (q1 - Q) * (q2 - Q) := by
    unfold lbdProfit; rw [hQ]; field_simp; ring
  nlinarith [sq_nonneg (q1 - Q - (q2 - Q)), sq_nonneg (q1 - Q + (q2 - Q)),
    mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q1 - Q)),
    mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q2 - Q)), sq_nonneg (q1 - Q), sq_nonneg (q2 - Q)]

/-- **Exercise 12.B.8(b)** (MWG, p. 430). A planner produces `q₁ = q₂ = (a − c₁)/(b − m)`
(maximizing aggregate surplus), and then the period-1 price equals marginal cost net of the
learning benefit, `p(q₁) = c₁ − mq₂`, while the period-2 price equals the period-2 cost
`c₂ = c₁ − mq₁`. -/
theorem exercise_12_B_8b {a b c1 m : ℝ} (hm : 0 < m) (hmb : m < b) :
    (∀ q1 q2, lbdWelfare a b c1 m q1 q2 ≤
      lbdWelfare a b c1 m ((a - c1) / (b - m)) ((a - c1) / (b - m))) ∧
    a - b * ((a - c1) / (b - m)) = c1 - m * ((a - c1) / (b - m)) := by
  have hd : 0 < b - m := by linarith
  have hd' : b - m ≠ 0 := hd.ne'
  refine ⟨fun q1 q2 => ?_, by field_simp; ring⟩
  set Q := (a - c1) / (b - m) with hQ
  have key : lbdWelfare a b c1 m Q Q - lbdWelfare a b c1 m q1 q2 =
      b / 2 * (q1 - Q) ^ 2 + b / 2 * (q2 - Q) ^ 2 - m * (q1 - Q) * (q2 - Q) := by
    unfold lbdWelfare; rw [hQ]; field_simp; ring
  nlinarith [sq_nonneg (q1 - Q - (q2 - Q)), mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q1 - Q)),
    mul_nonneg (sub_nonneg.2 hmb.le) (sq_nonneg (q2 - Q))]

/-- **Exercise 12.B.8(c)** (MWG, p. 430). When the monopolist will choose the period-2 output
`(a − c₂)/(2b)` itself, the planner would like it to raise period-1 output slightly above its
choice `q₁ᵐ = (a − c₁)/(2b − m)`: welfare strictly increases for all small increases `h > 0`.
(Intuition: more period-1 output both raises period-1 surplus, since price exceeds cost, and
lowers `c₂`, which raises the monopolist's period-2 output.) -/
theorem exercise_12_B_8c {a b c1 m : ℝ} (hac : c1 < a) (hm : 0 < m) (hmb : m < b) :
    ∃ ε > 0, ∀ h, 0 < h → h < ε →
      lbdWelfare a b c1 m ((a - c1) / (2 * b - m))
          ((a - (c1 - m * ((a - c1) / (2 * b - m)))) / (2 * b)) <
        lbdWelfare a b c1 m ((a - c1) / (2 * b - m) + h)
          ((a - (c1 - m * ((a - c1) / (2 * b - m) + h))) / (2 * b)) := by
  have hb : 0 < b := by linarith
  have hd : 0 < 2 * b - m := by linarith
  set D := (a - c1) * b / (2 * b - m) * (1 + m / (2 * b)) with hD
  set E := (4 * b ^ 2 - 3 * m ^ 2) / (8 * b) with hE
  have hDpos : 0 < D := by
    rw [hD]; have : 0 < a - c1 := by linarith
    positivity
  have hEpos : 0 < E := by
    rw [hE]; apply div_pos _ (by positivity); nlinarith
  refine ⟨D / E, div_pos hDpos hEpos, fun h hh hε => ?_⟩
  have key : lbdWelfare a b c1 m ((a - c1) / (2 * b - m) + h)
        ((a - (c1 - m * ((a - c1) / (2 * b - m) + h))) / (2 * b)) -
      lbdWelfare a b c1 m ((a - c1) / (2 * b - m))
        ((a - (c1 - m * ((a - c1) / (2 * b - m)))) / (2 * b)) = h * (D - E * h) := by
    unfold lbdWelfare; rw [hD, hE]; field_simp; ring
  have : E * h < D := by rwa [lt_div_iff₀ hEpos, mul_comm] at hε
  have : 0 < h * (D - E * h) := mul_pos hh (by linarith)
  linarith

/-! ### Exercise 12.B.9 -/

/-- **Exercise 12.B.9(a)** (MWG, p. 430). If `(q, I)` with `q, I > 0` maximizes the monopolist's
profit `p(q)q − c(I)q − I` over `q, I ≥ 0`, then marginal revenue equals marginal cost,
`p'(q)q + p(q) = c(I)`, and the marginal cost saving equals the marginal investment cost,
`−c'(I)q = 1`. -/
theorem exercise_12_B_9a {p c : ℝ → ℝ} {dp dc q I : ℝ} (hq : 0 < q) (hI : 0 < I)
    (hp : HasDerivAt p dp q) (hc : HasDerivAt c dc I)
    (hmax : ∀ q' I', 0 ≤ q' → 0 ≤ I' → p q' * q' - c I' * q' - I' ≤ p q * q - c I * q - I) :
    dp * q + p q = c I ∧ -dc * q = 1 := by
  constructor
  · have hloc : IsLocalMax (fun q' => p q' * q' - c I * q' - I) q :=
      Filter.mem_of_superset (Ioi_mem_nhds hq) fun q' hq' => hmax q' I (le_of_lt hq') hI.le
    have hd : HasDerivAt (fun q' => p q' * q' - c I * q' - I) (dp * q + p q * 1 - c I * 1) q :=
      ((hp.mul (hasDerivAt_id q)).sub ((hasDerivAt_id q).const_mul (c I))).sub_const I
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  · have hloc : IsLocalMax (fun I' => p q * q - c I' * q - I') I :=
      Filter.mem_of_superset (Ioi_mem_nhds hI) fun I' hI' => hmax q I' hq.le (le_of_lt hI')
    have hd : HasDerivAt (fun I' => p q * q - c I' * q - I') (0 - dc * q - 1) I :=
      (((hasDerivAt_const I (p q * q)).sub (hc.mul_const q)).sub (hasDerivAt_id I))
    have := hloc.hasDerivAt_eq_zero hd
    linarith

/-- **Exercise 12.B.9(b)** (MWG, p. 430). A first-best planner maximizes
`S(q) − c(I)q − I`, where `S' = p` is gross consumer benefit; at an interior optimum price equals
marginal cost, `p(q) = c(I)`, and `−c'(I)q = 1`. Compared with the monopolist (`p' < 0`): at the
monopolist's choice the planner's marginal welfare of output is `p(qᵐ) − c(Iᵐ) = −p'(qᵐ)qᵐ > 0`,
and since `c'' > 0` (`c'` strictly increasing), more first-best output means more first-best
investment: `qᶠᵇ > qᵐ` implies `Iᶠᵇ > Iᵐ`. -/
theorem exercise_12_B_9b {S p c c' : ℝ → ℝ} {dp qf If qm Im : ℝ} (hqf : 0 < qf) (hIf : 0 < If)
    (hS : HasDerivAt S (p qf) qf) (hc : HasDerivAt c (c' If) If)
    (hmax : ∀ q' I', 0 ≤ q' → 0 ≤ I' → S q' - c I' * q' - I' ≤ S qf - c If * qf - If)
    (hqm : 0 < qm) (hmono : StrictMono c') (hmr : dp * qm + p qm = c Im) (hdp : dp < 0)
    (hinv : -c' Im * qm = 1) :
    p qf = c If ∧ -c' If * qf = 1 ∧ 0 < p qm - c Im ∧ (qm < qf → Im < If) := by
  have h1 : p qf = c If := by
    have hloc : IsLocalMax (fun q' => S q' - c If * q' - If) qf :=
      Filter.mem_of_superset (Ioi_mem_nhds hqf) fun q' hq' => hmax q' If (le_of_lt hq') hIf.le
    have hd : HasDerivAt (fun q' => S q' - c If * q' - If) (p qf - c If * 1) qf :=
      (hS.sub ((hasDerivAt_id qf).const_mul (c If))).sub_const If
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  have h2 : -c' If * qf = 1 := by
    have hloc : IsLocalMax (fun I' => S qf - c I' * qf - I') If :=
      Filter.mem_of_superset (Ioi_mem_nhds hIf) fun I' hI' => hmax qf I' hqf.le (le_of_lt hI')
    have hd : HasDerivAt (fun I' => S qf - c I' * qf - I') (0 - c' If * qf - 1) If :=
      (((hasDerivAt_const If (S qf)).sub (hc.mul_const qf)).sub (hasDerivAt_id If))
    have := hloc.hasDerivAt_eq_zero hd
    linarith
  refine ⟨h1, h2, by nlinarith, fun hlt => ?_⟩
  by_contra hle
  push Not at hle
  have := hmono.monotone hle
  have hcIm : c' Im < 0 := by nlinarith
  nlinarith [mul_lt_mul_of_neg_left hlt hcIm, mul_le_mul_of_nonneg_right this hqf.le]

/-- **Exercise 12.B.9(c)** (MWG, p. 430). Second best: the planner picks `I` and the monopolist
then picks `q(I)` (with `q'(Iᵐ) > 0`). The planner's welfare `V(I) = S(q(I)) − c(I)q(I) − I` has
derivative `(p(qᵐ) − c(Iᵐ))q'(Iᵐ)` at the monopolist's own choice `Iᵐ` (where `−c'(Iᵐ)qᵐ = 1`),
which is positive: the planner would invest more than the monopolist. -/
theorem exercise_12_B_9c {S p c q : ℝ → ℝ} {dc dq Im : ℝ} (hS : HasDerivAt S (p (q Im)) (q Im))
    (hc : HasDerivAt c dc Im) (hq : HasDerivAt q dq Im) (hinv : -dc * q Im = 1)
    (hmarg : c Im < p (q Im)) (hdq : 0 < dq) :
    HasDerivAt (fun I => S (q I) - c I * q I - I) ((p (q Im) - c Im) * dq) Im ∧
      0 < (p (q Im) - c Im) * dq := by
  refine ⟨?_, mul_pos (by linarith) hdq⟩
  have h := ((hS.comp Im hq).sub (hc.mul hq)).sub (hasDerivAt_id Im)
  refine h.congr_deriv ?_
  linear_combination hinv

/-! ### Exercise 12.B.10 -/

/-- **Exercise 12.B.10** (MWG, p. 430). Fix the monopolist's price `p`. Let `CS(q)` be consumer
surplus at quality `q` (strictly increasing in `q`, as `x(p, q)` is increasing in `q`; see
`consumerSurplus_strictMono`) and `π(q)` the profit. If `qᵐ` maximizes `π`, then every
welfare-maximizing quality `qˢ` (maximizing `CS + π`) satisfies `qˢ > qᵐ` or `qˢ = qᵐ`; and if
`CS` has positive derivative at `qᵐ` and `π` has derivative `0` there, `qᵐ` is not
welfare-maximizing: the monopolist does not choose the efficient quality. -/
theorem exercise_12_B_10 {CS π : ℝ → ℝ} {qm qs dCS : ℝ} (hCS : StrictMono CS)
    (hm : ∀ q, π q ≤ π qm) (hs : ∀ q, CS q + π q ≤ CS qs + π qs) :
    qm ≤ qs ∧ (HasDerivAt CS dCS qm → 0 < dCS → HasDerivAt π 0 qm →
      ¬ ∀ q, CS q + π q ≤ CS qm + π qm) := by
  refine ⟨?_, fun hd hpos hπ hmax => ?_⟩
  · by_contra hlt
    push Not at hlt
    have := hCS hlt
    linarith [hs qm, hm qs]
  · have hloc : IsLocalMax (fun q => CS q + π q) qm := Filter.Eventually.of_forall hmax
    have := hloc.hasDerivAt_eq_zero (hd.add hπ)
    linarith

/-- Consumer surplus `∫_p^{p̄} x(s, q) ds` is strictly increasing in quality when `x(s, ·)` is
increasing, strictly at some price in `[p, p̄]`, and `x(·, q)` is continuous. -/
theorem consumerSurplus_strictMono {x : ℝ → ℝ → ℝ} {p pbar q q' : ℝ} (hp : p < pbar)
    (hc : ∀ r, ContinuousOn (fun s => x s r) (Icc p pbar))
    (hle : ∀ s ∈ Ioc p pbar, x s q ≤ x s q') (hlt : ∃ s ∈ Icc p pbar, x s q < x s q') :
    ∫ s in p..pbar, x s q < ∫ s in p..pbar, x s q' :=
  intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hp (hc q) (hc q')
    hle hlt

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 12.B.2(c) and 12.B.5

MWG, Exercises 12.B.2(c) and 12.B.5(a)-(b), p. 429.

* 12.B.2(c): constant-elasticity demand `x(p) = αp^{-ε}`, unit cost `c > 0`, `ε > 1`, with `α`
  adjusted so that the competitive quantity `x(c) = X` is the same for every `ε` (`α = Xc^ε`).
  The deadweight loss is, in closed form,
  `DWL(ε) = Xc(1 − ((ε − 1)/ε)^{ε−1}(2ε − 1)/ε)/(ε − 1)` (`ceDWL`); it equals the book's
  integral `∫_{qᵐ}^{X}(p(s) − c) ds` (`exercise_12_B_2c_derivation`). It is positive, strictly
  DECREASING in `ε` on `(1, ∞)`, tends to `+∞` as `ε → 1⁺` and to `0` as `ε → ∞`, with
  `(ε − 1)DWL(ε) → Xc(1 − 2/e)`. The "computer" part is numerical; two exact values
  (`ε = 2, 3`) are proved.
* 12.B.5 (a verbal "argue" exercise) is formalized with the following models (correction 52).
  The monopolist cannot discern preferences, so it offers ONE menu `M ⊆ ℕ × ℝ` of
  (number of units, total payment) offers to every consumer, always containing the null offer
  `(0, 0)`; any nonlinear price schedule `T` is the menu `{(k, T k)}`, and a single per-unit
  price `p` is the menu `{(k, pk)}`. Unit cost is a constant `c`.
  (a) Unit demand: consumer `i` values one unit at `vᵢ` and further units at zero; each consumer
  picks a utility-maximizing offer. For any menu and any optimal choices there is a per-unit price
  `p ≥ 0` and optimal choices at `p` with at least the same profit (`exercise_12_B_5a`; needs
  `c ≥ 0`).
  (b) Multiple units and costless resale in a competitive resale market: given the resale price
  `ρ`, each consumer chooses an offer from `M` and a final consumption `xᵢ`, trading `xᵢ − kᵢ`
  at `ρ`; the resale market clears. Then the purchases maximize `ρk − T` (arbitrage) and the
  consumptions are the demands at the single price `ρ`, and the profit is at most the profit of
  the single per-unit price `ρ` (`exercise_12_B_5b`). Without resale the claim fails: a bundle
  beats every single price (`exercise_12_B_5b_needs_resale`).
-/

namespace MWG.MarketPower

open Set Filter Topology

/-! ### Exercise 12.B.2(c) -/

/-- The deadweight loss of constant-elasticity monopoly with unit cost `c` and elasticity `ε`
when `α` is chosen so that the competitive quantity `x(c)` equals `X`:
`Xc(1 − ((ε − 1)/ε)^{ε−1}(2ε − 1)/ε)/(ε − 1)`. -/
noncomputable def ceDWL (X c ε : ℝ) : ℝ :=
  X * c * ((1 - ((ε - 1) / ε) ^ (ε - 1) * ((2 * ε - 1) / ε)) / (ε - 1))

/-- The deadweight loss per unit of `Xc`: `ceDWL X c ε = Xc · ceDWLShape ε`. -/
noncomputable def ceDWLShape (ε : ℝ) : ℝ :=
  (1 - ((ε - 1) / ε) ^ (ε - 1) * ((2 * ε - 1) / ε)) / (ε - 1)

theorem ceDWL_eq (X c ε : ℝ) : ceDWL X c ε = X * c * ceDWLShape ε := rfl

/-- **Exercise 12.B.2(c), derivation** (MWG, p. 429). With `α = Xc^ε` the competitive quantity
is `x(c) = X` and the monopoly quantity `qᵐ = α(pᵐ)^{-ε}` (with `pᵐ = εc/(ε − 1)`) is below `X`;
the deadweight loss `∫_{qᵐ}^{X}(p(s) − c) ds`, with inverse demand `p(s) = α^{1/ε}s^{-1/ε}`, is
`ceDWL X c ε`. -/
theorem exercise_12_B_2c_derivation {X c ε : ℝ} (hX : 0 < X) (hc : 0 < c) (hε : 1 < ε) :
    X * c ^ ε * c ^ (-ε) = X ∧ X * c ^ ε * (ε * c / (ε - 1)) ^ (-ε) < X ∧
    ∫ s in (X * c ^ ε * (ε * c / (ε - 1)) ^ (-ε))..X,
      ((X * c ^ ε) ^ (1 / ε) * s ^ (-(1 / ε)) - c) = ceDWL X c ε := by
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  set r := (ε - 1) / ε with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hε0]; linarith
  have hpm : ε * c / (ε - 1) = c / r := by rw [hr]; field_simp
  have hqm : X * c ^ ε * (ε * c / (ε - 1)) ^ (-ε) = X * r ^ ε := by
    rw [hpm, Real.rpow_neg (by positivity), Real.div_rpow hc.le hr0.le]
    have : 0 < c ^ ε := Real.rpow_pos_of_pos hc _
    field_simp
  have hrε : r ^ ε < 1 := Real.rpow_lt_one hr0.le hr1 hε0
  have hcX : X * c ^ ε * c ^ (-ε) = X := by
    rw [mul_assoc, ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, mul_one]
  refine ⟨hcX, ?_, ?_⟩
  · rw [hqm]; nlinarith
  have hα : 0 < X * c ^ ε := mul_pos hX (Real.rpow_pos_of_pos hc _)
  have hqm0 : 0 < X * r ^ ε := mul_pos hX (Real.rpow_pos_of_pos hr0 _)
  rw [hqm, (exercise_12_B_2b_dwl (c := c) hα hε hqm0 (by nlinarith)).2]
  have h1 : (X * c ^ ε) ^ (1 / ε) = X ^ (1 / ε) * c := by
    rw [Real.mul_rpow hX.le (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le,
      mul_one_div_cancel hε0.ne', Real.rpow_one]
  have h2 : (X * r ^ ε) ^ (1 - 1 / ε) = X ^ (1 - 1 / ε) * r ^ (ε - 1) := by
    rw [Real.mul_rpow hX.le (Real.rpow_nonneg hr0.le _), ← Real.rpow_mul hr0.le]
    congr 2; field_simp
  have h3 : X ^ (1 / ε) * X ^ (1 - 1 / ε) = X := by
    rw [← Real.rpow_add hX, show 1 / ε + (1 - 1 / ε) = 1 by ring, Real.rpow_one]
  have h4 : r ^ ε = r ^ (ε - 1) * r := by
    rw [← Real.rpow_add_one hr0.ne', sub_add_cancel]
  unfold ceDWL
  rw [h1, h2, ← hr, h4]
  have h6 : 1 - 1 / ε = (ε - 1) / ε := by field_simp
  rw [h6]
  set R := r ^ (ε - 1)
  have h7 : X ^ (1 / ε) * X ^ ((ε - 1) / ε) = X := by rw [← h6]; exact h3
  rw [hr]
  field_simp
  linear_combination (ε ^ 2 * (1 - R)) * h7

/-- The key bounds behind 12.B.2(c): for `ε > 1` and `y = −(ε − 1) log((ε − 1)/ε)`
(so that `((ε − 1)/ε)^{ε−1} = e^{−y}`), `1 − 1/ε < y < 1`. -/
theorem ceDWL_y_bounds {ε : ℝ} (hε : 1 < ε) :
    1 - ε⁻¹ < -((ε - 1) * Real.log ((ε - 1) / ε)) ∧
      -((ε - 1) * Real.log ((ε - 1) / ε)) < 1 := by
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  have hr0 : 0 < (ε - 1) / ε := by positivity
  have hr1 : (ε - 1) / ε ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hε0.ne'] at h; linarith
  have h1 := Real.log_lt_sub_one_of_pos hr0 hr1
  have hq0 : 0 < ε / (ε - 1) := by positivity
  have hq1 : ε / (ε - 1) ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hε1.ne'] at h; linarith
  have h2 := Real.log_lt_sub_one_of_pos hq0 hq1
  have hL : Real.log ((ε - 1) / ε) = -Real.log (ε / (ε - 1)) := by
    rw [← Real.log_inv, inv_div]
  have e1 : (ε - 1) / ε - 1 = -ε⁻¹ := by field_simp; ring
  have e2 : ε / (ε - 1) - 1 = (ε - 1)⁻¹ := by field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  constructor
  · have : (ε - 1) * ε⁻¹ < (ε - 1) * -Real.log ((ε - 1) / ε) :=
      mul_lt_mul_of_pos_left (by linarith) hε1
    have e3 : (ε - 1) * ε⁻¹ = 1 - ε⁻¹ := by field_simp
    linarith
  · rw [hL]
    have : (ε - 1) * Real.log (ε / (ε - 1)) < (ε - 1) * (ε - 1)⁻¹ :=
      mul_lt_mul_of_pos_left h2 hε1
    rw [mul_inv_cancel₀ hε1.ne'] at this
    linarith

/-- The power in `ceDWL` as an exponential: `((ε − 1)/ε)^{ε−1} = exp(log((ε − 1)/ε)(ε − 1))`. -/
theorem ceDWL_rpow_eq {ε : ℝ} (hε : 1 < ε) :
    ((ε - 1) / ε) ^ (ε - 1) = Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) :=
  Real.rpow_def_of_pos (div_pos (by linarith) (by linarith)) _

/-- `exp(log((ε − 1)/ε)(ε − 1)) · e^{y} = 1` with `y = −(ε − 1) log((ε − 1)/ε)`. -/
theorem ceDWL_exp_mul (ε : ℝ) :
    Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) *
      Real.exp (-((ε - 1) * Real.log ((ε - 1) / ε))) = 1 := by
  rw [← Real.exp_add, show Real.log ((ε - 1) / ε) * (ε - 1) +
    -((ε - 1) * Real.log ((ε - 1) / ε)) = 0 by ring, Real.exp_zero]

/-- **Exercise 12.B.2(c), positivity** (MWG, p. 429). The deadweight loss is positive. -/
theorem ceDWLShape_pos {ε : ℝ} (hε : 1 < ε) : 0 < ceDWLShape ε := by
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  obtain ⟨hlo, -⟩ := ceDWL_y_bounds hε
  set y := -((ε - 1) * Real.log ((ε - 1) / ε))
  set E := Real.exp (Real.log ((ε - 1) / ε) * (ε - 1))
  have hE : E * Real.exp y = 1 := ceDWL_exp_mul ε
  have hE0 : 0 < E := Real.exp_pos _
  have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hεy : ε - 1 < ε * y := by
    have := mul_lt_mul_of_pos_left hlo hε0
    rw [mul_sub, mul_inv_cancel₀ hε0.ne', mul_one] at this
    exact this
  have k1 : E * ε * (y + 1) ≤ E * ε * Real.exp y :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have k2 : E * (2 * ε - 1) < E * (ε * (y + 1)) := mul_lt_mul_of_pos_left (by linarith) hE0
  have key : E * (2 * ε - 1) < ε := by nlinarith
  unfold ceDWLShape
  rw [ceDWL_rpow_eq hε]
  apply div_pos _ hε1
  rw [sub_pos, ← mul_div_assoc, div_lt_one hε0]
  exact key

/-- The derivative of the exponential form of `ceDWLShape` at `x > 1`. -/
theorem ceDWLShape_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun ε => (1 - Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) *
      ((2 * ε - 1) / ε)) / (ε - 1))
      ((Real.exp (Real.log ((x - 1) / x) * (x - 1)) *
        (1 - (2 * x - 1) * ((x - 1) * Real.log ((x - 1) / x))) / x - 1) / (x - 1) ^ 2) x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hg := ((hasDerivAt_id' x).sub_const 1).div (hasDerivAt_id' x) hx0.ne'
  have hL := hg.log (div_pos hx1 hx0).ne'
  have hA := hL.mul ((hasDerivAt_id' x).sub_const 1)
  have hE := hA.exp
  have hB := (((hasDerivAt_id' x).const_mul 2).sub_const 1).div (hasDerivAt_id' x) hx0.ne'
  have hN := (hasDerivAt_const x (1 : ℝ)).sub (hE.mul hB)
  have hF := hN.div ((hasDerivAt_id' x).sub_const 1) hx1.ne'
  refine hF.congr_deriv ?_
  simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

/-- **Exercise 12.B.2(c), monotonicity** (MWG, p. 429). The deadweight loss per unit of `Xc`
is strictly decreasing in `ε` on `(1, ∞)`. -/
theorem ceDWLShape_strictAntiOn : StrictAntiOn ceDWLShape (Ioi 1) := by
  set F := fun ε : ℝ => (1 - Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) *
      ((2 * ε - 1) / ε)) / (ε - 1) with hFdef
  have hEq : ∀ ε, 1 < ε → ceDWLShape ε = F ε := by
    intro ε hε; unfold ceDWLShape; rw [ceDWL_rpow_eq hε]
  have hanti : StrictAntiOn F (Ioi 1) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 1)
      (f' := fun x => (Real.exp (Real.log ((x - 1) / x) * (x - 1)) *
        (1 - (2 * x - 1) * ((x - 1) * Real.log ((x - 1) / x))) / x - 1) / (x - 1) ^ 2)
      (fun x hx => (ceDWLShape_hasDerivAt hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioi] at hx; exact (ceDWLShape_hasDerivAt hx).hasDerivWithinAt
    · rw [interior_Ioi] at hx
      have hx' : 1 < x := hx
      have hx0 : 0 < x := by linarith
      have hx1 : 0 < x - 1 := by linarith
      obtain ⟨-, hhi⟩ := ceDWL_y_bounds hx'
      set L := Real.log ((x - 1) / x)
      set y := -((x - 1) * L)
      set E := Real.exp (L * (x - 1))
      have hE : E * Real.exp y = 1 := ceDWL_exp_mul x
      have hE0 : 0 < E := Real.exp_pos _
      have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
      have k1 : E * x * (y + 1) ≤ E * x * Real.exp y :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have k2 : E * (1 + (2 * x - 1) * y) < E * (x * (y + 1)) := by
        apply mul_lt_mul_of_pos_left _ hE0
        nlinarith
      have key : E * (1 - (2 * x - 1) * ((x - 1) * L)) < x := by
        have : E * (1 - (2 * x - 1) * ((x - 1) * L)) = E * (1 + (2 * x - 1) * y) := by
          simp only [y]; ring
        rw [this]; nlinarith
      apply div_neg_of_neg_of_pos _ (by positivity)
      rw [sub_neg, div_lt_one hx0]
      exact key
  intro a ha b hb hab
  rw [hEq a ha, hEq b hb]
  exact hanti ha hb hab

/-- `(ε − 1) · ceDWLShape ε = 1 − e^{−y}(2ε − 1)/ε` for `ε > 1`, with
`y = −(ε − 1) log((ε − 1)/ε)`. -/
theorem ceDWLShape_scaled_eq {ε : ℝ} (hε : 1 < ε) :
    (ε - 1) * ceDWLShape ε =
      1 - Real.exp (-(-((ε - 1) * Real.log ((ε - 1) / ε)))) * ((2 * ε - 1) / ε) := by
  have hε1 : 0 < ε - 1 := by linarith
  unfold ceDWLShape
  rw [ceDWL_rpow_eq hε, neg_neg, mul_comm (ε - 1) (Real.log _)]
  field_simp

/-- **Exercise 12.B.2(c), the limit `ε → ∞`** (MWG, p. 429): `(ε − 1) · DWL/(Xc) → 1 − 2/e`. -/
theorem ceDWLShape_scaled_tendsto :
    Tendsto (fun ε => (ε - 1) * ceDWLShape ε) atTop (𝓝 (1 - Real.exp (-1) * 2)) := by
  have hlow : Tendsto (fun ε : ℝ => 1 - ε⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      tendsto_inv_atTop_zero
  have hy : Tendsto (fun ε : ℝ => -((ε - 1) * Real.log ((ε - 1) / ε))) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with ε hε using (ceDWL_y_bounds hε).1.le
    · filter_upwards [eventually_gt_atTop 1] with ε hε using (ceDWL_y_bounds hε).2.le
  have hB : Tendsto (fun ε : ℝ => 2 - ε⁻¹) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2)).sub
      tendsto_inv_atTop_zero
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
    (((Real.continuous_exp.tendsto (-1)).comp hy.neg).mul hB)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with ε hε
  have hε0 : 0 < ε := by linarith
  rw [ceDWLShape_scaled_eq hε]
  simp only [Function.comp_apply]
  congr 2
  field_simp

/-- **Exercise 12.B.2(c), the limit `ε → ∞`** (MWG, p. 429): the deadweight loss vanishes. -/
theorem ceDWLShape_tendsto_atTop : Tendsto ceDWLShape atTop (𝓝 0) := by
  have hinv : Tendsto (fun ε : ℝ => (ε - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have h := ceDWLShape_scaled_tendsto.mul hinv
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with ε hε
  have hε1 : 0 < ε - 1 := by linarith
  field_simp

/-- **Exercise 12.B.2(c), the limit `ε → 1⁺`** (MWG, p. 429): the deadweight loss becomes
unbounded. -/
theorem ceDWLShape_tendsto_one : Tendsto ceDWLShape (𝓝[>] 1) atTop := by
  have hsub : Tendsto (fun ε : ℝ => ε - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => ε - 1) (𝓝 1) (𝓝 0) :=
        (continuous_sub_right (1 : ℝ)).tendsto' 1 0 (by norm_num)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Set.mem_Ioi.2 (sub_pos.2 (Set.mem_Ioi.1 hε))
  have hlog : Tendsto (fun ε : ℝ => Real.log ((ε - 1)⁻¹)) (𝓝[>] 1) atTop :=
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hsub)
  have hlow : Tendsto (fun ε : ℝ => (Real.log ((ε - 1)⁻¹) - 1) / 2) (𝓝[>] 1) atTop :=
    (tendsto_atTop_add_const_right _ (-1) hlog).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 1 < ε := hε
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := ceDWL_y_bounds hε'
  set L := Real.log ((ε - 1) / ε)
  set y := -((ε - 1) * L)
  set E := Real.exp (L * (ε - 1))
  have hE : E * Real.exp y = 1 := ceDWL_exp_mul ε
  have hE0 : 0 < E := Real.exp_pos _
  have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hL : L = -Real.log (ε / (ε - 1)) := by
    simp only [L]; rw [← Real.log_inv, inv_div]
  have hlogle : Real.log ((ε - 1)⁻¹) ≤ -L := by
    rw [hL, neg_neg]
    apply Real.log_le_log (by positivity)
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (by positivity) hε'.le
  have hEy : E * (y + 1) ≤ 1 := by nlinarith
  have hB0 : 0 < (2 * ε - 1) / ε := by
    apply div_pos _ hε0; linarith
  -- `(1 + y)(1 − EB) ≥ 1 + y − B = (ε − 1)(−L − 1/ε)`
  have h1 : (y + 1) * (1 - E * ((2 * ε - 1) / ε)) ≥ y + 1 - (2 * ε - 1) / ε := by
    nlinarith [mul_le_mul_of_nonneg_right hEy hB0.le]
  have h2 : y + 1 - (2 * ε - 1) / ε = (ε - 1) * (-L - ε⁻¹) := by
    simp only [y]; field_simp; ring
  have hpos : 0 < -L - ε⁻¹ := by
    have : (ε - 1) * ε⁻¹ < (ε - 1) * -L := by
      have e3 : (ε - 1) * ε⁻¹ = 1 - ε⁻¹ := by field_simp
      rw [e3]; simp only [y] at hlo; linarith
    linarith [lt_of_mul_lt_mul_left this hε1.le]
  have hS : (ε - 1) * ceDWLShape ε = 1 - E * ((2 * ε - 1) / ε) := by
    have e4 : (ε - 1) * Real.log ((ε - 1) / ε) = L * (ε - 1) := by simp only [L]; ring
    rw [ceDWLShape_scaled_eq hε', neg_neg, e4]
  have hinv : ε⁻¹ < 1 := inv_lt_one_of_one_lt₀ hε'
  -- `(y + 1)(ε − 1)·shape ≥ (ε − 1)(−L − 1/ε)` and `y + 1 < 2`
  have h3 : (y + 1) * ceDWLShape ε ≥ -L - ε⁻¹ := by
    have : (ε - 1) * ((y + 1) * ceDWLShape ε) ≥ (ε - 1) * (-L - ε⁻¹) := by
      nlinarith
    exact le_of_mul_le_mul_left this hε1
  have hsh : 0 < ceDWLShape ε := ceDWLShape_pos hε'
  have hy2 : y + 1 < 2 := by linarith
  nlinarith

/-- **Exercise 12.B.2(c)** (MWG, p. 429). Holding the competitive quantity `x(c) = X > 0` fixed
(with `c > 0`), the deadweight loss `ceDWL X c ε` is positive and strictly decreasing in `ε` on
`(1, ∞)`; it tends to `+∞` as `ε → 1⁺` and to `0` as `ε → ∞`, and
`(ε − 1) · DWL(ε) → Xc(1 − 2/e)`. -/
theorem exercise_12_B_2c {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    (∀ ε, 1 < ε → 0 < ceDWL X c ε) ∧ StrictAntiOn (ceDWL X c) (Ioi 1) ∧
    Tendsto (ceDWL X c) (𝓝[>] 1) atTop ∧ Tendsto (ceDWL X c) atTop (𝓝 0) ∧
    Tendsto (fun ε => (ε - 1) * ceDWL X c ε) atTop (𝓝 (X * c * (1 - Real.exp (-1) * 2))) := by
  have hXc : 0 < X * c := mul_pos hX hc
  refine ⟨fun ε hε => ?_, fun a ha b hb hab => ?_, ?_, ?_, ?_⟩
  · rw [ceDWL_eq]; exact mul_pos hXc (ceDWLShape_pos hε)
  · rw [ceDWL_eq, ceDWL_eq]
    exact mul_lt_mul_of_pos_left (ceDWLShape_strictAntiOn ha hb hab) hXc
  · exact ceDWLShape_tendsto_one.const_mul_atTop hXc
  · have h := ceDWLShape_tendsto_atTop.const_mul (X * c)
    rw [mul_zero] at h
    exact h
  · have h := ceDWLShape_scaled_tendsto.const_mul (X * c)
    refine h.congr fun ε => ?_
    rw [ceDWL_eq]; ring

/-- **Exercise 12.B.2(c), a computed value** (MWG, p. 429): at `ε = 2` the deadweight loss is
`Xc/4`. -/
theorem exercise_12_B_2c_eps2 (X c : ℝ) : ceDWL X c 2 = X * c / 4 := by
  unfold ceDWL
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

/-- **Exercise 12.B.2(c), a computed value** (MWG, p. 429): at `ε = 3` the deadweight loss is
`7Xc/54`, below its value `Xc/4` at `ε = 2`. -/
theorem exercise_12_B_2c_eps3 (X c : ℝ) : ceDWL X c 3 = 7 * X * c / 54 := by
  unfold ceDWL
  rw [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
  ring

/-! ### Exercise 12.B.5 -/

/-- The utility of a unit-demand consumer with valuation `v` from the offer `o = (k, t)`
(`k` units for the total payment `t`): `v − t` if `k ≥ 1` and `−t` if `k = 0`. -/
noncomputable def unitUtility (v : ℝ) (o : ℕ × ℝ) : ℝ := (if o.1 = 0 then 0 else v) - o.2

/-- In 12.B.5(a), a per-unit price high enough that nobody buys does at least as well as an
outcome in which every consumer's contribution `tᵢ − ckᵢ` to profit is nonpositive. -/
theorem unitMenu_highPrice {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (o : Fin n → ℕ × ℝ)
    (hle : ∀ i, (o i).2 - c * (o i).1 ≤ 0) :
    ∃ p, 0 ≤ p ∧ ∃ x : Fin n → ℕ,
      (∀ i, ∀ k : ℕ, unitUtility (v i) (k, p * k) ≤ unitUtility (v i) (x i, p * x i)) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (p * x i - c * x i) := by
  have hsum : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg (v i)
  refine ⟨c + ∑ i, |v i|, by linarith, fun _ => 0, fun i k => ?_, ?_⟩
  · have hvi : v i ≤ c + ∑ j, |v j| := by
      have := Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j))
        (Finset.mem_univ i)
      linarith [le_abs_self (v i)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [unitUtility]
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      simp only [unitUtility, hk.ne', ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
      nlinarith
  · simp only [Nat.cast_zero, mul_zero, sub_zero, Finset.sum_const_zero]
    exact Finset.sum_nonpos fun i _ => hle i

/-- The core of 12.B.5(a): if all buyers pay the same `P`, all non-buyers receive the same
`S ≥ 0`, buyers value the good at least at `P + S` and non-buyers at most at `P + S`, then a
single per-unit price does at least as well. -/
theorem unitMenu_core {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (o : Fin n → ℕ × ℝ)
    {P S : ℝ} (hS : 0 ≤ S) (hb : ∀ i, (o i).1 ≠ 0 → (o i).2 = P ∧ P + S ≤ v i)
    (hn : ∀ i, (o i).1 = 0 → (o i).2 = -S ∧ v i ≤ P + S) :
    ∃ p, 0 ≤ p ∧ ∃ x : Fin n → ℕ,
      (∀ i, ∀ k : ℕ, unitUtility (v i) (k, p * k) ≤ unitUtility (v i) (x i, p * x i)) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (p * x i - c * x i) := by
  by_cases hpc : c ≤ P + S
  · refine ⟨P + S, by linarith, fun i => if (o i).1 = 0 then 0 else 1, fun i k => ?_, ?_⟩
    · by_cases hi : (o i).1 = 0
      · obtain ⟨-, hv⟩ := hn i hi
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [unitUtility, hi]
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          simp only [unitUtility, hi, hk.ne', ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
          nlinarith
      · obtain ⟨-, hv⟩ := hb i hi
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp only [unitUtility, hi, ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero,
            Nat.cast_one, mul_one, one_ne_zero]
          linarith
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          simp only [unitUtility, hi, hk.ne', ↓reduceIte, Nat.cast_one, mul_one, one_ne_zero]
          nlinarith
    · refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : (o i).1 = 0
      · obtain ⟨ht, -⟩ := hn i hi
        simp only [hi, ht, ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
        linarith
      · obtain ⟨ht, -⟩ := hb i hi
        have hk1 : (1 : ℝ) ≤ (o i).1 := by exact_mod_cast Nat.pos_of_ne_zero hi
        simp only [hi, ht, ↓reduceIte, Nat.cast_one, mul_one]
        nlinarith
  · push Not at hpc
    refine unitMenu_highPrice v hc o fun i => ?_
    by_cases hi : (o i).1 = 0
    · obtain ⟨ht, -⟩ := hn i hi
      rw [ht, hi]; simp only [Nat.cast_zero, mul_zero, sub_zero]; linarith
    · obtain ⟨ht, -⟩ := hb i hi
      have hk1 : (1 : ℝ) ≤ (o i).1 := by exact_mod_cast Nat.pos_of_ne_zero hi
      rw [ht]; nlinarith

/-- **Exercise 12.B.5(a)** (MWG, p. 429). Many consumers, each wanting at most one unit
(valuation `vᵢ` for one unit, nothing for more), and a monopolist with unit cost `c ≥ 0` who
cannot discern preferences and so offers the same menu `M` of (units, total payment) offers to
everyone, including the null offer `(0, 0)`. Whatever the menu and whatever utility-maximizing
choices the consumers make, there is a per-unit price `p ≥ 0` and utility-maximizing choices
at `p` that give at least the same profit: the monopolist does no better than a single price. -/
theorem exercise_12_B_5a {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (M : Set (ℕ × ℝ))
    (h0 : ((0 : ℕ), (0 : ℝ)) ∈ M) (o : Fin n → ℕ × ℝ)
    (ho : ∀ i, o i ∈ M ∧ ∀ o' ∈ M, unitUtility (v i) o' ≤ unitUtility (v i) (o i)) :
    ∃ p, 0 ≤ p ∧ ∃ x : Fin n → ℕ,
      (∀ i, ∀ k : ℕ, unitUtility (v i) (k, p * k) ≤ unitUtility (v i) (x i, p * x i)) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (p * x i - c * x i) := by
  have hu : ∀ i j, unitUtility (v i) (o j) = (if (o j).1 = 0 then 0 else v i) - (o j).2 :=
    fun _ _ => rfl
  have hu0 : ∀ i, unitUtility (v i) ((0 : ℕ), (0 : ℝ)) = 0 := fun i => by simp [unitUtility]
  by_cases hB : ∃ j, (o j).1 ≠ 0
  · obtain ⟨j, hj⟩ := hB
    have hbuy : ∀ i, (o i).1 ≠ 0 → (o i).2 = (o j).2 := by
      intro i hi
      have h1 := (ho i).2 (o j) (ho j).1
      have h2 := (ho j).2 (o i) (ho i).1
      rw [hu, hu] at h1 h2
      simp only [hi, hj, ↓reduceIte] at h1 h2
      linarith
    by_cases hN : ∃ m, (o m).1 = 0
    · obtain ⟨m, hm⟩ := hN
      have hS : 0 ≤ -(o m).2 := by
        have := (ho m).2 _ h0
        rw [hu0, hu] at this; simp only [hm, ↓reduceIte] at this; linarith
      refine unitMenu_core v hc o hS (fun i hi => ⟨hbuy i hi, ?_⟩) (fun i hi => ⟨?_, ?_⟩)
      · have := (ho i).2 (o m) (ho m).1
        rw [hu, hu] at this; simp only [hm, hi, ↓reduceIte] at this
        rw [hbuy i hi] at this; linarith
      · have h1 := (ho i).2 (o m) (ho m).1
        have h2 := (ho m).2 (o i) (ho i).1
        rw [hu, hu] at h1 h2
        simp only [hi, hm, ↓reduceIte] at h1 h2
        linarith
      · have h2 := (ho i).2 (o j) (ho j).1
        have h3 := (ho m).2 (o i) (ho i).1
        rw [hu, hu] at h2 h3
        simp only [hi, hm, hj, ↓reduceIte] at h2 h3
        linarith
    · push Not at hN
      refine unitMenu_core v hc o le_rfl (fun i hi => ⟨hbuy i hi, ?_⟩)
        (fun i hi => absurd hi (hN i))
      have := (ho i).2 _ h0
      rw [hu0, hu] at this; simp only [hi, ↓reduceIte] at this
      rw [hbuy i hi] at this; linarith
  · push Not at hB
    refine unitMenu_highPrice v hc o fun i => ?_
    have := (ho i).2 _ h0
    rw [hu0, hu] at this; simp only [hB i, ↓reduceIte] at this
    rw [hB i]; simp only [Nat.cast_zero, mul_zero, sub_zero]; linarith

/-- **Exercise 12.B.5(a), an instance** (MWG, p. 429): valuations `3` and `1`, unit cost `1/2`,
the menu `{(0, 0), (1, 2), (2, 3)}`; the first consumer buys one unit for `2`, the second buys
nothing, and these choices are utility-maximizing (so `exercise_12_B_5a` applies). -/
theorem exercise_12_B_5a_instance :
    ∀ i : Fin 2, ![((1 : ℕ), (2 : ℝ)), ((0 : ℕ), (0 : ℝ))] i ∈
        ({(0, 0), (1, 2), (2, 3)} : Set (ℕ × ℝ)) ∧
      ∀ o' ∈ ({(0, 0), (1, 2), (2, 3)} : Set (ℕ × ℝ)),
        unitUtility (![3, 1] i) o' ≤
          unitUtility (![3, 1] i) (![((1 : ℕ), (2 : ℝ)), ((0 : ℕ), (0 : ℝ))] i) := by
  intro i
  fin_cases i
  · refine ⟨by simp, ?_⟩
    rintro o' (rfl | rfl | rfl) <;> norm_num [unitUtility]
  · refine ⟨by simp, ?_⟩
    rintro o' (rfl | rfl | rfl) <;> norm_num [unitUtility]

/-- A resale equilibrium for 12.B.5(b). Consumer `i` has utility `uᵢ(y) − (payment)` from
consuming `y` units. The monopolist offers the same menu `M` of (units, total payment) offers to
everyone. Given the competitive resale price `ρ`, each consumer chooses an offer `oᵢ = (kᵢ, tᵢ)`
from `M` and a final consumption `xᵢ`, selling (or buying) `kᵢ − xᵢ` units costlessly at `ρ`,
to maximize `uᵢ(xᵢ) − tᵢ − ρ(xᵢ − kᵢ)`; the resale market clears, `∑ xᵢ = ∑ kᵢ`. -/
def IsResaleEquilibrium {n : ℕ} (u : Fin n → ℕ → ℝ) (M : Set (ℕ × ℝ)) (ρ : ℝ)
    (o : Fin n → ℕ × ℝ) (x : Fin n → ℕ) : Prop :=
  (∀ i, o i ∈ M ∧ ∀ o' ∈ M, ∀ y : ℕ,
    u i y - o'.2 - ρ * ((y : ℝ) - o'.1) ≤ u i (x i) - (o i).2 - ρ * ((x i : ℝ) - (o i).1)) ∧
  ∑ i, x i = ∑ i, (o i).1

/-- **Exercise 12.B.5(b), costless resale separates purchase from consumption** (MWG, p. 429).
A profile is a resale equilibrium iff every consumer's purchase maximizes its resale value
`ρk − t` over the menu (arbitrage), every consumer's consumption is its demand at the single
per-unit price `ρ`, and the resale market clears. -/
theorem isResaleEquilibrium_iff {n : ℕ} (u : Fin n → ℕ → ℝ) (M : Set (ℕ × ℝ)) (ρ : ℝ)
    (o : Fin n → ℕ × ℝ) (x : Fin n → ℕ) :
    IsResaleEquilibrium u M ρ o x ↔
      (∀ i, o i ∈ M ∧ ∀ o' ∈ M, ρ * o'.1 - o'.2 ≤ ρ * (o i).1 - (o i).2) ∧
      (∀ i, ∀ k : ℕ, u i k - ρ * k ≤ u i (x i) - ρ * x i) ∧ ∑ i, x i = ∑ i, (o i).1 := by
  constructor
  · rintro ⟨h, hcl⟩
    refine ⟨fun i => ⟨(h i).1, fun o' ho' => ?_⟩, fun i k => ?_, hcl⟩
    · have := (h i).2 o' ho' (x i); linarith
    · have := (h i).2 (o i) (h i).1 k; linarith
  · rintro ⟨ha, hd, hcl⟩
    refine ⟨fun i => ⟨(ha i).1, fun o' ho' y => ?_⟩, hcl⟩
    have h1 := (ha i).2 o' ho'
    have h2 := hd i y
    linarith

/-- **Exercise 12.B.5(b)** (MWG, p. 429). Many consumers with arbitrary multi-unit utilities
`uᵢ`, a monopolist with unit cost `c` who cannot discern preferences and offers one menu `M`
(any nonlinear price schedule) containing `(0, 0)`, and costless resale in a competitive resale
market. In any resale equilibrium with resale price `ρ`, the consumptions are the demands at the
single per-unit price `ρ`, and the monopolist's profit is at most the profit `∑ (ρ − c)xᵢ` of
charging the single per-unit price `ρ`. -/
theorem exercise_12_B_5b {n : ℕ} (u : Fin n → ℕ → ℝ) (c : ℝ) (M : Set (ℕ × ℝ))
    (h0 : ((0 : ℕ), (0 : ℝ)) ∈ M) {ρ : ℝ} {o : Fin n → ℕ × ℝ} {x : Fin n → ℕ}
    (heq : IsResaleEquilibrium u M ρ o x) :
    (∀ i, ∀ k : ℕ, u i k - ρ * k ≤ u i (x i) - ρ * x i) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (ρ * x i - c * x i) := by
  obtain ⟨ha, hd, hcl⟩ := (isResaleEquilibrium_iff u M ρ o x).1 heq
  refine ⟨hd, ?_⟩
  have ht : ∀ i, (o i).2 ≤ ρ * (o i).1 := by
    intro i; have := (ha i).2 _ h0; simp only [Nat.cast_zero, mul_zero, sub_zero] at this
    linarith
  have hcl' : ∑ i, ((x i : ℕ) : ℝ) = ∑ i, (((o i).1 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, hcl]
  calc ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (ρ * (o i).1 - c * (o i).1) :=
        Finset.sum_le_sum fun i _ => by linarith [ht i]
    _ = (ρ - c) * ∑ i, (((o i).1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = (ρ - c) * ∑ i, ((x i : ℕ) : ℝ) := by rw [hcl']
    _ = ∑ i, (ρ * x i - c * x i) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- **Exercise 12.B.5(b), an instance** (MWG, p. 429): two consumers, each valuing one unit at
`3` and further units at nothing; the menu `{(0, 0), (1, 3), (2, 5)}` offers a quantity
discount. With resale price `ρ = 5/2` the first consumer buys the bundle of two for `5` and
resells one unit to the second: this is a resale equilibrium, and its profit `5 − 2c` equals the
profit of the single per-unit price `5/2`. -/
theorem exercise_12_B_5b_instance (c : ℝ) :
    IsResaleEquilibrium (fun _ k => if k = 0 then 0 else 3)
      ({(0, 0), (1, 3), (2, 5)} : Set (ℕ × ℝ)) (5 / 2)
      ![((2 : ℕ), (5 : ℝ)), ((0 : ℕ), (0 : ℝ))] ![1, 1] ∧
    ∑ i, ((![((2 : ℕ), (5 : ℝ)), ((0 : ℕ), (0 : ℝ))] i).2 -
      c * (![((2 : ℕ), (5 : ℝ)), ((0 : ℕ), (0 : ℝ))] i).1) =
      ∑ i : Fin 2, ((5 / 2 : ℝ) * (![1, 1] i : ℕ) - c * (![1, 1] i : ℕ)) := by
  refine ⟨(isResaleEquilibrium_iff _ _ _ _ _).2 ⟨fun i => ?_, fun i k => ?_, by decide⟩, ?_⟩
  · fin_cases i
    · refine ⟨by simp, ?_⟩
      rintro o' (rfl | rfl | rfl) <;> norm_num
    · refine ⟨by simp, ?_⟩
      rintro o' (rfl | rfl | rfl) <;> norm_num
  · fin_cases i <;>
    · rcases k with _ | _ | k
      · norm_num
      · norm_num
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        push_cast
        norm_num
        linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  · simp [Fin.sum_univ_two]
    ring

/-- **Exercise 12.B.5(b), the resale market is needed** (MWG, p. 429). Without resale a
nonlinear schedule can beat every single price: one consumer with `u(0) = 0`, `u(1) = 3`,
`u(k) = 4` for `k ≥ 2`, zero cost. The bundle offer `(2, 4)` (with `(0, 0)`) is accepted and
yields profit `4`, while at every per-unit price `p` every utility-maximizing quantity `x`
yields profit `px ≤ 3`. -/
theorem exercise_12_B_5b_needs_resale :
    (∀ o' ∈ ({(0, 0), (2, 4)} : Set (ℕ × ℝ)),
      (fun k : ℕ => if k = 0 then (0 : ℝ) else if k = 1 then 3 else 4) o'.1 - o'.2 ≤
        (if (2 : ℕ) = 0 then (0 : ℝ) else if (2 : ℕ) = 1 then 3 else 4) - 4) ∧
    ∀ p : ℝ, ∀ x : ℕ, (∀ k : ℕ, (if k = 0 then (0 : ℝ) else if k = 1 then 3 else 4) - p * k ≤
      (if x = 0 then (0 : ℝ) else if x = 1 then 3 else 4) - p * x) → p * x ≤ 3 := by
  refine ⟨?_, fun p x hx => ?_⟩
  · rintro o' (rfl | rfl) <;> norm_num
  · have h0 := hx 0
    have h1 := hx 1
    rcases x with _ | _ | x
    · simp
    · norm_num at h0 ⊢; linarith
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.cast_zero,
        mul_zero, sub_zero, Nat.cast_one, mul_one] at h0 h1
      have hx2 : x + 1 + 1 ≠ 1 := by omega
      simp only [hx2, ↓reduceIte] at h0 h1
      push_cast at h0 h1 ⊢
      have hxn : (0 : ℝ) ≤ x := x.cast_nonneg
      nlinarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Bertrand model of price competition

MWG, Section 12.C, pp. 388-389, and Exercises 12.C.1 and 12.C.3.

Firms `j ∈ ι` name prices simultaneously; demand `x(·)` is continuous, nonnegative, strictly
decreasing where positive, zero above some `p̄`, with `x(c) > 0`; each firm has unit cost `c > 0`.
The lowest-priced firms share the market equally: a firm naming the lowest price `p` together
with `J̄ − 1` others sells `x(p)/J̄`; the others sell nothing (`bertrandSales`). For two firms this
is MWG's sales function `x_j(p_j, p_k)` (`bertrandSales_duopoly`). The game is a Chapter 8
`NormalForm` (`bertrandGame`), and equilibrium is Chapter 8's `IsNashEquilibrium`.

* `proposition_12_C_1`: the unique Nash equilibrium of the duopoly is `p₁ = p₂ = c`.
* `exercise_12_C_1`: with `J ≥ 2` firms the lowest price is `c` in every Nash equilibrium, so all
  sales take place at a price equal to cost.
* `exercise_12_C_3a`, `exercise_12_C_3b`: prices on a grid of size `Δ`.

MWG's proof of Proposition 12.C.1 deviates to `p_j − ε` and to `c + (p_k − c)/2`; these give
strictly positive profit only if demand is positive there. The proofs below deviate instead to a
price chosen with the continuity of `(p − c)x(p)` (`bertrand_deviation`), which covers prices
above `p̄`.
-/

namespace MWG.MarketPower

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function Finset

/-- The demand assumptions of the Bertrand model (MWG, p. 388): `x` is continuous, nonnegative,
strictly decreasing at all `p` with `x(p) > 0`, and `x(p) = 0` for `p ≥ p̄`. -/
structure IsBertrandDemand (x : ℝ → ℝ) (pbar : ℝ) : Prop where
  cont : Continuous x
  nonneg : ∀ p, 0 ≤ x p
  strictAnti : ∀ p p', p < p' → 0 < x p' → x p' < x p
  zero : ∀ p, pbar ≤ p → x p = 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sales of firm `j` at the price profile `p` (MWG, pp. 388-389): if `p j` is a lowest price it
sells `x(p j)/J̄`, where `J̄` is the number of firms naming that price; otherwise nothing. -/
noncomputable def bertrandSales (x : ℝ → ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  if ∀ k, p j ≤ p k then x (p j) / ((univ.filter fun k => p k = p j).card : ℝ) else 0

/-- Firm `j`'s profit `(p_j − c)x_j(p)`. -/
noncomputable def bertrandProfit (x : ℝ → ℝ) (c : ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  (p j - c) * bertrandSales x p j

/-- **The Bertrand game** (MWG, p. 388) as a game in normal form. -/
noncomputable def bertrandGame (ι : Type*) [Fintype ι] [DecidableEq ι] (x : ℝ → ℝ) (c : ℝ) :
    NormalForm ι (fun _ => ℝ) where
  payoff j p := bertrandProfit x c p j

/-- **The duopoly sales function** (MWG, p. 388): `x_j = x(p_j)` if `p_j < p_k`, `x(p_j)/2` if
`p_j = p_k`, and `0` if `p_j > p_k`. -/
theorem bertrandSales_duopoly (x : ℝ → ℝ) (p : Fin 2 → ℝ) :
    bertrandSales x p 0 = if p 0 < p 1 then x (p 0) else if p 0 = p 1 then x (p 0) / 2 else 0 := by
  unfold bertrandSales
  rcases lt_trichotomy (p 0) (p 1) with h | h | h
  · have hall : ∀ k, p 0 ≤ p k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (univ.filter fun k => p k = p 0) = {0} := by
      ext k; fin_cases k <;> simp [h.ne']
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · have hall : ∀ k, p 0 ≤ p k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (univ.filter fun k => p k = p 0) = univ := by
      ext k; fin_cases k <;> simp [h]
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · have hn : ¬ ∀ k, p 0 ≤ p k := fun hall => absurd (hall 1) (not_le.2 h)
    simp [hn, h.not_gt, h.ne']

omit [DecidableEq ι] in
theorem bertrandSales_nonneg {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) (p : ι → ℝ) (j : ι) :
    0 ≤ bertrandSales x p j := by
  unfold bertrandSales; split_ifs
  · exact div_nonneg (hx _) (Nat.cast_nonneg _)
  · exact le_rfl

omit [DecidableEq ι] in
theorem bertrandSales_le {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) (p : ι → ℝ) (j : ι) :
    bertrandSales x p j ≤ x (p j) := by
  unfold bertrandSales; split_ifs
  · have h1 : (1 : ℝ) ≤ ((univ.filter fun k => p k = p j).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩
    exact div_le_self (hx _) h1
  · exact hx _

omit [DecidableEq ι] in
/-- A firm naming a strictly lowest price sells the whole demand. -/
theorem bertrandSales_of_lt {x : ℝ → ℝ} {p : ι → ℝ} {j : ι} (h : ∀ k, k ≠ j → p j < p k) :
    bertrandSales x p j = x (p j) := by
  classical
  unfold bertrandSales
  have hall : ∀ k, p j ≤ p k := fun k => by
    by_cases hk : k = j
    · rw [hk]
    · exact (h k hk).le
  have hcard : (univ.filter fun k => p k = p j) = {j} := by
    ext k; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hk; by_contra hne; exact (h k hne).ne' hk
    · rintro rfl; rfl
  simp [hall, hcard]

omit [DecidableEq ι] in
/-- A firm whose price is not a lowest price sells nothing. -/
theorem bertrandSales_of_gt {x : ℝ → ℝ} {p : ι → ℝ} {j k : ι} (h : p k < p j) :
    bertrandSales x p j = 0 := by
  unfold bertrandSales
  have hn : ¬ ∀ k, p j ≤ p k := fun hall => absurd (hall k) (not_le.2 h)
  simp [hn]

/-- The key deviation: for `m > c` there is a price `p' ∈ (c, m)` with
`(p' − c)x(p') > (m − c)x(m)/2`. -/
theorem bertrand_deviation {x : ℝ → ℝ} {pbar c m : ℝ} (hx : IsBertrandDemand x pbar)
    (hxc : 0 < x c) (hm : c < m) :
    ∃ p', c < p' ∧ p' < m ∧ (m - c) * x m / 2 < (p' - c) * x p' := by
  have hg : Continuous fun p => (p - c) * x p := (continuous_id.sub continuous_const).mul hx.cont
  have hgm : 0 ≤ (m - c) * x m := mul_nonneg (by linarith) (hx.nonneg m)
  rcases eq_or_lt_of_le hgm with h0 | hpos
  · -- positive demand just above `c`
    have hev : ∀ᶠ p in nhds c, 0 < x p := hx.cont.continuousAt.eventually (lt_mem_nhds hxc)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set p' := c + min δ (m - c) / 2 with hp'
    have hmin : 0 < min δ (m - c) := lt_min hδ (by linarith)
    have hp'c : c < p' := by rw [hp']; linarith
    have hp'm : p' < m := by rw [hp']; linarith [min_le_right δ (m - c)]
    have hxp : 0 < x p' := hball (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left δ (m - c)])
    refine ⟨p', hp'c, hp'm, ?_⟩
    rw [← h0]; simp only [zero_div]
    exact mul_pos (by linarith) hxp
  · -- continuity at `m`
    have hev : ∀ᶠ p in nhds m, (m - c) * x m / 2 < (p - c) * x p :=
      hg.continuousAt.eventually (lt_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set p' := max (m - δ / 2) ((c + m) / 2) with hp'
    have hp'c : c < p' := by rw [hp']; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hp'm : p' < m := by rw [hp']; exact max_lt (by linarith) (by linarith)
    refine ⟨p', hp'c, hp'm, hball ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (m - δ / 2) ((c + m) / 2)]
    · linarith

omit [DecidableEq ι] in
/-- In a Nash equilibrium no firm earns less than it would from the price `c`... more simply:
at any price at most `c` a firm earns at most `0`. -/
theorem bertrandProfit_le_zero {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) {c : ℝ} {p : ι → ℝ} {j : ι}
    (h : p j ≤ c) : bertrandProfit x c p j ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) (bertrandSales_nonneg hx p j)

omit [DecidableEq ι] in
/-- Profits are nonnegative at prices at least `c`. -/
theorem bertrandProfit_nonneg {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) {c : ℝ} {p : ι → ℝ} {j : ι}
    (h : c ≤ p j) : 0 ≤ bertrandProfit x c p j :=
  mul_nonneg (by linarith) (bertrandSales_nonneg hx p j)

/-- **Exercise 12.C.1** (MWG, p. 389). In the Bertrand model with `J ≥ 2` firms, in any Nash
equilibrium the lowest price is `c`: all sales take place at a price equal to cost (the firms
naming `c` share `x(c) > 0`, the others sell nothing). -/
theorem exercise_12_C_1 {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) (h2 : 2 ≤ Fintype.card ι) {p : ι → ℝ}
    (hne : IsNashEquilibrium (bertrandGame ι x c) p) :
    ∃ j, (∀ k, p j ≤ p k) ∧ p j = c := by
  have _ := hc
  have hnem : (univ : Finset ι).Nonempty := univ_nonempty_iff.2 (by
    rw [← Fintype.card_pos_iff]; omega)
  obtain ⟨j, -, hj⟩ := exists_min_image univ p hnem
  have hjmin : ∀ k, p j ≤ p k := fun k => hj k (mem_univ k)
  refine ⟨j, hjmin, ?_⟩
  set m := p j with hm
  rcases lt_trichotomy m c with hlt | heq | hgt
  · -- the lowest price is below cost: firm `j` sells at a loss
    exfalso
    have hxm : 0 < x m := by
      by_contra h0; push Not at h0
      have := hx.strictAnti m c hlt hxc; linarith [hx.nonneg m]
    have hsales : 0 < bertrandSales x p j := by
      unfold bertrandSales
      split_ifs with hcond
      · exact div_pos hxm (by exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩)
      · exact absurd hjmin hcond
    have hprof : bertrandProfit x c p j < 0 := mul_neg_of_neg_of_pos (by linarith) hsales
    have hdev := hne j c
    have : bertrandProfit x c (update p j c) j ≤ 0 :=
      bertrandProfit_le_zero hx.nonneg (by simp)
    have h0 : (bertrandGame ι x c).payoff j (update p j c) = bertrandProfit x c (update p j c) j :=
      rfl
    have h1 : (bertrandGame ι x c).payoff j p = bertrandProfit x c p j := rfl
    -- deviating to a price above `p̄` gives profit `0`
    have hdev2 := hne j (max pbar c + 1)
    have hz : bertrandProfit x c (update p j (max pbar c + 1)) j = 0 := by
      unfold bertrandProfit
      have : bertrandSales x (update p j (max pbar c + 1)) j = 0 := by
        have hle := bertrandSales_le hx.nonneg (update p j (max pbar c + 1)) j
        have hge := bertrandSales_nonneg hx.nonneg (update p j (max pbar c + 1)) j
        simp only [update_self] at hle
        rw [hx.zero _ (by linarith [le_max_left pbar c])] at hle
        linarith
      rw [this, mul_zero]
    change bertrandProfit x c (update p j (max pbar c + 1)) j ≤ bertrandProfit x c p j at hdev2
    linarith
  · exact heq
  · -- the lowest price exceeds cost: some firm earns at most half of `(m − c)x(m)`
    exfalso
    obtain ⟨p', hp'c, hp'm, hgain⟩ := bertrand_deviation hx hxc hgt
    -- a firm `k` earning at most `(m − c)x(m)/2`
    have hk : ∃ k, bertrandProfit x c p k ≤ (m - c) * x m / 2 := by
      by_cases hall : ∀ k, k ≠ j → p j < p k
      · -- `j` is the unique lowest; another firm earns nothing
        have hcard : 1 < Fintype.card ι := by omega
        obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard j
        refine ⟨k, ?_⟩
        unfold bertrandProfit
        rw [bertrandSales_of_gt (hall k hkj), mul_zero]
        exact div_nonneg (mul_nonneg (by linarith) (hx.nonneg m)) (by norm_num)
      · push Not at hall
        obtain ⟨k, hkj, hpk⟩ := hall
        have hpkm : p k = m := le_antisymm hpk (hjmin k)
        refine ⟨j, ?_⟩
        unfold bertrandProfit bertrandSales
        split_ifs with hcond
        swap
        · exact absurd hjmin hcond
        have h2le : (2 : ℝ) ≤ ((univ.filter fun l => p l = p j).card : ℝ) := by
          have : ({j, k} : Finset ι) ⊆ univ.filter fun l => p l = p j := by
            intro l hl
            simp only [mem_insert, mem_singleton] at hl
            rcases hl with rfl | rfl
            · simp
            · simp [hpkm, hm]
          have hc2 := Finset.card_le_card this
          rw [Finset.card_pair (Ne.symm hkj)] at hc2
          exact_mod_cast hc2
        rw [← hm, mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact div_le_div_of_nonneg_left (hx.nonneg m) (by norm_num) h2le
    obtain ⟨k, hkle⟩ := hk
    have hdev := hne k p'
    change bertrandProfit x c (update p k p') k ≤ bertrandProfit x c p k at hdev
    have hlow : ∀ l, l ≠ k → (update p k p') k < (update p k p') l := by
      intro l hl
      simp only [update_self, update_of_ne hl]
      exact lt_of_lt_of_le hp'm (hjmin l)
    have hval : bertrandProfit x c (update p k p') k = (p' - c) * x p' := by
      unfold bertrandProfit
      rw [bertrandSales_of_lt hlow]
      simp
    linarith

/-- **Proposition 12.C.1** (MWG, p. 388). There is a unique Nash equilibrium `(p₁*, p₂*)` of the
Bertrand duopoly: `p₁* = p₂* = c`. -/
theorem proposition_12_C_1 {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) :
    IsNashEquilibrium (bertrandGame (Fin 2) x c) (fun _ => c) ∧
    ∀ p, IsNashEquilibrium (bertrandGame (Fin 2) x c) p → p = fun _ => c := by
  constructor
  · intro j t
    change bertrandProfit x c (update (fun _ => c) j t) j ≤ bertrandProfit x c (fun _ => c) j
    have h0 : bertrandProfit x c (fun _ : Fin 2 => c) j = 0 := by simp [bertrandProfit]
    rw [h0]
    rcases le_or_gt t c with h | h
    · exact bertrandProfit_le_zero hx.nonneg (by simpa using h)
    · obtain ⟨k, hk⟩ : ∃ k, k ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
      unfold bertrandProfit
      rw [bertrandSales_of_gt (k := k) (by simpa [update_of_ne hk] using h), mul_zero]
  · intro p hne
    obtain ⟨j, hjmin, hj⟩ := exercise_12_C_1 hx hc hxc (by simp) hne
    -- the other firm also names `c`
    obtain ⟨k, hk⟩ : ∃ k, k ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
    have hall : ∀ l, l = j ∨ l = k := by
      intro l; fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
    have hpk : p k = c := by
      by_contra hne'
      have hgt : c < p k := lt_of_le_of_ne (hj ▸ hjmin k) (Ne.symm hne')
      obtain ⟨p', hp'c, hp'k, hgain⟩ := bertrand_deviation hx hxc hgt
      have hdev := hne j p'
      change bertrandProfit x c (update p j p') j ≤ bertrandProfit x c p j at hdev
      have hlow : ∀ l, l ≠ j → (update p j p') j < (update p j p') l := by
        intro l hl
        rcases hall l with rfl | rfl
        · exact absurd rfl hl
        · simp [update_of_ne hl, hp'k]
      have hval : bertrandProfit x c (update p j p') j = (p' - c) * x p' := by
        unfold bertrandProfit; rw [bertrandSales_of_lt hlow]; simp
      have h0 : bertrandProfit x c p j = 0 := by simp [bertrandProfit, hj]
      have : 0 ≤ (p k - c) * x (p k) / 2 :=
        div_nonneg (mul_nonneg (by linarith) (hx.nonneg _)) (by norm_num)
      linarith
    funext l
    rcases hall l with rfl | rfl
    · exact hj
    · exact hpk

/-! ### Exercise 12.C.3: prices on a grid -/

/-- The smallest multiple of `Δ` strictly greater than `c`: `(⌊c/Δ⌋ + 1)Δ`. -/
noncomputable def gridPrice (Δ c : ℝ) : ℝ := (⌊c / Δ⌋ + 1) * Δ

theorem gridPrice_spec {Δ c : ℝ} (hΔ : 0 < Δ) : c < gridPrice Δ c ∧ gridPrice Δ c ≤ c + Δ ∧
    gridPrice Δ c - Δ ≤ c := by
  unfold gridPrice
  have h1 := Int.lt_floor_add_one (c / Δ)
  have h2 := Int.floor_le (c / Δ)
  rw [div_lt_iff₀ hΔ] at h1
  rw [le_div_iff₀ hΔ] at h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The Bertrand duopoly with prices restricted to the multiples `nΔ`, `n ∈ ℤ`
(MWG, Exercise 12.C.3, p. 430). -/
noncomputable def gridBertrandGame (x : ℝ → ℝ) (c Δ : ℝ) : NormalForm (Fin 2) (fun _ => ℤ) where
  payoff j n := bertrandProfit x c (fun k => (n k : ℝ) * Δ) j

/-- **Exercise 12.C.3(a)** (MWG, p. 430). With prices on the grid `Δℤ`, both firms naming
`p̂ = (⌊c/Δ⌋ + 1)Δ`, the smallest multiple of `Δ` above `c`, is a pure strategy Nash
equilibrium. If `x(p̂) > 0`, this strategy is not weakly dominated: against any other grid price
`n'Δ` some rival price makes `p̂` strictly better. -/
theorem exercise_12_C_3a {x : ℝ → ℝ} {pbar c Δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hΔ : 0 < Δ) :
    IsNashEquilibrium (gridBertrandGame x c Δ) (fun _ => ⌊c / Δ⌋ + 1) ∧
    (0 < x (gridPrice Δ c) → ∀ n' : ℤ, n' ≠ ⌊c / Δ⌋ + 1 → ∃ r : ℤ,
      bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then n' else r : ℤ) : ℝ) * Δ) 0 <
      bertrandProfit x c
        (fun k : Fin 2 => ((if k = 0 then ⌊c / Δ⌋ + 1 else r : ℤ) : ℝ) * Δ) 0) := by
  obtain ⟨hgt, -, hle⟩ := gridPrice_spec (c := c) hΔ
  set N : ℤ := ⌊c / Δ⌋ + 1 with hN
  have hNΔ : (N : ℝ) * Δ = gridPrice Δ c := by rw [hN, gridPrice]; push_cast; ring
  constructor
  · intro j t
    change bertrandProfit x c (fun k => ((update (fun _ => N) j t k : ℤ) : ℝ) * Δ) j ≤
      bertrandProfit x c (fun k => ((N : ℤ) : ℝ) * Δ) j
    obtain ⟨k, hk⟩ : ∃ k, k ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
    have hr : bertrandProfit x c (fun _ : Fin 2 => (N : ℝ) * Δ) j =
        ((N : ℝ) * Δ - c) * (x ((N : ℝ) * Δ) / 2) := by
      unfold bertrandProfit; congr 1
      unfold bertrandSales
      simp
    rw [hr]
    have hR : 0 ≤ ((N : ℝ) * Δ - c) * (x ((N : ℝ) * Δ) / 2) :=
      mul_nonneg (by rw [hNΔ]; linarith) (div_nonneg (hx.nonneg _) (by norm_num))
    rcases lt_trichotomy t N with h | h | h
    · -- a lower grid price is at most `c`
      have ht : (t : ℝ) * Δ ≤ c := by
        have : (t : ℝ) ≤ N - 1 := by exact_mod_cast Int.le_sub_one_of_lt h
        have := mul_le_mul_of_nonneg_right this hΔ.le
        rw [hNΔ.symm] at hle
        nlinarith
      exact (bertrandProfit_le_zero hx.nonneg (by simpa using ht)).trans hR
    · have hu : update (fun _ : Fin 2 => N) j t = fun _ => N := by
        funext l; by_cases hl : l = j <;> simp [hl, h]
      rw [hu, ← hr]
    · have ht : (N : ℝ) * Δ < (t : ℝ) * Δ := by
        have : (N : ℝ) < t := by exact_mod_cast h
        nlinarith
      unfold bertrandProfit
      rw [bertrandSales_of_gt (k := k) (by simpa [update_of_ne hk] using ht), mul_zero]
      exact hR
  · intro hxp n' hn'
    rcases lt_or_gt_of_ne hn' with h | h
    · -- `n'Δ ≤ c`: against `p̂`, the price `p̂` earns half the positive profit
      refine ⟨N, ?_⟩
      have hl : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then n' else N : ℤ) : ℝ) * Δ) 0
          ≤ 0 := by
        apply bertrandProfit_le_zero hx.nonneg
        have : (n' : ℝ) ≤ N - 1 := by exact_mod_cast Int.le_sub_one_of_lt h
        have := mul_le_mul_of_nonneg_right this hΔ.le
        rw [hNΔ.symm] at hle
        simp only [ite_true]
        nlinarith
      have hr : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then N else N : ℤ) : ℝ) * Δ) 0 =
          (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) := by
        unfold bertrandProfit bertrandSales
        simp [hNΔ]
      have : 0 < (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) :=
        mul_pos (by linarith) (by positivity)
      linarith
    · -- `n'Δ > p̂`: against `p̂`, the higher price sells nothing
      refine ⟨N, ?_⟩
      have hl : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then n' else N : ℤ) : ℝ) * Δ) 0
          = 0 := by
        unfold bertrandProfit
        rw [bertrandSales_of_gt (k := 1)]
        · ring
        · simp only [ite_true, one_ne_zero, ite_false]
          have : (N : ℝ) < n' := by exact_mod_cast h
          nlinarith
      have hr : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then N else N : ℤ) : ℝ) * Δ) 0 =
          (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) := by
        unfold bertrandProfit bertrandSales
        simp [hNΔ]
      have : 0 < (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) :=
        mul_pos (by linarith) (by positivity)
      linarith

/-- **Exercise 12.C.3(b)** (MWG, p. 430). As `Δ → 0` the equilibrium price `p̂ ∈ (c, c + Δ]`
converges to `c`. -/
theorem exercise_12_C_3b (c : ℝ) :
    Filter.Tendsto (fun Δ => gridPrice Δ c) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  have h1 : Filter.Tendsto (fun Δ : ℝ => c + Δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
    have := (tendsto_const_nhds (x := c) (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).add
      (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ))
        (Filter.tendsto_id (x := nhds (0 : ℝ))))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with Δ hΔ using (gridPrice_spec hΔ).1.le
  · filter_upwards [self_mem_nhdsWithin] with Δ hΔ using (gridPrice_spec hΔ).2.1

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Product differentiation: the linear city

MWG, Example 12.C.2, pp. 396-398.

Consumers of total mass `M` are uniform on `[0, 1]`; firm 1 is at `0`, firm 2 at `1`; buying from
firm `j` at distance `d` costs `p_j + td`. With `v > c + 3t` nobody stays out of the market, and
a consumer at `z` buys from firm 1 iff `p₁ + tz < p₂ + t(1 − z)`, i.e. iff `z < ẑ`
(`linearCity_prefers`), where `ẑ = (t + p₂ − p₁)/(2t)` is the indifferent consumer (12.C.7).
Firm 1's demand is `M` times the clamped `ẑ` (12.C.8) (`lcDemand`).

* `lcBR_mid`, `lcBR_high`, `lcBR_low`: the best-response function (12.C.12), with uniqueness in
  the middle and upper regions.
* `example_12_C_2`: the unique Nash equilibrium is `p₁* = p₂* = c + t`; each firm sells `M/2`
  and earns `tM/2`; there are no asymmetric equilibria.
-/

namespace MWG.MarketPower

/-- The indifferent consumer (12.C.7). -/
noncomputable def lcHat (t p1 p2 : ℝ) : ℝ := (t + p2 - p1) / (2 * t)

/-- **Condition (12.C.7)** (MWG, p. 397). -/
theorem lcHat_spec {t p1 p2 : ℝ} (ht : 0 < t) :
    p1 + t * lcHat t p1 p2 = p2 + t * (1 - lcHat t p1 p2) := by
  unfold lcHat; field_simp; ring

/-- A consumer at `z` strictly prefers firm 1 iff `z < ẑ`. -/
theorem linearCity_prefers {t p1 p2 z : ℝ} (ht : 0 < t) :
    p1 + t * z < p2 + t * (1 - z) ↔ z < lcHat t p1 p2 := by
  unfold lcHat
  rw [lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- **Firm 1's demand (12.C.8)** (MWG, p. 397): `0` if `p₁ > p₂ + t`, `M` if `p₁ < p₂ − t`, and
`(t + p₂ − p₁)M/(2t)` in between. Firm 2's demand (12.C.9) is `lcDemand t M p₂ p₁`. -/
noncomputable def lcDemand (t M p1 p2 : ℝ) : ℝ :=
  if p2 + t < p1 then 0 else if p1 < p2 - t then M else (t + p2 - p1) * M / (2 * t)

/-- The profit `(p_j − c)x_j(p_j, p_{-j})`. -/
noncomputable def lcProfit (t M c pj p : ℝ) : ℝ := (pj - c) * lcDemand t M pj p

/-- The quadratic part of the profit. -/
theorem lcProfit_mid {t M c pj p : ℝ} (h1 : pj ≤ p + t) (h2 : p - t ≤ pj) :
    lcProfit t M c pj p = (pj - c) * ((t + p - pj) * M / (2 * t)) := by
  unfold lcProfit lcDemand
  split_ifs with a b
  · exact absurd a (not_lt.2 h1)
  · exact absurd b (not_lt.2 h2)
  · rfl

theorem lcProfit_low {t M c pj p : ℝ} (ht : 0 < t) (h : pj < p - t) :
    lcProfit t M c pj p = (pj - c) * M := by
  unfold lcProfit lcDemand
  split_ifs with a
  · exfalso; linarith
  · rfl

theorem lcProfit_high {t M c pj p : ℝ} (h : p + t < pj) : lcProfit t M c pj p = 0 := by
  unfold lcProfit lcDemand
  simp only [h, ↓reduceIte, mul_zero]

/-- **Best response, middle region** ((12.C.12), MWG, p. 398). If `p ∈ (c − t, c + 3t)`, the
unique best response is `(t + p + c)/2`, and it earns a strictly positive profit. -/
theorem lcBR_mid {t M c p : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p) (h2 : p < c + 3 * t) :
    0 < lcProfit t M c ((t + p + c) / 2) p ∧
    ∀ pj, pj ≠ (t + p + c) / 2 → lcProfit t M c pj p < lcProfit t M c ((t + p + c) / 2) p := by
  set m := (t + p + c) / 2 with hm
  have hmid := lcProfit_mid (M := M) (c := c) (show m ≤ p + t by rw [hm]; linarith)
    (show p - t ≤ m by rw [hm]; linarith)
  have hpos : 0 < lcProfit t M c m p := by
    rw [hmid]
    apply mul_pos (by rw [hm]; linarith)
    apply div_pos (mul_pos (by rw [hm]; linarith) hM) (by positivity)
  refine ⟨hpos, fun pj hne => ?_⟩
  rcases lt_or_ge (p + t) pj with h | h
  · rw [lcProfit_high h]; exact hpos
  rcases lt_or_ge pj (p - t) with h' | h'
  · -- below `p − t` the profit is `(p_j − c)M < (p − t − c)M ≤ π(m)`
    rw [lcProfit_low ht h']
    have hpt := lcProfit_mid (M := M) (c := c) (show p - t ≤ p + t by linarith) le_rfl
    have key : lcProfit t M c m p - lcProfit t M c (p - t) p = M / (2 * t) * (p - t - m) ^ 2 := by
      rw [hmid, hpt, hm]; field_simp; ring
    have : 0 ≤ M / (2 * t) * (p - t - m) ^ 2 := by positivity
    rw [hpt] at key
    have hlt : (pj - c) * M < (p - t - c) * M := mul_lt_mul_of_pos_right (by linarith) hM
    have e : (p - t - c) * ((t + p - (p - t)) * M / (2 * t)) = (p - t - c) * M := by
      field_simp; ring
    linarith
  · rw [lcProfit_mid h h', hmid]
    have key : (m - c) * ((t + p - m) * M / (2 * t)) - (pj - c) * ((t + p - pj) * M / (2 * t)) =
        M / (2 * t) * (pj - m) ^ 2 := by rw [hm]; field_simp; ring
    have : 0 < M / (2 * t) * (pj - m) ^ 2 := by
      have : pj - m ≠ 0 := sub_ne_zero.2 hne
      positivity
    linarith

/-- **Best response, upper region** ((12.C.12), MWG, p. 398). If `p ≥ c + 3t`, the unique best
response is `p − t` (capturing the whole market), with strictly positive profit. -/
theorem lcBR_high {t M c p : ℝ} (ht : 0 < t) (hM : 0 < M) (h : c + 3 * t ≤ p) :
    0 < lcProfit t M c (p - t) p ∧
    ∀ pj, pj ≠ p - t → lcProfit t M c pj p < lcProfit t M c (p - t) p := by
  have hpt := lcProfit_mid (M := M) (c := c) (show p - t ≤ p + t by linarith) le_rfl
  have hval : lcProfit t M c (p - t) p = (p - t - c) * M := by
    rw [hpt]; field_simp; ring
  have hpos : 0 < lcProfit t M c (p - t) p := by rw [hval]; exact mul_pos (by linarith) hM
  refine ⟨hpos, fun pj hne => ?_⟩
  rcases lt_or_ge (p + t) pj with h1 | h1
  · rw [lcProfit_high h1]; exact hpos
  rcases lt_or_ge pj (p - t) with h2 | h2
  · rw [lcProfit_low ht h2, hval]; exact mul_lt_mul_of_pos_right (by linarith) hM
  · have hgt : p - t < pj := lt_of_le_of_ne h2 (Ne.symm hne)
    rw [lcProfit_mid h1 h2, hval]
    have key : (p - t - c) * M - (pj - c) * ((t + p - pj) * M / (2 * t)) =
        M / (2 * t) * (pj - (p - t)) * (pj - 2 * t - c) := by field_simp; ring
    have : 0 < M / (2 * t) * (pj - (p - t)) * (pj - 2 * t - c) := by
      apply mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
    linarith

/-- **Best response, lower region** ((12.C.12), MWG, p. 398). If `p ≤ c − t`, no price earns a
positive profit, and `p + t` (which sells nothing) is a best response. -/
theorem lcBR_low {t M c p : ℝ} (ht : 0 < t) (hM : 0 < M) (h : p ≤ c - t) :
    lcProfit t M c (p + t) p = 0 ∧ ∀ pj, lcProfit t M c pj p ≤ 0 := by
  refine ⟨?_, fun pj => ?_⟩
  · rw [lcProfit_mid le_rfl (by linarith)]; ring
  rcases lt_or_ge (p + t) pj with h1 | h1
  · rw [lcProfit_high h1]
  rcases lt_or_ge pj (p - t) with h2 | h2
  · rw [lcProfit_low ht h2]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
  · rw [lcProfit_mid h1 h2]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (div_nonneg (mul_nonneg (by linarith) hM.le) (by positivity))

/-- A Nash equilibrium of the linear-city pricing game. -/
def IsLCNash (t M c p1 p2 : ℝ) : Prop :=
  (∀ q, lcProfit t M c q p2 ≤ lcProfit t M c p1 p2) ∧
    ∀ q, lcProfit t M c q p1 ≤ lcProfit t M c p2 p1

/-- **Example 12.C.2** (MWG, pp. 396-398). With `t > 0`, `M > 0`: `p₁* = p₂* = c + t` is a Nash
equilibrium, each firm sells `M/2` and earns `tM/2`, and it is the only Nash equilibrium (there
are no asymmetric equilibria). -/
theorem example_12_C_2 {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    IsLCNash t M c (c + t) (c + t) ∧ lcDemand t M (c + t) (c + t) = M / 2 ∧
    lcProfit t M c (c + t) (c + t) = t * M / 2 ∧
    ∀ p1 p2, IsLCNash t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  have hm : (t + (c + t) + c) / 2 = c + t := by ring
  obtain ⟨_, hbr⟩ := lcBR_mid (M := M) ht hM (show c - t < c + t by linarith)
    (show c + t < c + 3 * t by linarith)
  rw [hm] at hbr
  have hNE : ∀ q, lcProfit t M c q (c + t) ≤ lcProfit t M c (c + t) (c + t) := fun q => by
    by_cases hq : q = c + t
    · rw [hq]
    · exact (hbr q hq).le
  have hdem : lcDemand t M (c + t) (c + t) = M / 2 := by
    unfold lcDemand
    split_ifs with a b
    · exfalso; linarith
    · exfalso; linarith
    · field_simp; ring
  refine ⟨⟨hNE, hNE⟩, hdem, by unfold lcProfit; rw [hdem]; ring, fun p1 p2 hne => ?_⟩
  -- a firm facing a price above `c − t` can earn a positive profit
  have hposprof : ∀ p, c - t < p → ∃ q, 0 < lcProfit t M c q p := by
    intro p hp
    rcases lt_or_ge p (c + 3 * t) with h | h
    · exact ⟨_, (lcBR_mid ht hM hp h).1⟩
    · exact ⟨_, (lcBR_high ht hM h).1⟩
  -- neither price is at most `c − t`
  have hlow : ∀ p p', (∀ q, lcProfit t M c q p' ≤ lcProfit t M c p p') →
      (∀ q, lcProfit t M c q p ≤ lcProfit t M c p' p) → c - t < p' := by
    intro p p' hbr1 hbr2
    by_contra hle
    push Not at hle
    -- the rival's best response sells nothing, so this firm sells `M` at a loss
    have h0 : lcProfit t M c p p' = 0 :=
      le_antisymm ((lcBR_low ht hM hle).2 p) (by
        have := hbr1 (p' + t); rw [(lcBR_low ht hM hle).1] at this; exact this)
    by_cases hp : p' + t < p
    · have : lcProfit t M c p' p = (p' - c) * M := by
        rw [lcProfit_low ht (show p' < p - t by linarith)]
      have hneg : lcProfit t M c p' p < 0 := by
        rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hM
      have hc := hbr2 (p + t + 1)
      rw [lcProfit_high (by linarith)] at hc
      linarith
    · push Not at hp
      rcases eq_or_lt_of_le hp with h3 | h3
      · -- `p = p' + t`: the rival sells everything at `p' < c`
        have : lcProfit t M c p' p = (p' - c) * M := by
          rw [lcProfit_mid (by linarith) (by linarith)]; rw [h3]; field_simp; ring
        have hneg : lcProfit t M c p' p < 0 := by
          rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hM
        have hc := hbr2 (p + t + 1)
        rw [lcProfit_high (by linarith)] at hc
        linarith
      · -- this firm sells a positive amount at a price below `c`
        have hp' : p < c := by linarith
        rcases lt_or_ge p (p' - t) with h2 | h2
        · rw [lcProfit_low ht h2] at h0
          have : (p - c) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
          linarith
        · rw [lcProfit_mid h3.le h2] at h0
          have : (p - c) * ((t + p' - p) * M / (2 * t)) < 0 :=
            mul_neg_of_neg_of_pos (by linarith)
              (div_pos (mul_pos (by linarith) hM) (by positivity))
          linarith
  have h2l := hlow p1 p2 hne.1 hne.2
  have h1l := hlow p2 p1 hne.2 hne.1
  -- neither price is at least `c + 3t`
  have hhigh : ∀ p p', (∀ q, lcProfit t M c q p' ≤ lcProfit t M c p p') →
      (∀ q, lcProfit t M c q p ≤ lcProfit t M c p' p) → c - t < p → p' < c + 3 * t := by
    intro p p' hbr1 hbr2 hp
    by_contra hge
    push Not at hge
    obtain ⟨hpos, huniq⟩ := lcBR_high ht hM hge
    have hpp : p = p' - t := by
      by_contra hne'
      linarith [huniq p hne', hbr1 (p' - t)]
    -- then the rival sells nothing although it could earn a positive profit
    obtain ⟨q, hq⟩ := hposprof p hp
    have : lcProfit t M c p' p = 0 := by
      rw [lcProfit_mid (by linarith) (by linarith), show t + p - p' = 0 by linarith]; ring
    linarith [hbr2 q]
  have h2h := hhigh p1 p2 hne.1 hne.2 h1l
  have h1h := hhigh p2 p1 hne.2 hne.1 h2l
  -- both prices are in the middle region: the unique best responses
  have e1 : p1 = (t + p2 + c) / 2 := by
    by_contra hne'
    linarith [(lcBR_mid ht hM h2l h2h).2 p1 hne', hne.1 ((t + p2 + c) / 2)]
  have e2 : p2 = (t + p1 + c) / 2 := by
    by_contra hne'
    linarith [(lcBR_mid ht hM h1l h1h).2 p2 hne', hne.2 ((t + p1 + c) / 2)]
  constructor <;> linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Infinitely repeated games and Nash reversion

MWG, Appendix A of Chapter 12, pp. 417-421.

The repeated game is Chapter 9's multi-stage game with observed actions (`OSHist`,
`OSProfile`, `osValue`), with the stage-game payoffs `π_i(q)` as per-period payoffs (`stageU`):
a pure strategy maps histories to actions, and `osValue (stageU g) δ σ h i` is player `i`'s
discounted payoff `∑ₙ δⁿ π_i(qₙ)` from history `h`. `IsRepeatedSPNE` is subgame perfection: at
every history no player gains by any change of strategy. For an outcome path `Q`,
`pathValue g δ Q t i = v_i(Q, t) = ∑_τ δ^τ π_i(q_{t+τ})`.

* `osValue_eq_of_rec`: a bounded function satisfying the one-step recursion is the value.
* `stage_nash_spne`: playing a stage Nash equilibrium after every history is an SPNE (p. 418).
* `nashReversion` (Definition 12.AA.1) and `nashReversion_spne_iff`: the Nash reversion profile
  for `Q` is an SPNE iff for all `t`, `i` and all actions `a ≠ q_{it}`,
  `π_i(a, q_{jt}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)` (corrected Lemma 12.AA.1).
* `lemma_12_AA_1_if`: condition (12.AA.1) is sufficient. `counterexample_12_AA`: it is not
  necessary (correction), and in the same game Proposition 12.AA.2 and Exercise 12.AA.1 fail.
* `eq_12_AA_2`, `eq_12_AA_3`: the forms (12.AA.2) and (12.AA.3).
* `proposition_12_AA_2_corrected`: condition (12.AA.1) at `δ` implies it at every `δ' ≥ δ`.
* `proposition_12_AA_3`: Friedman's Nash reversion folk theorem.
* `exercise_12_AA_1_corrected`: a stationary path giving player `i` less than `π_i(q*)` can be
  sustained only if `q_i` is a strict best response to `q_j`.
* `minimax_le_nash`, `minimax_le_spne_value` (p. 421): stage Nash payoffs and SPNE average
  payoffs in every subgame are at least the minimax payoff.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- The stage-game payoffs `π_i(q)` as per-period payoffs of the repeated game. -/
def stageU (g : I → ((i : I) → A i) → ℝ) : I → OSHist A → ((i : I) → A i) → ℝ :=
  fun i _ x => g i x

/-- **Subgame perfection in the repeated game** (MWG, pp. 418, 275). At every history `h`, no
player `i` gains by switching to any other strategy `τ`. -/
def IsRepeatedSPNE (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (σ : OSProfile A) : Prop :=
  ∀ i (τ : OSHist A → A i) h, osValue (stageU g) δ (update σ i τ) h i ≤ osValue (stageU g) δ σ h i

omit [DecidableEq I] in
/-- **Values from a recursion.** If `V` is bounded and satisfies
`V(h) = u_i(h, σ(h)) + δV(σ(h) :: h)`, then `V` is player `i`'s continuation payoff. -/
theorem osValue_eq_of_rec {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M B : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (i : I) (V : OSHist A → ℝ)
    (hV : ∀ h, |V h| ≤ B) (hrec : ∀ h, V h = u i h (osPlay σ h) + δ * V (osPlay σ h :: h))
    (h : OSHist A) : osValue u δ σ h i = V h := by
  set K := M / (1 - δ) + B with hK
  have hD : ∀ n : ℕ, ∀ h, |osValue u δ σ h i - V h| ≤ δ ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add (osValue_abs_le hδ0 hδ1 hu σ h i) (hV h))
    | succ n ih =>
      intro h
      rw [osValue_succ hδ0 hδ1 hu σ h i, hrec h]
      have : u i h (osPlay σ h) + δ * osValue u δ σ (osPlay σ h :: h) i -
          (u i h (osPlay σ h) + δ * V (osPlay σ h :: h)) =
          δ * (osValue u δ σ (osPlay σ h :: h) i - V (osPlay σ h :: h)) := by ring
      rw [this, abs_mul, abs_of_nonneg hδ0, pow_succ]
      calc δ * |osValue u δ σ (osPlay σ h :: h) i - V (osPlay σ h :: h)|
          ≤ δ * (δ ^ n * K) := mul_le_mul_of_nonneg_left (ih _) hδ0
        _ = δ ^ n * δ * K := by ring
  have ht : Tendsto (fun n : ℕ => δ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const K
  have h0 : |osValue u δ σ h i - V h| ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun n => hD n h)
  have := abs_nonpos_iff.1 h0
  linarith

omit [DecidableEq I] in
theorem stageU_bound {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) :
    ∀ i h x, |stageU g i h x| ≤ M := fun i _ x => hg i x

/-! ### Outcome paths -/

/-- Player `i`'s discounted payoff `v_i(Q, t) = ∑_τ δ^τ π_i(q_{t+τ})` from period `t` of the
outcome path `Q` (MWG, p. 418). -/
noncomputable def pathValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (Q : ℕ → (i : I) → A i)
    (t : ℕ) (i : I) : ℝ :=
  ∑' n : ℕ, δ ^ n * g i (Q (t + n))

omit [DecidableEq I] in
theorem pathValue_summable {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (t : ℕ) (i : I) :
    Summable fun n : ℕ => δ ^ n * g i (Q (t + n)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M)
    fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
  exact mul_le_mul_of_nonneg_left (hg _ _) (pow_nonneg hδ0 n)

omit [DecidableEq I] in
/-- `v_i(Q, t) = π_i(q_t) + δv_i(Q, t + 1)`. -/
theorem pathValue_succ {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (t : ℕ) (i : I) :
    pathValue g δ Q t i = g i (Q t) + δ * pathValue g δ Q (t + 1) i := by
  unfold pathValue
  rw [(pathValue_summable hδ0 hδ1 hg Q t i).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, pow_succ]
  congr 1
  refine tsum_congr fun n => ?_
  rw [show t + (n + 1) = t + 1 + n by ring]
  ring

omit [DecidableEq I] in
theorem pathValue_abs_le {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (t : ℕ) (i : I) :
    |pathValue g δ Q t i| ≤ M / (1 - δ) := by
  have hs := pathValue_summable hδ0 hδ1 hg Q t i
  have hgeo := (summable_geometric_of_lt_one hδ0 hδ1).mul_right M
  have hle : ∀ n : ℕ, |δ ^ n * g i (Q (t + n))| ≤ δ ^ n * M := by
    intro n
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
    exact mul_le_mul_of_nonneg_left (hg _ _) (pow_nonneg hδ0 n)
  have h1 : |pathValue g δ Q t i| ≤ ∑' n : ℕ, δ ^ n * M := by
    unfold pathValue
    rw [abs_le]
    constructor
    · rw [← tsum_neg]
      exact hgeo.neg.tsum_le_tsum (fun n => neg_le_of_abs_le (hle n)) hs
    · exact hs.tsum_le_tsum (fun n => le_of_abs_le (hle n)) hgeo
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at h1
  rw [div_eq_inv_mul]
  exact h1

omit [DecidableEq I] in
/-- A constant path gives `v_i = π_i(q)/(1 − δ)`. -/
theorem pathValue_const (g : I → ((i : I) → A i) → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (q : (i : I) → A i) (t : ℕ) (i : I) :
    pathValue g δ (fun _ => q) t i = g i q / (1 - δ) := by
  unfold pathValue
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1, div_eq_inv_mul]

/-- The history consisting of the first `n` profiles of the path `Q` (most recent first). -/
def pathHist (Q : ℕ → (i : I) → A i) : ℕ → OSHist A
  | 0 => []
  | n + 1 => Q n :: pathHist Q n

omit [DecidableEq I] in
theorem pathHist_length (Q : ℕ → (i : I) → A i) (n : ℕ) : (pathHist Q n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathHist, ih]

omit [DecidableEq I] in
/-- Once play has left the path, it never returns. -/
theorem not_pathHist_cons {Q : ℕ → (i : I) → A i} {h : OSHist A} (hh : h ≠ pathHist Q h.length)
    (x : (i : I) → A i) : x :: h ≠ pathHist Q (x :: h).length := by
  intro heq
  simp only [List.length_cons, pathHist] at heq
  exact hh (List.cons.inj heq).2

open Classical in
/-- **Definition 12.AA.1** (MWG, p. 418). The Nash reversion profile for the outcome path `Q`:
play `q_t` in period `t` as long as play has followed `Q`, and the stage Nash equilibrium `q*`
after any deviation. -/
noncomputable def nashReversion (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i) : OSProfile A :=
  fun i h => if h = pathHist Q h.length then Q h.length i else qs i

omit [DecidableEq I] in
theorem osPlay_nashReversion_on {Q : ℕ → (i : I) → A i} {qs : (i : I) → A i} (t : ℕ) :
    osPlay (nashReversion Q qs) (pathHist Q t) = Q t := by
  funext i
  simp [osPlay, nashReversion, pathHist_length]

omit [DecidableEq I] in
theorem osPlay_nashReversion_off {Q : ℕ → (i : I) → A i} {qs : (i : I) → A i} {h : OSHist A}
    (hh : h ≠ pathHist Q h.length) : osPlay (nashReversion Q qs) h = qs := by
  funext i
  simp [osPlay, nashReversion, hh]

/-- A pure strategy Nash equilibrium of the stage game. -/
def IsStageNash (g : I → ((i : I) → A i) → ℝ) (qs : (i : I) → A i) : Prop :=
  ∀ i a, g i (update qs i a) ≤ g i qs

open Classical in
/-- The value of the Nash reversion profile: `v_i(Q, t)` on the path and `π_i(q*)/(1 − δ)` off
it. -/
noncomputable def nashReversionValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ)
    (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i) (i : I) (h : OSHist A) : ℝ :=
  if h = pathHist Q h.length then pathValue g δ Q h.length i else g i qs / (1 - δ)

omit [DecidableEq I] in
theorem nashReversionValue_on (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (Q : ℕ → (i : I) → A i)
    (qs : (i : I) → A i) (i : I) (t : ℕ) :
    nashReversionValue g δ Q qs i (pathHist Q t) = pathValue g δ Q t i := by
  simp [nashReversionValue, pathHist_length]

omit [DecidableEq I] in
theorem nashReversionValue_off (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) {Q : ℕ → (i : I) → A i}
    (qs : (i : I) → A i) (i : I) {h : OSHist A} (hh : h ≠ pathHist Q h.length) :
    nashReversionValue g δ Q qs i h = g i qs / (1 - δ) := by
  simp [nashReversionValue, hh]

omit [DecidableEq I] in
theorem pathHist_succ_eq (Q : ℕ → (i : I) → A i) (t : ℕ) :
    Q t :: pathHist Q t = pathHist Q (t + 1) := rfl

omit [DecidableEq I] in
theorem update_cons_off [DecidableEq I] {Q : ℕ → (i : I) → A i} {t : ℕ} {i : I} {a : A i}
    (ha : a ≠ Q t i) :
    update (Q t) i a :: pathHist Q t ≠ pathHist Q (update (Q t) i a :: pathHist Q t).length := by
  simp only [List.length_cons, pathHist_length, pathHist]
  intro heq
  have := congrFun (List.cons.inj heq).1 i
  simp only [update_self] at this
  exact ha this

omit [DecidableEq I] in
theorem osValue_nashReversion {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i)
    (i : I) (h : OSHist A) :
    osValue (stageU g) δ (nashReversion Q qs) h i = nashReversionValue g δ Q qs i h := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg i qs)
  refine osValue_eq_of_rec hδ0 hδ1 (stageU_bound hg) _ i _ (B := M / (1 - δ)) (fun h => ?_)
    (fun h => ?_) h
  · unfold nashReversionValue
    split_ifs
    · exact pathValue_abs_le hδ0 hδ1 hg Q _ i
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - δ)]
      exact div_le_div_of_nonneg_right (hg i qs) (by linarith)
  · by_cases hh : h = pathHist Q h.length
    · set t := h.length
      rw [hh, osPlay_nashReversion_on, nashReversionValue_on, pathHist_succ_eq,
        nashReversionValue_on]
      exact pathValue_succ hδ0 hδ1 hg Q t i
    · rw [osPlay_nashReversion_off hh, nashReversionValue_off g δ qs i hh,
        nashReversionValue_off g δ qs i (not_pathHist_cons hh qs)]
      simp only [stageU]
      have : (1 - δ) ≠ 0 := by linarith
      field_simp
      ring

/-- **Lemma 12.AA.1, corrected** (MWG, p. 418). Let `q*` be a stage Nash equilibrium and payoffs
be bounded. The Nash reversion profile for `Q` is an SPNE if and only if, for every period `t`,
player `i`, and action `a ≠ q_{it}`,
`π_i(a, q_{-i,t}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)`.
(MWG's condition (12.AA.1) uses the best-response payoff `br_i(q_{jt})`, which also counts
`a = q_{it}`; see `counterexample_12_AA`.) -/
theorem nashReversion_spne_iff {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs) :
    IsRepeatedSPNE g δ (nashReversion Q qs) ↔
      ∀ t i (a : A i), a ≠ Q t i →
        g i (update (Q t) i a) + δ * (g i qs / (1 - δ)) ≤ pathValue g δ Q t i := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hval := osValue_nashReversion hδ0 hδ1 hg Q qs
  rw [IsRepeatedSPNE, oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound hg)]
  simp only [hval, stageU]
  constructor
  · intro hos t i a ha
    have := hos i (pathHist Q t) a
    rw [osPlay_nashReversion_on, nashReversionValue_off g δ qs i (update_cons_off ha),
      nashReversionValue_on] at this
    exact this
  · intro hcond i h a
    by_cases hh : h = pathHist Q h.length
    · set t := h.length
      rw [hh, osPlay_nashReversion_on, nashReversionValue_on]
      by_cases ha : a = Q t i
      · subst ha
        rw [update_eq_self, pathHist_succ_eq, nashReversionValue_on,
          pathValue_succ hδ0 hδ1 hg Q t i]
      · rw [nashReversionValue_off g δ qs i (update_cons_off ha)]
        exact hcond t i a ha
    · rw [osPlay_nashReversion_off hh, nashReversionValue_off g δ qs i hh,
        nashReversionValue_off g δ qs i (not_pathHist_cons hh _)]
      have := hqs i a
      have hne : (1 - δ) ≠ 0 := by linarith
      have h2 : g i qs / (1 - δ) = g i qs + δ * (g i qs / (1 - δ)) := by field_simp; ring
      linarith

/-- **The stage Nash equilibrium repeated** (MWG, p. 418). Playing a stage Nash equilibrium `q*`
in every period regardless of history is an SPNE for every `δ ∈ [0, 1)`. -/
theorem stage_nash_spne {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) {qs : (i : I) → A i} (hqs : IsStageNash g qs) :
    IsRepeatedSPNE g δ (nashReversion (fun _ => qs) qs) := by
  rw [nashReversion_spne_iff hδ0 hδ1 hg _ hqs]
  intro t i a _
  rw [pathValue_const g hδ0 hδ1]
  have := hqs i a
  have hne : (1 - δ) ≠ 0 := by linarith
  have h2 : g i qs / (1 - δ) = g i qs + δ * (g i qs / (1 - δ)) := by
    field_simp; ring
  linarith

/-- The best-response payoff `br_i(q_{-i}) = sup_a π_i(a, q_{-i})` (MWG, p. 417). -/
noncomputable def bestReplyValue (g : I → ((i : I) → A i) → ℝ) (i : I) (x : (i : I) → A i) : ℝ :=
  ⨆ a : A i, g i (update x i a)

theorem le_bestReplyValue {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M)
    (i : I) (x : (i : I) → A i) (a : A i) : g i (update x i a) ≤ bestReplyValue g i x :=
  le_ciSup (f := fun a => g i (update x i a)) ⟨M, fun _ ⟨_, hb⟩ => hb ▸ (le_abs_self _).trans
    (hg i _)⟩ a

/-- **Lemma 12.AA.1, the "if" part** (MWG, p. 418, condition (12.AA.1)). If
`br_i(q_{jt}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)` for all `t` and `i`, the Nash reversion profile for
`Q` is an SPNE. -/
theorem lemma_12_AA_1_if {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs)
    (h12AA1 : ∀ t i, bestReplyValue g i (Q t) + δ / (1 - δ) * g i qs ≤ pathValue g δ Q t i) :
    IsRepeatedSPNE g δ (nashReversion Q qs) := by
  rw [nashReversion_spne_iff hδ0 hδ1 hg Q hqs]
  intro t i a _
  have h1 := le_bestReplyValue hg i (Q t) a
  have h2 := h12AA1 t i
  have : δ * (g i qs / (1 - δ)) = δ / (1 - δ) * g i qs := by ring
  linarith

omit [DecidableEq I] in
/-- **Condition (12.AA.2)** (MWG, p. 419): (12.AA.1) rewritten as
`br_i(q_{jt}) − π_i(q_t) ≤ δ(v_i(Q, t + 1) − π_i(q*)/(1 − δ))`. -/
theorem eq_12_AA_2 {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i)
    (t : ℕ) (i : I) (br : ℝ) :
    br + δ / (1 - δ) * g i qs ≤ pathValue g δ Q t i ↔
      br - g i (Q t) ≤ δ * (pathValue g δ Q (t + 1) i - g i qs / (1 - δ)) := by
  rw [pathValue_succ hδ0 hδ1 hg Q t i]
  have : δ / (1 - δ) * g i qs = δ * (g i qs / (1 - δ)) := by ring
  rw [this]
  constructor <;> intro h <;> linarith

omit [DecidableEq I] in
/-- **Condition (12.AA.3)** (MWG, p. 419): for a stationary path `q, q, …`, (12.AA.1) reads
`br_i(q_j) − π_i(q) ≤ δ/(1 − δ)[π_i(q) − π_i(q*)]`. -/
theorem eq_12_AA_3 (g : I → ((i : I) → A i) → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (q qs : (i : I) → A i) (t : ℕ) (i : I) (br : ℝ) :
    br + δ / (1 - δ) * g i qs ≤ pathValue g δ (fun _ => q) t i ↔
      br - g i q ≤ δ / (1 - δ) * (g i q - g i qs) := by
  rw [pathValue_const g hδ0 hδ1]
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have : g i q / (1 - δ) = g i q + δ / (1 - δ) * g i q := by field_simp; ring
  rw [this]
  constructor <;> intro h <;> linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Nash reversion: Propositions 12.AA.2-12.AA.3, Exercise 12.AA.1, minimax payoffs

MWG, Appendix A of Chapter 12, pp. 419-421.

* `counterexample_12_AA`: a stage game with the unique Nash equilibrium `q* = (D, L)` and the
  stationary path `q = (U, R)`, where player 1 gets `1 < 2 = π₁(q*)`. Its Nash reversion profile
  is an SPNE at `δ = 1/2`, although (12.AA.1) fails there (so Lemma 12.AA.1's "only if" is false),
  and it is not an SPNE at `δ' = 3/5 > 1/2` (so Proposition 12.AA.2 is false), and it is a
  stationary SPNE path giving player 1 less than `π₁(q*)` (so Exercise 12.AA.1 is false).
* `proposition_12_AA_2_corrected`: if (12.AA.1) holds at `δ > 0`, it holds at every
  `δ' ∈ [δ, 1)`, so `Q` is then sustained at `δ'` too.
* `proposition_12_AA_3`: Friedman's Nash reversion folk theorem.
* `exercise_12_AA_1_corrected`, `exercise_12_AA_1_printed_condition`.
* `minimax_le_nash`, `minimax_le_spne_value`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

/-! ### The counterexample -/

/-- Player 1's stage payoffs (`true` = U, L; `false` = D, R): `(U,L) ↦ 0`, `(U,R) ↦ 1`,
`(D,L) ↦ 2`, `(D,R) ↦ 0`. -/
def cexG0 : Bool → Bool → ℝ
  | true, true => 0
  | true, false => 1
  | false, true => 2
  | false, false => 0

/-- Player 2's stage payoffs: `(U,L) ↦ 4`, `(U,R) ↦ 3`, `(D,L) ↦ 1`, `(D,R) ↦ 0`. -/
def cexG1 : Bool → Bool → ℝ
  | true, true => 4
  | true, false => 3
  | false, true => 1
  | false, false => 0

/-- The stage game of the counterexample. -/
def cexG (i : Fin 2) (x : Fin 2 → Bool) : ℝ :=
  if i = 0 then cexG0 (x 0) (x 1) else cexG1 (x 0) (x 1)

theorem cexG_bound : ∀ i x, |cexG i x| ≤ 4 := by
  intro i x
  unfold cexG
  split_ifs <;> cases x 0 <;> cases x 1 <;> norm_num [cexG0, cexG1]

/-- The stage game has the unique pure Nash equilibrium `q* = (D, L)`. -/
theorem cexG_unique_nash :
    IsStageNash cexG ![false, true] ∧ ∀ x, IsStageNash cexG x → x = ![false, true] := by
  constructor
  · intro i a
    fin_cases i <;> cases a <;> simp [cexG, cexG0, cexG1, update]
  · intro x hx
    have e0 : ∀ b, update x 0 b 0 = b := fun b => update_self _ _ _
    have e1 : ∀ b, update x 0 b 1 = x 1 := fun b => update_of_ne (by decide) _ _
    have f0 : ∀ b, update x 1 b 0 = x 0 := fun b => update_of_ne (by decide) _ _
    have f1 : ∀ b, update x 1 b 1 = b := fun b => update_self _ _ _
    have h0 : cexG0 false (x 1) ≤ cexG0 (x 0) (x 1) := by
      simpa [cexG, e0, e1] using hx 0 false
    have h1 : cexG1 (x 0) true ≤ cexG1 (x 0) (x 1) := by simpa [cexG, f0, f1] using hx 1 true
    funext k
    fin_cases k <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;> simp_all [cexG0, cexG1] <;>
      norm_num at *

/-- **Lemma 12.AA.1, Proposition 12.AA.2 and Exercise 12.AA.1 are false as printed**
(MWG, pp. 418-420; corrections). In the game `cexG` with the unique stage Nash equilibrium
`q* = (D, L)` and payoffs `π(q*) = (2, 1)`, take the stationary path `q = (U, R)` with
`π(q) = (1, 3)`.
1. At `δ = 1/2` its Nash reversion profile is an SPNE, but condition (12.AA.1) fails for player 1
   (U is player 1's best response to R, so `π̂₁(R) = π₁(q)`): Lemma 12.AA.1's "only if" fails.
2. At `δ' = 3/5 > 1/2` the same profile is not an SPNE: Proposition 12.AA.2 fails.
3. Player 1 gets `π₁(q) = 1 < 2 = π₁(q*)` on this stationary SPNE path: Exercise 12.AA.1 fails. -/
theorem counterexample_12_AA :
    IsRepeatedSPNE cexG (1 / 2) (nashReversion (fun _ => ![true, false]) ![false, true]) ∧
    ¬ (bestReplyValue cexG 0 ![true, false] + (1 / 2) / (1 - 1 / 2) * cexG 0 ![false, true] ≤
      pathValue cexG (1 / 2) (fun _ => ![true, false]) 0 0) ∧
    ¬ IsRepeatedSPNE cexG (3 / 5) (nashReversion (fun _ => ![true, false]) ![false, true]) ∧
    cexG 0 ![true, false] < cexG 0 ![false, true] := by
  have hN := cexG_unique_nash.1
  refine ⟨?_, ?_, ?_, by norm_num [cexG, cexG0]⟩
  · rw [nashReversion_spne_iff (by norm_num) (by norm_num) cexG_bound _ hN]
    intro t i a ha
    rw [pathValue_const cexG (by norm_num) (by norm_num)]
    fin_cases i <;> cases a <;> simp_all [cexG, cexG0, cexG1, update] <;> norm_num
  · intro h
    have h1 := le_bestReplyValue cexG_bound 0 ![true, false] true
    rw [pathValue_const cexG (by norm_num) (by norm_num)] at h
    simp [cexG, cexG0, update] at h h1
    norm_num at h h1
    linarith
  · rw [nashReversion_spne_iff (by norm_num) (by norm_num) cexG_bound _ hN]
    intro h
    have := h 0 0 false (by decide)
    rw [pathValue_const cexG (by norm_num) (by norm_num)] at this
    simp [cexG, cexG0, update] at this
    norm_num at this

/-- **Proposition 12.AA.2, corrected** (MWG, p. 420). If condition (12.AA.1) holds for the
outcome path `Q` at the discount factor `δ > 0`, it holds at every `δ' ∈ [δ, 1)`; hence the Nash
reversion profile for `Q` is then an SPNE at `δ'` (`lemma_12_AA_1_if`). -/
theorem proposition_12_AA_2_corrected {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ δ' M : ℝ} (hδ0 : 0 < δ) (hδδ' : δ ≤ δ') (hδ'1 : δ' < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i)
    (h12 : ∀ t i, bestReplyValue g i (Q t) + δ / (1 - δ) * g i qs ≤ pathValue g δ Q t i) :
    ∀ t i, bestReplyValue g i (Q t) + δ' / (1 - δ') * g i qs ≤ pathValue g δ' Q t i := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδδ' hδ'1
  have hδ'0 : 0 ≤ δ' := hδ0.le.trans hδδ'
  intro t i
  -- `D s d = v_i(Q, s) − π_i(q*)/(1 − d)` at the discount factor `d`
  set D : ℝ → ℕ → ℝ := fun d s => pathValue g d Q s i - g i qs / (1 - d) with hD
  have hDrec : ∀ d, 0 ≤ d → d < 1 → ∀ s, D d s = (g i (Q s) - g i qs) + d * D d (s + 1) := by
    intro d hd0 hd1 s
    simp only [hD]
    rw [pathValue_succ hd0 hd1 hg Q s i]
    have : (1 - d) ≠ 0 := by linarith
    field_simp
    ring
  have hbr : ∀ s, g i (Q s) ≤ bestReplyValue g i (Q s) := fun s => by
    have := le_bestReplyValue hg i (Q s) (Q s i)
    rwa [update_eq_self] at this
  -- (12.AA.1) at `δ` makes `D δ s ≥ 0` for `s ≥ 1`
  have hDnn : ∀ s, 0 ≤ D δ (s + 1) := by
    intro s
    have h1 := (eq_12_AA_2 hδ0.le hδ1 hg Q qs s i _).1 (h12 s i)
    have h2 := hbr s
    have : 0 ≤ δ * D δ (s + 1) := by simp only [hD]; linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hδ0
  -- the difference `D δ' s − D δ s` is nonnegative
  have hB : ∀ d, 0 ≤ d → d < 1 → ∀ s, |D d s| ≤ 2 * M / (1 - d) := by
    intro d hd0 hd1 s
    have h1 := pathValue_abs_le hd0 hd1 hg Q s i
    have h2 : |g i qs / (1 - d)| ≤ M / (1 - d) := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - d)]
      exact div_le_div_of_nonneg_right (hg i qs) (by linarith)
    calc |D d s| ≤ |pathValue g d Q s i| + |g i qs / (1 - d)| := abs_sub _ _
      _ ≤ M / (1 - d) + M / (1 - d) := add_le_add h1 h2
      _ = 2 * M / (1 - d) := by ring
  set K := 2 * M / (1 - δ') + 2 * M / (1 - δ) with hK
  have hgap : ∀ n s, -(δ' ^ n * K) ≤ D δ' s - D δ s := by
    intro n
    induction n with
    | zero =>
      intro s
      have := hB δ' hδ'0 hδ'1 s
      have := hB δ hδ0.le hδ1 s
      rw [pow_zero, one_mul, hK]
      have h3 := neg_abs_le (D δ' s)
      have h4 := le_abs_self (D δ s)
      linarith
    | succ n ih =>
      intro s
      rw [hDrec δ' hδ'0 hδ'1 s, hDrec δ hδ0.le hδ1 s]
      have h5 := ih (s + 1)
      have h6 := hDnn s
      have h7 : 0 ≤ (δ' - δ) * D δ (s + 1) := mul_nonneg (by linarith) h6
      have : g i (Q s) - g i qs + δ' * D δ' (s + 1) - (g i (Q s) - g i qs + δ * D δ (s + 1)) =
          δ' * (D δ' (s + 1) - D δ (s + 1)) + (δ' - δ) * D δ (s + 1) := by ring
      rw [this, pow_succ]
      have h8 : δ' * (-(δ' ^ n * K)) ≤ δ' * (D δ' (s + 1) - D δ (s + 1)) :=
        mul_le_mul_of_nonneg_left h5 hδ'0
      nlinarith
  have hmono : ∀ s, D δ s ≤ D δ' s := by
    intro s
    have ht : Tendsto (fun n : ℕ => -(δ' ^ n * K)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ'0 hδ'1).mul_const K).neg
    have := le_of_tendsto ht (Eventually.of_forall fun n => hgap n s)
    linarith
  have hfin := (eq_12_AA_2 hδ0.le hδ1 hg Q qs t i _).1 (h12 t i)
  rw [eq_12_AA_2 hδ'0 hδ'1 hg Q qs t i]
  have h9 : δ * D δ (t + 1) ≤ δ' * D δ' (t + 1) :=
    mul_le_mul hδδ' (hmono (t + 1)) (hDnn t) hδ'0
  simp only [hD] at h9
  linarith

/-- **Proposition 12.AA.3** (Friedman's Nash reversion folk theorem; MWG, p. 420). Let payoffs
be bounded by `M`, `q*` a stage Nash equilibrium, and `q` a profile with `π_i(q) > π_i(q*)` for
every player. Then there is `δ̲ < 1` such that for every `δ ∈ (δ̲, 1)` the infinite repetition of
`q` is the outcome path of an SPNE that uses Nash reversion. -/
theorem proposition_12_AA_3 {I : Type*} [Finite I] [Nonempty I] [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) {qs q : (i : I) → A i}
    (hqs : IsStageNash g qs) (hgt : ∀ i, g i qs < g i q) :
    ∃ δ₀ < 1, ∀ δ, δ₀ < δ → δ < 1 → 0 ≤ δ →
      IsRepeatedSPNE g δ (nashReversion (fun _ => q) qs) := by
  have := Fintype.ofFinite I
  have hMq : ∀ i, g i q ≤ M := fun i => (le_abs_self _).trans (hg i q)
  have hpos : ∀ i, 0 < M - g i qs := fun i => by linarith [hMq i, hgt i]
  set δ₀ := Finset.univ.sup' Finset.univ_nonempty fun i => (M - g i q) / (M - g i qs) with hδ₀
  have hlt : δ₀ < 1 := by
    rw [hδ₀, Finset.sup'_lt_iff]
    intro i _
    rw [div_lt_one (hpos i)]
    linarith [hgt i]
  refine ⟨δ₀, hlt, fun δ hδ hδ1 hδ0 => lemma_12_AA_1_if hδ0 hδ1 hg _ hqs fun t i => ?_⟩
  have hi : (M - g i q) / (M - g i qs) ≤ δ₀ := Finset.le_sup' (fun i => (M - g i q) /
    (M - g i qs)) (Finset.mem_univ i)
  have : Nonempty (A i) := ⟨q i⟩
  have hbr : bestReplyValue g i q ≤ M :=
    ciSup_le (fun a => (le_abs_self _).trans (hg i _))
  rw [pathValue_const g hδ0 hδ1]
  have h1δ : 0 < 1 - δ := by linarith
  have key : M - g i q ≤ δ * (M - g i qs) := by
    have := (div_le_iff₀ (hpos i)).1 (hi.trans hδ.le)
    linarith
  have e : M + δ / (1 - δ) * g i qs = (M * (1 - δ) + δ * g i qs) / (1 - δ) := by
    field_simp
  calc bestReplyValue g i q + δ / (1 - δ) * g i qs ≤ M + δ / (1 - δ) * g i qs := by linarith
    _ = (M * (1 - δ) + δ * g i qs) / (1 - δ) := e
    _ ≤ g i q / (1 - δ) := div_le_div_of_nonneg_right (by linarith) h1δ.le

/-- **Exercise 12.AA.1, corrected** (MWG, p. 420). If the infinite repetition of `q` is the
outcome path of a Nash reversion SPNE at `δ ∈ [0, 1)` and `π_i(q) < π_i(q*)`, then `q_i` is a
best response to `q_{-i}` with a margin: every other action loses at least
`δ/(1 − δ)(π_i(q*) − π_i(q))`; for `δ > 0` it is a strict best response. -/
theorem exercise_12_AA_1_corrected {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) {qs q : (i : I) → A i} (hqs : IsStageNash g qs)
    (hspne : IsRepeatedSPNE g δ (nashReversion (fun _ => q) qs)) (i : I) (a : A i)
    (ha : a ≠ q i) :
    g i (update q i a) ≤ g i q - δ / (1 - δ) * (g i qs - g i q) := by
  have h := (nashReversion_spne_iff hδ0 hδ1 hg _ hqs).1 hspne 0 i a ha
  rw [pathValue_const g hδ0 hδ1] at h
  have h1δ : (1 - δ) ≠ 0 := by linarith
  have e : g i q / (1 - δ) = g i q + δ * (g i q / (1 - δ)) := by field_simp; ring
  have e2 : δ / (1 - δ) * (g i qs - g i q) = δ * (g i qs / (1 - δ)) - δ * (g i q / (1 - δ)) := by
    ring
  linarith

/-- **Exercise 12.AA.1 under MWG's condition (12.AA.3)** (MWG, p. 420). If `q` satisfies
(12.AA.3), `π̂_i(q_j) − π_i(q) ≤ δ/(1 − δ)[π_i(q) − π_i(q*)]`, with `δ > 0`, then
`π_i(q) ≥ π_i(q*)`: under the printed characterization no `q` giving some player less than
`π_i(q*)` is sustainable. -/
theorem exercise_12_AA_1_printed_condition {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (q qs : (i : I) → A i) (i : I)
    (h : bestReplyValue g i q - g i q ≤ δ / (1 - δ) * (g i q - g i qs)) : g i qs ≤ g i q := by
  have h1 := le_bestReplyValue hg i q (q i)
  rw [update_eq_self] at h1
  have hpos : 0 < δ / (1 - δ) := div_pos hδ0 (by linarith)
  by_contra hlt
  push Not at hlt
  have := mul_neg_of_pos_of_neg hpos (by linarith : g i q - g i qs < 0)
  linarith

/-- Player `i`'s (pure strategy) minimax payoff `π̲_i = inf_{q_{-i}} sup_{q_i} π_i(q)`
(MWG, p. 421). -/
noncomputable def minimaxValue {I : Type*} [DecidableEq I] {A : I → Type*}
    (g : I → ((i : I) → A i) → ℝ) (i : I) : ℝ :=
  ⨅ x : (i : I) → A i, bestReplyValue g i x

theorem bestReplyValue_ge {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) (i : I)
    (x : (i : I) → A i) : -M ≤ bestReplyValue g i x := by
  have := le_bestReplyValue hg i x (x i)
  rw [update_eq_self] at this
  exact (neg_le_of_abs_le (hg i x)).trans this

/-- **Stage Nash payoffs are individually rational** (MWG, p. 421): `π_i(q*) ≥ π̲_i`. -/
theorem minimax_le_nash {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs) (i : I) : minimaxValue g i ≤ g i qs := by
  have : Nonempty (A i) := ⟨qs i⟩
  refine (ciInf_le ⟨-M, fun _ ⟨x, hx⟩ => hx ▸ bestReplyValue_ge hg i x⟩ qs).trans ?_
  exact ciSup_le fun a => hqs i a

/-- **SPNE payoffs are individually rational in every subgame** (MWG, p. 421). If `σ` is an SPNE
of the repeated game, then at every history player `i`'s average payoff `(1 − δ)V_i(h)` is at
least the minimax payoff `π̲_i` (a deviation to a period-by-period near best response secures
almost `π̲_i` in every period). -/
theorem minimax_le_spne_value {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) {σ : OSProfile A} (hσ : IsRepeatedSPNE g δ σ) (i : I)
    (h : OSHist A) : minimaxValue g i ≤ (1 - δ) * osValue (stageU g) δ σ h i := by
  have h1δ : 0 < 1 - δ := by linarith
  have hne : Nonempty (A i) := ⟨σ i h⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a near best response at every history
  have hex : ∀ h' : OSHist A, ∃ a : A i,
      bestReplyValue g i (osPlay σ h') - ε < g i (update (osPlay σ h') i a) := by
    intro h'
    have hb : BddAbove (Set.range fun a : A i => g i (update (osPlay σ h') i a)) :=
      ⟨M, fun _ ⟨b, hb⟩ => hb ▸ (le_abs_self _).trans (hg i _)⟩
    exact exists_lt_of_lt_ciSup (by unfold bestReplyValue at *; linarith)
  choose τ hτ using hex
  have hdev := hσ i τ h
  -- per-period payoffs of the deviation exceed `π̲_i − ε`
  have hterm : ∀ h' : OSHist A, minimaxValue g i - ε ≤
      stageU g i h' (osPlay (update σ i τ) h') := by
    intro h'
    rw [osPlay_update]
    have h2 : minimaxValue g i ≤ bestReplyValue g i (osPlay σ h') :=
      ciInf_le ⟨-M, fun _ ⟨x, hx⟩ => hx ▸ bestReplyValue_ge hg i x⟩ _
    have h3 := hτ h'
    simp only [stageU]
    linarith
  have hs := osValue_summable hδ0 hδ1 (stageU_bound hg) (update σ i τ) h i
  have hgeo := (summable_geometric_of_lt_one hδ0 hδ1).mul_right (minimaxValue g i - ε)
  have hlow : (minimaxValue g i - ε) / (1 - δ) ≤ osValue (stageU g) δ (update σ i τ) h i := by
    have := hgeo.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hterm _)
      (pow_nonneg hδ0 n)) hs
    rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at this
    rw [div_eq_inv_mul]
    exact this
  have := hlow.trans hdev
  rw [div_le_iff₀ h1δ] at this
  linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exact average payoffs from pure action sequences

A tool for the folk theorem (MWG, Proposition 12.AA.5, p. 422): a feasible payoff vector
`v = ∑ₗ λₗ π(aₗ)` (a convex combination of pure stage payoffs with weights `λₗ > 0`) is the exact
discounted average payoff of a deterministic sequence of the profiles `aₗ`, and all continuation
payoffs stay within `(1 − δ)C` of `v`, for `δ` close to `1` (this is how the folk theorem
dispenses with public randomization; compare Fudenberg and Maskin 1991).

The sequence is built greedily. A "lag" vector `G_t` with `∑ₗ λₗ G_t(l) = 0` starts at `0`; each
period plays a profile `a_k` whose lag is `G_t(k) ≤ 0`, and updates
`G_{t+1}(l) = (G_t(l) − 1 + [l = k]/λ_k)/δ` (`schedG`). The continuation target
`w_t = v − (1 − δ)∑ₗ λₗ G_t(l) π(aₗ)` then satisfies `w_t = (1 − δ)π(a_{k_t}) + δw_{t+1}`
(`schedCont_rec`), and `G_t(l) ≤ U` throughout (`sched_invariant`), so
`|w_t − v| ≤ (1 − δ)(n + 1)UM` (`schedCont_close`).
-/

namespace MWG.MarketPower

open Finset

variable {n : ℕ}

open Classical in
/-- The profile index chosen at lag vector `G`: some `k` with `G(k) ≤ 0` (if any). -/
noncomputable def schedK (G : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  if h : ∃ k, G k ≤ 0 then h.choose else 0

/-- One step of the lag recursion. -/
noncomputable def schedStep (wt : Fin (n + 1) → ℝ) (δ : ℝ) (G : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun l => (G l - 1 + (if l = schedK G then 1 / wt l else 0)) / δ

/-- The lag vectors `G_t`. -/
noncomputable def schedG (wt : Fin (n + 1) → ℝ) (δ : ℝ) : ℕ → Fin (n + 1) → ℝ
  | 0 => 0
  | t + 1 => schedStep wt δ (schedG wt δ t)

/-- The index played in period `t`. -/
noncomputable def schedIdx (wt : Fin (n + 1) → ℝ) (δ : ℝ) (t : ℕ) : Fin (n + 1) :=
  schedK (schedG wt δ t)

theorem schedK_spec {G : Fin (n + 1) → ℝ} (h : ∃ k, G k ≤ 0) : G (schedK G) ≤ 0 := by
  classical
  have e : schedK G = h.choose := by unfold schedK; simp [h]
  rw [e]
  exact h.choose_spec

/-- **The invariant of the schedule.** If `λ > 0`, `∑ λ = 1`, `1/λₗ ≤ U/2`, `δ ∈ [1/2, 1)` and
`(1 − δ)U ≤ 1`, then `∑ₗ λₗ G_t(l) = 0` and `G_t(l) ≤ U` for all `t` and `l`. -/
theorem sched_invariant {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) (hsum : ∑ l, wt l = 1)
    {δ U : ℝ} (hδ : 1 / 2 ≤ δ) (hU : ∀ l, 1 / wt l ≤ U / 2) (hUδ : (1 - δ) * U ≤ 1) :
    ∀ t, (∑ l, wt l * schedG wt δ t l = 0) ∧ ∀ l, schedG wt δ t l ≤ U := by
  have hδ0 : 0 < δ := by linarith
  have hU0 : 0 ≤ U := by have := hU 0; have := one_div_pos.2 (hwt 0); linarith
  intro t
  induction t with
  | zero => simp [schedG, hU0]
  | succ t ih =>
    obtain ⟨hs, hle⟩ := ih
    set G := schedG wt δ t with hG
    have hex : ∃ k, G k ≤ 0 := by
      by_contra hno
      push Not at hno
      have : 0 < ∑ l, wt l * G l :=
        Finset.sum_pos (fun l _ => mul_pos (hwt l) (hno l)) Finset.univ_nonempty
      linarith
    have hk := schedK_spec hex
    set k := schedK G with hkdef
    have hstep : schedG wt δ (t + 1) = schedStep wt δ G := rfl
    rw [hstep]
    constructor
    · unfold schedStep
      have : ∑ l, wt l * ((G l - 1 + (if l = k then 1 / wt l else 0)) / δ) =
          (∑ l, wt l * G l - ∑ l, wt l + ∑ l, wt l * (if l = k then 1 / wt l else 0)) / δ := by
        rw [eq_div_iff hδ0.ne', Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        field_simp
      have h1 : ∑ l, wt l * (if l = k then 1 / wt l else 0) = 1 := by
        rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
        simp [(hwt k).ne']
      rw [← hkdef, this, hs, hsum, h1]
      simp
    · intro l
      unfold schedStep
      rw [← hkdef]
      by_cases hl : l = k
      · simp only [hl, ite_true]
        rw [div_le_iff₀ hδ0]
        have := hU k
        nlinarith
      · simp only [hl, ite_false, add_zero]
        rw [div_le_iff₀ hδ0]
        have := hle l
        nlinarith

/-- The lower bound `λₗ G_t(l) ≥ −U` that follows from the invariant. -/
theorem sched_lower {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) (hsum : ∑ l, wt l = 1)
    {G : Fin (n + 1) → ℝ} {U : ℝ} (hU0 : 0 ≤ U) (hs : ∑ l, wt l * G l = 0)
    (hle : ∀ l, G l ≤ U) (l : Fin (n + 1)) : -U ≤ wt l * G l := by
  have hsplit := Finset.add_sum_erase Finset.univ (fun m => wt m * G m) (Finset.mem_univ l)
  have h1 : ∑ m ∈ Finset.univ.erase l, wt m * G m ≤ ∑ m ∈ Finset.univ.erase l, wt m * U :=
    Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hle m) (hwt m).le
  have h2 : ∑ m ∈ Finset.univ.erase l, wt m * U ≤ ∑ m, wt m * U :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun m _ _ =>
      mul_nonneg (hwt m).le hU0
  have h3 : ∑ m, wt m * U = U := by rw [← Finset.sum_mul, hsum, one_mul]
  linarith

/-- The continuation target `w_t(i) = v_i − (1 − δ)∑ₗ λₗ G_t(l) π_i(aₗ)`. -/
noncomputable def schedCont (wt : Fin (n + 1) → ℝ) (δ : ℝ) (u : Fin (n + 1) → ℝ) (v : ℝ)
    (t : ℕ) : ℝ :=
  v - (1 - δ) * ∑ l, wt l * schedG wt δ t l * u l

/-- **The recursion of the continuation targets**: `w_t = (1 − δ)π(a_{k_t}) + δw_{t+1}`, when
`v = ∑ₗ λₗ uₗ`. -/
theorem schedCont_rec {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) {δ : ℝ} (hδ0 : 0 < δ)
    (u : Fin (n + 1) → ℝ) {v : ℝ} (hv : v = ∑ l, wt l * u l) (t : ℕ) :
    schedCont wt δ u v t = (1 - δ) * u (schedIdx wt δ t) + δ * schedCont wt δ u v (t + 1) := by
  unfold schedCont schedIdx
  set G := schedG wt δ t with hG
  set k := schedK G with hk
  have hstep : schedG wt δ (t + 1) = schedStep wt δ G := rfl
  rw [hstep]
  have hsum : δ * ∑ l, wt l * schedStep wt δ G l * u l =
      ∑ l, wt l * G l * u l - ∑ l, wt l * u l + u k := by
    rw [Finset.mul_sum]
    have : ∀ l, δ * (wt l * schedStep wt δ G l * u l) =
        wt l * G l * u l - wt l * u l + (if l = k then u l else 0) := by
      intro l
      unfold schedStep
      rw [← hk]
      by_cases hl : l = k
      · simp only [hl, ite_true]; have := (hwt k).ne'; field_simp
      · simp only [hl, ite_false, add_zero]; field_simp
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq']
    simp
  have e : δ * (v - (1 - δ) * ∑ l, wt l * schedStep wt δ G l * u l) =
      δ * v - (1 - δ) * (δ * ∑ l, wt l * schedStep wt δ G l * u l) := by ring
  rw [e, hsum, ← hv]
  ring

/-- **Continuation targets stay close to `v`**: `|w_t − v| ≤ (1 − δ)(n + 1)UM` when
`|uₗ| ≤ M`. -/
theorem schedCont_close {wt : Fin (n + 1) → ℝ} (hwt : ∀ l, 0 < wt l) (hsum : ∑ l, wt l = 1)
    {δ U M : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) (hU : ∀ l, 1 / wt l ≤ U / 2)
    (hUδ : (1 - δ) * U ≤ 1) (u : Fin (n + 1) → ℝ) (hu : ∀ l, |u l| ≤ M) (v : ℝ) (t : ℕ) :
    |schedCont wt δ u v t - v| ≤ (1 - δ) * ((n + 1) * U * M) := by
  obtain ⟨hs, hle⟩ := sched_invariant hwt hsum hδ hU hUδ t
  have hU0 : 0 ≤ U := by have := hU 0; have := one_div_pos.2 (hwt 0); linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu 0)
  have hwt1 : ∀ l, wt l ≤ 1 := fun l => by
    rw [← hsum]
    exact Finset.single_le_sum (fun m _ => (hwt m).le) (Finset.mem_univ l)
  have hterm : ∀ l, |wt l * schedG wt δ t l * u l| ≤ U * M := by
    intro l
    have h1 := sched_lower hwt hsum hU0 hs hle l
    have h2 : wt l * schedG wt δ t l ≤ U := by
      have := hle l
      have := mul_le_mul_of_nonneg_left this (hwt l).le
      nlinarith [hwt1 l]
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ⟨h1, h2⟩) (hu l) (abs_nonneg _) hU0
  unfold schedCont
  rw [show v - (1 - δ) * ∑ l, wt l * schedG wt δ t l * u l - v =
    -((1 - δ) * ∑ l, wt l * schedG wt δ t l * u l) by ring, abs_neg, abs_mul,
    abs_of_pos (by linarith : (0 : ℝ) < 1 - δ)]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
  simp [mul_assoc]

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The folk theorem

MWG, Proposition 12.AA.5, p. 422, for two players and pure strategies.

A payoff pair `v` is *feasible* if it is a convex combination `v = ∑ₗ λₗ π(aₗ)` of stage payoffs
of finitely many pure profiles (MWG: "there is some outcome path that generates these average
payoffs"; by `Schedule`, for `δ` near `1` such a `v` is exactly the average payoff of a pure
outcome path). It is *individually rational* if `v_i > π̲_i`.

The equilibrium (`folkProfile`) is the two-player construction of Fudenberg and Maskin (1986):
play the path generated by `Schedule`; after any deviation both players play the mutual minimax
profile `m` (each player's action holds the other to at most `π̲`) for `L` periods and then
restart the path; a deviation during the punishment restarts the punishment. Subgame perfection
is checked with the one-shot deviation principle (Chapter 9).

* `proposition_12_AA_5`: for punishment levels `w_i` that `m_{-i}` enforces and any feasible `v`
  with `v ≫ w`, there is `δ̲ < 1` such that for all `δ ∈ (δ̲, 1)` some SPNE has average payoffs
  exactly `v`.
* `folk_theorem`: the statement with the minimax payoffs `π̲_i` (when the minimum over the rival's
  actions is attained, e.g. for finite action sets).
* `folk_theorem_instance`: the repeated Prisoner's Dilemma and the payoff `(3/2, 3/2)`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

variable {A : Fin 2 → Type*}

/-- States of the folk-theorem automaton: `inl t` is period `t` of the cooperative path,
`inr r` is the punishment phase with `r + 1` periods left. -/
abbrev FolkState := ℕ ⊕ ℕ

/-- The profile prescribed in each state. -/
def folkPresc (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i) :
    FolkState → (i : Fin 2) → A i
  | Sum.inl t => path t
  | Sum.inr _ => mm

open Classical in
/-- The transition: conforming play moves along the path or through the punishment; any
deviation (re)starts a punishment of `R + 1` periods. -/
noncomputable def folkTrans (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i) (R : ℕ) :
    FolkState → ((i : Fin 2) → A i) → FolkState
  | Sum.inl t, x => if x = path t then Sum.inl (t + 1) else Sum.inr R
  | Sum.inr r, x => if x = mm then (if r = 0 then Sum.inl 0 else Sum.inr (r - 1)) else Sum.inr R

/-- The state after a history. -/
noncomputable def folkStateOf (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i)
    (R : ℕ) : OSHist A → FolkState
  | [] => Sum.inl 0
  | x :: h => folkTrans path mm R (folkStateOf path mm R h) x

/-- The folk-theorem strategy profile. -/
noncomputable def folkProfile (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i)
    (R : ℕ) : OSProfile A :=
  fun i h => folkPresc path mm (folkStateOf path mm R h) i

theorem osPlay_folkProfile (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i) (R : ℕ)
    (h : OSHist A) :
    osPlay (folkProfile path mm R) h = folkPresc path mm (folkStateOf path mm R h) :=
  rfl

theorem folkTrans_conform (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i) (R : ℕ)
    (s : FolkState) : folkTrans path mm R s (folkPresc path mm s) =
      match s with
      | Sum.inl t => Sum.inl (t + 1)
      | Sum.inr r => if r = 0 then Sum.inl 0 else Sum.inr (r - 1) := by
  cases s <;> simp [folkTrans, folkPresc]

theorem folkTrans_deviate (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i) (R : ℕ)
    (s : FolkState) {i : Fin 2} {a : A i} (ha : a ≠ folkPresc path mm s i) :
    folkTrans path mm R s (update (folkPresc path mm s) i a) = Sum.inr R := by
  have hne : update (folkPresc path mm s) i a ≠ folkPresc path mm s := by
    intro heq
    have := congrFun heq i
    rw [update_self] at this
    exact ha this
  cases s with
  | inl t =>
    simp only [folkPresc] at hne
    simp only [folkTrans, folkPresc, hne, ↓reduceIte]
  | inr r =>
    simp only [folkPresc] at hne
    simp only [folkTrans, folkPresc, hne, ↓reduceIte]

/-- Punishment states that occur have at most `R + 1` periods left. -/
theorem folkStateOf_le (path : ℕ → (i : Fin 2) → A i) (mm : (i : Fin 2) → A i) (R : ℕ) :
    ∀ (h : OSHist A) (r : ℕ), folkStateOf path mm R h = Sum.inr r → r ≤ R := by
  intro h
  induction h with
  | nil => intro r hr; simp [folkStateOf] at hr
  | cons x h ih =>
    intro r hr
    simp only [folkStateOf] at hr
    cases hs : folkStateOf path mm R h with
    | inl t =>
      rw [hs] at hr
      simp only [folkTrans] at hr
      split_ifs at hr
      simp only [Sum.inr.injEq] at hr
      omega
    | inr r' =>
      rw [hs] at hr
      have := ih r' hs
      simp only [folkTrans] at hr
      split_ifs at hr <;> simp only [Sum.inr.injEq] at hr <;> omega

/-- The value of each state for player `i` (unnormalized): `w_t/(1 − δ)` on the path and
`((1 − δ^{r+1})p + δ^{r+1}v)/(1 − δ)` with `r + 1` punishment periods left. -/
noncomputable def folkVal (cont : ℕ → ℝ) (p v δ : ℝ) : FolkState → ℝ
  | Sum.inl t => cont t / (1 - δ)
  | Sum.inr r => ((1 - δ ^ (r + 1)) * p + δ ^ (r + 1) * v) / (1 - δ)

/-- The continuation payoffs of the folk-theorem profile are given by `folkVal`. -/
theorem osValue_folkProfile {g : Fin 2 → ((i : Fin 2) → A i) → ℝ} {δ M B : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (path : ℕ → (i : Fin 2) → A i)
    (mm : (i : Fin 2) → A i) (R : ℕ) (i : Fin 2) (cont : ℕ → ℝ) (v : ℝ)
    (hcont : ∀ t, cont t = (1 - δ) * g i (path t) + δ * cont (t + 1)) (hcont0 : cont 0 = v)
    (hB : ∀ s, |folkVal cont (g i mm) v δ s| ≤ B) (h : OSHist A) :
    osValue (stageU g) δ (folkProfile path mm R) h i =
      folkVal cont (g i mm) v δ (folkStateOf path mm R h) := by
  have h1δ : (1 - δ) ≠ 0 := by linarith
  refine osValue_eq_of_rec hδ0 hδ1 (stageU_bound hg) _ i
    (fun h => folkVal cont (g i mm) v δ (folkStateOf path mm R h)) (fun h => hB _)
    (fun h => ?_) h
  simp only [osPlay_folkProfile, folkStateOf, folkTrans_conform, stageU]
  cases folkStateOf path mm R h with
  | inl t =>
    simp only [folkPresc, folkVal]
    rw [hcont t]
    field_simp
  | inr r =>
    simp only [folkPresc]
    split_ifs with hr
    · subst hr
      simp only [folkVal, hcont0]
      field_simp
      ring
    · simp only [folkVal]
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      ring

/-- Clearing the denominator `1 − δ`. -/
theorem folk_div_helper {X Y Z δ : ℝ} (hδ1 : δ < 1) (h : (1 - δ) * X + δ * Y ≤ Z) :
    X + δ * (Y / (1 - δ)) ≤ Z / (1 - δ) := by
  have h1δ : 0 < 1 - δ := by linarith
  rw [le_div_iff₀ h1δ]
  have : (X + δ * (Y / (1 - δ))) * (1 - δ) = (1 - δ) * X + δ * Y := by field_simp
  rw [this]
  exact h

/-- **Proposition 12.AA.5 (the folk theorem)** (MWG, p. 422), two players, pure strategies.
Let stage payoffs be bounded by `M`, and let the mutual punishment profile `m` hold each player
`i` to at most `w_i` whatever `i` does (`π_i(a, m_{-i}) ≤ w_i`). Let `v = ∑ₗ λₗ π(aₗ)` be a
feasible payoff pair (`λₗ > 0`, `∑ λₗ = 1`) with `v_i > w_i` for both players. Then there is
`δ̲ < 1` such that for every `δ ∈ (δ̲, 1)` some SPNE of the infinitely repeated game has average
payoffs `(1 − δ)V_i = v_i` exactly. -/
theorem proposition_12_AA_5 {g : Fin 2 → ((i : Fin 2) → A i) → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (mm : (i : Fin 2) → A i) (w : Fin 2 → ℝ)
    (hmm : ∀ i (b : A i), g i (update mm i b) ≤ w i) {n : ℕ}
    (a : Fin (n + 1) → (i : Fin 2) → A i) (wt : Fin (n + 1) → ℝ) (hwt : ∀ l, 0 < wt l)
    (hsum : ∑ l, wt l = 1) (v : Fin 2 → ℝ) (hv : ∀ i, v i = ∑ l, wt l * g i (a l))
    (hIR : ∀ i, w i < v i) :
    ∃ δ₀ < 1, ∀ δ, δ₀ < δ → δ < 1 → ∃ σ : OSProfile A,
      IsRepeatedSPNE g δ σ ∧ ∀ i, (1 - δ) * osValue (stageU g) δ σ [] i = v i := by
  -- constants that do not depend on `δ`
  set p : Fin 2 → ℝ := fun i => g i mm with hp
  have hpw : ∀ i, p i ≤ w i := fun i => by
    have := hmm i (mm i); rwa [update_eq_self] at this
  have hvp : ∀ i, 0 < v i - p i := fun i => by linarith [hpw i, hIR i]
  set ρ : Fin 2 → ℝ := fun i => (w i - p i) / (v i - p i) with hρ
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => div_nonneg (by linarith [hpw i]) (hvp i).le
  have hρ1 : ∀ i, ρ i < 1 := fun i => (div_lt_one (hvp i)).2 (by linarith [hIR i])
  set θ := max ((1 + ρ 0) / 2) ((1 + ρ 1) / 2) with hθ
  have hθρ : ∀ i, ρ i < θ := by
    rw [Fin.forall_fin_two]
    exact ⟨lt_of_lt_of_le (by linarith [hρ1 0]) (le_max_left _ _),
      lt_of_lt_of_le (by linarith [hρ1 1]) (le_max_right _ _)⟩
  have hθ1 : θ < 1 := max_lt (by linarith [hρ1 0]) (by linarith [hρ1 1])
  have hθ0 : 0 < θ := lt_of_le_of_lt (hρ0 0) (hθρ 0)
  set U := 2 * ∑ l, 1 / wt l with hUdef
  have hU : ∀ l, 1 / wt l ≤ U / 2 := fun l => by
    rw [hUdef, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact Finset.single_le_sum (fun m _ => (one_div_pos.2 (hwt m)).le) (Finset.mem_univ l)
  have hUpos : 0 < U := by
    have := hU 0; have := one_div_pos.2 (hwt 0); linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg 0 mm)
  set C := ((n : ℝ) + 1) * U * M with hC
  have hC0 : 0 ≤ C := by positivity
  have hvM : ∀ i, v i ≤ M := fun i => by
    rw [hv i]
    calc ∑ l, wt l * g i (a l) ≤ ∑ l, wt l * M :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans (hg i _)) (hwt l).le
      _ = M := by rw [← Finset.sum_mul, hsum, one_mul]
  set K : Fin 2 → ℝ := fun i => M - v i + C with hK
  have hK0 : ∀ i, 0 ≤ K i := fun i => by simp only [hK]; linarith [hvM i]
  set d : Fin 2 → ℝ := fun i => (θ * (v i - p i) + K i) / (v i - p i + K i) with hd
  have hd1 : ∀ i, d i < 1 := fun i => by
    have h1 : 0 < v i - p i + K i := by linarith [hvp i, hK0 i]
    rw [hd, div_lt_one h1]
    nlinarith [hvp i]
  set δ₀ := max (max (max (1 / 2) (1 - 1 / U)) θ) (max (d 0) (d 1)) with hδ₀
  have hU1 : 1 - 1 / U < 1 := by have := one_div_pos.2 hUpos; linarith
  refine ⟨δ₀, max_lt (max_lt (max_lt (by norm_num) hU1) hθ1) (max_lt (hd1 0) (hd1 1)),
    fun δ hδ hδ1 => ?_⟩
  have hδh : 1 / 2 ≤ δ := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hδ.le
  have hδ0 : 0 ≤ δ := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hδU : (1 - δ) * U ≤ 1 := by
    have : 1 - 1 / U ≤ δ := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) hδ.le
    have h2 : 1 - δ ≤ 1 / U := by linarith
    calc (1 - δ) * U ≤ 1 / U * U := mul_le_mul_of_nonneg_right h2 hUpos.le
      _ = 1 := by field_simp
  have hδθ : θ ≤ δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hδ.le
  have hδd : ∀ i, d i ≤ δ := by
    rw [Fin.forall_fin_two]
    exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hδ.le,
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hδ.le⟩
  -- the punishment length
  have hex : ∃ N : ℕ, δ ^ N < θ := exists_pow_lt_of_lt_one hθ0 hδ1
  classical
  set N := Nat.find hex with hN
  have hN2 : 2 ≤ N := by
    by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec hex
    rw [← hN] at hspec
    rcases (by omega : N = 0 ∨ N = 1) with h0 | h1
    · rw [h0, pow_zero] at hspec; linarith
    · rw [h1, pow_one] at hspec; linarith
  set R := N - 2 with hR
  have hL : θ ≤ δ ^ (R + 1) := not_lt.1 (Nat.find_min hex (show R + 1 < N by omega))
  have hL2 : δ ^ (R + 2) < θ := by
    have := Nat.find_spec hex
    rwa [← hN, show N = R + 2 by omega] at this
  -- the path and continuation targets
  set path : ℕ → (i : Fin 2) → A i := fun t => a (schedIdx wt δ t) with hpath
  set cont : Fin 2 → ℕ → ℝ := fun i t => schedCont wt δ (fun l => g i (a l)) (v i) t
    with hcontdef
  have hcont : ∀ i t, cont i t = (1 - δ) * g i (path t) + δ * cont i (t + 1) := fun i t =>
    schedCont_rec hwt (by linarith) (fun l => g i (a l)) (hv i) t
  have hcont0 : ∀ i, cont i 0 = v i := fun i => by simp [hcontdef, schedCont, schedG]
  have hclose : ∀ i t, |cont i t - v i| ≤ (1 - δ) * C := fun i t =>
    schedCont_close hwt hsum hδh hδ1 hU hδU (fun l => g i (a l)) (fun l => hg i _) (v i) t
  -- values
  have hB : ∀ i s, |folkVal (cont i) (p i) (v i) δ s| ≤ (|v i| + |p i| + C) / (1 - δ) := by
    intro i s
    cases s with
    | inl t =>
      simp only [folkVal]
      rw [abs_div, abs_of_pos h1δ]
      refine div_le_div_of_nonneg_right ?_ h1δ.le
      have := hclose i t
      have h3 : (1 - δ) * C ≤ C := by nlinarith
      have := abs_sub_abs_le_abs_sub (cont i t) (v i)
      linarith [abs_nonneg (p i)]
    | inr r =>
      simp only [folkVal]
      rw [abs_div, abs_of_pos h1δ]
      refine div_le_div_of_nonneg_right ?_ h1δ.le
      have hq0 : 0 ≤ δ ^ (r + 1) := pow_nonneg hδ0 _
      have hq1 : δ ^ (r + 1) ≤ 1 := pow_le_one₀ hδ0 hδ1.le
      calc |(1 - δ ^ (r + 1)) * p i + δ ^ (r + 1) * v i|
          ≤ |(1 - δ ^ (r + 1)) * p i| + |δ ^ (r + 1) * v i| := abs_add_le _ _
        _ = (1 - δ ^ (r + 1)) * |p i| + δ ^ (r + 1) * |v i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hq0]
        _ ≤ |v i| + |p i| + C := by nlinarith [abs_nonneg (p i), abs_nonneg (v i)]
  have hval : ∀ i h, osValue (stageU g) δ (folkProfile path mm R) h i =
      folkVal (cont i) (p i) (v i) δ (folkStateOf path mm R h) := fun i h =>
    osValue_folkProfile hδ0 hδ1 hg path mm R i (cont i) (v i) (hcont i) (hcont0 i) (hB i) h
  refine ⟨folkProfile path mm R, ?_, fun i => ?_⟩
  swap
  · rw [hval]
    simp only [folkStateOf, folkVal, hcont0]
    field_simp
  -- subgame perfection by the one-shot deviation principle
  unfold IsRepeatedSPNE
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound hg)]
  intro i h b
  by_cases hb : b = folkPresc path mm (folkStateOf path mm R h) i
  · rw [osPlay_folkProfile, hb, update_eq_self, ← osPlay_folkProfile]
    exact (osValue_succ hδ0 hδ1 (stageU_bound hg) _ h i).ge
  rw [hval, hval, osPlay_folkProfile]
  simp only [folkStateOf]
  rw [folkTrans_deviate path mm R _ hb]
  simp only [stageU]
  have hpv : 0 ≤ v i - p i := (hvp i).le
  cases hs : folkStateOf path mm R h with
  | inl t =>
    simp only [folkVal, folkPresc]
    rw [hs] at hb
    have hgM : g i (update (path t) i b) ≤ M := (le_abs_self _).trans (hg i _)
    have hct : v i - (1 - δ) * C ≤ cont i t := by
      have := hclose i t; rw [abs_le] at this; linarith
    apply folk_div_helper hδ1
    -- `(1 − δ)(M + C − v) ≤ (δ − θ)(v − p) < (δ − δ^{R+2})(v − p)`
    have hdi := hδd i
    have hKpos : 0 < v i - p i + K i := by linarith [hvp i, hK0 i]
    have h1 : θ * (v i - p i) + K i ≤ δ * (v i - p i + K i) := by
      have := (div_le_iff₀ hKpos).1 hdi
      linarith
    have h2 : δ ^ (R + 2) * (v i - p i) ≤ θ * (v i - p i) :=
      mul_le_mul_of_nonneg_right hL2.le hpv
    have e : δ ^ (R + 2) = δ * δ ^ (R + 1) := by ring
    simp only [hK] at h1
    nlinarith [mul_le_mul_of_nonneg_left hgM h1δ.le]
  | inr r =>
    simp only [folkVal, folkPresc]
    have hr := folkStateOf_le path mm R h r hs
    have hgw : g i (update mm i b) ≤ w i := hmm i b
    apply folk_div_helper hδ1
    have hpow : δ ^ (R + 1) ≤ δ ^ (r + 1) := pow_le_pow_of_le_one hδ0 hδ1.le (by omega)
    have hρθ : (w i - p i) ≤ δ ^ (R + 1) * (v i - p i) := by
      have := (div_le_iff₀ (hvp i)).1 ((hθρ i).le.trans hL)
      linarith
    have e : δ ^ (R + 1 + 1) = δ * δ ^ (R + 1) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hgw h1δ.le, mul_le_mul_of_nonneg_right hpow hpv,
      mul_le_mul_of_nonneg_left hρθ h1δ.le]

/-- **Proposition 12.AA.5 with minimax payoffs** (MWG, pp. 421-422). If each player's minimax
payoff `π̲_i = min_{q_j} max_{q_i} π_i` is attained (by the rival profile `xs i`), then every
feasible pair `v ≫ (π̲₁, π̲₂)` is the average payoff of an SPNE for all `δ` close enough to `1`. -/
theorem folk_theorem {g : Fin 2 → ((i : Fin 2) → A i) → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (xs : Fin 2 → (i : Fin 2) → A i)
    (hxs : ∀ i, bestReplyValue g i (xs i) = minimaxValue g i) {n : ℕ}
    (a : Fin (n + 1) → (i : Fin 2) → A i) (wt : Fin (n + 1) → ℝ) (hwt : ∀ l, 0 < wt l)
    (hsum : ∑ l, wt l = 1) (v : Fin 2 → ℝ) (hv : ∀ i, v i = ∑ l, wt l * g i (a l))
    (hIR : ∀ i, minimaxValue g i < v i) :
    ∃ δ₀ < 1, ∀ δ, δ₀ < δ → δ < 1 → ∃ σ : OSProfile A,
      IsRepeatedSPNE g δ σ ∧ ∀ i, (1 - δ) * osValue (stageU g) δ σ [] i = v i := by
  refine proposition_12_AA_5 hg (fun j => xs (if j = 0 then 1 else 0) j)
    (fun i => minimaxValue g i) (fun i b => ?_) a wt hwt hsum v hv hIR
  have heq : update (fun j => xs (if j = 0 then 1 else 0) j) i b = update (xs i) i b := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [update_of_ne hj, update_of_ne hj]
      fin_cases i <;> fin_cases j <;> simp_all
  rw [heq, ← hxs i]
  exact le_bestReplyValue hg i (xs i) b

/-- The Prisoner's Dilemma used as an instance (`true` = cooperate): `(C,C) ↦ (2,2)`,
`(D,C) ↦ (3,0)`, `(C,D) ↦ (0,3)`, `(D,D) ↦ (1,1)`. -/
def pdPay (i : Fin 2) (x : Fin 2 → Bool) : ℝ :=
  match x i, x (if i = 0 then 1 else 0) with
  | true, true => 2
  | false, true => 3
  | true, false => 0
  | false, false => 1

/-- **Proposition 12.AA.5, an instance.** In the infinitely repeated Prisoner's Dilemma the
payoff `(3/2, 3/2) = ½(2, 2) + ½(1, 1)`, which exceeds the punishment level `1` that mutual
defection enforces, is the average payoff of an SPNE for every `δ` close enough to `1`. -/
theorem folk_theorem_instance :
    ∃ δ₀ < 1, ∀ δ, δ₀ < δ → δ < 1 → ∃ σ : OSProfile (fun _ : Fin 2 => Bool),
      IsRepeatedSPNE pdPay δ σ ∧ ∀ i, (1 - δ) * osValue (stageU pdPay) δ σ [] i = 3 / 2 := by
  have hg : ∀ i x, |pdPay i x| ≤ 3 := by
    intro i x; unfold pdPay
    split <;> norm_num
  obtain ⟨δ₀, hδ₀, h⟩ := proposition_12_AA_5 (n := 1) hg (fun _ => false) (fun _ => 1)
    (fun i b => by fin_cases i <;> cases b <;> simp [pdPay, update])
    ![fun _ => true, fun _ => false] ![1 / 2, 1 / 2] (fun l => by fin_cases l <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) (fun _ => 3 / 2)
    (fun i => by fin_cases i <;> simp [Fin.sum_univ_two, pdPay] <;> norm_num)
    (fun i => by norm_num)
  exact ⟨δ₀, hδ₀, h⟩

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Severer punishments: stick-and-carrot strategies

MWG, Propositions 12.AA.1 and 12.AA.4, Exercise 12.AA.2 and Example 12.AA.1, pp. 419-423.

A three-state automaton (`scProfile`): in the *stick* state play `s`; if everybody conforms move
to the *carrot* state, where `c` is played as long as nobody deviates; a deviation in the stick
state restarts the stick, a deviation in the carrot state moves to the target state `tgt` (the
stick again, or the *Nash* state, where the stage Nash equilibrium `n` is played forever).

* `scProfile_spne`: the automaton is an SPNE when the stick is a credible one-period punishment,
  `π_i(a, s_{-i}) ≤ (1 − δ)π_i(s) + δπ_i(c)`, and deviations from the carrot are deterred.
* `stage_pareto_improvement`, `proposition_12_AA_1`: near `q*`, with differentiable payoffs,
  nonzero cross partials and the envelope property (12.AA.6), a Pareto improvement satisfies
  (12.AA.3) for every `δ > 0`, so its repetition is sustained by Nash reversion.
* `stage_severe_punishment`, `proposition_12_AA_4` (Exercise 12.AA.2): under the same
  conditions, some stick-and-carrot SPNE gives both players average payoffs below `π_i(q*)`.
* `example_12_AA_1`: the Cournot stick-and-carrot equilibrium with average payoff zero, and
  `example_12_AA_1_qbar`: the stick `q̄ ≥ q_c` solving (12.AA.7) exists for `δ` near `1`;
  `example_12_AA_1_instance`: a linear instance.

Departure: Propositions 12.AA.1 and 12.AA.4 are proved under the envelope property (12.AA.6)
(`π̂_i` differentiable at `q_j*` with derivative `∂π_i(q*)/∂q_j`), which MWG's proof invokes;
MWG lists only the differentiability of `π_i` at `q*`; without (12.AA.6) both propositions
are false (`StickCarrotLiteral`).
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- The profile prescribed in the stick (`0`), carrot (`1`) and Nash (`2`) states. -/
def scPresc (s c n : (i : I) → A i) : Fin 3 → (i : I) → A i
  | 0 => s
  | 1 => c
  | 2 => n

open Classical in
/-- The transitions of the stick-and-carrot automaton. -/
noncomputable def scTrans (s c : (i : I) → A i) (tgt : Fin 3) : Fin 3 → ((i : I) → A i) → Fin 3
  | 0, x => if x = s then 1 else 0
  | 1, x => if x = c then 1 else tgt
  | 2, _ => 2

/-- The state after a history (play starts in the stick state). -/
noncomputable def scStateOf (s c : (i : I) → A i) (tgt : Fin 3) : OSHist A → Fin 3
  | [] => 0
  | x :: h => scTrans s c tgt (scStateOf s c tgt h) x

/-- The stick-and-carrot profile. -/
noncomputable def scProfile (s c n : (i : I) → A i) (tgt : Fin 3) : OSProfile A :=
  fun i h => scPresc s c n (scStateOf s c tgt h) i

/-- The value of each state. -/
noncomputable def scVal (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (s c n : (i : I) → A i) (i : I) :
    Fin 3 → ℝ
  | 0 => g i s + δ * (g i c / (1 - δ))
  | 1 => g i c / (1 - δ)
  | 2 => g i n / (1 - δ)

omit [DecidableEq I] in
theorem scTrans_conform (s c n : (i : I) → A i) (tgt : Fin 3) (k : Fin 3) :
    scTrans s c tgt k (scPresc s c n k) = if k = 2 then 2 else 1 := by
  fin_cases k <;> simp [scTrans, scPresc]

theorem scTrans_deviate (s c n : (i : I) → A i) (tgt : Fin 3) (k : Fin 3) {i : I} {a : A i}
    (ha : a ≠ scPresc s c n k i) :
    scTrans s c tgt k (update (scPresc s c n k) i a) =
      if k = 0 then 0 else if k = 1 then tgt else 2 := by
  have hne : update (scPresc s c n k) i a ≠ scPresc s c n k := by
    intro heq
    have := congrFun heq i
    rw [update_self] at this
    exact ha this
  fin_cases k <;> simp only [scPresc] at hne <;> simp [scTrans, scPresc, hne]

/-- **The stick-and-carrot automaton is an SPNE** under the one-shot conditions: `n` is a stage
Nash equilibrium; the stick is accepted, `π_i(a, s_{-i}) ≤ (1 − δ)π_i(s) + δπ_i(c)` for all `a`;
and every deviation from the carrot is deterred, `π_i(a, c_{-i}) + δV_tgt ≤ π_i(c)/(1 − δ)` for
`a ≠ c_i`. Its value from the start is `π_i(s) + δπ_i(c)/(1 − δ)`. -/
theorem scProfile_spne {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (s c n : (i : I) → A i) (tgt : Fin 3)
    (hn : IsStageNash g n)
    (hs : ∀ i a, g i (update s i a) ≤ (1 - δ) * g i s + δ * g i c)
    (hc : ∀ i a, a ≠ c i → g i (update c i a) + δ * scVal g δ s c n i tgt ≤ g i c / (1 - δ)) :
    IsRepeatedSPNE g δ (scProfile s c n tgt) ∧
      ∀ i, osValue (stageU g) δ (scProfile s c n tgt) [] i = g i s + δ * (g i c / (1 - δ)) := by
  have h1δ : (1 - δ) ≠ 0 := by linarith
  have h1δp : 0 < 1 - δ := by linarith
  have hB : ∀ i k, |scVal g δ s c n i k| ≤ M + M / (1 - δ) := by
    intro i k
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg i s)
    have hdiv : ∀ x, |g i x / (1 - δ)| ≤ M / (1 - δ) := fun x => by
      rw [abs_div, abs_of_pos h1δp]; exact div_le_div_of_nonneg_right (hg i x) h1δp.le
    have hMd : 0 ≤ M / (1 - δ) := div_nonneg hM0 h1δp.le
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · simp only [scVal]
      refine (abs_add_le _ _).trans (add_le_add (hg i s) ?_)
      rw [abs_mul, abs_of_nonneg hδ0]
      calc δ * |g i c / (1 - δ)| ≤ 1 * (M / (1 - δ)) :=
            mul_le_mul (by linarith) (hdiv c) (abs_nonneg _) zero_le_one
        _ = M / (1 - δ) := one_mul _
    · simp only [scVal]; linarith [hdiv c]
    · simp only [scVal]; linarith [hdiv n]
  have hval : ∀ i h, osValue (stageU g) δ (scProfile s c n tgt) h i =
      scVal g δ s c n i (scStateOf s c tgt h) := by
    intro i h
    refine osValue_eq_of_rec hδ0 hδ1 (stageU_bound hg) _ i _ (fun h => hB i _) (fun h => ?_) h
    have hp : osPlay (scProfile s c n tgt) h = scPresc s c n (scStateOf s c tgt h) := rfl
    simp only [hp, scStateOf, scTrans_conform, stageU]
    generalize scStateOf s c tgt h = k
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [scVal, scPresc] <;> field_simp <;> ring
  refine ⟨?_, fun i => by rw [hval]; rfl⟩
  unfold IsRepeatedSPNE
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound hg)]
  intro i h a
  have hp : osPlay (scProfile s c n tgt) h = scPresc s c n (scStateOf s c tgt h) := rfl
  by_cases ha : a = scPresc s c n (scStateOf s c tgt h) i
  · rw [hp, ha, update_eq_self, ← hp]
    exact (osValue_succ hδ0 hδ1 (stageU_bound hg) _ h i).ge
  rw [hval, hval, hp]
  simp only [scStateOf]
  rw [scTrans_deviate s c n tgt _ ha]
  simp only [stageU]
  generalize hk : scStateOf s c tgt h = k at ha ⊢
  rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simp only [scVal, scPresc, ite_true]
    have := hs i a
    have e : g i s + δ * (g i c / (1 - δ)) =
        (1 - δ) * g i s + δ * g i c + δ * (g i s + δ * (g i c / (1 - δ))) := by
      field_simp; ring
    linarith
  · simp only [scPresc] at ha ⊢
    simp only [show ((1 : Fin 3) = 0) = False by decide, ite_false, ite_true]
    exact hc i a ha
  · simp only [scVal, scPresc, show ((2 : Fin 3) = 0) = False by decide,
      show ((2 : Fin 3) = 1) = False by decide, ite_false]
    have := hn i a
    have e : g i n / (1 - δ) = g i n + δ * (g i n / (1 - δ)) := by field_simp; ring
    linarith

/-! ### Local constructions near `q*` -/

/-- Along a ray with common slope `a > 0`, the payoff `f` rises and the deviation gain `h − f`
is small relative to it: for every `κ > 0`, eventually (as `s ↓ 0`) `f(0) < f(s)` and
`h(s) − f(s) ≤ κ(f(s) − f(0))`. -/
theorem stage_local_pos {f h : ℝ → ℝ} {a κ : ℝ} (hf : HasDerivAt f a 0) (hh : HasDerivAt h a 0)
    (h0 : f 0 = h 0) (ha : 0 < a) (hκ : 0 < κ) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f 0 < f s ∧ h s - f s ≤ κ * (f s - f 0) := by
  set ε := min (a / 2) (κ * a / 4) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hf' := (hf.isLittleO.bound hεpos)
  have hh' := (hh.isLittleO.bound hεpos)
  filter_upwards [nhdsWithin_le_nhds hf', nhdsWithin_le_nhds hh', self_mem_nhdsWithin]
    with s h1 h2 (hs : 0 < s)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hs] at h1 h2
  rw [abs_le] at h1 h2
  have e1 : ε ≤ a / 2 := min_le_left _ _
  have e2 : ε ≤ κ * a / 4 := min_le_right _ _
  have k1 : κ * (s * a - ε * s) ≤ κ * (f s - f 0) := mul_le_mul_of_nonneg_left (by linarith) hκ.le
  have k2 : ε * s ≤ κ * a / 4 * s := mul_le_mul_of_nonneg_right e2 hs.le
  have k3 : κ * (ε * s) ≤ κ * (a / 2 * s) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e1 hs.le) hκ.le
  constructor
  · nlinarith
  · nlinarith

/-- Along a ray with common slope `a < 0`: eventually `f(s) < f(0)` and
`h(s) ≤ (1 − δ)f(s) + δf(0)`, for any `δ ∈ (0, 1)`. -/
theorem stage_local_neg {f h : ℝ → ℝ} {a δ : ℝ} (hf : HasDerivAt f a 0) (hh : HasDerivAt h a 0)
    (h0 : f 0 = h 0) (ha : a < 0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < f 0 ∧ h s ≤ (1 - δ) * f s + δ * f 0 := by
  set ε := -(δ * a) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; nlinarith
  have hf' := (hf.isLittleO.bound hεpos)
  have hh' := (hh.isLittleO.bound hεpos)
  filter_upwards [nhdsWithin_le_nhds hf', nhdsWithin_le_nhds hh', self_mem_nhdsWithin]
    with s h1 h2 (hs : 0 < s)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hs] at h1 h2
  rw [abs_le] at h1 h2
  constructor
  · nlinarith
  · nlinarith [mul_pos hδ0 hs]

/-- Best-response payoffs do not depend on the player's own action. -/
theorem bestReplyValue_update (g : I → ((i : I) → A i) → ℝ) (i : I) (x : (i : I) → A i)
    (b : A i) : bestReplyValue g i (update x i b) = bestReplyValue g i x := by
  unfold bestReplyValue
  congr 1
  funext a
  rw [update_idem]

/-- The payoff along the ray `q* + s·d` has derivative `L d` at `s = 0`. -/
theorem hasDerivAt_along {φ : (Fin 2 → ℝ) → ℝ} {L : (Fin 2 → ℝ) →L[ℝ] ℝ} {q d : Fin 2 → ℝ}
    (hφ : HasFDerivAt φ L q) :
    HasDerivAt (fun s : ℝ => φ (q + s • d)) (L d) 0 := by
  have hline : HasDerivAt (fun s : ℝ => q + s • d) d 0 := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id' 0
    simpa using HasDerivAt.smul_const hid d
  exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => q + s • d) 0 (by simpa using hφ) hline

theorem L_apply_two {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (d : Fin 2 → ℝ) :
    L d = d 0 * L (Pi.single 0 1) + d 1 * L (Pi.single 1 1) := by
  have : d = d 0 • (Pi.single 0 1 : Fin 2 → ℝ) + d 1 • Pi.single 1 1 := by
    funext k; fin_cases k <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The data of Propositions 12.AA.1 and 12.AA.4: a two-player game with actions in `ℝ`,
payoffs differentiable at the stage Nash equilibrium `q*` (derivatives `L₀`, `L₁`), the
first-order conditions `∂π_i/∂q_i(q*) = 0`, nonzero cross partials `∂π_i/∂q_j(q*) ≠ 0`, and the
envelope property (12.AA.6): `q_j ↦ π̂_i(q_j)` is differentiable at `q_j*` with derivative
`∂π_i/∂q_j(q*)`. -/
structure LocalGameData (g : Fin 2 → (Fin 2 → ℝ) → ℝ) (qs : Fin 2 → ℝ) where
  L0 : (Fin 2 → ℝ) →L[ℝ] ℝ
  L1 : (Fin 2 → ℝ) →L[ℝ] ℝ
  deriv0 : HasFDerivAt (g 0) L0 qs
  deriv1 : HasFDerivAt (g 1) L1 qs
  own0 : L0 (Pi.single 0 1) = 0
  own1 : L1 (Pi.single 1 1) = 0
  cross0 : L0 (Pi.single 1 1) ≠ 0
  cross1 : L1 (Pi.single 0 1) ≠ 0
  env0 : HasDerivAt (fun y => bestReplyValue g 0 (update qs 1 y)) (L0 (Pi.single 1 1)) (qs 1)
  env1 : HasDerivAt (fun y => bestReplyValue g 1 (update qs 0 y)) (L1 (Pi.single 0 1)) (qs 0)

/-- Slopes along the ray `d = (σ∂π₂/∂q₁, σ∂π₁/∂q₂)`: player `i`'s payoff and best-response
payoff both have slope `σ(∂π_i/∂q_j)²`. -/
theorem localGame_slopes {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ}
    (D : LocalGameData g qs) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => g 0 (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L0 (Pi.single 1 1) ^ 2) 0 ∧
    HasDerivAt (fun s : ℝ => bestReplyValue g 0
      (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L0 (Pi.single 1 1) ^ 2) 0 ∧
    HasDerivAt (fun s : ℝ => g 1 (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L1 (Pi.single 0 1) ^ 2) 0 ∧
    HasDerivAt (fun s : ℝ => bestReplyValue g 1
      (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L1 (Pi.single 0 1) ^ 2) 0 := by
  set d : Fin 2 → ℝ := ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)] with hd
  have hd0 : d 0 = σ * D.L1 (Pi.single 0 1) := rfl
  have hd1 : d 1 = σ * D.L0 (Pi.single 1 1) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hasDerivAt_along (d := d) D.deriv0
    rw [L_apply_two, D.own0, hd1] at h
    convert h using 1; ring
  · have hfun : (fun s : ℝ => bestReplyValue g 0 (qs + s • d)) =
        fun s => bestReplyValue g 0 (update qs 1 (qs 1 + s * d 1)) := by
      funext s
      rw [← bestReplyValue_update g 0 (qs + s • d) (qs 0)]
      congr 1
      funext k; fin_cases k <;> simp [update]
    rw [hfun]
    have hid : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id' 0
    have hin : HasDerivAt (fun s : ℝ => qs 1 + s * d 1) (d 1) 0 := by
      simpa using HasDerivAt.mul_const hid (d 1)
    have := D.env0.comp_of_eq (0 : ℝ) hin (by simp)
    exact this.congr_deriv (by rw [hd1]; ring)
  · have h := hasDerivAt_along (d := d) D.deriv1
    rw [L_apply_two, D.own1, hd0] at h
    convert h using 1; ring
  · have hfun : (fun s : ℝ => bestReplyValue g 1 (qs + s • d)) =
        fun s => bestReplyValue g 1 (update qs 0 (qs 0 + s * d 0)) := by
      funext s
      rw [← bestReplyValue_update g 1 (qs + s • d) (qs 1)]
      congr 1
      funext k; fin_cases k <;> simp [update]
    rw [hfun]
    have hid : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id' 0
    have hin : HasDerivAt (fun s : ℝ => qs 0 + s * d 0) (d 0) 0 := by
      simpa using HasDerivAt.mul_const hid (d 0)
    have := D.env1.comp_of_eq (0 : ℝ) hin (by simp)
    exact this.congr_deriv (by rw [hd0]; ring)

theorem bestReplyValue_nash {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs) (i : I) : bestReplyValue g i qs = g i qs := by
  have : Nonempty (A i) := ⟨qs i⟩
  refine le_antisymm (ciSup_le fun a => hqs i a) ?_
  have := le_bestReplyValue hg i qs (qs i)
  rwa [update_eq_self] at this

/-- **Proposition 12.AA.1** (MWG, p. 419), under the envelope property (12.AA.6). In a
two-player game with actions in `ℝ`, bounded payoffs and stage Nash equilibrium `q*` satisfying
the conditions of `LocalGameData`, for every `δ ∈ (0, 1)` there is `q'` with
`π_i(q') > π_i(q*)` for both players whose infinite repetition is the outcome path of a Nash
reversion SPNE. -/
theorem proposition_12_AA_1 {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    (D : LocalGameData g qs) :
    ∃ q', (∀ i, g i qs < g i q') ∧ IsRepeatedSPNE g δ (nashReversion (fun _ => q') qs) := by
  obtain ⟨h0, h0', h1, h1'⟩ := localGame_slopes D 1
  have hbr := bestReplyValue_nash hg hqs
  have hκ : 0 < δ / (1 - δ) := div_pos hδ0 (by linarith)
  have e0 := stage_local_pos h0 h0' (by simp [hbr 0]) (by
    have := D.cross0; positivity) hκ
  have e1 := stage_local_pos h1 h1' (by simp [hbr 1]) (by
    have := D.cross1; positivity) hκ
  obtain ⟨s, ⟨a0, b0⟩, ⟨a1, b1⟩⟩ := (e0.and e1).exists
  simp only [zero_smul, add_zero] at a0 b0 a1 b1
  set q' := qs + s • ![1 * D.L1 (Pi.single 0 1), 1 * D.L0 (Pi.single 1 1)]
  refine ⟨q', by rw [Fin.forall_fin_two]; exact ⟨a0, a1⟩, ?_⟩
  refine lemma_12_AA_1_if hδ0.le hδ1 hg _ hqs fun t i => ?_
  rw [eq_12_AA_3 g hδ0.le hδ1 q' qs t i]
  fin_cases i
  · exact b0
  · exact b1

/-- **Proposition 12.AA.4 and Exercise 12.AA.2** (MWG, pp. 421 and 435), under the envelope
property (12.AA.6). Under the conditions of Proposition 12.AA.1, for every `δ ∈ (0, 1)` some
stick-and-carrot SPNE (play `q'` once, then `q*` forever, restarting after any deviation) gives
both players average payoffs `(1 − δ)v_i' < π_i(q*)`. -/
theorem proposition_12_AA_4 {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    (D : LocalGameData g qs) :
    ∃ q', (∀ i, g i q' < g i qs) ∧ IsRepeatedSPNE g δ (scProfile q' qs qs 0) ∧
      ∀ i, (1 - δ) * osValue (stageU g) δ (scProfile q' qs qs 0) [] i < g i qs := by
  obtain ⟨h0, h0', h1, h1'⟩ := localGame_slopes D (-1)
  have hbr := bestReplyValue_nash hg hqs
  have e0 := stage_local_neg h0 h0' (by simp [hbr 0]) (by
    have : 0 < D.L0 (Pi.single 1 1) ^ 2 := by have := D.cross0; positivity
    linarith) hδ0 hδ1
  have e1 := stage_local_neg h1 h1' (by simp [hbr 1]) (by
    have : 0 < D.L1 (Pi.single 0 1) ^ 2 := by have := D.cross1; positivity
    linarith) hδ0 hδ1
  obtain ⟨s, ⟨a0, b0⟩, ⟨a1, b1⟩⟩ := (e0.and e1).exists
  simp only [zero_smul, add_zero] at a0 b0 a1 b1
  set q' := qs + s • ![-1 * D.L1 (Pi.single 0 1), -1 * D.L0 (Pi.single 1 1)]
  have hlt : ∀ i, g i q' < g i qs := by rw [Fin.forall_fin_two]; exact ⟨a0, a1⟩
  have hb : ∀ i, bestReplyValue g i q' ≤ (1 - δ) * g i q' + δ * g i qs := by
    rw [Fin.forall_fin_two]; exact ⟨b0, b1⟩
  have h1δ : (1 - δ) ≠ 0 := by linarith
  obtain ⟨hspne, hval⟩ := scProfile_spne hδ0.le hδ1 hg q' qs qs 0 hqs
    (fun i a => (le_bestReplyValue hg i q' a).trans (hb i))
    (fun i a _ => by
      simp only [scVal]
      have := hqs i a
      have := hlt i
      have e : g i qs / (1 - δ) = g i qs + δ * (g i qs / (1 - δ)) := by field_simp; ring
      nlinarith)
  refine ⟨q', hlt, hspne, fun i => ?_⟩
  rw [hval]
  have := hlt i
  have e : (1 - δ) * (g i q' + δ * (g i qs / (1 - δ))) = (1 - δ) * g i q' + δ * g i qs := by
    field_simp
  rw [e]
  nlinarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Instances of Propositions 12.AA.1 and 12.AA.4; Example 12.AA.1

MWG, pp. 419-423.

* `locG`: a bounded two-player game on `ℝ²`, `π_i(q) = φ(q_j) − ψ(q_i)` with
  `φ(x) = x/(1 + x²)` and `ψ(x) = x²/(1 + x²)`, whose unique stage Nash equilibrium `q* = 0`
  satisfies all conditions of `LocalGameData` (`locG_data`); hence Propositions 12.AA.1 and
  12.AA.4 apply (`proposition_12_AA_1_instance`, `proposition_12_AA_4_instance`).
* `example_12_AA_1`: the Cournot stick-and-carrot SPNE with average payoff `0`, for quantities
  in a compact interval `[0, B]` (footnote 36).
* `example_12_AA_1_qbar`: as `δ → 1`, the stick `q̄` solving (12.AA.7) exists and exceeds the
  competitive quantity `q_c`.
* `example_12_AA_1_instance`: `p(x) = max(4 − x, 0)`, `c = 1`, `δ = 9/10`, `B = 11`,
  `q̄ = 81/8`, `qᵐ = 3/4`, `q* = (1, 1)`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

/-- `φ(x) = x/(1 + x²)`. -/
noncomputable def locPhi (x : ℝ) : ℝ := x / (1 + x ^ 2)

/-- `ψ(x) = x²/(1 + x²)`. -/
noncomputable def locPsi (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2)

/-- The game `π_i(q) = φ(q_j) − ψ(q_i)`. -/
noncomputable def locG (i : Fin 2) (q : Fin 2 → ℝ) : ℝ :=
  if i = 0 then locPhi (q 1) - locPsi (q 0) else locPhi (q 0) - locPsi (q 1)

theorem locPhi_abs (x : ℝ) : |locPhi x| ≤ 1 := by
  unfold locPhi
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2), div_le_one (by positivity)]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; nlinarith [sq_nonneg (x - 1)]
  · rw [abs_of_nonpos h]; nlinarith [sq_nonneg (x + 1)]

theorem locPsi_nonneg (x : ℝ) : 0 ≤ locPsi x := by unfold locPsi; positivity

theorem locPsi_le (x : ℝ) : locPsi x ≤ 1 := by
  unfold locPsi; rw [div_le_one (by positivity)]; linarith

theorem locG_bound : ∀ i x, |locG i x| ≤ 2 := by
  intro i x
  unfold locG
  split_ifs <;>
  · rw [abs_le]
    constructor <;> linarith [abs_le.1 (locPhi_abs (x 1)), abs_le.1 (locPhi_abs (x 0)),
      locPsi_nonneg (x 0), locPsi_nonneg (x 1), locPsi_le (x 0), locPsi_le (x 1)]

theorem locG_nash : IsStageNash locG 0 := by
  have h0 : ∀ j, locG j 0 = 0 := fun j => by
    unfold locG; split_ifs <;> simp [locPhi, locPsi]
  have hφ : locPhi 0 = 0 := by simp [locPhi]
  unfold IsStageNash
  rw [Fin.forall_fin_two]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have : locG 0 (update 0 0 a) = locPhi 0 - locPsi a := by simp [locG, update]
    rw [this, hφ, h0]; linarith [locPsi_nonneg a]
  · have : locG 1 (update 0 1 a) = locPhi 0 - locPsi a := by simp [locG, update]
    rw [this, hφ, h0]; linarith [locPsi_nonneg a]

theorem locPhi_hasDerivAt : HasDerivAt locPhi 1 0 := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * 0) 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_add 1
  have := (hasDerivAt_id' (0 : ℝ)).div h1 (by norm_num)
  exact this.congr_deriv (by norm_num)

theorem locPsi_hasDerivAt : HasDerivAt locPsi 0 0 := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * 0) 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * 0) 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have := h2.div h1 (by norm_num)
  exact this.congr_deriv (by norm_num)

theorem locG_bestReply (i : Fin 2) (y : ℝ) :
    bestReplyValue locG i (update 0 (1 - i) y) = locPhi y := by
  unfold bestReplyValue
  refine le_antisymm (ciSup_le fun a => ?_) ?_
  · fin_cases i <;> simp [locG, update] <;> linarith [locPsi_nonneg a]
  · refine le_trans ?_ (le_ciSup (f := fun a => locG i (update (update 0 (1 - i) y) i a))
      ⟨2, fun _ ⟨b, hb⟩ => hb ▸ (le_abs_self _).trans (locG_bound i _)⟩ 0)
    fin_cases i <;> simp [locG, update, locPsi]

/-- The game `locG` satisfies the hypotheses of Propositions 12.AA.1 and 12.AA.4 at `q* = 0`. -/
noncomputable def locG_data : LocalGameData locG 0 where
  L0 := (1 : ℝ) • ContinuousLinearMap.proj 1 - (0 : ℝ) • ContinuousLinearMap.proj 0
  L1 := (1 : ℝ) • ContinuousLinearMap.proj 0 - (0 : ℝ) • ContinuousLinearMap.proj 1
  deriv0 := by
    have hφ : HasDerivAt locPhi 1 ((0 : Fin 2 → ℝ) 1) := by simpa using locPhi_hasDerivAt
    have hψ : HasDerivAt locPsi 0 ((0 : Fin 2 → ℝ) 0) := by simpa using locPsi_hasDerivAt
    have h1 := hφ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ))
    have h2 := hψ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ))
    have := h1.sub h2
    convert this using 1
    funext q; simp [locG, Function.comp]
  deriv1 := by
    have hφ : HasDerivAt locPhi 1 ((0 : Fin 2 → ℝ) 0) := by simpa using locPhi_hasDerivAt
    have hψ : HasDerivAt locPsi 0 ((0 : Fin 2 → ℝ) 1) := by simpa using locPsi_hasDerivAt
    have h1 := hφ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ))
    have h2 := hψ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ))
    have := h1.sub h2
    convert this using 1
    funext q; simp [locG, Function.comp]
  own0 := by simp
  own1 := by simp
  cross0 := by simp
  cross1 := by simp
  env0 := by
    have : (fun y => bestReplyValue locG 0 (update 0 1 y)) = locPhi := by
      funext y; simpa using locG_bestReply 0 y
    rw [this]
    simpa using locPhi_hasDerivAt
  env1 := by
    have : (fun y => bestReplyValue locG 1 (update 0 0 y)) = locPhi := by
      funext y; simpa using locG_bestReply 1 y
    rw [this]
    simpa using locPhi_hasDerivAt

/-- **Proposition 12.AA.1, an instance**: in `locG` with `δ = 1/2`, a Pareto improvement over
`q* = 0` is sustained by Nash reversion. -/
theorem proposition_12_AA_1_instance :
    ∃ q', (∀ i, locG i 0 < locG i q') ∧
      IsRepeatedSPNE locG (1 / 2) (nashReversion (fun _ => q') 0) :=
  proposition_12_AA_1 (by norm_num) (by norm_num) locG_bound locG_nash locG_data

/-- **Proposition 12.AA.4, an instance**: in `locG` with `δ = 1/2`, a stick-and-carrot SPNE
gives both players less than their stage Nash payoff. -/
theorem proposition_12_AA_4_instance :
    ∃ q', (∀ i, locG i q' < locG i 0) ∧ IsRepeatedSPNE locG (1 / 2) (scProfile q' 0 0 0) ∧
      ∀ i, (1 - 1 / 2) * osValue (stageU locG) (1 / 2) (scProfile q' 0 0 0) [] i < locG i 0 :=
  proposition_12_AA_4 (by norm_num) (by norm_num) locG_bound locG_nash locG_data

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Propositions 12.AA.1 and 12.AA.4 as printed are false

MWG, Appendix A of Chapter 12, Propositions 12.AA.1 (p. 419) and 12.AA.4 (p. 421; Exercise
12.AA.2, p. 435).

MWG states both propositions for a two-player game with actions in `ℝ`, payoffs `π_i`
differentiable at the stage Nash equilibrium `q*`, and `∂π_i(q*)/∂q_j ≠ 0` (12.AA.4 adds
`π_i(q*) > π̲_i`). The proof of 12.AA.1 also uses the envelope property (12.AA.6), that the
best-response payoff `π̂_i` is differentiable at `q_j*` with derivative `∂π_i(q*)/∂q_j`; this does
not follow from the printed hypotheses, and without it both propositions fail.

* `sclG`: actions clamped to `S_i = [-1, 1]`; with `u = q_1`, `y = q_2` (after clamping),
  `π_1 = y − u² − min(u, 0)·|y|^{1/4}` and `π_2 = u − y²`. It has bounded payoffs, the unique
  stage Nash equilibrium `q* = 0`, best responses that exist, `π_i` differentiable at `q*` with
  cross partials `1`, and minimax payoffs below the Nash payoffs (`sclG_hypotheses`). But
  `π̂_1(y) = y + |y|^{1/2}/4`: a deviation gain of order `|y|^{1/2}`, not `o(|y|)`.
* `proposition_12_AA_1_false`: for every `δ ∈ (0, 1/5]` no `q'` with `π_i(q') > π_i(q*)` for
  both players is sustained by Nash reversion.
* `proposition_12_AA_4_false`: for every `δ ∈ (0, 1/2000]`, in every SPNE player 1's average
  payoff in every subgame is at least `π_1(q*)`, so no SPNE gives both players less.
* `counterexample_12_AA_1_4`: the two together, and `LocalGameData sclG 0` is empty.
* Corrected statements, `proposition_12_AA_1_upper` and `proposition_12_AA_4_upper`: MWG's
  hypotheses plus the one-sided bound
  `π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)`; the reverse bound already
  follows from `q*` being a Nash equilibrium and differentiability (`scl_env_of_upper`), as does
  `∂π_i(q*)/∂q_i = 0` (`scl_own_partial_zero`). Given those hypotheses the one-sided bound is
  equivalent to (12.AA.6) (`scl_upper_of_hasDerivAt`). Instances: `scl_upper_instance_1`,
  `scl_upper_instance_4`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

/-! ### The counterexample game -/

/-- Clamping to the action set `S_i = [-1, 1]`. -/
noncomputable def sclClamp (x : ℝ) : ℝ := max (-1) (min x 1)

/-- `|y|^{1/4}` of the clamped action `y`. -/
noncomputable def sclRoot (y : ℝ) : ℝ := Real.sqrt (Real.sqrt |sclClamp y|)

/-- The stage game: with `u = clamp(q_1)` and `y = clamp(q_2)`, player 1 (index `0`) gets
`y − u² − min(u, 0)·|y|^{1/4}` and player 2 (index `1`) gets `u − y²`. -/
noncomputable def sclG (i : Fin 2) (q : Fin 2 → ℝ) : ℝ :=
  if i = 0 then sclClamp (q 1) - sclClamp (q 0) ^ 2 - min (sclClamp (q 0)) 0 * sclRoot (q 1)
  else sclClamp (q 0) - sclClamp (q 1) ^ 2

theorem sclClamp_abs (x : ℝ) : |sclClamp x| ≤ 1 := by
  unfold sclClamp
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem sclClamp_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : sclClamp x = x := by
  unfold sclClamp
  rw [abs_le] at hx
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem sclClamp_eq_zero {x : ℝ} (hx : sclClamp x = 0) : x = 0 := by
  unfold sclClamp at hx
  rcases le_total x 1 with h | h
  · rw [min_eq_left h] at hx
    rcases le_total (-1) x with h' | h'
    · rwa [max_eq_right h'] at hx
    · rw [max_eq_left h'] at hx
      norm_num at hx
  · rw [min_eq_right h, max_eq_right (by norm_num)] at hx
    norm_num at hx

/-- The game depends on actions only through their clamped values: the action sets are
effectively the compact interval `[-1, 1]` (MWG, p. 417). -/
theorem sclG_clamp (i : Fin 2) (q : Fin 2 → ℝ) : sclG i (fun k => sclClamp (q k)) = sclG i q := by
  have e : ∀ x, sclClamp (sclClamp x) = sclClamp x := fun x => sclClamp_of_abs_le (sclClamp_abs x)
  simp only [sclG, sclRoot, e]

theorem sclClamp_zero : sclClamp 0 = 0 := sclClamp_of_abs_le (by simp)

theorem sclRoot_nonneg (y : ℝ) : 0 ≤ sclRoot y := Real.sqrt_nonneg _

theorem sclRoot_zero : sclRoot 0 = 0 := by simp [sclRoot, sclClamp_zero]

theorem sclRoot_sq (y : ℝ) : sclRoot y ^ 2 = Real.sqrt |sclClamp y| :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem sclRoot_le_one (y : ℝ) : sclRoot y ≤ 1 := by
  have h1 : Real.sqrt |sclClamp y| ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (sclClamp_abs y)
  simpa [sclRoot] using Real.sqrt_le_sqrt h1

/-- `|y| ≤ |y|^{1/2}` on `[-1, 1]`. -/
theorem sclRoot_sq_ge (y : ℝ) : |sclClamp y| ≤ sclRoot y ^ 2 := by
  rw [sclRoot_sq]
  have ht := sclClamp_abs y
  have hs := Real.sq_sqrt (abs_nonneg (sclClamp y))
  have hs0 := Real.sqrt_nonneg |sclClamp y|
  nlinarith

/-- `4|y| ≤ |y|^{1/2}` when `|y| ≤ 1/16`. -/
theorem sclRoot_sq_ge_four {y : ℝ} (hy : |sclClamp y| ≤ 1 / 16) :
    4 * |sclClamp y| ≤ sclRoot y ^ 2 := by
  rw [sclRoot_sq]
  have hs := Real.sq_sqrt (abs_nonneg (sclClamp y))
  have hs0 := Real.sqrt_nonneg |sclClamp y|
  have hs1 : Real.sqrt |sclClamp y| ≤ 1 / 4 := by nlinarith
  nlinarith

theorem sclG_bound : ∀ i x, |sclG i x| ≤ 3 := by
  intro i x
  have h0 := abs_le.1 (sclClamp_abs (x 0))
  have h1 := abs_le.1 (sclClamp_abs (x 1))
  have hr0 := sclRoot_nonneg (x 1)
  have hr1 := sclRoot_le_one (x 1)
  have hm1 : min (sclClamp (x 0)) 0 ≤ 0 := min_le_right _ _
  have hm2 : -1 ≤ min (sclClamp (x 0)) 0 := le_min h0.1 (by norm_num)
  have hp1 : min (sclClamp (x 0)) 0 * sclRoot (x 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm1 hr0
  have hp2 : -1 ≤ min (sclClamp (x 0)) 0 * sclRoot (x 1) := by nlinarith
  have hq0 : sclClamp (x 0) ^ 2 ≤ 1 := by nlinarith
  have hq1 : sclClamp (x 1) ^ 2 ≤ 1 := by nlinarith
  unfold sclG
  rw [abs_le]
  split_ifs
  · constructor <;> nlinarith [sq_nonneg (sclClamp (x 0))]
  · constructor <;> nlinarith [sq_nonneg (sclClamp (x 1))]

theorem sclG_zero_update (x : Fin 2 → ℝ) (a : ℝ) :
    sclG 0 (update x 0 a) =
      sclClamp (x 1) - sclClamp a ^ 2 - min (sclClamp a) 0 * sclRoot (x 1) := by
  simp [sclG]

theorem sclG_one_update (x : Fin 2 → ℝ) (a : ℝ) :
    sclG 1 (update x 1 a) = sclClamp (x 0) - sclClamp a ^ 2 := by
  simp [sclG]

theorem sclG_zero_val : ∀ i, sclG i 0 = 0 := by
  intro i
  fin_cases i <;> simp [sclG, sclClamp_zero, sclRoot_zero]

/-- Player 1's best-response payoff is `π̂_1(y) = y + |y|^{1/2}/4`, attained at
`u = −|y|^{1/4}/2`. -/
theorem sclG_br0 (x : Fin 2 → ℝ) :
    bestReplyValue sclG 0 x = sclClamp (x 1) + sclRoot (x 1) ^ 2 / 4 ∧
      sclG 0 (update x 0 (-sclRoot (x 1) / 2)) = bestReplyValue sclG 0 x := by
  have hr0 := sclRoot_nonneg (x 1)
  have hr1 := sclRoot_le_one (x 1)
  have hat : sclG 0 (update x 0 (-sclRoot (x 1) / 2)) =
      sclClamp (x 1) + sclRoot (x 1) ^ 2 / 4 := by
    rw [sclG_zero_update, sclClamp_of_abs_le (x := -sclRoot (x 1) / 2)
      (by rw [abs_le]; constructor <;> linarith), min_eq_left (by linarith)]
    ring
  have hbr : bestReplyValue sclG 0 x = sclClamp (x 1) + sclRoot (x 1) ^ 2 / 4 := by
    refine le_antisymm (ciSup_le fun a => ?_) ?_
    · rw [sclG_zero_update]
      rcases le_total 0 (sclClamp a) with h | h
      · rw [min_eq_right h]
        nlinarith [sq_nonneg (sclClamp a)]
      · rw [min_eq_left h]
        nlinarith [sq_nonneg (sclClamp a + sclRoot (x 1) / 2)]
    · rw [← hat]
      exact le_bestReplyValue sclG_bound 0 x _
  exact ⟨hbr, by rw [hat, hbr]⟩

/-- Player 2's best-response payoff is `π̂_2(u) = u`, attained at `y = 0`. -/
theorem sclG_br1 (x : Fin 2 → ℝ) :
    bestReplyValue sclG 1 x = sclClamp (x 0) ∧ sclG 1 (update x 1 0) = bestReplyValue sclG 1 x := by
  have hat : sclG 1 (update x 1 0) = sclClamp (x 0) := by
    rw [sclG_one_update, sclClamp_zero]
    ring
  have hbr : bestReplyValue sclG 1 x = sclClamp (x 0) := by
    refine le_antisymm (ciSup_le fun a => ?_) ?_
    · rw [sclG_one_update]
      nlinarith [sq_nonneg (sclClamp a)]
    · rw [← hat]
      exact le_bestReplyValue sclG_bound 1 x _
  exact ⟨hbr, by rw [hat, hbr]⟩

theorem sclG_nash : IsStageNash sclG 0 := by
  intro i a
  rw [sclG_zero_val]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [sclG_zero_update]
    simp only [Pi.zero_apply, sclClamp_zero, sclRoot_zero, mul_zero, sub_zero, zero_sub,
      Left.neg_nonpos_iff]
    exact sq_nonneg _
  · simp only [Fin.mk_one, Fin.isValue]
    rw [sclG_one_update]
    simp only [Pi.zero_apply, sclClamp_zero, zero_sub, Left.neg_nonpos_iff]
    exact sq_nonneg _

theorem sclG_nash_unique (x : Fin 2 → ℝ) (hx : IsStageNash sclG x) : x = 0 := by
  have h1 := hx 1 0
  rw [sclG_one_update, sclClamp_zero] at h1
  simp only [sclG, Fin.isValue, one_ne_zero, ↓reduceIte] at h1
  have hx1 : x 1 = 0 := sclClamp_eq_zero (by nlinarith [sq_nonneg (sclClamp (x 1))])
  have h0 := hx 0 0
  rw [sclG_zero_update, sclClamp_zero] at h0
  simp only [sclG, ↓reduceIte, hx1, sclClamp_zero, sclRoot_zero] at h0
  have hx0 : x 0 = 0 := sclClamp_eq_zero (by nlinarith [sq_nonneg (sclClamp (x 0))])
  funext k
  fin_cases k
  · exact hx0
  · exact hx1

/-- Player 1's payoff is differentiable at `q* = 0` with derivative `(0, 1)`. -/
theorem sclG_deriv0 :
    HasFDerivAt (sclG 0) (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hρ : 0 < min 1 (min (c / 2) ((c / 2) ^ 4)) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Fin 2 → ℝ) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hb1 : ‖h‖ < 1 := hh.trans_le (min_le_left _ _)
  have hb2 : ‖h‖ < c / 2 := hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hb3 : ‖h‖ < (c / 2) ^ 4 := hh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have h0 : |h 0| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 0
  have h1 : |h 1| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 1
  have e0 : sclClamp (h 0) = h 0 := sclClamp_of_abs_le (by linarith)
  have e1 : sclClamp (h 1) = h 1 := sclClamp_of_abs_le (by linarith)
  have hr : sclRoot (h 1) ≤ c / 2 := by
    unfold sclRoot
    rw [e1]
    have h4 : |h 1| ≤ ((c / 2) ^ 2) ^ 2 := by rw [← pow_mul]; linarith
    have s1 : Real.sqrt |h 1| ≤ (c / 2) ^ 2 :=
      (Real.sqrt_le_sqrt h4).trans_eq (Real.sqrt_sq (by positivity))
    exact (Real.sqrt_le_sqrt s1).trans_eq (Real.sqrt_sq (by positivity))
  have hr0 := sclRoot_nonneg (h 1)
  have hm : |min (h 0) 0| ≤ |h 0| := by
    rcases le_total (h 0) 0 with h' | h'
    · rw [min_eq_left h']
    · rw [min_eq_right h', abs_zero]
      exact abs_nonneg _
  have p1 : h 0 ^ 2 ≤ ‖h‖ * (c / 2) := by
    rw [← sq_abs]
    calc |h 0| ^ 2 = |h 0| * |h 0| := sq _
      _ ≤ ‖h‖ * (c / 2) := mul_le_mul h0 (by linarith) (abs_nonneg _) (norm_nonneg _)
  have p2 : |min (h 0) 0 * sclRoot (h 1)| ≤ ‖h‖ * (c / 2) := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul (hm.trans h0) hr hr0 (norm_nonneg _)
  have p2' := abs_le.1 p2
  rw [zero_add, sclG_zero_val, Real.norm_eq_abs, ContinuousLinearMap.proj_apply]
  simp only [sclG, ↓reduceIte, e0, e1]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (h 0)]

/-- Player 2's payoff is differentiable at `q* = 0` with derivative `(1, 0)`. -/
theorem sclG_deriv1 :
    HasFDerivAt (sclG 1) (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hρ : 0 < min 1 c := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Fin 2 → ℝ) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hb1 : ‖h‖ < 1 := hh.trans_le (min_le_left _ _)
  have hb2 : ‖h‖ < c := hh.trans_le (min_le_right _ _)
  have h0 : |h 0| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 0
  have h1 : |h 1| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 1
  have e0 : sclClamp (h 0) = h 0 := sclClamp_of_abs_le (by linarith)
  have e1 : sclClamp (h 1) = h 1 := sclClamp_of_abs_le (by linarith)
  have p1 : h 1 ^ 2 ≤ c * ‖h‖ := by
    rw [← sq_abs]
    calc |h 1| ^ 2 = |h 1| * |h 1| := sq _
      _ ≤ c * ‖h‖ := mul_le_mul (by linarith) h1 (abs_nonneg _) hc.le
  rw [zero_add, sclG_zero_val, Real.norm_eq_abs, ContinuousLinearMap.proj_apply]
  simp only [sclG, Fin.isValue, one_ne_zero, ↓reduceIte, e0, e1]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (h 1)]

/-- **The counterexample satisfies MWG's hypotheses** (pp. 417, 419, 421): bounded payoffs
depending on actions only through `[-1, 1]` (`sclG_clamp`), the unique pure stage Nash
equilibrium `q* = 0`, best responses that exist (footnote 31), `π_i` differentiable at `q*` with
`∂π_1(q*)/∂q_2 = ∂π_2(q*)/∂q_1 = 1 ≠ 0`, and minimax payoffs `π̲_i < π_i(q*)`. -/
theorem sclG_hypotheses :
    (∀ i x, |sclG i x| ≤ 3) ∧ IsStageNash sclG 0 ∧ (∀ x, IsStageNash sclG x → x = 0) ∧
    (∀ i x, ∃ a, sclG i (update x i a) = bestReplyValue sclG i x) ∧
    HasFDerivAt (sclG 0) (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
    HasFDerivAt (sclG 1) (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 1 1) ≠ 0 ∧
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 0 1) ≠ 0 ∧
    ∀ i, minimaxValue sclG i < sclG i 0 := by
  refine ⟨sclG_bound, sclG_nash, sclG_nash_unique, ?_, sclG_deriv0, sclG_deriv1, by simp,
    by simp, ?_⟩
  · intro i x
    fin_cases i
    · exact ⟨_, (sclG_br0 x).2⟩
    · exact ⟨_, (sclG_br1 x).2⟩
  · intro i
    rw [sclG_zero_val]
    have hbdd : BddBelow (Set.range fun x : Fin 2 → ℝ => bestReplyValue sclG i x) :=
      ⟨-3, fun _ ⟨x, hx⟩ => hx ▸ bestReplyValue_ge sclG_bound i x⟩
    refine lt_of_le_of_lt (ciInf_le hbdd (fun _ => -1)) ?_
    have hc : sclClamp (-1) = -1 := sclClamp_of_abs_le (by norm_num)
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [(sclG_br0 _).1]
      have hr : sclRoot (-1) = 1 := by simp [sclRoot, hc]
      simp only [hc, hr]
      norm_num
    · simp only [Fin.mk_one, Fin.isValue]
      rw [(sclG_br1 _).1, hc]
      norm_num

/-! ### Proposition 12.AA.1 fails -/

/-- **Proposition 12.AA.1 is false as printed** (MWG, p. 419). In `sclG`, for every
`δ ∈ (0, 1/5]`, no `q'` with `π_i(q') > π_i(q*)` for both players is sustained by Nash reversion:
player 1's gain from deviating to `−|q_2'|^{1/4}/2` is `|q_2'|^{1/2}/4 + q_1'^2`, more than
`δ/(1 − δ)` times the gain `π_1(q') − π_1(q*) < q_2'`. -/
theorem proposition_12_AA_1_false {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 5) (q' : Fin 2 → ℝ)
    (hq' : ∀ i, sclG i 0 < sclG i q') :
    ¬ IsRepeatedSPNE sclG δ (nashReversion (fun _ => q') 0) := by
  intro hspne
  have hδ1 : δ < 1 := by linarith
  rw [nashReversion_spne_iff hδ0.le hδ1 sclG_bound _ sclG_nash] at hspne
  have hp0 := hq' 0
  have hp1 := hq' 1
  rw [sclG_zero_val] at hp0 hp1
  simp only [sclG, Fin.isValue, one_ne_zero, ↓reduceIte] at hp0 hp1
  have hr0 := sclRoot_nonneg (q' 1)
  have hr1 := sclRoot_le_one (q' 1)
  have hu : 0 < sclClamp (q' 0) := by nlinarith [sq_nonneg (sclClamp (q' 1))]
  rw [min_eq_right hu.le, zero_mul, sub_zero] at hp0
  have hy : 0 < sclClamp (q' 1) := by nlinarith [sq_nonneg (sclClamp (q' 0))]
  have hca : sclClamp (-sclRoot (q' 1) / 2) = -sclRoot (q' 1) / 2 :=
    sclClamp_of_abs_le (by rw [abs_le]; constructor <;> linarith)
  have ha : -sclRoot (q' 1) / 2 ≠ q' 0 := by
    intro h
    rw [h] at hca
    rw [hca] at hu
    linarith
  have key := hspne 0 0 _ ha
  rw [pathValue_const sclG hδ0.le hδ1, sclG_zero_update, sclG_zero_val, hca,
    min_eq_left (by linarith)] at key
  have hge := sclRoot_sq_ge (q' 1)
  rw [abs_of_pos hy] at hge
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  simp only [sclG, ↓reduceIte, min_eq_right hu.le, zero_mul, sub_zero, zero_div, mul_zero,
    add_zero] at key
  rw [le_div_iff₀ h1δ] at key
  nlinarith [sq_pos_of_pos hu, mul_le_mul_of_nonneg_left hge h1δ.le]

/-! ### Proposition 12.AA.4 fails -/

/-- In every SPNE of the repeated `sclG` game, player 2's action at every history satisfies
`clamp(q_2)² ≤ 6δ/(1 − δ)`: playing `0` instead gains `clamp(q_2)²` now and loses at most the
range `6/(1 − δ)` of continuation values. -/
theorem sclG_spne_action_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : OSProfile fun _ : Fin 2 => ℝ} (hσ : IsRepeatedSPNE sclG δ σ)
    (h : OSHist fun _ : Fin 2 => ℝ) :
    sclClamp (σ 1 h) ^ 2 ≤ 6 * δ / (1 - δ) := by
  have hos := (oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound sclG_bound) σ).1
    hσ 1 h 0
  rw [osValue_succ hδ0 hδ1 (stageU_bound sclG_bound) σ h 1] at hos
  have hV1 := abs_le.1 (osValue_abs_le hδ0 hδ1 (stageU_bound sclG_bound) σ
    (osPlay σ h :: h) 1)
  have hV2 := abs_le.1 (osValue_abs_le hδ0 hδ1 (stageU_bound sclG_bound) σ
    (update (osPlay σ h) 1 0 :: h) 1)
  simp only [stageU] at hos
  rw [sclG_one_update, sclClamp_zero] at hos
  have e : sclG 1 (osPlay σ h) = sclClamp (σ 0 h) - sclClamp (σ 1 h) ^ 2 := by
    simp [sclG, osPlay]
  have e2 : (osPlay σ h) 0 = σ 0 h := rfl
  rw [e, e2] at hos
  have hd : δ * (osValue (stageU sclG) δ σ (osPlay σ h :: h) 1 -
      osValue (stageU sclG) δ σ (update (osPlay σ h) 1 0 :: h) 1) ≤ δ * (6 / (1 - δ)) :=
    mul_le_mul_of_nonneg_left (by
      have : 6 / (1 - δ) = 3 / (1 - δ) + 3 / (1 - δ) := by ring
      linarith [hV1.2, hV2.1]) hδ0
  have e3 : 6 * δ / (1 - δ) = δ * (6 / (1 - δ)) := by ring
  rw [e3]
  nlinarith

/-- In every SPNE of the repeated `sclG` game with `δ ∈ [0, 1/2000]`, player 1's payoff in every
subgame is nonnegative: player 2's actions satisfy `|clamp(q_2)| ≤ 1/16`, where
`π̂_1(q_2) = clamp(q_2) + |clamp(q_2)|^{1/2}/4 ≥ 0`, so best-responding period by period secures
`0 = π_1(q*)`. -/
theorem sclG_spne_value_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2000)
    {σ : OSProfile fun _ : Fin 2 => ℝ} (hσ : IsRepeatedSPNE sclG δ σ)
    (h : OSHist fun _ : Fin 2 => ℝ) :
    0 ≤ osValue (stageU sclG) δ σ h 0 := by
  have hδ1 : δ < 1 := by linarith
  set τ : OSHist (fun _ : Fin 2 => ℝ) → ℝ := fun h' => -sclRoot (σ 1 h') / 2 with hτ
  have hterm : ∀ h', 0 ≤ stageU sclG 0 h' (osPlay (update σ 0 τ) h') := by
    intro h'
    rw [osPlay_update]
    simp only [stageU]
    have hsq := sclG_spne_action_sq hδ0 hδ1 hσ h'
    have hsmall : 6 * δ / (1 - δ) ≤ 1 / 256 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hc : |sclClamp (σ 1 h')| ≤ 1 / 16 := by
      have := sq_abs (sclClamp (σ 1 h'))
      nlinarith [abs_nonneg (sclClamp (σ 1 h'))]
    have h4 := sclRoot_sq_ge_four hc
    have hv := (sclG_br0 (osPlay σ h')).2
    rw [(sclG_br0 (osPlay σ h')).1] at hv
    have e : (osPlay σ h') 1 = σ 1 h' := rfl
    simp only [hτ, ← e]
    rw [hv]
    rw [e]
    nlinarith [neg_abs_le (sclClamp (σ 1 h'))]
  have hnn : 0 ≤ osValue (stageU sclG) δ (update σ 0 τ) h 0 :=
    tsum_nonneg fun n => mul_nonneg (pow_nonneg hδ0 n) (hterm _)
  exact hnn.trans (hσ 0 τ h)

/-- **Proposition 12.AA.4 (Exercise 12.AA.2) is false as printed** (MWG, pp. 421, 435). In
`sclG`, for every `δ ∈ (0, 1/2000]`, no SPNE gives both players average payoffs
`(1 − δ)v_i' < π_i(q*)`. -/
theorem proposition_12_AA_4_false {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2000) :
    ¬ ∃ σ : OSProfile (fun _ : Fin 2 => ℝ), IsRepeatedSPNE sclG δ σ ∧
      ∀ i, (1 - δ) * osValue (stageU sclG) δ σ [] i < sclG i 0 := by
  rintro ⟨σ, hσ, hlt⟩
  have h1 := hlt 0
  have h2 := sclG_spne_value_nonneg hδ0.le hδ hσ []
  rw [sclG_zero_val] at h1
  have : 0 ≤ (1 - δ) * osValue (stageU sclG) δ σ [] 0 := mul_nonneg (by linarith) h2
  linarith

/-- **Propositions 12.AA.1 and 12.AA.4 are false as printed** (MWG, pp. 419, 421). The game
`sclG` satisfies every printed hypothesis (`sclG_hypotheses`), yet at `δ = 1/5` no Pareto
improvement over `q*` is sustained by Nash reversion, and at `δ = 1/2000` no SPNE gives both
players less than `π_i(q*)`. Consequently the envelope property (12.AA.6) fails there:
`LocalGameData sclG 0` is empty. -/
theorem counterexample_12_AA_1_4 :
    (∀ q' : Fin 2 → ℝ, (∀ i, sclG i 0 < sclG i q') →
      ¬ IsRepeatedSPNE sclG (1 / 5) (nashReversion (fun _ => q') 0)) ∧
    (¬ ∃ σ : OSProfile (fun _ : Fin 2 => ℝ), IsRepeatedSPNE sclG (1 / 2000) σ ∧
      ∀ i, (1 - 1 / 2000) * osValue (stageU sclG) (1 / 2000) σ [] i < sclG i 0) ∧
    IsEmpty (LocalGameData sclG 0) := by
  refine ⟨fun q' hq' => proposition_12_AA_1_false (by norm_num) le_rfl q' hq',
    proposition_12_AA_4_false (by norm_num) le_rfl, ⟨fun D => ?_⟩⟩
  obtain ⟨q', hq', hs⟩ := proposition_12_AA_1 (δ := 1 / 5) (by norm_num) (by norm_num)
    sclG_bound sclG_nash D
  exact proposition_12_AA_1_false (by norm_num) le_rfl q' hq' hs

/-! ### The corrected statements -/

/-- At a stage Nash equilibrium where `π_i` is differentiable, `∂π_i(q*)/∂q_i = 0`
((12.AA.4), MWG, p. 419). -/
theorem scl_own_partial_zero {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ}
    {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (i : Fin 2) (hd : HasFDerivAt (g i) L qs)
    (hqs : IsStageNash g qs) : L (Pi.single i 1) = 0 := by
  have hc := hd.comp_hasDerivAt_of_eq (qs i) (hasDerivAt_update qs i (qs i))
    (update_eq_self i qs).symm
  have hmax : IsLocalMax (g i ∘ update qs i) (qs i) :=
    Eventually.of_forall fun s => by
      change g i (update qs i s) ≤ g i (update qs i (qs i))
      rw [update_eq_self]
      exact hqs i s
  exact hmax.hasDerivAt_eq_zero hc

/-- A function squeezed between a differentiable lower bound touching it at `y₀` and a one-sided
first-order upper bound is differentiable at `y₀`. -/
theorem scl_hasDerivAt_squeeze {f h : ℝ → ℝ} {a c y₀ : ℝ} (hh : HasDerivAt h a y₀)
    (hle : ∀ y, h y ≤ f y) (hf0 : f y₀ = c) (hh0 : h y₀ = c)
    (hup : ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, f y ≤ c + a * (y - y₀) + ε * |y - y₀|) :
    HasDerivAt f a y₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hh.isLittleO.bound hε, hup ε hε] with y h1 h2
  simp only [smul_eq_mul, Real.norm_eq_abs] at h1 ⊢
  rw [abs_le] at h1 ⊢
  have := hle y
  rw [hf0]
  rw [hh0] at h1
  constructor <;> nlinarith [h1.1, h1.2]

/-- The envelope property (12.AA.6) for player `i` from the one-sided bound
`π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)`: the reverse bound holds since
`π̂_i(q_j) ≥ π_i(q_i*, q_j)`. -/
theorem scl_env_of_upper {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs) {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (i j : Fin 2)
    (hij : j ≠ i) (hd : HasFDerivAt (g i) L qs)
    (hup : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs j),
      bestReplyValue g i (update qs j y) ≤ g i qs + L (Pi.single j 1) * (y - qs j) +
        ε * |y - qs j|) :
    HasDerivAt (fun y => bestReplyValue g i (update qs j y)) (L (Pi.single j 1)) (qs j) := by
  have hc := hd.comp_hasDerivAt_of_eq (qs j) (hasDerivAt_update qs j (qs j))
    (update_eq_self j qs).symm
  refine scl_hasDerivAt_squeeze hc (fun y => ?_) ?_ ?_ hup
  · have h1 := le_bestReplyValue hg i (update qs j y) (qs i)
    have e : update (update qs j y) i (qs i) = update qs j y := by
      rw [update_eq_self_iff, update_of_ne hij.symm]
    rw [e] at h1
    exact h1
  · simp only [update_eq_self]
    exact bestReplyValue_nash hg hqs i
  · simp only [comp_apply, update_eq_self]

/-- Conversely, the envelope property (12.AA.6) gives the one-sided bound. -/
theorem scl_upper_of_hasDerivAt {f : ℝ → ℝ} {a y₀ : ℝ} (hf : HasDerivAt f a y₀) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, f y ≤ f y₀ + a * (y - y₀) + ε * |y - y₀| := by
  intro ε hε
  filter_upwards [hf.isLittleO.bound hε] with y h1
  simp only [smul_eq_mul, Real.norm_eq_abs] at h1
  have := (abs_le.1 h1).2
  nlinarith

/-- `LocalGameData` from MWG's hypotheses plus the one-sided bounds on `π̂_1`, `π̂_2`. -/
noncomputable def sclLocalData {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs) {L0 L1 : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hd0 : HasFDerivAt (g 0) L0 qs) (hd1 : HasFDerivAt (g 1) L1 qs)
    (hc0 : L0 (Pi.single 1 1) ≠ 0) (hc1 : L1 (Pi.single 0 1) ≠ 0)
    (hup0 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 1),
      bestReplyValue g 0 (update qs 1 y) ≤ g 0 qs + L0 (Pi.single 1 1) * (y - qs 1) +
        ε * |y - qs 1|)
    (hup1 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 0),
      bestReplyValue g 1 (update qs 0 y) ≤ g 1 qs + L1 (Pi.single 0 1) * (y - qs 0) +
        ε * |y - qs 0|) :
    LocalGameData g qs where
  L0 := L0
  L1 := L1
  deriv0 := hd0
  deriv1 := hd1
  own0 := scl_own_partial_zero 0 hd0 hqs
  own1 := scl_own_partial_zero 1 hd1 hqs
  cross0 := hc0
  cross1 := hc1
  env0 := scl_env_of_upper hg hqs 0 1 (by decide) hd0 hup0
  env1 := scl_env_of_upper hg hqs 1 0 (by decide) hd1 hup1

/-- **Proposition 12.AA.1, corrected** (MWG, p. 419). Two players with actions in `ℝ`, bounded
payoffs, a stage Nash equilibrium `q*`, `π_i` differentiable at `q*` with
`∂π_i(q*)/∂q_j ≠ 0`, and the one-sided bound
`π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)` for `i = 1, 2`. Then for every
`δ ∈ (0, 1)` some `q'` with `π_i(q') > π_i(q*)` for both players is the stationary outcome path of
a Nash reversion SPNE. Without the one-sided bound the claim fails (`proposition_12_AA_1_false`).
-/
theorem proposition_12_AA_1_upper {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    {L0 L1 : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hd0 : HasFDerivAt (g 0) L0 qs) (hd1 : HasFDerivAt (g 1) L1 qs)
    (hc0 : L0 (Pi.single 1 1) ≠ 0) (hc1 : L1 (Pi.single 0 1) ≠ 0)
    (hup0 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 1),
      bestReplyValue g 0 (update qs 1 y) ≤ g 0 qs + L0 (Pi.single 1 1) * (y - qs 1) +
        ε * |y - qs 1|)
    (hup1 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 0),
      bestReplyValue g 1 (update qs 0 y) ≤ g 1 qs + L1 (Pi.single 0 1) * (y - qs 0) +
        ε * |y - qs 0|) :
    ∃ q', (∀ i, g i qs < g i q') ∧ IsRepeatedSPNE g δ (nashReversion (fun _ => q') qs) :=
  proposition_12_AA_1 hδ0 hδ1 hg hqs (sclLocalData hg hqs hd0 hd1 hc0 hc1 hup0 hup1)

/-- **Proposition 12.AA.4 and Exercise 12.AA.2, corrected** (MWG, pp. 421, 435). Under the
hypotheses of `proposition_12_AA_1_upper`, for every `δ ∈ (0, 1)` some stick-and-carrot SPNE gives
both players average payoffs `(1 − δ)v_i' < π_i(q*)`. (MWG's hypothesis `π_i(q*) > π̲_i` is not
needed.) Without the one-sided bound the claim fails (`proposition_12_AA_4_false`). -/
theorem proposition_12_AA_4_upper {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    {L0 L1 : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hd0 : HasFDerivAt (g 0) L0 qs) (hd1 : HasFDerivAt (g 1) L1 qs)
    (hc0 : L0 (Pi.single 1 1) ≠ 0) (hc1 : L1 (Pi.single 0 1) ≠ 0)
    (hup0 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 1),
      bestReplyValue g 0 (update qs 1 y) ≤ g 0 qs + L0 (Pi.single 1 1) * (y - qs 1) +
        ε * |y - qs 1|)
    (hup1 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 0),
      bestReplyValue g 1 (update qs 0 y) ≤ g 1 qs + L1 (Pi.single 0 1) * (y - qs 0) +
        ε * |y - qs 0|) :
    ∃ q', (∀ i, g i q' < g i qs) ∧ IsRepeatedSPNE g δ (scProfile q' qs qs 0) ∧
      ∀ i, (1 - δ) * osValue (stageU g) δ (scProfile q' qs qs 0) [] i < g i qs :=
  proposition_12_AA_4 hδ0 hδ1 hg hqs (sclLocalData hg hqs hd0 hd1 hc0 hc1 hup0 hup1)

/-- The one-sided bounds hold in the game `locG` at `q* = 0`. -/
theorem scl_locG_upper :
    (∀ ε > 0, ∀ᶠ y in 𝓝 ((0 : Fin 2 → ℝ) 1),
      bestReplyValue locG 0 (update 0 1 y) ≤
        locG 0 0 + locG_data.L0 (Pi.single 1 1) * (y - (0 : Fin 2 → ℝ) 1) +
          ε * |y - (0 : Fin 2 → ℝ) 1|) ∧
    (∀ ε > 0, ∀ᶠ y in 𝓝 ((0 : Fin 2 → ℝ) 0),
      bestReplyValue locG 1 (update 0 0 y) ≤
        locG 1 0 + locG_data.L1 (Pi.single 0 1) * (y - (0 : Fin 2 → ℝ) 0) +
          ε * |y - (0 : Fin 2 → ℝ) 0|) := by
  have e : ∀ i j : Fin 2, bestReplyValue locG i (update 0 j ((0 : Fin 2 → ℝ) j)) = locG i 0 :=
    fun i j => by rw [update_eq_self]; exact bestReplyValue_nash locG_bound locG_nash i
  constructor
  · intro ε hε
    filter_upwards [scl_upper_of_hasDerivAt locG_data.env0 ε hε] with y hy
    rwa [e] at hy
  · intro ε hε
    filter_upwards [scl_upper_of_hasDerivAt locG_data.env1 ε hε] with y hy
    rwa [e] at hy

/-- **Proposition 12.AA.1, corrected, an instance**: `locG` with `δ = 1/2`. -/
theorem scl_upper_instance_1 :
    ∃ q', (∀ i, locG i 0 < locG i q') ∧
      IsRepeatedSPNE locG (1 / 2) (nashReversion (fun _ => q') 0) :=
  proposition_12_AA_1_upper (by norm_num) (by norm_num) locG_bound locG_nash locG_data.deriv0
    locG_data.deriv1 locG_data.cross0 locG_data.cross1 scl_locG_upper.1 scl_locG_upper.2

/-- **Proposition 12.AA.4, corrected, an instance**: `locG` with `δ = 1/2`. -/
theorem scl_upper_instance_4 :
    ∃ q', (∀ i, locG i q' < locG i 0) ∧ IsRepeatedSPNE locG (1 / 2) (scProfile q' 0 0 0) ∧
      ∀ i, (1 - 1 / 2) * osValue (stageU locG) (1 / 2) (scProfile q' 0 0 0) [] i < locG i 0 :=
  proposition_12_AA_4_upper (by norm_num) (by norm_num) locG_bound locG_nash locG_data.deriv0
    locG_data.deriv1 locG_data.cross0 locG_data.cross1 scl_locG_upper.1 scl_locG_upper.2

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Example 12.AA.1: an average payoff of zero in the repeated Cournot game

MWG, Example 12.AA.1, pp. 422-423, with footnotes 36-37.

The stage game is the Cournot duopoly with unit cost `c > 0`, nonincreasing inverse demand `p`,
and (footnote 36) quantities in a compact interval `[0, B]` (`cfG`). With `π(q) = (p(2q) − c)q`
for symmetric outputs, the strategies are: play `q̄` in period 1 and `qᵐ` afterwards; a deviation
when `q̄` is due restarts; a deviation when `qᵐ` is due triggers Nash reversion. Here
(12.AA.7) `π(q̄) + δπ(qᵐ)/(1 − δ) = 0`.

* `example_12_AA_1`: if `q̄ ≥ q_c` (`p(q_c) ≤ c`, so that a best response to `q̄` earns `0`),
  the strategies form an SPNE (using Chapter 9's one-shot deviation principle, footnote 37)
  with average payoff `0` for both firms.
* `example_12_AA_1_qbar`: for `δ` close to `1` such a `q̄ ≥ q_c` exists (when `p(x) → 0`).
* `example_12_AA_1_instance`: `p(x) = max(4 − x, 0)`, `c = 1`, `B = 11`, `δ = 9/10`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

/-- The Cournot duopoly with quantities in `[0, B]` (MWG, p. 422 and footnote 36). -/
def cfG (p : ℝ → ℝ) (c B : ℝ) (i : Fin 2) (q : Fin 2 → Icc (0 : ℝ) B) : ℝ :=
  (p ((q 0 : ℝ) + q 1) - c) * q i

theorem cfG_update_sum {B : ℝ} (x : Icc (0 : ℝ) B) (i : Fin 2) (a : Icc (0 : ℝ) B) :
    ((update (fun _ => x) i a 0 : ℝ) + update (fun _ => x) i a 1) = a + x := by
  fin_cases i <;> simp [update, add_comm]

theorem cfG_update_own {B : ℝ} (x : Icc (0 : ℝ) B) (i : Fin 2) (a : Icc (0 : ℝ) B) :
    (update (fun _ => x) i a i : ℝ) = a := by simp

/-- **Example 12.AA.1** (MWG, pp. 422-423). Let `c > 0`, `p` nonincreasing on `[0, ∞)` with
`p(q_c) ≤ c` and `|p| ≤ P` on `[0, 2B]`, `q*` a stage Nash equilibrium, `q̄ ≥ q_c`, and
(12.AA.7) `π(q̄) + δπ(qᵐ)/(1 − δ) = 0`. If Nash reversion deters deviations from `qᵐ`, the
stick-and-carrot strategies are an SPNE in which both firms earn an average payoff of `0`. -/
theorem example_12_AA_1 {p : ℝ → ℝ} {c B δ qc P : ℝ} (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hanti : AntitoneOn p (Ici 0)) (hqc : 0 ≤ qc) (hpqc : p qc ≤ c)
    (hP : ∀ x ∈ Icc (0 : ℝ) (2 * B), |p x| ≤ P) (qs : Fin 2 → Icc (0 : ℝ) B)
    (hqs : IsStageNash (cfG p c B) qs) (qbar qm : Icc (0 : ℝ) B) (hqbar : qc ≤ qbar)
    (h7 : cfG p c B 0 (fun _ => qbar) + δ / (1 - δ) * cfG p c B 0 (fun _ => qm) = 0)
    (hdet : ∀ i a, a ≠ qm → cfG p c B i (update (fun _ => qm) i a) +
      δ * (cfG p c B i qs / (1 - δ)) ≤ cfG p c B i (fun _ => qm) / (1 - δ)) :
    IsRepeatedSPNE (cfG p c B) δ (scProfile (fun _ => qbar) (fun _ => qm) qs 2) ∧
      ∀ i, (1 - δ) * osValue (stageU (cfG p c B)) δ
        (scProfile (fun _ => qbar) (fun _ => qm) qs 2) [] i = 0 := by
  have h1δ : (1 - δ) ≠ 0 := by linarith
  have hsym : ∀ (x : Icc (0 : ℝ) B) i, cfG p c B i (fun _ => x) = cfG p c B 0 (fun _ => x) := by
    intro x i; fin_cases i <;> rfl
  have hB : ∀ i x, |cfG p c B i x| ≤ (P + c) * B := by
    intro i x
    unfold cfG
    have hx0 := (x 0).2
    have hx1 := (x 1).2
    have hxi := (x i).2
    have hp := hP ((x 0 : ℝ) + x 1) ⟨by linarith [hx0.1, hx1.1], by linarith [hx0.2, hx1.2]⟩
    rw [abs_mul, abs_of_nonneg hxi.1]
    have h1 : |p ((x 0 : ℝ) + x 1) - c| ≤ P + c := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos hc]; linarith
    exact mul_le_mul h1 hxi.2 hxi.1 ((abs_nonneg _).trans h1)
  obtain ⟨hspne, hval⟩ := scProfile_spne hδ0 hδ1 hB (fun _ => qbar) (fun _ => qm) qs 2 hqs
    (fun i a => by
      -- a best response to `q̄ ≥ q_c` earns at most `0`
      have hle : cfG p c B i (update (fun _ => qbar) i a) ≤ 0 := by
        unfold cfG
        rw [cfG_update_sum, cfG_update_own]
        have ha := a.2
        have hle : p ((a : ℝ) + qbar) ≤ c :=
          (hanti (mem_Ici.2 hqc) (mem_Ici.2 (by linarith [ha.1])) (by linarith [ha.1])).trans
            hpqc
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ha.1
      have : (1 - δ) * cfG p c B i (fun _ => qbar) + δ * cfG p c B i (fun _ => qm) = 0 := by
        rw [hsym, hsym qm]
        have := congrArg (fun z => (1 - δ) * z) h7
        simp only [mul_zero] at this
        rw [← this]; field_simp
      linarith)
    (fun i a ha => by simpa [scVal] using hdet i a ha)
  refine ⟨hspne, fun i => ?_⟩
  rw [hval]
  rw [hsym, hsym qm]
  have := congrArg (fun z => (1 - δ) * z) h7
  simp only [mul_zero] at this
  rw [← this]; field_simp

/-- **Example 12.AA.1, existence of the stick** (MWG, p. 423). Let `c > 0`, `p` continuous,
nonincreasing on `[0, ∞)` with `p(x) → 0`, `q_c ≥ 0`, and `π(qᵐ) > 0`. There is `δ_c < 1` such
that for all `δ ∈ (δ_c, 1)` some `q̄ ≥ q_c` solves (12.AA.7):
`(p(2q̄) − c)q̄ + δπ(qᵐ)/(1 − δ) = 0`. -/
theorem example_12_AA_1_qbar {p : ℝ → ℝ} {c qc πm : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn p (Ici 0)) (hanti : AntitoneOn p (Ici 0))
    (hlim : Tendsto p atTop (𝓝 0)) (hqc : 0 ≤ qc) (hπm : 0 < πm) :
    ∃ δc < 1, ∀ δ, δc < δ → δ < 1 →
      ∃ qbar, qc ≤ qbar ∧ (p (2 * qbar) - c) * qbar + δ / (1 - δ) * πm = 0 := by
  -- `p ≥ 0` on `[0, ∞)`
  have hp0 : ∀ x, 0 ≤ x → 0 ≤ p x := by
    intro x hx
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hanti (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hy)) hy
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : 0 < c / 2)))
  refine ⟨c * qc / (c * qc + πm), (div_lt_one (by positivity)).2 (by linarith),
    fun δ hδ hδ1 => ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  set T := δ / (1 - δ) * πm with hT
  have hTq : c * qc ≤ T := by
    rw [div_lt_iff₀ (by positivity)] at hδ
    rw [hT, div_mul_eq_mul_div, le_div_iff₀ h1δ]
    nlinarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hTq
  set Q := max (max qc (|X| / 2)) (2 * T / c) + 1 with hQ
  have hQqc : qc ≤ Q := by
    have := le_max_left (max qc (|X| / 2)) (2 * T / c)
    have := le_max_left qc (|X| / 2); linarith
  have hQX : X ≤ 2 * Q := by
    have := le_max_right qc (|X| / 2)
    have := le_max_left (max qc (|X| / 2)) (2 * T / c)
    have := le_abs_self X; linarith
  have hQT : 2 * T / c ≤ Q := by have := le_max_right (max qc (|X| / 2)) (2 * T / c); linarith
  set f : ℝ → ℝ := fun q => (p (2 * q) - c) * q with hf
  have hfc : ContinuousOn f (Icc qc Q) := by
    refine ContinuousOn.mul (ContinuousOn.sub ?_ continuousOn_const) continuousOn_id
    exact hcont.comp (continuousOn_const.mul continuousOn_id) fun x hx => by
      simp only [mem_Ici]; nlinarith [hx.1]
  have hfQ : f Q ≤ -T := by
    have hpQ := hX (2 * Q) hQX
    have hQ0 : 0 ≤ Q := hqc.trans hQqc
    have : (p (2 * Q) - c) * Q ≤ -(c / 2) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0
    have : T ≤ c / 2 * Q := by
      have := (div_le_iff₀ hc).1 hQT; linarith
    simp only [hf]; linarith
  have hfqc : -T ≤ f qc := by
    have := hp0 (2 * qc) (by linarith)
    simp only [hf]; nlinarith
  obtain ⟨qbar, hqbar, hfq⟩ := intermediate_value_Icc' hQqc hfc ⟨hfQ, hfqc⟩
  exact ⟨qbar, hqbar.1, by simp only [hf] at hfq; linarith⟩

/-- The inverse demand `p(x) = max(4 − x, 0)` of the instance. -/
noncomputable def pLin4 (x : ℝ) : ℝ := max (4 - x) 0

/-- **Example 12.AA.1, an instance.** With `p(x) = max(4 − x, 0)`, `c = 1`, quantities in
`[0, 11]` and `δ = 9/10`: the Cournot equilibrium is `q* = (1, 1)`, `qᵐ = 3/4` (half the
monopoly output), and `q̄ = 81/8 ≥ q_c = 3` solves (12.AA.7); the stick-and-carrot strategies
are an SPNE with average payoff `0`. -/
theorem example_12_AA_1_instance :
    let qs : Fin 2 → Icc (0 : ℝ) 11 := fun _ => ⟨1, by norm_num, by norm_num⟩
    let qbar : Icc (0 : ℝ) 11 := ⟨81 / 8, by norm_num, by norm_num⟩
    let qm : Icc (0 : ℝ) 11 := ⟨3 / 4, by norm_num, by norm_num⟩
    IsRepeatedSPNE (cfG pLin4 1 11) (9 / 10) (scProfile (fun _ => qbar) (fun _ => qm) qs 2) ∧
      ∀ i, (1 - 9 / 10) * osValue (stageU (cfG pLin4 1 11)) (9 / 10)
        (scProfile (fun _ => qbar) (fun _ => qm) qs 2) [] i = 0 := by
  intro qs qbar qm
  have hanti : AntitoneOn pLin4 (Ici 0) := fun x _ y _ hxy => by
    unfold pLin4; exact max_le_max (by linarith) le_rfl
  have hqs_val : ∀ i, cfG pLin4 1 11 i qs = 1 := by
    intro i; fin_cases i <;> norm_num [cfG, qs, pLin4]
  have hqs : IsStageNash (cfG pLin4 1 11) qs := by
    intro i a
    rw [hqs_val]
    have hsum : ((update qs i a 0 : ℝ) + update qs i a 1) = a + 1 := cfG_update_sum _ i a
    unfold cfG
    rw [hsum, cfG_update_own]
    have ha := a.2
    unfold pLin4
    rcases le_total (4 - ((a : ℝ) + 1)) 0 with h | h
    · rw [max_eq_right h]; nlinarith [ha.1]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ((a : ℝ) - 1)]
  refine example_12_AA_1 (qc := 3) (P := 4) (by norm_num) (by norm_num) (by norm_num) hanti
    (by norm_num) (by norm_num [pLin4]) (fun x hx => ?_) qs hqs qbar qm (by norm_num [qbar])
    (by norm_num [cfG, qbar, qm, pLin4]) (fun i a _ => ?_)
  · unfold pLin4
    rw [abs_le]
    constructor
    · exact le_trans (by norm_num) (le_max_right _ _)
    · exact max_le (by linarith [hx.1]) (by norm_num)
  · rw [hqs_val]
    have hqm : cfG pLin4 1 11 i (fun _ => qm) = 9 / 8 := by
      fin_cases i <;> norm_num [cfG, qm, pLin4]
    rw [hqm]
    have hsum : ((update (fun _ => qm) i a 0 : ℝ) + update (fun _ => qm) i a 1) = a + 3 / 4 :=
      cfG_update_sum _ i a
    unfold cfG
    rw [hsum, cfG_update_own]
    have ha := a.2
    unfold pLin4
    rcases le_total (4 - ((a : ℝ) + 3 / 4)) 0 with h | h
    · rw [max_eq_right h]; nlinarith [ha.1]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ((a : ℝ) - 9 / 8)]

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Repeated interaction: the infinitely repeated Bertrand game

MWG, Section 12.D, pp. 400-405, and Exercise 12.D.2.

The stage game is the Bertrand game of Section 12.C with `J` firms (`ι`), prices restricted to
`p ≥ 0` (so that per-period profits are bounded; prices are nonnegative in MWG's model anyway),
and the repeated game is that of Appendix A (`RepeatedGames`). The Nash reversion strategies
(12.D.1) for a price `p` are `nashReversion (fun _ => p̂) ĉ`: charge `p` as long as everybody
always has, and `c` otherwise.

* `bertrandStage_nash`: all firms charging `c` is a stage Nash equilibrium.
* `bertrand_nashReversion_iff`: if `p > c`, `x(p) > 0` and no lower price earns more than `p`
  (`(a − c)x(a) ≤ (p − c)x(p)` for `a < p`), then Nash reversion sustains `p` iff
  `δ ≥ (J − 1)/J`.
* `proposition_12_D_1`: the strategies (12.D.1) with the monopoly price are an SPNE iff
  `δ ≥ 1/2`.
* `exercise_12_D_2_corrected`, `proposition_12_D_2_part1_corrected`.
* `proposition_12_D_2_counterexample`, `exercise_12_D_2_counterexample` (correction): a demand
  for which the price `2 ∈ (c, pᵐ)` cannot be sustained by Nash reversion at `δ = 1/2`, because
  a lower price earns more than `2`; Proposition 12.D.2's first part and Exercise 12.D.2 assume
  implicitly that profit `(p − c)x(p)` increases up to `pᵐ`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Bertrand stage game with nonnegative prices. -/
noncomputable def bertrandStage (x : ℝ → ℝ) (c : ℝ) (j : ι) (p : ι → Ici (0 : ℝ)) : ℝ :=
  bertrandProfit x c (fun k => (p k : ℝ)) j

/-- The constant price profile. -/
def constPrice (ι : Type*) (p : Ici (0 : ℝ)) : ι → Ici (0 : ℝ) := fun _ => p

omit [DecidableEq ι] in
/-- Per-period profits are bounded: `|(p − c)x_j| ≤ (p̄ + c)x(0)` for `p ≥ 0`. -/
theorem bertrandStage_bound {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hpbar : 0 ≤ pbar) :
    ∀ j (p : ι → Ici (0 : ℝ)), |bertrandStage x c j p| ≤ (pbar + c) * x 0 := by
  intro j p
  unfold bertrandStage bertrandProfit
  have hs0 := bertrandSales_nonneg hx.nonneg (fun k => (p k : ℝ)) j
  have hsx := bertrandSales_le hx.nonneg (fun k => (p k : ℝ)) j
  have hp0 : 0 ≤ (p j : ℝ) := (p j).2
  have hx0 : x (p j) ≤ x 0 := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]
    · rcases eq_or_lt_of_le (hx.nonneg (p j)) with h' | h'
      · rw [← h']; exact hx.nonneg 0
      · exact (hx.strictAnti 0 _ h h').le
  rcases le_or_gt pbar (p j) with h | h
  · rw [hx.zero _ h] at hsx
    have : bertrandSales x (fun k => (p k : ℝ)) j = 0 := le_antisymm hsx hs0
    rw [this, mul_zero, abs_zero]
    exact mul_nonneg (by linarith) (hx.nonneg 0)
  · rw [abs_mul, abs_of_nonneg hs0]
    have h1 : |(p j : ℝ) - c| ≤ pbar + c := by rw [abs_le]; constructor <;> linarith
    exact mul_le_mul h1 (hsx.trans hx0) hs0 (by linarith)

/-- All firms charging `c` is a Nash equilibrium of the stage game (any number of firms
`J ≥ 2`; Proposition 12.C.1). -/
theorem bertrandStage_nash {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (h2 : 2 ≤ Fintype.card ι) :
    IsStageNash (bertrandStage (ι := ι) x cc) (constPrice ι cc) := by
  intro j a
  have h0 : bertrandStage x cc j (constPrice ι cc) = 0 := by
    simp [bertrandStage, bertrandProfit, constPrice]
  rw [h0]
  unfold bertrandStage
  rcases le_or_gt (a : ℝ) cc with h | h
  · exact bertrandProfit_le_zero hx.nonneg (by simpa using h)
  · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
    unfold bertrandProfit
    rw [bertrandSales_of_gt (k := k) (by simpa [constPrice, update_of_ne hk] using h), mul_zero]

/-- The profit of a firm undercutting all rivals' common price, or matching it. -/
theorem bertrandStage_update {x : ℝ → ℝ} {c : ℝ} (p a : Ici (0 : ℝ)) (j : ι)
    (h2 : 2 ≤ Fintype.card ι) :
    ((a : ℝ) < p → bertrandStage x c j (update (constPrice ι p) j a) = (a - c) * x a) ∧
    ((p : ℝ) < a → bertrandStage x c j (update (constPrice ι p) j a) = 0) ∧
    bertrandStage x c j (constPrice ι p) = (p - c) * (x p / Fintype.card ι) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · unfold bertrandStage bertrandProfit
    rw [bertrandSales_of_lt (fun k hk => by simpa [constPrice, update_of_ne hk] using h)]
    simp
  · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
    unfold bertrandStage bertrandProfit
    rw [bertrandSales_of_gt (k := k) (by simpa [constPrice, update_of_ne hk] using h), mul_zero]
  · unfold bertrandStage bertrandProfit bertrandSales
    simp [constPrice]

/-- **Nash reversion in the repeated Bertrand game** (MWG, pp. 401-405). Let `J ≥ 2`,
`c ≥ 0`, `p > c` with `x(p) > 0`, and suppose no lower price earns more than `p`:
`(a − c)x(a) ≤ (p − c)x(p)` for `0 ≤ a < p`. Then the Nash reversion strategies that charge `p`
are an SPNE iff `δ ≥ (J − 1)/J`. -/
theorem bertrand_nashReversion_iff {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc p : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h2 : 2 ≤ Fintype.card ι) (hpc : (cc : ℝ) < p) (hxp : 0 < x p)
    (hmax : ∀ a : ℝ, 0 ≤ a → a < p → (a - cc) * x a ≤ (p - cc) * x p) :
    IsRepeatedSPNE (bertrandStage (ι := ι) x cc) δ
        (nashReversion (fun _ => constPrice ι p) (constPrice ι cc)) ↔
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι ≤ δ := by
  set J : ℝ := (Fintype.card ι : ℝ) with hJ
  have hJ2 : (2 : ℝ) ≤ J := by rw [hJ]; exact_mod_cast h2
  have hJ0 : 0 < J := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  set R := ((p : ℝ) - cc) * x p with hR
  have hRpos : 0 < R := mul_pos (by linarith) hxp
  rw [nashReversion_spne_iff hδ0 hδ1 (bertrandStage_bound hx cc.2 hpbar) _
    (bertrandStage_nash hx cc h2)]
  have hc0 : ∀ j, bertrandStage (ι := ι) x cc j (constPrice ι cc) = 0 := fun j => by
    simp [bertrandStage, bertrandProfit, constPrice]
  have hpv : ∀ j t, pathValue (bertrandStage (ι := ι) x cc) δ (fun _ => constPrice ι p) t j =
      R / J / (1 - δ) := fun j t => by
    rw [pathValue_const _ hδ0 hδ1, (bertrandStage_update p p j h2).2.2]
    rw [hR]; ring
  simp only [hc0, zero_div, mul_zero, add_zero, hpv]
  -- the condition says every deviation earns at most `R/(J(1 − δ))`
  have hkey : R / J / (1 - δ) ≥ R ↔ (J - 1) / J ≤ δ := by
    rw [ge_iff_le, le_div_iff₀ h1δ, div_le_iff₀ hJ0, le_div_iff₀ hJ0]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  constructor
  · intro h
    rw [← hkey]
    -- deviations just below `p` earn almost `R`
    by_contra hlt
    push Not at hlt
    have hcont : ContinuousAt (fun a : ℝ => (a - cc) * x a) p :=
      ((continuous_id.sub continuous_const).mul hx.cont).continuousAt
    have hev : ∀ᶠ a in 𝓝 (p : ℝ), R / J / (1 - δ) < (a - cc) * x a :=
      hcont.eventually (lt_mem_nhds hlt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set a : ℝ := max ((p : ℝ) - ε / 2) ((cc + p) / 2) with ha
    have hap : a < p := max_lt (by linarith) (by linarith)
    have hcc0 : (0 : ℝ) ≤ cc := cc.2
    have ha0 : 0 ≤ a := le_trans (by linarith) (le_max_right _ _)
    have hdist : dist a p < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left ((p : ℝ) - ε / 2) ((cc + p) / 2)]
    obtain ⟨j⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hne : (⟨a, ha0⟩ : Ici (0 : ℝ)) ≠ constPrice ι p j := by
      intro heq; have := congrArg Subtype.val heq; simp [constPrice] at this; linarith
    have := h 0 j ⟨a, ha0⟩ hne
    rw [(bertrandStage_update p ⟨a, ha0⟩ j h2).1 hap] at this
    linarith [hball hdist]
  · intro hδ t j a ha
    have hRle := (hkey.2 hδ)
    rcases lt_trichotomy (a : ℝ) p with h | h | h
    · rw [(bertrandStage_update p a j h2).1 h]
      linarith [hmax a a.2 h]
    · exact absurd (Subtype.ext h) (by simpa [constPrice] using ha)
    · rw [(bertrandStage_update p a j h2).2.1 h]
      exact div_nonneg (div_nonneg hRpos.le hJ0.le) h1δ.le

/-- **Proposition 12.D.1** (MWG, p. 401). In the infinitely repeated Bertrand duopoly, the
Nash reversion strategies (12.D.1) with the monopoly price `pᵐ` (a maximizer of `(p − c)x(p)`
with `pᵐ > c`, `x(pᵐ) > 0`) constitute an SPNE if and only if `δ ≥ 1/2`. -/
theorem proposition_12_D_1 {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc pm : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpc : (cc : ℝ) < pm) (hxp : 0 < x pm)
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - cc) * x a ≤ (pm - cc) * x pm) :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ
        (nashReversion (fun _ => constPrice (Fin 2) pm) (constPrice (Fin 2) cc)) ↔ 1 / 2 ≤ δ := by
  rw [bertrand_nashReversion_iff hx cc pm hpbar hδ0 hδ1 (by simp) hpc hxp
    (fun a ha _ => hmono a ha)]
  norm_num

/-- **Exercise 12.D.2, corrected** (MWG, p. 405). With `J ≥ 2` firms, repeated choice of a price
`p ∈ (c, pᵐ]` with `x(p) > 0` is sustained as a stationary SPNE outcome path with Nash reversion
iff `δ ≥ (J − 1)/J`, provided no lower price earns more than `p` (true for `p = pᵐ`, and for all
`p ∈ (c, pᵐ]` when `(p − c)x(p)` is nondecreasing on `[0, pᵐ]`). More firms make collusion
harder to sustain: `(J − 1)/J` increases with `J`. -/
theorem exercise_12_D_2_corrected {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc p : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h2 : 2 ≤ Fintype.card ι) (hpc : (cc : ℝ) < p) (hxp : 0 < x p)
    (hmono : MonotoneOn (fun a : ℝ => (a - cc) * x a) (Icc 0 p)) :
    (IsRepeatedSPNE (bertrandStage (ι := ι) x cc) δ
        (nashReversion (fun _ => constPrice ι p) (constPrice ι cc)) ↔
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι ≤ δ) ∧
    StrictMono (fun J : ℕ => ((J : ℝ) + 1 - 1) / ((J : ℝ) + 1)) := by
  refine ⟨bertrand_nashReversion_iff hx cc p hpbar hδ0 hδ1 h2 hpc hxp
    fun a ha hap => hmono ⟨ha, hap.le⟩ ⟨le_trans cc.2 hpc.le, le_rfl⟩ hap.le, ?_⟩
  intro m n hmn
  have : (m : ℝ) < n := by exact_mod_cast hmn
  simp only [add_sub_cancel_right]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Proposition 12.D.2, first part, corrected** (MWG, p. 403). With `δ ≥ 1/2`, repeated choice
of any price `p ∈ (c, pᵐ]` with `x(p) > 0` can be supported by Nash reversion if `(p − c)x(p)` is
nondecreasing on `[0, p]` (the price `c` is the repeated stage equilibrium). -/
theorem proposition_12_D_2_part1_corrected {x : ℝ → ℝ} {pbar δ : ℝ}
    (hx : IsBertrandDemand x pbar) (cc p : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ)
    (hδ1 : δ < 1) (hpc : (cc : ℝ) < p) (hxp : 0 < x p)
    (hmono : MonotoneOn (fun a : ℝ => (a - cc) * x a) (Icc 0 p)) :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ
      (nashReversion (fun _ => constPrice (Fin 2) p) (constPrice (Fin 2) cc)) := by
  refine ((exercise_12_D_2_corrected hx cc p hpbar (by linarith) hδ1 (by simp) hpc hxp
    hmono).1).2 ?_
  norm_num; linarith

/-- The demand of the counterexample (`c = 1`): `x(p) = 19 − 9p` for `p ≤ 2`,
`(102 − p)/100` for `2 ≤ p ≤ 102`, and `0` above. Profit `(p − 1)x(p)` has a local peak
`25/9` at `p = 14/9` and its global maximum at `pᵐ = 103/2`; at `p = 2` it is only `1`. -/
noncomputable def cexDemand (p : ℝ) : ℝ :=
  if p ≤ 2 then 19 - 9 * p else if p ≤ 102 then (102 - p) / 100 else 0

theorem cexDemand_isBertrand : IsBertrandDemand cexDemand 102 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cexDemand
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const ?_
      intro p hp; rw [hp]; norm_num
    · intro p hp; rw [hp]; norm_num
  · intro p; unfold cexDemand
    split_ifs
    · linarith
    · exact div_nonneg (by linarith) (by norm_num)
    · exact le_rfl
  · intro p p' hpp' hpos
    unfold cexDemand at hpos ⊢
    split_ifs at hpos ⊢ <;> linarith
  · intro p hp; unfold cexDemand
    split_ifs <;> linarith

/-- The cost `c = 1` of the counterexample, as a nonnegative price. -/
def cexC1 : Ici (0 : ℝ) := ⟨1, by norm_num⟩

/-- The price `p = 2` of the counterexample. -/
def cexP2 : Ici (0 : ℝ) := ⟨2, by norm_num⟩

/-- **Proposition 12.D.2 and Exercise 12.D.2 are false as printed** (MWG, pp. 403 and 405;
correction). With `c = 1` and the demand `cexDemand`, the monopoly price is `pᵐ = 103/2`, the
price `p = 2 ∈ (c, pᵐ]` has `x(2) = 1 > 0`, and `δ = 1/2 ≥ (J − 1)/J` for `J = 2`; yet repeated
choice of `p = 2` is not sustained by Nash reversion, since undercutting to `14/9` earns
`25/9 > 1 = (p − c)x(p)/(2(1 − δ))`. -/
theorem proposition_12_D_2_counterexample :
    (∀ a : ℝ, 0 ≤ a → (a - 1) * cexDemand a ≤ (103 / 2 - 1) * cexDemand (103 / 2)) ∧
    0 < cexDemand 2 ∧
    ¬ IsRepeatedSPNE (bertrandStage (ι := Fin 2) cexDemand cexC1) (1 / 2)
      (nashReversion (fun _ => constPrice (Fin 2) cexP2) (constPrice (Fin 2) cexC1)) := by
  refine ⟨fun a ha => ?_, by norm_num [cexDemand], fun h => ?_⟩
  · have hm : (103 / 2 - 1) * cexDemand (103 / 2) = 10201 / 400 := by norm_num [cexDemand]
    rw [hm]
    unfold cexDemand
    split_ifs
    · nlinarith [sq_nonneg (a - 14 / 9)]
    · nlinarith [sq_nonneg (a - 103 / 2)]
    · norm_num
  · rw [nashReversion_spne_iff (δ := 1 / 2) (by norm_num) (by norm_num)
      (bertrandStage_bound cexDemand_isBertrand cexC1.2 (by norm_num)) _
      (bertrandStage_nash cexDemand_isBertrand cexC1 (by simp))] at h
    have hdev := h 0 0 ⟨14 / 9, by norm_num⟩ (by
      intro heq; have := congrArg Subtype.val heq
      simp [constPrice, cexP2] at this; norm_num at this)
    rw [(bertrandStage_update (c := cexC1) (x := cexDemand) cexP2 ⟨14 / 9, by norm_num⟩
      0 (by simp)).1 (by norm_num [cexP2]), pathValue_const _ (by norm_num) (by norm_num),
      (bertrandStage_update (c := cexC1) (x := cexDemand) cexP2 cexP2 0 (by simp)).2.2] at hdev
    have h1 : bertrandStage (ι := Fin 2) cexDemand cexC1 0 (constPrice (Fin 2) cexC1) = 0 := by
      simp [bertrandStage, bertrandProfit, constPrice]
    rw [h1] at hdev
    norm_num [cexDemand, cexC1, cexP2] at hdev

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Proposition 12.D.2: no collusion when `δ < 1/2`

MWG, Proposition 12.D.2 (second part) and its small-type proof, pp. 403-404.

`proposition_12_D_2_part2`: in the infinitely repeated Bertrand duopoly with `δ < 1/2`, along
the outcome path of any SPNE (from any history), the lowest price is `c` in every period, so all
sales take place at a price equal to cost.

The proof follows MWG: a firm can always secure `0` from any period on (price `c`), and can earn
almost the whole industry profit `π_t` by undercutting in period `t` (12.D.3); adding over the
two firms gives `2π_t ≤ v_{1t} + v_{2t} ≤ π̄/(1 − δ)` with `π̄ = sup π_t`, impossible for
`π̄ > 0` and `δ < 1/2`. MWG's argument stops at "`π_t ≤ 0` for all `t`"; to conclude that sales
occur at the price `c` we add: then every firm earns `0` in every period, so the lowest price
cannot be below `c` (a loss) nor above `c` (a profitable deviation would exist).
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

theorem osPath_succ' {I : Type*} {A : I → Type*} (σ : OSProfile A) (h : OSHist A) (n : ℕ) :
    osPath σ h (n + 1) = osPlay σ (osPath σ h n) :: osPath σ h n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change osPath σ (osPlay σ h :: h) (n + 1) = _
    rw [ih]
    rfl

/-- Duopoly profits with `R(a) = (a − c)x(a)`: the strictly lowest-priced firm earns `R`. -/
theorem duopoly_profit_lt (x : ℝ → ℝ) (c : ℝ) (q : Fin 2 → ℝ) {j k : Fin 2} (hk : k ≠ j)
    (h : q j < q k) : bertrandProfit x c q j = (q j - c) * x (q j) := by
  have hall : ∀ l : Fin 2, l = j ∨ l = k := by
    intro l; fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  unfold bertrandProfit
  rw [bertrandSales_of_lt fun l hl => by rcases hall l with rfl | rfl; exacts [absurd rfl hl, h]]

/-- At a tie each firm earns `R/2`. -/
theorem duopoly_profit_eq (x : ℝ → ℝ) (c : ℝ) (q : Fin 2 → ℝ) {j k : Fin 2} (hk : k ≠ j)
    (h : q j = q k) : bertrandProfit x c q j = (q j - c) * x (q j) / 2 := by
  have hall : ∀ l : Fin 2, l = j ∨ l = k := by
    intro l; fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  unfold bertrandProfit bertrandSales
  have hmin : ∀ l, q j ≤ q l := fun l => by rcases hall l with rfl | rfl <;> simp [h]
  have hcard : (Finset.univ.filter fun l => q l = q j) = Finset.univ := by
    ext l; rcases hall l with rfl | rfl <;> simp [h]
  simp only [hmin, implies_true, ↓reduceIte, hcard]
  simp; ring

/-- The higher-priced firm earns nothing. -/
theorem duopoly_profit_gt (x : ℝ → ℝ) (c : ℝ) (q : Fin 2 → ℝ) {j k : Fin 2}
    (h : q k < q j) : bertrandProfit x c q j = 0 := by
  unfold bertrandProfit
  rw [bertrandSales_of_gt (k := k) h, mul_zero]

/-- **Proposition 12.D.2, second part** (MWG, pp. 403-404). In the infinitely repeated Bertrand
duopoly with `c > 0`, `x(c) > 0` and `δ < 1/2`, along the outcome path of any SPNE `σ` starting
from any history, the lowest price in every period equals `c`. -/
theorem proposition_12_D_2_part2 {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (hc : 0 < (cc : ℝ)) (hxc : 0 < x cc) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 2) {σ : OSProfile (fun _ : Fin 2 => Ici (0 : ℝ))}
    (hσ : IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ σ) (h : OSHist _) (t : ℕ) :
    min ((osPlay σ (osPath σ h t) 0 : ℝ)) (osPlay σ (osPath σ h t) 1) = cc := by
  classical
  set g := bertrandStage (ι := Fin 2) x cc with hgdef
  have hδ1 : δ < 1 := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  set M := (pbar + cc) * x 0 with hM
  have hg : ∀ j p, |g j p| ≤ M := bertrandStage_bound hx cc.2 hpbar
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg 0 (fun _ => cc))
  set P : ℕ → Fin 2 → Ici (0 : ℝ) := fun t => osPlay σ (osPath σ h t) with hP
  set V : Fin 2 → ℕ → ℝ := fun j t => osValue (stageU g) δ σ (osPath σ h t) j with hV
  have hrec : ∀ j t, V j t = g j (P t) + δ * V j (t + 1) := by
    intro j t
    simp only [hV, hP]
    rw [osValue_succ hδ0 hδ1 (stageU_bound hg) σ _ j, osPath_succ']
    rfl
  have hVb : ∀ j t, |V j t| ≤ M / (1 - δ) := fun j t =>
    osValue_abs_le hδ0 hδ1 (stageU_bound hg) σ _ j
  -- a firm pricing at `c` earns nothing
  have hzero : ∀ j (p : Fin 2 → Ici (0 : ℝ)), g j (update p j cc) = 0 := by
    intro j p; simp [hgdef, bertrandStage, bertrandProfit]
  -- deviating in period `t` to `a` and charging `c` afterwards
  have hdev : ∀ j t (a : Ici (0 : ℝ)), g j (update (P t) j a) ≤ V j t := by
    intro j t a
    set H := osPath σ h t with hH
    set τ : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)) → Ici (0 : ℝ) :=
      fun h' => if h' = H then a else cc with hτ
    have hs := hσ j τ H
    rw [osValue_succ hδ0 hδ1 (stageU_bound hg) _ H j, osPlay_update] at hs
    have hτH : τ H = a := by simp [hτ]
    rw [hτH] at hs
    have hW : osValue (stageU g) δ (update σ j τ) (update (osPlay σ H) j a :: H) j = 0 := by
      unfold osValue
      have : ∀ n, δ ^ n * stageU g j
          (osPath (update σ j τ) (update (osPlay σ H) j a :: H) n)
          (osPlay (update σ j τ) (osPath (update σ j τ) (update (osPlay σ H) j a :: H) n)) =
          0 := by
        intro n
        rw [osPlay_update]
        have hne : osPath (update σ j τ) (update (osPlay σ H) j a :: H) n ≠ H := by
          intro heq
          have := congrArg List.length heq
          rw [osPath_length, List.length_cons] at this
          omega
        have : τ (osPath (update σ j τ) (update (osPlay σ H) j a :: H) n) = cc := by
          simp only [hτ]
          exact ite_eq_right_iff.mpr fun h' => absurd h' hne
        rw [this]
        simp only [stageU, hzero, mul_zero]
      simp [this]
    rw [hW, mul_zero, add_zero] at hs
    exact hs
  have hV0 : ∀ j t, 0 ≤ V j t := fun j t => by
    have := hdev j t cc; rwa [hzero] at this
  set R : ℝ → ℝ := fun a => (a - cc) * x a with hR
  have hRc : Continuous R := (continuous_id.sub continuous_const).mul hx.cont
  set m : ℕ → ℝ := fun t => min ((P t 0 : ℝ)) (P t 1) with hm
  have hother : ∀ j : Fin 2, ∃ k, k ≠ j ∧ ∀ l : Fin 2, l = j ∨ l = k := by
    intro j; fin_cases j
    · exact ⟨1, by decide, fun l => by fin_cases l <;> decide⟩
    · exact ⟨0, by decide, fun l => by fin_cases l <;> decide⟩
  -- industry profit `π_t = R(m_t)` and each firm's profit
  have hfirm : ∀ j t, g j (P t) = R (m t) ∨ g j (P t) = R (m t) / 2 ∨ g j (P t) = 0 := by
    intro j t
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp only [hgdef, bertrandStage]
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
    · rcases lt_trichotomy ((P t 0 : ℝ)) (P t 1) with h1 | h1 | h1
      · left; rw [duopoly_profit_lt x cc _ h10 h1]; simp only [hm, hR, min_eq_left h1.le]
      · right; left; rw [duopoly_profit_eq x cc _ h10 h1]; simp only [hm, hR, h1, min_self]
      · right; right; exact duopoly_profit_gt x cc _ h1
    · rcases lt_trichotomy ((P t 1 : ℝ)) (P t 0) with h1 | h1 | h1
      · left; rw [duopoly_profit_lt x cc _ h01 h1]; simp only [hm, hR, min_eq_right h1.le]
      · right; left; rw [duopoly_profit_eq x cc _ h01 h1]; simp only [hm, hR, h1, min_self]
      · right; right; exact duopoly_profit_gt x cc _ h1
  have hπ : ∀ t, g 0 (P t) + g 1 (P t) = R (m t) := by
    intro t
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp only [hgdef, bertrandStage]
    rcases lt_trichotomy ((P t 0 : ℝ)) (P t 1) with h1 | h1 | h1
    · rw [duopoly_profit_lt x cc _ h10 h1, duopoly_profit_gt x cc _ h1, hm]
      simp only [min_eq_left h1.le, hR]; ring
    · rw [duopoly_profit_eq x cc _ h10 h1, duopoly_profit_eq x cc _ h01 h1.symm, hm]
      simp only [h1, min_self, hR]; ring
    · rw [duopoly_profit_gt x cc _ h1, duopoly_profit_lt x cc _ h01 h1, hm]
      simp only [min_eq_right h1.le, hR]; ring
  -- (12.D.3): each firm earns at least `π_t`
  have hER : ∀ j t, R (m t) ≤ V j t := by
    intro j t
    obtain ⟨k, hk, hall⟩ := hother j
    have hm0 : 0 ≤ m t := le_min (P t 0).2 (P t 1).2
    rcases eq_or_lt_of_le hm0 with h0 | h0
    · rw [← h0]; simp only [hR, zero_sub]
      nlinarith [hx.nonneg 0, hV0 j t]
    · have hlim : Tendsto R (𝓝[<] (m t)) (𝓝 (R (m t))) :=
        hRc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT h0] with a ha
      have hlow : ∀ l, l ≠ j → (update (P t) j ⟨a, ha.1.le⟩ j : ℝ) <
          (update (P t) j ⟨a, ha.1.le⟩ l : ℝ) := by
        intro l hl
        rw [update_self, update_of_ne hl]
        exact lt_of_lt_of_le ha.2 (by
          rcases hall l with rfl | rfl
          · exact absurd rfl hl
          · fin_cases l <;> simp [hm])
      have := hdev j t ⟨a, ha.1.le⟩
      simp only [hgdef, bertrandStage] at this
      unfold bertrandProfit at this
      rw [bertrandSales_of_lt hlow] at this
      simpa [hR] using this
  -- `π_t ≤ 0` for all `t`
  have hπbd : ∀ t, R (m t) ≤ 2 * M := fun t => by
    rw [← hπ t]; linarith [(abs_le.1 (hg 0 (P t))).2, (abs_le.1 (hg 1 (P t))).2]
  set U := ⨆ t, R (m t) with hU
  have hbdd : BddAbove (Set.range fun t => R (m t)) := ⟨2 * M, fun _ ⟨t, ht⟩ => ht ▸ hπbd t⟩
  have hSU : ∀ t, V 0 t + V 1 t ≤ U / (1 - δ) := by
    have hgap : ∀ n t, V 0 t + V 1 t - U / (1 - δ) ≤
        δ ^ n * (2 * (M / (1 - δ)) + |U| / (1 - δ)) := by
      intro n
      induction n with
      | zero =>
        intro t
        have h0 := abs_le.1 (hVb 0 t); have h1 := abs_le.1 (hVb 1 t)
        have : -(|U| / (1 - δ)) ≤ U / (1 - δ) := by
          rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_abs_le U) h1δ.le
        rw [pow_zero, one_mul]; linarith
      | succ n ih =>
        intro t
        have hπU : R (m t) ≤ U := le_ciSup hbdd t
        rw [hrec 0 t, hrec 1 t]
        have := ih (t + 1)
        have e : U / (1 - δ) = U + δ * (U / (1 - δ)) := by field_simp; ring
        have h2 := hπ t
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left this hδ0]
    intro t
    have ht : Tendsto (fun n : ℕ => δ ^ n * (2 * (M / (1 - δ)) + |U| / (1 - δ))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _
    have := ge_of_tendsto ht (Eventually.of_forall fun n => hgap n t)
    linarith
  have hU0 : U ≤ 0 := by
    have h2U : 2 * U ≤ U / (1 - δ) := by
      rw [show 2 * U = ⨆ t, 2 * R (m t) by
        rw [Real.mul_iSup_of_nonneg (by norm_num)]]
      refine ciSup_le fun t => ?_
      have := hER 0 t; have := hER 1 t; have := hSU t; linarith
    rw [le_div_iff₀ h1δ] at h2U
    nlinarith
  have hπ0 : ∀ t, R (m t) ≤ 0 := fun t => (le_ciSup hbdd t).trans hU0
  -- every firm earns `0` in every period
  have hg0 : ∀ j t, g j (P t) ≤ 0 := by
    intro j t
    rcases hfirm j t with h | h | h <;> rw [h] <;> linarith [hπ0 t]
  have hVle : ∀ j t, V j t ≤ 0 := by
    intro j
    have hgap : ∀ n t, V j t ≤ δ ^ n * (M / (1 - δ)) := by
      intro n
      induction n with
      | zero => intro t; rw [pow_zero, one_mul]; exact (le_abs_self _).trans (hVb j t)
      | succ n ih =>
        intro t
        rw [hrec j t, pow_succ]
        nlinarith [hg0 j t, mul_le_mul_of_nonneg_left (ih (t + 1)) hδ0]
    intro t
    have ht : Tendsto (fun n : ℕ => δ ^ n * (M / (1 - δ))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hgap n t)
  have hVz : ∀ j t, V j t = 0 := fun j t => le_antisymm (hVle j t) (hV0 j t)
  have hgz : ∀ j t, g j (P t) = 0 := fun j t => by
    have := hrec j t; rw [hVz, hVz] at this; linarith
  -- the lowest price is `c`
  change m t = cc
  rcases lt_trichotomy (m t) cc with hlt | heq | hgt
  · exfalso
    have hxm : 0 < x (m t) := by
      by_contra hn; push Not at hn
      linarith [hx.strictAnti _ _ hlt hxc, hx.nonneg (m t)]
    have hRneg : (m t - cc) * x (m t) < 0 := mul_neg_of_neg_of_pos (by linarith) hxm
    -- the lowest-priced firm sells at a loss
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hg00 := hgz 0 t
    have hg01 := hgz 1 t
    simp only [hgdef, bertrandStage] at hg00 hg01
    rcases lt_trichotomy ((P t 0 : ℝ)) (P t 1) with h1 | h1 | h1
    · rw [duopoly_profit_lt x cc _ h10 h1] at hg00
      have : m t = (P t 0 : ℝ) := min_eq_left h1.le
      rw [← this] at hg00; linarith
    · rw [duopoly_profit_eq x cc _ h10 h1] at hg00
      have : m t = (P t 0 : ℝ) := by rw [hm]; simp [h1]
      rw [← this] at hg00; linarith
    · rw [duopoly_profit_lt x cc _ h01 h1] at hg01
      have : m t = (P t 1 : ℝ) := min_eq_right h1.le
      rw [← this] at hg01; linarith
  · exact heq
  · exfalso
    obtain ⟨a, hac, ham, hgain⟩ := bertrand_deviation hx hxc hgt
    have hRm : 0 ≤ R (m t) := mul_nonneg (by linarith) (hx.nonneg _)
    have ha0 : 0 ≤ a := by linarith
    have hlow : ∀ l, l ≠ (0 : Fin 2) → (update (P t) 0 ⟨a, ha0⟩ 0 : ℝ) <
        (update (P t) 0 ⟨a, ha0⟩ l : ℝ) := by
      intro l hl
      rw [update_self, update_of_ne hl]
      have : l = 1 := by
        rcases (show l = 0 ∨ l = 1 by fin_cases l <;> simp) with h | h
        · exact absurd h hl
        · exact h
      subst this
      exact lt_of_lt_of_le ham (min_le_right _ _)
    have := hdev 0 t ⟨a, ha0⟩
    simp only [hgdef, bertrandStage] at this
    unfold bertrandProfit at this
    rw [bertrandSales_of_lt hlow, hVz] at this
    simp only [update_self] at this
    linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 12.D.3: Nash reversion in the repeated linear Cournot duopoly

MWG, Exercise 12.D.3, p. 433.

With `A = a − c > 0`, symmetric outputs `(q, q)`, the stationary condition (12.AA.3) reads
`π̂(q) − π(q) ≤ δ/(1 − δ)(π(q) − π*)`, where `π(q) = (A − 2bq)q`, the best-response profit is
`π̂(q) = (A − bq)²/(4b)` (for `q ≤ A/b`, Example 12.C.1), and `π* = A²/(9b)` is the Cournot profit.
The gain from deviating is `π̂(q) − π(q) = (A − 3bq)²/(4b)`.

* `exercise_12_D_3a`: the joint monopoly outputs `(A/(4b), A/(4b))` satisfy (12.AA.3) iff
  `δ ≥ 9/17`.
* `exercise_12_D_3b_printed_false` (correction): for every `q` in the printed interval
  `[A/(2b), A/b]` and every `δ ∈ [0, 1)`, (12.AA.3) fails (the price is at most `c`).
* `exercise_12_D_3b_corrected`: for `q ∈ [A/(4b), A/(3b))` (between joint monopoly and Cournot),
  (12.AA.3) holds iff `δ ≥ δ(q) = 9(A − 3bq)/(5A − 3bq)`; `δ(q)` is differentiable and strictly
  *decreasing* in `q` (not increasing, as printed).
-/

namespace MWG.MarketPower

/-- The deviation gain `π̂(q) − π(q) = (A − 3bq)²/(4b)`. -/
theorem cournot_gain {A b q : ℝ} (hb : 0 < b) :
    (A - b * q) ^ 2 / (4 * b) - (A - 2 * b * q) * q = (A - 3 * b * q) ^ 2 / (4 * b) := by
  field_simp; ring

/-- Condition (12.AA.3) for the symmetric output `q` of the linear Cournot duopoly. -/
def CournotNR (A b δ q : ℝ) : Prop :=
  (A - b * q) ^ 2 / (4 * b) - (A - 2 * b * q) * q ≤
    δ / (1 - δ) * ((A - 2 * b * q) * q - A ^ 2 / (9 * b))

/-- **Exercise 12.D.3(b), corrected** (MWG, p. 433). For `q ∈ [A/(4b), A/(3b))`, condition
(12.AA.3) holds iff `δ ≥ 9(A − 3bq)/(5A − 3bq)` (indeed for every `q < A/(3b)`). -/
theorem exercise_12_D_3b_corrected {A b δ q : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hδ1 : δ < 1) (hq2 : q < A / (3 * b)) :
    CournotNR A b δ q ↔ 9 * (A - 3 * b * q) / (5 * A - 3 * b * q) ≤ δ := by
  unfold CournotNR
  rw [cournot_gain hb]
  have h3 : 0 < A - 3 * b * q := by
    rw [lt_div_iff₀ (by positivity)] at hq2; linarith
  have h5 : 0 < 5 * A - 3 * b * q := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hπ : (A - 2 * b * q) * q - A ^ 2 / (9 * b) =
      (A - 3 * b * q) * (6 * b * q - A) / (9 * b) := by
    field_simp; ring
  rw [hπ, div_le_iff₀ h5]
  set X := A - 3 * b * q with hX
  set Y := 6 * b * q - A with hY
  have h36 : 0 < 36 * b * (1 - δ) := by positivity
  rw [show δ / (1 - δ) * (X * Y / (9 * b)) = 4 * δ * X * Y / (36 * b * (1 - δ)) by
      field_simp; ring,
    show X ^ 2 / (4 * b) = 9 * X ^ 2 * (1 - δ) / (36 * b * (1 - δ)) by field_simp; ring,
    div_le_div_iff_of_pos_right h36]
  have e : 9 * X - δ * (5 * A - 3 * b * q) = 9 * X * (1 - δ) - 4 * δ * Y := by
    rw [hX, hY]; ring
  constructor
  · intro h
    have : 9 * X * (1 - δ) ≤ 4 * δ * Y := by
      by_contra hc; push Not at hc
      nlinarith [mul_lt_mul_of_pos_left hc h3]
    linarith
  · intro h
    have : 9 * X * (1 - δ) ≤ 4 * δ * Y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h3.le]

/-- **Exercise 12.D.3(a)** (MWG, p. 433). The joint monopoly outputs `(A/(4b), A/(4b))` are
sustained by Nash reversion iff `δ ≥ 9/17`. -/
theorem exercise_12_D_3a {A b δ : ℝ} (hA : 0 < A) (hb : 0 < b) (hδ1 : δ < 1) :
    CournotNR A b δ (A / (4 * b)) ↔ 9 / 17 ≤ δ := by
  rw [exercise_12_D_3b_corrected hA hb hδ1 (by
    apply div_lt_div_of_pos_left hA (by positivity); linarith)]
  have : 9 * (A - 3 * b * (A / (4 * b))) / (5 * A - 3 * b * (A / (4 * b))) = 9 / 17 := by
    field_simp; ring
  rw [this]

/-- **Exercise 12.D.3(b) is false on the printed interval** (MWG, p. 433; correction). For
`q ∈ [A/(2b), A/b]` the market price is at most `c`, so `π(q) ≤ 0 < π*` and (12.AA.3) fails for
every `δ ∈ [0, 1)`: no output in the printed interval is sustainable by Nash reversion. -/
theorem exercise_12_D_3b_printed_false {A b δ q : ℝ} (hA : 0 < A) (hb : 0 < b) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hq1 : A / (2 * b) ≤ q) : ¬ CournotNR A b δ q := by
  unfold CournotNR
  rw [cournot_gain hb]
  intro h
  have hq : A ≤ 2 * b * q := by rw [div_le_iff₀ (by positivity)] at hq1; linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hgain : 0 < (A - 3 * b * q) ^ 2 / (4 * b) := by
    have : A - 3 * b * q ≠ 0 := by nlinarith
    positivity
  have hπ : (A - 2 * b * q) * q - A ^ 2 / (9 * b) < 0 := by
    have h1 : (A - 2 * b * q) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq0.le
    have h2 : 0 < A ^ 2 / (9 * b) := by positivity
    linarith
  have : δ / (1 - δ) * ((A - 2 * b * q) * q - A ^ 2 / (9 * b)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hδ0 (by linarith)) hπ.le
  linarith

/-- **Exercise 12.D.3(b): the threshold is differentiable and decreasing** (MWG, p. 433;
correction: MWG says increasing). `δ(q) = 9(A − 3bq)/(5A − 3bq)` has derivative
`−108Ab/(5A − 3bq)² < 0` on `q < 5A/(3b)`. -/
theorem exercise_12_D_3b_threshold {A b q : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hq : 3 * b * q < 5 * A) :
    HasDerivAt (fun q => 9 * (A - 3 * b * q) / (5 * A - 3 * b * q))
      (-(108 * A * b) / (5 * A - 3 * b * q) ^ 2) q ∧
    -(108 * A * b) / (5 * A - 3 * b * q) ^ 2 < 0 := by
  have hne : 5 * A - 3 * b * q ≠ 0 := by linarith
  constructor
  · have h1 : HasDerivAt (fun q => 9 * (A - 3 * b * q)) (9 * (-(3 * b))) q := by
      have := ((hasDerivAt_id q).const_mul (3 * b)).const_sub A |>.const_mul 9
      simpa using this
    have h2 : HasDerivAt (fun q => 5 * A - 3 * b * q) (-(3 * b)) q := by
      have := ((hasDerivAt_id q).const_mul (3 * b)).const_sub (5 * A)
      simpa using this
    refine (h1.div h2 hne).congr_deriv ?_
    field_simp; ring
  · apply div_neg_of_neg_of_pos (by nlinarith) (by positivity)

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 12.C.9(c) and 12.D.1

MWG, pp. 431, 433.

* `exercise_12_C_9c`: in any Cournot equilibrium with constant unit costs, industry profit
  divided by industry revenue equals `H/ε`, with `H = ∑ⱼ (qⱼ/Q)²` and `ε = −p(Q)/(p'(Q)Q)`.
* `exercise_12_D_1a`-`exercise_12_D_1c`: the conditions under which the strategies (12.D.1)
  sustain the monopoly price, comparing the discounted collusive profit with the best one-period
  (or `K`-period) deviation followed by zero profits: `δγ ≥ 1/2` with demand growth `γ`,
  `δ(1 − γ) ≥ 1/2` when the market ends with probability `γ` each period, and `δ^K ≥ 1/2` when
  a deviation is answered only after `K` periods.
-/

namespace MWG.MarketPower

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Exercise 12.C.9(c)** (MWG, p. 431). In a Cournot equilibrium with constant unit costs `cⱼ`
in which every producing firm satisfies its first-order condition `p'(Q)qⱼ + p(Q) = cⱼ`, the ratio
of industry profit to industry revenue is `H/ε`, where `H = ∑ⱼ (qⱼ/Q)²` is the Herfindahl index
and `ε = −p(Q)/(p'(Q)Q)` is the elasticity of demand, `Q = ∑ⱼ qⱼ` the industry output
(the identity holds for any `Q ≠ 0`). Firms with `qⱼ = 0` contribute nothing. -/
theorem exercise_12_C_9c {c q : ι → ℝ} {P P' Q : ℝ} (hQ0 : Q ≠ 0)
    (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hfoc : ∀ j, q j ≠ 0 → P' * q j + P = c j) :
    (∑ j, (P - c j) * q j) / (P * Q) = (∑ j, (q j / Q) ^ 2) / (-(P / (P' * Q))) := by
  have hterm : ∀ j, (P - c j) * q j = -P' * q j ^ 2 := by
    intro j
    by_cases hj : q j = 0
    · rw [hj]; ring
    · rw [← hfoc j hj]; ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum]
  have hsq : ∑ j, (q j / Q) ^ 2 = (∑ j, q j ^ 2) / Q ^ 2 := by
    rw [Finset.sum_div]; congr 1; funext j; rw [div_pow]
  rw [hsq]
  field_simp

/-- **Exercise 12.D.1(a)** (MWG, p. 433). With demand growing at rate `γ` (`x_t = γᵗx`,
`δγ < 1`) the collusive value from period `t`, `γᵗπᵐ/(2(1 − δγ))`, is at least the best
deviation payoff `γᵗπᵐ` (followed by zero profits) iff `δγ ≥ 1/2`. -/
theorem exercise_12_D_1a {δ γ πm : ℝ} (hγ : 0 < γ) (hπ : 0 < πm) (h1 : δ * γ < 1) (t : ℕ) :
    γ ^ t * πm ≤ γ ^ t * πm / (2 * (1 - δ * γ)) ↔ 1 / 2 ≤ δ * γ := by
  have hpos : 0 < γ ^ t * πm := by positivity
  rw [le_div_iff₀ (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Exercise 12.D.1(b)** (MWG, p. 433). If after each period the market ends with probability
`γ`, expected discounted profits use the factor `δ(1 − γ)`; the monopoly price is sustained iff
`δ(1 − γ) ≥ 1/2`. -/
theorem exercise_12_D_1b {δ γ πm : ℝ} (hπ : 0 < πm) (h1 : δ * (1 - γ) < 1) :
    πm ≤ πm / (2 * (1 - δ * (1 - γ))) ↔ 1 / 2 ≤ δ * (1 - γ) := by
  rw [le_div_iff₀ (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Exercise 12.D.1(c)** (MWG, p. 433). If it takes `K` periods to respond to a deviation, the
deviator earns `πᵐ` for `K` periods, `πᵐ(1 − δ^K)/(1 − δ)`; collusion is sustained iff
`δ^K ≥ 1/2`. -/
theorem exercise_12_D_1c {δ πm : ℝ} (hπ : 0 < πm) (hδ1 : δ < 1) (K : ℕ) :
    πm * (1 - δ ^ K) / (1 - δ) ≤ πm / (2 * (1 - δ)) ↔ 1 / 2 ≤ δ ^ K := by
  have h1δ : 0 < 1 - δ := by linarith
  rw [div_le_div_iff₀ h1δ (by linarith)]
  have e1 : πm * (1 - δ ^ K) * (2 * (1 - δ)) = (πm * (1 - δ)) * (2 * (1 - δ ^ K)) := by ring
  have hp := mul_pos hπ h1δ
  rw [e1]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left (show 1 < 2 * (1 - δ ^ K) by linarith) hp
    linarith
  · intro h
    have := mul_le_mul_of_nonneg_left (show 2 * (1 - δ ^ K) ≤ 1 by linarith) hp.le
    linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Entry

MWG, Section 12.E, pp. 405-411, and Exercise 12.E.2.

The two-stage entry model: firms decide to enter (paying `K > 0`), then the `J` entrants play a
unique symmetric stage-2 equilibrium with profit `π_J` per firm. With the convention that a firm
enters when indifferent, `J*` entrants form an SPNE iff (12.E.1) `π_{J*} ≥ K` and
(12.E.2) `π_{J*+1} < K` (`IsEntryEquilibrium`).

* `entry_equilibrium_unique`, `entry_equilibrium_exists`, `entry_equilibrium_iff`: with `π_J`
  decreasing, the equilibrium number is the unique `Ĵ` with `π_J ≥ K` for `J ≤ Ĵ` and `π_J < K`
  for `J > Ĵ`; `footnote_12_22`: with weak inequalities `Ĵ − 1` is also an equilibrium when
  `π_Ĵ = K`.
* `example_12_E_1`: Cournot entry, `π_J = ((a − c)/(J + 1))²/b`, and `J*` is the largest
  integer `≤ J̃ = (a − c)/√(bK) − 1`; comparative statics in `K`.
* `example_12_E_2`: Bertrand entry, `J* = 1`.
* `entryWelfare` (12.E.5), `example_12_E_3`: the linear welfare function and the three numerical
  cases `J° = 2, 3, 8` with `J* = 4, 7, 26`.
* `exercise_12_E_2`, `proposition_12_E_1`: under (A1)-(A3) the equilibrium number of entrants
  is at least `J° − 1`, for every welfare maximizer `J°` (so also footnote 23).
-/

namespace MWG.MarketPower

open Set MWG.CompetitiveMarkets

/-- **Conditions (12.E.1)-(12.E.2)** (MWG, p. 406): `J ≥ 1` entrants form an equilibrium of the
two-stage entry game (firms enter when indifferent) iff `π_J ≥ K` and `π_{J+1} < K`. -/
def IsEntryEquilibrium (π : ℕ → ℝ) (K : ℝ) (J : ℕ) : Prop := 1 ≤ J ∧ K ≤ π J ∧ π (J + 1) < K

/-- With `π_J` decreasing there is at most one equilibrium number of firms (MWG, p. 406). -/
theorem entry_equilibrium_unique {π : ℕ → ℝ} {K : ℝ} (hπ : Antitone π) {J₁ J₂ : ℕ}
    (h₁ : IsEntryEquilibrium π K J₁) (h₂ : IsEntryEquilibrium π K J₂) : J₁ = J₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hπ (show J₁ + 1 ≤ J₂ by omega); linarith [h₁.2.2, h₂.2.1]
  · have := hπ (show J₂ + 1 ≤ J₁ by omega); linarith [h₂.2.2, h₁.2.1]

/-- With `π_J` decreasing, `π₁ ≥ K` and `π_J < K` for some `J` (e.g. `π_J → 0`), an equilibrium
number of entrants exists (MWG, p. 406). -/
theorem entry_equilibrium_exists {π : ℕ → ℝ} {K : ℝ} (h1 : K ≤ π 1)
    (hex : ∃ n, π (n + 1) < K) : ∃ J, IsEntryEquilibrium π K J := by
  classical
  set n := Nat.find hex with hn
  have hspec : π (n + 1) < K := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hspec; linarith
  · refine ⟨n, hpos, ?_, hspec⟩
    have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this
    rwa [Nat.sub_add_cancel hpos] at this

/-- **The equilibrium number of firms** (MWG, p. 406). With `π_J` decreasing, `J*` is an
equilibrium iff `π_J ≥ K` for all `1 ≤ J ≤ J*` and `π_J < K` for all `J > J*`. -/
theorem entry_equilibrium_iff {π : ℕ → ℝ} {K : ℝ} (hπ : Antitone π) {J : ℕ} (hJ : 1 ≤ J) :
    IsEntryEquilibrium π K J ↔ (∀ J', J' ≤ J → K ≤ π J') ∧ ∀ J', J < J' → π J' < K := by
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨fun J' hJ' => h1.trans (hπ hJ'), fun J' hJ' => lt_of_le_of_lt (hπ hJ') h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hJ, h1 J le_rfl, h2 (J + 1) (by omega)⟩

/-- **Footnote 22** (MWG, p. 406). If firms need not enter when indifferent, the conditions are
`π_{J*} ≥ K` and `π_{J*+1} ≤ K`; when `π_Ĵ = K` exactly, both `Ĵ` and `Ĵ − 1` satisfy them. -/
theorem footnote_12_22 {π : ℕ → ℝ} {K : ℝ} (hπ : Antitone π) {J : ℕ} (hJ : 2 ≤ J)
    (heq : π J = K) (hnext : π (J + 1) ≤ K) :
    (K ≤ π J ∧ π (J + 1) ≤ K) ∧ (K ≤ π (J - 1) ∧ π (J - 1 + 1) ≤ K) := by
  refine ⟨⟨heq.ge, hnext⟩, ⟨heq ▸ hπ (Nat.sub_le J 1), ?_⟩⟩
  rw [Nat.sub_add_cancel (by omega)]; exact heq.le

/-! ### Examples 12.E.1 and 12.E.2 -/

/-- Per-firm Cournot profit with `J` firms, linear demand and constant cost (12.E.4). -/
noncomputable def cournotEntryProfit (a b c : ℝ) (J : ℕ) : ℝ := ((a - c) / (J + 1)) ^ 2 / b

/-- **Example 12.E.1** (MWG, p. 407). With `J` Cournot firms, `p(q) = a − bq`, `c(q) = cq`:
each produces `q_J = (a − c)/(b(J + 1))` (12.E.3) at the price `(a + Jc)/(J + 1)`
(Exercise 12.C.7) and earns `π_J = ((a − c)/(J + 1))²/b` (12.E.4); `π_J` is strictly decreasing,
`π_J → 0` and `Jq_J → (a − c)/b`. -/
theorem example_12_E_1 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ J : ℕ, ((a + J * c) / (J + 1) - c) * ((a - c) / (b * (J + 1))) =
      cournotEntryProfit a b c J) ∧
    StrictAnti (cournotEntryProfit a b c) ∧
    Filter.Tendsto (cournotEntryProfit a b c) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun J : ℕ => J * ((a - c) / (b * (J + 1)))) Filter.atTop
      (nhds ((a - c) / b)) := by
  have hA : 0 < a - c := by linarith
  refine ⟨fun J => by unfold cournotEntryProfit; field_simp; ring, fun m n hmn => ?_, ?_, ?_⟩
  · unfold cournotEntryProfit
    have : (m : ℝ) < n := by exact_mod_cast hmn
    apply div_lt_div_of_pos_right _ hb
    have h1 : (a - c) / (n + 1) < (a - c) / (m + 1) :=
      div_lt_div_of_pos_left hA (by positivity) (by linarith)
    have h2 : 0 < (a - c) / (n + 1) := by positivity
    nlinarith
  · unfold cournotEntryProfit
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (h.mul h).const_mul ((a - c) ^ 2 / b)
    rw [mul_zero, mul_zero] at h2
    refine h2.congr fun J => ?_
    field_simp
  · have := (exercise_12_C_7_limits hac hb).2.2.2.2
    refine this.congr fun J => ?_
    field_simp

/-- **Example 12.E.1, the equilibrium number of firms** (MWG, p. 407). `J ≥ 1` is the
equilibrium number of Cournot entrants iff `(J + 1)² ≤ (a − c)²/(bK) < (J + 2)²`, i.e. iff `J`
is the largest integer not exceeding `J̃ = (a − c)/√(bK) − 1`. -/
theorem example_12_E_1_number {a b c K : ℝ} (hb : 0 < b) (hK : 0 < K) {J : ℕ}
    (hJ : 1 ≤ J) :
    IsEntryEquilibrium (cournotEntryProfit a b c) K J ↔
      ((J : ℝ) + 1) ^ 2 ≤ (a - c) ^ 2 / (b * K) ∧ (a - c) ^ 2 / (b * K) < ((J : ℝ) + 2) ^ 2 := by
  have hbK : 0 < b * K := by positivity
  have aux : ∀ n : ℝ, 0 < n → ((K ≤ ((a - c) / n) ^ 2 / b ↔ n ^ 2 ≤ (a - c) ^ 2 / (b * K)) ∧
      (((a - c) / n) ^ 2 / b < K ↔ (a - c) ^ 2 / (b * K) < n ^ 2)) := by
    intro n hn
    have hn2 : 0 < n ^ 2 := by positivity
    rw [le_div_iff₀ hb, div_pow, le_div_iff₀ hn2, le_div_iff₀ hbK, div_lt_iff₀ hb,
      div_lt_iff₀ hn2, div_lt_iff₀ hbK]
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith
  unfold IsEntryEquilibrium cournotEntryProfit
  push_cast
  rw [(aux _ (by positivity)).1, (aux _ (by positivity)).2]
  simp only [hJ, true_and]
  rw [show ((J : ℝ) + 1 + 1) = J + 2 by ring]

/-- **Example 12.E.1, comparative statics** (MWG, p. 407). A lower entry cost weakly raises the
equilibrium number of firms, and `J* → ∞` as `K → 0`. -/
theorem example_12_E_1_statics {a b c : ℝ} (hac : c < a) (hb : 0 < b) {K K' : ℝ}
    (hKK : K' ≤ K) {J J' : ℕ}
    (hJ : IsEntryEquilibrium (cournotEntryProfit a b c) K J)
    (hJ' : IsEntryEquilibrium (cournotEntryProfit a b c) K' J') :
    J ≤ J' ∧ ∀ N : ℕ, ∃ K₀ > 0, ∀ K'', 0 < K'' → K'' < K₀ → ∀ J'',
      IsEntryEquilibrium (cournotEntryProfit a b c) K'' J'' → N ≤ J'' := by
  have hanti : StrictAnti (cournotEntryProfit a b c) := (example_12_E_1 hac hb).2.1
  constructor
  · by_contra hlt
    push Not at hlt
    have := hanti.antitone (show J' + 1 ≤ J by omega)
    linarith [hJ.2.1, hJ'.2.2]
  · intro N
    refine ⟨cournotEntryProfit a b c N, by unfold cournotEntryProfit; positivity,
      fun K'' _ hK'' J'' hJ'' => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hanti.antitone (show J'' + 1 ≤ N by omega)
    linarith [hJ''.2.2]

/-- **Example 12.E.2** (MWG, p. 407). With Bertrand competition in stage 2, `π₁ = πᵐ` and
`π_J = 0` for `J ≥ 2`; if `πᵐ ≥ K > 0`, the unique equilibrium has one entrant, the monopolist. -/
theorem example_12_E_2 {πm K : ℝ} (hK : 0 < K) (hπm : K ≤ πm) :
    let π : ℕ → ℝ := fun J => if J = 1 then πm else 0
    IsEntryEquilibrium π K 1 ∧ ∀ J, IsEntryEquilibrium π K J → J = 1 := by
  intro π
  refine ⟨⟨le_rfl, by simp [π, hπm], by simp [π, hK]⟩, fun J hJ => ?_⟩
  by_contra hne
  have := hJ.2.1
  simp only [π, hne, ite_false] at this
  linarith

/-! ### Entry and welfare -/

/-- **Social welfare with `J` firms** (12.E.5), MWG, p. 408:
`W(J) = ∫₀^{Jq_J} p(s) ds − Jc(q_J) − JK`. -/
noncomputable def entryWelfare (p c : ℝ → ℝ) (q : ℕ → ℝ) (K : ℝ) (J : ℕ) : ℝ :=
  (∫ s in (0 : ℝ)..(J * q J), p s) - J * c (q J) - J * K

/-- The linear welfare function of Example 12.E.3:
`W(J) = ((a − c)²/b)(J² + 2J)/(2(J + 1)²) − JK`. -/
theorem entryWelfare_linear {a b c K : ℝ} (hb : 0 < b) (J : ℕ) :
    entryWelfare (fun s => a - b * s) (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K J =
      (a - c) ^ 2 / b * ((J ^ 2 + 2 * J) / (2 * (J + 1) ^ 2)) - J * K := by
  unfold entryWelfare
  simp only []
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => b * s).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The welfare comparison polynomial. -/
theorem example_12_E_3_aux (A : ℝ) (J : ℝ) (hJ : 0 ≤ J) (m : ℝ) (hm : 0 < m)
    (hA : A = (m + 1) ^ 3) :
    A * ((J ^ 2 + 2 * J) / (2 * (J + 1) ^ 2)) - J ≤
      A * ((m ^ 2 + 2 * m) / (2 * (m + 1) ^ 2)) - m := by
  subst hA
  have h1 : (0 : ℝ) < J + 1 := by linarith
  have h2 : (0 : ℝ) < m + 1 := by linarith
  rw [← sub_nonneg]
  have key : (m + 1) ^ 3 * ((m ^ 2 + 2 * m) / (2 * (m + 1) ^ 2)) - m -
      ((m + 1) ^ 3 * ((J ^ 2 + 2 * J) / (2 * (J + 1) ^ 2)) - J) =
      (J - m) ^ 2 * (2 * J + m + 3) / (2 * (J + 1) ^ 2) := by
    field_simp; ring
  rw [key]
  positivity

/-- **Example 12.E.3** (MWG, p. 408). In the linear Cournot model with `A = (a − c)²/b`, if
`A/K = (J̄ + 1)³` for an integer `J̄`, then `J° = J̄` maximizes welfare among all numbers of firms
(the real welfare function is maximized at `J̄`, where `(J̄ + 1)³ = A/K`, (12.E.6)), while the
equilibrium number is the integer part of `J̃ = (J̄ + 1)^{3/2} − 1` ((12.E.7)). In particular:
`J° = 2` gives `J* = 4`, `J° = 3` gives `J* = 7`, `J° = 8` gives `J* = 26`. -/
theorem example_12_E_3 {a b c K : ℝ} (hb : 0 < b) (hK : 0 < K) (m : ℕ) (hm : 1 ≤ m)
    (hA : (a - c) ^ 2 / b = ((m : ℝ) + 1) ^ 3 * K) :
    (∀ J : ℕ, entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K J ≤ entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K m) ∧
    ((m = 2 → IsEntryEquilibrium (cournotEntryProfit a b c) K 4) ∧
     (m = 3 → IsEntryEquilibrium (cournotEntryProfit a b c) K 7) ∧
     (m = 8 → IsEntryEquilibrium (cournotEntryProfit a b c) K 26)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨fun J => ?_, ?_, ?_, ?_⟩
  · rw [entryWelfare_linear hb, entryWelfare_linear hb, hA]
    have := example_12_E_3_aux (((m : ℝ) + 1) ^ 3) J (Nat.cast_nonneg J) m hm0 rfl
    have hK' := mul_le_mul_of_nonneg_right this hK.le
    nlinarith
  all_goals intro hmv
  all_goals subst hmv
  all_goals rw [example_12_E_1_number hb hK (by norm_num)]
  all_goals rw [div_mul_eq_div_div, hA, mul_div_assoc, div_self hK.ne', mul_one]
  all_goals norm_num

/-! ### Proposition 12.E.1 -/

/-- **Exercise 12.E.2** (MWG, p. 434). Under (A1)-(A3), `p` nonincreasing and `c` convex
(tangent-line inequality with derivative `c'`), per-firm profit `π_J = p(Jq_J)q_J − c(q_J)` is
nonincreasing in `J`. -/
theorem exercise_12_E_2 {p c c' : ℝ → ℝ} {q : ℕ → ℝ} (hp : Antitone p)
    (hc : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' x) (Ici 0) x) (hc' : MonotoneOn c' (Ici 0))
    (hq0 : ∀ J, 0 ≤ q J)
    (hA1 : ∀ J J' : ℕ, J' ≤ J → J' * q J' ≤ J * q J) (hA2 : ∀ J J' : ℕ, J' ≤ J → q J ≤ q J')
    (hA3 : ∀ J : ℕ, c' (q J) ≤ p (J * q J)) :
    Antitone fun J : ℕ => p (J * q J) * q J - c (q J) := by
  intro J' J hJ
  simp only
  have h1 : p (J * q J) ≤ p (J' * q J') := hp (hA1 J J' hJ)
  have h2 : q J ≤ q J' := hA2 J J' hJ
  -- `p(Q_{J'})q − c(q)` is nondecreasing for `q ≤ q_{J'}`
  have htan := foc_le_tangent_convex hc hc' (hq0 J) (hq0 J')
  have htan2 := foc_le_tangent_convex hc hc' (hq0 J') (hq0 J)
  have h3 : c' (q J) ≤ c' (q J') := hc' (hq0 J) (hq0 J') h2
  nlinarith [hA3 J', mul_le_mul_of_nonneg_right h1 (hq0 J)]

/-- **Proposition 12.E.1** (MWG, p. 409). Suppose the post-entry game satisfies (A1)-(A3),
`p` is nonincreasing and continuous, and `c` is convex (with derivative `c'`) with `c(0) = 0`.
Let `J° ≥ 1` maximize welfare `W(J)` (12.E.5) among `J ≥ 1`. Then any equilibrium number of
entrants satisfies `J* ≥ J° − 1`; indeed `π_{J°−1} ≥ K` (via (12.E.8)). -/
theorem proposition_12_E_1 {p c c' : ℝ → ℝ} {q : ℕ → ℝ} {K : ℝ} (hp : Antitone p)
    (hpc : Continuous p)
    (hc : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' x) (Ici 0) x) (hc' : MonotoneOn c' (Ici 0))
    (hq0 : ∀ J, 0 ≤ q J)
    (hA1 : ∀ J J' : ℕ, J' ≤ J → J' * q J' ≤ J * q J) (hA2 : ∀ J J' : ℕ, J' ≤ J → q J ≤ q J')
    (hA3 : ∀ J : ℕ, c' (q J) ≤ p (J * q J)) {Jo : ℕ} (hJo : 1 ≤ Jo)
    (hmax : ∀ J, 1 ≤ J → entryWelfare p c q K J ≤ entryWelfare p c q K Jo) :
    (2 ≤ Jo → K ≤ p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1))) ∧
    ∀ J, IsEntryEquilibrium (fun J : ℕ => p (J * q J) * q J - c (q J)) K J → Jo - 1 ≤ J := by
  have hanti := exercise_12_E_2 hp hc hc' hq0 hA1 hA2 hA3
  have key : 2 ≤ Jo → K ≤ p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1)) := by
    intro h2
    set J' := Jo - 1 with hJ'
    have hJo' : Jo = J' + 1 := by omega
    have hW := hmax J' (by omega)
    unfold entryWelfare at hW
    set Q := (Jo : ℝ) * q Jo with hQ
    set Q' := (J' : ℝ) * q J' with hQ'
    have hQQ : Q' ≤ Q := hA1 Jo J' (by omega)
    have hQ'0 : 0 ≤ Q' := mul_nonneg (Nat.cast_nonneg _) (hq0 _)
    have hint : (∫ s in (0 : ℝ)..Q, p s) - ∫ s in (0 : ℝ)..Q', p s = ∫ s in Q'..Q, p s :=
      intervalIntegral.integral_interval_sub_left (hpc.intervalIntegrable _ _)
        (hpc.intervalIntegrable _ _)
    have hbound : (∫ s in Q'..Q, p s) ≤ p Q' * (Q - Q') := by
      have := intervalIntegral.integral_mono_on hQQ (hpc.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := p Q')) (fun s hs => hp hs.1)
      simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
    have htan := foc_le_tangent_convex hc hc' (hq0 J') (hq0 Jo)
    have hA3' := hA3 J'
    have hA2' : q Jo ≤ q J' := hA2 Jo J' (by omega)
    have hJ'cast : (Jo : ℝ) = J' + 1 := by rw [hJo']; push_cast; ring
    -- (12.E.8) and the convexity step
    have e : q J' + Q' - Q = Jo * (q J' - q Jo) := by
      rw [hQ, hQ', hJ'cast]; ring
    have hJo0 : (0 : ℝ) ≤ Jo := Nat.cast_nonneg _
    have hfinal : 0 ≤ (p Q' - c' (q J')) * (Jo * (q J' - q Jo)) :=
      mul_nonneg (by linarith) (mul_nonneg hJo0 (by linarith))
    have step1 : K ≤ (∫ s in Q'..Q, p s) - Jo * c (q Jo) + J' * c (q J') := by
      rw [← hint]; rw [hJ'cast] at hW ⊢; linarith
    rw [hJ'cast] at hfinal step1 e
    have e2 : p Q' * (q J' + Q' - Q) = p Q' * ((J' + 1) * (q J' - q Jo)) := by rw [e]
    have h4 := mul_le_mul_of_nonneg_left htan (show (0 : ℝ) ≤ J' + 1 by positivity)
    linarith
  refine ⟨key, fun J hJ => ?_⟩
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Jo := by omega
  have := hanti (show J + 1 ≤ Jo - 1 by omega)
  simp only at this
  linarith [key h2, hJ.2.2]

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strategic precommitments

MWG, Section 12.G, pp. 414-417, Exercises 12.C.9, 12.C.17 (interior equilibria) and 12.G.1.

* `eq_12_G_1`: differentiating `s₂*(k) = b₂(b₁(s₂*(k), k))` gives
  `ds₂*/dk = b₂'·(∂b₁/∂k)/(1 − (∂b₁/∂s₂)b₂')` (12.G.1); `figure_12_G_1`: under the stability
  condition the sign of `ds₂*/dk` is that of `b₂'·∂b₁/∂k`.
* `eq_12_G_2`: `dπ₁/dk = ∂π₁/∂k + (∂π₁/∂s₂)(ds₂*/dk)` when `∂π₁/∂s₁ = 0` (12.G.2).
* `cournot_two_costs`: the interior Cournot equilibrium with costs `c₁, c₂` (Exercise 12.C.9(a));
  `linearCity_two_costs`: the interior linear-city equilibrium with costs `c₁, c₂`
  (Exercise 12.C.17).
* `example_12_G_1`, `exercise_12_G_1`: lowering firm 1's cost lowers firm 2's Cournot output
  (`dq₂/dc₁ = 1/(3b) > 0`, beneficial to firm 1) but lowers firm 2's price in the linear city
  (`dp₂/dc₁ = 1/3 > 0`, detrimental to firm 1).
-/

namespace MWG.MarketPower

open Set Filter Topology Function

/-- **Condition (12.G.1)** (MWG, p. 414). Suppose `s₂*(k) = b₂(b₁(s₂*(k), k))` for `k` near
`k₀`, `b₁` has derivative `L` at `(s₂*(k₀), k₀)`, `b₂` has derivative `β` at
`b₁(s₂*(k₀), k₀)`, and `s₂*` has derivative `d` at `k₀`. Then
`d·(1 − L(1,0)β) = β·L(0,1)`, i.e. `ds₂*/dk = b₂'(∂b₁/∂k)/(1 − (∂b₁/∂s₂)b₂')`. -/
theorem eq_12_G_1 {b1 : ℝ × ℝ → ℝ} {b2 s2 : ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {β d k₀ : ℝ}
    (hb1 : HasFDerivAt b1 L (s2 k₀, k₀)) (hb2 : HasDerivAt b2 β (b1 (s2 k₀, k₀)))
    (hs2 : HasDerivAt s2 d k₀) (hid : ∀ᶠ k in 𝓝 k₀, s2 k = b2 (b1 (s2 k, k))) :
    d * (1 - L (1, 0) * β) = β * L (0, 1) := by
  have hf : HasDerivAt (fun k => (s2 k, k)) (d, 1) k₀ := hs2.prodMk (hasDerivAt_id k₀)
  have h1 := HasFDerivAt.comp_hasDerivAt (f := fun k => (s2 k, k)) k₀ hb1 hf
  have h2 := hb2.comp k₀ h1
  have h3 : HasDerivAt (fun k => b2 (b1 (s2 k, k))) d k₀ :=
    hs2.congr_of_eventuallyEq (hid.mono fun k hk => hk.symm)
  have heq := h2.unique h3
  have hsplit : ((d, 1) : ℝ × ℝ) = d • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at heq
  linarith

/-- **Figure 12.G.1** (MWG, p. 415). Under the stability condition `1 − (∂b₁/∂s₂)b₂' > 0`, the
sign of `ds₂*/dk` is the sign of `b₂'·∂b₁/∂k`: with strategic substitutes (`b₂' < 0`) an
investment that makes firm 1 more aggressive (`∂b₁/∂k > 0`) lowers `s₂`, and with strategic
complements (`b₂' > 0`) it raises `s₂`. -/
theorem figure_12_G_1 {Lk Ls β d : ℝ} (hstab : 0 < 1 - Ls * β)
    (h : d * (1 - Ls * β) = β * Lk) : (0 < d ↔ 0 < β * Lk) ∧ (d < 0 ↔ β * Lk < 0) := by
  constructor
  · constructor
    · intro hd; rw [← h]; exact mul_pos hd hstab
    · intro hp; rw [← h] at hp; exact pos_of_mul_pos_left hp hstab.le
  · constructor
    · intro hd; rw [← h]; exact mul_neg_of_neg_of_pos hd hstab
    · intro hp; rw [← h] at hp
      by_contra hge; push Not at hge
      linarith [mul_nonneg hge hstab.le]

/-- **Condition (12.G.2)** (MWG, p. 416). If `π₁` has derivative `Lp` at
`(s₁*(k₀), s₂*(k₀), k₀)` with `∂π₁/∂s₁ = 0` there (stage-2 equilibrium), and `s₁*`, `s₂*` have
derivatives `d₁`, `d₂`, then `k ↦ π₁(s₁*(k), s₂*(k), k)` has derivative
`∂π₁/∂k + (∂π₁/∂s₂)d₂`: the direct effect plus the strategic effect. -/
theorem eq_12_G_2 {π1 : ℝ × ℝ × ℝ → ℝ} {s1 s2 : ℝ → ℝ} {Lp : ℝ × ℝ × ℝ →L[ℝ] ℝ} {d1 d2 k₀ : ℝ}
    (hπ : HasFDerivAt π1 Lp (s1 k₀, s2 k₀, k₀)) (hs1 : HasDerivAt s1 d1 k₀)
    (hs2 : HasDerivAt s2 d2 k₀) (hfoc : Lp (1, 0, 0) = 0) :
    HasDerivAt (fun k => π1 (s1 k, s2 k, k)) (Lp (0, 0, 1) + Lp (0, 1, 0) * d2) k₀ := by
  have hf : HasDerivAt (fun k => (s1 k, s2 k, k)) (d1, d2, 1) k₀ :=
    hs1.prodMk (hs2.prodMk (hasDerivAt_id k₀))
  have h := HasFDerivAt.comp_hasDerivAt (f := fun k => (s1 k, s2 k, k)) k₀ hπ hf
  refine h.congr_deriv ?_
  have hsplit : ((d1, d2, 1) : ℝ × ℝ × ℝ) =
      d1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + d2 • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hfoc]
  ring

/-- **Exercise 12.C.9(a), interior case** (MWG, p. 431). In the linear Cournot duopoly with
costs `c₁, c₂`, if `a − 2c₁ + c₂ > 0` and `a − 2c₂ + c₁ > 0` then
`q₁ = (a − 2c₁ + c₂)/(3b)` and `q₂ = (a − 2c₂ + c₁)/(3b)` are mutual best responses (each is the
unique maximizer of the firm's profit over `q ≥ 0`). -/
theorem cournot_two_costs {a b c1 c2 : ℝ} (hb : 0 < b) (h1 : 0 < a - 2 * c1 + c2)
    (h2 : 0 < a - 2 * c2 + c1) :
    0 < (a - 2 * c1 + c2) / (3 * b) ∧ 0 < (a - 2 * c2 + c1) / (3 * b) ∧
    (∀ y, 0 ≤ y → (a - b * (y + (a - 2 * c2 + c1) / (3 * b))) * y - c1 * y ≤
      (a - b * ((a - 2 * c1 + c2) / (3 * b) + (a - 2 * c2 + c1) / (3 * b))) *
        ((a - 2 * c1 + c2) / (3 * b)) - c1 * ((a - 2 * c1 + c2) / (3 * b))) ∧
    (∀ y, 0 ≤ y → (a - b * (y + (a - 2 * c1 + c2) / (3 * b))) * y - c2 * y ≤
      (a - b * ((a - 2 * c2 + c1) / (3 * b) + (a - 2 * c1 + c2) / (3 * b))) *
        ((a - 2 * c2 + c1) / (3 * b)) - c2 * ((a - 2 * c2 + c1) / (3 * b))) := by
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · intro y _
    have key : (a - b * ((a - 2 * c1 + c2) / (3 * b) + (a - 2 * c2 + c1) / (3 * b))) *
        ((a - 2 * c1 + c2) / (3 * b)) - c1 * ((a - 2 * c1 + c2) / (3 * b)) -
        ((a - b * (y + (a - 2 * c2 + c1) / (3 * b))) * y - c1 * y) =
        b * (y - (a - 2 * c1 + c2) / (3 * b)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hb.le (sq_nonneg (y - (a - 2 * c1 + c2) / (3 * b)))]
  · intro y _
    have key : (a - b * ((a - 2 * c2 + c1) / (3 * b) + (a - 2 * c1 + c2) / (3 * b))) *
        ((a - 2 * c2 + c1) / (3 * b)) - c2 * ((a - 2 * c2 + c1) / (3 * b)) -
        ((a - b * (y + (a - 2 * c1 + c2) / (3 * b))) * y - c2 * y) =
        b * (y - (a - 2 * c2 + c1) / (3 * b)) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hb.le (sq_nonneg (y - (a - 2 * c2 + c1) / (3 * b)))]

/-- **Exercise 12.C.17, interior case** (MWG, p. 433). In the linear city with costs `c₁, c₂`
and `|c₁ − c₂| < 3t`, the prices `p₁ = t + (2c₁ + c₂)/3`, `p₂ = t + (c₁ + 2c₂)/3` are mutual
best responses (each the unique best response, both firms selling a positive amount). -/
theorem linearCity_two_costs {t M c1 c2 : ℝ} (ht : 0 < t) (hM : 0 < M)
    (h12 : c1 - c2 < 3 * t) (h21 : c2 - c1 < 3 * t) :
    (∀ q, q ≠ t + (2 * c1 + c2) / 3 →
      lcProfit t M c1 q (t + (c1 + 2 * c2) / 3) <
        lcProfit t M c1 (t + (2 * c1 + c2) / 3) (t + (c1 + 2 * c2) / 3)) ∧
    (∀ q, q ≠ t + (c1 + 2 * c2) / 3 →
      lcProfit t M c2 q (t + (2 * c1 + c2) / 3) <
        lcProfit t M c2 (t + (c1 + 2 * c2) / 3) (t + (2 * c1 + c2) / 3)) := by
  have e1 : (t + (t + (c1 + 2 * c2) / 3) + c1) / 2 = t + (2 * c1 + c2) / 3 := by ring
  have e2 : (t + (t + (2 * c1 + c2) / 3) + c2) / 2 = t + (c1 + 2 * c2) / 3 := by ring
  obtain ⟨_, hb1⟩ := lcBR_mid (M := M) (c := c1) (p := t + (c1 + 2 * c2) / 3) ht hM
    (by linarith) (by linarith)
  obtain ⟨_, hb2⟩ := lcBR_mid (M := M) (c := c2) (p := t + (2 * c1 + c2) / 3) ht hM
    (by linarith) (by linarith)
  rw [e1] at hb1
  rw [e2] at hb2
  exact ⟨hb1, hb2⟩

/-- **Example 12.G.1 and Exercise 12.G.1** (MWG, pp. 415-416 and 435). In the interior Cournot
equilibrium firm 2's output `(a − 2c₂ + c₁)/(3b)` has derivative `1/(3b) > 0` in `c₁`, so a
reduction in firm 1's cost lowers firm 2's output (good for firm 1); in the interior linear-city
equilibrium firm 2's price `t + (c₁ + 2c₂)/3` has derivative `1/3 > 0` in `c₁`, so a reduction
in firm 1's cost lowers firm 2's price (bad for firm 1). -/
theorem example_12_G_1 {a b c2 t : ℝ} (hb : 0 < b) (c1 : ℝ) :
    HasDerivAt (fun c1 => (a - 2 * c2 + c1) / (3 * b)) (1 / (3 * b)) c1 ∧ 0 < 1 / (3 * b) ∧
    HasDerivAt (fun c1 => t + (c1 + 2 * c2) / 3) (1 / 3) c1 ∧ (0 : ℝ) < 1 / 3 := by
  refine ⟨?_, by positivity, ?_, by norm_num⟩
  · have := ((hasDerivAt_id c1).const_add (a - 2 * c2)).div_const (3 * b)
    simpa using this
  · have := (((hasDerivAt_id c1).add_const (2 * c2)).div_const 3).const_add t
    simpa using this

/-- **Exercise 12.G.1** (MWG, p. 435): an alias of `example_12_G_1`. -/
theorem exercise_12_G_1 {a b c2 t : ℝ} (hb : 0 < b) (c1 : ℝ) :
    HasDerivAt (fun c1 => (a - 2 * c2 + c1) / (3 * b)) (1 / (3 * b)) c1 ∧ 0 < 1 / (3 * b) ∧
    HasDerivAt (fun c1 => t + (c1 + 2 * c2) / 3) (1 / 3) c1 ∧ (0 : ℝ) < 1 / 3 :=
  example_12_G_1 hb c1

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cournot best responses with general costs

MWG, Exercise 12.C.8(a)-(f), p. 431: the homogeneous-good `J`-firm Cournot model with a
downward-sloping inverse demand `P` and an identical increasing convex cost `c`.

* `cbrProfit`, `IsBROn`: the profit `P(Q₋ⱼ + q)q − c(q)` of a firm facing rivals' aggregate
  `Q₋ⱼ`, and best responses within a strategy set `S`; `cgProfit`, `IsCournotGameNE`: the game
  among the firms of a finite set `E`; `IsCournotEqm`: every firm best-responds to its rivals'
  aggregate output.
* (a) `exercise_12_C_8a`: a firm's profit depends on the others' outputs only through `Q₋ⱼ`, so
  Nash equilibria are exactly profiles of best responses `qⱼ ∈ b(Q₋ⱼ)`.
* (b) `exercise_12_C_8b`: a strictly decreasing continuous demand and linear cost with two
  best responses to `Q₋ⱼ = 0`.
* (c) `exercise_12_C_8c`: if `Q̂₋ⱼ > Q₋ⱼ`, `q ∈ b(Q₋ⱼ)`, `q̂ ∈ b(Q̂₋ⱼ)` then
  `q̂ + Q̂₋ⱼ ≥ q + Q₋ⱼ` (revealed preference, using `P` strictly decreasing and `c` convex; the
  monotonicity of `c` is not needed). Consequences: `exercise_12_C_8c_monotone` (`b(R) + R` is
  nondecreasing along any selection), `exercise_12_C_8c_jump` (jumps are upward),
  `exercise_12_C_8c_deriv` (`b' ≥ −1` where `b` is differentiable).
* (d) As printed the existence claim is false: `exercise_12_C_8d_counterexample` has a strictly
  decreasing continuous demand and increasing linear cost with no best response at all, hence no
  equilibrium. Corrected (`exercise_12_C_8d`): with quantities in a compact interval `[0, B]` and
  `P`, `c` continuous, a symmetric pure-strategy equilibrium exists; the proof is the book's hint,
  part (c) plus a supremum argument (no fixed-point theorem).
* (e) `exercise_12_C_8e`: a kinked (concave, strictly decreasing) demand with a continuum of
  duopoly equilibria `(t, 2 − t)`, `t ∈ [1/2, 3/2]`.
* (f) `exercise_12_C_8f`: if `P` is differentiable with `P' < 0` and `c` is differentiable and
  convex, every pure equilibrium is symmetric; if in addition each firm's marginal revenue
  `P(Q) + qP'(Q)` is nonincreasing in `Q` (e.g. `P` concave), the equilibrium is unique.
  `exercise_12_C_8f_instance` verifies the hypotheses for linear demand and quadratic cost.

Departures: inverse demand `P : ℝ → ℝ` is primitive ("downward sloping" read as strictly
decreasing on `[0, ∞)`); (d) adds compactness and continuity (see `docs/corrections.md`).
-/

namespace MWG.MarketPower

open Set Filter Topology

variable {ι : Type*} [DecidableEq ι]

/-- Profit of a Cournot firm producing `y` when its rivals produce `R` in total:
`P(R + y)y − c(y)` (MWG, Exercise 12.C.8). -/
def cbrProfit (P c : ℝ → ℝ) (R y : ℝ) : ℝ := P (R + y) * y - c y

/-- `y` is a best response to the rivals' aggregate output `R` within the strategy set `S`. -/
def IsBROn (P c : ℝ → ℝ) (S : Set ℝ) (R y : ℝ) : Prop :=
  y ∈ S ∧ ∀ y' ∈ S, cbrProfit P c R y' ≤ cbrProfit P c R y

/-- Firm `j`'s profit in the Cournot game among the firms of `E` at the output profile `q`. -/
def cgProfit (P c : ℝ → ℝ) (E : Finset ι) (q : ι → ℝ) (j : ι) : ℝ :=
  P (∑ k ∈ E, q k) * q j - c (q j)

/-- A pure-strategy Nash equilibrium of the Cournot game among the firms of `E`, strategy set
`S`: no firm gains by a unilateral change of its own output. -/
def IsCournotGameNE (P c : ℝ → ℝ) (S : Set ℝ) (E : Finset ι) (q : ι → ℝ) : Prop :=
  ∀ j ∈ E, q j ∈ S ∧ ∀ y ∈ S, cgProfit P c E (Function.update q j y) j ≤ cgProfit P c E q j

/-- Every firm of `E` best-responds to its rivals' aggregate output `Q₋ⱼ`. -/
def IsCournotEqm (P c : ℝ → ℝ) (S : Set ℝ) (E : Finset ι) (q : ι → ℝ) : Prop :=
  ∀ j ∈ E, IsBROn P c S (∑ k ∈ E.erase j, q k) (q j)

/-- A firm's game profit after changing its own output to `y` depends on the others' outputs only
through their aggregate `Q₋ⱼ` (MWG, Exercise 12.C.8(a)). -/
theorem cgProfit_update (P c : ℝ → ℝ) (E : Finset ι) (q : ι → ℝ) {j : ι} (hj : j ∈ E) (y : ℝ) :
    cgProfit P c E (Function.update q j y) j = cbrProfit P c (∑ k ∈ E.erase j, q k) y := by
  unfold cgProfit cbrProfit
  rw [Finset.sum_update_of_mem hj, Finset.sdiff_singleton_eq_erase, Function.update_self,
    add_comm]

/-- **Exercise 12.C.8(a)** (MWG, p. 431). Firm `j`'s best response can be written as
`b(Q₋ⱼ)`: a profile is a Nash equilibrium of the Cournot game iff each `qⱼ` is a best response to
the rivals' aggregate output `Q₋ⱼ = ∑_{k ≠ j} q_k`. -/
theorem exercise_12_C_8a (P c : ℝ → ℝ) (S : Set ℝ) (E : Finset ι) (q : ι → ℝ) :
    IsCournotGameNE P c S E q ↔ IsCournotEqm P c S E q := by
  have hown : ∀ j ∈ E, cgProfit P c E q j = cbrProfit P c (∑ k ∈ E.erase j, q k) (q j) := by
    intro j hj
    rw [← cgProfit_update P c E q hj, Function.update_eq_self]
  constructor
  · intro h j hj
    refine ⟨(h j hj).1, fun y hy => ?_⟩
    rw [← cgProfit_update P c E q hj, ← hown j hj]
    exact (h j hj).2 y hy
  · intro h j hj
    refine ⟨(h j hj).1, fun y hy => ?_⟩
    rw [cgProfit_update P c E q hj, hown j hj]
    exact (h j hj).2 y hy

/-- The inverse demand of Exercise 12.C.8(b): `3 − Q` up to `Q = 1`, then `1 + 1/Q`. -/
noncomputable def cbrDemandB (Q : ℝ) : ℝ := if Q ≤ 1 then 3 - Q else 1 + 1 / Q

/-- **Exercise 12.C.8(b)** (MWG, p. 431). The best response need not be unique: with the
strictly decreasing inverse demand `cbrDemandB` and the increasing linear (convex) cost
`c(q) = q`, both `q = 1` and `q = 2` are best responses to `Q₋ⱼ = 0` (indeed every `q ≥ 1` is). -/
theorem exercise_12_C_8b :
    StrictAnti cbrDemandB ∧ StrictMono (fun y : ℝ => y) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y) ∧
    IsBROn cbrDemandB (fun y => y) (Ici 0) 0 1 ∧ IsBROn cbrDemandB (fun y => y) (Ici 0) 0 2 := by
  have hprof : ∀ y : ℝ, 0 ≤ y → cbrProfit cbrDemandB (fun y => y) 0 y ≤ 1 := by
    intro y hy
    unfold cbrProfit cbrDemandB
    rw [zero_add]
    split_ifs with h
    · nlinarith [sq_nonneg (y - 1)]
    · have hy1 : (1 : ℝ) < y := lt_of_not_ge h
      field_simp
      linarith
  have h1 : cbrProfit cbrDemandB (fun y => y) 0 1 = 1 := by
    unfold cbrProfit cbrDemandB; norm_num
  have h2 : cbrProfit cbrDemandB (fun y => y) 0 2 = 1 := by
    unfold cbrProfit cbrDemandB; norm_num
  refine ⟨fun x y hxy => ?_, strictMono_id, convexOn_id (convex_Ici 0),
    ⟨mem_Ici.2 zero_le_one, fun y hy => by rw [h1]; exact hprof y hy⟩,
    ⟨mem_Ici.2 zero_le_two, fun y hy => by rw [h2]; exact hprof y hy⟩⟩
  unfold cbrDemandB
  split_ifs with hy hx hx
  · linarith
  · exact absurd (hxy.le.trans hy) hx
  · have hx1 : (1 : ℝ) < y := lt_of_not_ge hy
    have : 1 / y < 1 := (div_lt_one (by linarith)).2 hx1
    linarith
  · have hx1 : (1 : ℝ) < x := lt_of_not_ge hx
    have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy
    linarith

/-- For a convex `c` on `[0, ∞)`, moving two points inwards keeping their sum fixed lowers
`c(x) + c(y)`: `c(x) + c(a + b − x) ≤ c(a) + c(b)` for `0 ≤ a ≤ x ≤ b`. -/
theorem cbr_convex_pair {c : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) c) {a b x : ℝ} (ha : 0 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) : c x + c (a + b - x) ≤ c a + c b := by
  rcases eq_or_lt_of_le (hax.trans hxb) with hab | hab
  · have h1 : x = a := le_antisymm (hab ▸ hxb) hax
    rw [h1, show a + b - a = b by ring]
  · set t := (b - x) / (b - a) with ht
    have hba : 0 < b - a := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hba.le
    have ht1 : 0 ≤ 1 - t := by
      rw [ht, sub_nonneg, div_le_one hba]; linarith
    have e1 : x = t * a + (1 - t) * b := by rw [ht]; field_simp; ring
    have e2 : a + b - x = (1 - t) * a + t * b := by rw [ht]; field_simp; ring
    have hb0 : (b : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.2 (by linarith)
    have i1 := hc.2 (mem_Ici.2 ha) hb0 ht0 ht1 (by ring)
    have i2 := hc.2 (mem_Ici.2 ha) hb0 ht1 ht0 (by ring)
    simp only [smul_eq_mul] at i1 i2
    calc c x + c (a + b - x) = c (t * a + (1 - t) * b) + c ((1 - t) * a + t * b) := by
          rw [← e1, ← e2]
      _ ≤ _ := by linarith

/-- **Exercise 12.C.8(c)** (MWG, p. 431). If `Q̂₋ⱼ > Q₋ⱼ ≥ 0`, `q ∈ b(Q₋ⱼ)` and
`q̂ ∈ b(Q̂₋ⱼ)`, then `q̂ + Q̂₋ⱼ ≥ q + Q₋ⱼ`. Here `P` is strictly decreasing and `c` convex on
`[0, ∞)`, and the strategy set `S ⊆ [0, ∞)` is an interval (`[0, ∞)` in the book). -/
theorem exercise_12_C_8c {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0)
    {R R' y y' : ℝ} (hR : 0 ≤ R) (hRR : R < R') (hy : IsBROn P c S R y)
    (hy' : IsBROn P c S R' y') : y + R ≤ y' + R' := by
  by_contra hlt
  push Not at hlt
  set d := R' - R with hd
  have hd0 : 0 < d := by linarith
  have hy'0 : 0 ≤ y' := hS0 hy'.1
  have hm1 : y' + d ∈ S := hS.out hy'.1 hy.1 ⟨by linarith, by linarith⟩
  have hm2 : y - d ∈ S := hS.out hy'.1 hy.1 ⟨by linarith, by linarith⟩
  have i1 := hy.2 _ hm1
  have i2 := hy'.2 _ hm2
  unfold cbrProfit at i1 i2
  rw [show R + (y' + d) = R' + y' by rw [hd]; ring] at i1
  rw [show R' + (y - d) = R + y by rw [hd]; ring] at i2
  have hPlt : P (R + y) < P (R' + y') :=
    hP (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith)
  have hcv := cbr_convex_pair hc hy'0 (x := y' + d) (b := y) (by linarith) (by linarith)
  rw [show y' + y - (y' + d) = y - d by ring] at hcv
  nlinarith [mul_pos (sub_pos.2 hPlt) hd0]

/-- **Exercise 12.C.8(c), consequence** (MWG, p. 431). Along any selection `b` of the
best-response correspondence, `Q₋ⱼ ↦ b(Q₋ⱼ) + Q₋ⱼ` is nondecreasing. -/
theorem exercise_12_C_8c_monotone {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0) {b : ℝ → ℝ}
    (hb : ∀ R, 0 ≤ R → IsBROn P c S R (b R)) : MonotoneOn (fun R => b R + R) (Ici 0) := by
  intro R hR R' hR' hle
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · exact exercise_12_C_8c hP hc hS hS0 hR h (hb R hR) (hb R' hR')

/-- **Exercise 12.C.8(c), "`b` can jump only upward"** (MWG, p. 431). If a selection `b` of the
best-response correspondence has a left limit `L` and a right limit `U` at `R₀ > 0`, then
`L ≤ U`. -/
theorem exercise_12_C_8c_jump {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0) {b : ℝ → ℝ}
    (hb : ∀ R, 0 ≤ R → IsBROn P c S R (b R)) {R₀ L U : ℝ} (hR₀ : 0 < R₀)
    (hL : Tendsto b (𝓝[<] R₀) (𝓝 L)) (hU : Tendsto b (𝓝[>] R₀) (𝓝 U)) : L ≤ U := by
  have hmono := exercise_12_C_8c_monotone hP hc hS hS0 hb
  have hgL : Tendsto (fun R => b R + R) (𝓝[<] R₀) (𝓝 (L + R₀)) :=
    hL.add (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have hgU : Tendsto (fun R => b R + R) (𝓝[>] R₀) (𝓝 (U + R₀)) :=
    hU.add (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have hstep : ∀ R', R₀ < R' → L + R₀ ≤ b R' + R' := by
    intro R' hR'
    refine le_of_tendsto hgL ?_
    filter_upwards [Ioo_mem_nhdsLT hR₀] with R hR
    exact hmono (mem_Ici.2 hR.1.le) (mem_Ici.2 (by linarith)) (by linarith [hR.2])
  have : L + R₀ ≤ U + R₀ := by
    refine ge_of_tendsto hgU ?_
    filter_upwards [self_mem_nhdsWithin] with R' hR'
    exact hstep R' hR'
  linarith

/-- **Exercise 12.C.8(c), "`b'(Q₋ⱼ) ≥ −1` whenever this derivative is defined"** (MWG,
p. 431), for a selection `b` of the best-response correspondence and `Q₋ⱼ > 0`. -/
theorem exercise_12_C_8c_deriv {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0) {b : ℝ → ℝ}
    (hb : ∀ R, 0 ≤ R → IsBROn P c S R (b R)) {R₀ b' : ℝ} (hR₀ : 0 < R₀)
    (hd : HasDerivAt b b' R₀) : -1 ≤ b' := by
  have hmono := exercise_12_C_8c_monotone hP hc hS hS0 hb
  have hg : HasDerivAt (fun R => b R + R) (b' + 1) R₀ := hd.add (hasDerivAt_id R₀)
  have hsl := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
    (nhdsWithin_mono R₀ (s := Ioi R₀) (fun x hx => ne_of_gt (mem_Ioi.1 hx)))
  have : 0 ≤ b' + 1 := by
    refine ge_of_tendsto hsl ?_
    filter_upwards [self_mem_nhdsWithin] with R hR
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.2 (hmono (mem_Ici.2 hR₀.le) (mem_Ici.2 (by linarith [hR.out]))
      (le_of_lt hR))) (by linarith [hR.out])
  linarith

/-- **Exercise 12.C.8(d), the printed claim is false** (MWG, p. 431). With the strictly
decreasing, continuous, positive inverse demand `P(Q) = 1 + 1/(1 + Q)` and the increasing linear
(hence convex) cost `c(q) = q`, no output `q ≥ 0` is a best response to any `Q₋ⱼ ≥ 0` (profit
`q/(1 + Q₋ⱼ + q)` increases without attaining its supremum), so for every nonempty set of firms
there is no pure-strategy Nash equilibrium at all, symmetric or not. -/
theorem exercise_12_C_8d_counterexample :
    StrictAntiOn (fun Q : ℝ => 1 + 1 / (1 + Q)) (Ici 0) ∧ Continuous (fun y : ℝ => y) ∧
    StrictMono (fun y : ℝ => y) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y) ∧
    (∀ R y : ℝ, 0 ≤ R → ¬ IsBROn (fun Q => 1 + 1 / (1 + Q)) (fun y => y) (Ici 0) R y) ∧
    ∀ (E : Finset ι) (q : ι → ℝ), E.Nonempty →
      ¬ IsCournotEqm (fun Q => 1 + 1 / (1 + Q)) (fun y => y) (Ici 0) E q := by
  have hnobr : ∀ R y : ℝ, 0 ≤ R →
      ¬ IsBROn (fun Q => 1 + 1 / (1 + Q)) (fun y => y) (Ici 0) R y := by
    intro R y hR ⟨hy, hmax⟩
    have hy0 : 0 ≤ y := hy
    have h := hmax (y + 1) (mem_Ici.2 (by linarith))
    unfold cbrProfit at h
    have e : ∀ z : ℝ, 0 ≤ z → (1 + 1 / (1 + (R + z))) * z - z = z / (1 + (R + z)) := by
      intro z hz
      field_simp
      ring
    rw [e y hy0, e (y + 1) (by linarith), div_le_div_iff₀ (by linarith) (by linarith)] at h
    nlinarith
  refine ⟨fun x hx y hy hxy => ?_, continuous_id, strictMono_id, convexOn_id (convex_Ici 0),
    hnobr, fun E q ⟨j, hj⟩ h => ?_⟩
  · have hx0 : (0 : ℝ) ≤ x := hx
    have : 1 / (1 + y) < 1 / (1 + x) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    simp only
    linarith
  · have hR : 0 ≤ ∑ k ∈ E.erase j, q k :=
      Finset.sum_nonneg fun k hk => (h k (Finset.mem_of_mem_erase hk)).1
    exact hnobr _ _ hR (h j hj)

/-- Best responses exist on a compact interval `[0, B]` when `P` and `c` are continuous. -/
theorem cbr_exists_Icc {P c : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hPc : Continuous P)
    (hcc : Continuous c) (R : ℝ) : ∃ y, IsBROn P c (Icc 0 B) R y := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hB)
    (f := fun y => cbrProfit P c R y) (by unfold cbrProfit; fun_prop)
  exact ⟨y, hy, fun y' hy' => hmax hy'⟩

/-- The fixed-point step of Exercise 12.C.8(d): for `m ≥ 0` (the number `J − 1` of rivals) there
is `x ∈ [0, B]` with `x ∈ b(mx)`, where `b` is the best response on `[0, B]`. Proof: the largest
`x` with some best response to `mx` above `x` works, by part (c) and compactness. -/
theorem cbr_symmetric_fixed_point {P c : ℝ → ℝ} {B m : ℝ} (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hPc : Continuous P) (hcc : Continuous c) (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) : ∃ x ∈ Icc 0 B, IsBROn P c (Icc 0 B) (m * x) x := by
  have hS : (Icc (0 : ℝ) B).OrdConnected := ordConnected_Icc
  have hS0 : Icc (0 : ℝ) B ⊆ Ici 0 := Icc_subset_Ici_self
  have hex := cbr_exists_Icc hB hPc hcc
  set T : Set ℝ := {x | x ∈ Icc (0 : ℝ) B ∧ ∃ y, IsBROn P c (Icc 0 B) (m * x) y ∧ x ≤ y}
    with hT
  have hT0 : (0 : ℝ) ∈ T := by
    obtain ⟨y, hy⟩ := hex (m * 0)
    exact ⟨⟨le_rfl, hB⟩, y, hy, hy.1.1⟩
  have hTb : BddAbove T := ⟨B, fun x hx => hx.1.2⟩
  set s := sSup T with hs
  have hs0 : 0 ≤ s := le_csSup hTb hT0
  obtain ⟨u, -, hu, huT⟩ := exists_seq_tendsto_sSup ⟨0, hT0⟩ hTb
  choose y hy hxy using fun n => (huT n).2
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := isCompact_Icc.tendsto_subseq (fun n => (hy n).1)
  have hus : Tendsto (u ∘ φ) atTop (𝓝 s) := hu.comp hφ.tendsto_atTop
  have hsz : s ≤ z := le_of_tendsto_of_tendsto' hus hzlim (fun n => hxy (φ n))
  have hcont : Continuous (fun pr : ℝ × ℝ => cbrProfit P c (m * pr.1) pr.2) := by
    unfold cbrProfit; fun_prop
  have hzbr : IsBROn P c (Icc 0 B) (m * s) z := by
    refine ⟨hz, fun y' hy' => ?_⟩
    have h1 : Tendsto (fun n => cbrProfit P c (m * (u ∘ φ) n) y') atTop
        (𝓝 (cbrProfit P c (m * s) y')) :=
      (hcont.tendsto (s, y')).comp (hus.prodMk_nhds tendsto_const_nhds)
    have h2 : Tendsto (fun n => cbrProfit P c (m * (u ∘ φ) n) ((y ∘ φ) n)) atTop
        (𝓝 (cbrProfit P c (m * s) z)) :=
      (hcont.tendsto (s, z)).comp (hus.prodMk_nhds hzlim)
    exact le_of_tendsto_of_tendsto' h1 h2 (fun n => (hy (φ n)).2 y' hy')
  rcases eq_or_lt_of_le hsz with h | h
  · exact ⟨s, ⟨hs0, h ▸ hz.2⟩, h ▸ hzbr⟩
  · exfalso
    rcases eq_or_lt_of_le hm with hm0 | hm0
    · have hzT : z ∈ T := by
        refine ⟨hz, z, ?_, le_rfl⟩
        rw [← hm0, zero_mul] at hzbr ⊢
        exact hzbr
      linarith [le_csSup hTb hzT]
    · have hsB : s < B := lt_of_lt_of_le h hz.2
      set w := (z + m * s) / (1 + m) with hw
      have hsw : s < w := by rw [hw, lt_div_iff₀ (by linarith)]; nlinarith
      set x := min B ((s + w) / 2) with hx
      have hsx : s < x := lt_min hsB (by linarith)
      have hxw : x < w := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hxw' : x * (1 + m) < z + m * s := by
        rw [hw, lt_div_iff₀ (by linarith)] at hxw; exact hxw
      obtain ⟨y', hy'⟩ := hex (m * x)
      have key := exercise_12_C_8c hP hc hS hS0 (by positivity) (by nlinarith) hzbr hy'
      have hxT : x ∈ T := ⟨⟨by linarith, min_le_left _ _⟩, y', hy', by nlinarith⟩
      linarith [le_csSup hTb hxT]

/-- **Exercise 12.C.8(d), corrected** (MWG, p. 431). With quantities in a compact interval
`[0, B]`, `P` continuous and strictly decreasing on `[0, ∞)` and `c` continuous and convex, the
`J`-firm Cournot game among the firms of any finite `E` has a symmetric pure-strategy Nash
equilibrium. -/
theorem exercise_12_C_8d {P c : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hPc : Continuous P)
    (hcc : Continuous c) (hP : StrictAntiOn P (Ici 0)) (hc : ConvexOn ℝ (Ici 0) c)
    (E : Finset ι) : ∃ x ∈ Icc 0 B, IsCournotGameNE P c (Icc 0 B) E (fun _ => x) := by
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨0, ⟨le_rfl, hB⟩, fun j hj => by simp [hE] at hj⟩
  have h1 : 1 ≤ E.card := Nat.succ_le_of_lt hE.card_pos
  have hcard : (1 : ℝ) ≤ E.card := by exact_mod_cast h1
  obtain ⟨x, hx, hbr⟩ := cbr_symmetric_fixed_point (m := (E.card : ℝ) - 1) hB (by linarith)
    hPc hcc hP hc
  refine ⟨x, hx, (exercise_12_C_8a P c _ E _).2 fun j hj => ?_⟩
  have hsum : ∑ k ∈ E.erase j, (fun _ => x) k = ((E.card : ℝ) - 1) * x := by
    rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul, Nat.cast_sub h1,
      Nat.cast_one]
  rw [hsum]
  exact hbr

/-! ### Instances for parts (c) and (d) -/

/-- The best-response selection `b(R) = max(0, (2 − R)/4)` for `P(Q) = 2 − Q`, `c(q) = q²`. -/
noncomputable def cbrSelLinear (R : ℝ) : ℝ := max 0 ((2 - R) / 4)

/-- **Instance for Exercise 12.C.8(c)** (MWG, p. 431). For `P(Q) = 2 − Q` and `c(q) = q²` all
hypotheses of `exercise_12_C_8c`, `exercise_12_C_8c_jump` and `exercise_12_C_8c_deriv` hold:
`b(R) = max(0, (2 − R)/4)` is a best-response selection, differentiable at `R₀ = 1` with
`b'(1) = −1/4 ≥ −1`, and continuous there. -/
theorem exercise_12_C_8c_instance :
    StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y ^ 2) ∧
    (Ici (0 : ℝ)).OrdConnected ∧
    (∀ R : ℝ, 0 ≤ R → IsBROn (fun Q => 2 - Q) (fun y => y ^ 2) (Ici 0) R (cbrSelLinear R)) ∧
    HasDerivAt cbrSelLinear (-1 / 4) 1 ∧ Tendsto cbrSelLinear (𝓝[<] 1) (𝓝 (1 / 4)) ∧
    Tendsto cbrSelLinear (𝓝[>] 1) (𝓝 (1 / 4)) := by
  have hcont : Continuous cbrSelLinear := by unfold cbrSelLinear; fun_prop
  have h1 : cbrSelLinear 1 = 1 / 4 := by unfold cbrSelLinear; norm_num
  have hlim : Tendsto cbrSelLinear (𝓝 1) (𝓝 (1 / 4)) := h1 ▸ hcont.tendsto 1
  refine ⟨fun x _ y _ h => by simp only; linarith, convexOn_pow 2, ordConnected_Ici,
    fun R _ => ?_, ?_, hlim.mono_left nhdsWithin_le_nhds, hlim.mono_left nhdsWithin_le_nhds⟩
  · refine ⟨mem_Ici.2 (le_max_left _ _), fun y hy => ?_⟩
    have hy0 : (0 : ℝ) ≤ y := hy
    unfold cbrProfit cbrSelLinear
    rcases le_total R 2 with h | h
    · rw [max_eq_right (by linarith)]
      nlinarith [sq_nonneg (y - (2 - R) / 4)]
    · rw [max_eq_left (by linarith)]
      nlinarith
  · have hd : HasDerivAt (fun R : ℝ => (2 - R) / 4) (-1 / 4) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 2).div_const 4
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)] with R hR
    unfold cbrSelLinear
    rw [max_eq_right (by linarith [hR.out])]

/-- **Instance for Exercise 12.C.8(d)** (MWG, p. 431). With `P(Q) = 2 − Q`, `c(q) = q²` and
quantities in `[0, 1]` every hypothesis of `exercise_12_C_8d` holds, so a symmetric equilibrium
exists for every finite set of firms. -/
theorem exercise_12_C_8d_instance (E : Finset ι) :
    Continuous (fun Q : ℝ => 2 - Q) ∧ Continuous (fun y : ℝ => y ^ 2) ∧
    StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y ^ 2) ∧
    ∃ x ∈ Icc (0 : ℝ) 1,
      IsCournotGameNE (fun Q => 2 - Q) (fun y => y ^ 2) (Icc 0 1) E (fun _ => x) := by
  have hP : StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) := fun x _ y _ h => by simp only; linarith
  exact ⟨by fun_prop, by fun_prop, hP, convexOn_pow 2,
    exercise_12_C_8d zero_le_one (by fun_prop) (by fun_prop) hP (convexOn_pow 2) E⟩

/-! ### Part (e): multiple equilibria -/

/-- The kinked inverse demand of Exercise 12.C.8(e): `P(Q) = 1 + min(2 − Q/2, 9 − 4Q)`
(concave and strictly decreasing, kinked at `Q = 2`). -/
noncomputable def cbrDemandE (Q : ℝ) : ℝ := 1 + min (2 - Q / 2) (9 - 4 * Q)

/-- With demand `cbrDemandE` and cost `c(q) = q`, any `y ∈ [1/4, 2]` is a best response to
`Q₋ⱼ = 2 − y`. -/
theorem cbrDemandE_br {R y : ℝ} (hy1 : 1 / 4 ≤ y) (hy2 : y ≤ 2) (hRy : R + y = 2) :
    IsBROn cbrDemandE (fun y => y) (Ici 0) R y := by
  refine ⟨mem_Ici.2 (by linarith), fun y' hy' => ?_⟩
  have hy'0 : (0 : ℝ) ≤ y' := hy'
  have hval : cbrProfit cbrDemandE (fun y => y) R y = y := by
    unfold cbrProfit cbrDemandE; rw [hRy]; norm_num; ring
  rw [hval]
  unfold cbrProfit cbrDemandE
  have e : (1 + min (2 - (R + y') / 2) (9 - 4 * (R + y'))) * y' - y' =
      min (2 - (R + y') / 2) (9 - 4 * (R + y')) * y' := by ring
  rw [e]
  have hR : R = 2 - y := by linarith
  subst hR
  rcases le_total y' y with h | h
  · have := mul_le_mul_of_nonneg_right
      (min_le_left (2 - (2 - y + y') / 2) (9 - 4 * (2 - y + y'))) hy'0
    nlinarith [mul_nonneg (sub_nonneg.2 h) (show (0 : ℝ) ≤ 1 - y' / 2 by linarith)]
  · have := mul_le_mul_of_nonneg_right
      (min_le_right (2 - (2 - y + y') / 2) (9 - 4 * (2 - y + y'))) hy'0
    nlinarith [mul_nonneg (sub_nonneg.2 h) (show (0 : ℝ) ≤ 4 * y' - 1 by linarith)]

/-- **Exercise 12.C.8(e)** (MWG, p. 431). Multiple equilibria are possible: with the strictly
decreasing inverse demand `cbrDemandE` and the increasing convex cost `c(q) = q`, every profile
`(t, 2 − t)` with `t ∈ [1/2, 3/2]` is a pure-strategy Nash equilibrium of the duopoly; e.g.
`(1, 1)` and `(1/2, 3/2)`. -/
theorem exercise_12_C_8e :
    StrictAnti cbrDemandE ∧ StrictMono (fun y : ℝ => y) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y) ∧
    (∀ t ∈ Icc (1 / 2 : ℝ) (3 / 2), IsCournotGameNE cbrDemandE (fun y => y) (Ici 0)
      (Finset.univ : Finset (Fin 2)) ![t, 2 - t]) ∧ (![1, 1] : Fin 2 → ℝ) ≠ ![1 / 2, 3 / 2] := by
  refine ⟨fun x y hxy => ?_, strictMono_id, convexOn_id (convex_Ici 0), fun t ht => ?_, ?_⟩
  · unfold cbrDemandE
    have : min (2 - y / 2) (9 - 4 * y) < min (2 - x / 2) (9 - 4 * x) :=
      lt_min (min_lt_of_left_lt (by linarith)) (min_lt_of_right_lt (by linarith))
    linarith
  · rw [exercise_12_C_8a]
    intro j _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), Fin.sum_univ_two]
    fin_cases j
    · exact cbrDemandE_br (by simp; linarith [ht.1]) (by simp; linarith [ht.2]) (by simp)
    · exact cbrDemandE_br (by simp; linarith [ht.2]) (by simp; linarith [ht.1]) (by simp)
  · intro h
    have := congrFun h 0
    norm_num at this

/-! ### Part (f): uniqueness -/

/-- First-order conditions at a best response on `[0, ∞)`: `P(Q) + qP'(Q) ≤ c'(q)`, with
equality when `q > 0`, where `Q = Q₋ⱼ + q`. -/
theorem cbr_foc {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hc : ∀ y, HasDerivAt c (c' y) y) {R y : ℝ} (hy : IsBROn P c (Ici 0) R y) :
    P (R + y) + y * P' (R + y) ≤ c' y ∧ (0 < y → P (R + y) + y * P' (R + y) = c' y) := by
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hg : HasDerivAt (fun t => cbrProfit P c R t) (P (R + y) + y * P' (R + y) - c' y) y := by
    have h1 : HasDerivAt (fun t => P (R + t)) (P' (R + y)) y := (hP (R + y)).comp_const_add R y
    have := (h1.mul (hasDerivAt_id' y)).sub (hc y)
    unfold cbrProfit
    convert this using 1
    ring
  constructor
  · have hsl := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
      (nhdsWithin_mono y (s := Ioi y) (fun x hx => ne_of_gt (mem_Ioi.1 hx)))
    have : P (R + y) + y * P' (R + y) - c' y ≤ 0 := by
      refine le_of_tendsto hsl ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field]
      have ht' : y < t := ht
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hy.2 t (mem_Ici.2 (by linarith))))
        (by linarith)
    linarith
  · intro hpos
    have hmax : IsLocalMax (fun t => cbrProfit P c R t) y :=
      Filter.eventually_of_mem (Ioi_mem_nhds hpos)
        (fun t ht => hy.2 t (mem_Ici.2 (le_of_lt (mem_Ioi.1 ht))))
    have := hmax.hasDerivAt_eq_zero hg
    linarith

/-- First-order conditions at a Cournot equilibrium, in terms of total output `Q = ∑ q_k`. -/
theorem cournotEqm_foc {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hc : ∀ y, HasDerivAt c (c' y) y) {E : Finset ι} {q : ι → ℝ}
    (hq : IsCournotEqm P c (Ici 0) E q) {j : ι} (hj : j ∈ E) :
    0 ≤ q j ∧ P (∑ k ∈ E, q k) + q j * P' (∑ k ∈ E, q k) ≤ c' (q j) ∧
      (0 < q j → P (∑ k ∈ E, q k) + q j * P' (∑ k ∈ E, q k) = c' (q j)) := by
  have h := cbr_foc hP hc (hq j hj)
  rw [Finset.sum_erase_add E q hj] at h
  exact ⟨(hq j hj).1, h⟩

/-- **Exercise 12.C.8(f)** (MWG, p. 431). Sufficient conditions for the symmetric equilibrium
to be the only pure-strategy equilibrium. If `P` is differentiable with `P' < 0` and `c` is
differentiable with nondecreasing `c'` (convex), every pure-strategy equilibrium is symmetric;
if moreover each firm's marginal revenue `P(Q) + qP'(Q)` is nonincreasing in total output `Q`
(e.g. `P` concave), any two equilibria coincide. -/
theorem exercise_12_C_8f {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hP' : ∀ Q, 0 ≤ Q → P' Q < 0) (hc : ∀ y, HasDerivAt c (c' y) y)
    (hc' : MonotoneOn c' (Ici 0)) (E : Finset ι) :
    (∀ q, IsCournotEqm P c (Ici 0) E q → ∀ i ∈ E, ∀ j ∈ E, q i = q j) ∧
    ((∀ y, 0 ≤ y → AntitoneOn (fun Q => P Q + y * P' Q) (Ici 0)) →
      ∀ q q', IsCournotEqm P c (Ici 0) E q → IsCournotEqm P c (Ici 0) E q' →
        ∀ i ∈ E, q i = q' i) := by
  have hQ0 : ∀ q, IsCournotEqm P c (Ici 0) E q → 0 ≤ ∑ k ∈ E, q k :=
    fun q hq => Finset.sum_nonneg fun k hk => (hq k hk).1
  have part1 : ∀ q, IsCournotEqm P c (Ici 0) E q → ∀ i ∈ E, ∀ j ∈ E, ¬ q i < q j := by
    intro q hq i hi j hj hlt
    obtain ⟨hi0, hfi, -⟩ := cournotEqm_foc hP hc hq hi
    obtain ⟨-, -, hfj⟩ := cournotEqm_foc hP hc hq hj
    have hneg := hP' _ (hQ0 q hq)
    have e := hfj (by linarith)
    have hc'le := hc' (mem_Ici.2 hi0) (mem_Ici.2 (by linarith)) hlt.le
    nlinarith [mul_lt_mul_of_neg_right hlt hneg]
  have hsym : ∀ q, IsCournotEqm P c (Ici 0) E q → ∀ i ∈ E, ∀ j ∈ E, q i = q j :=
    fun q hq i hi j hj => le_antisymm (not_lt.1 (part1 q hq j hj i hi))
      (not_lt.1 (part1 q hq i hi j hj))
  refine ⟨hsym, fun H => ?_⟩
  have part2 : ∀ q q', IsCournotEqm P c (Ici 0) E q → IsCournotEqm P c (Ici 0) E q' →
      ∀ i ∈ E, ¬ q i < q' i := by
    intro q q' hq hq' i hi hlt
    have hQQ : ∑ k ∈ E, q k ≤ ∑ k ∈ E, q' k := Finset.sum_le_sum fun k hk => by
      rw [hsym q hq k hk i hi, hsym q' hq' k hk i hi]; exact hlt.le
    obtain ⟨hi0, hfi, -⟩ := cournotEqm_foc hP hc hq hi
    obtain ⟨-, -, hfi'⟩ := cournotEqm_foc hP hc hq' hi
    have e' := hfi' (by linarith)
    have hneg := hP' _ (hQ0 q' hq')
    have hanti := H (q i) hi0 (mem_Ici.2 (hQ0 q hq)) (mem_Ici.2 (hQ0 q' hq')) hQQ
    simp only at hanti
    have hc'le := hc' (mem_Ici.2 hi0) (mem_Ici.2 (by linarith)) hlt.le
    nlinarith [mul_lt_mul_of_neg_right hlt hneg]
  intro q q' hq hq' i hi
  exact le_antisymm (not_lt.1 (part2 q' q hq' hq i hi)) (not_lt.1 (part2 q q' hq hq' i hi))

/-- **Instance for Exercise 12.C.8(f)** (MWG, p. 431). Linear demand `P(Q) = a − Q` and
quadratic cost `c(q) = q²/2` satisfy every hypothesis of `exercise_12_C_8f` (including the
marginal-revenue condition), so any two Cournot equilibria coincide and each is symmetric. -/
theorem exercise_12_C_8f_instance (a : ℝ) (E : Finset ι) :
    (∀ q, IsCournotEqm (fun Q => a - Q) (fun y => y ^ 2 / 2) (Ici 0) E q →
      ∀ i ∈ E, ∀ j ∈ E, q i = q j) ∧
    ∀ q q', IsCournotEqm (fun Q => a - Q) (fun y => y ^ 2 / 2) (Ici 0) E q →
      IsCournotEqm (fun Q => a - Q) (fun y => y ^ 2 / 2) (Ici 0) E q' → ∀ i ∈ E, q i = q' i := by
  have hP : ∀ Q : ℝ, HasDerivAt (fun Q : ℝ => a - Q) ((fun _ => (-1 : ℝ)) Q) Q := fun Q => by
    simpa using (hasDerivAt_id Q).const_sub a
  have hc : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((fun y => y) y) y := fun y => by
    convert (hasDerivAt_pow 2 y).div_const 2 using 1
    norm_num
  have h := exercise_12_C_8f hP (fun _ _ => by norm_num) hc (fun x _ y _ h => h) E
  refine ⟨h.1, h.2 fun y _ Q _ Q' _ hQQ => ?_⟩
  simp only
  linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The competitive limit

MWG, Section 12.F, pp. 411-413 (Proposition 12.F.1, its small-type argument and footnote 29),
and Exercise 12.F.1, p. 435.

Market demand is `αx(p)`; with `p(·)` the inverse of `x(·)` the inverse demand at market size
`α` is `p_α(Q) = p(Q/α)` (`sizedDemand`). Potential firms are indexed by `ℕ` (infinitely many);
each has cost `c` and entry cost `K`. `c̄ = min_{q>0} (K + c(q))/q` is minimum average cost,
reached at the efficient scale `q̄ > 0`, and `X = x(c̄) > 0` (so `p(X) = c̄`).

**The SPNE.** In the two-stage Cournot entry game a pure strategy profile consists of stage-1
entry decisions, which we record as the finite set `E` of entrants, and stage-2 output rules: for
every set `F` of entrants (every stage-1 history), the output profile `σ F`. Subgame perfection
requires (i) `σ F` to be a Cournot equilibrium among the firms of `F`, for every `F` (every
stage-2 subgame), and (ii) no firm to gain by changing its stage-1 decision given the continuation
`σ`: an entrant earns at least `0` net of `K`, and an outsider `j` who entered would earn at most
`0` in the continuation equilibrium `σ (insert j E)` that the profile specifies. (A firm changing
both decisions gains nothing more, since `σ F` is an equilibrium of each subgame.) This is
`IsCournotEntrySPNE`. Only the subgames after `E` and after single-firm entry deviations are
used in the proof.

* `entry_incumbents_no_expand`: the small-type paragraph of p. 413. If best responses are unique
  and weakly decreasing, the incumbents' aggregate output cannot rise when a firm enters (via
  `exercise_12_C_8c`).
* `entry_step_ii`: step (ii) of the proof, in the form: if an entrant producing `q₀` at average
  output `s₀ = Q/α` would earn more than `K`, then `Q_α + q₀ ≥ αs₀`.
* `competitive_limit`: every SPNE price tends to `c̄` when `c̄` is only an infimum of average
  cost; `proposition_12_F_1` (minimum attained at `q̄`) and `footnote_12_29` (constant marginal
  cost `c`, `c̄ = c` the limit of average cost) are corollaries.
* Exercise 12.F.1 as printed is false: `exercise_12_F_1_counterexample`,
  `exercise_12_F_1_false` (inverse demand `1 + e^{−(s+1)²}`, cost `q²`: for every `α ≥ 4` best
  responses are unique but increase between `Q₋ⱼ = 2α²` and `2α² + 1`). Corrected:
  `exercise_12_F_1_core`, `exercise_12_F_1` (`p'' ≤ L(−p')`, best responses bounded by `B`,
  `α > LB`).
* `entry_spne_instance`: an explicit SPNE (linear demand, zero cost), so the SPNE hypotheses of
  the lemmas above are satisfiable.
* `proposition_12_F_1_of_exercise_12_F_1`: Proposition 12.F.1 with the decreasing best response
  derived from the Exercise 12.F.1 condition; `proposition_12_F_1_instance` (linear demand,
  quadratic cost) and `footnote_12_29_instance` verify every hypothesis.

Departures: the inverse demand `p` is primitive (continuous at `X`, strictly decreasing on
`[0, ∞)`); the proof uses convexity of `c` only (MWG assume strict convexity); the book's standing
assumption that the best response is unique is part of `BRDecreasing`.
-/

namespace MWG.MarketPower

open Set Filter Topology

/-- Inverse demand at market size `α`: `p_α(Q) = p(Q/α)` (MWG, p. 412). -/
noncomputable def sizedDemand (p : ℝ → ℝ) (α : ℝ) : ℝ → ℝ := fun Q => p (Q / α)

/-- `p_α` inherits strict decrease on `[0, ∞)` from `p` when `α > 0`. -/
theorem sizedDemand_strictAntiOn {p : ℝ → ℝ} (hp : StrictAntiOn p (Ici 0)) {α : ℝ}
    (hα : 0 < α) : StrictAntiOn (sizedDemand p α) (Ici 0) := fun _ hx _ hy h =>
  hp (mem_Ici.2 (div_nonneg hx hα.le)) (mem_Ici.2 (div_nonneg hy hα.le))
    (div_lt_div_of_pos_right h hα)

/-- Net profit of firm `j` among the entrants `E` at the output profile `q`, market size `α`:
`p_α(∑_{k∈E} q_k)qⱼ − c(qⱼ) − K`. -/
noncomputable def entryNetProfit (p c : ℝ → ℝ) (K α : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  p ((∑ k ∈ E, q k) / α) * q j - c (q j) - K

/-- A pure-strategy subgame perfect Nash equilibrium of the two-stage Cournot entry model with
market size `α` (MWG, p. 412): entrants `E`, stage-2 output rules `σ` (see the module docstring).
-/
def IsCournotEntrySPNE (p c : ℝ → ℝ) (K α : ℝ) (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ) : Prop :=
  (∀ F : Finset ℕ, IsCournotEqm (sizedDemand p α) c (Ici 0) F (σ F)) ∧
  (∀ j ∈ E, 0 ≤ entryNetProfit p c K α E (σ E) j) ∧
  ∀ j ∉ E, entryNetProfit p c K α (insert j E) (σ (insert j E)) j ≤ 0

/-- The best response `b(Q₋ⱼ)` is unique and weakly decreasing on `Q₋ⱼ ≥ 0` (MWG, p. 412 and
step (i) of the proof of Proposition 12.F.1). -/
def BRDecreasing (P c : ℝ → ℝ) : Prop :=
  (∀ R, 0 ≤ R → ∀ y y', IsBROn P c (Ici 0) R y → IsBROn P c (Ici 0) R y' → y = y') ∧
  ∀ R R', 0 ≤ R → R < R' → ∀ y y', IsBROn P c (Ici 0) R y → IsBROn P c (Ici 0) R' y' → y' ≤ y

/-- **Proposition 12.F.1, small-type argument** (MWG, pp. 412-413). If `P` is strictly decreasing,
`c` convex and the best response unique and decreasing, then when firm `j ∉ E` enters, the
aggregate output of the original entrants cannot increase: `Q̃ ≤ Q`. -/
theorem entry_incumbents_no_expand {P c : ℝ → ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hdec : BRDecreasing P c) {E : Finset ℕ} {j : ℕ} (hj : j ∉ E)
    {q q' : ℕ → ℝ} (hq : IsCournotEqm P c (Ici 0) E q)
    (hq' : IsCournotEqm P c (Ici 0) (insert j E) q') : ∑ k ∈ E, q' k ≤ ∑ k ∈ E, q k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk, hkk⟩ := Finset.exists_lt_of_sum_lt hlt
  have hkF : k ∈ insert j E := Finset.mem_insert_of_mem hk
  have hR0 : 0 ≤ ∑ l ∈ E.erase k, q l :=
    Finset.sum_nonneg fun l hl => (hq l (Finset.mem_of_mem_erase hl)).1
  have hR'0 : 0 ≤ ∑ l ∈ (insert j E).erase k, q' l :=
    Finset.sum_nonneg fun l hl => (hq' l (Finset.mem_of_mem_erase hl)).1
  rcases lt_or_ge (∑ l ∈ (insert j E).erase k, q' l) (∑ l ∈ E.erase k, q l) with hlt' | hge
  · have key := exercise_12_C_8c hP hc ordConnected_Ici subset_rfl hR'0 hlt' (hq' k hkF)
      (hq k hk)
    have e1 := Finset.add_sum_erase E q hk
    have e2 := Finset.add_sum_erase _ q' hkF
    rw [Finset.sum_insert hj] at e2
    have hj0 : 0 ≤ q' j := (hq' j (Finset.mem_insert_self j E)).1
    linarith
  · rcases eq_or_lt_of_le hge with heq | hgt
    · have h' := hq' k hkF
      rw [← heq] at h'
      have := hdec.1 _ hR0 (q k) (q' k) (hq k hk) h'
      linarith
    · have := hdec.2 _ _ hR0 hgt (q k) (q' k) (hq k hk) (hq' k hkF)
      linarith

/-- **Proposition 12.F.1, step (ii)** (MWG, p. 412). In any SPNE with market size `α`, if a firm
producing `q₀ > 0` at the average output `s₀` would earn more than its entry cost
(`K + c(q₀) < p(s₀)q₀`), then `Q_α + q₀ ≥ αs₀`. (The book takes `q₀ = q̄`, `s₀ = x(c̄)`.) -/
theorem entry_step_ii {p c : ℝ → ℝ} {K α : ℝ} (hα : 0 < α) (hp : StrictAntiOn p (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hdec : BRDecreasing (sizedDemand p α) c)
    {E : Finset ℕ} {σ : Finset ℕ → ℕ → ℝ} (hE : IsCournotEntrySPNE p c K α E σ)
    {q₀ s₀ : ℝ} (hq₀ : 0 < q₀) (hprof : K + c q₀ < p s₀ * q₀) :
    α * s₀ ≤ ∑ k ∈ E, σ E k + q₀ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset E
  have hNE := hE.1 E
  have hNF := hE.1 (insert j E)
  have hsmall := entry_incumbents_no_expand (sizedDemand_strictAntiOn hp hα) hc hdec hj hNE hNF
  have hQ'0 : 0 ≤ ∑ k ∈ E, σ (insert j E) k :=
    Finset.sum_nonneg fun k hk => (hNF k (Finset.mem_insert_of_mem hk)).1
  have hbr := hNF j (Finset.mem_insert_self j E)
  rw [Finset.erase_insert hj] at hbr
  have hdev := hbr.2 q₀ (mem_Ici.2 hq₀.le)
  have hout := hE.2.2 j hj
  unfold entryNetProfit at hout
  rw [Finset.sum_insert hj] at hout
  unfold cbrProfit sizedDemand at hdev
  have hlt2 : (∑ k ∈ E, σ (insert j E) k + q₀) / α < s₀ := by
    rw [div_lt_iff₀ hα]; linarith
  have hpr1 : p s₀ < p ((∑ k ∈ E, σ (insert j E) k + q₀) / α) :=
    hp (mem_Ici.2 (by positivity)) (mem_Ici.2 (le_trans (by positivity) hlt2.le)) hlt2
  have hpr2 := mul_lt_mul_of_pos_right hpr1 hq₀
  rw [add_comm (σ (insert j E) j)] at hout
  linarith

/-- In any SPNE with positive aggregate output, the price is at least minimum average cost: some
entrant produces `qₖ > 0` and earns `p qₖ ≥ K + c(qₖ) ≥ c̄ qₖ` (MWG, p. 412). -/
theorem entry_price_ge {p c : ℝ → ℝ} {K α cbar : ℝ} {E : Finset ℕ} {σ : Finset ℕ → ℕ → ℝ}
    (hE : IsCournotEntrySPNE p c K α E σ) (hlow : ∀ q, 0 < q → cbar * q ≤ K + c q)
    (hQ : 0 < ∑ k ∈ E, σ E k) : cbar ≤ p ((∑ k ∈ E, σ E k) / α) := by
  obtain ⟨k, hk, hpos⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (by simpa using hQ)
  have h1 := hE.2.1 k hk
  unfold entryNetProfit at h1
  have h2 := hlow _ hpos
  by_contra h
  push Not at h
  nlinarith [mul_lt_mul_of_pos_right h hpos]

/-- **Proposition 12.F.1, general form** (MWG, pp. 412-413, with footnote 29). Let `p` be
strictly decreasing on `[0, ∞)` and continuous at `X > 0` with `p(X) = c̄`, `c` convex, `c̄` the
infimum of average cost (`c̄q ≤ K + c(q)` for `q > 0`, and average cost comes arbitrarily close
to `c̄`), and best responses unique and decreasing for all large `α`. Then for every `ε > 0` there
is `A` such that every SPNE price at every market size `α ≥ A` lies within `ε` of `c̄`, i.e.
`max_{p_α ∈ P_α} |p_α − c̄| → 0`. -/
theorem competitive_limit {p c : ℝ → ℝ} {K cbar X : ℝ} (hp : StrictAntiOn p (Ici 0))
    (hpc : ContinuousAt p X) (hX : 0 < X) (hpX : p X = cbar) (hc : ConvexOn ℝ (Ici 0) c)
    (hlow : ∀ q, 0 < q → cbar * q ≤ K + c q)
    (hinf : ∀ η, 0 < η → ∃ q₀, 0 < q₀ ∧ K + c q₀ < (cbar + η) * q₀)
    (hdec : ∃ A₀, ∀ α, A₀ ≤ α → BRDecreasing (sizedDemand p α) c) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p c K α E σ → |p ((∑ k ∈ E, σ E k) / α) - cbar| < ε := by
  intro ε hε
  obtain ⟨A₀, hA₀⟩ := hdec
  obtain ⟨δ, hδ, hδp⟩ := Metric.continuousAt_iff.1 hpc ε hε
  set d := min δ X with hd
  have hd0 : 0 < d := lt_min hδ hX
  have hdδ : d ≤ δ := min_le_left _ _
  have hdX : d ≤ X := min_le_right _ _
  have hs₀ : cbar < p (X - d / 3) :=
    hpX ▸ hp (mem_Ici.2 (by linarith)) (mem_Ici.2 hX.le) (by linarith)
  obtain ⟨q₀, hq₀, hK⟩ := hinf (p (X - d / 3) - cbar) (by linarith)
  refine ⟨max (max A₀ 1) (3 * q₀ / d), fun α hα E σ hE => ?_⟩
  have hα1 : 1 ≤ α := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hα)
  have hα0 : 0 < α := by linarith
  have hαA : A₀ ≤ α := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hα)
  have hαq : 3 * q₀ / d ≤ α := le_trans (le_max_right _ _) hα
  have hq₀α : q₀ / α ≤ d / 3 := by
    rw [div_le_iff₀ hd0] at hαq
    rw [div_le_iff₀ hα0]; linarith
  have hii := entry_step_ii hα0 hp hc (hA₀ α hαA) hE hq₀
    (show K + c q₀ < p (X - d / 3) * q₀ by linarith)
  set Q := ∑ k ∈ E, σ E k with hQ
  have hQα : X - 2 * d / 3 ≤ Q / α := by
    have h1 : X - d / 3 ≤ (Q + q₀) / α := by rw [le_div_iff₀ hα0]; linarith
    rw [add_div] at h1
    linarith
  have hQpos : 0 < Q := by
    have : 0 < Q / α := by linarith
    exact (div_pos_iff_of_pos_right hα0).1 this
  have hge := entry_price_ge hE hlow hQpos
  rw [abs_lt]
  refine ⟨by linarith, ?_⟩
  rcases le_or_gt X (Q / α) with h | h
  · have := hp.antitoneOn (mem_Ici.2 hX.le) (mem_Ici.2 (hX.le.trans h)) h
    linarith
  · have hdist : dist (Q / α) X < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδp hdist
    rw [Real.dist_eq, abs_lt, hpX] at this
    linarith

/-- **Proposition 12.F.1** (MWG, p. 412). Market demand `αx(p)` with inverse `p` (strictly
decreasing, continuous at `X = x(c̄) > 0`), convex cost `c`, entry cost `K`, minimum average cost
`c̄ = min_{q>0}(K + c(q))/q` attained at the efficient scale `q̄ > 0`, and best responses unique
and weakly decreasing for large `α` (Exercise 12.F.1). Then the price in any SPNE of the
two-stage Cournot entry model converges to `c̄` uniformly: `max_{p_α ∈ P_α} |p_α − c̄| → 0`. -/
theorem proposition_12_F_1 {p c : ℝ → ℝ} {K cbar qbar X : ℝ} (hp : StrictAntiOn p (Ici 0))
    (hpc : ContinuousAt p X) (hX : 0 < X) (hpX : p X = cbar) (hc : ConvexOn ℝ (Ici 0) c)
    (hqbar : 0 < qbar) (hmin : ∀ q, 0 < q → cbar * q ≤ K + c q)
    (hatt : cbar * qbar = K + c qbar)
    (hdec : ∃ A₀, ∀ α, A₀ ≤ α → BRDecreasing (sizedDemand p α) c) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p c K α E σ → |p ((∑ k ∈ E, σ E k) / α) - cbar| < ε :=
  competitive_limit hp hpc hX hpX hc hmin
    (fun η hη => ⟨qbar, hqbar, by nlinarith [mul_pos hη hqbar]⟩) hdec

/-- **Footnote 29** (MWG, p. 413). With constant marginal cost, `c(q) = c₀q` and entry cost
`K ≥ 0` (the cost of Example 12.E.2), average cost `c₀ + K/q` has no minimum, but Proposition
12.F.1 still holds with `c̄ = c₀`, the limit of average cost. -/
theorem footnote_12_29 {p : ℝ → ℝ} {K c₀ X : ℝ} (hK : 0 ≤ K) (hp : StrictAntiOn p (Ici 0))
    (hpc : ContinuousAt p X) (hX : 0 < X) (hpX : p X = c₀)
    (hdec : ∃ A₀, ∀ α, A₀ ≤ α → BRDecreasing (sizedDemand p α) (fun q => c₀ * q)) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p (fun q => c₀ * q) K α E σ →
        |p ((∑ k ∈ E, σ E k) / α) - c₀| < ε := by
  have hlin : ConvexOn ℝ (Ici 0) (fun q : ℝ => c₀ * q) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  refine competitive_limit hp hpc hX hpX hlin (fun q _ => by linarith) (fun η hη => ?_) hdec
  refine ⟨K / η + 1, by positivity, ?_⟩
  have : (c₀ + η) * (K / η + 1) = c₀ * (K / η + 1) + K + η := by field_simp; ring
  linarith

/-! ### Exercise 12.F.1: decreasing best responses -/

/-- **Exercise 12.F.1, core step** (MWG, p. 435). Let `p` be twice differentiable with `p' < 0`
and `p'' ≤ L(−p')` on `[0, ∞)` (`L ≥ 0`). At market size `α > 0`, if `0 ≤ Q₋ⱼ < Q̂₋ⱼ`,
`q ∈ b(Q₋ⱼ)`, `q̂ ∈ b(Q̂₋ⱼ)` and `Lq̂ < α`, then `q̂ ≤ q`: the cross partial
`p'(s)/α + q p''(s)/α²` is negative where `Lq < α`, so profit has strictly decreasing differences
and revealed preference applies. No assumption on `c` is needed. -/
theorem exercise_12_F_1_core {p p' p'' c : ℝ → ℝ} {L α : ℝ} (hp : ∀ s, HasDerivAt p (p' s) s)
    (hp' : ∀ s, HasDerivAt p' (p'' s) s) (hneg : ∀ s, 0 ≤ s → p' s < 0)
    (hL : ∀ s, 0 ≤ s → p'' s ≤ L * -p' s) (hL0 : 0 ≤ L) (hα : 0 < α)
    {R R' y y' : ℝ} (hR : 0 ≤ R) (hRR : R < R')
    (hy : IsBROn (sizedDemand p α) c (Ici 0) R y) (hy' : IsBROn (sizedDemand p α) c (Ici 0) R' y')
    (hLy : L * y' < α) : y' ≤ y := by
  by_contra hlt
  push Not at hlt
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hφ : ∀ r, 0 ≤ r → p' ((r + y') / α) * y' < p' ((r + y) / α) * y := by
    intro r hr
    have hderiv : ∀ t, HasDerivAt (fun t => p' ((r + t) / α) * t)
        (p'' ((r + t) / α) * (1 / α) * t + p' ((r + t) / α)) t := by
      intro t
      have h1 : HasDerivAt (fun t => (r + t) / α) (1 / α) t := by
        simpa using ((hasDerivAt_id' t).const_add r).div_const α
      have h2 : HasDerivAt (fun t => p' ((r + t) / α)) (p'' ((r + t) / α) * (1 / α)) t :=
        (hp' ((r + t) / α)).comp t h1
      convert h2.mul (hasDerivAt_id' t) using 1
      ring
    have hanti : StrictAntiOn (fun t => p' ((r + t) / α) * t) (Icc y y') := by
      apply strictAntiOn_of_deriv_neg (convex_Icc y y')
      · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hderiv t).deriv]
        have ht0 : 0 ≤ t := by linarith [ht.1]
        have hs : 0 ≤ (r + t) / α := div_nonneg (by linarith) hα.le
        have h1 := mul_le_mul_of_nonneg_right (hL _ hs) ht0
        have h2 := hneg _ hs
        have hLt : L * t < α := lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2.le hL0) hLy
        have e : p'' ((r + t) / α) * (1 / α) * t + p' ((r + t) / α) =
            (p'' ((r + t) / α) * t + α * p' ((r + t) / α)) / α := by
          field_simp
        rw [e]
        apply div_neg_of_neg_of_pos _ hα
        nlinarith [mul_neg_of_neg_of_pos h2 (sub_pos.2 hLt)]
    exact hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  set D : ℝ → ℝ := fun r => (p ((r + y') / α) * y' - c y') - (p ((r + y) / α) * y - c y)
    with hD
  have hA : ∀ z r, HasDerivAt (fun r => p ((r + z) / α)) (p' ((r + z) / α) * (1 / α)) r := by
    intro z r
    have h1 : HasDerivAt (fun r => (r + z) / α) (1 / α) r := by
      simpa using ((hasDerivAt_id' r).add_const z).div_const α
    exact (hp _).comp r h1
  have hDd : ∀ r, HasDerivAt D ((p' ((r + y') / α) * y' - p' ((r + y) / α) * y) / α) r := by
    intro r
    have := (((hA y' r).mul_const y').sub_const (c y')).sub (((hA y r).mul_const y).sub_const (c y))
    convert this using 1
    field_simp
  have hDanti : StrictAntiOn D (Icc R R') := by
    apply strictAntiOn_of_deriv_neg (convex_Icc R R')
    · exact fun r _ => (hDd r).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hDd r).deriv]
      exact div_neg_of_neg_of_pos (by linarith [hφ r (by linarith [hr.1])]) hα
  have hlt2 := hDanti ⟨le_rfl, hRR.le⟩ ⟨hRR.le, le_rfl⟩ hRR
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  unfold cbrProfit sizedDemand at h1 h2
  simp only [hD] at hlt2
  linarith

/-- If `p` is nonincreasing on `[0, ∞)` and `c(q) − c(0) > p(0)q` for `q > B`, every best response
(at any market size `α > 0`, rivals' output `R ≥ 0`) is at most `B`. -/
theorem sized_br_le {p c : ℝ → ℝ} {B α R y : ℝ} (hp : AntitoneOn p (Ici 0))
    (hcB : ∀ y, B < y → p 0 * y < c y - c 0) (hα : 0 < α) (hR : 0 ≤ R)
    (hy : IsBROn (sizedDemand p α) c (Ici 0) R y) : y ≤ B := by
  by_contra h
  push Not at h
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have h0 := hy.2 0 (mem_Ici.2 le_rfl)
  unfold cbrProfit sizedDemand at h0
  have hpy : p ((R + y) / α) ≤ p 0 :=
    hp (mem_Ici.2 le_rfl) (mem_Ici.2 (div_nonneg (by linarith) hα.le))
      (div_nonneg (by linarith) hα.le)
  have := mul_le_mul_of_nonneg_right hpy hy0
  have := hcB y h
  simp only [mul_zero, zero_sub] at h0
  linarith

/-- **Exercise 12.F.1** (MWG, p. 435), under a sufficient condition. Suppose `p` is twice
differentiable with `p' < 0` and `p'' ≤ L(−p')` on `[0, ∞)` (`L ≥ 0`), and costs grow fast enough
that best responses are bounded: `c(q) − c(0) > p(0)q` for `q > B`. Then for every market size
`α > LB` the best-response correspondence is weakly decreasing: `0 ≤ Q₋ⱼ < Q̂₋ⱼ`, `q ∈ b(Q₋ⱼ)`,
`q̂ ∈ b(Q̂₋ⱼ)` imply `q̂ ≤ q`. -/
theorem exercise_12_F_1 {p p' p'' c : ℝ → ℝ} {L B α : ℝ} (hp : ∀ s, HasDerivAt p (p' s) s)
    (hp' : ∀ s, HasDerivAt p' (p'' s) s) (hneg : ∀ s, 0 ≤ s → p' s < 0)
    (hL : ∀ s, 0 ≤ s → p'' s ≤ L * -p' s) (hL0 : 0 ≤ L)
    (hcB : ∀ y, B < y → p 0 * y < c y - c 0) (hα : 0 < α) (hαL : L * B < α) :
    ∀ R R', 0 ≤ R → R < R' → ∀ y y', IsBROn (sizedDemand p α) c (Ici 0) R y →
      IsBROn (sizedDemand p α) c (Ici 0) R' y' → y' ≤ y := by
  have hpanti : StrictAntiOn p (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact fun s _ => (hp s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hp s).deriv]
      exact hneg s (le_of_lt hs)
  intro R R' hR hRR y y' hy hy'
  have hyB := sized_br_le hpanti.antitoneOn hcB hα (by linarith) hy'
  exact exercise_12_F_1_core hp hp' hneg hL hL0 hα hR hRR hy hy'
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hyB hL0) hαL)

/-- **Proposition 12.F.1 from Exercise 12.F.1** (MWG, pp. 412 and 435). Proposition 12.F.1 with
the decreasing best response derived from the sufficient condition of `exercise_12_F_1`, plus the
book's standing assumption that best responses are unique. -/
theorem proposition_12_F_1_of_exercise_12_F_1 {p p' p'' c : ℝ → ℝ} {K cbar qbar X L B : ℝ}
    (hp : ∀ s, HasDerivAt p (p' s) s) (hp' : ∀ s, HasDerivAt p' (p'' s) s)
    (hneg : ∀ s, 0 ≤ s → p' s < 0) (hL : ∀ s, 0 ≤ s → p'' s ≤ L * -p' s) (hL0 : 0 ≤ L)
    (hB : 0 ≤ B) (hcB : ∀ y, B < y → p 0 * y < c y - c 0)
    (huniq : ∀ α, 0 < α → ∀ R, 0 ≤ R → ∀ y y', IsBROn (sizedDemand p α) c (Ici 0) R y →
      IsBROn (sizedDemand p α) c (Ici 0) R y' → y = y')
    (hX : 0 < X) (hpX : p X = cbar) (hc : ConvexOn ℝ (Ici 0) c) (hqbar : 0 < qbar)
    (hmin : ∀ q, 0 < q → cbar * q ≤ K + c q) (hatt : cbar * qbar = K + c qbar) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p c K α E σ → |p ((∑ k ∈ E, σ E k) / α) - cbar| < ε := by
  have hpanti : StrictAntiOn p (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact fun s _ => (hp s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hp s).deriv]
      exact hneg s (le_of_lt hs)
  refine proposition_12_F_1 hpanti (hp X).continuousAt hX hpX hc hqbar hmin hatt
    ⟨L * B + 1, fun α hα => ?_⟩
  have hLB : 0 ≤ L * B := mul_nonneg hL0 hB
  have hα0 : 0 < α := by linarith
  exact ⟨huniq α hα0, exercise_12_F_1 hp hp' hneg hL hL0 hcB hα0 (by linarith)⟩

/-! ### Exercise 12.F.1 as printed is false -/

/-- The inverse demand of the counterexample to Exercise 12.F.1: `p(s) = 1 + e^{−(s+1)²}`. -/
noncomputable def gaussDemand (s : ℝ) : ℝ := 1 + Real.exp (-(s + 1) ^ 2)

/-- `p'(s) = −2(s + 1)e^{−(s+1)²}`. -/
noncomputable def gaussDemand' (s : ℝ) : ℝ := -2 * (s + 1) * Real.exp (-(s + 1) ^ 2)

/-- `p''(s) = (4(s + 1)² − 2)e^{−(s+1)²}`. -/
noncomputable def gaussDemand'' (s : ℝ) : ℝ := (4 * (s + 1) ^ 2 - 2) * Real.exp (-(s + 1) ^ 2)

/-- `p'` is the derivative of `gaussDemand`. -/
theorem gaussDemand_hasDerivAt (s : ℝ) : HasDerivAt gaussDemand (gaussDemand' s) s := by
  have h : HasDerivAt (fun s : ℝ => -(s + 1) ^ 2) (-(2 * (s + 1))) s := by
    convert (((hasDerivAt_id' s).add_const 1).pow 2).neg using 1
    norm_num
  unfold gaussDemand gaussDemand'
  convert h.exp.const_add 1 using 1
  ring

/-- `p''` is the derivative of `gaussDemand'`. -/
theorem gaussDemand'_hasDerivAt (s : ℝ) : HasDerivAt gaussDemand' (gaussDemand'' s) s := by
  have h : HasDerivAt (fun s : ℝ => -(s + 1) ^ 2) (-(2 * (s + 1))) s := by
    convert (((hasDerivAt_id' s).add_const 1).pow 2).neg using 1
    norm_num
  have h2 : HasDerivAt (fun s : ℝ => -2 * (s + 1)) (-2) s := by
    convert ((hasDerivAt_id' s).add_const 1).const_mul (-2) using 1
    ring
  unfold gaussDemand' gaussDemand''
  convert h2.mul h.exp using 1
  ring

/-- Bounds on `[0, ∞)`: `1 < p ≤ 2`, `−1 ≤ p' < 0`, `p'' < 4`. -/
theorem gaussDemand_bounds {s : ℝ} (hs : 0 ≤ s) :
    1 < gaussDemand s ∧ gaussDemand s ≤ 2 ∧ gaussDemand' s < 0 ∧ -1 ≤ gaussDemand' s ∧
      gaussDemand'' s < 4 := by
  unfold gaussDemand gaussDemand' gaussDemand''
  set u := s + 1 with hu
  have hu1 : 1 ≤ u := by linarith
  set E := Real.exp (-u ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hEu : E * (u ^ 2 + 1) ≤ 1 := by
    have h1 := Real.add_one_le_exp (u ^ 2)
    have h2 : E * Real.exp (u ^ 2) = 1 := by rw [hE, ← Real.exp_add]; simp
    nlinarith
  refine ⟨by linarith, by linarith, by nlinarith, ?_, ?_⟩
  · nlinarith [sq_nonneg (u - 1)]
  · nlinarith

/-- The model of the counterexample satisfies the Section 12.F assumptions: `p` is differentiable
with `p' < 0` on `[0, ∞)` (so `x = p⁻¹` is differentiable with `x' < 0`) and `c(q) = q²` is
strictly convex. -/
theorem gaussDemand_model :
    (∀ s, HasDerivAt gaussDemand (gaussDemand' s) s) ∧ (∀ s, 0 ≤ s → gaussDemand' s < 0) ∧
    StrictConvexOn ℝ (Ici 0) (fun q : ℝ => q ^ 2) :=
  ⟨gaussDemand_hasDerivAt, fun _ hs => (gaussDemand_bounds hs).2.2.1, strictConvexOn_pow le_rfl⟩

/-- The first-order expression `F(R, y) = p(s) + y p'(s)/α − 2y`, `s = (R + y)/α`, for the
counterexample (`c(q) = q²`). -/
noncomputable def gaussFOC (α R y : ℝ) : ℝ :=
  gaussDemand ((R + y) / α) + y * (gaussDemand' ((R + y) / α) * (1 / α)) - 2 * y

/-- At a best response, `F(R, y) = 0` and `3/8 ≤ y ≤ 1` (for `α ≥ 4`). -/
theorem gauss_br_foc {α R y : ℝ} (hα : 4 ≤ α) (hR : 0 ≤ R)
    (hy : IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y) :
    gaussFOC α R y = 0 ∧ 3 / 8 ≤ y ∧ y ≤ 1 := by
  have hα0 : 0 < α := by linarith
  have hP : ∀ Q, HasDerivAt (sizedDemand gaussDemand α)
      ((fun Q => gaussDemand' (Q / α) * (1 / α)) Q) Q := by
    intro Q
    have h1 : HasDerivAt (fun Q : ℝ => Q / α) (1 / α) Q := by
      simpa using (hasDerivAt_id' Q).div_const α
    exact (gaussDemand_hasDerivAt (Q / α)).comp Q h1
  have hc : ∀ y : ℝ, HasDerivAt (fun q : ℝ => q ^ 2) ((fun q => 2 * q) y) y := fun y => by
    simpa using hasDerivAt_pow 2 y
  have hfoc := cbr_foc hP hc hy
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hs : 0 ≤ (R + y) / α := div_nonneg (by linarith) hα0.le
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ := gaussDemand_bounds hs
  unfold sizedDemand at hfoc
  have hpos : 0 < y := by
    rcases eq_or_lt_of_le hy0 with h | h
    · subst h
      simp only [zero_mul, add_zero, mul_zero] at hfoc hb1
      linarith [hfoc.1]
    · exact h
  have hF := hfoc.2 hpos
  have hF' : gaussFOC α R y = 0 := by unfold gaussFOC; linarith
  have hinv : 0 < 1 / α := by positivity
  have hinv4 : 1 / α ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hα
  have hy1 : y ≤ 1 := by nlinarith [mul_pos hpos hinv]
  refine ⟨hF', ?_, hy1⟩
  nlinarith [mul_le_mul_of_nonneg_left hb4 (mul_nonneg hy0 hinv.le)]

/-- `F(R, ·)` is strictly decreasing on `[0, 1]` (for `α ≥ 4`, `R ≥ 0`). -/
theorem gaussFOC_anti {α R : ℝ} (hα : 4 ≤ α) (hR : 0 ≤ R) :
    StrictAntiOn (gaussFOC α R) (Icc 0 1) := by
  have hα0 : 0 < α := by linarith
  have h1 : ∀ y, HasDerivAt (fun y : ℝ => (R + y) / α) (1 / α) y := fun y => by
    simpa using ((hasDerivAt_id' y).const_add R).div_const α
  have hd : ∀ y, HasDerivAt (gaussFOC α R)
      (gaussDemand' ((R + y) / α) * (1 / α) + (1 * (gaussDemand' ((R + y) / α) * (1 / α)) +
        y * (gaussDemand'' ((R + y) / α) * (1 / α) * (1 / α))) - 2 * 1) y := by
    intro y
    have hA : HasDerivAt (fun y => gaussDemand ((R + y) / α))
        (gaussDemand' ((R + y) / α) * (1 / α)) y := (gaussDemand_hasDerivAt _).comp y (h1 y)
    have hB : HasDerivAt (fun y => gaussDemand' ((R + y) / α))
        (gaussDemand'' ((R + y) / α) * (1 / α)) y := (gaussDemand'_hasDerivAt _).comp y (h1 y)
    exact (hA.add ((hasDerivAt_id' y).mul (hB.mul_const (1 / α)))).sub
      ((hasDerivAt_id' y).const_mul 2)
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · exact fun y _ => (hd y).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have hs : 0 ≤ (R + y) / α := div_nonneg (by linarith [hy.1]) hα0.le
    obtain ⟨-, -, hb3, -, hb5⟩ := gaussDemand_bounds hs
    have hinv : 0 < 1 / α := by positivity
    have hinv4 : 1 / α ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hα
    have hq : y * gaussDemand'' ((R + y) / α) ≤ 4 :=
      by nlinarith [mul_le_mul_of_nonneg_left hb5.le hy.1.le, hy.2]
    have : y * (gaussDemand'' ((R + y) / α) * (1 / α) * (1 / α)) ≤ 4 * (1 / α) * (1 / α) := by
      have := mul_le_mul_of_nonneg_right hq (mul_nonneg hinv.le hinv.le)
      linarith
    nlinarith [mul_neg_of_neg_of_pos hb3 hinv, mul_le_mul hinv4 hinv4 hinv.le (by norm_num)]

/-- For `y ∈ [3/8, 1]`, `F(·, y)` is strictly increasing on `R ≥ 2α²` (strategic
complements: `p' + (y/α)p'' > 0` far out in the tail of `p`). -/
theorem gaussFOC_mono {α y : ℝ} (hα : 4 ≤ α) (hy1 : 3 / 8 ≤ y) (hy2 : y ≤ 1) :
    StrictMonoOn (fun R => gaussFOC α R y) (Ici (2 * α ^ 2)) := by
  have hα0 : 0 < α := by linarith
  have h1 : ∀ R, HasDerivAt (fun R : ℝ => (R + y) / α) (1 / α) R := fun R => by
    simpa using ((hasDerivAt_id' R).add_const y).div_const α
  have hd : ∀ R, HasDerivAt (fun R => gaussFOC α R y)
      (gaussDemand' ((R + y) / α) * (1 / α) +
        y * (gaussDemand'' ((R + y) / α) * (1 / α) * (1 / α))) R := by
    intro R
    have hA : HasDerivAt (fun R => gaussDemand ((R + y) / α))
        (gaussDemand' ((R + y) / α) * (1 / α)) R := (gaussDemand_hasDerivAt _).comp R (h1 R)
    have hB : HasDerivAt (fun R => gaussDemand' ((R + y) / α))
        (gaussDemand'' ((R + y) / α) * (1 / α)) R := (gaussDemand'_hasDerivAt _).comp R (h1 R)
    have := (hA.add ((hB.mul_const (1 / α)).const_mul y)).sub_const (2 * y)
    exact this
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun R _ => (hd R).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ici] at hR
    rw [(hd R).deriv]
    have hR' : 2 * α ^ 2 < R := hR
    set u := (R + y) / α + 1 with hu
    have hu2 : 2 * α + 1 ≤ u := by
      rw [hu]
      have : 2 * α ≤ (R + y) / α := by rw [le_div_iff₀ hα0]; nlinarith
      linarith
    unfold gaussDemand' gaussDemand''
    rw [← hu]
    set E := Real.exp (-u ^ 2)
    have hE : 0 < E := Real.exp_pos _
    have key : 0 < -2 * u * α + y * (4 * u ^ 2 - 2) := by nlinarith
    have e : -2 * u * E * (1 / α) + y * ((4 * u ^ 2 - 2) * E * (1 / α) * (1 / α)) =
        E * (-2 * u * α + y * (4 * u ^ 2 - 2)) / α ^ 2 := by
      field_simp
    rw [e]
    positivity

/-- **Exercise 12.F.1, the printed claim is false** (MWG, p. 435). For the inverse demand
`p(s) = 1 + e^{−(s+1)²}` (differentiable, `p' < 0` on `[0, ∞)`) and the strictly convex cost
`c(q) = q²`, at every market size `α ≥ 4` best responses exist and are unique, but the best
response is strictly increasing somewhere: at `Q₋ⱼ = 2α²` and `2α² + 1`. So there is no `α̂` such
that `b(·)` is weakly decreasing for all `α ≥ α̂`. (The ratio `p''/(−p')` is unbounded, so the
sufficient condition of `exercise_12_F_1` fails.) -/
theorem exercise_12_F_1_counterexample {α : ℝ} (hα : 4 ≤ α) :
    (∀ R, 0 ≤ R → ∃ y, IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y) ∧
    (∀ R, 0 ≤ R → ∀ y y', IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y →
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y' → y = y') ∧
    ∃ y y', IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) (2 * α ^ 2) y ∧
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) (2 * α ^ 2 + 1) y' ∧ y < y' := by
  have hα0 : 0 < α := by linarith
  have hex : ∀ R, 0 ≤ R → ∃ y, IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y := by
    intro R hR
    obtain ⟨y, hy⟩ := cbr_exists_Icc (P := sizedDemand gaussDemand α) (c := fun q => q ^ 2)
      (B := 2) (by norm_num) (by unfold sizedDemand gaussDemand; fun_prop) (by fun_prop) R
    refine ⟨y, hy.1.1, fun y' hy' => ?_⟩
    rcases le_or_gt y' 2 with h | h
    · exact hy.2 y' ⟨hy', h⟩
    · have h0 := hy.2 0 ⟨le_rfl, by norm_num⟩
      have hp2 : sizedDemand gaussDemand α (R + y') ≤ 2 := by
        unfold sizedDemand gaussDemand
        have : Real.exp (-((R + y') / α + 1) ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith
      unfold cbrProfit at h0 ⊢
      have hy'0 : (0 : ℝ) ≤ y' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hp2 hy'0]
  have huniq : ∀ R, 0 ≤ R → ∀ y y',
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y →
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y' → y = y' := by
    intro R hR y y' hy hy'
    obtain ⟨h1, h2, h3⟩ := gauss_br_foc hα hR hy
    obtain ⟨h1', h2', h3'⟩ := gauss_br_foc hα hR hy'
    exact (gaussFOC_anti hα hR).injOn ⟨by linarith, h3⟩ ⟨by linarith, h3'⟩ (h1.trans h1'.symm)
  refine ⟨hex, huniq, ?_⟩
  have hR1 : (0 : ℝ) ≤ 2 * α ^ 2 := by positivity
  obtain ⟨y, hy⟩ := hex _ hR1
  obtain ⟨y', hy'⟩ := hex (2 * α ^ 2 + 1) (by positivity)
  refine ⟨y, y', hy, hy', ?_⟩
  obtain ⟨f1, l1, u1⟩ := gauss_br_foc hα hR1 hy
  obtain ⟨f2, l2, u2⟩ := gauss_br_foc hα (by positivity) hy'
  by_contra hle
  push Not at hle
  have hA := (gaussFOC_anti hα (show (0 : ℝ) ≤ 2 * α ^ 2 + 1 by positivity)).antitoneOn
    ⟨by linarith, u2⟩ ⟨by linarith, u1⟩ hle
  have hM := gaussFOC_mono hα l1 u1 (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith))
    (show 2 * α ^ 2 < 2 * α ^ 2 + 1 by linarith)
  simp only at hM
  linarith

/-- **Exercise 12.F.1, the printed claim refuted** (MWG, p. 435): for the model of
`exercise_12_F_1_counterexample` there is no market size beyond which best responses are unique
and weakly decreasing. -/
theorem exercise_12_F_1_false :
    ¬ ∃ A, ∀ α, A ≤ α → BRDecreasing (sizedDemand gaussDemand α) (fun q => q ^ 2) := by
  rintro ⟨A, hA⟩
  set α := max A 4
  obtain ⟨-, -, y, y', hy, hy', hlt⟩ := exercise_12_F_1_counterexample (le_max_right A 4)
  have := (hA α (le_max_left A 4)).2 _ _ (by positivity) (by linarith) y y' hy hy'
  linarith

/-- With linear demand `p(s) = a − s` and any convex cost, best responses are unique: profit is
strictly concave in own output. -/
theorem linear_br_unique {a α : ℝ} (hα : 0 < α) {c : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) c)
    {R y y' : ℝ} (hy : IsBROn (sizedDemand (fun s => a - s) α) c (Ici 0) R y)
    (hy' : IsBROn (sizedDemand (fun s => a - s) α) c (Ici 0) R y') : y = y' := by
  by_contra hne
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hy'0 : (0 : ℝ) ≤ y' := hy'.1
  have hm : (y + y') / 2 ∈ Ici (0 : ℝ) := mem_Ici.2 (by linarith)
  have h1 := hy.2 _ hm
  have h2 := hy'.2 y hy.1
  have h3 := hy.2 y' hy'.1
  have hcv := hc.2 (mem_Ici.2 hy0) (mem_Ici.2 hy'0) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hcv
  rw [show 1 / 2 * y + 1 / 2 * y' = (y + y') / 2 by ring] at hcv
  unfold cbrProfit sizedDemand at h1 h2 h3
  have hsq : 0 < (y - y') ^ 2 := by
    have : y - y' ≠ 0 := sub_ne_zero.2 hne
    positivity
  have e : (a - (R + (y + y') / 2) / α) * ((y + y') / 2) -
      ((a - (R + y) / α) * y + (a - (R + y') / α) * y') / 2 = (y - y') ^ 2 / (4 * α) := by
    field_simp
    ring
  have : 0 < (y - y') ^ 2 / (4 * α) := by positivity
  linarith

/-- With linear demand `p(s) = a − s` and convex cost, the best response is unique and weakly
decreasing at every market size `α > 0` (Exercise 12.F.1 with `L = 0`). -/
theorem linear_brDecreasing {a α : ℝ} (hα : 0 < α) {c : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) c) :
    BRDecreasing (sizedDemand (fun s => a - s) α) c := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a - s) ((fun _ => (-1 : ℝ)) s) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub a
  have hp' : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) s) s :=
    fun s => hasDerivAt_const s _
  refine ⟨fun R _ y y' hy hy' => linear_br_unique hα hc hy hy', fun R R' hR hRR y y' hy hy' =>
    exercise_12_F_1_core (L := 0) hp hp' (fun _ _ => by norm_num) (fun _ _ => by norm_num) le_rfl
      hα hR hRR hy hy' (by simpa using hα)⟩

/-- **Instance for Proposition 12.F.1** (MWG, p. 412). Inverse demand `p(s) = 3 − s`, cost
`c(q) = q²`, entry cost `K = 1`: average cost `1/q + q` is minimized at `q̄ = 1` with `c̄ = 2`,
`x(c̄) = 1`; every hypothesis of `proposition_12_F_1_of_exercise_12_F_1` holds (`L = 0`,
`B = 3`, unique best responses), so SPNE prices converge to `2`. -/
theorem proposition_12_F_1_instance :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE (fun s => 3 - s) (fun q => q ^ 2) 1 α E σ →
        |(fun s : ℝ => 3 - s) ((∑ k ∈ E, σ E k) / α) - 2| < ε := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 - s) ((fun _ => (-1 : ℝ)) s) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub 3
  have hp' : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) s) s :=
    fun s => hasDerivAt_const s _
  exact proposition_12_F_1_of_exercise_12_F_1 (L := 0) (B := 3) (qbar := 1) (X := 1) hp hp'
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) le_rfl (by norm_num)
    (fun y hy => by norm_num; nlinarith)
    (fun α hα R _ y y' hy hy' => linear_br_unique hα (convexOn_pow 2) hy hy')
    one_pos (by norm_num) (convexOn_pow 2) one_pos (fun q _ => by nlinarith [sq_nonneg (q - 1)])
    (by norm_num)

/-- **Instance for footnote 29** (MWG, p. 413). Inverse demand `p(s) = 2 − s`, constant marginal
cost `c(q) = q` and entry cost `K = 1`: every hypothesis of `footnote_12_29` holds, so SPNE prices
converge to `c̄ = 1`. -/
theorem footnote_12_29_instance :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE (fun s => 2 - s) (fun q => 1 * q) 1 α E σ →
        |(fun s : ℝ => 2 - s) ((∑ k ∈ E, σ E k) / α) - 1| < ε := by
  have hlin : ConvexOn ℝ (Ici 0) (fun q : ℝ => 1 * q) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  exact footnote_12_29 zero_le_one (fun _ _ _ _ h => sub_lt_sub_left h 2)
    (by fun_prop : Continuous fun s : ℝ => 2 - s).continuousAt one_pos (by norm_num)
    ⟨1, fun α hα => linear_brDecreasing (by linarith) hlin⟩

/-- **Instance for Exercise 12.F.1** (MWG, p. 435). `p(s) = 3 − s` (`p' = −1`, `p'' = 0`,
`L = 0`) and `c(q) = q²` (`B = 3`) satisfy every hypothesis of `exercise_12_F_1` at `α = 1`. -/
theorem exercise_12_F_1_instance :
    ∀ R R', 0 ≤ R → R < R' → ∀ y y', IsBROn (sizedDemand (fun s => 3 - s) 1) (fun q => q ^ 2)
      (Ici 0) R y → IsBROn (sizedDemand (fun s => 3 - s) 1) (fun q => q ^ 2) (Ici 0) R' y' →
        y' ≤ y := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 - s) ((fun _ => (-1 : ℝ)) s) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub 3
  have hp' : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) s) s :=
    fun s => hasDerivAt_const s _
  exact exercise_12_F_1 (L := 0) (B := 3) hp hp' (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) le_rfl (fun y hy => by norm_num; nlinarith) one_pos (by norm_num)

/-! ### An explicit SPNE -/

/-- **An SPNE of the two-stage Cournot entry model** (MWG, p. 412), showing that the hypotheses of
`entry_incumbents_no_expand`, `entry_step_ii` and `entry_price_ge` are met. With `p(s) = 2 − s`,
`α = 1`, zero production cost and `K = 1`, the rule "`n` entrants each produce `2/(n + 1)`" is a
Cournot equilibrium after every entry set, and one entrant (`E = {0}`) is an SPNE: the entrant
earns `0`, a second entrant would earn `4/9 − 1 < 0`. -/
theorem entry_spne_instance :
    IsCournotEntrySPNE (fun s => 2 - s) (fun _ => 0) 1 1 {0}
      (fun F _ => 2 / ((F.card : ℝ) + 1)) ∧
    BRDecreasing (sizedDemand (fun s => 2 - s) 1) (fun _ => 0) ∧
    ∑ k ∈ ({0} : Finset ℕ), (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {1, 0} k ≤
      ∑ k ∈ ({0} : Finset ℕ), (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {0} k ∧
    1 * 0 ≤ ∑ k ∈ ({0} : Finset ℕ), (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {0} k
      + 1 ∧
    0 ≤ (fun s : ℝ => 2 - s) ((∑ k ∈ ({0} : Finset ℕ),
      (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {0} k) / 1) := by
  have hc0 : ConvexOn ℝ (Ici 0) (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 (convex_Ici 0)
  have hdec := linear_brDecreasing (a := 2) one_pos hc0
  have hp : StrictAntiOn (fun s : ℝ => 2 - s) (Ici 0) := fun _ _ _ _ h => sub_lt_sub_left h 2
  have hspne : IsCournotEntrySPNE (fun s => 2 - s) (fun _ => 0) 1 1 {0}
      (fun F _ => 2 / ((F.card : ℝ) + 1)) := by
    refine ⟨fun F j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · have h1 : 1 ≤ F.card := Nat.succ_le_of_lt (Finset.card_pos.2 ⟨j, hj⟩)
      have hsum : ∑ k ∈ F.erase j, (fun (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) k =
          ((F.card : ℝ) - 1) * (2 / ((F.card : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul, Nat.cast_sub h1,
          Nat.cast_one]
      have hn : (0 : ℝ) < (F.card : ℝ) + 1 := by positivity
      refine ⟨mem_Ici.2 (by positivity), fun y' hy' => ?_⟩
      unfold cbrProfit sizedDemand
      rw [hsum]
      have hy2 : ((F.card : ℝ) + 1) * (2 / ((F.card : ℝ) + 1)) = 2 := by field_simp
      simp only [div_one, sub_zero]
      generalize 2 / ((F.card : ℝ) + 1) = Y at hy2 ⊢
      generalize (F.card : ℝ) = n at hy2 ⊢
      have e : (2 - ((n - 1) * Y + y')) * y' = (2 - ((n - 1) * Y + Y)) * Y - (y' - Y) ^ 2 := by
        linear_combination (Y - y') * hy2
      rw [e]
      nlinarith [sq_nonneg (y' - Y)]
    · rw [Finset.mem_singleton] at hj
      subst hj
      unfold entryNetProfit
      norm_num
    · rw [Finset.mem_singleton] at hj
      unfold entryNetProfit
      rw [Finset.sum_const, Finset.card_pair hj]
      norm_num [Finset.card_pair hj]
  have hNE := hspne.1 {0}
  have hNF := hspne.1 (insert 1 {0})
  refine ⟨hspne, hdec, ?_, ?_, ?_⟩
  · exact entry_incumbents_no_expand (sizedDemand_strictAntiOn hp one_pos) hc0 hdec
      (by simp) hNE hNF
  · exact entry_step_ii one_pos hp hc0 hdec hspne one_pos (by norm_num)
  · refine le_trans (le_of_eq (zero_mul (2 : ℝ)).symm) ?_
    have h0 : (0 : ℝ) * 2 ≤ 2 := by norm_num
    have := entry_price_ge (cbar := 0) hspne (fun q _ => by norm_num) (by norm_num)
    simpa using this

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Competitive-limit exercises

MWG, Exercises 12.F.2-12.F.4, p. 435.

* `exercise_12_F_2a`: `I` consumers with demand `a − bp` give market demand `I(a − bp)` and
  inverse demand `a/b − Q/(bI)`, i.e. the Section 12.F model with `x(p) = a − bp` and `α = I`.
* `exercise_12_F_2b`: Cournot entry with cost `cq` and entry cost `K`, both two-stage
  (`IsEntryEquilibrium`, Section 12.E) and one-stage (`IsOneStageCournotEntry`: active firms play
  the Cournot equilibrium and earn at least `K`; no outsider gains by entering with any output
  against the active firms' outputs). In both, per-firm profit lies in `[K, 4K]`
  (`cournot_entry_profit_bounds`), so as `I → ∞` the number of firms tends to infinity, the price
  tends to `c`, output per consumer to the competitive `a − bc`, per-firm output per consumer to
  `0`, and consumer surplus per consumer to the competitive `(a − bc)²/(2b)`.
* `exercise_12_F_3`: in the linear two-stage Cournot entry model (Example 12.E.1, the model in
  which Section 12.F's phenomenon was first seen) with `α` fixed, the welfare loss relative to the
  first best, and hence relative to the welfare-optimal number of firms, tends to `0` as `K → 0`.
* Exercise 12.F.4 as printed is ill-posed: the demand `xⱼ(p) = α[γ − β(Jpⱼ/∑ₖ pₖ)]` is
  homogeneous of degree zero in prices. `exercise_12_F_4_br`: when `γ < βJ` the best response to
  rivals' price sum `s` is unique and proportional to `s`; `exercise_12_F_4_no_br`: when
  `γ ≥ βJ` there is no best response; `exercise_12_F_4_symmetric`: a symmetric price `p > 0` is
  an equilibrium iff `γ = β(2 − 1/J)` (a knife-edge that fixes `J`);
  `exercise_12_F_4_indeterminate`: then every `p > 0` is an equilibrium, with quantities
  `α(γ − β)` independent of `p` and profit `αp(γ − β)` taking every positive value, so neither
  prices nor the entry outcome are determined by `α` and `β`.

Departures: in Exercise 12.F.2(b) the stage-2 outputs are the symmetric linear Cournot
equilibrium (unique, Exercise 12.C.7); Exercise 12.F.3 is proved for the linear model; Exercise
12.F.4 is analysed as stated and found ill-posed (`docs/corrections.md`).
-/

namespace MWG.MarketPower

open Set Filter Topology

/-! ### Exercise 12.F.2 -/

/-- **Exercise 12.F.2(a)** (MWG, p. 435). With `I` consumers each demanding `a − bp`, market
demand is `I(a − bp)`; the market inverse demand is `p(Q) = a/b − Q/(bI)`, which is the
size-`I` inverse demand `p(Q/I)` of the individual demand `x(p) = a − bp`. -/
theorem exercise_12_F_2a {a b : ℝ} (hb : 0 < b) {I : ℕ} (hI : 0 < I) (p Q : ℝ) :
    ∑ _i ∈ Finset.range I, (a - b * p) = I * (a - b * p) ∧
    (Q = I * (a - b * p) ↔ p = a / b - Q / (b * I)) ∧
    sizedDemand (fun s => a / b - s / b) I Q = a / b - Q / (b * I) := by
  have hI' : (0 : ℝ) < I := by exact_mod_cast hI
  refine ⟨by simp; ring, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [h]; field_simp; ring
  · rw [h]; field_simp; ring
  · unfold sizedDemand; field_simp

/-- Per-firm Cournot output with `J` firms in the market of Exercise 12.F.2:
`(a/b − c)/(B(J + 1))` with `B = 1/(bI)`, i.e. `(a − bc)I/(J + 1)`. -/
noncomputable def fqJ (a b c I : ℝ) (J : ℕ) : ℝ := (a - b * c) * I / (J + 1)

/-- Consumer surplus at total output `Q` for the inverse demand `a/b − s/(bI)`:
`∫₀^Q p(s) ds − p(Q)Q`. -/
noncomputable def linCS (a b I Q : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..Q, (a / b - s / (b * I))) - (a / b - Q / (b * I)) * Q

/-- Consumer surplus with linear inverse demand is `Q²/(2bI)`. -/
theorem linCS_eq {a b I : ℝ} (hb : 0 < b) (hI : 0 < I) (Q : ℝ) :
    linCS a b I Q = Q ^ 2 / (2 * b * I) := by
  unfold linCS
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => s / (b * I)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- A one-stage Cournot entry equilibrium with `J` active firms (MWG, Section 12.E and Exercise
12.F.2(b)), linear inverse demand `A − BQ`, marginal cost `c` and entry cost `K` (paid only by
active firms): the active firms produce the Cournot output `(A − c)/(B(J + 1))` and earn at least
`K`, and no outsider can earn a positive net profit by entering with any output `y ≥ 0` against
the active firms' outputs. -/
def IsOneStageCournotEntry (A B c K : ℝ) (J : ℕ) : Prop :=
  1 ≤ J ∧ K ≤ cournotEntryProfit A B c J ∧
  ∀ y, 0 ≤ y → (A - B * (J * ((A - c) / (B * (J + 1))) + y) - c) * y - K ≤ 0

/-- In both the two-stage and the one-stage linear Cournot entry models, equilibrium per-firm
profit lies in `[K, 4K]`. -/
theorem cournot_entry_profit_bounds {A B c K : ℝ} (hB : 0 < B) (hAc : c ≤ A) {J : ℕ}
    (hJ : IsEntryEquilibrium (cournotEntryProfit A B c) K J ∨ IsOneStageCournotEntry A B c K J) :
    K ≤ cournotEntryProfit A B c J ∧ cournotEntryProfit A B c J ≤ 4 * K := by
  rcases hJ with h | h
  · refine ⟨h.2.1, ?_⟩
    have e : cournotEntryProfit A B c J * ((J : ℝ) + 1) ^ 2 =
        cournotEntryProfit A B c (J + 1) * ((J : ℝ) + 2) ^ 2 := by
      unfold cournotEntryProfit; push_cast; field_simp; ring
    have hnn : 0 ≤ cournotEntryProfit A B c (J + 1) := by
      unfold cournotEntryProfit; positivity
    have h2 := h.2.2
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hle : ((J : ℝ) + 2) ^ 2 ≤ 4 * ((J : ℝ) + 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < ((J : ℝ) + 1) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hle hnn]
  · refine ⟨h.2.1, ?_⟩
    have hy := h.2.2 ((A - c) / (B * (J + 1)) / 2) (by
      have : 0 ≤ A - c := by linarith
      positivity)
    have e : (A - B * (J * ((A - c) / (B * (J + 1))) + (A - c) / (B * (J + 1)) / 2) - c) *
        ((A - c) / (B * (J + 1)) / 2) = cournotEntryProfit A B c J / 4 := by
      unfold cournotEntryProfit; field_simp; ring
    linarith

/-- **Exercise 12.F.2(b)** (MWG, p. 435). Market of `I` consumers with demand `a − bp`
(`bc < a`), Cournot competition with cost `cq` and entry cost `K > 0`. Let `J(I)` be an
equilibrium number of firms of either the two-stage or the one-stage entry model for each `I ≥ 1`.
Each firm produces `fqJ = (a − bc)I/(J + 1)`. As `I → ∞`: the number of firms tends to infinity;
the price tends to `c`; total output per consumer tends to the competitive `a − bc`; each firm's
output per consumer tends to `0`; consumer surplus per consumer tends to the competitive
`(a − bc)²/(2b)`. -/
theorem exercise_12_F_2b {a b c K : ℝ} (hb : 0 < b) (hbc : b * c < a) (hK : 0 < K)
    (J : ℕ → ℕ) (hJ : ∀ I : ℕ, 1 ≤ I →
      IsEntryEquilibrium (cournotEntryProfit (a / b) (1 / (b * I)) c) K (J I) ∨
      IsOneStageCournotEntry (a / b) (1 / (b * I)) c K (J I)) :
    (∀ I : ℕ, 1 ≤ I → (a / b - c) / (1 / (b * I) * (J I + 1)) = fqJ a b c I (J I)) ∧
    Tendsto J atTop atTop ∧
    Tendsto (fun I : ℕ => a / b - J I * fqJ a b c I (J I) / (b * I)) atTop (𝓝 c) ∧
    Tendsto (fun I : ℕ => J I * fqJ a b c I (J I) / I) atTop (𝓝 (a - b * c)) ∧
    Tendsto (fun I : ℕ => fqJ a b c I (J I) / I) atTop (𝓝 0) ∧
    Tendsto (fun I : ℕ => linCS a b I (J I * fqJ a b c I (J I)) / I) atTop
      (𝓝 ((a - b * c) ^ 2 / (2 * b))) := by
  have hA : c < a / b := (lt_div_iff₀ hb).2 (by linarith)
  have hAc : 0 < a / b - c := sub_pos.2 hA
  have hD : 0 < (a / b - c) ^ 2 * b := by positivity
  have hJinf : Tendsto J atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    refine ⟨⌈4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b)⌉₊ + 1, fun I hI => ?_⟩
    have hI1 : 1 ≤ I := le_trans (Nat.le_add_left 1 _) hI
    have hIr : (0 : ℝ) < I := by exact_mod_cast hI1
    have hbd := (cournot_entry_profit_bounds (by positivity) hA.le (hJ I hI1)).2
    unfold cournotEntryProfit at hbd
    have e : ((a / b - c) / ((J I : ℝ) + 1)) ^ 2 / (1 / (b * I)) =
        (a / b - c) ^ 2 * b * I / ((J I : ℝ) + 1) ^ 2 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at hbd
    have hceil : 4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b) < I := by
      have h1 := Nat.le_ceil (4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b))
      have h2 : ((⌈4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b)⌉₊ + 1 : ℕ) : ℝ) ≤ I := by
        exact_mod_cast hI
      push_cast at h2
      linarith
    rw [div_lt_iff₀ hD] at hceil
    by_contra hlt
    push Not at hlt
    have h3 : ((J I : ℝ) + 1) ≤ M := by exact_mod_cast hlt
    have h4 : ((J I : ℝ) + 1) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    nlinarith
  have hJr : Tendsto (fun I => ((J I : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hJinf)
  have hev : ∀ᶠ I : ℕ in atTop, (1 : ℝ) ≤ I :=
    Filter.eventually_atTop.2 ⟨1, fun I hI => by exact_mod_cast hI⟩
  have hQI : Tendsto (fun I : ℕ => J I * fqJ a b c I (J I) / I) atTop (𝓝 (a - b * c)) := by
    have h := ((exercise_12_C_7_limits (b := 1) hbc one_pos).2.2.2.2).comp hJinf
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    simp only [Function.comp, fqJ]
    field_simp
  refine ⟨fun I hI => ?_, hJinf, ?_, hQI, ?_, ?_⟩
  · have hIr : (0 : ℝ) < I := by exact_mod_cast hI
    unfold fqJ; field_simp
  · have h := ((exercise_12_C_7_limits hA hb).2.2.2.1).comp hJinf
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    simp only [Function.comp, fqJ]
    field_simp
    ring
  · have h := (tendsto_const_nhds (x := a - b * c)).div_atTop hJr
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    simp only [fqJ]
    field_simp
  · have h := (hQI.pow 2).div_const (2 * b)
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    rw [linCS_eq hb (by linarith)]
    field_simp

/-- **Instance for Exercise 12.F.2(b)** (MWG, p. 435). With `a = 2`, `b = 1`, `c = 0`,
`K = 1`, per-firm profit is `π_J = 4I/(J + 1)²`, a two-stage entry equilibrium exists for every
`I ≥ 1` (`entry_equilibrium_exists`), so the hypotheses of `exercise_12_F_2b` hold and the price
tends to `0 = c`. -/
theorem exercise_12_F_2b_instance :
    ∃ J : ℕ → ℕ, (∀ I : ℕ, 1 ≤ I →
      IsEntryEquilibrium (cournotEntryProfit (2 / 1) (1 / (1 * I)) 0) 1 (J I)) ∧
      Tendsto (fun I : ℕ => 2 / 1 - J I * fqJ 2 1 0 I (J I) / (1 * I)) atTop (𝓝 0) := by
  have h : ∀ I : ℕ, ∃ J, 1 ≤ I →
      IsEntryEquilibrium (cournotEntryProfit (2 / 1) (1 / (1 * I)) 0) 1 J := by
    intro I
    by_cases hI : 1 ≤ I
    · have hIr : (1 : ℝ) ≤ I := by exact_mod_cast hI
      have hpi : ∀ n : ℕ, cournotEntryProfit (2 / 1) (1 / (1 * I)) 0 n =
          4 * I / ((n : ℝ) + 1) ^ 2 := by
        intro n; unfold cournotEntryProfit; field_simp; ring
      obtain ⟨J, hJ⟩ := entry_equilibrium_exists
        (π := cournotEntryProfit (2 / 1) (1 / (1 * I)) 0) (K := 1)
        (by rw [hpi]; norm_num; linarith)
        ⟨2 * I, by
          rw [hpi, div_lt_one (by positivity)]
          push_cast
          nlinarith⟩
      exact ⟨J, fun _ => hJ⟩
    · exact ⟨0, fun h => absurd h hI⟩
  choose J hJ using h
  exact ⟨J, hJ, (exercise_12_F_2b (a := 2) (b := 1) (c := 0) (K := 1) one_pos (by norm_num)
    one_pos J (fun I hI => Or.inl (hJ I hI))).2.2.1⟩

/-! ### Exercise 12.F.3 -/

/-- The first-best welfare in the linear model with marginal cost `c` and entry cost `K`: one firm
producing the competitive output `(a − c)/b`, `W = (a − c)²/(2b) − K`. -/
noncomputable def firstBestWelfare (a b c K : ℝ) : ℝ := (a - c) ^ 2 / (2 * b) - K

/-- Welfare (12.E.5) with `J` firms each producing `q_J`, linear demand, constant marginal cost:
`(a − c)Q − bQ²/2 − JK` with `Q = Jq_J`. -/
theorem entryWelfare_linear_general {a b c K : ℝ} (q : ℕ → ℝ) (J : ℕ) :
    entryWelfare (fun s => a - b * s) (fun q => c * q) q K J =
      (a - c) * (J * q J) - b * (J * q J) ^ 2 / 2 - J * K := by
  unfold entryWelfare
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => b * s).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- **Exercise 12.F.3** (MWG, p. 435). In the linear two-stage Cournot entry model (inverse
demand `a − bq`, cost `cq`, entry cost `K`, market size fixed): the first-best welfare
`(a − c)²/(2b) − K` bounds the welfare of every configuration of `J ≥ 1` firms and is attained
by one firm producing `(a − c)/b`; and as `K → 0` the welfare loss of the free-entry equilibrium
relative to the first best, hence also relative to any number `J°` of firms (in particular the
welfare-optimal one), tends to `0`. -/
theorem exercise_12_F_3 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ K, 0 ≤ K → ∀ (q : ℕ → ℝ) (J : ℕ), 1 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) q K J ≤ firstBestWelfare a b c K) ∧
    (∀ K, entryWelfare (fun s => a - b * s) (fun q => c * q) (fun _ => (a - c) / b) K 1 =
      firstBestWelfare a b c K) ∧
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ K, 0 < K → K < δ → ∀ J,
      IsEntryEquilibrium (cournotEntryProfit a b c) K J →
      firstBestWelfare a b c K - entryWelfare (fun s => a - b * s) (fun q => c * q)
          (fun J => (a - c) / (b * (J + 1))) K J < ε ∧
      ∀ (Jo : ℕ) (q : ℕ → ℝ), 1 ≤ Jo →
        entryWelfare (fun s => a - b * s) (fun q => c * q) q K Jo -
          entryWelfare (fun s => a - b * s) (fun q => c * q)
            (fun J => (a - c) / (b * (J + 1))) K J < ε := by
  have hFB : ∀ K, 0 ≤ K → ∀ (q : ℕ → ℝ) (J : ℕ), 1 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) q K J ≤ firstBestWelfare a b c K := by
    intro K hK q J hJ
    rw [entryWelfare_linear_general, firstBestWelfare]
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have e : (a - c) ^ 2 / (2 * b) - ((a - c) * (J * q J) - b * (J * q J) ^ 2 / 2) =
        (b * (J * q J) - (a - c)) ^ 2 / (2 * b) := by
      field_simp; ring
    have : 0 ≤ (b * (J * q J) - (a - c)) ^ 2 / (2 * b) := by positivity
    nlinarith
  refine ⟨hFB, fun K => ?_, fun ε hε => ?_⟩
  · rw [entryWelfare_linear_general, firstBestWelfare]
    push_cast
    field_simp
    ring
  set D := (a - c) ^ 2 with hD
  have hD0 : 0 < D := by have := sub_pos.2 hac; positivity
  refine ⟨min (ε / 4) (ε ^ 2 * b / (4 * (D + 1))), lt_min (by linarith) (by positivity),
    fun K hK hKδ J hJ => ?_⟩
  have hK1 : K < ε / 4 := lt_of_lt_of_le hKδ (min_le_left _ _)
  have hK2 : K < ε ^ 2 * b / (4 * (D + 1)) := lt_of_lt_of_le hKδ (min_le_right _ _)
  have hJ1 : 1 ≤ J := hJ.1
  have hnum := (example_12_E_1_number hb hK hJ1).1 hJ
  have hbK : 0 < b * K := by positivity
  rw [le_div_iff₀ hbK, div_lt_iff₀ hbK] at hnum
  obtain ⟨h1, h2⟩ := hnum
  rw [← hD] at h1 h2
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hJp : (0 : ℝ) < (J : ℝ) + 1 := by linarith
  have hloss : firstBestWelfare a b c K - entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K J = D / (2 * b * ((J : ℝ) + 1) ^ 2) + (J - 1) * K := by
    rw [entryWelfare_linear hb, firstBestWelfare, hD]
    field_simp
    ring
  -- first term `< 2K`
  have t1 : D / (2 * b * ((J : ℝ) + 1) ^ 2) < 2 * K := by
    rw [div_lt_iff₀ (by positivity)]
    have hle : ((J : ℝ) + 2) ^ 2 ≤ 4 * ((J : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hle hbK.le]
  -- second term: `(JK)² ≤ DK/b < ε²/4`
  have hJK : (J : ℝ) * K < ε / 2 := by
    have hsq : ((J : ℝ) * K) ^ 2 * b ≤ D * K := by
      have hJJ : (J : ℝ) ^ 2 ≤ ((J : ℝ) + 1) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 hK.le
      have := mul_le_mul_of_nonneg_right hJJ (show 0 ≤ K ^ 2 * b by positivity)
      nlinarith
    have hDK : D * K < ε ^ 2 * b / 4 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      rw [lt_div_iff₀ (by positivity)] at hK2
      nlinarith
    by_contra hge
    push Not at hge
    have : (ε / 2) ^ 2 ≤ ((J : ℝ) * K) ^ 2 := pow_le_pow_left₀ (by positivity) hge 2
    nlinarith
  have hmain : firstBestWelfare a b c K - entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K J < ε := by
    rw [hloss]; nlinarith
  refine ⟨hmain, fun Jo q hJo => ?_⟩
  have := hFB K hK.le q Jo hJo
  linarith

/-! ### Exercise 12.F.4 -/

/-- Firm `j`'s profit in the differentiated-products price game of Exercise 12.F.4 when it charges
`p`, the other active firms' prices sum to `s`, and `J` firms are active:
`p xⱼ = αp[γ − β(Jp/(p + s))]` (zero marginal cost). -/
noncomputable def dpProfit (α γ β J s p : ℝ) : ℝ := α * p * (γ - β * (J * p / (p + s)))

/-- `p ≥ 0` is a best response to the rivals' price sum `s`. -/
def IsDPBR (α γ β J s p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p', 0 ≤ p' → dpProfit α γ β J s p' ≤ dpProfit α γ β J s p

/-- **Exercise 12.F.4, best responses** (MWG, p. 435). If `γ < βJ`, write `D = βJ − γ > 0` and
let `u > 1` solve `u²D = βJ`. Against rivals' price sum `s > 0` the unique best response is
`p* = (u − 1)s`: `π(p*) − π(p) = αD(p + s − us)²/(p + s)`. -/
theorem exercise_12_F_4_br {α γ β J s u : ℝ} (hα : 0 < α) (hs : 0 < s) (hu : 1 < u)
    (hD : 0 < β * J - γ) (hu2 : u ^ 2 * (β * J - γ) = β * J) :
    IsDPBR α γ β J s ((u - 1) * s) ∧ ∀ p, IsDPBR α γ β J s p → p = (u - 1) * s := by
  have key : ∀ p, 0 ≤ p → dpProfit α γ β J s ((u - 1) * s) - dpProfit α γ β J s p =
      α * (β * J - γ) * (p + s - u * s) ^ 2 / (p + s) := by
    intro p hp
    unfold dpProfit
    have hps : 0 < p + s := by linarith
    have hus : 0 < u * s := by positivity
    rw [show (u - 1) * s + s = u * s by ring]
    have e1 : β * (J * p / (p + s)) = β * J * p / (p + s) := by ring
    have e2 : β * (J * ((u - 1) * s) / (u * s)) = β * J * ((u - 1) * s) / (u * s) := by ring
    rw [e1, e2]
    generalize hM : β * J = M at hu2 ⊢
    obtain ⟨D, rfl⟩ : ∃ D, γ = M - D := ⟨M - γ, by ring⟩
    have hMD : M = u ^ 2 * D := by rw [← hu2]; ring
    subst hMD
    field_simp
    ring
  have hnn : ∀ p, 0 ≤ p → 0 ≤ α * (β * J - γ) * (p + s - u * s) ^ 2 / (p + s) := by
    intro p hp
    have : 0 < p + s := by linarith
    positivity
  refine ⟨⟨by nlinarith, fun p hp => by linarith [key p hp, hnn p hp]⟩, fun p hp => ?_⟩
  have h1 := hp.2 ((u - 1) * s) (mul_nonneg (by linarith) hs.le)
  have h2 := key p hp.1
  have hps : 0 < p + s := by linarith [hp.1]
  have h3 : α * (β * J - γ) * (p + s - u * s) ^ 2 / (p + s) = 0 :=
    le_antisymm (by linarith) (hnn p hp.1)
  rw [div_eq_zero_iff] at h3
  rcases h3 with h3 | h3
  · have : α * (β * J - γ) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h3).resolve_left this
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · linarith

/-- The root `u = √(βJ/(βJ − γ)) > 1` of `u²(βJ − γ) = βJ` exists when `0 < γ < βJ`. -/
theorem exercise_12_F_4_root {γ β J : ℝ} (hγ : 0 < γ) (hD : 0 < β * J - γ) :
    ∃ u, 1 < u ∧ u ^ 2 * (β * J - γ) = β * J := by
  refine ⟨Real.sqrt (β * J / (β * J - γ)), ?_, ?_⟩
  · rw [Real.lt_sqrt zero_le_one, one_pow, lt_div_iff₀ hD]; linarith
  · rw [Real.sq_sqrt (div_nonneg (by linarith) hD.le)]; field_simp

/-- **Exercise 12.F.4, no best response when `γ ≥ βJ`** (MWG, p. 435). Then profit is strictly
increasing in own price: `π(p + 1) > π(p)` for every `p ≥ 0`, so no best response exists. -/
theorem exercise_12_F_4_no_br {α γ β J s : ℝ} (hα : 0 < α) (hβJ : 0 < β * J) (hγ : β * J ≤ γ)
    (hs : 0 < s) (p : ℝ) (hp : 0 ≤ p) : dpProfit α γ β J s p < dpProfit α γ β J s (p + 1) := by
  have e : dpProfit α γ β J s (p + 1) - dpProfit α γ β J s p =
      α * ((γ - β * J) + β * J * s ^ 2 / ((p + s) * (p + 1 + s))) := by
    unfold dpProfit
    have e1 : ∀ x, β * (J * x / (x + s)) = β * J * x / (x + s) := fun x => by ring
    rw [e1, e1]
    field_simp
    ring
  have : 0 < α * ((γ - β * J) + β * J * s ^ 2 / ((p + s) * (p + 1 + s))) := by
    have : 0 < β * J * s ^ 2 / ((p + s) * (p + 1 + s)) := by
      have : 0 < p + s := by linarith
      positivity
    have : 0 ≤ γ - β * J := by linarith
    positivity
  linarith

/-- **Exercise 12.F.4, symmetric equilibria** (MWG, p. 435). With `J ≥ 2` active firms,
`α, β, γ > 0` and a common price `p > 0`, `p` is a best response to the others' prices (sum
`(J − 1)p`) iff `γ = β(2 − 1/J)`, equivalently `J(2β − γ) = β`. So a symmetric equilibrium with
positive prices exists only on this knife-edge, which pins down the number of firms. -/
theorem exercise_12_F_4_symmetric {α γ β : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) {p : ℝ} (hp : 0 < p) :
    (IsDPBR α γ β J ((J - 1) * p) p ↔ γ = β * (2 - 1 / J)) ∧
    (γ = β * (2 - 1 / J) ↔ (J : ℝ) * (2 * β - γ) = β) := by
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ1 : (0 : ℝ) < (J : ℝ) - 1 := by linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hs : 0 < ((J : ℝ) - 1) * p := by positivity
  refine ⟨⟨fun hbr => ?_, fun hγe => ?_⟩, ⟨fun h => by rw [h]; field_simp; ring, fun h => ?_⟩⟩
  · by_cases hlt : γ < β * J
    · obtain ⟨u, hu, hu2⟩ := exercise_12_F_4_root (β := β) (J := (J : ℝ)) hγ (by linarith)
      have hpu := (exercise_12_F_4_br hα hs hu (by linarith) hu2).2 p hbr
      -- `(u − 1)(J − 1) = 1`, so `u = J/(J − 1)`
      have hu' : u * ((J : ℝ) - 1) = J := by
        have : p * ((u - 1) * ((J : ℝ) - 1) - 1) = 0 := by linear_combination -hpu
        have := (mul_eq_zero.1 this).resolve_left hp.ne'
        linarith
      have h4 : (u * ((J : ℝ) - 1)) ^ 2 * (β * J - γ) = β * J * ((J : ℝ) - 1) ^ 2 := by
        calc (u * ((J : ℝ) - 1)) ^ 2 * (β * J - γ) = (u ^ 2 * (β * J - γ)) * ((J : ℝ) - 1) ^ 2 :=
              by ring
          _ = _ := by rw [hu2]
      rw [hu'] at h4
      have h5 : (J : ℝ) * (γ * J - β * (2 * J - 1)) = 0 := by linear_combination (-1 : ℝ) * h4
      have h6 := (mul_eq_zero.1 h5).resolve_left hJ0.ne'
      field_simp
      linarith
    · exfalso
      push Not at hlt
      have := hbr.2 (p + 1) (by linarith)
      have := exercise_12_F_4_no_br hα (by positivity) hlt hs p hp.le
      linarith
  · have hD : 0 < β * J - γ := by
      rw [hγe]
      have : β * J - β * (2 - 1 / J) = β * ((J : ℝ) - 1) ^ 2 / J := by field_simp; ring
      rw [this]; positivity
    have hu : 1 < (J : ℝ) / (J - 1) := by rw [lt_div_iff₀ hJ1]; linarith
    have hu2 : ((J : ℝ) / (J - 1)) ^ 2 * (β * J - γ) = β * J := by
      rw [hγe]; field_simp; ring
    have h := (exercise_12_F_4_br hα hs hu hD hu2).1
    have e : ((J : ℝ) / (J - 1) - 1) * (((J : ℝ) - 1) * p) = p := by field_simp; ring
    rwa [e] at h
  · field_simp
    linarith

/-- **Exercise 12.F.4, indeterminacy** (MWG, p. 435). On the knife-edge `γ = β(2 − 1/J)`
(`J ≥ 2`, `α, β > 0`), every common price `p > 0` is a symmetric equilibrium of the stage-2 price
game; each firm sells `α(γ − β) > 0` whatever `p` is, and earns `αp(γ − β)`, which takes every
positive value as `p` varies. So the equilibrium price level, profits, and hence the entry
outcome, are not determined by the size `α` and substitution `β` parameters. -/
theorem exercise_12_F_4_indeterminate {α β : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hα : 0 < α)
    (hβ : 0 < β) :
    let γ := β * (2 - 1 / J)
    0 < γ - β ∧ (∀ p, 0 < p → IsDPBR α γ β J ((J - 1) * p) p ∧
      α * (γ - β * (J * p / (p + (J - 1) * p))) = α * (γ - β) ∧
      dpProfit α γ β J ((J - 1) * p) p = α * p * (γ - β)) ∧
    ∀ π, 0 < π → ∃ p, 0 < p ∧ dpProfit α γ β J ((J - 1) * p) p = π := by
  intro γ
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hγβ : 0 < γ - β := by
    have : γ - β = β * ((J : ℝ) - 1) / J := by simp only [γ]; field_simp; ring
    rw [this]
    have : (0 : ℝ) < (J : ℝ) - 1 := by linarith
    positivity
  have hγ : 0 < γ := by linarith
  have hq : ∀ p, 0 < p → α * (γ - β * (J * p / (p + (J - 1) * p))) = α * (γ - β) := by
    intro p hp
    have : (J : ℝ) * p / (p + (J - 1) * p) = 1 := by
      rw [div_eq_one_iff_eq (by nlinarith)]; ring
    rw [this, mul_one]
  have hprof : ∀ p, 0 < p → dpProfit α γ β J ((J - 1) * p) p = α * p * (γ - β) := by
    intro p hp
    unfold dpProfit
    rw [show α * p * (γ - β * (J * p / (p + (J - 1) * p))) =
      p * (α * (γ - β * (J * p / (p + (J - 1) * p)))) by ring, hq p hp]
    ring
  refine ⟨hγβ, fun p hp => ⟨((exercise_12_F_4_symmetric hJ hα hβ hγ hp).1).2 rfl, hq p hp,
    hprof p hp⟩, fun π hπ => ⟨π / (α * (γ - β)), by positivity, ?_⟩⟩
  rw [hprof _ (by positivity)]
  field_simp

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Strategic entry deterrence and accommodation

MWG, Appendix B of Chapter 12, pp. 423-427 (Figures 12.BB.1-12.BB.8), Exercise 12.BB.1, and the
stage-1.5 entry remark of Section 12.G (p. 417).

Dixit's three-stage game: in stage 1 the incumbent I builds capacity `k_I` at `r` per unit; in
stage 2 the potential entrant E decides whether to enter at cost `F`; in stage 3 the active
firms choose quantities, I at marginal cost `w` up to its capacity and E at `w + r`.

**General results** (inverse demand `p` concave and strictly decreasing on `[0, ∞)`, as in the
book):
* `appendixB_profit_strictConcave`: concavity of `p` makes each firm's profit strictly concave in
  its own quantity (the book's "sufficient condition"); `appendixB_br_antitone`: it also makes
  best responses (weakly) downward sloping.
* `figure_12_BB_1`: E's best-response profit strictly falls as I's output rises.
* `figure_12_BB_2`: firm I's stage-3 best response is `b_I(q_E | k_I) = min{b(q_E | w), k_I}`.
* `exercise_12_BB_1`: if the Stackelberg point `S` lies to the right of `Z`, deterring entry
  (capacity `k_Z`, no entry) beats every accommodation outcome.

**The linear model.** Every other claim of the appendix is a statement about the curves of the
figures; we prove them in the linear specification `p(Q) = a − Q` with `r > 0` and
`a − w − 2r > 0` (so that point `B` is interior). Write `u = a − w − r`.
* `figure_12_BB_3`: the stage-3 game after entry has the unique Nash equilibrium
  `q_I = min{k_I, k_B}`, `q_E = (u − q_I)/2` with `k_B = (a − w + r)/3`; point `A` (no
  first-mover advantage) is `(u/3, u/3)`, and `k_B > u/3` (I can move right of `A`);
  `figure_12_BB_3_range`: I can induce exactly the points of E's best response up to `B`.
* `figure_12_BB_4`: with `k_I > k_B` firm I uses only `k_B`; producing `k_I` is not credible.
* `appendixB_stage3_noEntry`: without entry I produces `b_I(0 | k_I) = min{k_I, (a − w)/2}`.
* `appendixB_stage2`: with `k_Z = u − 2√F`, E's post-entry profit is at least `F` iff the
  post-entry equilibrium lies at or to the left of `Z` (`q_I ≤ k_Z`).
* `figure_12_BB_5` (blockaded entry), `figure_12_BB_6` (entry inevitable: the Stackelberg point
  `S = u/2`, or `k_B` if `S` lies right of `B`; first-mover advantage
  `figure_12_BB_6_firstMover`), `figure_12_BB_7_deter` / `figure_12_BB_7_accommodate`
  (deterrence possible but not inevitable) and `figure_12_BB_8` (the comparison of `k_π`, the
  monopoly output earning the Stackelberg profit, with `k_Z`): each with existence and
  uniqueness of the SPNE capacity, and proved parameter instances.
* `appendixB_deterrence_raises_output`: deterrence raises output and welfare relative to a
  situation where no entry is possible.

**Departures** (docs/corrections.md): the book's tie rule (E enters when its net profit is
nonnegative) is incompatible with "a capacity at least `k_Z` deters entry": under that rule
`k_Z` does not deter, and when deterrence is optimal no SPNE exists
(`appendixB_bookRule_no_spne`); in every SPNE E stays out at `k_Z`
(`figure_12_BB_7_deter`). In the linear model the Stackelberg point never lies strictly to the
right of `Z` when entry is not blockaded (`appendixB_linear_S_le_Z`), so Exercise 12.BB.1 is
proved in the general model.
-/

namespace MWG.MarketPower

/-! ## General results -/

/-- Increments of a concave function fall: for `p` concave on `[0, ∞)`, `0 ≤ x ≤ y` and `h ≥ 0`,
`p(y + h) − p(y) ≤ p(x + h) − p(x)`. -/
theorem appendixB_concave_increment {p : ℝ → ℝ} (hp : ConcaveOn ℝ (Set.Ici 0) p) {x y h : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hh : 0 ≤ h) : p (y + h) - p y ≤ p (x + h) - p x := by
  rcases eq_or_lt_of_le hh with rfl | hh'
  · simp
  have hd : 0 < y + h - x := by linarith
  set l := h / (y + h - x) with hl
  have hl0 : 0 ≤ l := div_nonneg hh hd.le
  have hl1 : 0 ≤ 1 - l := by
    rw [hl, sub_nonneg, div_le_one hd]; linarith
  have hX : x ∈ Set.Ici (0 : ℝ) := hx
  have hY : y + h ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have h1 := hp.2 hX hY hl1 hl0 (by ring)
  have h2 := hp.2 hX hY hl0 hl1 (by ring)
  have e1 : (1 - l) • x + l • (y + h) = x + h := by
    simp only [smul_eq_mul]; rw [hl]; field_simp; ring
  have e2 : l • x + (1 - l) • (y + h) = y := by
    simp only [smul_eq_mul]; rw [hl]; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- **Concavity of profits** (MWG, p. 424). If the inverse demand `p` is concave and strictly
decreasing on `[0, ∞)`, then for every rival output `Q ≥ 0` and marginal cost `c` the profit
`q ↦ q(p(q + Q) − c)` is strictly concave on `[0, ∞)`: "a sufficient condition for this is for
`p(·)` to be concave". -/
theorem appendixB_profit_strictConcave {p : ℝ → ℝ} (hp : ConcaveOn ℝ (Set.Ici 0) p)
    (hpd : StrictAntiOn p (Set.Ici 0)) (c : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun q => q * (p (q + Q) - c)) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  have hxQ : x + Q ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have hyQ : y + Q ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have hc := hp.2 hxQ hyQ ha.le hb.le hab
  simp only [smul_eq_mul] at hc
  have hz : a * (x + Q) + b * (y + Q) = a * x + b * y + Q := by
    linear_combination Q * hab
  rw [hz] at hc
  have hmono : 0 < (y - x) * (p (x + Q) - p (y + Q)) := by
    rcases lt_or_gt_of_ne hxy with h | h
    · have := hpd hxQ hyQ (by linarith)
      exact mul_pos (by linarith) (by linarith)
    · have := hpd hyQ hxQ (by linarith)
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hz0 : 0 ≤ a * x + b * y := by positivity
  have key : (a * x + b * y) * (a * p (x + Q) + b * p (y + Q)) - a * x * p (x + Q) -
      b * y * p (y + Q) = a * b * ((y - x) * (p (x + Q) - p (y + Q))) := by
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  have h1 := mul_le_mul_of_nonneg_left hc hz0
  have h2 : 0 < a * b * ((y - x) * (p (x + Q) - p (y + Q))) := mul_pos (mul_pos ha hb) hmono
  have hcz : a * x * c + b * y * c = (a * x + b * y) * c := by ring
  nlinarith

/-- **Downward-sloping best responses** (MWG, p. 424). If `p` is concave and strictly
decreasing on `[0, ∞)`, `0 ≤ Q ≤ Q'`, `b` is a best response to `Q` and `b'` a best response to
`Q'` (over outputs `q ≥ 0`), then `b' ≤ b`: "the concavity of `p(·)` also implies that firms'
best-response functions are downward sloping". -/
theorem appendixB_br_antitone {p : ℝ → ℝ} (hp : ConcaveOn ℝ (Set.Ici 0) p)
    (hpd : StrictAntiOn p (Set.Ici 0)) {c Q Q' b b' : ℝ} (hQ : 0 ≤ Q) (hQQ : Q ≤ Q')
    (hb : 0 ≤ b) (hbm : ∀ q, 0 ≤ q → q * (p (q + Q) - c) ≤ b * (p (b + Q) - c))
    (hb' : 0 ≤ b') (hbm' : ∀ q, 0 ≤ q → q * (p (q + Q') - c) ≤ b' * (p (b' + Q') - c)) :
    b' ≤ b := by
  by_contra hlt
  have hlt : b < b' := lt_of_not_ge hlt
  have hinc := appendixB_concave_increment hp (x := b + Q) (y := b' + Q) (h := Q' - Q)
    (by linarith) (by linarith) (by linarith)
  have e1 : b + Q + (Q' - Q) = b + Q' := by ring
  have e2 : b' + Q + (Q' - Q) = b' + Q' := by ring
  rw [e1, e2] at hinc
  have hB : p (b + Q') ≤ p (b + Q) :=
    hpd.antitoneOn (show b + Q ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show b + Q' ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
  have hd1 : b' * ((p (b' + Q') - p (b' + Q)) - (p (b + Q') - p (b + Q))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb' (by linarith)
  have hd2 : (b' - b) * (p (b + Q') - p (b + Q)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h1 := hbm b' hb'
  have hbmax : b' * (p (b' + Q') - c) ≤ b * (p (b + Q') - c) := by nlinarith
  have hsc := appendixB_profit_strictConcave hp hpd c (show 0 ≤ Q' by linarith)
  have hmid := hsc.2 (show b ∈ Set.Ici (0 : ℝ) from hb) (show b' ∈ Set.Ici (0 : ℝ) from hb')
    (ne_of_lt hlt) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have := hbm' (1 / 2 * b + 1 / 2 * b') (by positivity)
  linarith

/-- **Figure 12.BB.1** (MWG, p. 424). "Firm E's stage 3 profits decline as we move along this
curve to the right": if `p` is strictly decreasing, `0 ≤ Q < Q'`, `b` is a best response to `Q`
and `b' > 0` is any output, then E's profit `b'(p(b' + Q') − c)` against `Q'` is strictly below
its best-response profit against `Q`. -/
theorem figure_12_BB_1 {p : ℝ → ℝ} (hpd : StrictAntiOn p (Set.Ici 0)) {c Q Q' b b' : ℝ}
    (hQ : 0 ≤ Q) (hQQ : Q < Q') (hbm : ∀ q, 0 ≤ q → q * (p (q + Q) - c) ≤ b * (p (b + Q) - c))
    (hb' : 0 < b') : b' * (p (b' + Q') - c) < b * (p (b + Q) - c) := by
  have hlt : p (b' + Q') < p (b' + Q) :=
    hpd (show b' + Q ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show b' + Q' ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
  have := hbm b' hb'.le
  have : b' * (p (b' + Q') - c) < b' * (p (b' + Q) - c) :=
    mul_lt_mul_of_pos_left (by linarith) hb'
  linarith

/-- **Firm I's stage-3 best response; Figure 12.BB.2** (MWG, pp. 424-425). If I's profit `f`
(as a function of its own output, given `q_E`) is strictly concave on `[0, ∞)` with maximizer
`m = b(q_E | w) ≥ 0`, then with capacity `k_I ≥ 0` its unique best response is
`b_I(q_E | k_I) = min{b(q_E | w), k_I}`. -/
theorem figure_12_BB_2 {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {m k : ℝ}
    (hm0 : 0 ≤ m) (hm : ∀ q, 0 ≤ q → f q ≤ f m) (hk : 0 ≤ k) :
    min m k ∈ Set.Icc 0 k ∧ ∀ q ∈ Set.Icc 0 k, q ≠ min m k → f q < f (min m k) := by
  refine ⟨⟨le_min hm0 hk, min_le_right _ _⟩, fun q hq hne => ?_⟩
  obtain ⟨hq0, hqk⟩ := hq
  rcases le_or_gt m k with hmk | hkm
  · rw [min_eq_left hmk] at hne ⊢
    by_contra hge
    have hge : f m ≤ f q := le_of_not_gt hge
    have hmid := hf.2 (show q ∈ Set.Ici (0 : ℝ) from hq0) (show m ∈ Set.Ici (0 : ℝ) from hm0)
      hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hmid
    have := hm (1 / 2 * q + 1 / 2 * m) (by positivity)
    have := hm q hq0
    linarith
  · rw [min_eq_right hkm.le] at hne ⊢
    have hqk' : q < k := lt_of_le_of_ne hqk hne
    have hz : k ∈ openSegment ℝ q m := by
      rw [openSegment_eq_Ioo (by linarith)]; exact ⟨hqk', hkm⟩
    have h := hf.lt_on_openSegment (show q ∈ Set.Ici (0 : ℝ) from hq0)
      (show m ∈ Set.Ici (0 : ℝ) from hm0) (by intro h; linarith) hz
    rwa [min_eq_left (hm q hq0)] at h

/-- **Exercise 12.BB.1** (MWG, p. 427). Entry deterrence is better than accommodation when the
Stackelberg point `S` lies to the right of `Z`. Let `p` be strictly decreasing, E's best
response `b_E`, and `G(x) = x(p(x + b_E(x)) − (w + r))` I's profit along E's best response
(concave, maximized on `[0, ∞)` at `q_S`). If `0 < k_Z ≤ q_S` (`S` to the right of `Z`) and
`b_E(k_Z) > 0`, then every accommodation outcome (I produces `q ≤ k_Z` from capacity `k ≥ q`
and E plays `b_E(q)`; entry occurs only left of `Z`) earns I strictly less than deterrence
(capacity `k_Z`, monopoly output `k_Z`). -/
theorem exercise_12_BB_1 {p bE G : ℝ → ℝ} {w r kZ qS q k : ℝ} (hp : StrictAntiOn p (Set.Ici 0))
    (hG : ∀ x, G x = x * (p (x + bE x) - (w + r))) (hGc : ConcaveOn ℝ (Set.Ici 0) G)
    (hS : ∀ x, 0 ≤ x → G x ≤ G qS) (hZS : kZ ≤ qS) (hkZ : 0 < kZ) (hbZ : 0 < bE kZ)
    (hq : 0 ≤ q) (hqZ : q ≤ kZ) (hqk : q ≤ k) (hr : 0 ≤ r) :
    q * (p (q + bE q) - w) - r * k < kZ * (p kZ - w) - r * kZ := by
  have hseg : kZ ∈ segment ℝ q qS := by
    rw [segment_eq_Icc (by linarith)]; exact ⟨hqZ, hZS⟩
  have hmin := hGc.ge_on_segment (show q ∈ Set.Ici (0 : ℝ) from hq)
    (show qS ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) hseg
  rw [min_eq_left (hS q hq)] at hmin
  have hlt : p (kZ + bE kZ) < p kZ :=
    hp (show kZ ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show kZ + bE kZ ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
  rw [hG, hG] at hmin
  have h1 : kZ * (p (kZ + bE kZ) - (w + r)) < kZ * (p kZ - (w + r)) :=
    mul_lt_mul_of_pos_left (by linarith) hkZ
  have h2 : r * q ≤ r * k := mul_le_mul_of_nonneg_left hqk hr
  nlinarith

/-- A proved instance of `exercise_12_BB_1`: `p(Q) = 10 − Q`, `w = r = 1`, `b_E(x) = (8 − x)/2`,
`G(x) = x(8 − x)/2`, `q_S = 4`, `k_Z = 3`, `q = k = 2`. -/
theorem exercise_12_BB_1_instance :
    (2 : ℝ) * ((fun x : ℝ => 10 - x) (2 + (fun x : ℝ => (8 - x) / 2) 2) - 1) - 1 * 2 <
      3 * ((fun x : ℝ => 10 - x) 3 - 1) - 1 * 3 := by
  refine exercise_12_BB_1 (p := fun x => 10 - x) (bE := fun x => (8 - x) / 2)
    (G := fun x => x * (8 - x) / 2) (qS := 4) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
  · intro x hx y _ hxy; simp only; linarith
  · intro x; ring
  · refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  · intro x _; nlinarith [sq_nonneg (x - 4)]

/-! ## The linear model -/

/-- Profit `(a − (q + Q))q − cq` of a firm with marginal cost `c` producing `q` against rival
output `Q`, with the linear inverse demand `p(Q) = a − Q`. -/
noncomputable def edProfit (a c q Q : ℝ) : ℝ := (a - (q + Q)) * q - c * q

theorem edProfit_eq (a c q Q : ℝ) : edProfit a c q Q = q * (a - c - Q - q) := by
  unfold edProfit; ring

/-- The maximizer of the quadratic `q(α − q)` on `[0, k]` (`α, k ≥ 0`) is `min{k, α/2}`, and it
is the unique maximizer. -/
theorem appendixB_quad_max {α k : ℝ} (hα : 0 ≤ α) (hk : 0 ≤ k) :
    min k (α / 2) ∈ Set.Icc 0 k ∧ ∀ q ∈ Set.Icc 0 k, q ≠ min k (α / 2) →
      q * (α - q) < min k (α / 2) * (α - min k (α / 2)) := by
  refine ⟨⟨le_min hk (by linarith), min_le_left _ _⟩, fun q hq hne => ?_⟩
  obtain ⟨hq0, hqk⟩ := hq
  have key : q * (α - q) - min k (α / 2) * (α - min k (α / 2)) =
      (q - min k (α / 2)) * (α - q - min k (α / 2)) := by ring
  rcases lt_or_gt_of_ne hne with h | h
  · have hm : min k (α / 2) ≤ α / 2 := min_le_right _ _
    nlinarith
  · have hm : min k (α / 2) = α / 2 := by
      rcases min_cases k (α / 2) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1] at h; linarith
      · exact h1
    rw [hm] at h key ⊢
    nlinarith

/-- For every `q ≠ α/2`, `q(α − q) < (α/2)(α − α/2)`: for `α ≥ 0`, `α/2` is the unique maximizer
of `q(α − q)` on `[0, ∞)`. -/
theorem appendixB_quad_max_Ici (α : ℝ) :
    ∀ q, 0 ≤ q → q ≠ α / 2 → q * (α - q) < α / 2 * (α - α / 2) := by
  intro q _ hne
  have : 0 < (q - α / 2) ^ 2 := by
    have : q - α / 2 ≠ 0 := sub_ne_zero.2 hne
    positivity
  nlinarith

/-- The capacity `k_B = (a − w + r)/3` at point `B`, the intersection of `b(q_E | w)` and
`b(q_I | w + r)` (Figure 12.BB.3). -/
noncomputable def edKB (a w r : ℝ) : ℝ := (a - w + r) / 3

/-- Firm I's stage-3 output after entry, `min{k_I, k_B}`. -/
noncomputable def edQI (a w r k : ℝ) : ℝ := min k (edKB a w r)

/-- Firm E's stage-3 output after entry, `b(q_I | w + r) = (a − w − r − q_I)/2`. -/
noncomputable def edQE (a w r k : ℝ) : ℝ := (a - w - r - edQI a w r k) / 2

/-- Firm I's stage-3 output without entry, `b_I(0 | k_I) = min{k_I, (a − w)/2}`. -/
noncomputable def edQM (a w k : ℝ) : ℝ := min k ((a - w) / 2)

/-- Firm E's stage-3 (gross) profit after entry, given I's capacity `k`. -/
noncomputable def edProfE (a w r k : ℝ) : ℝ := edProfit a (w + r) (edQE a w r k) (edQI a w r k)

/-- The capacity `k_Z = a − w − r − 2√F` at point `Z`, where E's post-entry profit equals `F`
(Figure 12.BB.1). -/
noncomputable def edKZ (a w r F : ℝ) : ℝ := a - w - r - 2 * Real.sqrt F

/-- The capacity `k_π = u(2 + √2)/4` (`u = a − w − r`) of Figure 12.BB.8: the monopoly output
above `b(0 | w + r)` that earns the Stackelberg profit `u²/8`. -/
noncomputable def edKPi (a w r : ℝ) : ℝ := (a - w - r) * (2 + Real.sqrt 2) / 4

/-- Nash equilibrium of the stage-3 quantity game after entry, given I's capacity `k`: I
chooses `q_I ∈ [0, k]` at marginal cost `w`, E chooses `q_E ≥ 0` at marginal cost `w + r`. -/
def IsStage3Nash (a w r k qI qE : ℝ) : Prop :=
  qI ∈ Set.Icc 0 k ∧ 0 ≤ qE ∧ (∀ q ∈ Set.Icc 0 k, edProfit a w q qE ≤ edProfit a w qI qE) ∧
    ∀ q, 0 ≤ q → edProfit a (w + r) q qI ≤ edProfit a (w + r) qE qI

theorem edKB_pos {a w r : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) : 0 < edKB a w r := by
  unfold edKB; linarith

theorem edQI_le {a w r k : ℝ} : edQI a w r k ≤ k := min_le_left _ _

theorem edQI_le_kB {a w r k : ℝ} : edQI a w r k ≤ edKB a w r := min_le_right _ _

theorem edQI_nonneg {a w r k : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) (hk : 0 ≤ k) :
    0 ≤ edQI a w r k := le_min hk (edKB_pos hr hB).le

theorem edQI_of_le {a w r k : ℝ} (h : k ≤ edKB a w r) : edQI a w r k = k := min_eq_left h

theorem edProfE_eq (a w r k : ℝ) : edProfE a w r k = edQE a w r k ^ 2 := by
  unfold edProfE edProfit edQE; ring

/-- Firm I's stage-3 best response after entry in the linear model (Figure 12.BB.2): for
`0 ≤ q_E ≤ a − w` and `k ≥ 0`, the unique best response is `min{k, (a − w − q_E)/2}`. -/
theorem figure_12_BB_2_linear {a w qE k : ℝ} (hqE : qE ≤ a - w) (hk : 0 ≤ k) :
    min k ((a - w - qE) / 2) ∈ Set.Icc 0 k ∧ ∀ q ∈ Set.Icc 0 k, q ≠ min k ((a - w - qE) / 2) →
      edProfit a w q qE < edProfit a w (min k ((a - w - qE) / 2)) qE := by
  have h := appendixB_quad_max (α := a - w - qE) (by linarith) hk
  refine ⟨h.1, fun q hq hne => ?_⟩
  rw [edProfit_eq, edProfit_eq]
  have := h.2 q hq hne
  linarith

/-- **Stage-3 equilibrium after entry; Figure 12.BB.3** (MWG, pp. 424-425). With `r > 0`,
`a − w − 2r > 0` and capacity `k ≥ 0`, the stage-3 game has the unique Nash equilibrium
`q_I = min{k, k_B}`, `q_E = (a − w − r − q_I)/2`. Point `A`, the outcome without first-mover
advantage (both firms at cost `w + r`), is `(u/3, u/3)` with `u = a − w − r`, and point `B`
lies to its right: `k_B > u/3`, with `q_E = (a − w − 2r)/3 < u/3` at `B`. -/
theorem figure_12_BB_3 {a w r k : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) (hk : 0 ≤ k) :
    IsStage3Nash a w r k (edQI a w r k) (edQE a w r k) ∧
    (∀ qI qE, IsStage3Nash a w r k qI qE → qI = edQI a w r k ∧ qE = edQE a w r k) ∧
    (∀ q, 0 ≤ q → edProfit a (w + r) q ((a - w - r) / 3) ≤
        edProfit a (w + r) ((a - w - r) / 3) ((a - w - r) / 3)) ∧
    (a - w - r) / 3 < edKB a w r ∧
    (a - w - r - edKB a w r) / 2 = (a - w - 2 * r) / 3 ∧ (a - w - 2 * r) / 3 < (a - w - r) / 3 := by
  have hKB := edKB_pos hr hB
  have hqI0 := edQI_nonneg hr hB hk
  have hqIk : edQI a w r k ≤ k := edQI_le
  have hqIB : edQI a w r k ≤ edKB a w r := edQI_le_kB
  -- the unique best response of E on `[0, ∞)`
  have hEbr : ∀ qI qE, 0 ≤ qE → qI ≤ a - w - r →
      (∀ q, 0 ≤ q → edProfit a (w + r) q qI ≤ edProfit a (w + r) qE qI) →
      qE = (a - w - r - qI) / 2 := by
    intro qI qE _ hqI h
    by_contra hne
    have := appendixB_quad_max_Ici (a - w - r - qI) qE (by assumption)
      (by intro h'; exact hne (by linarith))
    have h2 := h ((a - w - r - qI) / 2) (by linarith)
    rw [edProfit_eq, edProfit_eq] at h2
    have e : a - (w + r) - qI = a - w - r - qI := by ring
    rw [e] at h2
    linarith
  refine ⟨⟨⟨hqI0, hqIk⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold edQE; unfold edKB at hqIB; linarith
  · -- I's best response
    intro q hq
    have hqE : edQE a w r k ≤ a - w := by unfold edQE; unfold edKB at hqIB; linarith
    have hbr := figure_12_BB_2_linear hqE hk
    have hm : min k ((a - w - edQE a w r k) / 2) = edQI a w r k := by
      unfold edQE edQI edKB
      rcases le_or_gt k ((a - w + r) / 3) with h | h
      · rw [min_eq_left h, min_eq_left]; linarith
      · rw [min_eq_right h.le, min_eq_right] <;> linarith
    rw [hm] at hbr
    rcases eq_or_ne q (edQI a w r k) with rfl | hne
    · exact le_rfl
    · exact (hbr.2 q hq hne).le
  · intro q hq
    have h := appendixB_quad_max_Ici (a - w - r - edQI a w r k)
    rw [edProfit_eq, edProfit_eq]
    have e : a - (w + r) - edQI a w r k = a - w - r - edQI a w r k := by ring
    rw [e]
    unfold edQE
    rcases eq_or_ne q ((a - w - r - edQI a w r k) / 2) with rfl | hne
    · exact le_rfl
    · exact (h q hq hne).le
  · -- uniqueness
    rintro qI qE ⟨⟨hI0, hIk⟩, hE0, hI, hE⟩
    -- step 1: `q_I ≤ u`
    have hqIu : qI ≤ a - w - r := by
      by_contra hgt
      have hgt : a - w - r < qI := lt_of_not_ge hgt
      have hE0' : qE = 0 := by
        by_contra hne
        have hpos : 0 < qE := lt_of_le_of_ne hE0 (Ne.symm hne)
        have := hE 0 le_rfl
        rw [edProfit_eq, edProfit_eq] at this
        nlinarith
      subst hE0'
      have hbr := figure_12_BB_2_linear (a := a) (w := w) (qE := 0) (by linarith) hk
      have hqm : qI = min k ((a - w - 0) / 2) := by
        by_contra hne
        have := hbr.2 qI ⟨hI0, hIk⟩ hne
        have := hI _ hbr.1
        linarith
      have : qI ≤ (a - w - 0) / 2 := hqm ▸ min_le_right _ _
      linarith
    have hqE := hEbr qI qE hE0 hqIu hE
    subst hqE
    have hbr := figure_12_BB_2_linear (a := a) (w := w) (qE := (a - w - r - qI) / 2)
      (by linarith) hk
    have hqm : qI = min k ((a - w - (a - w - r - qI) / 2) / 2) := by
      by_contra hne
      have := hbr.2 qI ⟨hI0, hIk⟩ hne
      have := hI _ hbr.1
      linarith
    have hqI : qI = edQI a w r k := by
      unfold edQI edKB
      rcases min_cases k ((a - w - (a - w - r - qI) / 2) / 2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hqm
        subst hqm
        rw [min_eq_left]; linarith
      · rw [h1] at hqm
        have hv : qI = (a - w + r) / 3 := by linarith
        rw [min_eq_right]
        · exact hv
        · linarith
    refine ⟨hqI, ?_⟩
    unfold edQE; rw [hqI]
  · intro q hq
    have h := appendixB_quad_max_Ici (a - w - r - (a - w - r) / 3)
    rw [edProfit_eq, edProfit_eq]
    have e : a - (w + r) - (a - w - r) / 3 = a - w - r - (a - w - r) / 3 := by ring
    have e2 : (a - w - r) / 3 = (a - w - r - (a - w - r) / 3) / 2 := by ring
    rw [e]
    rcases eq_or_ne q ((a - w - r - (a - w - r) / 3) / 2) with h' | hne
    · rw [h', ← e2]
    · have := h q hq hne
      rw [← e2] at this
      exact this.le
  · unfold edKB; linarith
  · unfold edKB; ring
  · linarith

/-- **Figure 12.BB.3, the reachable points** (MWG, p. 425). By its choice of capacity, firm I
can make the post-entry equilibrium any point of E's best-response function up to `B`: for
every `q ∈ [0, k_B]` the capacity `k = q` yields `(q, (u − q)/2)`; and no capacity yields a
point beyond `B` (`q_I ≤ k_B` always). -/
theorem figure_12_BB_3_range {a w r : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) :
    (∀ q, 0 ≤ q → q ≤ edKB a w r → IsStage3Nash a w r q q ((a - w - r - q) / 2)) ∧
    ∀ k, edQI a w r k ≤ edKB a w r := by
  refine ⟨fun q hq hqB => ?_, fun k => edQI_le_kB⟩
  have h := (figure_12_BB_3 hr hB hq).1
  have e : edQI a w r q = q := edQI_of_le hqB
  unfold edQE at h
  rwa [e] at h

/-- **Figure 12.BB.4** (MWG, p. 425). If I builds capacity `k > k_B`, the post-entry equilibrium
is `B` and I does not use all its capacity (`q_I = k_B < k`); a threat to produce up to
capacity is not credible: producing `k` against E's equilibrium output is strictly worse for I
than producing `k_B`. -/
theorem figure_12_BB_4 {a w r k : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hk : edKB a w r < k) :
    edQI a w r k = edKB a w r ∧ edQI a w r k < k ∧
    edProfit a w k (edQE a w r k) < edProfit a w (edQI a w r k) (edQE a w r k) := by
  have hqI : edQI a w r k = edKB a w r := min_eq_right hk.le
  refine ⟨hqI, by rw [hqI]; exact hk, ?_⟩
  have hk0 : 0 ≤ k := by linarith [edKB_pos hr hB]
  have hqE : edQE a w r k ≤ a - w := by
    unfold edQE; rw [hqI]; unfold edKB; linarith
  have hbr := figure_12_BB_2_linear hqE hk0
  have hm : min k ((a - w - edQE a w r k) / 2) = edQI a w r k := by
    unfold edQE; rw [hqI]; unfold edKB at hk ⊢
    rw [min_eq_right] <;> linarith
  rw [hm] at hbr
  exact hbr.2 k ⟨hk0, le_rfl⟩ (by rw [hqI]; exact ne_of_gt hk)

/-- **Stage-3 outcome without entry** (MWG, p. 425). If E does not enter, I is a monopolist with
capacity `k ≥ 0`, and its unique optimal output is `b_I(0 | k) = min{k, (a − w)/2}`. -/
theorem appendixB_stage3_noEntry {a w k : ℝ} (hw : w < a) (hk : 0 ≤ k) :
    edQM a w k ∈ Set.Icc 0 k ∧
    ∀ q ∈ Set.Icc 0 k, q ≠ edQM a w k → edProfit a w q 0 < edProfit a w (edQM a w k) 0 := by
  have h := figure_12_BB_2_linear (a := a) (w := w) (qE := 0) (by linarith) hk
  simpa [edQM] using h

/-- **Figure 12.BB.1, linear model** (MWG, p. 424). Along E's best response `b(q_I | w + r)`,
E's profit is `((u − q_I)/2)²`, strictly decreasing in `q_I ∈ [0, u]`; for `0 ≤ F` and
`q_I ≤ u`, it is at least `F` iff `q_I ≤ k_Z = u − 2√F`, and it equals `F` at `k_Z`. -/
theorem figure_12_BB_1_linear {a w r F : ℝ} (hF : 0 ≤ F) :
    (∀ q, edProfit a (w + r) ((a - w - r - q) / 2) q = ((a - w - r - q) / 2) ^ 2) ∧
    (∀ q q', q < q' → q' ≤ a - w - r → ((a - w - r - q') / 2) ^ 2 < ((a - w - r - q) / 2) ^ 2) ∧
    (∀ q, q ≤ a - w - r → (F ≤ ((a - w - r - q) / 2) ^ 2 ↔ q ≤ edKZ a w r F)) ∧
    (∀ q, q ≤ a - w - r → (F < ((a - w - r - q) / 2) ^ 2 ↔ q < edKZ a w r F)) ∧
    ((a - w - r - edKZ a w r F) / 2) ^ 2 = F := by
  have hs := Real.sq_sqrt hF
  have hs0 := Real.sqrt_nonneg F
  refine ⟨fun q => by unfold edProfit; ring, fun q q' hq hq' => by nlinarith, fun q hq => ?_,
    fun q hq => ?_, by unfold edKZ; nlinarith⟩
  · unfold edKZ
    constructor
    · intro h
      by_contra hc
      have : (a - w - r - q) / 2 < Real.sqrt F := by linarith
      nlinarith
    · intro h
      have : Real.sqrt F ≤ (a - w - r - q) / 2 := by linarith
      nlinarith
  · unfold edKZ
    constructor
    · intro h
      by_contra hc
      have : (a - w - r - q) / 2 ≤ Real.sqrt F := by linarith
      nlinarith
    · intro h
      have : Real.sqrt F < (a - w - r - q) / 2 := by linarith
      nlinarith

/-- **Stage 2: firm E's entry decision** (MWG, p. 426; also Section 12.G, p. 417). Given I's
capacity `k ≥ 0` and `F ≥ 0`, E's post-entry profit is at least `F` iff the post-entry
equilibrium lies at or to the left of `Z` (`q_I ≤ k_Z`), and exceeds `F` iff it lies strictly to
the left. -/
theorem appendixB_stage2 {a w r F k : ℝ} (hB : 0 < a - w - 2 * r) (hF : 0 ≤ F) :
    (F ≤ edProfE a w r k ↔ edQI a w r k ≤ edKZ a w r F) ∧
    (F < edProfE a w r k ↔ edQI a w r k < edKZ a w r F) := by
  have hu : edQI a w r k ≤ a - w - r := by
    have := edQI_le_kB (a := a) (w := w) (r := r) (k := k); unfold edKB at this; linarith
  have h := figure_12_BB_1_linear (a := a) (w := w) (r := r) hF
  rw [edProfE_eq]
  exact ⟨h.2.2.1 _ hu, h.2.2.2.1 _ hu⟩

/-! ## Stage 1 and the subgame perfect equilibria -/

/-- Firm I's overall profit when it builds capacity `k` and E enters (`true`) or stays out
(`false`), with stage-3 play at the unique stage-3 equilibrium (`figure_12_BB_3`,
`appendixB_stage3_noEntry`). -/
noncomputable def edPayI (a w r k : ℝ) (enter : Bool) : ℝ :=
  cond enter (edProfit a w (edQI a w r k) (edQE a w r k) - r * k)
    (edProfit a w (edQM a w k) 0 - r * k)

/-- E's stage-2 strategy `e` (enter after capacity `k` iff `e k = true`) is optimal in every
stage-2 subgame: E enters when its post-entry profit exceeds `F` and stays out when it falls
short of `F` (either choice is optimal at a tie). -/
def EDEntryOptimal (a w r F : ℝ) (e : ℝ → Bool) : Prop :=
  ∀ k, 0 ≤ k → (F < edProfE a w r k → e k = true) ∧ (edProfE a w r k < F → e k = false)

/-- A subgame perfect Nash equilibrium of the three-stage game: E's entry strategy is optimal
after every capacity, stage 3 is played at its unique equilibrium, and I's capacity `k`
maximizes its overall profit given E's strategy. -/
def IsEDSPNE (a w r F k : ℝ) (e : ℝ → Bool) : Prop :=
  0 ≤ k ∧ EDEntryOptimal a w r F e ∧
    ∀ k', 0 ≤ k' → edPayI a w r k' (e k') ≤ edPayI a w r k (e k)

/-- The book's stage-2 rule (p. 426): E enters iff it expects nonnegative profits net of `F`. -/
noncomputable def edBookRule (a w r F k : ℝ) : Bool := decide (F ≤ edProfE a w r k)

/-- The rule under which E stays out when indifferent. -/
noncomputable def edStayOutRule (a w r F k : ℝ) : Bool := decide (F < edProfE a w r k)

theorem edBookRule_optimal (a w r F : ℝ) : EDEntryOptimal a w r F (edBookRule a w r F) :=
  fun _ _ => ⟨fun h => decide_eq_true h.le, fun h => decide_eq_false (not_le.2 h)⟩

theorem edStayOutRule_optimal (a w r F : ℝ) : EDEntryOptimal a w r F (edStayOutRule a w r F) :=
  fun _ _ => ⟨fun h => decide_eq_true h, fun h => decide_eq_false (not_lt.2 h.le)⟩

theorem edPayI_true_eq (a w r k : ℝ) : edPayI a w r k true =
    edQI a w r k * (a - w - r - edQI a w r k) / 2 - r * (k - edQI a w r k) := by
  change edProfit a w (edQI a w r k) (edQE a w r k) - r * k = _
  unfold edProfit edQE; ring

theorem edPayI_false_eq (a w r k : ℝ) : edPayI a w r k false =
    edQM a w k * (a - w - r - edQM a w k) - r * (k - edQM a w k) := by
  change edProfit a w (edQM a w k) 0 - r * k = _
  unfold edProfit; ring

/-- With entry, I earns at most the Stackelberg profit `u²/8`. -/
theorem edPayI_true_le {a w r k : ℝ} (hr : 0 < r) : edPayI a w r k true ≤ (a - w - r) ^ 2 / 8 := by
  rw [edPayI_true_eq]
  have h1 : edQI a w r k ≤ k := edQI_le
  nlinarith [sq_nonneg (a - w - r - 2 * edQI a w r k), mul_nonneg hr.le (sub_nonneg.2 h1)]

/-- Without entry, I earns at most the monopoly profit `u²/4` of a firm with cost `w + r`. -/
theorem edPayI_false_le {a w r k : ℝ} (hr : 0 < r) :
    edPayI a w r k false ≤ (a - w - r) ^ 2 / 4 := by
  rw [edPayI_false_eq]
  have h1 : edQM a w k ≤ k := min_le_left _ _
  nlinarith [sq_nonneg (a - w - r - 2 * edQM a w k), mul_nonneg hr.le (sub_nonneg.2 h1)]

/-- **Blockaded entry; Figure 12.BB.5** (MWG, p. 426). If E would not enter even when I builds
the uncontested-monopoly capacity `b(0 | w + r) = u/2` (`π_E(u/2) < F`), then I achieves its
best possible outcome: no capacity and entry decision gives more than `u²/4`; for every optimal
entry strategy, `k_I = u/2` with no entry and output `u/2` is an SPNE earning `u²/4`; and every
SPNE has `k_I = u/2` and no entry. -/
theorem figure_12_BB_5 {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hbl : edProfE a w r ((a - w - r) / 2) < F) :
    (∀ k : ℝ, ∀ b : Bool, edPayI a w r k b ≤ (a - w - r) ^ 2 / 4) ∧
    edQM a w ((a - w - r) / 2) = (a - w - r) / 2 ∧
    edPayI a w r ((a - w - r) / 2) false = (a - w - r) ^ 2 / 4 ∧
    (∀ e, EDEntryOptimal a w r F e →
      IsEDSPNE a w r F ((a - w - r) / 2) e ∧ e ((a - w - r) / 2) = false) ∧
    ∀ k e, IsEDSPNE a w r F k e → k = (a - w - r) / 2 ∧ e k = false := by
  have hu : 0 < a - w - r := by linarith
  have hqM : edQM a w ((a - w - r) / 2) = (a - w - r) / 2 := min_eq_left (by linarith)
  have hval : edPayI a w r ((a - w - r) / 2) false = (a - w - r) ^ 2 / 4 := by
    rw [edPayI_false_eq, hqM]; ring
  have hbound : ∀ k : ℝ, ∀ b : Bool, edPayI a w r k b ≤ (a - w - r) ^ 2 / 4 := by
    intro k b
    cases b
    · exact edPayI_false_le hr
    · exact (edPayI_true_le hr).trans (by nlinarith)
  refine ⟨hbound, hqM, hval, fun e he => ?_, fun k e hspne => ?_⟩
  · have hout : e ((a - w - r) / 2) = false := (he _ (by linarith)).2 hbl
    refine ⟨⟨by linarith, he, fun k' _ => ?_⟩, hout⟩
    rw [hout, hval]; exact hbound _ _
  · obtain ⟨_, he, hopt⟩ := hspne
    have hout : e ((a - w - r) / 2) = false := (he _ (by linarith)).2 hbl
    have h := hopt _ (by linarith : (0 : ℝ) ≤ (a - w - r) / 2)
    rw [hout, hval] at h
    cases hek : e k
    · rw [hek, edPayI_false_eq] at h
      have h1 : edQM a w k ≤ k := min_le_left _ _
      have h2 := mul_nonneg hr.le (sub_nonneg.2 h1)
      have hsq : (a - w - r - 2 * edQM a w k) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQM a w k)]
      have hrk : r * (k - edQM a w k) = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQM a w k)]
      have hq : edQM a w k = (a - w - r) / 2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
        linarith
      have hk : k - edQM a w k = 0 := by
        rcases mul_eq_zero.1 hrk with h | h
        · linarith
        · exact h
      exact ⟨by linarith, rfl⟩
    · rw [hek] at h
      have := edPayI_true_le (a := a) (w := w) (k := k) hr
      nlinarith

/-- **Entry inevitable: strategic accommodation; Figure 12.BB.6** (MWG, pp. 426-427). If `Z`
lies to the right of `B` (`π_E(k_B) > F`), E enters after every capacity, and the SPNE
capacity is the Stackelberg output `S = u/2`, or `k_B` if `S` lies to the right of `B`: for
every optimal entry strategy `k_I = min{k_B, u/2}` is an SPNE, every SPNE has this capacity,
and I's profit is `k_I(u − k_I)/2`. -/
theorem figure_12_BB_6 {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hacc : F < edProfE a w r (edKB a w r)) :
    (∀ e, EDEntryOptimal a w r F e → ∀ k, 0 ≤ k → e k = true) ∧
    (∀ e, EDEntryOptimal a w r F e →
      IsEDSPNE a w r F (min (edKB a w r) ((a - w - r) / 2)) e) ∧
    (∀ k e, IsEDSPNE a w r F k e → k = min (edKB a w r) ((a - w - r) / 2)) ∧
    edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true =
      min (edKB a w r) ((a - w - r) / 2) *
        (a - w - r - min (edKB a w r) ((a - w - r) / 2)) / 2 := by
  have hu : 0 < a - w - r := by linarith
  have hKB := edKB_pos hr hB
  have hmono : ∀ k, edProfE a w r (edKB a w r) ≤ edProfE a w r k := by
    intro k
    rw [edProfE_eq, edProfE_eq]
    unfold edQE
    rw [edQI_of_le le_rfl]
    have h1 : edQI a w r k ≤ edKB a w r := edQI_le_kB
    have h2 : edKB a w r ≤ a - w - r := by unfold edKB; linarith
    nlinarith
  have hin : ∀ e, EDEntryOptimal a w r F e → ∀ k, 0 ≤ k → e k = true :=
    fun e he k hk => (he k hk).1 (lt_of_lt_of_le hacc (hmono k))
  obtain ⟨⟨hS0, hSB⟩, hstrict⟩ := appendixB_quad_max (α := a - w - r) hu.le hKB.le
  have hqIS : edQI a w r (min (edKB a w r) ((a - w - r) / 2)) =
      min (edKB a w r) ((a - w - r) / 2) := edQI_of_le hSB
  have hval : edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true =
      min (edKB a w r) ((a - w - r) / 2) * (a - w - r - min (edKB a w r) ((a - w - r) / 2)) /
        2 := by
    rw [edPayI_true_eq, hqIS]; ring
  -- every entry payoff is at most the value at `min{k_B, u/2}`, with equality only there
  have hle : ∀ k, 0 ≤ k → edPayI a w r k true ≤
      edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true ∧
      (edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true ≤ edPayI a w r k true →
        k = min (edKB a w r) ((a - w - r) / 2)) := by
    intro k hk
    have hq0 := edQI_nonneg hr hB hk
    have hqB : edQI a w r k ≤ edKB a w r := edQI_le_kB
    have hqk : edQI a w r k ≤ k := edQI_le
    have hrk := mul_nonneg hr.le (sub_nonneg.2 hqk)
    rw [hval, edPayI_true_eq]
    constructor
    · rcases eq_or_ne (edQI a w r k) (min (edKB a w r) ((a - w - r) / 2)) with h | h
      · rw [h] at hrk ⊢; linarith
      · have := hstrict _ ⟨hq0, hqB⟩ h; linarith
    · intro hge
      have hq : edQI a w r k = min (edKB a w r) ((a - w - r) / 2) := by
        by_contra h
        have := hstrict _ ⟨hq0, hqB⟩ h; linarith
      rw [hq] at hge hrk
      have : r * (k - min (edKB a w r) ((a - w - r) / 2)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
  refine ⟨hin, fun e he => ⟨hS0, he, fun k' hk' => ?_⟩, fun k e hspne => ?_, hval⟩
  · rw [hin e he k' hk', hin e he _ hS0]
    exact (hle k' hk').1
  · obtain ⟨hk, he, hopt⟩ := hspne
    have h := hopt _ hS0
    rw [hin e he k hk, hin e he _ hS0] at h
    exact (hle k hk).2 h

/-- **First-mover advantage at `S`** (MWG, p. 426). If `S` lies (weakly) to the left of `B`,
then at `S` firm I produces `u/2`, E produces `u/4`, I earns `u²/8`, and this is strictly more
than E's net profit `u²/16 − F` (for `F ≥ 0`). -/
theorem figure_12_BB_6_firstMover {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hF : 0 ≤ F) (hS : (a - w - r) / 2 ≤ edKB a w r) :
    edQI a w r ((a - w - r) / 2) = (a - w - r) / 2 ∧
    edQE a w r ((a - w - r) / 2) = (a - w - r) / 4 ∧
    edPayI a w r ((a - w - r) / 2) true = (a - w - r) ^ 2 / 8 ∧
    edProfE a w r ((a - w - r) / 2) - F < edPayI a w r ((a - w - r) / 2) true := by
  have hu : 0 < a - w - r := by linarith
  have hq : edQI a w r ((a - w - r) / 2) = (a - w - r) / 2 := edQI_of_le hS
  have hE : edQE a w r ((a - w - r) / 2) = (a - w - r) / 4 := by unfold edQE; rw [hq]; ring
  have hP : edPayI a w r ((a - w - r) / 2) true = (a - w - r) ^ 2 / 8 := by
    rw [edPayI_true_eq, hq]; ring
  refine ⟨hq, hE, hP, ?_⟩
  rw [hP, edProfE_eq, hE]
  nlinarith

/-- **`S` to the right of `B`** (MWG, pp. 426-427). If `k_B < u/2`, the optimal accommodation
capacity is `k_B` and I's profit there is strictly below the Stackelberg profit `u²/8`. -/
theorem figure_12_BB_6_rightOfB {a w r : ℝ} (hSB : edKB a w r < (a - w - r) / 2) :
    min (edKB a w r) ((a - w - r) / 2) = edKB a w r ∧
    edPayI a w r (edKB a w r) true < (a - w - r) ^ 2 / 8 := by
  refine ⟨min_eq_left hSB.le, ?_⟩
  rw [edPayI_true_eq, edQI_of_le le_rfl]
  have : 0 < (a - w - r - 2 * edKB a w r) ^ 2 := by
    have : a - w - r - 2 * edKB a w r ≠ 0 := by intro h; linarith
    positivity
  nlinarith

/-- **The region where deterrence is possible but not inevitable** (MWG, p. 427): if
`π_E(k_B) < F ≤ π_E(u/2)` (`Z` left of `B`, entry not blockaded), then `F > 0`,
`u/2 ≤ k_B`, and `u/2 ≤ k_Z < k_B ≤ (a − w)/2`. -/
theorem appendixB_deter_region {a w r F : ℝ} (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2)) :
    0 < F ∧ (a - w - r) / 2 ≤ edKB a w r ∧ (a - w - r) / 2 ≤ edKZ a w r F ∧
    edKZ a w r F < edKB a w r ∧ edKB a w r ≤ (a - w) / 2 := by
  have hF : 0 < F := lt_of_le_of_lt (by rw [edProfE_eq]; positivity) hD1
  have hSB : (a - w - r) / 2 ≤ edKB a w r := by
    by_contra h
    have h : edKB a w r < (a - w - r) / 2 := lt_of_not_ge h
    have e1 : edQI a w r ((a - w - r) / 2) = edKB a w r := min_eq_right h.le
    have e2 : edProfE a w r ((a - w - r) / 2) = edProfE a w r (edKB a w r) := by
      rw [edProfE_eq, edProfE_eq]; unfold edQE; rw [e1, edQI_of_le le_rfl]
    linarith
  have h2 := (appendixB_stage2 (k := (a - w - r) / 2) hB hF.le).1.1 hD2
  rw [edQI_of_le hSB] at h2
  have h3 : ¬ edQI a w r (edKB a w r) ≤ edKZ a w r F := fun h =>
    absurd ((appendixB_stage2 (k := edKB a w r) hB hF.le).1.2 h) (not_le.2 hD1)
  rw [edQI_of_le le_rfl] at h3
  exact ⟨hF, hSB, h2, lt_of_not_ge h3, by unfold edKB; linarith⟩

/-- **The linear model never has `S` strictly to the right of `Z` unless entry is blockaded**
(remark to Exercise 12.BB.1). If entry is not blockaded (`F ≤ π_E(u/2)`, `F ≥ 0`) and `S` lies
weakly left of `B`, then `S = u/2 ≤ k_Z`. -/
theorem appendixB_linear_S_le_Z {a w r F : ℝ} (hB : 0 < a - w - 2 * r) (hF : 0 ≤ F)
    (hnb : F ≤ edProfE a w r ((a - w - r) / 2)) (hSB : (a - w - r) / 2 ≤ edKB a w r) :
    (a - w - r) / 2 ≤ edKZ a w r F := by
  have h2 := (appendixB_stage2 (k := (a - w - r) / 2) hB hF).1.1 hnb
  rwa [edQI_of_le hSB] at h2

/-- **Entry in the deterrence region** (MWG, p. 427). Under any optimal entry strategy, E enters
after every capacity `k < k_Z` and stays out after every `k > k_Z` ("a capacity level at least
as large as `k_Z`" deters, up to the tie at `k_Z`). -/
theorem appendixB_deter_entry {a w r F : ℝ} (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    {e : ℝ → Bool} (he : EDEntryOptimal a w r F e) :
    (∀ k, 0 ≤ k → k < edKZ a w r F → e k = true) ∧
    (∀ k, edKZ a w r F < k → e k = false) := by
  obtain ⟨hF, _, hZ, hZB, _⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  refine ⟨fun k hk hkZ => (he k hk).1 ?_, fun k hk => (he k (by linarith)).2 ?_⟩
  · exact (appendixB_stage2 hB hF.le).2.2 (lt_of_le_of_lt edQI_le hkZ)
  · have hq : edKZ a w r F < edQI a w r k := lt_min hk hZB
    by_contra h
    exact absurd ((appendixB_stage2 hB hF.le).1.1 (le_of_not_gt h)) (not_le.2 hq)

/-- No-entry payoffs in the deterrence region: for `k ≥ k_Z`, I's profit without entry is at
most the deterrence profit `k_Z(u − k_Z)`, strictly less if `k > k_Z`, and equal to it at
`k = k_Z`. -/
theorem appendixB_deter_noEntry {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2)) :
    edPayI a w r (edKZ a w r F) false = edKZ a w r F * (a - w - r - edKZ a w r F) ∧
    ∀ k, edKZ a w r F ≤ k →
      edPayI a w r k false ≤ edKZ a w r F * (a - w - r - edKZ a w r F) ∧
      (edKZ a w r F < k → edPayI a w r k false < edKZ a w r F * (a - w - r - edKZ a w r F)) := by
  obtain ⟨_, _, hZ, hZB, hBw⟩ := appendixB_deter_region hB hD1 hD2
  refine ⟨?_, fun k hk => ?_⟩
  · rw [edPayI_false_eq, show edQM a w (edKZ a w r F) = edKZ a w r F from
      min_eq_left (by linarith)]
    ring
  have hqk : edQM a w k ≤ k := min_le_left _ _
  have hqZ : edKZ a w r F ≤ edQM a w k := le_min hk (by linarith)
  have hrk := mul_nonneg hr.le (sub_nonneg.2 hqk)
  rw [edPayI_false_eq]
  refine ⟨by nlinarith, fun hlt => ?_⟩
  have hqZ' : edKZ a w r F < edQM a w k := lt_min hlt (by linarith)
  nlinarith

/-- **Figure 12.BB.8: the capacity `k_π`** (MWG, p. 427). `k_π = u(2 + √2)/4` is the monopoly
output above `u/2` earning exactly the Stackelberg profit `u²/8`; for every `k ≥ u/2`, the
monopoly profit `k(u − k)` exceeds `u²/8` iff `k < k_π` and falls short of it iff `k > k_π`.
So, comparing the deterrence profit `k_Z(u − k_Z)` with the accommodation profit `u²/8`: if
`k_π > k_Z` deterrence is better, and if `k_π < k_Z` accommodation is better. -/
theorem figure_12_BB_8 {a w r k : ℝ} (hu : 0 < a - w - r) (hk : (a - w - r) / 2 ≤ k) :
    edKPi a w r * (a - w - r - edKPi a w r) = (a - w - r) ^ 2 / 8 ∧
    (a - w - r) / 2 < edKPi a w r ∧
    ((a - w - r) ^ 2 / 8 < k * (a - w - r - k) ↔ k < edKPi a w r) ∧
    (k * (a - w - r - k) < (a - w - r) ^ 2 / 8 ↔ edKPi a w r < k) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi : edKPi a w r * (a - w - r - edKPi a w r) = (a - w - r) ^ 2 / 8 := by
    unfold edKPi; nlinarith
  have hgt : (a - w - r) / 2 < edKPi a w r := by
    unfold edKPi; nlinarith
  have key : k * (a - w - r - k) - (a - w - r) ^ 2 / 8 =
      (edKPi a w r - k) * (k + edKPi a w r - (a - w - r)) := by rw [← hpi]; ring
  have hpos : 0 < k + edKPi a w r - (a - w - r) := by linarith
  refine ⟨hpi, hgt, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra h'
    have : (edKPi a w r - k) * (k + edKPi a w r - (a - w - r)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    linarith
  · have := mul_pos (sub_pos.2 h) hpos; linarith
  · by_contra h'
    have : 0 ≤ (edKPi a w r - k) * (k + edKPi a w r - (a - w - r)) :=
      mul_nonneg (by linarith) hpos.le
    linarith
  · have := mul_neg_of_neg_of_pos (sub_neg.2 h) hpos; linarith

/-- **Entry deterrence possible but not inevitable, deterrence optimal; Figures 12.BB.7 and
12.BB.8** (MWG, p. 427). In the region `π_E(k_B) < F ≤ π_E(u/2)`, if `k_Z < k_π`: for every
optimal entry strategy under which E stays out at the tie `k_Z`, capacity `k_Z` (no entry,
output `k_Z`) is an SPNE; every SPNE has capacity `k_Z` and E staying out at `k_Z`; and such
an entry strategy exists (`edStayOutRule`). -/
theorem figure_12_BB_7_deter {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hlt : edKZ a w r F < edKPi a w r) :
    (∀ e, EDEntryOptimal a w r F e → e (edKZ a w r F) = false →
      IsEDSPNE a w r F (edKZ a w r F) e) ∧
    (∀ k e, IsEDSPNE a w r F k e → k = edKZ a w r F ∧ e (edKZ a w r F) = false) ∧
    EDEntryOptimal a w r F (edStayOutRule a w r F) ∧
    edStayOutRule a w r F (edKZ a w r F) = false := by
  obtain ⟨hF, _, hZ, hZB, hBw⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  have hpi := figure_12_BB_8 (k := edKZ a w r F) hu hZ
  have hDA : (a - w - r) ^ 2 / 8 < edKZ a w r F * (a - w - r - edKZ a w r F) := hpi.2.2.1.2 hlt
  obtain ⟨hval, hno⟩ := appendixB_deter_noEntry hr hB hD1 hD2
  have hZ0 : 0 ≤ edKZ a w r F := by linarith
  -- every payoff is at most the deterrence payoff
  have hbound : ∀ e, EDEntryOptimal a w r F e → ∀ k', 0 ≤ k' →
      edPayI a w r k' (e k') ≤ edKZ a w r F * (a - w - r - edKZ a w r F) := by
    intro e he k' hk'
    have hent := appendixB_deter_entry hB hD1 hD2 he
    cases hek : e k'
    · have : edKZ a w r F ≤ k' := by
        by_contra h
        have := hent.1 k' hk' (lt_of_not_ge h)
        rw [hek] at this; exact absurd this (by decide)
      exact (hno k' this).1
    · exact (edPayI_true_le hr).trans hDA.le
  have hout : edStayOutRule a w r F (edKZ a w r F) = false := by
    unfold edStayOutRule
    have h := (figure_12_BB_1_linear (a := a) (w := w) (r := r) hF.le).2.2.2.2
    rw [edProfE_eq]; unfold edQE; rw [edQI_of_le hZB.le, h]
    exact decide_eq_false (lt_irrefl F)
  refine ⟨fun e he hez => ⟨hZ0, he, fun k' hk' => ?_⟩, fun k e hspne => ?_,
    edStayOutRule_optimal a w r F, hout⟩
  · rw [hez, hval]; exact hbound e he k' hk'
  · obtain ⟨hk, he, hopt⟩ := hspne
    have hent := appendixB_deter_entry hB hD1 hD2 he
    -- I's equilibrium payoff is at least the deterrence payoff
    have hge : edKZ a w r F * (a - w - r - edKZ a w r F) ≤ edPayI a w r k (e k) := by
      by_contra hlt'
      have hlt' := lt_of_not_ge hlt'
      have hg : 0 < edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k) := by
        linarith
      have hc : 0 < 2 * edKZ a w r F - (a - w - r) + 2 := by linarith
      obtain ⟨δ, hδ0, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
          δ ≤ (a - w) / 2 - edKZ a w r F ∧ δ * (2 * edKZ a w r F - (a - w - r) + 2) ≤
            edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k) := by
        refine ⟨min (min 1 ((a - w) / 2 - edKZ a w r F))
          ((edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k)) /
            (2 * edKZ a w r F - (a - w - r) + 2)),
          lt_min (lt_min one_pos (by linarith)) (div_pos hg hc),
          (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
          ?_⟩
        have := min_le_right (min 1 ((a - w) / 2 - edKZ a w r F))
          ((edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k)) /
            (2 * edKZ a w r F - (a - w - r) + 2))
        rwa [le_div_iff₀ hc] at this
      have hout' := hent.2 (edKZ a w r F + δ) (by linarith)
      have hqM : edQM a w (edKZ a w r F + δ) = edKZ a w r F + δ := min_eq_left (by linarith)
      have hpay : edPayI a w r (edKZ a w r F + δ) false =
          (edKZ a w r F + δ) * (a - w - r - (edKZ a w r F + δ)) := by
        rw [edPayI_false_eq, hqM]; ring
      have h := hopt (edKZ a w r F + δ) (by linarith)
      rw [hout', hpay] at h
      nlinarith [mul_nonneg hδ0.le (sub_nonneg.2 hδ1)]
    cases hek : e k
    · rw [hek] at hge
      have hkZ : edKZ a w r F ≤ k := by
        by_contra h
        have := hent.1 k hk (lt_of_not_ge h)
        rw [hek] at this; exact absurd this (by decide)
      rcases eq_or_lt_of_le hkZ with h | h
      · subst h; exact ⟨rfl, hek⟩
      · have := (hno k hkZ).2 h; linarith
    · rw [hek] at hge
      have := edPayI_true_le (a := a) (w := w) (k := k) hr
      linarith

/-- **Correction: the book's tie rule.** Under the book's stage-2 rule ("enter if it expects
nonnegative profits", `edBookRule`), which is an optimal entry strategy, E enters at the
capacity `k_Z` itself; hence in the deterrence region with `k_Z < k_π` the three-stage game has
no SPNE in which E follows the book's rule: capacity `k_Z` does not deter, and capacities above
`k_Z` are dominated by smaller ones still above `k_Z`. -/
theorem appendixB_bookRule_no_spne {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hlt : edKZ a w r F < edKPi a w r) :
    EDEntryOptimal a w r F (edBookRule a w r F) ∧ edBookRule a w r F (edKZ a w r F) = true ∧
    ¬ ∃ k, IsEDSPNE a w r F k (edBookRule a w r F) := by
  obtain ⟨hF, _, _, hZB, _⟩ := appendixB_deter_region hB hD1 hD2
  have hin : edBookRule a w r F (edKZ a w r F) = true := by
    unfold edBookRule
    have h := (figure_12_BB_1_linear (a := a) (w := w) (r := r) hF.le).2.2.2.2
    rw [edProfE_eq]; unfold edQE; rw [edQI_of_le hZB.le, h]
    exact decide_eq_true le_rfl
  refine ⟨edBookRule_optimal a w r F, hin, fun ⟨k, hk⟩ => ?_⟩
  have := ((figure_12_BB_7_deter hr hB hD1 hD2 hlt).2.1 k _ hk).2
  rw [hin] at this
  exact absurd this (by decide)

/-- **Entry deterrence possible but not inevitable, accommodation optimal; Figures 12.BB.7 and
12.BB.8** (MWG, p. 427). In the region `π_E(k_B) < F ≤ π_E(u/2)`, if `k_π < k_Z`: for every
optimal entry strategy, the Stackelberg capacity `u/2` with entry is an SPNE, and every SPNE
has capacity `u/2`. -/
theorem figure_12_BB_7_accommodate {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hgt : edKPi a w r < edKZ a w r F) :
    (∀ e, EDEntryOptimal a w r F e →
      IsEDSPNE a w r F ((a - w - r) / 2) e ∧ e ((a - w - r) / 2) = true) ∧
    ∀ k e, IsEDSPNE a w r F k e → k = (a - w - r) / 2 := by
  obtain ⟨hF, hSB, hZ, _, _⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  have hpi := figure_12_BB_8 (k := edKZ a w r F) hu hZ
  have hDA : edKZ a w r F * (a - w - r - edKZ a w r F) < (a - w - r) ^ 2 / 8 :=
    hpi.2.2.2.2 hgt
  have hSZ : (a - w - r) / 2 < edKZ a w r F := lt_trans hpi.2.1 hgt
  obtain ⟨_, hno⟩ := appendixB_deter_noEntry hr hB hD1 hD2
  have hP := (figure_12_BB_6_firstMover hr hB hF.le hSB).2.2.1
  have hS0 : (0 : ℝ) ≤ (a - w - r) / 2 := by linarith
  -- no-entry payoffs fall short of `u²/8`
  have hfalse : ∀ e, EDEntryOptimal a w r F e → ∀ k, 0 ≤ k → e k = false →
      edPayI a w r k false < (a - w - r) ^ 2 / 8 := by
    intro e he k hk hek
    have hkZ : edKZ a w r F ≤ k := by
      by_contra h
      have := (appendixB_deter_entry hB hD1 hD2 he).1 k hk (lt_of_not_ge h)
      rw [hek] at this; exact absurd this (by decide)
    exact lt_of_le_of_lt (hno k hkZ).1 hDA
  refine ⟨fun e he => ?_, fun k e hspne => ?_⟩
  · have hin : e ((a - w - r) / 2) = true :=
      (appendixB_deter_entry hB hD1 hD2 he).1 _ hS0 hSZ
    refine ⟨⟨hS0, he, fun k' hk' => ?_⟩, hin⟩
    rw [hin, hP]
    cases hek : e k'
    · exact (hfalse e he k' hk' hek).le
    · exact edPayI_true_le hr
  · obtain ⟨hk, he, hopt⟩ := hspne
    have hin : e ((a - w - r) / 2) = true :=
      (appendixB_deter_entry hB hD1 hD2 he).1 _ hS0 hSZ
    have h := hopt _ hS0
    rw [hin, hP] at h
    cases hek : e k
    · rw [hek] at h
      have := hfalse e he k hk hek; linarith
    · rw [hek, edPayI_true_eq] at h
      have h1 : edQI a w r k ≤ k := edQI_le
      have h2 := mul_nonneg hr.le (sub_nonneg.2 h1)
      have hsq : (a - w - r - 2 * edQI a w r k) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQI a w r k)]
      have hrk : r * (k - edQI a w r k) = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQI a w r k)]
      have hq : edQI a w r k = (a - w - r) / 2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
        linarith
      rcases mul_eq_zero.1 hrk with h' | h'
      · linarith
      · linarith

/-- Total surplus `∫₀^Q (a − x) dx − cost` when total output is `Q` and total cost is `cost`. -/
noncomputable def edSurplus (a Q cost : ℝ) : ℝ := a * Q - Q ^ 2 / 2 - cost

theorem edSurplus_eq_integral (a Q cost : ℝ) :
    edSurplus a Q cost = (∫ x in (0 : ℝ)..Q, (a - x)) - cost := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  unfold edSurplus; simp only [sub_zero, smul_eq_mul]; ring

/-- **The threat of entry raises output and welfare** (MWG, p. 427). In the deterrence region,
the deterrence output `k_Z` is at least the output `u/2` of a monopolist facing no possible
entry, and total surplus is at least as high; both strictly if `F < π_E(u/2)`. -/
theorem appendixB_deterrence_raises_output {a w r F : ℝ} (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2)) :
    (a - w - r) / 2 ≤ edKZ a w r F ∧
    edSurplus a ((a - w - r) / 2) ((w + r) * ((a - w - r) / 2)) ≤
      edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F) ∧
    (F < edProfE a w r ((a - w - r) / 2) → (a - w - r) / 2 < edKZ a w r F ∧
      edSurplus a ((a - w - r) / 2) ((w + r) * ((a - w - r) / 2)) <
        edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F)) := by
  obtain ⟨hF, hSB, hZ, hZB, _⟩ := appendixB_deter_region hB hD1 hD2
  have hZu : edKZ a w r F ≤ a - w - r := by unfold edKB at hZB; linarith
  have key : edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F) -
      edSurplus a ((a - w - r) / 2) ((w + r) * ((a - w - r) / 2)) =
      (edKZ a w r F - (a - w - r) / 2) * (a - w - r - (edKZ a w r F + (a - w - r) / 2) / 2) := by
    unfold edSurplus; ring
  have hp : 0 < a - w - r - (edKZ a w r F + (a - w - r) / 2) / 2 := by linarith
  refine ⟨hZ, by nlinarith [mul_nonneg (sub_nonneg.2 hZ) hp.le], fun hlt => ?_⟩
  have h := (appendixB_stage2 (k := (a - w - r) / 2) hB hF.le).2.1 hlt
  rw [edQI_of_le hSB] at h
  exact ⟨h, by nlinarith [mul_pos (sub_pos.2 h) hp]⟩

/-- **Exercise 12.BB.2** (MWG, p. 435). If, in the deterrence region, the incumbent is
indifferent between deterring entry (capacity `k_Z`, output `k_Z`, no entry) and
accommodating it (capacity and output `u/2`, E producing `u/4` and paying `F`), then total
surplus is strictly higher under deterrence. (The "discuss generally" part is verbal.) -/
theorem exercise_12_BB_2 {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hind : edPayI a w r (edKZ a w r F) false = edPayI a w r ((a - w - r) / 2) true) :
    edQI a w r ((a - w - r) / 2) = (a - w - r) / 2 ∧
    edQE a w r ((a - w - r) / 2) = (a - w - r) / 4 ∧
    edSurplus a ((a - w - r) / 2 + (a - w - r) / 4)
        ((w + r) * ((a - w - r) / 2) + (w + r) * ((a - w - r) / 4) + F) <
      edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F) := by
  obtain ⟨hF, hSB, hZ, _, _⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  obtain ⟨hq, hE, hP, _⟩ := figure_12_BB_6_firstMover hr hB hF.le hSB
  refine ⟨hq, hE, ?_⟩
  rw [(appendixB_deter_noEntry hr hB hD1 hD2).1, hP] at hind
  have hFz := (figure_12_BB_1_linear (a := a) (w := w) (r := r) hF.le).2.2.2.2
  have h34 : 3 * (a - w - r) / 4 < edKZ a w r F := by
    by_contra h
    have h := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (show edKZ a w r F - 3 * (a - w - r) / 4 ≤ 0 by
      linarith) (show 0 ≤ edKZ a w r F - (a - w - r) / 4 by linarith)]
  unfold edSurplus
  nlinarith [mul_pos hu (sub_pos.2 h34), hFz, hind]

/-! ## Proved parameter instances -/

/-- Instance of the general hypotheses (`appendixB_profit_strictConcave`,
`appendixB_br_antitone`, `figure_12_BB_1`, `figure_12_BB_2`): `p(Q) = 10 − Q` is concave and
strictly decreasing on `[0, ∞)`; with `c = 2`, `b = 4` is a best response to `Q = 0` and
`b' = 3` a best response to `Q' = 2`. -/
theorem appendixB_general_instance :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => 10 - x) ∧ StrictAntiOn (fun x : ℝ => 10 - x) (Set.Ici 0) ∧
    (∀ q : ℝ, 0 ≤ q → q * ((fun x : ℝ => 10 - x) (q + 0) - 2) ≤
      4 * ((fun x : ℝ => 10 - x) (4 + 0) - 2)) ∧
    ∀ q : ℝ, 0 ≤ q → q * ((fun x : ℝ => 10 - x) (q + 2) - 2) ≤
      3 * ((fun x : ℝ => 10 - x) (3 + 2) - 2) := by
  refine ⟨⟨convex_Ici 0, fun x _ y _ a b _ _ hab => ?_⟩, fun x _ y _ hxy => ?_,
    fun q _ => ?_, fun q _ => ?_⟩
  · simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'; nlinarith
  · simp only; linarith
  · nlinarith [sq_nonneg (q - 4)]
  · nlinarith [sq_nonneg (q - 3)]

/-- Instance of the linear-model standing hypotheses and of `figure_12_BB_5` (blockaded entry):
`a = 4`, `w = 0`, `r = 1`, `F = 1` (`π_E(u/2) = 9/16`). -/
theorem figure_12_BB_5_instance :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 4 - 0 - 2 * 1 ∧ edProfE 4 0 1 ((4 - 0 - 1) / 2) < 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simp only [edProfE_eq, edQE, edQI, edKB]
  norm_num [min_def]

/-- Instance of `figure_12_BB_6` (entry inevitable) and `figure_12_BB_6_firstMover`: `a = 4`,
`w = 0`, `r = 1`, `F = 1/4` (`π_E(k_B) = 4/9`; `u/2 = 3/2 ≤ k_B = 5/3`). -/
theorem figure_12_BB_6_instance :
    (1 : ℝ) / 4 < edProfE 4 0 1 (edKB 4 0 1) ∧ ((4 : ℝ) - 0 - 1) / 2 ≤ edKB 4 0 1 := by
  simp only [edProfE_eq, edQE, edQI, edKB]
  norm_num [min_def]

/-- Instance of `figure_12_BB_6_rightOfB`: `a = 10`, `w = 0`, `r = 1` (`k_B = 11/3 < u/2 = 9/2`).
-/
theorem figure_12_BB_6_rightOfB_instance : edKB 10 0 1 < ((10 : ℝ) - 0 - 1) / 2 := by
  unfold edKB; norm_num

/-- Instance of the deterrence region with deterrence optimal (`figure_12_BB_7_deter`,
`appendixB_bookRule_no_spne`, `appendixB_deterrence_raises_output` including its strict part,
`appendixB_linear_S_le_Z`): `a = 4`, `w = 0`, `r = 1`, `F = 49/100`, so `k_Z = 8/5`,
`π_E(k_B) = 4/9 < F < π_E(u/2) = 9/16` and `k_Z < k_π = 3(2 + √2)/4`. -/
theorem figure_12_BB_7_deter_instance :
    edProfE 4 0 1 (edKB 4 0 1) < 49 / 100 ∧ 49 / 100 < edProfE 4 0 1 ((4 - 0 - 1) / 2) ∧
    edKZ 4 0 1 (49 / 100) = 8 / 5 ∧ edKZ 4 0 1 (49 / 100) < edKPi 4 0 1 := by
  have hs : Real.sqrt (49 / 100) = 7 / 10 := by
    rw [show (49 / 100 : ℝ) = (7 / 10) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  have hZ : edKZ 4 0 1 (49 / 100) = 8 / 5 := by unfold edKZ; rw [hs]; norm_num
  refine ⟨?_, ?_, hZ, ?_⟩
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · rw [hZ]; unfold edKPi; nlinarith

/-- Instance of the deterrence region with accommodation optimal
(`figure_12_BB_7_accommodate`): `a = 11/5`, `w = 0`, `r = 1`, `F = 16/2500`, so
`k_Z = 26/25`, `π_E(k_B) = 1/225 < F ≤ π_E(u/2) = 9/100` and `k_π = 3(2 + √2)/10 < k_Z`. -/
theorem figure_12_BB_7_accommodate_instance :
    edProfE (11 / 5) 0 1 (edKB (11 / 5) 0 1) < 16 / 2500 ∧
    16 / 2500 ≤ edProfE (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) ∧
    edKPi (11 / 5) 0 1 < edKZ (11 / 5) 0 1 (16 / 2500) := by
  have hs : Real.sqrt (16 / 2500) = 2 / 25 := by
    rw [show (16 / 2500 : ℝ) = (2 / 25) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  refine ⟨?_, ?_, ?_⟩
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · unfold edKPi edKZ; rw [hs]; nlinarith

/-- Instance of `exercise_12_BB_2` (indifference between deterring and accommodating):
`a = 11/5`, `w = 0`, `r = 1`, `F = (3(2 − √2)/20)²`, so `k_Z = k_π = 3(2 + √2)/10`. -/
theorem exercise_12_BB_2_instance :
    edProfE (11 / 5) 0 1 (edKB (11 / 5) 0 1) < (3 * (2 - Real.sqrt 2) / 20) ^ 2 ∧
    (3 * (2 - Real.sqrt 2) / 20) ^ 2 ≤ edProfE (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) ∧
    edPayI (11 / 5) 0 1 (edKZ (11 / 5) 0 1 ((3 * (2 - Real.sqrt 2) / 20) ^ 2)) false =
      edPayI (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) true := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  have hlt2 : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hgt2 : 7 / 5 < Real.sqrt 2 := by nlinarith
  have hs : Real.sqrt ((3 * (2 - Real.sqrt 2) / 20) ^ 2) = 3 * (2 - Real.sqrt 2) / 20 :=
    Real.sqrt_sq (by linarith)
  have hZ : edKZ (11 / 5) 0 1 ((3 * (2 - Real.sqrt 2) / 20) ^ 2) = (6 + 3 * Real.sqrt 2) / 10 := by
    unfold edKZ; rw [hs]; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]; nlinarith
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]; nlinarith
  · rw [hZ, edPayI_false_eq, edPayI_true_eq]
    have hM : edQM (11 / 5) 0 ((6 + 3 * Real.sqrt 2) / 10) = (6 + 3 * Real.sqrt 2) / 10 :=
      min_eq_left (by linarith)
    have hI : edQI (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) = (11 / 5 - 0 - 1) / 2 :=
      edQI_of_le (by unfold edKB; norm_num)
    rw [hM, hI]
    nlinarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 12.BB.3: entry deterrence by plant proliferation in the linear city

MWG, Exercise 12.BB.3, p. 435, in the linear city of Example 12.C.2 (consumers of mass `M`
uniform on `[0, 1]`, unit demand with value `v`, transport cost `t` per unit distance, marginal
cost `c`, and `v > c + 3t`). Firm I first builds one plant (at an end) or two plants (one at
each end), each costing `F > 0`; then E decides whether to build one plant and at which end;
then the plants compete in prices.

Demand. With prices `m` at end `0` (the lowest price there) and `q` at end `1`, the consumers
buying at end `0` are the `z ∈ [0, 1]` with `m + tz ≤ v` and `m + tz ≤ q + t(1 − z)`, of mass
`M·clamp(min{(v − m)/t, (t + q − m)/(2t)})` (`bb3D`, `clamp x = max 0 (min x 1)`); a plant alone
in the market at end `0` sells `M·clamp((v − m)/t)`; two plants at the same end share their
customers by price, equally at a tie (`bb3ShareE`).

Subgames.
* `exercise_12_BB_3_monopoly_one`: one plant, no entry: the unique optimal price is `v − t`
  (the whole market is served), profit `(v − t − c)M`.
* `exercise_12_BB_3_monopoly_two`: two plants, no entry: the unique optimal prices are
  `v − t/2` at both ends, profit `(v − t/2 − c)M`.
* `exercise_12_BB_3_duopoly`: one plant each at opposite ends: Example 12.C.2 (`example_12_C_2`),
  unique equilibrium `c + t`, profit `tM/2` each.
* `exercise_12_BB_3_coloc_two`, `exercise_12_BB_3_coloc_one`: E's plant at the same end as one of
  I's plants: in every price equilibrium E earns zero (`bb3_coloc_zero`, a Bertrand argument),
  and an equilibrium exists. (E at end `1` against I's two plants is the mirror image
  `z ↦ 1 − z` of E at end `0`.)

Equilibrium (`exercise_12_BB_3`): against two plants E stays out; against one plant E enters at
the far end iff `F < tM/2`. Hence if `F < tM/2`, I builds two plants and E stays out (prices
`v − t/2`); if `F > tM/2`, I builds one plant and E stays out (price `v − t`).

Welfare (`exercise_12_BB_3_welfare`): the transport costs are `tM/2` with one plant and `tM/4`
with plants at both ends (`bb3_transport_one`, `bb3_transport_two`). A monopolist with no
entrant makes the same plant choice (two plants iff `F < tM/2`), so welfare is the same as with
the entrant; if I may build only one plant, then for `F < tM/2` E enters at the other end and
total surplus is again the same (the plant configuration is the same), while consumer surplus
is strictly higher, by `M(v − c − 3t/2)`.

The prices in the opposite-ends duopoly are those of Example 12.C.2 (`lcDemand`, where every
consumer buys); with `v > c + 3t` no consumer facing prices at most `c + 2t` at both ends
prefers not to buy, which is why Example 12.C.2's model applies there.
-/

namespace MWG.MarketPower

/-- `clamp x = max 0 (min x 1)`. -/
noncomputable def bb3Cl (x : ℝ) : ℝ := max 0 (min x 1)

theorem bb3Cl_nonneg (x : ℝ) : 0 ≤ bb3Cl x := le_max_left _ _

theorem bb3Cl_le_one (x : ℝ) : bb3Cl x ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem bb3Cl_mono {x y : ℝ} (h : x ≤ y) : bb3Cl x ≤ bb3Cl y :=
  max_le_max le_rfl (min_le_min_right _ h)

theorem bb3Cl_le_max (x : ℝ) : bb3Cl x ≤ max 0 x := max_le_max le_rfl (min_le_left _ _)

theorem bb3Cl_le_of_pos {x : ℝ} (h : 0 < bb3Cl x) : bb3Cl x ≤ x := by
  unfold bb3Cl at h ⊢
  rcases le_total 0 (min x 1) with h1 | h1
  · rw [max_eq_right h1]; exact min_le_left _ _
  · rw [max_eq_left h1] at h; exact absurd h (lt_irrefl 0)

theorem bb3Cl_lip {x y : ℝ} (h : x ≤ y) : bb3Cl y - bb3Cl x ≤ y - x := by
  unfold bb3Cl
  rcases le_total y 1 with h1 | h1 <;> rcases le_total x 1 with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, h1, h2] <;>
    rcases le_total 0 x with h3 | h3 <;> rcases le_total 0 y with h4 | h4 <;>
    simp only [max_eq_left, max_eq_right, h3, h4, zero_le_one] <;> linarith

theorem bb3Cl_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : bb3Cl x = x := by
  unfold bb3Cl; rw [min_eq_left h1, max_eq_right h0]

/-- Demand at end `0` when the lowest price there is `m` and the price at end `1` is `q`:
`M·clamp(min{(v − m)/t, (t + q − m)/(2t)})`. Demand at end `1` is `bb3D v t M q m`. -/
noncomputable def bb3D (v t M m q : ℝ) : ℝ := M * bb3Cl (min ((v - m) / t) ((t + q - m) / (2 * t)))

/-- E's share of the end-`0` demand `D` when E charges `e` and I's plant there charges `p`. -/
noncomputable def bb3ShareE (e p D : ℝ) : ℝ := if e < p then D else if e = p then D / 2 else 0

theorem bb3ShareE_nonneg {e p D : ℝ} (hD : 0 ≤ D) : 0 ≤ bb3ShareE e p D := by
  unfold bb3ShareE; split_ifs <;> linarith

theorem bb3ShareE_le {e p D : ℝ} (hD : 0 ≤ D) : bb3ShareE e p D ≤ D := by
  unfold bb3ShareE; split_ifs <;> linarith

theorem bb3D_nonneg {v t M m q : ℝ} (hM : 0 ≤ M) : 0 ≤ bb3D v t M m q :=
  mul_nonneg hM (bb3Cl_nonneg _)

theorem bb3D_le {v t M m q : ℝ} (hM : 0 ≤ M) : bb3D v t M m q ≤ M := by
  unfold bb3D; nlinarith [bb3Cl_le_one (min ((v - m) / t) ((t + q - m) / (2 * t)))]

/-- Demand at an end falls with the price there. -/
theorem bb3D_anti {v t M q : ℝ} (ht : 0 < t) (hM : 0 ≤ M) : Antitone (fun m => bb3D v t M m q) := by
  intro m m' h
  simp only [bb3D]
  apply mul_le_mul_of_nonneg_left (bb3Cl_mono (min_le_min _ _)) hM
  · exact div_le_div_of_nonneg_right (by linarith) ht.le
  · exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Demand at end `1` rises with the price at end `0`, with slope at most `M/(2t)`. -/
theorem bb3D_lip {v t M q m m' : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (h : m' ≤ m) :
    bb3D v t M q m' ≤ bb3D v t M q m ∧
      bb3D v t M q m - bb3D v t M q m' ≤ M * (m - m') / (2 * t) := by
  have hB : (t + m' - q) / (2 * t) ≤ (t + m - q) / (2 * t) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hmin : min ((v - q) / t) ((t + m' - q) / (2 * t)) ≤
      min ((v - q) / t) ((t + m - q) / (2 * t)) := min_le_min_left _ hB
  have hdiff : min ((v - q) / t) ((t + m - q) / (2 * t)) -
      min ((v - q) / t) ((t + m' - q) / (2 * t)) ≤ (m - m') / (2 * t) := by
    have e : (t + m - q) / (2 * t) - (t + m' - q) / (2 * t) = (m - m') / (2 * t) := by ring
    rcases min_cases ((v - q) / t) ((t + m - q) / (2 * t)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases min_cases ((v - q) / t) ((t + m' - q) / (2 * t)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] <;> nlinarith [div_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ 2 * t)]
  unfold bb3D
  refine ⟨mul_le_mul_of_nonneg_left (bb3Cl_mono hmin) hM, ?_⟩
  have := bb3Cl_lip hmin
  have e : M * (m - m') / (2 * t) = M * ((m - m') / (2 * t)) := by ring
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (by linarith) hM

/-- **Bertrand competition at a shared location.** Let `D₀(m)` (decreasing, with values in
`[0, M]`) be the demand at an end where E (price `e`) and one of I's plants (price `p`) are
both located, and let `R(m)` be the profit of I's other plants as a function of the lowest
price `m` at that end, with `R(m') ≥ R(m) − L(m − m')` for `m' ≤ m`. If neither E (changing
`e`) nor I (changing `p`) can gain, E's profit is zero. -/
theorem bb3_coloc_zero {D0 R : ℝ → ℝ} {M L c e p : ℝ} (hD0 : Antitone D0)
    (hD0n : ∀ m, 0 ≤ D0 m) (hD0M : ∀ m, D0 m ≤ M) (hL : 0 ≤ L)
    (hR : ∀ m m', m' ≤ m → R m - L * (m - m') ≤ R m')
    (hE : ∀ e', (e' - c) * bb3ShareE e' p (D0 (min e' p)) ≤
      (e - c) * bb3ShareE e p (D0 (min e p)))
    (hI : ∀ p', (p' - c) * (D0 (min e p') - bb3ShareE e p' (D0 (min e p'))) + R (min e p') ≤
      (p - c) * (D0 (min e p) - bb3ShareE e p (D0 (min e p))) + R (min e p)) :
    (e - c) * bb3ShareE e p (D0 (min e p)) = 0 := by
  have hge : 0 ≤ (e - c) * bb3ShareE e p (D0 (min e p)) := by
    have := hE c; rw [sub_self, zero_mul] at this; exact this
  refine le_antisymm ?_ hge
  by_contra hpos
  have hpos : 0 < (e - c) * bb3ShareE e p (D0 (min e p)) := lt_of_not_ge hpos
  have hsn : 0 ≤ bb3ShareE e p (D0 (min e p)) := bb3ShareE_nonneg (hD0n _)
  have hec : 0 < e - c := by
    by_contra h
    have : (e - c) * bb3ShareE e p (D0 (min e p)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hsn
    linarith
  have hs : 0 < bb3ShareE e p (D0 (min e p)) := by
    by_contra h
    have : bb3ShareE e p (D0 (min e p)) = 0 := le_antisymm (le_of_not_gt h) hsn
    rw [this, mul_zero] at hpos; exact lt_irrefl 0 hpos
  have hep : e ≤ p := by
    by_contra h
    have h : p < e := lt_of_not_ge h
    have : bb3ShareE e p (D0 (min e p)) = 0 := by
      unfold bb3ShareE
      simp only [not_lt.2 h.le, ne_of_gt h, ↓reduceIte]
    linarith
  have hm : min e p = e := min_eq_left hep
  rw [hm] at hpos hs hsn hI
  have hold : (p - c) * (D0 e - bb3ShareE e p (D0 e)) =
      (e - c) * (D0 e - bb3ShareE e p (D0 e)) := by
    rcases eq_or_lt_of_le hep with h | h
    · rw [h]
    · have : bb3ShareE e p (D0 e) = D0 e := by unfold bb3ShareE; simp only [h, ↓reduceIte]
      rw [this]; ring
  have hM0 : 0 ≤ M := (hD0n 0).trans (hD0M 0)
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ (e - c) / 2 ∧
      ε * (2 * (M + L + 1)) ≤ (e - c) * bb3ShareE e p (D0 e) := by
    refine ⟨min ((e - c) / 2) ((e - c) * bb3ShareE e p (D0 e) / (2 * (M + L + 1))),
      lt_min (by linarith) (div_pos hpos (by linarith)), min_le_left _ _, ?_⟩
    have := min_le_right ((e - c) / 2) ((e - c) * bb3ShareE e p (D0 e) / (2 * (M + L + 1)))
    rwa [le_div_iff₀ (by linarith)] at this
  have hdev := hI (e - ε)
  have hm' : min e (e - ε) = e - ε := min_eq_right (by linarith)
  have hsh : bb3ShareE e (e - ε) (D0 (e - ε)) = 0 := by
    unfold bb3ShareE
    have h1 : ¬ e < e - ε := by linarith
    have h2 : e ≠ e - ε := by intro h; linarith
    simp only [h1, h2, ↓reduceIte]
  rw [hm', hsh, hold] at hdev
  have hD0e : D0 e ≤ D0 (e - ε) := hD0 (by linarith)
  have hRe : R e - L * ε ≤ R (e - ε) := by
    have := hR e (e - ε) (by linarith)
    rwa [show e - (e - ε) = ε by ring] at this
  have h1 : (e - ε - c) * D0 e ≤ (e - ε - c) * D0 (e - ε) :=
    mul_le_mul_of_nonneg_left hD0e (by linarith)
  have h2 : ε * D0 e ≤ ε * M := mul_le_mul_of_nonneg_left (hD0M e) hε0.le
  have h3 : 0 < ε * (M + L + 1) := mul_pos hε0 (by linarith)
  nlinarith

/-- Profits in the colocation subgame against two plants: E at end `0` (price `e`), I's plants
at end `0` (price `p`) and end `1` (price `q`). -/
noncomputable def bb3ProfitE2 (v t M c e p q : ℝ) : ℝ :=
  (e - c) * bb3ShareE e p (bb3D v t M (min e p) q)

noncomputable def bb3ProfitI2 (v t M c e p q : ℝ) : ℝ :=
  (p - c) * (bb3D v t M (min e p) q - bb3ShareE e p (bb3D v t M (min e p) q)) +
    (q - c) * bb3D v t M q (min e p)

/-- Price equilibrium of the colocation subgame against two plants (I chooses both prices). -/
def IsBB3Coloc2Nash (v t M c e p q : ℝ) : Prop :=
  (∀ e', bb3ProfitE2 v t M c e' p q ≤ bb3ProfitE2 v t M c e p q) ∧
    ∀ p' q', bb3ProfitI2 v t M c e p' q' ≤ bb3ProfitI2 v t M c e p q

/-- Profits in the colocation subgame against one plant: E and I both at end `0`. -/
noncomputable def bb3ProfitE1 (v t M c e p : ℝ) : ℝ :=
  (e - c) * bb3ShareE e p (M * bb3Cl ((v - min e p) / t))

noncomputable def bb3ProfitI1 (v t M c e p : ℝ) : ℝ :=
  (p - c) * (M * bb3Cl ((v - min e p) / t) - bb3ShareE e p (M * bb3Cl ((v - min e p) / t)))

/-- Price equilibrium of the colocation subgame against one plant. -/
def IsBB3Coloc1Nash (v t M c e p : ℝ) : Prop :=
  (∀ e', bb3ProfitE1 v t M c e' p ≤ bb3ProfitE1 v t M c e p) ∧
    ∀ p', bb3ProfitI1 v t M c e p' ≤ bb3ProfitI1 v t M c e p

/-- Pricing below a rival at the same location never earns E a positive profit when E's price
is at most the rival's: `(e − p)·share ≤ 0`. -/
theorem bb3_shareE_profit_le {e p D : ℝ} (hD : 0 ≤ D) : (e - p) * bb3ShareE e p D ≤ 0 := by
  unfold bb3ShareE
  split_ifs with h1 h2
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hD
  · rw [h2, sub_self, zero_mul]
  · rw [mul_zero]

/-- I's plant facing E's price `e` at the same location: `(p − e)·(D − share_E) ≤ 0`. -/
theorem bb3_I_term_le {e p D : ℝ} (hD : 0 ≤ D) : (p - e) * (D - bb3ShareE e p D) ≤ 0 := by
  unfold bb3ShareE
  split_ifs with h1 h2
  · rw [sub_self, mul_zero]
  · rw [h2, sub_self, zero_mul]
  · have : p < e := lt_of_le_of_ne (le_of_not_gt h1) (fun h => h2 h.symm)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- **Exercise 12.BB.3, E next to one of I's two plants** (MWG, p. 435). In every price
equilibrium of the subgame in which E has located at an end where I has a plant (I having
plants at both ends), E's operating profit is zero; and such an equilibrium exists
(`e = p = c`, `q = c + t/2`, I earning `tM/8`). -/
theorem exercise_12_BB_3_coloc_two {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v) :
    (∀ e p q, IsBB3Coloc2Nash v t M c e p q → bb3ProfitE2 v t M c e p q = 0) ∧
    IsBB3Coloc2Nash v t M c c c (c + t / 2) ∧
    bb3ProfitI2 v t M c c c (c + t / 2) = t * M / 8 := by
  have hval : bb3ProfitI2 v t M c c c (c + t / 2) = t * M / 8 := by
    unfold bb3ProfitI2
    rw [sub_self, zero_mul, zero_add, min_self]
    have hmin : min ((v - (c + t / 2)) / t) ((t + c - (c + t / 2)) / (2 * t)) = 1 / 4 := by
      have e : (t + c - (c + t / 2)) / (2 * t) = 1 / 4 := by field_simp; ring
      rw [e, min_eq_right]
      rw [le_div_iff₀ ht]; linarith
    unfold bb3D
    rw [hmin, bb3Cl_of_mem (x := 1 / 4) (by norm_num) (by norm_num)]
    ring
  refine ⟨fun e p q hN => ?_, ⟨fun e' => ?_, fun p' q' => ?_⟩, hval⟩
  · obtain ⟨hE, hI⟩ := hN
    refine bb3_coloc_zero (D0 := fun m => bb3D v t M m q)
      (R := fun m => (q - c) * bb3D v t M q m) (M := M) (L := |q - c| * M / (2 * t))
      (bb3D_anti ht hM.le) (fun _ => bb3D_nonneg hM.le) (fun _ => bb3D_le hM.le)
      (by positivity) ?_ (fun e' => hE e') (fun p' => hI p' q)
    intro m m' hmm
    obtain ⟨h1, h2⟩ := bb3D_lip (v := v) (q := q) ht hM.le hmm
    have h3 : (q - c) * (bb3D v t M q m - bb3D v t M q m') ≤
        |q - c| * (bb3D v t M q m - bb3D v t M q m') :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h4 : |q - c| * (bb3D v t M q m - bb3D v t M q m') ≤ |q - c| * (M * (m - m') / (2 * t)) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have e : |q - c| * M / (2 * t) * (m - m') = |q - c| * (M * (m - m') / (2 * t)) := by ring
    nlinarith
  · unfold bb3ProfitE2
    rw [sub_self, zero_mul]
    exact bb3_shareE_profit_le (bb3D_nonneg hM.le)
  · rw [hval]
    unfold bb3ProfitI2
    have h1 := bb3_I_term_le (e := c) (p := p') (D := bb3D v t M (min c p') q')
      (bb3D_nonneg hM.le)
    have h2 : (q' - c) * bb3D v t M q' (min c p') ≤ t * M / 8 := by
      rcases le_or_gt q' c with hq | hq
      · nlinarith [bb3D_nonneg (v := v) (t := t) (m := q') (q := min c p') hM.le]
      · have hle : bb3D v t M q' (min c p') ≤ M * max 0 ((t + c - q') / (2 * t)) := by
          unfold bb3D
          apply mul_le_mul_of_nonneg_left _ hM.le
          refine (bb3Cl_le_max _).trans (max_le_max le_rfl ((min_le_right _ _).trans ?_))
          exact div_le_div_of_nonneg_right (by linarith [min_le_left c p']) (by linarith)
        have hb : (q' - c) * max 0 ((t + c - q') / (2 * t)) ≤ t / 8 := by
          rcases le_total 0 ((t + c - q') / (2 * t)) with h | h
          · rw [max_eq_right h]
            have e : (q' - c) * ((t + c - q') / (2 * t)) = (q' - c) * (t + c - q') / (2 * t) := by
              ring
            rw [e, div_le_iff₀ (by linarith)]
            nlinarith [sq_nonneg (q' - c - t / 2)]
          · rw [max_eq_left h, mul_zero]; linarith
        have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ q' - c)
        nlinarith
    linarith

/-- **Exercise 12.BB.3, E next to I's single plant** (MWG, p. 435). In every price equilibrium
of the subgame in which E has located at the same end as I's only plant, E's operating profit
is zero (Bertrand); and `e = p = c` is an equilibrium. -/
theorem exercise_12_BB_3_coloc_one {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    (∀ e p, IsBB3Coloc1Nash v t M c e p → bb3ProfitE1 v t M c e p = 0) ∧
    IsBB3Coloc1Nash v t M c c c := by
  have hD : ∀ m, 0 ≤ M * bb3Cl ((v - m) / t) := fun _ => mul_nonneg hM.le (bb3Cl_nonneg _)
  refine ⟨fun e p hN => ?_, fun e' => ?_, fun p' => ?_⟩
  · obtain ⟨hE, hI⟩ := hN
    refine bb3_coloc_zero (D0 := fun m => M * bb3Cl ((v - m) / t)) (R := fun _ => 0) (M := M)
      (L := 0) ?_ hD (fun m => by nlinarith [bb3Cl_le_one ((v - m) / t)]) le_rfl
      (fun _ _ _ => by simp) (fun e' => hE e') (fun p' => by
        have := hI p'; unfold bb3ProfitI1 at this; simpa using this)
    intro m m' h
    exact mul_le_mul_of_nonneg_left (bb3Cl_mono (div_le_div_of_nonneg_right (by linarith) ht.le))
      hM.le
  · unfold bb3ProfitE1
    rw [sub_self, zero_mul]
    exact bb3_shareE_profit_le (hD _)
  · unfold bb3ProfitI1
    rw [sub_self, zero_mul]
    exact bb3_I_term_le (hD _)

/-- **Exercise 12.BB.3, one plant and no entry** (MWG, p. 435). A monopolist with one plant at an
end earns at most `(v − t − c)M`; the price `v − t` (serving the whole market) attains it and is
the unique optimal price. -/
theorem exercise_12_BB_3_monopoly_one {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M)
    (hv : c + 3 * t < v) :
    (∀ p, (p - c) * (M * bb3Cl ((v - p) / t)) ≤ (v - t - c) * M) ∧
    (v - t - c) * (M * bb3Cl ((v - (v - t)) / t)) = (v - t - c) * M ∧
    ∀ p, (p - c) * (M * bb3Cl ((v - p) / t)) = (v - t - c) * M → p = v - t := by
  have key : ∀ p, (p - c) * bb3Cl ((v - p) / t) ≤
      (v - c) * bb3Cl ((v - p) / t) - t * bb3Cl ((v - p) / t) ^ 2 := by
    intro p
    rcases eq_or_lt_of_le (bb3Cl_nonneg ((v - p) / t)) with h | h
    · rw [← h]; ring_nf; exact le_rfl
    · have hx := bb3Cl_le_of_pos h
      rw [le_div_iff₀ ht] at hx
      nlinarith
  have hg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (v - c) * x - t * x ^ 2 ≤ v - t - c := by
    intro x h0 h1
    have : 0 ≤ v - c - t * (1 + x) := by nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) this]
  refine ⟨fun p => ?_, ?_, fun p hp => ?_⟩
  · have := (key p).trans (hg _ (bb3Cl_nonneg _) (bb3Cl_le_one _))
    nlinarith
  · rw [show (v - (v - t)) / t = 1 by field_simp; ring, bb3Cl_of_mem zero_le_one le_rfl]; ring
  · have hp' : (p - c) * bb3Cl ((v - p) / t) = v - t - c := by
      have : M * ((p - c) * bb3Cl ((v - p) / t)) = M * (v - t - c) := by linarith
      exact mul_left_cancel₀ hM.ne' this
    have h0 := bb3Cl_nonneg ((v - p) / t)
    have h1 := bb3Cl_le_one ((v - p) / t)
    have hk := key p
    have hx : bb3Cl ((v - p) / t) = 1 := by
      by_contra hne
      have hlt : bb3Cl ((v - p) / t) < 1 := lt_of_le_of_ne h1 hne
      have : 0 < v - c - t * (1 + bb3Cl ((v - p) / t)) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
      nlinarith [mul_pos (sub_pos.2 hlt) this]
    rw [hx] at hp'
    linarith

/-- **Exercise 12.BB.3, two plants and no entry** (MWG, p. 435). A monopolist with plants at
both ends earns at most `(v − t/2 − c)M`; the prices `v − t/2` at both ends attain it and are
the unique optimal prices. -/
theorem exercise_12_BB_3_monopoly_two {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M)
    (hv : c + 3 * t < v) :
    (∀ p q, (p - c) * bb3D v t M p q + (q - c) * bb3D v t M q p ≤ (v - t / 2 - c) * M) ∧
    (v - t / 2 - c) * bb3D v t M (v - t / 2) (v - t / 2) +
      (v - t / 2 - c) * bb3D v t M (v - t / 2) (v - t / 2) = (v - t / 2 - c) * M ∧
    ∀ p q, (p - c) * bb3D v t M p q + (q - c) * bb3D v t M q p = (v - t / 2 - c) * M →
      p = v - t / 2 ∧ q = v - t / 2 := by
  -- per-plant bound: price at most `v − t·x` when the plant sells `x > 0`
  have hplant : ∀ p q, (p - c) * bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) ≤
      (v - c) * bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) -
        t * bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) ^ 2 := by
    intro p q
    rcases eq_or_lt_of_le (bb3Cl_nonneg (min ((v - p) / t) ((t + q - p) / (2 * t)))) with h | h
    · rw [← h]; ring_nf; exact le_rfl
    · have hx := (bb3Cl_le_of_pos h).trans (min_le_left _ _)
      rw [le_div_iff₀ ht] at hx
      nlinarith
  -- the two plants sell at most the whole market
  have hsum : ∀ p q, bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) +
      bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))) ≤ 1 := by
    intro p q
    rcases eq_or_lt_of_le (bb3Cl_nonneg (min ((v - p) / t) ((t + q - p) / (2 * t)))) with h | h
    · rw [← h, zero_add]; exact bb3Cl_le_one _
    rcases eq_or_lt_of_le (bb3Cl_nonneg (min ((v - q) / t) ((t + p - q) / (2 * t)))) with h' | h'
    · rw [← h', add_zero]; exact bb3Cl_le_one _
    have h1 := (bb3Cl_le_of_pos h).trans (min_le_right _ _)
    have h2 := (bb3Cl_le_of_pos h').trans (min_le_right _ _)
    have e : (t + q - p) / (2 * t) + (t + p - q) / (2 * t) = 1 := by field_simp; ring
    linarith
  -- the slack identity
  have hslack : ∀ x0 x1 : ℝ,
      (v - t / 2 - c) - ((v - c) * x0 - t * x0 ^ 2 + ((v - c) * x1 - t * x1 ^ 2)) =
        t * (x0 - x1) ^ 2 / 2 + (1 - (x0 + x1)) * (v - c - t * (1 + (x0 + x1)) / 2) := by
    intro x0 x1; ring
  refine ⟨fun p q => ?_, ?_, fun p q hpq => ?_⟩
  · have h1 := hplant p q
    have h2 := hplant q p
    have h3 := hsum p q
    have hs := hslack (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))))
      (bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))))
    have h0 := bb3Cl_nonneg (min ((v - p) / t) ((t + q - p) / (2 * t)))
    have h0' := bb3Cl_nonneg (min ((v - q) / t) ((t + p - q) / (2 * t)))
    have hpos : 0 ≤ (1 - (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) +
        bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))))) *
        (v - c - t * (1 + (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) +
          bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))))) / 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hsq := mul_nonneg ht.le (sq_nonneg (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) -
      bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t)))))
    unfold bb3D
    nlinarith
  · have e : min ((v - (v - t / 2)) / t) ((t + (v - t / 2) - (v - t / 2)) / (2 * t)) = 1 / 2 := by
      rw [show (v - (v - t / 2)) / t = 1 / 2 by field_simp; ring,
        show (t + (v - t / 2) - (v - t / 2)) / (2 * t) = 1 / 2 by field_simp; ring, min_self]
    unfold bb3D
    rw [e, bb3Cl_of_mem (by norm_num) (by norm_num)]
    ring
  · set x0 := bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) with hx0
    set x1 := bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))) with hx1
    have h1 := hplant p q
    have h2 := hplant q p
    rw [← hx0] at h1
    rw [← hx1] at h2
    have h3 : x0 + x1 ≤ 1 := hsum p q
    have hs := hslack x0 x1
    have h0 : 0 ≤ x0 := bb3Cl_nonneg _
    have h0' : 0 ≤ x1 := bb3Cl_nonneg _
    have hpq' : (p - c) * x0 + (q - c) * x1 = v - t / 2 - c := by
      unfold bb3D at hpq
      rw [← hx0, ← hx1] at hpq
      have : M * ((p - c) * x0 + (q - c) * x1) = M * (v - t / 2 - c) := by linarith
      exact mul_left_cancel₀ hM.ne' this
    have hA : 0 ≤ (1 - (x0 + x1)) * (v - c - t * (1 + (x0 + x1)) / 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hB : 0 ≤ t * (x0 - x1) ^ 2 / 2 := by positivity
    have hA0 : (1 - (x0 + x1)) * (v - c - t * (1 + (x0 + x1)) / 2) = 0 := by linarith
    have hB0 : t * (x0 - x1) ^ 2 / 2 = 0 := by linarith
    have hs1 : x0 + x1 = 1 := by
      rcases mul_eq_zero.1 hA0 with h | h
      · linarith
      · nlinarith
    have hx01 : x0 = x1 := by
      have : (x0 - x1) ^ 2 = 0 := by
        have := mul_eq_zero.1 (show t * (x0 - x1) ^ 2 = 0 by linarith)
        rcases this with h | h
        · linarith
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    have hx0v : x0 = 1 / 2 := by linarith
    have hx1v : x1 = 1 / 2 := by linarith
    rw [hx0v] at h1
    rw [hx1v] at h2
    rw [hx0v, hx1v] at hpq'
    constructor <;> linarith

/-- **Exercise 12.BB.3, one plant each at opposite ends** (MWG, p. 435; Example 12.C.2): the
unique price equilibrium is `c + t` at both ends, each firm earning `tM/2`. -/
theorem exercise_12_BB_3_duopoly {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    IsLCNash t M c (c + t) (c + t) ∧ lcProfit t M c (c + t) (c + t) = t * M / 2 ∧
    ∀ p1 p2, IsLCNash t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  obtain ⟨h1, _, h3, h4⟩ := example_12_C_2 (c := c) ht hM
  exact ⟨h1, h3, h4⟩

/-- I's overall payoff with one plant, when E enters at the far end iff that is strictly
profitable (`F < tM/2`). -/
noncomputable def bb3PayOne (v t M c F : ℝ) : ℝ :=
  if F < t * M / 2 then t * M / 2 - F else (v - t - c) * M - F

/-- I's overall payoff with two plants (E stays out). -/
noncomputable def bb3PayTwo (v t M c F : ℝ) : ℝ := (v - t / 2 - c) * M - 2 * F

/-- **Exercise 12.BB.3, the equilibrium** (MWG, p. 435). With `t, M, F > 0` and `v > c + 3t`, and
the subgame values above: (i) against two plants E stays out (`0 > 0 − F`, its operating profit
next to an I plant being `0`); (ii) against one plant E's best location is the far end
(`tM/2 − F > 0 − F`), and E enters iff `F < tM/2`; (iii) if `F < tM/2`, I builds two plants
(`bb3PayTwo > bb3PayOne`) and E stays out, prices `v − t/2`; (iv) if `F > tM/2`, I builds one
plant (`bb3PayOne > bb3PayTwo`) and E stays out, price `v − t` (entry is blockaded). -/
theorem exercise_12_BB_3 {v t M c F : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v)
    (hF : 0 < F) :
    0 - F < 0 ∧ 0 - F < t * M / 2 - F ∧
    (F < t * M / 2 → 0 < t * M / 2 - F ∧ bb3PayOne v t M c F < bb3PayTwo v t M c F) ∧
    (t * M / 2 < F → t * M / 2 - F < 0 ∧ bb3PayTwo v t M c F < bb3PayOne v t M c F) := by
  have htm : 0 < t * M := mul_pos ht hM
  refine ⟨by linarith, by linarith, fun h => ⟨by linarith, ?_⟩, fun h => ⟨by linarith, ?_⟩⟩
  · unfold bb3PayOne bb3PayTwo
    simp only [h, ↓reduceIte]
    nlinarith
  · unfold bb3PayOne bb3PayTwo
    simp only [not_lt.2 h.le, ↓reduceIte]
    nlinarith

/-- Total transport cost with one plant at an end serving everyone: `M∫₀¹ tz dz = tM/2`. -/
theorem bb3_transport_one (t M : ℝ) : M * ∫ z in (0 : ℝ)..1, t * z = t * M / 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]; ring

/-- Total transport cost with plants at both ends, each consumer using the nearer plant:
`M∫₀¹ t·min{z, 1 − z} dz = tM/4`. -/
theorem bb3_transport_two (t M : ℝ) : M * ∫ z in (0 : ℝ)..1, t * min z (1 - z) = t * M / 4 := by
  have hc : Continuous (fun z : ℝ => t * min z (1 - z)) :=
    continuous_const.mul (continuous_id.min (continuous_const.sub continuous_id))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ z in (0 : ℝ)..1 / 2, t * min z (1 - z) = ∫ z in (0 : ℝ)..1 / 2, t * z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp only
    rw [min_eq_left (by linarith [hz.2])]
  have h2 : ∫ z in (1 / 2 : ℝ)..1, t * min z (1 - z) = ∫ z in (1 / 2 : ℝ)..1, t * (1 - z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp only
    rw [min_eq_right (by linarith [hz.1])]
  rw [h1, h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Total surplus with every consumer served: gross value minus production, transport and plant
costs, `(v − c)M − T − nF`. -/
noncomputable def bb3Welfare (v M c T F : ℝ) (n : ℕ) : ℝ := (v - c) * M - T - n * F

/-- **Exercise 12.BB.3, welfare comparisons** (MWG, p. 435). (i) With no entrant, a monopolist
builds two plants iff `F < tM/2` (`bb3PayTwo > (v − t − c)M − F`), the same choice as in the
equilibrium with an entrant, so the outcome and total surplus coincide. (ii) If I may build
only one plant and `F < tM/2`, E enters at the far end; total surplus is the same as in the
equilibrium (two plants at the ends, transport cost `tM/4`), while consumer surplus is higher
by `M(v − c − 3t/2) > 0` (prices `c + t` instead of `v − t/2`). -/
theorem exercise_12_BB_3_welfare {v t M c F : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v) :
    ((v - t - c) * M - F < bb3PayTwo v t M c F ↔ F < t * M / 2) ∧
    bb3Welfare v M c (t * M / 4) F 2 = (v - t / 2 - c) * M - 2 * F + t * M / 4 ∧
    bb3Welfare v M c (t * M / 4) F 2 = (t * M / 2 - F) + (t * M / 2 - F) +
      (M * (v - (c + t)) - t * M / 4) ∧
    (M * (v - (c + t)) - t * M / 4) - (M * (v - (v - t / 2)) - t * M / 4) =
      M * (v - c - 3 * t / 2) ∧
    0 < M * (v - c - 3 * t / 2) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_, by ring, mul_pos hM (by linarith)⟩
  · unfold bb3PayTwo at h; nlinarith
  · unfold bb3PayTwo; nlinarith
  · unfold bb3Welfare; push_cast; ring
  · unfold bb3Welfare; push_cast; ring

/-- A proved instance of the hypotheses of the Exercise 12.BB.3 theorems in both regimes:
`t = M = 1`, `c = 0`, `v = 4 > c + 3t`, and `F = 1/4 < tM/2` (two plants) or `F = 1 > tM/2`
(one plant). -/
theorem exercise_12_BB_3_instance :
    (0 : ℝ) < 1 ∧ (0 : ℝ) + 3 * 1 < 4 ∧ (0 : ℝ) < 1 / 4 ∧ (1 : ℝ) / 4 < 1 * 1 / 2 ∧
    (1 : ℝ) * 1 / 2 < 1 := by
  norm_num

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Existence of Cournot equilibrium and quasiconcavity

MWG, Section 12.C, small type on p. 393.

The quantity game has firms `j ∈ ι`, inverse demand `p(·)` and cost functions `c_j(·)`; firm `j`
earns `p(∑ q_k)q_j − c_j(q_j)` (`cournotGenProfit`).

* `smallType_12_C_393`: "with quasiconcavity, we can use Proposition 8.D.3 to show that a pure
  strategy Nash equilibrium necessarily exists". Proposition 8.D.3 needs compact strategy sets,
  so quantities are taken in `[0, B]`; with `p` continuous on `[0, ∞)`, each `c_j` continuous and
  each profit quasiconcave in the firm's own quantity, an equilibrium of the game on `[0, B]`
  exists (Chapter 8's `nash_exists_of_quasiconcave`).
* `smallType_12_C_393_unbounded`: with constant marginal cost `c` and `p(Q) ≤ c` for `Q ≥ B`, the
  equilibrium of the truncated game is a Cournot equilibrium on `[0, ∞)` (`IsCournotNE`).
  `smallType_12_C_393_linear` instantiates it for `p(Q) = a − bQ`.
* `smallType_12_C_393_nonexistence`: "without quasiconcavity ... a pure strategy Nash
  equilibrium of this quantity game may not exist": a duopoly with a convex kinked inverse demand
  and costs that are zero (firm 1) or linear (firm 2) on two output levels and prohibitive
  elsewhere has no pure strategy equilibrium.

Departure: the existence statement adds the compact strategy set `[0, B]` that Proposition 8.D.3
requires (correction 25).
-/

namespace MWG.MarketPower

open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Firm `j`'s profit `p(∑ q_k)q_j − c_j(q_j)` in the Cournot game with cost functions `c_j`
(problem (12.C.1), MWG, p. 390). -/
def cournotGenProfit (p : ℝ → ℝ) (C : ι → ℝ → ℝ) (q : ι → ℝ) (j : ι) : ℝ :=
  p (∑ k, q k) * q j - C j (q j)

/-- **Small type, p. 393** (MWG), via **Proposition 8.D.3**. If quantities lie in `[0, B]`, the
inverse demand is continuous on `[0, ∞)`, the costs are continuous on `[0, B]` and each firm's
profit is quasiconcave in its own quantity, a pure strategy Nash equilibrium exists. -/
theorem smallType_12_C_393 {p : ℝ → ℝ} {C : ι → ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hp : ContinuousOn p (Ici 0)) (hC : ∀ j, ContinuousOn (C j) (Icc 0 B))
    (hqc : ∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 B) →
      QuasiconcaveOn ℝ (Icc 0 B) fun y => cournotGenProfit p C (update q j y) j) :
    ∃ q : ι → ℝ, (∀ k, q k ∈ Icc 0 B) ∧
      ∀ j, ∀ y ∈ Icc 0 B, cournotGenProfit p C (update q j y) j ≤ cournotGenProfit p C q j := by
  have hmem : ∀ q : ι → ℝ, q ∈ Set.pi univ (fun _ : ι => Icc (0 : ℝ) B) ↔ ∀ k, q k ∈ Icc 0 B :=
    fun q => Set.mem_univ_pi
  have hcont : ∀ j, ContinuousOn (fun q : ι → ℝ => cournotGenProfit p C q j)
      (Set.pi univ fun _ : ι => Icc (0 : ℝ) B) := by
    intro j
    unfold cournotGenProfit
    have hsum : ContinuousOn (fun q : ι → ℝ => p (∑ k, q k))
        (Set.pi univ fun _ : ι => Icc (0 : ℝ) B) :=
      hp.comp (continuous_finsetSum _ fun k _ => continuous_apply k).continuousOn
        fun q hq => Finset.sum_nonneg fun k _ => ((hmem q).1 hq k).1
    have hc : ContinuousOn (fun q : ι → ℝ => C j (q j))
        (Set.pi univ fun _ : ι => Icc (0 : ℝ) B) :=
      (hC j).comp (continuous_apply j).continuousOn fun q hq => (hmem q).1 hq j
    exact (hsum.mul (continuous_apply j).continuousOn).sub hc
  obtain ⟨q, hq, hne⟩ := MWG.SimultaneousMoveGames.nash_exists_of_quasiconcave
    (E := fun _ : ι => ℝ) (u := fun j q => cournotGenProfit p C q j)
    (S := fun _ : ι => Icc (0 : ℝ) B) (fun _ => nonempty_Icc.2 hB) (fun _ => isCompact_Icc)
    (fun _ => convex_Icc 0 B) hcont (fun j s hs => hqc j s ((hmem s).1 hs))
  exact ⟨q, (hmem q).1 hq, hne⟩

/-- **Small type, p. 393** (MWG), on the book's strategy sets `[0, ∞)`: with constant marginal
cost `c`, if `p(Q) ≤ c` for `Q ≥ B` then the equilibrium of the game on `[0, B]` is a Cournot
equilibrium (no firm gains by any output `y ≥ 0`). -/
theorem smallType_12_C_393_unbounded {p : ℝ → ℝ} {c B : ℝ} (hB : 0 ≤ B)
    (hp : ContinuousOn p (Ici 0))
    (hqc : ∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 B) →
      QuasiconcaveOn ℝ (Icc 0 B) fun y => cournotProfit p c (update q j y) j)
    (hpB : ∀ Q, B ≤ Q → p Q ≤ c) : ∃ q : ι → ℝ, IsCournotNE p c q := by
  obtain ⟨q, hq, hne⟩ := smallType_12_C_393 (C := fun _ y => c * y) hB hp
    (fun _ => (continuous_const.mul continuous_id).continuousOn) hqc
  refine ⟨q, fun j => (hq j).1, fun j y hy => ?_⟩
  by_cases hyB : y ≤ B
  · exact hne j y ⟨hy, hyB⟩
  · push Not at hyB
    have h0 := hne j 0 ⟨le_rfl, hB⟩
    have hrest : 0 ≤ ∑ k, q k - q j := by
      have := Finset.sum_nonneg (s := Finset.univ) fun k (_ : k ∈ Finset.univ) =>
        (show 0 ≤ update q j 0 k by
          by_cases hk : k = j
          · rw [hk, update_self]
          · rw [update_of_ne hk]; exact (hq k).1)
      rw [sum_update_eq] at this
      linarith
    have hdev : cournotProfit p c (update q j y) j ≤ 0 := by
      unfold cournotProfit
      rw [sum_update_eq, update_self]
      have := hpB (y + (∑ k, q k - q j)) (by linarith)
      nlinarith
    have hzero : cournotGenProfit p (fun _ y => c * y) (update q j 0) j = 0 := by
      unfold cournotGenProfit; rw [update_self]; ring
    have : cournotGenProfit p (fun _ y => c * y) q j = cournotProfit p c q j := rfl
    linarith

/-- The hypotheses of `smallType_12_C_393_unbounded` hold for the linear model
`p(Q) = a − bQ` (`a > c`, `b > 0`) with `B = (a − c)/b`: each profit is concave in own output. -/
theorem smallType_12_C_393_linear {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    0 ≤ (a - c) / b ∧ ContinuousOn (fun Q => a - b * Q) (Ici 0) ∧
    (∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 ((a - c) / b)) →
      QuasiconcaveOn ℝ (Icc 0 ((a - c) / b)) fun y =>
        cournotProfit (fun Q => a - b * Q) c (update q j y) j) ∧
    (∀ Q, (a - c) / b ≤ Q → a - b * Q ≤ c) ∧ ∃ q : ι → ℝ, IsCournotNE (fun Q => a - b * Q) c q := by
  have hB : 0 ≤ (a - c) / b := div_nonneg (by linarith) hb.le
  have hcont : ContinuousOn (fun Q : ℝ => a - b * Q) (Ici 0) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  have hqc : ∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 ((a - c) / b)) →
      QuasiconcaveOn ℝ (Icc 0 ((a - c) / b)) fun y =>
        cournotProfit (fun Q => a - b * Q) c (update q j y) j := by
    intro j q _
    apply ConcaveOn.quasiconcaveOn
    refine ⟨convex_Icc _ _, fun u _ v _ α β hα hβ hαβ => ?_⟩
    simp only [cournotProfit, sum_update_eq, update_self, smul_eq_mul]
    obtain rfl : β = 1 - α := by linarith
    nlinarith [mul_nonneg (mul_nonneg hα hβ) (mul_nonneg hb.le (sq_nonneg (u - v)))]
  have hpB : ∀ Q, (a - c) / b ≤ Q → a - b * Q ≤ c := by
    intro Q hQ
    rw [div_le_iff₀ hb] at hQ
    linarith
  exact ⟨hB, hcont, hqc, hpB, smallType_12_C_393_unbounded hB hcont hqc hpB⟩

/-! ### Nonexistence without quasiconcavity -/

/-- A pure strategy Nash equilibrium of the Cournot game with cost functions `c_j` and
quantities in `[0, ∞)`. -/
def IsCournotGenNE (p : ℝ → ℝ) (C : ι → ℝ → ℝ) (q : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ ∀ j y, 0 ≤ y → cournotGenProfit p C (update q j y) j ≤ cournotGenProfit p C q j

/-- A convex, kinked, strictly decreasing (until it reaches zero) inverse demand. -/
noncomputable def cnxP (Q : ℝ) : ℝ := if Q ≤ 2 then 10 - 4 * Q else max 0 (3 - Q / 2)

/-- Costs: firm `0` produces `1` or `2` at no cost, firm `1` produces `0` or `1` at unit cost
`7/4`; any other output costs `100`. -/
noncomputable def cnxC (j : Fin 2) (y : ℝ) : ℝ :=
  if j = 0 then (if y = 1 ∨ y = 2 then 0 else 100) else (if y = 0 ∨ y = 1 then 7 / 4 * y else 100)

theorem cnxP_rev {y R : ℝ} (hy : 0 ≤ y) (hR : 0 ≤ R) : 0 ≤ cnxP (y + R) * y ∧
    cnxP (y + R) * y ≤ 60 := by
  unfold cnxP
  split_ifs with h
  · constructor <;> nlinarith
  · rcases le_total (3 - (y + R) / 2) 0 with h' | h'
    · rw [max_eq_left h']; simp
    · rw [max_eq_right h']; constructor <;> nlinarith

theorem cournotGenProfit_fin0 (p : ℝ → ℝ) (C : Fin 2 → ℝ → ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit p C (update q 0 y) 0 = p (y + q 1) * y - C 0 y := by
  simp [cournotGenProfit, Fin.sum_univ_two]

theorem cournotGenProfit_fin1 (p : ℝ → ℝ) (C : Fin 2 → ℝ → ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit p C (update q 1 y) 1 = p (q 0 + y) * y - C 1 y := by
  simp [cournotGenProfit, Fin.sum_univ_two]

/-- **Small type, p. 393** (MWG): "without quasiconcavity of these functions, however, a pure
strategy Nash equilibrium of this quantity game may not exist." With the inverse demand `cnxP`
and the costs `cnxC` (whose profits are not quasiconcave), the duopoly has no pure strategy Nash
equilibrium: the best responses cycle `(1, 0) → (1, 1) → (2, 1) → (2, 0) → (1, 0)`. -/
theorem smallType_12_C_393_nonexistence : ¬ ∃ q : Fin 2 → ℝ, IsCournotGenNE cnxP cnxC q := by
  rintro ⟨q, hq0, hne⟩
  have cur0 : cournotGenProfit cnxP cnxC q 0 = cnxP (q 0 + q 1) * q 0 - cnxC 0 (q 0) := by
    simp [cournotGenProfit, Fin.sum_univ_two]
  have cur1 : cournotGenProfit cnxP cnxC q 1 = cnxP (q 0 + q 1) * q 1 - cnxC 1 (q 1) := by
    simp [cournotGenProfit, Fin.sum_univ_two]
  have d0 := fun y hy => hne 0 y hy
  have d1 := fun y hy => hne 1 y hy
  simp only [cournotGenProfit_fin0, cournotGenProfit_fin1, cur0, cur1] at d0 d1
  -- firm 0 produces `1` or `2`
  have h0 : q 0 = 1 ∨ q 0 = 2 := by
    by_contra hn
    have hc : cnxC 0 (q 0) = 100 := by simp [cnxC, hn]
    have := d0 1 zero_le_one
    have hr := cnxP_rev (hq0 0) (hq0 1)
    have hr1 := cnxP_rev zero_le_one (hq0 1)
    have hc1 : cnxC 0 1 = 0 := by simp [cnxC]
    rw [hc, hc1] at this
    linarith [hr.2, hr1.1]
  -- firm 1 produces `0` or `1`
  have h1 : q 1 = 0 ∨ q 1 = 1 := by
    by_contra hn
    have hc : cnxC 1 (q 1) = 100 := by simp [cnxC, hn]
    have := d1 0 le_rfl
    have hr := cnxP_rev (hq0 1) (hq0 0)
    rw [add_comm (q 1)] at hr
    have hc0 : cnxC 1 0 = 0 := by simp [cnxC]
    rw [hc, hc0] at this
    simp only [mul_zero] at this
    linarith [hr.2]
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rw [e0, e1] at d0 d1
  · -- `(1, 0)`: firm 1 gains by producing `1`
    have := d1 1 zero_le_one
    norm_num [cnxP, cnxC] at this
  · -- `(1, 1)`: firm 0 gains by producing `2`
    have := d0 2 zero_le_two
    norm_num [cnxP, cnxC] at this
  · -- `(2, 0)`: firm 0 gains by producing `1`
    have := d0 1 zero_le_one
    norm_num [cnxP, cnxC] at this
  · -- `(2, 1)`: firm 1 gains by producing `0`
    have := d1 0 le_rfl
    norm_num [cnxP, cnxC] at this

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Product differentiation: prices above cost

MWG, Section 12.C, pp. 395-396, and footnote 13.

There are `J > 1` firms with constant marginal cost `c`; firm `j`'s demand `x_j(p_j, p_{-j})` is
continuous, and firm `j` chooses `p_j` to maximize `(p_j − c)x_j(p_j, p̄_{-j})`. Fixing the rivals'
prices, write `f(p) = x_j(p, p̄_{-j})`.

* `diffProducts_profitable`: if `x_j(c, p̄_{-j}) > 0` and `x_j` is continuous in its own price at
  `c`, firm `j` can assure itself a strictly positive profit by setting its price slightly above
  `c`.
* `diffProducts_br_above_cost`: hence every best response is a price strictly above cost.
* `diffProducts_eqm_above_cost`: in every Nash equilibrium in which `x_j(c, p*_{-j}) > 0` for all
  `j`, every equilibrium price exceeds `c`.
* `footnote_12_13`: in the Bertrand model `x_j(p_j, p_{-j})` is discontinuous at
  `p_j = min_{k ≠ j} p_k` whenever demand is positive there.

Departure: demand is taken nonnegative (it is a quantity demanded); without this a "profit"
`(p − c)x` could be positive at `p < c` with negative `x`.
-/

namespace MWG.MarketPower

open Filter Topology Function

/-- **Product differentiation** (MWG, p. 396). If `x_j(c, p̄_{-j}) > 0` and firm `j`'s demand is
continuous in its own price at `c`, some price `p > c` earns a strictly positive profit. -/
theorem diffProducts_profitable {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f c) (hpos : 0 < f c) :
    ∃ p, c < p ∧ 0 < (p - c) * f p := by
  have h1 : ∀ᶠ p in 𝓝[>] c, 0 < f p := nhdsWithin_le_nhds (hf.eventually (lt_mem_nhds hpos))
  have hev : ∀ᶠ p in 𝓝[>] c, 0 < f p ∧ c < p := h1.and self_mem_nhdsWithin
  obtain ⟨p, hp, hcp⟩ := hev.exists
  exact ⟨p, hcp, mul_pos (by linarith) hp⟩

/-- **Product differentiation** (MWG, p. 396). As long as `x_j(c, p̄_{-j}) > 0`, firm `j`'s best
response to `p̄_{-j}` is a price strictly above cost. -/
theorem diffProducts_br_above_cost {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f c) (hpos : 0 < f c)
    (hnn : ∀ p, 0 ≤ f p) {ps : ℝ} (hbr : ∀ p, (p - c) * f p ≤ (ps - c) * f ps) : c < ps := by
  obtain ⟨p, _, hp⟩ := diffProducts_profitable hf hpos
  have h := lt_of_lt_of_le hp (hbr p)
  by_contra hle
  push Not at hle
  have : (ps - c) * f ps ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hnn ps)
  linarith

/-- **Product differentiation** (MWG, p. 396). In a Nash equilibrium `p*` of the simultaneous
price game with demands `x_j(p)` (`x j p`), nonnegative and continuous in own price, if
`x_j(c, p*_{-j}) > 0` for every `j` then every equilibrium price is above cost: "equilibrium
prices will be above the competitive level". -/
theorem diffProducts_eqm_above_cost {ι : Type*} [DecidableEq ι] {x : ι → (ι → ℝ) → ℝ} {c : ℝ}
    {ps : ι → ℝ} (hnn : ∀ j p, 0 ≤ x j p)
    (hcont : ∀ j, ContinuousAt (fun q => x j (update ps j q)) c)
    (hpos : ∀ j, 0 < x j (update ps j c))
    (hne : ∀ j q, (q - c) * x j (update ps j q) ≤ (ps j - c) * x j ps) (j : ι) : c < ps j := by
  refine diffProducts_br_above_cost (f := fun q => x j (update ps j q)) (hcont j) (hpos j)
    (fun p => hnn j _) (fun p => ?_)
  simp only [update_eq_self]
  exact hne j p

/-- The hypotheses of `diffProducts_br_above_cost` are satisfiable: `x(p) = max(0, 1 − p)`,
`c = 1/2`, best response `3/4`. -/
theorem diffProducts_instance :
    ContinuousAt (fun p : ℝ => max 0 (1 - p)) (1 / 2) ∧ 0 < max 0 (1 - (1 / 2 : ℝ)) ∧
    (∀ p : ℝ, 0 ≤ max 0 (1 - p)) ∧
    ∀ p : ℝ, (p - 1 / 2) * max 0 (1 - p) ≤ (3 / 4 - 1 / 2) * max 0 (1 - (3 / 4 : ℝ)) := by
  refine ⟨(continuous_const.max (continuous_const.sub continuous_id)).continuousAt,
    by norm_num, fun p => le_max_left _ _, fun p => ?_⟩
  rw [show max 0 (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num]
  rcases le_total (1 - p) 0 with h | h
  · rw [max_eq_left h]; norm_num
  · rw [max_eq_right h]; nlinarith [sq_nonneg (p - 3 / 4)]

/-- **Footnote 13** (MWG, p. 395). In the Bertrand model firm `j`'s demand `x_j(p_j, p_{-j})` is
discontinuous in `p_j` at `p_j = min_{k ≠ j} p_k = m` whenever `x(m) > 0`: there `j` sells
`x(m)/J̄ > 0`, while at every higher price it sells nothing. -/
theorem footnote_12_13 {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ℝ → ℝ} (p : ι → ℝ) {j k : ι}
    (hkj : k ≠ j) (hmin : ∀ l, l ≠ j → p k ≤ p l) (hxpos : 0 < x (p k)) :
    0 < bertrandSales x (update p j (p k)) j ∧
    (∀ q, p k < q → bertrandSales x (update p j q) j = 0) ∧
    ¬ ContinuousAt (fun q => bertrandSales x (update p j q) j) (p k) := by
  have hval : 0 < bertrandSales x (update p j (p k)) j := by
    unfold bertrandSales
    have hall : ∀ l, p k ≤ update p j (p k) l := by
      intro l
      by_cases hl : l = j
      · rw [hl, update_self]
      · rw [update_of_ne hl]; exact hmin l hl
    simp only [update_self]
    simp only [hall, implies_true, ↓reduceIte]
    apply div_pos hxpos
    exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩
  have hzero : ∀ q, p k < q → bertrandSales x (update p j q) j = 0 := by
    intro q hq
    apply bertrandSales_of_gt (k := k)
    rw [update_self, update_of_ne hkj]; exact hq
  refine ⟨hval, hzero, fun hc => ?_⟩
  have hev : ∀ᶠ q in 𝓝[>] (p k), 0 < bertrandSales x (update p j q) j :=
    nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds hval))
  obtain ⟨q, hq, hqk⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [hzero q hqk] at hq
  exact lt_irrefl _ hq

/-- The hypotheses of `footnote_12_13` are satisfiable: two firms at the price `1`, demand
`x(p) = max(0, 2 − p)`. -/
theorem footnote_12_13_instance :
    (1 : Fin 2) ≠ 0 ∧ (∀ l : Fin 2, l ≠ 0 → (fun _ : Fin 2 => (1 : ℝ)) 1 ≤ (fun _ => 1) l) ∧
      0 < max 0 (2 - (fun _ : Fin 2 => (1 : ℝ)) 1) :=
  ⟨by decide, fun _ _ => le_rfl, by norm_num⟩

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The linear city with nonpurchase

MWG, Example 12.C.2 (pp. 396-398) without the assumption `v > c + 3t`: the small type on p. 398,
Figure 12.C.6(a), and the best-response analysis behind Exercises 12.C.13 and 12.C.14.

A consumer at `z ∈ [0, 1]` buys from firm 1 iff `v − p₁ − tz > 0` and
`p₁ + tz < p₂ + t(1 − z)`, i.e. iff `z < min{(v − p₁)/t, ẑ}` (`lcv_buys_iff`). Firm 1's share of the
`M` consumers is the length of that set, `max{0, min{1, (v − p₁)/t, ẑ}}` (`lcvShare`,
`lcvShare_spec`); firm 2's is `lcvShare v t p₂ p₁`. `lcvProfit` is `(p₁ − c)M·share`.

Firm 1's profit is bounded above, for `p₁ ≥ c`, by `M·max{0, (p₁ − c)L(p₁)}` for each of
`L ∈ {1, (v − p₁)/t, ẑ}` (`lcv_le_one`, `lcv_le_A`, `lcv_le_B`). Combining these bounds gives the
unique best response on each region of the rival's price:

* `lcvBR_low`: `p₂ ≤ c − t`: no price earns a positive profit;
* `lcvBR_duo`: interior duopoly `(t + p₂ + c)/2` (the middle line of (12.C.12));
* `lcvBR_kink`: the kink `2v − t − p₂`, where the indifferent consumer gets zero surplus;
* `lcvBR_mono`: the local monopoly price `(v + c)/2`;
* `lcvBR_cover`: the price `v − t` that just covers the firm's whole side of the market;
* `lcvBR_capture`: the price `p₂ − t` that captures the whole market.

`lcvBRLow` (for `c < v ≤ c + 2t`), `lcvBRMid` (for `c + 2t ≤ v < c + 3t`) and `lcvBRHigh` (for
`v ≥ c + 3t`) assemble these into best-response functions (`lcvBRLow_spec`, `lcvBRMid_spec`,
`lcvBRHigh_spec`), and every Nash equilibrium has both prices at least `c` (`lcvNash_ge_c`).
-/

namespace MWG.MarketPower

open MeasureTheory

/-- Firm 1's share of the market in the linear city with nonpurchase: the length of the set of
consumers `z ∈ [0, 1]` with `z < min{(v − p₁)/t, ẑ}`. -/
noncomputable def lcvShare (v t p1 p2 : ℝ) : ℝ :=
  max 0 (min 1 (min ((v - p1) / t) (lcHat t p1 p2)))

/-- Firm 1's profit `(p₁ − c)M·share` in the linear city with nonpurchase. -/
noncomputable def lcvProfit (v t M c p1 p2 : ℝ) : ℝ := (p1 - c) * (M * lcvShare v t p1 p2)

/-- A Nash equilibrium of the linear city with nonpurchase. -/
def IsLCVNash (v t M c p1 p2 : ℝ) : Prop :=
  (∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c p1 p2) ∧
    ∀ q, lcvProfit v t M c q p1 ≤ lcvProfit v t M c p2 p1

/-- `ps` is the unique best response to `p₂`, and it earns a strictly positive profit. -/
def IsLCVUniqueBR (v t M c p2 ps : ℝ) : Prop :=
  0 < lcvProfit v t M c ps p2 ∧ ∀ p, p ≠ ps → lcvProfit v t M c p p2 < lcvProfit v t M c ps p2

/-- **Figure 12.C.6** (MWG, pp. 396-397). A consumer at `z` buys from firm 1 (positive surplus,
and strictly cheaper than firm 2) iff `z < min{(v − p₁)/t, ẑ}`. -/
theorem lcv_buys_iff {v t p1 p2 z : ℝ} (ht : 0 < t) :
    (0 < v - p1 - t * z ∧ p1 + t * z < p2 + t * (1 - z)) ↔
      z < min ((v - p1) / t) (lcHat t p1 p2) := by
  rw [lt_min_iff, ← linearCity_prefers ht, lt_div_iff₀ ht]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩

/-- The length of `{z ∈ [0, 1] : z < m}` is `max{0, min{1, m}}`. -/
theorem volume_unit_inter_Iio (m : ℝ) :
    volume (Set.Icc (0 : ℝ) 1 ∩ Set.Iio m) = ENNReal.ofReal (max 0 (min 1 m)) := by
  rcases le_or_gt m 1 with h | h
  · have hs : Set.Icc (0 : ℝ) 1 ∩ Set.Iio m = Set.Ico 0 m := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h0, _⟩, hm⟩; exact ⟨h0, hm⟩
      · rintro ⟨h0, hm⟩; exact ⟨⟨h0, by linarith⟩, hm⟩
    rw [hs, Real.volume_Ico, sub_zero, min_eq_right h]
    rcases le_total m 0 with h0 | h0
    · rw [max_eq_left h0, ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_zero]
    · rw [max_eq_right h0]
  · have hs : Set.Icc (0 : ℝ) 1 ∩ Set.Iio m = Set.Icc 0 1 := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio]
      constructor
      · rintro ⟨hz, _⟩; exact hz
      · rintro ⟨h0, h1⟩; exact ⟨⟨h0, h1⟩, by linarith⟩
    rw [hs, Real.volume_Icc, sub_zero, min_eq_left h.le, max_eq_right zero_le_one]

/-- **Firm 1's demand with nonpurchase** (MWG, pp. 396-397): the set of consumers buying from
firm 1, `{z ∈ [0, 1] : z < min{(v − p₁)/t, ẑ}}`, has length `lcvShare v t p₁ p₂`. -/
theorem lcvShare_spec (v t p1 p2 : ℝ) :
    volume (Set.Icc (0 : ℝ) 1 ∩ Set.Iio (min ((v - p1) / t) (lcHat t p1 p2))) =
      ENNReal.ofReal (lcvShare v t p1 p2) :=
  volume_unit_inter_Iio _

/-- Firm 2's indifferent-consumer share is `1 − ẑ`. -/
theorem lcHat_symm {t p1 p2 : ℝ} (ht : 0 < t) : lcHat t p2 p1 = 1 - lcHat t p1 p2 := by
  unfold lcHat; field_simp; ring

theorem lcvShare_nonneg (v t p1 p2 : ℝ) : 0 ≤ lcvShare v t p1 p2 := le_max_left _ _

/-- Computing the share: if `s ∈ [0, 1]` is at most `(v − p₁)/t` and `ẑ` and equals one of
`1, (v − p₁)/t, ẑ`, the share is `s`. -/
theorem lcvShare_eq_of {v t p1 p2 s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hA : s ≤ (v - p1) / t)
    (hB : s ≤ lcHat t p1 p2) (hatt : s = 1 ∨ s = (v - p1) / t ∨ s = lcHat t p1 p2) :
    lcvShare v t p1 p2 = s := by
  unfold lcvShare
  have hmin : min 1 (min ((v - p1) / t) (lcHat t p1 p2)) = s := by
    refine le_antisymm ?_ (le_min hs1 (le_min hA hB))
    rcases hatt with h | h | h
    · rw [← h]; exact min_le_left _ _
    · rw [h]; exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [h]; exact (min_le_right _ _).trans (min_le_right _ _)
  rw [hmin, max_eq_right hs0]

/-- The share is zero when `ẑ ≤ 0`. -/
theorem lcvShare_eq_zero {v t p1 p2 : ℝ} (h : lcHat t p1 p2 ≤ 0) : lcvShare v t p1 p2 = 0 := by
  unfold lcvShare
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans h))

/-- A firm pricing below cost earns at most zero. -/
theorem lcv_le_zero_of_lt {v t M c p p2 : ℝ} (hM : 0 ≤ M) (h : p < c) :
    lcvProfit v t M c p p2 ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hM (lcvShare_nonneg _ _ _ _))

theorem lcv_mul_le {a s L : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hsL : s ≤ max 0 L) :
    a * s ≤ max 0 (a * L) := by
  rcases le_total L 0 with h | h
  · rw [max_eq_left h] at hsL
    rw [le_antisymm hsL hs, mul_zero]; exact le_max_left _ _
  · rw [max_eq_right h] at hsL
    exact (mul_le_mul_of_nonneg_left hsL ha).trans (le_max_right _ _)

theorem lcv_le_of_share {v t M c p p2 L : ℝ} (hM : 0 ≤ M) (hp : c ≤ p)
    (hL : lcvShare v t p p2 ≤ max 0 L) : lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * L) := by
  unfold lcvProfit
  have := lcv_mul_le (sub_nonneg.2 hp) (lcvShare_nonneg v t p p2) hL
  calc (p - c) * (M * lcvShare v t p p2) = M * ((p - c) * lcvShare v t p p2) := by ring
    _ ≤ M * max 0 ((p - c) * L) := mul_le_mul_of_nonneg_left this hM

/-- Bound by the full-coverage piece `L = 1`. -/
theorem lcv_le_one {v t M c p p2 : ℝ} (hM : 0 ≤ M) (hp : c ≤ p) :
    lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * 1) :=
  lcv_le_of_share hM hp (max_le_max le_rfl (min_le_left _ _))

/-- Bound by the local-monopoly piece `L = (v − p)/t`. -/
theorem lcv_le_A {v t M c p p2 : ℝ} (hM : 0 ≤ M) (hp : c ≤ p) :
    lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * ((v - p) / t)) :=
  lcv_le_of_share hM hp (max_le_max le_rfl ((min_le_right _ _).trans (min_le_left _ _)))

/-- Bound by the duopoly piece `L = ẑ`. -/
theorem lcv_le_B {v t M c p p2 : ℝ} (hM : 0 ≤ M) (hp : c ≤ p) :
    lcvProfit v t M c p p2 ≤ M * max 0 ((p - c) * lcHat t p p2) :=
  lcv_le_of_share hM hp (max_le_max le_rfl ((min_le_right _ _).trans (min_le_right _ _)))

/-- The unique best response from the piecewise bounds. -/
theorem lcv_uniqueBR_of {v t M c p2 ps T : ℝ} (hM : 0 < M) (hT : 0 < T)
    (hval : lcvProfit v t M c ps p2 = M * T)
    (hb : ∀ p, c ≤ p → p ≠ ps →
      (p - c) * 1 < T ∨ (p - c) * ((v - p) / t) < T ∨ (p - c) * lcHat t p p2 < T) :
    IsLCVUniqueBR v t M c p2 ps := by
  refine ⟨by rw [hval]; positivity, fun p hp => ?_⟩
  rw [hval]
  rcases lt_or_ge p c with h | h
  · exact lt_of_le_of_lt (lcv_le_zero_of_lt hM.le h) (by positivity)
  · rcases hb p h hp with h1 | h1 | h1
    · exact lt_of_le_of_lt (lcv_le_one hM.le h)
        (mul_lt_mul_of_pos_left (max_lt hT h1) hM)
    · exact lt_of_le_of_lt (lcv_le_A hM.le h)
        (mul_lt_mul_of_pos_left (max_lt hT h1) hM)
    · exact lt_of_le_of_lt (lcv_le_B hM.le h)
        (mul_lt_mul_of_pos_left (max_lt hT h1) hM)

/-- A unique best response is the only maximizer. -/
theorem lcv_eq_of_uniqueBR {v t M c p2 ps p1 : ℝ} (h : IsLCVUniqueBR v t M c p2 ps)
    (hmax : ∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c p1 p2) : p1 = ps := by
  by_contra hne
  linarith [h.2 p1 hne, hmax ps]

theorem lcv_max_of_uniqueBR {v t M c p2 ps : ℝ} (h : IsLCVUniqueBR v t M c p2 ps) :
    ∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c ps p2 := fun q => by
  by_cases hq : q = ps
  · rw [hq]
  · exact (h.2 q hq).le

/-- Two unique best responses to each other form a Nash equilibrium. -/
theorem lcvNash_of_BR {v t M c p1 p2 : ℝ} (h1 : IsLCVUniqueBR v t M c p2 p1)
    (h2 : IsLCVUniqueBR v t M c p1 p2) : IsLCVNash v t M c p1 p2 :=
  ⟨lcv_max_of_uniqueBR h1, lcv_max_of_uniqueBR h2⟩

/-! ### Best responses on the regions of the rival's price -/

/-- **Best response, `p₂ ≤ c − t`** (MWG, (12.C.12), with nonpurchase). No price earns a positive
profit; the price `c` earns zero. -/
theorem lcvBR_low {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h : p2 ≤ c - t) :
    lcvProfit v t M c c p2 = 0 ∧ ∀ p, lcvProfit v t M c p p2 ≤ 0 := by
  refine ⟨by unfold lcvProfit; ring, fun p => ?_⟩
  rcases lt_or_ge p c with hp | hp
  · exact lcv_le_zero_of_lt hM.le hp
  · refine (lcv_le_B hM.le hp).trans ?_
    have : lcHat t p p2 ≤ 0 := by
      unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by linarith) this), mul_zero]

/-- **Best response, interior duopoly** (MWG, (12.C.12), middle line). If `c − t < p₂ < c + 3t`
and `3p₂ ≤ 4v − 3t − c` (the indifferent consumer then gets positive surplus), the unique best
response is `(t + p₂ + c)/2`, with share `(t + p₂ − c)/(4t)`. -/
theorem lcvBR_duo {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p2)
    (h2 : p2 < c + 3 * t) (h3 : 3 * p2 ≤ 4 * v - 3 * t - c) :
    lcvShare v t ((t + p2 + c) / 2) p2 = (t + p2 - c) / (4 * t) ∧
      IsLCVUniqueBR v t M c p2 ((t + p2 + c) / 2) := by
  have hs : lcvShare v t ((t + p2 + c) / 2) p2 = (t + p2 - c) / (4 * t) := by
    apply lcvShare_eq_of
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity)]; linarith
    · rw [div_le_div_iff₀ (by positivity) ht]; nlinarith
    · unfold lcHat; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    · right; right; unfold lcHat; field_simp; ring
  refine ⟨hs, lcv_uniqueBR_of (T := (t + p2 - c) ^ 2 / (8 * t)) hM
    (div_pos (pow_pos (by linarith) 2) (by positivity)) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; field_simp; ring
  · right; right
    have key : (t + p2 - c) ^ 2 / (8 * t) - (p - c) * lcHat t p p2 =
        (p - (t + p2 + c) / 2) ^ 2 / (2 * t) := by unfold lcHat; field_simp; ring
    have hne : p - (t + p2 + c) / 2 ≠ 0 := sub_ne_zero.2 hp
    have : 0 < (p - (t + p2 + c) / 2) ^ 2 / (2 * t) := by positivity
    linarith

/-- **Best response at the kink** (MWG, p. 398 small type). If `v − t < p₂ ≤ v`,
`(v + c)/2 ≤ α ≤ (t + p₂ + c)/2`, where `α = 2v − t − p₂`, the unique best response is
`α`: the indifferent consumer `ẑ` gets zero surplus. The share is `(p₂ + t − v)/t`. -/
theorem lcvBR_kink {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : v - t < p2) (h2 : p2 ≤ v)
    (h3 : v + c ≤ 2 * (2 * v - t - p2)) (h4 : 2 * (2 * v - t - p2) ≤ t + p2 + c) :
    lcvShare v t (2 * v - t - p2) p2 = (p2 + t - v) / t ∧
      IsLCVUniqueBR v t M c p2 (2 * v - t - p2) := by
  have eA : (v - (2 * v - t - p2)) / t = (p2 + t - v) / t := by congr 1; ring
  have eB : lcHat t (2 * v - t - p2) p2 = (p2 + t - v) / t := by unfold lcHat; field_simp; ring
  have hs : lcvShare v t (2 * v - t - p2) p2 = (p2 + t - v) / t := by
    apply lcvShare_eq_of
    · exact div_nonneg (by linarith) ht.le
    · rw [div_le_one ht]; linarith
    · rw [eA]
    · rw [eB]
    · right; left; rw [eA]
  refine ⟨hs, lcv_uniqueBR_of (T := (2 * v - t - p2 - c) * ((p2 + t - v) / t)) hM
    (mul_pos (by linarith) (div_pos (by linarith) ht)) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; ring
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · right; right
      have key : (2 * v - t - p2 - c) * ((p2 + t - v) / t) - (p - c) * lcHat t p p2 =
          (2 * v - t - p2 - p) * (t + p2 + c - (2 * v - t - p2) - p) / (2 * t) := by
        unfold lcHat; field_simp; ring
      have : 0 < (2 * v - t - p2 - p) * (t + p2 + c - (2 * v - t - p2) - p) / (2 * t) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
      linarith
    · right; left
      have key : (2 * v - t - p2 - c) * ((p2 + t - v) / t) - (p - c) * ((v - p) / t) =
          (p - (2 * v - t - p2)) * (p + (2 * v - t - p2) - v - c) / t := by
        field_simp; ring
      have : 0 < (p - (2 * v - t - p2)) * (p + (2 * v - t - p2) - v - c) / t :=
        div_pos (mul_pos (by linarith) (by linarith)) ht
      linarith

/-- **Best response, local monopoly** (MWG, p. 398 small type). If `c < v ≤ c + 2t` and
`2p₂ ≥ 3v − 2t − c`, the unique best response is `(v + c)/2`, with share `(v − c)/(2t)`: the
firm's market area does not reach the indifferent consumer. -/
theorem lcvBR_mono {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hv : v ≤ c + 2 * t) (h : 3 * v - 2 * t - c ≤ 2 * p2) :
    lcvShare v t ((v + c) / 2) p2 = (v - c) / (2 * t) ∧
      IsLCVUniqueBR v t M c p2 ((v + c) / 2) := by
  have eA : (v - (v + c) / 2) / t = (v - c) / (2 * t) := by field_simp; ring
  have hs : lcvShare v t ((v + c) / 2) p2 = (v - c) / (2 * t) := by
    apply lcvShare_eq_of
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity)]; linarith
    · rw [eA]
    · unfold lcHat; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    · right; left; rw [eA]
  refine ⟨hs, lcv_uniqueBR_of (T := (v - c) ^ 2 / (4 * t)) hM
    (div_pos (pow_pos (by linarith) 2) (by positivity)) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; field_simp; ring
  · right; left
    have key : (v - c) ^ 2 / (4 * t) - (p - c) * ((v - p) / t) = (p - (v + c) / 2) ^ 2 / t := by
      field_simp; ring
    have hne : p - (v + c) / 2 ≠ 0 := sub_ne_zero.2 hp
    have : 0 < (p - (v + c) / 2) ^ 2 / t := by positivity
    linarith

/-- **Best response, covering the market** (MWG, p. 398). If `v ≥ c + 2t` and `p₂ ≥ v`, the unique
best response is `v − t`, at which every consumer buys from the firm (share `1`). -/
theorem lcvBR_cover {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 2 * t ≤ v)
    (h : v ≤ p2) : lcvShare v t (v - t) p2 = 1 ∧ IsLCVUniqueBR v t M c p2 (v - t) := by
  have eA : (v - (v - t)) / t = 1 := by field_simp; ring
  have hs : lcvShare v t (v - t) p2 = 1 := by
    apply lcvShare_eq_of zero_le_one le_rfl (by rw [eA])
    · unfold lcHat; rw [le_div_iff₀ (by positivity)]; linarith
    · left; rfl
  refine ⟨hs, lcv_uniqueBR_of (T := v - t - c) hM (by linarith) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; ring
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · left; linarith
    · right; left
      have key : v - t - c - (p - c) * ((v - p) / t) = (p - (v - t)) * (p - (c + t)) / t := by
        field_simp; ring
      have : 0 < (p - (v - t)) * (p - (c + t)) / t :=
        div_pos (mul_pos (by linarith) (by linarith)) ht
      linarith

/-- **Best response, capturing the market** (MWG, (12.C.12), last line). If
`c + 3t ≤ p₂ ≤ v`, the unique best response is `p₂ − t`, capturing every consumer. -/
theorem lcvBR_capture {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c + 3 * t ≤ p2)
    (h2 : p2 ≤ v) : lcvShare v t (p2 - t) p2 = 1 ∧ IsLCVUniqueBR v t M c p2 (p2 - t) := by
  have eB : lcHat t (p2 - t) p2 = 1 := by unfold lcHat; field_simp; ring
  have hs : lcvShare v t (p2 - t) p2 = 1 := by
    apply lcvShare_eq_of zero_le_one le_rfl _ (by rw [eB])
    · right; right; rw [eB]
    · rw [le_div_iff₀ ht]; linarith
  refine ⟨hs, lcv_uniqueBR_of (T := p2 - t - c) hM (by linarith) ?_ fun p _ hp => ?_⟩
  · unfold lcvProfit; rw [hs]; ring
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · left; linarith
    · right; right
      have key : p2 - t - c - (p - c) * lcHat t p p2 =
          (p - (p2 - t)) * (p - (2 * t + c)) / (2 * t) := by
        unfold lcHat; field_simp; ring
      have : 0 < (p - (p2 - t)) * (p - (2 * t + c)) / (2 * t) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
      linarith

/-! ### Best-response functions and equilibrium prices above cost -/

/-- The best-response function for `c < v ≤ c + 2t` and `p₂ > c − t`: interior duopoly, kink,
local monopoly. -/
noncomputable def lcvBRLow (v t c p2 : ℝ) : ℝ :=
  if 3 * p2 ≤ 4 * v - 3 * t - c then (t + p2 + c) / 2
  else if 2 * p2 ≤ 3 * v - 2 * t - c then 2 * v - t - p2 else (v + c) / 2

/-- The best-response function for `c + 2t ≤ v < c + 3t` and `p₂ > c − t`: interior duopoly,
kink, covering the market. -/
noncomputable def lcvBRMid (v t c p2 : ℝ) : ℝ :=
  if 3 * p2 ≤ 4 * v - 3 * t - c then (t + p2 + c) / 2 else if p2 ≤ v then 2 * v - t - p2 else v - t

/-- The best-response function for `v ≥ c + 3t` and `p₂ > c − t`: interior duopoly, capturing
the market, covering the market. For `p₂ ≤ v` it is (12.C.12). -/
noncomputable def lcvBRHigh (v t c p2 : ℝ) : ℝ :=
  if p2 < c + 3 * t then (t + p2 + c) / 2 else if p2 ≤ v then p2 - t else v - t

/-- `lcvBRLow` is the unique best response when `c < v ≤ c + 2t` and `p₂ > c − t`. -/
theorem lcvBRLow_spec {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hv : v ≤ c + 2 * t) (hp2 : c - t < p2) : IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2) := by
  unfold lcvBRLow
  split_ifs with h1 h2
  · exact (lcvBR_duo ht hM hp2 (by linarith) h1).2
  · exact (lcvBR_kink ht hM (by linarith) (by linarith) (by linarith) (by linarith)).2
  · exact (lcvBR_mono ht hM hcv hv (by linarith)).2

/-- `lcvBRMid` is the unique best response when `c + 2t ≤ v < c + 3t` and `p₂ > c − t`. -/
theorem lcvBRMid_spec {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + 2 * t ≤ v)
    (hv2 : v < c + 3 * t) (hp2 : c - t < p2) : IsLCVUniqueBR v t M c p2 (lcvBRMid v t c p2) := by
  unfold lcvBRMid
  split_ifs with h1 h2
  · exact (lcvBR_duo ht hM hp2 (by linarith) h1).2
  · exact (lcvBR_kink ht hM (by linarith) h2 (by linarith) (by linarith)).2
  · exact (lcvBR_cover ht hM hv1 (by linarith)).2

/-- `lcvBRHigh` is the unique best response when `v ≥ c + 3t` and `p₂ > c − t`. -/
theorem lcvBRHigh_spec {v t M c p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t ≤ v)
    (hp2 : c - t < p2) : IsLCVUniqueBR v t M c p2 (lcvBRHigh v t c p2) := by
  unfold lcvBRHigh
  split_ifs with h1 h2
  · exact (lcvBR_duo ht hM hp2 h1 (by linarith)).2
  · exact (lcvBR_capture ht hM (by linarith) h2).2
  · exact (lcvBR_cover ht hM (by linarith) (by linarith)).2

/-- A firm pricing below cost with a nonnegative profit sells nothing, so its rival's price is at
most its own minus `t`. -/
theorem lcv_rival_low {v t M c p p' : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v) (hp : p < c)
    (h0 : 0 ≤ lcvProfit v t M c p p') : p' ≤ p - t := by
  unfold lcvProfit at h0
  have hs : lcvShare v t p p' ≤ 0 := by
    by_contra h; push Not at h
    have : (p - c) * (M * lcvShare v t p p') < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (mul_pos hM h)
    linarith
  unfold lcvShare at hs
  have hmin : min 1 (min ((v - p) / t) (lcHat t p p')) ≤ 0 := (le_max_right _ _).trans hs
  have hA : 0 < (v - p) / t := div_pos (by linarith) ht
  rcases min_le_iff.1 hmin with h | h
  · linarith
  · rcases min_le_iff.1 h with h' | h'
    · linarith
    · unfold lcHat at h'
      have := (div_nonpos_iff.1 h')
      rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · linarith

/-- In every Nash equilibrium of the linear city with `v > c`, both prices are at least `c`. -/
theorem lcvNash_ge_c {v t M c p1 p2 : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hne : IsLCVNash v t M c p1 p2) : c ≤ p1 ∧ c ≤ p2 := by
  have z : ∀ q, lcvProfit v t M c c q = 0 := fun q => by unfold lcvProfit; ring
  have h1 : 0 ≤ lcvProfit v t M c p1 p2 := by rw [← z p2]; exact hne.1 c
  have h2 : 0 ≤ lcvProfit v t M c p2 p1 := by rw [← z p1]; exact hne.2 c
  have key : ∀ a b, 0 ≤ lcvProfit v t M c a b → 0 ≤ lcvProfit v t M c b a → c ≤ a := by
    intro a b ha hb
    by_contra h; push Not at h
    have hba := lcv_rival_low ht hM hcv h ha
    have hab := lcv_rival_low ht hM hcv (show b < c by linarith) hb
    linarith
  exact ⟨key p1 p2 h1 h2, key p2 p1 h2 h1⟩

/-- At a symmetric profile `p ≤ v − t/2` each firm serves half the market. -/
theorem lcvShare_symm_half {v t p : ℝ} (ht : 0 < t) (hp : 2 * p ≤ 2 * v - t) :
    lcvShare v t p p = 1 / 2 := by
  have e : lcHat t p p = 1 / 2 := by unfold lcHat; field_simp; ring
  apply lcvShare_eq_of (by norm_num) (by norm_num) _ (by rw [e])
  · right; right; rw [e]
  · rw [le_div_iff₀ ht]; linarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Linear city exercises and the small type of p. 398

MWG, small type on p. 398, and Exercises 12.C.13 and 12.C.14 (p. 432-433), in the linear city
with nonpurchase of `MWGMarketPower.CityModels`. Throughout `t > 0` and `M > 0`; write
`L = (4v − 3t − c)/3` and `U = (3v − 2t − c)/2`.

* `smallType_12_C_398`: for every `v ≥ c + 3t/2` the profile `p₁ = p₂ = c + t` is the unique Nash
  equilibrium, with profits `tM/2` ("the equilibrium just derived remains valid as long as
  `v ≥ c + 3t/2`"); `smallType_12_C_398_kink`: for `v ∈ [c + t, c + 3t/2]` the profile
  `p₁ = p₂ = v − t/2` is an equilibrium at the kink, every consumer buys, and the consumer at `ẑ`
  gets no surplus.
* `exercise_12_C_13`: with `v > c + 3t`, every best response to every rival price leaves all
  consumers purchasing (the two shares sum to one).
* `exercise_12_C_14a`, `exercise_12_C_14b`: best responses and the unique equilibrium `c + t`.
* `exercise_12_C_14c`: for `c < v < c + t`, best responses, the unique equilibrium `(v + c)/2`, and
  some consumers do not buy. The hypothesis `v > c` is needed:
  `exercise_12_C_14c_counterexample` (correction 26).
* `exercise_12_C_14d`: for `v ∈ (c + t, c + 3t/2)` the equilibria are exactly the pairs with
  `p₁ + p₂ = 2v − t` and `p₁, p₂ ∈ [L, U]`; the unique symmetric one is `v − t/2`, and there are
  asymmetric equilibria (the answer to (d)'s question is yes).
* `exercise_12_C_14e`: in case (d) a fall in `t` raises the equilibrium price and profits; in
  cases (a) and (b) it lowers them.
-/

namespace MWG.MarketPower

/-- **Small type, p. 398** (MWG). For every `v ≥ c + 3t/2`, `p₁* = p₂* = c + t` is the unique Nash
equilibrium of the linear city with nonpurchase, and each firm earns `tM/2`. -/
theorem smallType_12_C_398 {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : 2 * c + 3 * t ≤ 2 * v) :
    IsLCVNash v t M c (c + t) (c + t) ∧ lcvProfit v t M c (c + t) (c + t) = t * M / 2 ∧
      ∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  have hcv : c < v := by linarith
  have hbr := (lcvBR_duo (v := v) (M := M) (c := c) ht hM (p2 := c + t) (by linarith) (by linarith)
    (by linarith))
  have e : (t + (c + t) + c) / 2 = c + t := by ring
  rw [e] at hbr
  refine ⟨lcvNash_of_BR hbr.2 hbr.2, ?_, fun p1 p2 hne => ?_⟩
  · unfold lcvProfit; rw [hbr.1]; field_simp; ring
  obtain ⟨hc1, hc2⟩ := lcvNash_ge_c ht hM hcv hne
  rcases le_or_gt v (c + 2 * t) with hlow | hv2
  · have h1 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv hlow (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv hlow (by linarith)) hne.2
    unfold lcvBRLow at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith
  rcases lt_or_ge v (c + 3 * t) with hmid | hhigh
  · have h1 := lcv_eq_of_uniqueBR (lcvBRMid_spec ht hM hv2.le hmid (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRMid_spec ht hM hv2.le hmid (by linarith)) hne.2
    unfold lcvBRMid at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith
  · have h1 := lcv_eq_of_uniqueBR (lcvBRHigh_spec ht hM hhigh (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRHigh_spec ht hM hhigh (by linarith)) hne.2
    unfold lcvBRHigh at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith

/-- **Small type, p. 398** (MWG). For `v ∈ [c + t, c + 3t/2]`, `p₁ = p₂ = v − t/2` is a Nash
equilibrium "at a kink": each firm serves half the market, so every consumer buys, and the
consumer at `ẑ = 1/2` gets no surplus from his purchase. -/
theorem smallType_12_C_398_kink {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + t ≤ v)
    (hv2 : 2 * v ≤ 2 * c + 3 * t) :
    IsLCVNash v t M c (v - t / 2) (v - t / 2) ∧ lcvShare v t (v - t / 2) (v - t / 2) = 1 / 2 ∧
      lcHat t (v - t / 2) (v - t / 2) = 1 / 2 ∧ v - (v - t / 2) - t * (1 / 2) = 0 := by
  have hcv : c < v := by linarith
  have hbr := lcvBRLow_spec (M := M) ht hM hcv (by linarith) (show c - t < v - t / 2 by linarith)
  have e : lcvBRLow v t c (v - t / 2) = v - t / 2 := by
    unfold lcvBRLow; split_ifs <;> linarith
  rw [e] at hbr
  refine ⟨lcvNash_of_BR hbr hbr, lcvShare_symm_half ht (by linarith), ?_, by ring⟩
  unfold lcHat; field_simp; ring

/-- **Exercise 12.C.13** (MWG, p. 432). If `v > c + 3t`, any best response of firm 1 to any price
`p₂` of firm 2 results in all consumers purchasing from one of the two firms: the shares sum to
one. -/
theorem exercise_12_C_13 {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v)
    (p2 p1 : ℝ) (hbr : ∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c p1 p2) :
    lcvShare v t p1 p2 + lcvShare v t p2 p1 = 1 := by
  have hcv : c < v := by linarith
  rcases le_or_gt p2 (c - t) with hlow | hp2
  · have hz : lcHat t p1 p2 ≤ 0 := by
      rcases lt_or_ge p1 c with h | h
      · have h0 : 0 ≤ lcvProfit v t M c p1 p2 := by
          have := hbr c; unfold lcvProfit at this ⊢; linarith [this, show (c - c) * (M *
            lcvShare v t c p2) = 0 by ring]
        have := lcv_rival_low ht hM hcv h h0
        unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      · unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [lcvShare_eq_zero hz, zero_add]
    apply lcvShare_eq_of zero_le_one le_rfl
    · rw [le_div_iff₀ ht]; linarith
    · rw [lcHat_symm ht]; linarith
    · left; rfl
  · have h1 := lcv_eq_of_uniqueBR (lcvBRHigh_spec ht hM hv.le hp2) hbr
    unfold lcvBRHigh at h1
    split_ifs at h1 with ha hb
    · rw [h1, (lcvBR_duo (v := v) (M := M) (c := c) ht hM hp2 ha (by linarith)).1]
      have hz : lcHat t ((t + p2 + c) / 2) p2 = (t + p2 - c) / (4 * t) := by
        unfold lcHat; field_simp; ring
      have hs2 : lcvShare v t p2 ((t + p2 + c) / 2) = (3 * t - p2 + c) / (4 * t) := by
        have e : lcHat t p2 ((t + p2 + c) / 2) = (3 * t - p2 + c) / (4 * t) := by
          rw [lcHat_symm ht, hz]; field_simp; ring
        apply lcvShare_eq_of
        · exact div_nonneg (by linarith) (by positivity)
        · rw [div_le_one (by positivity)]; linarith
        · rw [div_le_div_iff₀ (by positivity) ht]; nlinarith
        · rw [e]
        · right; right; rw [e]
      rw [hs2]; field_simp; ring
    · rw [h1, (lcvBR_capture (v := v) (M := M) (c := c) ht hM (by linarith) hb).1,
        lcvShare_eq_zero (by unfold lcHat; field_simp; linarith)]
      ring
    · rw [h1, (lcvBR_cover (v := v) (M := M) (c := c) ht hM (by linarith) (by linarith)).1,
        lcvShare_eq_zero]
      · ring
      · unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- **Exercise 12.C.14(a)** (MWG, p. 432). For `v ∈ (c + 2t, c + 3t)`: the best response to
`p₂ > c − t` is `lcvBRMid` (interior duopoly up to `L`, the kink `2v − t − p₂` on `(L, v]`, then
`v − t`), no price earns a positive profit against `p₂ ≤ c − t`, and the unique Nash equilibrium
is `p₁* = p₂* = c + t`. -/
theorem exercise_12_C_14a {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + 2 * t < v)
    (hv2 : v < c + 3 * t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRMid v t c p2)) ∧
    (∀ p2, p2 ≤ c - t → ∀ p, lcvProfit v t M c p p2 ≤ 0) ∧
    IsLCVNash v t M c (c + t) (c + t) ∧
      ∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = c + t ∧ p2 = c + t :=
  ⟨fun _ h => lcvBRMid_spec ht hM hv1.le hv2 h, fun _ h => (lcvBR_low ht hM h).2,
    (smallType_12_C_398 ht hM (by linarith)).1, (smallType_12_C_398 ht hM (by linarith)).2.2⟩

/-- **Exercise 12.C.14(b)** (MWG, p. 432). For `v ∈ (c + 3t/2, c + 2t)`: the best response to
`p₂ > c − t` is `lcvBRLow` (interior duopoly up to `L`, the kink on `(L, U]`, then the local
monopoly price `(v + c)/2`), and the unique Nash equilibrium is `p₁* = p₂* = c + t`. -/
theorem exercise_12_C_14b {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : 2 * c + 3 * t < 2 * v)
    (hv2 : v < c + 2 * t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2)) ∧
    (∀ p2, p2 ≤ c - t → ∀ p, lcvProfit v t M c p p2 ≤ 0) ∧
    IsLCVNash v t M c (c + t) (c + t) ∧
      ∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = c + t ∧ p2 = c + t :=
  ⟨fun _ h => lcvBRLow_spec ht hM (by linarith) hv2.le h, fun _ h => (lcvBR_low ht hM h).2,
    (smallType_12_C_398 ht hM hv1.le).1, (smallType_12_C_398 ht hM hv1.le).2.2⟩

/-- **Exercise 12.C.14(c)** (MWG, p. 432), with `v > c` added. For `c < v < c + t`: the best
response to `p₂ > c − t` is `lcvBRLow`; the unique Nash equilibrium is
`p₁* = p₂* = (v + c)/2`; each firm serves `(v − c)/(2t)` of the market, so a fraction
`1 − (v − c)/t > 0` of consumers buys from neither firm ("local monopolists", p. 398). -/
theorem exercise_12_C_14c {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hv : v < c + t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2)) ∧
    IsLCVNash v t M c ((v + c) / 2) ((v + c) / 2) ∧
    (∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = (v + c) / 2 ∧ p2 = (v + c) / 2) ∧
    lcvShare v t ((v + c) / 2) ((v + c) / 2) = (v - c) / (2 * t) ∧
    lcvShare v t ((v + c) / 2) ((v + c) / 2) + lcvShare v t ((v + c) / 2) ((v + c) / 2) < 1 := by
  have hbr := lcvBR_mono (M := M) (p2 := (v + c) / 2) ht hM hcv (by linarith) (by linarith)
  refine ⟨fun _ h => lcvBRLow_spec ht hM hcv (by linarith) h, lcvNash_of_BR hbr.2 hbr.2,
    fun p1 p2 hne => ?_, hbr.1, ?_⟩
  · obtain ⟨hc1, hc2⟩ := lcvNash_ge_c ht hM hcv hne
    have h1 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv (by linarith) (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv (by linarith) (by linarith)) hne.2
    unfold lcvBRLow at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith
  · rw [hbr.1, ← add_div, div_lt_one (by positivity)]; linarith

/-- **Exercise 12.C.14(c)** (MWG, p. 432): without `v > c` the equilibrium is not unique. With
`v = c`, both `p₁ = p₂ = c = (v + c)/2` and `p₁ = p₂ = c + 1` are Nash equilibria (nobody can earn
a positive profit). -/
theorem exercise_12_C_14c_counterexample {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    IsLCVNash c t M c ((c + c) / 2) ((c + c) / 2) ∧ IsLCVNash c t M c (c + 1) (c + 1) := by
  have hle : ∀ p q, lcvProfit c t M c p q ≤ 0 := by
    intro p q
    rcases lt_or_ge p c with h | h
    · exact lcv_le_zero_of_lt hM.le h
    · refine (lcv_le_A hM.le h).trans ?_
      have : (p - c) * ((c - p) / t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (div_nonpos_of_nonpos_of_nonneg
          (by linarith) ht.le)
      rw [max_eq_left this, mul_zero]
  have hz1 : ∀ q, lcvProfit c t M c ((c + c) / 2) q = 0 := fun q => by
    unfold lcvProfit; ring
  have hz2 : ∀ q, lcvProfit c t M c (c + 1) q = 0 := fun q => by
    unfold lcvProfit lcvShare
    have : (c - (c + 1)) / t < 0 := div_neg_of_neg_of_pos (by linarith) ht
    rw [max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans this.le))]
    ring
  exact ⟨⟨fun q => by rw [hz1]; exact hle _ _, fun q => by rw [hz1]; exact hle _ _⟩,
    ⟨fun q => by rw [hz2]; exact hle _ _, fun q => by rw [hz2]; exact hle _ _⟩⟩

/-- **Exercise 12.C.14(d)** (MWG, p. 432). For `v ∈ (c + t, c + 3t/2)`: the best response to
`p₂ > c − t` is `lcvBRLow`; the Nash equilibria are exactly the pairs with `p₁ + p₂ = 2v − t`
and `L ≤ p₁, p₂ ≤ U`; the unique symmetric equilibrium is `p₁* = p₂* = v − t/2`; and asymmetric
equilibria exist. -/
theorem exercise_12_C_14d {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + t < v)
    (hv2 : 2 * v < 2 * c + 3 * t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2)) ∧
    (∀ p1 p2, IsLCVNash v t M c p1 p2 ↔ p1 + p2 = 2 * v - t ∧
      (4 * v - 3 * t - c) / 3 ≤ p1 ∧ p1 ≤ (3 * v - 2 * t - c) / 2 ∧
      (4 * v - 3 * t - c) / 3 ≤ p2 ∧ p2 ≤ (3 * v - 2 * t - c) / 2) ∧
    (∀ p, IsLCVNash v t M c p p ↔ p = v - t / 2) ∧
    ∃ p1 p2, p1 ≠ p2 ∧ IsLCVNash v t M c p1 p2 := by
  have hcv : c < v := by linarith
  have hspec : ∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2) :=
    fun _ h => lcvBRLow_spec ht hM hcv (by linarith) h
  have hchar : ∀ p1 p2, IsLCVNash v t M c p1 p2 ↔ p1 + p2 = 2 * v - t ∧
      (4 * v - 3 * t - c) / 3 ≤ p1 ∧ p1 ≤ (3 * v - 2 * t - c) / 2 ∧
      (4 * v - 3 * t - c) / 3 ≤ p2 ∧ p2 ≤ (3 * v - 2 * t - c) / 2 := by
    intro p1 p2
    constructor
    · intro hne
      obtain ⟨hc1, hc2⟩ := lcvNash_ge_c ht hM hcv hne
      have h1 := lcv_eq_of_uniqueBR (hspec p2 (by linarith)) hne.1
      have h2 := lcv_eq_of_uniqueBR (hspec p1 (by linarith)) hne.2
      unfold lcvBRLow at h1 h2
      split_ifs at h1 h2 <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨hs, h1, h2, h3, h4⟩
      have e1 : lcvBRLow v t c p2 = p1 := by unfold lcvBRLow; split_ifs <;> linarith
      have e2 : lcvBRLow v t c p1 = p2 := by unfold lcvBRLow; split_ifs <;> linarith
      have b1 := hspec p2 (by linarith)
      have b2 := hspec p1 (by linarith)
      rw [e1] at b1; rw [e2] at b2
      exact lcvNash_of_BR b1 b2
  refine ⟨hspec, hchar, fun p => ?_, ?_⟩
  · rw [hchar]
    constructor
    · rintro ⟨hs, -⟩; linarith
    · intro hp; subst hp; refine ⟨by ring, ?_, ?_, ?_, ?_⟩ <;> linarith
  · set δ := min ((3 * t + 2 * c - 2 * v) / 6) ((v - c - t) / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ1 : δ ≤ (3 * t + 2 * c - 2 * v) / 6 := min_le_left _ _
    have hδ2 : δ ≤ (v - c - t) / 2 := min_le_right _ _
    refine ⟨v - t / 2 + δ, v - t / 2 - δ, by linarith, (hchar _ _).2 ⟨by ring, ?_, ?_, ?_, ?_⟩⟩ <;>
      linarith

/-- **Exercise 12.C.14(e)** (MWG, p. 433). Let `t₁ < t₂`. If both travel costs are in case (d)
(`c + t₂ < v` and `2v < 2c + 3t₁`), the symmetric equilibrium price and profit are higher at the
lower travel cost `t₁`. If both are in cases (a)-(b) (`2v ≥ 2c + 3t₂`), they are lower at `t₁`:
a fall in `t` raises prices and profits in case (d) but lowers them in cases (a) and (b). -/
theorem exercise_12_C_14e {v M c t1 t2 : ℝ} (hM : 0 < M) (ht1 : 0 < t1) (h12 : t1 < t2) :
    ((c + t2 < v ∧ 2 * v < 2 * c + 3 * t1) → ∀ p q, IsLCVNash v t1 M c p p →
      IsLCVNash v t2 M c q q → q < p ∧ lcvProfit v t2 M c q q < lcvProfit v t1 M c p p) ∧
    (2 * c + 3 * t2 ≤ 2 * v → ∀ p q, IsLCVNash v t1 M c p p →
      IsLCVNash v t2 M c q q → p < q ∧ lcvProfit v t1 M c p p < lcvProfit v t2 M c q q) := by
  have ht2 : 0 < t2 := by linarith
  constructor
  · rintro ⟨hv1, hv2⟩ p q hp hq
    have ep := ((exercise_12_C_14d ht1 hM (by linarith) hv2).2.2.1 p).1 hp
    have eq := ((exercise_12_C_14d ht2 hM hv1 (by linarith)).2.2.1 q).1 hq
    subst ep; subst eq
    have s1 := lcvShare_symm_half (v := v) ht1 (p := v - t1 / 2) (by linarith)
    have s2 := lcvShare_symm_half (v := v) ht2 (p := v - t2 / 2) (by linarith)
    refine ⟨by linarith, ?_⟩
    unfold lcvProfit; rw [s1, s2]; nlinarith
  · intro hv p q hp hq
    have ep := ((smallType_12_C_398 ht1 hM (by linarith)).2.2 p p hp).1
    have eq := ((smallType_12_C_398 ht2 hM hv).2.2 q q hq).1
    subst ep; subst eq
    rw [(smallType_12_C_398 ht1 hM (by linarith)).2.1, (smallType_12_C_398 ht2 hM hv).2.1]
    exact ⟨by linarith, by nlinarith⟩

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Quadratic travel costs and the circular city

MWG, Exercise 12.C.15 (p. 433), the circular city of p. 399 (Salop, 1979), and Exercise 12.C.16.

**Exercise 12.C.15.** With total cost `p_j + td²`, a consumer at `z` prefers firm 1 iff
`z < ẑ = (t + p₂ − p₁)/(2t)`, exactly as with linear costs (`quadCity_prefers`), so firm 1's
demand is (12.C.8) (`quadCity_demand`) and the unique equilibrium is `p₁* = p₂* = c + t`
(`exercise_12_C_15`).

**The circular city.** `J` firms sit at equal intervals `1/J` on a circle of circumference 1 with
`M` consumers spread uniformly. Firm `j` charges `q`, all other firms `p`. With travel cost
`t·d` (linear) or `t·d²` (quadratic), a consumer between firm `j` and a neighbour at distance `x`
from `j` buys from `j` iff `x < x̂(q)` (`circLin_prefers`, `circQuad_prefers`), where
`x̂(q) = (p − q + w)/(2s)` with `(s, w) = (t, t/J)` (linear) or `(t/J, t/J²)` (quadratic). As long
as `q ≥ p − w`, consumers beyond a neighbour prefer that neighbour to firm `j`
(`circLin_beyond`, `circQuad_beyond`), so firm `j`'s demand is
`2M·max{0, min{1/J, x̂(q)}}` (`circDemand`). For lower prices only nonnegativity of demand is
used (the margin is then negative at the candidate equilibrium).

* `circ_symmetric_eqm`, `circ_symmetric_unique`: the symmetric equilibrium price is `c + w`, and
  no other symmetric profile is an equilibrium.
* `circularCity_linear`: with linear travel cost the equilibrium price is `c + t/J` and each firm
  earns `tM/J²` (the model of p. 399; MWG states no equilibrium there).
* `exercise_12_C_16`: with quadratic travel cost the equilibrium price is `c + t/J²` and each firm
  earns `tM/J³`; `exercise_12_C_16_limits`: as `J → ∞` the price tends to `c` and profits to `0`,
  and price and profit fall as `t` falls.
-/

namespace MWG.MarketPower

open Filter Topology

/-! ### Exercise 12.C.15 -/

/-- **Exercise 12.C.15** (MWG, p. 433). With quadratic travel cost a consumer at `z` strictly
prefers firm 1 iff `z < ẑ`, the same indifferent consumer (12.C.7) as with linear costs. -/
theorem quadCity_prefers {t p1 p2 z : ℝ} (ht : 0 < t) :
    p1 + t * z ^ 2 < p2 + t * (1 - z) ^ 2 ↔ z < lcHat t p1 p2 := by
  rw [← linearCity_prefers ht]
  constructor <;> intro h <;> nlinarith

/-- Firm 1's demand (12.C.8) is `M` times the length of the set of consumers buying from it. -/
theorem lcDemand_eq_share {t M p1 p2 : ℝ} (ht : 0 < t) :
    lcDemand t M p1 p2 = M * max 0 (min 1 (lcHat t p1 p2)) := by
  unfold lcDemand lcHat
  split_ifs with h1 h2
  · rw [max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)))]; ring
  · rw [min_eq_left (by rw [le_div_iff₀ (by positivity)]; linarith),
      max_eq_right zero_le_one, mul_one]
  · push Not at h1 h2
    rw [min_eq_right (by rw [div_le_one (by positivity)]; linarith),
      max_eq_right (div_nonneg (by linarith) (by positivity))]
    ring

/-- **Exercise 12.C.15** (MWG, p. 433). With quadratic travel cost (and `v` large enough that
everyone buys), firm 1's demand is `M` times the length of
`{z ∈ [0, 1] : p₁ + tz² < p₂ + t(1 − z)²}` and equals (12.C.8); hence `p₁* = p₂* = c + t` is
the unique Nash equilibrium, with profits `tM/2`. -/
theorem exercise_12_C_15 {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    (∀ p1 p2, lcDemand t M p1 p2 = M *
      (MeasureTheory.volume
        {z ∈ Set.Icc (0 : ℝ) 1 | p1 + t * z ^ 2 < p2 + t * (1 - z) ^ 2}).toReal) ∧
    IsLCNash t M c (c + t) (c + t) ∧ lcProfit t M c (c + t) (c + t) = t * M / 2 ∧
    ∀ p1 p2, IsLCNash t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  refine ⟨fun p1 p2 => ?_, (example_12_C_2 ht hM).1, (example_12_C_2 ht hM).2.2.1,
    (example_12_C_2 ht hM).2.2.2⟩
  have hs : {z ∈ Set.Icc (0 : ℝ) 1 | p1 + t * z ^ 2 < p2 + t * (1 - z) ^ 2} =
      Set.Icc (0 : ℝ) 1 ∩ Set.Iio (lcHat t p1 p2) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Iio, quadCity_prefers ht]
  rw [hs, volume_unit_inter_Iio, ENNReal.toReal_ofReal (le_max_left _ _), lcDemand_eq_share ht]

/-! ### The circular city -/

/-- **The circular city** (MWG, p. 399), linear travel cost: a consumer at distance
`x` from firm `j` (charging `q`) on the arc to a neighbour (charging `p`, at distance `1/J`) buys
from `j` iff `x < (p − q + t/J)/(2t)`. -/
theorem circLin_prefers {t J p q x : ℝ} (ht : 0 < t) :
    q + t * x < p + t * (1 / J - x) ↔ x < (p - q + t / J) / (2 * t) := by
  rw [lt_div_iff₀ (by positivity)]
  have e : t * (1 / J - x) = t / J - t * x := by ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- With linear travel cost and `q ≥ p − t/J`, a consumer beyond a neighbour (at distance `y ≥ 0`
past it) weakly prefers the neighbour to firm `j`. -/
theorem circLin_beyond {t J p q y : ℝ} (h : p - t / J ≤ q) :
    p + t * y ≤ q + t * (1 / J + y) := by
  have : t * (1 / J) = t / J := by ring
  nlinarith

/-- **Exercise 12.C.16** (MWG, p. 433), quadratic travel cost: a consumer at distance `x` from
firm `j` on the arc to a neighbour buys from `j` iff `x < (p − q + t/J²)/(2t/J)`. -/
theorem circQuad_prefers {t J p q x : ℝ} (ht : 0 < t) (hJ : 0 < J) :
    q + t * x ^ 2 < p + t * (1 / J - x) ^ 2 ↔ x < (p - q + t / J ^ 2) / (2 * (t / J)) := by
  rw [lt_div_iff₀ (by positivity)]
  have e : t * (1 / J - x) ^ 2 = t * x ^ 2 + t / J ^ 2 - x * (2 * (t / J)) := by
    field_simp; ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- With quadratic travel cost and `q ≥ p − t/J²`, a consumer beyond a neighbour weakly prefers
the neighbour to firm `j`. -/
theorem circQuad_beyond {t J p q y : ℝ} (ht : 0 < t) (hJ : 0 < J) (hy : 0 ≤ y)
    (h : p - t / J ^ 2 ≤ q) : p + t * y ^ 2 ≤ q + t * (1 / J + y) ^ 2 := by
  have e : t * (1 / J + y) ^ 2 = t / J ^ 2 + 2 * (t / J) * y + t * y ^ 2 := by field_simp; ring
  rw [e]
  have : 0 ≤ 2 * (t / J) * y := by positivity
  linarith

/-- Firm `j`'s demand in the circular city when it charges `q ≥ p − w` and all other firms charge
`p`: `2M·max{0, min{1/J, (p − q + w)/(2s)}}`. -/
noncomputable def circDemand (M J s w p q : ℝ) : ℝ :=
  2 * M * max 0 (min (1 / J) ((p - q + w) / (2 * s)))

/-- **The circular city: symmetric equilibrium** (MWG, p. 399 and Exercise 12.C.16). Let
`s, J, M > 0` and `w = s/J`, and let `D` be firm `j`'s demand when the others charge `c + w`:
nonnegative, and equal to `circDemand` at every price `q ≥ c`. Then `q = c + w` is a best
response for firm `j`, which sells `M/J` and earns `wM/J`. -/
theorem circ_symmetric_eqm {M J s w c : ℝ} (hM : 0 < M) (hJ : 0 < J) (hs : 0 < s)
    (hw : w * J = s) {D : ℝ → ℝ} (hD0 : ∀ q, 0 ≤ D q)
    (hDloc : ∀ q, c + w - w ≤ q → D q = circDemand M J s w (c + w) q) :
    D (c + w) = M / J ∧ (c + w - c) * D (c + w) = w * M / J ∧
      ∀ q, (q - c) * D q ≤ (c + w - c) * D (c + w) := by
  have hwpos : 0 < w := by
    by_contra h; push Not at h; nlinarith
  have hws : w / (2 * s) = 1 / (2 * J) := by
    rw [← hw]; field_simp
  have hD : D (c + w) = M / J := by
    rw [hDloc _ (by linarith)]
    unfold circDemand
    rw [show c + w - (c + w) + w = w by ring, hws, min_eq_right (by
      rw [div_le_div_iff₀ (by positivity) hJ]; linarith), max_eq_right (by positivity)]
    field_simp
  refine ⟨hD, by rw [hD]; ring, fun q => ?_⟩
  rw [hD]
  rcases lt_or_ge q c with h | h
  · have : (q - c) * D q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hD0 q)
    have : 0 < (c + w - c) * (M / J) := by
      rw [show c + w - c = w by ring]; positivity
    linarith
  · rw [hDloc q (by linarith)]
    unfold circDemand
    have hx : (q - c) * max 0 (min (1 / J) ((c + w - q + w) / (2 * s))) ≤
        max 0 ((q - c) * ((c + w - q + w) / (2 * s))) :=
      lcv_mul_le (by linarith) (le_max_left _ _) (max_le_max le_rfl (min_le_right _ _))
    have hb : (q - c) * ((c + w - q + w) / (2 * s)) ≤ w / (2 * J) := by
      rw [← hw, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (q - c - w), mul_pos hJ hwpos]
    have hb' : max 0 ((q - c) * ((c + w - q + w) / (2 * s))) ≤ w / (2 * J) :=
      max_le (by positivity) hb
    calc (q - c) * (2 * M * max 0 (min (1 / J) ((c + w - q + w) / (2 * s))))
        = 2 * M * ((q - c) * max 0 (min (1 / J) ((c + w - q + w) / (2 * s)))) := by ring
      _ ≤ 2 * M * (w / (2 * J)) := by
          apply mul_le_mul_of_nonneg_left (hx.trans hb') (by positivity)
      _ = (c + w - c) * (M / J) := by field_simp; ring

/-- **The circular city: uniqueness among symmetric profiles** (MWG, p. 399 and Exercise 12.C.16).
If every firm charging `p` is an equilibrium (firm `j`'s demand `D`, when the others charge `p`,
equals `circDemand` at every `q ≥ p − w`), then `p = c + w`. -/
theorem circ_symmetric_unique {M J s w c p : ℝ} (hM : 0 < M) (hJ : 0 < J) (hs : 0 < s)
    (hw : w * J = s) {D : ℝ → ℝ} (hDloc : ∀ q, p - w ≤ q → D q = circDemand M J s w p q)
    (hne : ∀ q, (q - c) * D q ≤ (p - c) * D p) : p = c + w := by
  have hwpos : 0 < w := by
    by_contra h; push Not at h; nlinarith
  -- on `[p − w, p + w]` the profit is `(q − c)M(p − q + w)/s`
  have hloc : ∀ δ, -w ≤ δ → δ ≤ w → (p + δ - c) * D (p + δ) = (p + δ - c) * M * (w - δ) / s := by
    intro δ h1 h2
    rw [hDloc _ (by linarith)]
    unfold circDemand
    have hX0 : 0 ≤ (p - (p + δ) + w) / (2 * s) := div_nonneg (by linarith) (by positivity)
    have hX1 : (p - (p + δ) + w) / (2 * s) ≤ 1 / J := by
      rw [div_le_div_iff₀ (by positivity) hJ, ← hw]; nlinarith
    rw [min_eq_right hX1, max_eq_right hX0]
    field_simp; ring
  have hgain : ∀ δ, -w ≤ δ → δ ≤ w →
      (p + δ - c) * D (p + δ) - (p - c) * D p = M / s * δ * (w - (p - c) - δ) := by
    intro δ h1 h2
    have h0 := hloc 0 (by linarith) (by linarith)
    rw [add_zero, sub_zero] at h0
    rw [hloc δ h1 h2, h0]; field_simp; ring
  by_contra hne'
  set e := w - (p - c) with he
  have he0 : e ≠ 0 := by intro h; apply hne'; linarith
  have hMs : 0 < M / s := div_pos hM hs
  rcases lt_or_gt_of_ne he0 with hneg | hpos
  · by_cases hbig : -(2 * w) ≤ e
    · have := hgain (e / 2) (by linarith) (by linarith)
      have h := hne (p + e / 2)
      have : 0 < M / s * (e / 2) * (e - e / 2) := by
        have : M / s * (e / 2) * (e - e / 2) = M / s * (e / 2) ^ 2 := by ring
        rw [this]; have : e / 2 ≠ 0 := by positivity
        positivity
      linarith
    · push Not at hbig
      have := hgain (-w) le_rfl (by linarith)
      have h := hne (p + -w)
      have : 0 < M / s * (-w) * (e - -w) :=
        mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hMs (by linarith)) (by linarith)
      linarith
  · by_cases hbig : e ≤ 2 * w
    · have := hgain (e / 2) (by linarith) (by linarith)
      have h := hne (p + e / 2)
      have : 0 < M / s * (e / 2) * (e - e / 2) :=
        mul_pos (mul_pos hMs (by linarith)) (by linarith)
      linarith
    · push Not at hbig
      have := hgain w (by linarith) le_rfl
      have h := hne (p + w)
      have : 0 < M / s * w * (e - w) := mul_pos (mul_pos hMs hwpos) (by linarith)
      linarith

/-- **The circular city with linear travel cost** (MWG, p. 399; Salop 1979): with `J ≥ 1` firms
the symmetric equilibrium price is `c + t/J`; each firm sells `M/J` and earns `tM/J²`; and no other
symmetric price is an equilibrium. -/
theorem circularCity_linear {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) {J : ℕ} (hJ : 0 < J)
    {D : ℝ → ℝ} (hD0 : ∀ q, 0 ≤ D q)
    (hDloc : ∀ q, c + t / J - t / J ≤ q → D q = circDemand M J t (t / J) (c + t / J) q) :
    (c + t / J - c) * D (c + t / J) = t * M / (J : ℝ) ^ 2 ∧
      (∀ q, (q - c) * D q ≤ (c + t / J - c) * D (c + t / J)) ∧
      ∀ p (E : ℝ → ℝ), (∀ q, p - t / J ≤ q → E q = circDemand M J t (t / J) p q) →
        (∀ q, (q - c) * E q ≤ (p - c) * E p) → p = c + t / J := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : t / J * J = t := by field_simp
  obtain ⟨_, hval, hbr⟩ := circ_symmetric_eqm hM hJ' ht hw hD0 hDloc
  refine ⟨by rw [hval]; field_simp, hbr, fun p E hE hne => ?_⟩
  exact circ_symmetric_unique hM hJ' ht hw hE hne

/-- **Exercise 12.C.16** (MWG, p. 433). In the circular city with `J ≥ 1` firms and quadratic
travel cost `td²`, the symmetric equilibrium price is `c + t/J²`; each firm sells `M/J` and earns
`tM/J³`; and no other symmetric price is an equilibrium. -/
theorem exercise_12_C_16 {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) {J : ℕ} (hJ : 0 < J)
    {D : ℝ → ℝ} (hD0 : ∀ q, 0 ≤ D q)
    (hDloc : ∀ q, c + t / (J : ℝ) ^ 2 - t / (J : ℝ) ^ 2 ≤ q →
      D q = circDemand M J (t / J) (t / (J : ℝ) ^ 2) (c + t / (J : ℝ) ^ 2) q) :
    D (c + t / (J : ℝ) ^ 2) = M / J ∧
      (c + t / (J : ℝ) ^ 2 - c) * D (c + t / (J : ℝ) ^ 2) = t * M / (J : ℝ) ^ 3 ∧
      (∀ q, (q - c) * D q ≤ (c + t / (J : ℝ) ^ 2 - c) * D (c + t / (J : ℝ) ^ 2)) ∧
      ∀ p (E : ℝ → ℝ), (∀ q, p - t / (J : ℝ) ^ 2 ≤ q →
        E q = circDemand M J (t / J) (t / (J : ℝ) ^ 2) p q) →
        (∀ q, (q - c) * E q ≤ (p - c) * E p) → p = c + t / (J : ℝ) ^ 2 := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : t / (J : ℝ) ^ 2 * J = t / J := by field_simp
  obtain ⟨hD, hval, hbr⟩ := circ_symmetric_eqm hM hJ' (div_pos ht hJ') hw hD0 hDloc
  refine ⟨hD, by rw [hval]; field_simp, hbr, fun p E hE hne => ?_⟩
  exact circ_symmetric_unique hM hJ' (div_pos ht hJ') hw hE hne

/-- **Exercise 12.C.16** (MWG, p. 433): "What happens as `J` grows large? As `t` falls?" As
`J → ∞` the equilibrium price `c + t/J²` tends to `c` and each firm's profit `tM/J³` (and the
industry profit `tM/J²`) to `0`; for fixed `J`, a fall in `t` strictly lowers price and
profit. -/
theorem exercise_12_C_16_limits {t M c : ℝ} :
    Tendsto (fun J : ℕ => c + t / (J : ℝ) ^ 2) atTop (𝓝 c) ∧
      Tendsto (fun J : ℕ => t * M / (J : ℝ) ^ 3) atTop (𝓝 0) ∧
      Tendsto (fun J : ℕ => (J : ℝ) * (t * M / (J : ℝ) ^ 3)) atTop (𝓝 0) ∧
      ∀ {J : ℕ}, 0 < J → 0 < M → ∀ {t' : ℝ}, t' < t →
        c + t' / (J : ℝ) ^ 2 < c + t / (J : ℝ) ^ 2 ∧
          t' * M / (J : ℝ) ^ 3 < t * M / (J : ℝ) ^ 3 := by
  have h2 : Tendsto (fun J : ℕ => ((J : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp
      tendsto_natCast_atTop_atTop)
  have h3 : Tendsto (fun J : ℕ => ((J : ℝ) ^ 3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop three_ne_zero).comp
      tendsto_natCast_atTop_atTop)
  refine ⟨?_, ?_, ?_, fun {J} hJ hM {t'} htt => ?_⟩
  · have := (h2.const_mul t).const_add c
    rw [mul_zero, add_zero] at this
    exact this.congr fun J => by simp [div_eq_mul_inv]
  · have := h3.const_mul (t * M)
    rw [mul_zero] at this
    exact this.congr fun J => by simp [div_eq_mul_inv]
  · have := h2.const_mul (t * M)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with J hJ
    have : (0 : ℝ) < J := by exact_mod_cast hJ
    field_simp
  · have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
    constructor
    · have := div_lt_div_of_pos_right htt (pow_pos hJ' 2); linarith
    · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right htt hM) (pow_pos hJ' 3)

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The representative-consumer model and monopolistic competition

MWG, Section 12.C, pp. 399-400, and footnotes 15-18.

The representative consumer has quasilinear utility `u(m, x₁, …, x_J) = G(∑_j f(x_j)) + m`, with
`G` and `f` concave. With the price of the numeraire normalized to `1` and wealth `w`, the
budget gives `m = w − ∑ p_j x_j`, so the consumer maximizes
`W(x) = G(∑_j f(x_j)) − ∑_j p_j x_j` (`repWelfare`, `repUtility_budget`).

* `eq_12_C_13`: at an interior optimum the first-order conditions (12.C.13)
  `G'(∑ f(x_j))f'(x_j) = p_j` hold.
* `eq_12_C_13_sufficient`: conversely, with `G` and `f` concave and `G' ≥ 0` at the point, a
  bundle satisfying (12.C.13) maximizes `W` over `x ≥ 0`; `eq_12_C_13_unique`: with `f` strictly
  concave and `G' > 0` it is the only maximizer, so (12.C.13) can be inverted to give demand
  functions. `eq_12_C_13_instance` verifies the hypotheses for `G(X) = X`, `f(x) = x − x²/2`.
* Monopolistic competition (p. 400): `monComp_demand`: with `ψ = f'⁻¹` and `G'(x̄) ≠ 0`, firm
  `j`'s first-order condition holds iff `x_j = ψ(p_j/G'(x̄))`; `monComp_index_update`: in the
  continuum model a single firm's quantity does not affect the index `x̄ = ∫₀¹ f(x_j) dj`, so no
  firm's choice affects any other firm's payoff (`monComp_no_interaction`; footnote 18's contrast
  is verbal). `IsMonCompEqm` is a symmetric equilibrium `x̄* = ∫₀¹ f(x_j(p*(x̄*), x̄*)) dj`;
  `monComp_example` exhibits one (`G = log`, `f(x) = 2√x`: `p* = 2c`, `x̄* = 1/√c`).

Departure: the sufficiency of (12.C.13) uses `G'(∑ f(x_j)) ≥ 0`, which MWG leaves implicit.
-/

namespace MWG.MarketPower

open Function MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The representative consumer's objective after substituting the budget constraint:
`G(∑_j f(x_j)) − ∑_j p_j x_j`. -/
noncomputable def repWelfare (G f : ℝ → ℝ) (p x : ι → ℝ) : ℝ :=
  G (∑ j, f (x j)) - ∑ j, p j * x j

omit [DecidableEq ι] in
/-- **The representative consumer** (MWG, p. 399). With `m = w − ∑ p_j x_j`,
`u(m, x) = G(∑ f(x_j)) + m = w + repWelfare`. -/
theorem repUtility_budget (G f : ℝ → ℝ) (p x : ι → ℝ) (w : ℝ) :
    G (∑ j, f (x j)) + (w - ∑ j, p j * x j) = w + repWelfare G f p x := by
  unfold repWelfare; ring

/-- The representative consumer's objective as a function of `x_j` alone. -/
theorem repWelfare_update (G f : ℝ → ℝ) (p x : ι → ℝ) (j : ι) (y : ℝ) :
    repWelfare G f p (update x j y) =
      G (f y + (∑ k, f (x k) - f (x j))) - (p j * y + (∑ k, p k * x k - p j * x j)) := by
  unfold repWelfare
  have h1 : ∑ k, f (update x j y k) = f y + (∑ k, f (x k) - f (x j)) := by
    simp_rw [apply_update (fun _ => f) x j y]
    exact sum_update_eq (fun k => f (x k)) j (f y)
  have h2 : ∑ k, p k * update x j y k = p j * y + (∑ k, p k * x k - p j * x j) := by
    have : ∀ k, p k * update x j y k = update (fun k => p k * x k) j (p j * y) k := by
      intro k
      by_cases hk : k = j
      · subst hk; simp
      · simp [update_of_ne hk]
    simp_rw [this]
    exact sum_update_eq (fun k => p k * x k) j (p j * y)
  rw [h1, h2]

omit [DecidableEq ι] in
/-- **Condition (12.C.13)** (MWG, p. 399). If `x` (with every `x_j > 0`) maximizes the
representative consumer's utility over positive bundles, and `G`, `f` are differentiable there,
then `G'(∑ f(x_j))f'(x_j) = p_j` for every `j`. -/
theorem eq_12_C_13 {G f f' : ℝ → ℝ} {G'S : ℝ} {p x : ι → ℝ} (hx : ∀ j, 0 < x j)
    (hG : HasDerivAt G G'S (∑ j, f (x j))) (hf : ∀ j, HasDerivAt f (f' (x j)) (x j))
    (hmax : ∀ y : ι → ℝ, (∀ j, 0 < y j) → repWelfare G f p y ≤ repWelfare G f p x) (j : ι) :
    G'S * f' (x j) = p j := by
  classical
  set g : ℝ → ℝ := fun y => repWelfare G f p (update x j y) with hg
  have hgx : g (x j) = repWelfare G f p x := by simp [hg]
  have hloc : IsLocalMax g (x j) := by
    filter_upwards [Ioi_mem_nhds (hx j)] with y hy
    rw [hgx]
    apply hmax
    intro k
    by_cases hk : k = j
    · rw [hk, update_self]; exact hy
    · rw [update_of_ne hk]; exact hx k
  have hd : HasDerivAt g (G'S * f' (x j) - p j) (x j) := by
    have e : g = fun y => G (f y + (∑ k, f (x k) - f (x j))) -
        (p j * y + (∑ k, p k * x k - p j * x j)) := by
      funext y; simp only [hg]; exact repWelfare_update G f p x j y
    rw [e]
    have hin : HasDerivAt (fun y => f y + (∑ k, f (x k) - f (x j))) (f' (x j)) (x j) :=
      (hf j).add_const _
    have hG' : HasDerivAt G G'S (f (x j) + (∑ k, f (x k) - f (x j))) := by
      rw [add_sub_cancel]; exact hG
    have h1 := hG'.comp (x j) hin
    have h2 : HasDerivAt (fun y => p j * y + (∑ k, p k * x k - p j * x j)) (p j) (x j) := by
      simpa using ((hasDerivAt_id (x j)).const_mul (p j)).add_const (∑ k, p k * x k - p j * x j)
    exact h1.sub h2
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- The tangent-line inequality for a concave function: `f(y) ≤ f(x) + f'(x)(y − x)`. -/
theorem repTangent {f : ℝ → ℝ} {S : Set ℝ} {x y d : ℝ} (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · rw [h]; simp
  · have := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- The strict tangent-line inequality for a strictly concave function. -/
theorem repTangent_strict {f : ℝ → ℝ} {S : Set ℝ} {x y d : ℝ} (hf : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hd : HasDerivAt f d x) :
    f y < f x + d * (y - x) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have := hf.slope_lt_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at this
    linarith
  · have := hf.lt_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
    linarith

omit [DecidableEq ι] in
/-- **Condition (12.C.13) is sufficient** (MWG, p. 399). If `f` is concave on `[0, ∞)`, `G` is
concave, both are differentiable at the bundle `x ≥ 0`, `G'(∑ f(x_j)) ≥ 0`, and (12.C.13) holds,
then `x` maximizes the representative consumer's utility over all bundles `y ≥ 0`. -/
theorem eq_12_C_13_sufficient {G f f' : ℝ → ℝ} {G'S : ℝ} {p x : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hfc : ConcaveOn ℝ (Set.Ici 0) f) (hGc : ConcaveOn ℝ Set.univ G)
    (hG : HasDerivAt G G'S (∑ j, f (x j))) (hf : ∀ j, HasDerivAt f (f' (x j)) (x j))
    (hG0 : 0 ≤ G'S) (hfoc : ∀ j, G'S * f' (x j) = p j) :
    ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → repWelfare G f p y ≤ repWelfare G f p x := by
  intro y hy
  unfold repWelfare
  have hT := repTangent hGc (Set.mem_univ _) (Set.mem_univ (∑ j, f (y j))) hG
  have hsum : ∑ j, f (y j) - ∑ j, f (x j) ≤ ∑ j, f' (x j) * (y j - x j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => by
      have := repTangent hfc (hx j) (hy j) (hf j); linarith
  have hmul : G'S * (∑ j, f (y j) - ∑ j, f (x j)) ≤ ∑ j, p j * (y j - x j) := by
    calc G'S * (∑ j, f (y j) - ∑ j, f (x j)) ≤ G'S * ∑ j, f' (x j) * (y j - x j) :=
          mul_le_mul_of_nonneg_left hsum hG0
      _ = ∑ j, p j * (y j - x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [← hfoc j]; ring
  have e : ∑ j, p j * (y j - x j) = ∑ j, p j * y j - ∑ j, p j * x j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  linarith

omit [DecidableEq ι] in
/-- **Inverting (12.C.13)** (MWG, p. 399). If moreover `f` is strictly concave on `[0, ∞)` and
`G'(∑ f(x_j)) > 0`, the bundle satisfying (12.C.13) is the unique maximizer over `y ≥ 0`: the
first-order conditions determine the demands `x_j(p₁, …, p_J)`. -/
theorem eq_12_C_13_unique {G f f' : ℝ → ℝ} {G'S : ℝ} {p x : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hfc : StrictConcaveOn ℝ (Set.Ici 0) f) (hGc : ConcaveOn ℝ Set.univ G)
    (hG : HasDerivAt G G'S (∑ j, f (x j))) (hf : ∀ j, HasDerivAt f (f' (x j)) (x j))
    (hG0 : 0 < G'S) (hfoc : ∀ j, G'S * f' (x j) = p j) :
    ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → y ≠ x → repWelfare G f p y < repWelfare G f p x := by
  intro y hy hne
  unfold repWelfare
  have hT := repTangent hGc (Set.mem_univ _) (Set.mem_univ (∑ j, f (y j))) hG
  obtain ⟨j0, hj0⟩ : ∃ j, y j ≠ x j := by
    by_contra h; push Not at h; exact hne (funext h)
  have hsum : ∑ j, f (y j) - ∑ j, f (x j) < ∑ j, f' (x j) * (y j - x j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_lt_sum
    · intro j _
      have := repTangent hfc.concaveOn (hx j) (hy j) (hf j); linarith
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      have := repTangent_strict hfc (hx j0) (hy j0) (Ne.symm hj0) (hf j0); linarith
  have hmul : G'S * (∑ j, f (y j) - ∑ j, f (x j)) < ∑ j, p j * (y j - x j) := by
    calc G'S * (∑ j, f (y j) - ∑ j, f (x j)) < G'S * ∑ j, f' (x j) * (y j - x j) :=
          mul_lt_mul_of_pos_left hsum hG0
      _ = ∑ j, p j * (y j - x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [← hfoc j]; ring
  have e : ∑ j, p j * (y j - x j) = ∑ j, p j * y j - ∑ j, p j * x j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  linarith

/-- The hypotheses of `eq_12_C_13_unique` are satisfiable: `G(X) = X`, `f(x) = x − x²/2`
(`f'(x) = 1 − x`), prices `(1/2, 1/4)`, demands `x_j = 1 − p_j = (1/2, 3/4)`. -/
theorem eq_12_C_13_instance :
    StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x - x ^ 2 / 2) ∧
    ConcaveOn ℝ Set.univ (fun X : ℝ => X) ∧
    (∀ z : ℝ, HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - z) z) ∧
    (∀ S : ℝ, HasDerivAt (fun X : ℝ => X) 1 S) ∧
    ∀ j : Fin 2, (1 : ℝ) * (1 - ![1 / 2, 3 / 4] j) = ![1 / 2, 1 / 4] j := by
  refine ⟨⟨convex_Ici 0, fun a _ b _ hab u v hu hv huv => ?_⟩, concaveOn_id convex_univ,
    fun z => ?_, fun S => hasDerivAt_id S, fun j => by fin_cases j <;> norm_num⟩
  · simp only [smul_eq_mul]
    obtain rfl : v = 1 - u := by linarith
    have : 0 < (a - b) ^ 2 := by have : a - b ≠ 0 := sub_ne_zero.2 hab; positivity
    nlinarith [mul_pos hu hv]
  · have h : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - ((2 : ℕ) : ℝ) * z ^ (2 - 1) / 2) z :=
      (hasDerivAt_id' z).sub ((hasDerivAt_pow 2 z).div_const 2)
    convert h using 1
    norm_num

/-! ### Monopolistic competition (p. 400) -/

/-- **Monopolistic competition: demand** (MWG, p. 400). If `ψ` inverts `f'` (`ψ(f'(y)) = y` and
`f'(ψ(r)) = r` at `r = p/G'(x̄)`) and `G'(x̄) ≠ 0`, the consumer's first-order condition
`G'(x̄)f'(x_j) = p_j` holds iff `x_j = ψ(p_j/G'(x̄))`. -/
theorem monComp_demand {f' ψ : ℝ → ℝ} {Gx p y : ℝ} (hG : Gx ≠ 0) (hleft : ψ (f' y) = y)
    (hright : f' (ψ (p / Gx)) = p / Gx) : Gx * f' y = p ↔ y = ψ (p / Gx) := by
  constructor
  · intro h
    rw [← hleft, show f' y = p / Gx by rw [← h]; field_simp]
  · intro h
    rw [h, hright]; field_simp

/-- **Monopolistic competition: the index** (MWG, p. 400). In the continuum model a single firm
`j₀` changing its quantity does not change the index of aggregate output `x̄ = ∫₀¹ f(x_j) dj`. -/
theorem monComp_index_update (f : ℝ → ℝ) (x : ℝ → ℝ) (j0 y : ℝ) :
    ∫ j in (0 : ℝ)..1, f (update x j0 y j) = ∫ j in (0 : ℝ)..1, f (x j) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume j0] with j hj _
  rw [update_of_ne hj]

/-- **Monopolistic competition: no strategic interaction** (MWG, p. 400). If firm `k`'s payoff
depends only on its own quantity and the index, `Φ(x_k, ∫₀¹ f(x_j) dj)`, then a change in the
quantity of any other firm `j₀ ≠ k` leaves firm `k`'s payoff unchanged. -/
theorem monComp_no_interaction (f : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) (x : ℝ → ℝ) {j0 k : ℝ} (hk : k ≠ j0)
    (y : ℝ) :
    Φ (update x j0 y k) (∫ j in (0 : ℝ)..1, f (update x j0 y j)) =
      Φ (x k) (∫ j in (0 : ℝ)..1, f (x j)) := by
  rw [monComp_index_update, update_of_ne hk]

/-- A symmetric equilibrium of the monopolistic competition model (MWG, p. 400): every firm
charges `p* > 0`, which maximizes `(p − c)ψ(p/G'(x̄*))` over `p > 0` given the index, and the index
is `x̄* = ∫₀¹ f(x_j(p*, x̄*)) dj` with `x_j(p, x̄) = ψ(p/G'(x̄))`. -/
def IsMonCompEqm (f G' ψ : ℝ → ℝ) (c X ps : ℝ) : Prop :=
  0 < ps ∧ (∀ p, 0 < p → (p - c) * ψ (p / G' X) ≤ (ps - c) * ψ (ps / G' X)) ∧
    X = ∫ _j in (0 : ℝ)..1, f (ψ (ps / G' X))

/-- **Monopolistic competition: an example** (MWG, p. 400). With `G(X) = log X` (`G'(X) = 1/X`),
`f(x) = 2√x` (`f'(x) = 1/√x`, inverted by `ψ(r) = 1/r²`) and cost `c > 0`, the price `p* = 2c` and
index `x̄* = 1/√c` form a symmetric equilibrium. -/
theorem monComp_example {c : ℝ} (hc : 0 < c) :
    (∀ x : ℝ, 0 < x → HasDerivAt (fun x => 2 * √x) (1 / √x) x) ∧
    (∀ x : ℝ, 0 < x → (fun r : ℝ => 1 / r ^ 2) (1 / √x) = x) ∧
    IsMonCompEqm (fun x => 2 * √x) (fun X => 1 / X) (fun r => 1 / r ^ 2) c (1 / √c) (2 * c) := by
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hcc : √c * √c = c := Real.mul_self_sqrt hc.le
  refine ⟨fun x hx => ?_, fun x hx => ?_, by linarith, fun p hp => ?_, ?_⟩
  · have := (Real.hasDerivAt_sqrt hx.ne').const_mul 2
    convert this using 1
    have : 0 < √x := Real.sqrt_pos.2 hx
    field_simp
  · have : √x ^ 2 = x := Real.sq_sqrt hx.le
    simp only [one_div, inv_pow, inv_inv, this]
  · have e1 : 1 / (p / (1 / (1 / √c))) ^ 2 = c / p ^ 2 := by
      rw [one_div_one_div, div_pow, Real.sq_sqrt hc.le]; field_simp
    have e2 : 1 / (2 * c / (1 / (1 / √c))) ^ 2 = 1 / (4 * c) := by
      rw [one_div_one_div, div_pow, Real.sq_sqrt hc.le]; field_simp; ring
    beta_reduce
    rw [e1, e2]
    rw [show (p - c) * (c / p ^ 2) = c * (p - c) / p ^ 2 by ring,
      show (2 * c - c) * (1 / (4 * c)) = 1 / 4 by field_simp; ring,
      div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p - 2 * c)]
  · rw [intervalIntegral.integral_const, sub_zero, one_smul]
    have e : 1 / (2 * c / (1 / (1 / √c))) ^ 2 = (1 / (2 * √c)) ^ 2 := by
      have r : (1 / (2 * √c)) ^ 2 = 1 / (4 * c) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hc.le]; ring
      rw [r, one_div_one_div, div_pow, Real.sq_sqrt hc.le]; field_simp; ring
    beta_reduce
    rw [e, Real.sqrt_sq (by positivity)]
    field_simp

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Mixed strategies in the Bertrand duopoly

MWG, Exercise 12.C.2, p. 430 (footnote 9, p. 388).

A mixed strategy is a probability measure `σ` on prices (Mathlib's `Measure ℝ`) that puts no
mass on negative prices (`IsMixedPrice`). A firm naming `p` against a rival naming `q` earns
`(p − c)x(p)` if `p < q`, half of it if `p = q` and `0` if `p > q` (`mbProfit`; this is firm 0's
and, with the arguments swapped, firm 1's payoff in Chapter 12's `bertrandProfit`,
`mbProfit_fst`, `mbProfit_snd`). Expected profit is the iterated integral
`∫∫ mbProfit(p, q) dτ(q) dσ(p)` (`mbPayoff`); on the price set `[0, ∞)` the profit is bounded and
measurable, so this is the expectation over the product of the two mixed strategies.
`IsMixedBertrandNE` asks that no firm gain from any mixed deviation.

* `mbProfit_integral`: against a mixed strategy `τ`, the pure price `p` earns
  `(p − c)x(p)·(τ(p, ∞) + τ[p, ∞))/2`.
* `exercise_12_C_2`: under the assumptions of Proposition 12.C.1 (`x` continuous, nonnegative,
  strictly decreasing where positive, `x(p) = 0` for `p ≥ p̄`, `x(c) > 0`, `c > 0`), both firms
  naming `c` with certainty is a Nash equilibrium in mixed strategies, and it is the only one.

The proof of uniqueness: in an equilibrium each firm's expected profit `Vᵢ` is attained at almost
every price it names (`mb_ae_eq`). If `V₁ > 0`, firm 1 never names a price below
`c + V₁/x(c)`, so firm 2 earns a positive profit by naming a price just above `c`
(`mb_rival_pos`). If both profits are positive, both strategies have an atom at a common highest
price `B` (`mb_top_atom`), and undercutting `B` slightly almost doubles firm 1's profit. So
`V₁ = V₂ = 0`; then no firm names a price above `c` (it would leave the rival a profitable
price) and no firm names a price below `c` with positive probability (`mb_below_null`).

Departure: MWG does not specify the price space; mixed strategies here are supported on
`[0, ∞)`, which makes expected profits bounded (see `docs/corrections.md`).
-/

namespace MWG.MarketPower

open MeasureTheory Set Function

/-- The profit of a duopolist naming `p` against a rival naming `q` (MWG, p. 388):
`(p − c)x(p)` if `p < q`, `(p − c)x(p)/2` if `p = q`, `0` if `p > q`. -/
noncomputable def mbProfit (x : ℝ → ℝ) (c p q : ℝ) : ℝ :=
  (p - c) * (if p < q then x p else if p = q then x p / 2 else 0)

theorem mbProfit_fst (x : ℝ → ℝ) (c p q : ℝ) :
    bertrandProfit x c ![p, q] 0 = mbProfit x c p q := by
  unfold bertrandProfit mbProfit
  rw [bertrandSales_duopoly]
  rfl

theorem mbProfit_snd (x : ℝ → ℝ) (c p q : ℝ) :
    bertrandProfit x c ![p, q] 1 = mbProfit x c q p := by
  unfold bertrandProfit mbProfit
  rcases lt_trichotomy q p with h | h | h
  · unfold bertrandSales
    have hall : ∀ k, ![p, q] 1 ≤ ![p, q] k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (Finset.univ.filter fun k => ![p, q] k = ![p, q] 1) = {1} := by
      ext k; fin_cases k <;> simp [h.ne']
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · unfold bertrandSales
    have hall : ∀ k, ![p, q] 1 ≤ ![p, q] k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (Finset.univ.filter fun k => ![p, q] k = ![p, q] 1) = Finset.univ := by
      ext k; fin_cases k <;> simp [h]
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · rw [bertrandSales_of_gt (k := 0) (by simpa using h)]
    simp [h.not_gt, h.ne']

/-- The probability weight with which a price `p` wins against `τ`, counting ties half:
`(τ(p, ∞) + τ[p, ∞))/2 = τ(p, ∞) + τ{p}/2`. -/
noncomputable def mbWin (τ : Measure ℝ) (p : ℝ) : ℝ := (τ.real (Ioi p) + τ.real (Ici p)) / 2

theorem mbProfit_indicator (x : ℝ → ℝ) (c p q : ℝ) :
    mbProfit x c p q = (p - c) * x p * (((Ioi p).indicator 1 q + (Ici p).indicator 1 q) / 2) := by
  unfold mbProfit
  rcases lt_trichotomy p q with h | h | h
  · simp [h, h.le]
  · subst h; simp; ring
  · have h1 : q ∉ Ioi p := fun hq => absurd (mem_Ioi.1 hq) (not_lt.2 h.le)
    have h2 : q ∉ Ici p := fun hq => absurd (mem_Ici.1 hq) (not_le.2 h)
    simp [h.not_gt, h.ne', h1, h2]

/-- **Expected profit of a pure price against a mixed strategy** (MWG, Exercise 12.C.2):
`∫ mbProfit(p, q) dτ(q) = (p − c)x(p)·mbWin τ p` for any finite measure `τ`. -/
theorem mbProfit_integral (x : ℝ → ℝ) (c p : ℝ) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    ∫ q, mbProfit x c p q ∂τ = (p - c) * x p * mbWin τ p := by
  simp_rw [mbProfit_indicator]
  rw [integral_const_mul, integral_div, integral_add, integral_indicator_one measurableSet_Ioi,
    integral_indicator_one measurableSet_Ici]
  · rfl
  · exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  · exact (integrable_const (1 : ℝ)).indicator measurableSet_Ici

/-- A mixed price strategy: a probability measure on prices with no mass on negative prices. -/
def IsMixedPrice (σ : Measure ℝ) : Prop := IsProbabilityMeasure σ ∧ σ (Iio 0) = 0

/-- The expected profit of a firm playing `σ` against a rival playing `τ`. -/
noncomputable def mbPayoff (x : ℝ → ℝ) (c : ℝ) (σ τ : Measure ℝ) : ℝ :=
  ∫ p, ∫ q, mbProfit x c p q ∂τ ∂σ

/-- A Nash equilibrium in mixed strategies of the Bertrand duopoly: no firm gains from any mixed
deviation (MWG, p. 388, footnote 9, and Exercise 12.C.2). -/
def IsMixedBertrandNE (x : ℝ → ℝ) (c : ℝ) (σ₁ σ₂ : Measure ℝ) : Prop :=
  IsMixedPrice σ₁ ∧ IsMixedPrice σ₂ ∧
    (∀ σ, IsMixedPrice σ → mbPayoff x c σ σ₂ ≤ mbPayoff x c σ₁ σ₂) ∧
    (∀ σ, IsMixedPrice σ → mbPayoff x c σ σ₁ ≤ mbPayoff x c σ₂ σ₁)

theorem mbPayoff_eq (x : ℝ → ℝ) (c : ℝ) (σ τ : Measure ℝ) [IsFiniteMeasure τ] :
    mbPayoff x c σ τ = ∫ p, (p - c) * x p * mbWin τ p ∂σ := by
  unfold mbPayoff
  congr 1
  funext p
  exact mbProfit_integral x c p τ

theorem mbPayoff_dirac (x : ℝ → ℝ) (c p : ℝ) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    mbPayoff x c (Measure.dirac p) τ = (p - c) * x p * mbWin τ p := by
  rw [mbPayoff_eq, integral_dirac]

theorem isMixedPrice_dirac {p : ℝ} (hp : 0 ≤ p) : IsMixedPrice (Measure.dirac p) := by
  refine ⟨inferInstance, ?_⟩
  rw [Measure.dirac_apply' p measurableSet_Iio]
  exact indicator_of_notMem (fun h => absurd (mem_Iio.1 h) (not_lt.2 hp)) _

theorem mbWin_nonneg (τ : Measure ℝ) (p : ℝ) : 0 ≤ mbWin τ p := by
  unfold mbWin; positivity

theorem mbWin_le_Ici (τ : Measure ℝ) [IsFiniteMeasure τ] (p : ℝ) :
    mbWin τ p ≤ τ.real (Ici p) := by
  unfold mbWin
  have := measureReal_mono (μ := τ) (Ioi_subset_Ici_self (a := p))
  linarith

theorem mbWin_le_one (τ : Measure ℝ) [IsProbabilityMeasure τ] (p : ℝ) : mbWin τ p ≤ 1 := by
  have h1 := mbWin_le_Ici τ p
  have h2 : τ.real (Ici p) ≤ 1 := measureReal_le_one
  linarith

theorem mbWin_antitone (τ : Measure ℝ) [IsFiniteMeasure τ] : Antitone (mbWin τ) := by
  intro p p' h
  unfold mbWin
  have h1 := measureReal_mono (μ := τ) (Ioi_subset_Ioi h)
  have h2 := measureReal_mono (μ := τ) (Ici_subset_Ici.2 h)
  linarith

theorem mb_x_anti {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar) {p p' : ℝ}
    (h : p ≤ p') : x p' ≤ x p := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  rcases eq_or_lt_of_le (hx.nonneg p') with h0 | h0
  · rw [← h0]; exact hx.nonneg p
  · exact (hx.strictAnti p p' h h0).le

/-- The profit `(p − c)x(p)` is bounded on `[0, ∞)`. -/
theorem mb_bound {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar) (c : ℝ) :
    ∃ G, 0 ≤ G ∧ ∀ p, 0 ≤ p → |(p - c) * x p| ≤ G := by
  have hg : Continuous fun p => (p - c) * x p :=
    (continuous_id.sub continuous_const).mul hx.cont
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max pbar 0)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max G 0, le_max_right _ _, fun p hp => ?_⟩
  by_cases h : p ≤ max pbar 0
  · have := hG p ⟨hp, h⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · push Not at h
    rw [hx.zero p (le_trans (le_max_left _ _) h.le), mul_zero, abs_zero]
    exact le_max_right _ _

/-- A property holding almost everywhere holds at some point of a set of positive measure. -/
theorem mb_exists_mem {σ : Measure ℝ} {s : Set ℝ} {Q : ℝ → Prop} (hs : σ s ≠ 0)
    (hQ : ∀ᵐ p ∂σ, Q p) : ∃ p ∈ s, Q p := by
  by_contra h
  push Not at h
  exact hs (measure_mono_null (fun p hp => h p hp) (ae_iff.1 hQ))

theorem mb_ae_nonneg {σ : Measure ℝ} (h0 : σ (Iio 0) = 0) : ∀ᵐ p ∂σ, 0 ≤ p := by
  rw [ae_iff]
  simp only [not_le]
  exact h0

/-- In a best response `σ` to `τ`, almost every price named earns the expected profit: if no
pure price `p ≥ 0` earns more than `V = U(σ, τ)`, then `(p − c)x(p)·mbWin τ p = V` for
`σ`-almost every `p`. -/
theorem mb_ae_eq {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) {σ τ : Measure ℝ}
    [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (h0 : σ (Iio 0) = 0)
    (hbr : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p ≤ mbPayoff x c σ τ) :
    ∀ᵐ p ∂σ, (p - c) * x p * mbWin τ p = mbPayoff x c σ τ := by
  have hpos := mb_ae_nonneg h0
  obtain ⟨G, -, hG⟩ := mb_bound hx c
  have hmeas : Measurable fun p => (p - c) * x p * mbWin τ p :=
    (((continuous_id.sub continuous_const).mul hx.cont).measurable).mul
      (mbWin_antitone τ).measurable
  have hint : Integrable (fun p => (p - c) * x p * mbWin τ p) σ := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable G (hpos.mono fun p hp => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mbWin_nonneg τ p)]
    have h1 := hG p hp
    have h2 := mbWin_le_one τ p
    have h3 := mbWin_nonneg τ p
    nlinarith [abs_nonneg ((p - c) * x p)]
  have hle : (fun p => (p - c) * x p * mbWin τ p) ≤ᵐ[σ] fun _ => mbPayoff x c σ τ :=
    hpos.mono fun p hp => hbr p hp
  have heq : ∫ p, (p - c) * x p * mbWin τ p ∂σ = ∫ _, mbPayoff x c σ τ ∂σ := by
    rw [integral_const, ← mbPayoff_eq]
    simp
  exact (integral_eq_iff_of_ae_le hint (integrable_const _) hle).1 heq

/-- If a firm's best response earns `V > 0`, it names no price below `c + V/x(c)`. -/
theorem mb_gap {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hxc : 0 < x c)
    {σ τ : Measure ℝ} [IsProbabilityMeasure τ] {V : ℝ} (hV : 0 < V)
    (hae : ∀ᵐ p ∂σ, 0 ≤ p ∧ (p - c) * x p * mbWin τ p = V) : σ (Iio (c + V / x c)) = 0 := by
  refine measure_mono_null ?_ (ae_iff.1 hae)
  intro p hp hgood
  obtain ⟨-, heq⟩ := hgood
  have hw0 := mbWin_nonneg τ p
  have hw1 := mbWin_le_one τ p
  rcases le_or_gt p c with h | h
  · have : (p - c) * x p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg p)
    nlinarith
  · have hg0 : 0 ≤ (p - c) * x p := mul_nonneg (by linarith) (hx.nonneg p)
    have h1 : (p - c) * x p * mbWin τ p ≤ (p - c) * x p := mul_le_of_le_one_right hg0 hw1
    have h2 : (p - c) * x p ≤ (p - c) * x c :=
      mul_le_mul_of_nonneg_left (mb_x_anti hx h.le) (by linarith)
    have h3 : (p - c) * x c < V := by
      have : p - c < V / x c := by linarith [mem_Iio.1 hp]
      exact (lt_div_iff₀ hxc).1 this
    linarith

/-- Against a strategy with no mass below `e`, prices below `e` win for sure. -/
theorem mb_win_one {σ : Measure ℝ} [IsProbabilityMeasure σ] {e p : ℝ} (he : σ (Iio e) = 0)
    (hp : p < e) : mbWin σ p = 1 := by
  have h0 : σ (Iic p) = 0 := measure_mono_null (Iic_subset_Iio.2 hp) he
  have h1 : σ (Ioi p) = 1 := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, h0, tsub_zero]
  have h2 : σ (Ici p) = 1 := le_antisymm prob_le_one (h1 ▸ measure_mono Ioi_subset_Ici_self)
  unfold mbWin
  simp [Measure.real, h1, h2]

/-- If the rival names no price below `e > c`, a price just above `c` earns a positive
profit. -/
theorem mb_rival_pos {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) {σ : Measure ℝ} [IsProbabilityMeasure σ] {e : ℝ} (hce : c < e)
    (he : σ (Iio e) = 0) : ∃ p, 0 ≤ p ∧ 0 < (p - c) * x p * mbWin σ p := by
  obtain ⟨p, hpc, hpe, hgain⟩ := bertrand_deviation hx hxc hce
  refine ⟨p, by linarith, ?_⟩
  rw [mb_win_one he hpe, mul_one]
  have : 0 ≤ (e - c) * x e / 2 := div_nonneg (mul_nonneg (by linarith) (hx.nonneg e)) (by norm_num)
  linarith

/-- Almost every point `p` has `μ[p, ∞) > 0`. -/
theorem mb_ae_Ici_ne_zero (μ : Measure ℝ) : ∀ᵐ p ∂μ, μ (Ici p) ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  by_cases hmin : ∃ m, μ (Ici m) = 0 ∧ ∀ p, μ (Ici p) = 0 → m ≤ p
  · obtain ⟨m, hm, hle⟩ := hmin
    exact measure_mono_null (fun p hp => mem_Ici.2 (hle p hp)) hm
  · push Not at hmin
    have hsub : {p | μ (Ici p) = 0} ⊆
        ⋃ q : {q : ℚ // μ (Ici ((q : ℚ) : ℝ)) = 0}, Ici ((q.1 : ℚ) : ℝ) := by
      intro p hp
      obtain ⟨p', hp', hlt⟩ := hmin p hp
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact mem_iUnion.2 ⟨⟨q, measure_mono_null (Ici_subset_Ici.2 hq1.le) hp'⟩, hq2.le⟩
    exact measure_mono_null hsub (measure_iUnion_null fun q => q.2)

/-- If both firms earn positive profits, both mixed strategies have an atom at a common top
price; this is the one-sided step: `σ` has no mass above `B`, an atom at `B`, and `τ[B, ∞) > 0`.
-/
theorem mb_top_atom {σ τ : Measure ℝ} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    {ε pbar : ℝ} (hε : 0 < ε) (hσ : ∀ᵐ p ∂σ, ε ≤ τ.real (Ici p))
    (hτ : ∀ᵐ p ∂τ, σ (Ici p) ≠ 0) (hbar : τ (Ici pbar) = 0) :
    ∃ B, σ (Ioi B) = 0 ∧ σ {B} ≠ 0 ∧ τ (Ici B) ≠ 0 := by
  set T := {p | ε ≤ τ.real (Ici p)} with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, -, hp⟩ := mb_exists_mem (s := univ) (by simp) hσ
    exact ⟨p, hp⟩
  have hTbdd : BddAbove T := by
    refine ⟨pbar, fun p hp => ?_⟩
    by_contra h
    push Not at h
    have : τ.real (Ici p) = 0 :=
      (measureReal_eq_zero_iff).2 (measure_mono_null (Ici_subset_Ici.2 h.le) hbar)
    have hp' : ε ≤ τ.real (Ici p) := hp
    linarith
  set B := sSup T with hB
  have hIoi : σ (Ioi B) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hσ)
    intro p hp hpT
    exact absurd (le_csSup hTbdd hpT) (not_le.2 hp)
  have hIci : τ (Ici B) ≠ 0 := by
    have hseq : ⋂ n : ℕ, Ici (B - 1 / ((n : ℝ) + 1)) = Ici B := by
      ext p
      simp only [mem_iInter, mem_Ici]
      constructor
      · intro h
        by_contra hlt
        push Not at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        have := h n
        linarith
      · intro h n
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hanti : Antitone fun n : ℕ => Ici (B - 1 / ((n : ℝ) + 1)) := by
      intro m n hmn
      apply Ici_subset_Ici.2
      have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hmn'
      linarith
    have hlow : ∀ n : ℕ, ENNReal.ofReal ε ≤ τ (Ici (B - 1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hTne (show B - 1 / ((n : ℝ) + 1) < B by
        linarith)
      have ht' : ε ≤ τ.real (Ici t) := ht
      have h1 : ε ≤ τ.real (Ici (B - 1 / ((n : ℝ) + 1))) :=
        le_trans ht' (measureReal_mono (Ici_subset_Ici.2 hlt.le))
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal h1
    have hinf := hanti.measure_iInter (μ := τ) (fun n => measurableSet_Ici.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
    rw [hseq] at hinf
    have hge : ENNReal.ofReal ε ≤ τ (Ici B) := by rw [hinf]; exact le_iInf hlow
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) hge)
  obtain ⟨p, hpB, hp⟩ := mb_exists_mem hIci hτ
  have hpB' : p ≤ B := by
    by_contra h
    push Not at h
    exact hp (measure_mono_null (Ici_subset_Ioi.2 h) hIoi)
  have hpeq : p = B := le_antisymm hpB' hpB
  refine ⟨B, hIoi, fun h0 => hp ?_, hIci⟩
  rw [hpeq]
  refine measure_mono_null (fun q hq => ?_) (measure_union_null h0 hIoi)
  rcases eq_or_lt_of_le (mem_Ici.1 hq) with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

/-- Undercutting a common atom: if firm `i` earns `V > 0` at a price `B` at which the rival has
no mass above `B`, a price slightly below `B` earns more than `V`. -/
theorem mb_undercut {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) {τ : Measure ℝ} [IsProbabilityMeasure τ] {B V : ℝ} (hV : 0 < V)
    (hB : (B - c) * x B * mbWin τ B = V) (hτB : τ (Ioi B) = 0)
    (hbr : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p ≤ V) : False := by
  set a := τ.real (Ici B) with ha_def
  have hw : mbWin τ B = a / 2 := by
    unfold mbWin
    rw [show τ.real (Ioi B) = 0 from (measureReal_eq_zero_iff).2 hτB]
    ring
  have ha : 0 ≤ a := measureReal_nonneg
  rw [hw] at hB
  have hgB : 0 < (B - c) * x B := by
    by_contra h
    push Not at h
    nlinarith
  have hBc : c < B := by
    by_contra h
    push Not at h
    nlinarith [hx.nonneg B]
  obtain ⟨p', hp'c, hp'B, hgain⟩ := bertrand_deviation hx hxc hBc
  have hw' : a ≤ mbWin τ p' := by
    unfold mbWin
    have h1 : a ≤ τ.real (Ioi p') := measureReal_mono (Ici_subset_Ioi.2 hp'B)
    have h2 : a ≤ τ.real (Ici p') := measureReal_mono (Ici_subset_Ici.2 hp'B.le)
    linarith
  have hdev := hbr p' (by linarith)
  have hg' : 0 < (p' - c) * x p' := by linarith [half_pos hgB]
  have ha' : 0 < a := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hB; simp at hB; linarith
    · exact h
  nlinarith [mul_le_mul_of_nonneg_left hw' hg'.le, mul_lt_mul_of_pos_right hgain ha']

/-- If no price `p ≥ 0` earns a positive profit against `τ`, then `τ` puts no mass above `c`. -/
theorem mb_above_null {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) {τ : Measure ℝ} [IsFiniteMeasure τ]
    (hbr : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p ≤ 0) : τ (Ioi c) = 0 := by
  have hev : ∀ᶠ p in nhds c, 0 < x p := hx.cont.continuousAt.eventually (lt_mem_nhds hxc)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hnull : ∀ p, c < p → p < c + δ → τ (Ici p) = 0 := by
    intro p h1 h2
    have hxp : 0 < x p := hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hg : 0 < (p - c) * x p := mul_pos (by linarith) hxp
    have hle := hbr p (by linarith)
    have hw0 := mbWin_nonneg τ p
    have hw : mbWin τ p = 0 := by
      by_contra hne
      have := mul_pos hg (lt_of_le_of_ne hw0 (Ne.symm hne))
      linarith
    have hr : τ.real (Ici p) = 0 := by
      unfold mbWin at hw
      linarith [measureReal_nonneg (μ := τ) (s := Ioi p), measureReal_nonneg (μ := τ) (s := Ici p)]
    exact (measureReal_eq_zero_iff).1 hr
  have hsub : Ioi c ⊆ ⋃ n : ℕ, Ici (c + δ / ((n : ℝ) + 2)) := by
    intro p hp
    have hpc : 0 < (p - c) / δ := div_pos (sub_pos.2 hp) hδ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpc
    refine mem_iUnion.2 ⟨n, mem_Ici.2 ?_⟩
    have h1 : δ / ((n : ℝ) + 2) ≤ δ / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_left hδ.le (by positivity) (by linarith)
    have h2 : δ / ((n : ℝ) + 1) < p - c := by
      rw [lt_div_iff₀ hδ] at hn
      rw [div_lt_iff₀ (by positivity)]
      have := hn
      field_simp at this ⊢
      linarith
    linarith
  refine measure_mono_null hsub (measure_iUnion_null fun n => hnull _ ?_ ?_)
  · have : 0 < δ / ((n : ℝ) + 2) := by positivity
    linarith
  · have : δ / ((n : ℝ) + 2) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith

/-- A price below `c` that earns zero against `τ` leaves `τ` no mass at or above it. -/
theorem mb_low_price {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hxc : 0 < x c)
    {τ : Measure ℝ} [IsFiniteMeasure τ] {p : ℝ} (hp : p < c)
    (h0 : (p - c) * x p * mbWin τ p = 0) : τ (Ici p) = 0 := by
  have hxp : 0 < x p := lt_of_lt_of_le hxc (mb_x_anti hx hp.le)
  have hg : (p - c) * x p ≠ 0 := (mul_neg_of_neg_of_pos (by linarith) hxp).ne
  have hw : mbWin τ p = 0 := (mul_eq_zero.1 h0).resolve_left hg
  have hr : τ.real (Ici p) = 0 := by
    unfold mbWin at hw
    linarith [measureReal_nonneg (μ := τ) (s := Ioi p), measureReal_nonneg (μ := τ) (s := Ici p)]
  exact (measureReal_eq_zero_iff).1 hr

/-- When both firms earn zero, neither names a price below `c` with positive probability. -/
theorem mb_below_null {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hxc : 0 < x c)
    {σ τ : Measure ℝ} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hσ : ∀ᵐ p ∂σ, (p - c) * x p * mbWin τ p = 0) (hτ : ∀ᵐ p ∂τ, (p - c) * x p * mbWin σ p = 0) :
    σ (Iio c) = 0 := by
  by_contra h1
  obtain ⟨p₁, hp₁, hF, hne⟩ := mb_exists_mem h1 (hσ.and (mb_ae_Ici_ne_zero σ))
  have hp₁c : p₁ < c := hp₁
  have hτ1 : τ (Ici p₁) = 0 := mb_low_price hx hxc hp₁c hF
  have hτlow : τ (Iio p₁) ≠ 0 := by
    intro h
    have : τ univ ≤ τ (Iio p₁) + τ (Ici p₁) :=
      calc τ univ = τ (Iio p₁ ∪ Ici p₁) := by rw [Iio_union_Ici]
        _ ≤ _ := measure_union_le _ _
    simp [h, hτ1] at this
  obtain ⟨p₂, hp₂, hF'⟩ := mb_exists_mem hτlow hτ
  have hp₂' : p₂ < p₁ := hp₂
  have hσ2 : σ (Ici p₂) = 0 := mb_low_price hx hxc (by linarith) hF'
  exact hne (measure_mono_null (Ici_subset_Ici.2 hp₂'.le) hσ2)

/-- A probability measure with no mass off `{c}` is the point mass at `c`. -/
theorem mb_eq_dirac {σ : Measure ℝ} [IsProbabilityMeasure σ] {c : ℝ} (h1 : σ (Iio c) = 0)
    (h2 : σ (Ioi c) = 0) : σ = Measure.dirac c := by
  have hcompl : σ ({c}ᶜ) = 0 := by
    refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
    rcases lt_or_gt_of_ne (show p ≠ c from hp) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hone : σ {c} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton c)).1 hcompl
  have hae : ∀ᵐ p ∂σ, p ∈ ({c} : Finset ℝ) := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hcompl
    simpa using hp
  rw [Measure.ae_mem_finset_iff] at hae
  rw [hae]
  simp [hone]

/-- **Exercise 12.C.2** (MWG, p. 430). Under the assumptions of Proposition 12.C.1 (demand `x`
continuous, nonnegative, strictly decreasing where positive, `x(p) = 0` for `p ≥ p̄`, `x(c) > 0`,
`c > 0`), both firms setting their price equal to `c` with certainty is a Nash equilibrium of the
Bertrand duopoly in mixed strategies, and it is the unique one: every mixed-strategy Nash
equilibrium is `(δ_c, δ_c)`. -/
theorem exercise_12_C_2 {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) :
    IsMixedBertrandNE x c (Measure.dirac c) (Measure.dirac c) ∧
    ∀ σ₁ σ₂, IsMixedBertrandNE x c σ₁ σ₂ → σ₁ = Measure.dirac c ∧ σ₂ = Measure.dirac c := by
  constructor
  · -- against `δ_c` no strategy earns a positive profit
    have hle : ∀ σ : Measure ℝ, mbPayoff x c σ (Measure.dirac c) ≤ 0 := by
      intro σ
      rw [mbPayoff_eq]
      refine integral_nonpos fun p => ?_
      rcases le_or_gt p c with h | h
      · exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg p)) (mbWin_nonneg _ p)
      · have hw : mbWin (Measure.dirac c) p = 0 := by
          unfold mbWin
          rw [Measure.dirac_real_apply, Measure.dirac_real_apply,
            indicator_of_notMem (fun hm => absurd (mem_Ioi.1 hm) (not_lt.2 h.le)),
            indicator_of_notMem (fun hm => absurd (mem_Ici.1 hm) (not_le.2 h))]
          norm_num
        simp [hw]
    have h0 : mbPayoff x c (Measure.dirac c) (Measure.dirac c) = 0 := by
      rw [mbPayoff_dirac]; ring
    have hP : IsMixedPrice (Measure.dirac c) := isMixedPrice_dirac hc.le
    exact ⟨hP, hP, fun σ _ => h0 ▸ hle σ, fun σ _ => h0 ▸ hle σ⟩
  · rintro σ₁ σ₂ ⟨⟨hP1, h01⟩, ⟨hP2, h02⟩, hbr1, hbr2⟩
    -- pure deviations
    have hb1 : ∀ p, 0 ≤ p → (p - c) * x p * mbWin σ₂ p ≤ mbPayoff x c σ₁ σ₂ := fun p hp => by
      rw [← mbPayoff_dirac]; exact hbr1 _ (isMixedPrice_dirac hp)
    have hb2 : ∀ p, 0 ≤ p → (p - c) * x p * mbWin σ₁ p ≤ mbPayoff x c σ₂ σ₁ := fun p hp => by
      rw [← mbPayoff_dirac]; exact hbr2 _ (isMixedPrice_dirac hp)
    set V₁ := mbPayoff x c σ₁ σ₂ with hV₁
    set V₂ := mbPayoff x c σ₂ σ₁ with hV₂
    have hae1 : ∀ᵐ p ∂σ₁, (p - c) * x p * mbWin σ₂ p = V₁ := mb_ae_eq hx h01 hb1
    have hae2 : ∀ᵐ p ∂σ₂, (p - c) * x p * mbWin σ₁ p = V₂ := mb_ae_eq hx h02 hb2
    have hpos1 := mb_ae_nonneg h01
    have hpos2 := mb_ae_nonneg h02
    -- profits are nonnegative: a price above `p̄` sells nothing
    have hq : ∀ τ : Measure ℝ, (max pbar 0 - c) * x (max pbar 0) * mbWin τ (max pbar 0) = 0 := by
      intro τ; rw [hx.zero _ (le_max_left _ _)]; ring
    have hV₁0 : 0 ≤ V₁ := (hq σ₂).symm.le.trans (hb1 _ (le_max_right _ _))
    have hV₂0 : 0 ≤ V₂ := (hq σ₁).symm.le.trans (hb2 _ (le_max_right _ _))
    -- step 1: a positive profit for one firm gives a positive profit to the other
    have step1 : ∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (V W : ℝ),
        0 < V → (∀ᵐ p ∂σ, 0 ≤ p ∧ (p - c) * x p * mbWin τ p = V) →
        (∀ p, 0 ≤ p → (p - c) * x p * mbWin σ p ≤ W) → 0 < W := by
      intro σ τ _ _ V W hV hae hbr
      have hgap := mb_gap hx hxc hV hae
      have hce : c < c + V / x c := by have := div_pos hV hxc; linarith
      obtain ⟨p, hp, hpos⟩ := mb_rival_pos hx hc hxc hce hgap
      linarith [hbr p hp]
    -- step 2: both profits cannot be positive
    have step2 : ¬ (0 < V₁ ∧ 0 < V₂) := by
      rintro ⟨hv1, hv2⟩
      obtain ⟨G, hG0, hG⟩ := mb_bound hx c
      -- almost every price of firm `i` wins with probability at least `Vᵢ/G`
      have hwin : ∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (V : ℝ),
          0 < V → (∀ᵐ p ∂σ, 0 ≤ p ∧ (p - c) * x p * mbWin τ p = V) →
          0 < G ∧ ∀ᵐ p ∂σ, V / G ≤ τ.real (Ici p) := by
        intro σ τ _ _ V hV hae
        have hkey : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p = V → V ≤ G * τ.real (Ici p) := by
          intro p hp heq
          have h1 := hG p hp
          have h2 := mbWin_le_Ici τ p
          have h3 := mbWin_nonneg τ p
          have h4 : (p - c) * x p ≤ G := (le_abs_self _).trans h1
          calc V = (p - c) * x p * mbWin τ p := heq.symm
            _ ≤ G * mbWin τ p := mul_le_mul_of_nonneg_right h4 h3
            _ ≤ G * τ.real (Ici p) := mul_le_mul_of_nonneg_left h2 hG0
        obtain ⟨p, -, hp, heq⟩ := mb_exists_mem (s := univ) (by simp) hae
        have hGpos : 0 < G := by
          have := hkey p hp heq
          have h5 : τ.real (Ici p) ≤ 1 := measureReal_le_one
          nlinarith
        refine ⟨hGpos, hae.mono fun p ⟨hp, heq⟩ => ?_⟩
        rw [div_le_iff₀ hGpos, mul_comm]
        exact hkey p hp heq
      -- almost every price named earns a positive profit, so wins with positive probability
      have hsupp : ∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsFiniteMeasure τ] (V : ℝ),
          0 < V → (∀ᵐ p ∂σ, (p - c) * x p * mbWin τ p = V) →
          (∀ᵐ p ∂σ, τ (Ici p) ≠ 0) ∧ σ (Ici pbar) = 0 := by
        intro σ τ _ _ V hV hae
        constructor
        · refine hae.mono fun p heq h0 => ?_
          have hr : τ.real (Ici p) = 0 := (measureReal_eq_zero_iff).2 h0
          have := mbWin_le_Ici τ p
          have hw : mbWin τ p = 0 := le_antisymm (hr ▸ this) (mbWin_nonneg τ p)
          rw [hw, mul_zero] at heq
          linarith
        · refine measure_mono_null ?_ (ae_iff.1 hae)
          intro p hp heq
          rw [hx.zero p hp] at heq
          simp at heq
          linarith
      have hae1' : ∀ᵐ p ∂σ₁, 0 ≤ p ∧ (p - c) * x p * mbWin σ₂ p = V₁ := hpos1.and hae1
      have hae2' : ∀ᵐ p ∂σ₂, 0 ≤ p ∧ (p - c) * x p * mbWin σ₁ p = V₂ := hpos2.and hae2
      obtain ⟨hG1, hw1⟩ := hwin σ₁ σ₂ V₁ hv1 hae1'
      obtain ⟨-, hw2⟩ := hwin σ₂ σ₁ V₂ hv2 hae2'
      obtain ⟨hs1, hbar1⟩ := hsupp σ₁ σ₂ V₁ hv1 hae1
      obtain ⟨hs2, hbar2⟩ := hsupp σ₂ σ₁ V₂ hv2 hae2
      obtain ⟨B₁, hB1, hA1, hC1⟩ := mb_top_atom (div_pos hv1 hG1) hw1 hs2 hbar2
      obtain ⟨B₂, hB2, -, hC2⟩ := mb_top_atom (div_pos hv2 hG1) hw2 hs1 hbar1
      have h21 : B₂ ≤ B₁ := by
        by_contra h
        push Not at h
        exact hC2 (measure_mono_null (Ici_subset_Ioi.2 h) hB1)
      have h12 : B₁ ≤ B₂ := by
        by_contra h
        push Not at h
        exact hC1 (measure_mono_null (Ici_subset_Ioi.2 h) hB2)
      have hBeq : B₂ = B₁ := le_antisymm h21 h12
      rw [hBeq] at hB2
      obtain ⟨p, hpB, heq⟩ := mb_exists_mem hA1 hae1
      rw [mem_singleton_iff.1 hpB] at heq
      exact mb_undercut hx hc hxc hv1 heq hB2 hb1
    have hv1 : V₁ = 0 := by
      by_contra h
      have hv1 : 0 < V₁ := lt_of_le_of_ne hV₁0 (Ne.symm h)
      exact step2 ⟨hv1, step1 σ₁ σ₂ V₁ V₂ hv1 (hpos1.and hae1) hb2⟩
    have hv2 : V₂ = 0 := by
      by_contra h
      have hv2 : 0 < V₂ := lt_of_le_of_ne hV₂0 (Ne.symm h)
      exact step2 ⟨step1 σ₂ σ₁ V₂ V₁ hv2 (hpos2.and hae2) hb1, hv2⟩
    -- step 3: with zero profits, both strategies are the point mass at `c`
    rw [hv1] at hb1 hae1
    rw [hv2] at hb2 hae2
    have hup2 := mb_above_null hx hc hxc hb1
    have hup1 := mb_above_null hx hc hxc hb2
    have hlow1 := mb_below_null hx hxc hae1 hae2
    have hlow2 := mb_below_null hx hxc hae2 hae1
    exact ⟨mb_eq_dirac hlow1 hup1, mb_eq_dirac hlow2 hup2⟩

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bertrand competition with different costs

MWG, Exercise 12.C.4, pp. 430-431.

Firm `j` has unit cost `cⱼ`, with `c₁ < c₂`; demand satisfies the assumptions of Proposition 12.C.1
(`IsBertrandDemand`) and `x(c₂) > 0`. Firm 1's profit from selling to the whole market at `p` is
`g₁(p) = (p − c₁)x(p)`. The duopoly is a Chapter 8 game in normal form (`bcGame`) whose payoffs
are `mbProfit` (ties split demand equally).

* (a) `exercise_12_C_4a`: `(p₁, p₂)` is a pure-strategy Nash equilibrium iff `p₁ < p₂`,
  `p₁ ≤ c₂`, `c₁ < p₂` and `g₁(p) ≤ g₁(p₁)` for every `p < p₂`: firm 1 serves the market at a
  price it cannot improve on below `p₂`, and firm 2 cannot profitably undercut.
  `exercise_12_C_4a_none`: if firm 1's monopoly price exceeds `c₂` (`g₁` strictly increasing on
  `[c₁, pᵐ]` with `pᵐ > c₂`) there is no pure-strategy equilibrium: firm 1 wants to price just
  below `c₂`. `exercise_12_C_4a_none_instance`, `exercise_12_C_4a_drastic_instance`: linear
  demand, without and with an equilibrium.
  `exercise_12_C_4a_tieRule`: if ties are resolved in favour of the low-cost firm, the equilibria
  are exactly `p₁ = p₂ ∈ [c₁, c₂]` (under the same monotonicity), so `p₁ = p₂ = c₂` is an
  equilibrium, and in every equilibrium firm 2 plays a weakly dominated strategy.
* (b) Prices on the grid `Δℤ`, `N₂Δ` the smallest grid price above `c₂`, `N₁ = N₂ − 1`:
  `exercise_12_C_4b_eqm`: `(N₁Δ, N₂Δ)` is an equilibrium; `exercise_12_C_4b_char`: every
  equilibrium is `(mΔ, (m + 1)Δ)` with `c₁ ≤ mΔ ≤ c₂`; `exercise_12_C_4b_dominated`: in all of
  them except `(N₁, N₂)` firm 2 plays a weakly dominated strategy, while in `(N₁, N₂)` neither
  firm does (`exercise_12_C_4b_undominated`); `exercise_12_C_4b_limit`: as `Δ → 0` both prices
  converge to `c₂`. `exercise_12_C_4b_instance`: the hypotheses hold for linear demand.

Departure: the book leaves the grid hypotheses implicit ("the grid becomes finer"); part (b)
assumes `Δ` small in the explicit forms listed in `exercise_12_C_4b_eqm` (see
`docs/corrections.md`).
-/

namespace MWG.MarketPower

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Set Function Filter Topology

/-- A two-player game in normal form with common strategy set `S` and payoffs
`u₀(s₀, s₁)`, `u₁(s₁, s₀)` (own strategy first). -/
def bcGame (S : Type*) (u₀ u₁ : S → S → ℝ) : NormalForm (Fin 2) (fun _ => S) where
  payoff j s := if j = 0 then u₀ (s 0) (s 1) else u₁ (s 1) (s 0)

theorem bcGame_nash_iff {S : Type*} (u₀ u₁ : S → S → ℝ) (a b : S) :
    IsNashEquilibrium (bcGame S u₀ u₁) ![a, b] ↔
      (∀ s, u₀ s b ≤ u₀ a b) ∧ ∀ s, u₁ s a ≤ u₁ b a := by
  constructor
  · intro h
    refine ⟨fun s => ?_, fun s => ?_⟩
    · have := h 0 s
      simpa [bcGame] using this
    · have := h 1 s
      simpa [bcGame] using this
  · rintro ⟨h0, h1⟩ j s
    fin_cases j
    · simpa [bcGame] using h0 s
    · simpa [bcGame] using h1 s

theorem bcGame_weaklyDominated_one {S : Type*} (u₀ u₁ : S → S → ℝ) (s : S) :
    WeaklyDominated (bcGame S u₀ u₁) 1 s ↔
      ∃ s', (∀ r, u₁ s r ≤ u₁ s' r) ∧ ∃ r, u₁ s r < u₁ s' r := by
  constructor
  · rintro ⟨s', hall, r, hr⟩
    refine ⟨s', fun r' => ?_, r 0, ?_⟩
    · have := hall (fun _ => r')
      simpa [bcGame] using this
    · simpa [bcGame] using hr
  · rintro ⟨s', hall, r, hr⟩
    refine ⟨s', fun r' => ?_, fun _ => r, ?_⟩
    · simpa [bcGame] using hall (r' 0)
    · simpa [bcGame] using hr

theorem bcGame_weaklyDominated_zero {S : Type*} (u₀ u₁ : S → S → ℝ) (s : S) :
    WeaklyDominated (bcGame S u₀ u₁) 0 s ↔
      ∃ s', (∀ r, u₀ s r ≤ u₀ s' r) ∧ ∃ r, u₀ s r < u₀ s' r := by
  constructor
  · rintro ⟨s', hall, r, hr⟩
    refine ⟨s', fun r' => ?_, r 1, ?_⟩
    · have := hall (fun _ => r')
      simpa [bcGame] using this
    · simpa [bcGame] using hr
  · rintro ⟨s', hall, r, hr⟩
    refine ⟨s', fun r' => ?_, fun _ => r, ?_⟩
    · simpa [bcGame] using hall (r' 1)
    · simpa [bcGame] using hr

theorem mbProfit_of_lt (x : ℝ → ℝ) {c p q : ℝ} (h : p < q) :
    mbProfit x c p q = (p - c) * x p := by
  simp [mbProfit, h]

theorem mbProfit_self (x : ℝ → ℝ) (c p : ℝ) : mbProfit x c p p = (p - c) * x p / 2 := by
  simp [mbProfit]; ring

theorem mbProfit_of_gt (x : ℝ → ℝ) {c p q : ℝ} (h : q < p) : mbProfit x c p q = 0 := by
  simp [mbProfit, h.not_gt, h.ne']

/-- A price above every other relevant price sells nothing. -/
theorem mbProfit_high (x : ℝ → ℝ) (c q : ℝ) : mbProfit x c (|q| + 1) q = 0 :=
  mbProfit_of_gt x (by linarith [le_abs_self q])

/-- **Exercise 12.C.4(a)** (MWG, p. 430). With `c₁ < c₂` (`0 < c₁`) and `x(c₂) > 0`, the pure
strategy Nash equilibria of the Bertrand duopoly (ties split equally) are exactly the price pairs
with `p₁ < p₂`, `p₁ ≤ c₂`, `c₁ < p₂` and `(p − c₁)x(p) ≤ (p₁ − c₁)x(p₁)` for all `p < p₂`. -/
theorem exercise_12_C_4a {x : ℝ → ℝ} {pbar c₁ c₂ : ℝ} (hx : IsBertrandDemand x pbar)
    (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hxc₂ : 0 < x c₂) (p₁ p₂ : ℝ) :
    IsNashEquilibrium (bcGame ℝ (mbProfit x c₁) (mbProfit x c₂)) ![p₁, p₂] ↔
      p₁ < p₂ ∧ p₁ ≤ c₂ ∧ c₁ < p₂ ∧ ∀ p, p < p₂ → (p - c₁) * x p ≤ (p₁ - c₁) * x p₁ := by
  have _ := hc₁
  have hxc₁ : 0 < x c₁ := lt_of_lt_of_le hxc₂ (mb_x_anti hx h12.le)
  have hxpos : ∀ p, p ≤ c₂ → 0 < x p := fun p hp => lt_of_lt_of_le hxc₂ (mb_x_anti hx hp)
  rw [bcGame_nash_iff]
  constructor
  · rintro ⟨h1, h2⟩
    -- firm 2's profit is nonnegative
    have hπ2 : 0 ≤ mbProfit x c₂ p₂ p₁ := by
      have := h2 (|p₁| + 1); rwa [mbProfit_high] at this
    have hπ1 : 0 ≤ mbProfit x c₁ p₁ p₂ := by
      have := h1 (|p₂| + 1); rwa [mbProfit_high] at this
    -- against `p₂ > c₁` firm 1 earns a positive profit
    have hpos1 : c₁ < p₂ → 0 < mbProfit x c₁ p₁ p₂ := by
      intro h
      obtain ⟨p', hp'c, hp'm, hgain⟩ := bertrand_deviation hx hxc₁ h
      have := h1 p'
      rw [mbProfit_of_lt x hp'm] at this
      have : 0 ≤ (p₂ - c₁) * x p₂ / 2 := div_nonneg (mul_nonneg (by linarith) (hx.nonneg _))
        (by norm_num)
      linarith
    have hlt : p₁ < p₂ := by
      rcases lt_trichotomy p₁ p₂ with h | h | h
      · exact h
      · exfalso
        subst h
        rw [mbProfit_self] at hπ2
        by_cases hxp : x p₁ = 0
        · have hgt : c₂ < p₁ := by
            by_contra hle; push Not at hle; exact (hxpos p₁ hle).ne' hxp
          have := hpos1 (by linarith)
          rw [mbProfit_self, hxp] at this
          simp at this
        · have hxp' : 0 < x p₁ := lt_of_le_of_ne (hx.nonneg _) (Ne.symm hxp)
          have hge : c₂ ≤ p₁ := by
            by_contra hlt'; push Not at hlt'
            have : (p₁ - c₂) * x p₁ < 0 := mul_neg_of_neg_of_pos (by linarith) hxp'
            linarith
          obtain ⟨p', -, hp'm, hgain⟩ := bertrand_deviation hx hxc₁ (show c₁ < p₁ by linarith)
          have := h1 p'
          rw [mbProfit_of_lt x hp'm, mbProfit_self] at this
          linarith
      · exfalso
        rw [mbProfit_of_gt x h] at hπ1
        have hle : p₂ ≤ c₁ := by
          by_contra h'; push Not at h'; linarith [hpos1 h', mbProfit_of_gt x (c := c₁) h]
        rw [mbProfit_of_lt x h] at hπ2
        have : (p₂ - c₂) * x p₂ < 0 :=
          mul_neg_of_neg_of_pos (by linarith) (hxpos p₂ (by linarith))
        linarith
    have hπ2' : mbProfit x c₂ p₂ p₁ = 0 := mbProfit_of_gt x hlt
    have hle2 : p₁ ≤ c₂ := by
      by_contra h; push Not at h
      obtain ⟨p', hp'c, hp'm, hgain⟩ := bertrand_deviation hx hxc₂ h
      have := h2 p'
      rw [mbProfit_of_lt x hp'm, hπ2'] at this
      have : 0 ≤ (p₁ - c₂) * x p₁ / 2 := div_nonneg (mul_nonneg (by linarith) (hx.nonneg _))
        (by norm_num)
      linarith
    have hc1 : c₁ < p₂ := by
      by_contra h; push Not at h
      rw [mbProfit_of_lt x hlt] at hπ1
      have : (p₁ - c₁) * x p₁ < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (hxpos p₁ hle2)
      linarith
    refine ⟨hlt, hle2, hc1, fun p hp => ?_⟩
    have := h1 p
    rwa [mbProfit_of_lt x hp, mbProfit_of_lt x hlt] at this
  · rintro ⟨hlt, hle2, hc1, hmax⟩
    have hg1 : 0 ≤ (p₁ - c₁) * x p₁ := by
      have := hmax c₁ hc1; simpa using this
    -- continuity gives `g₁(p₂) ≤ g₁(p₁)`
    have hcont : Continuous fun p => (p - c₁) * x p :=
      (continuous_id.sub continuous_const).mul hx.cont
    have hp2 : (p₂ - c₁) * x p₂ ≤ (p₁ - c₁) * x p₁ := by
      have ht : Tendsto (fun p => (p - c₁) * x p) (𝓝[<] p₂) (𝓝 ((p₂ - c₁) * x p₂)) :=
        hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun p hp => hmax p hp)
    refine ⟨fun p => ?_, fun p => ?_⟩
    · rw [mbProfit_of_lt x hlt]
      rcases lt_trichotomy p p₂ with h | h | h
      · rw [mbProfit_of_lt x h]; exact hmax p h
      · rw [h, mbProfit_self]
        rcases le_total 0 ((p₂ - c₁) * x p₂) with h' | h' <;> linarith
      · rw [mbProfit_of_gt x h]; exact hg1
    · rw [mbProfit_of_gt x hlt]
      rcases lt_trichotomy p p₁ with h | h | h
      · rw [mbProfit_of_lt x h]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
      · rw [h, mbProfit_self]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)) (by norm_num)
      · rw [mbProfit_of_gt x h]

/-- **Exercise 12.C.4(a), no equilibrium** (MWG, p. 430). If firm 1's monopoly price exceeds
`c₂`, in the sense that `g₁(p) = (p − c₁)x(p)` is strictly increasing on `[c₁, pᵐ]` for some
`pᵐ > c₂`, the Bertrand duopoly with `c₁ < c₂` has no pure-strategy Nash equilibrium. -/
theorem exercise_12_C_4a_none {x : ℝ → ℝ} {pbar c₁ c₂ pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hxc₂ : 0 < x c₂) (hpm : c₂ < pm)
    (hmono : StrictMonoOn (fun p => (p - c₁) * x p) (Icc c₁ pm)) (p₁ p₂ : ℝ) :
    ¬ IsNashEquilibrium (bcGame ℝ (mbProfit x c₁) (mbProfit x c₂)) ![p₁, p₂] := by
  rw [exercise_12_C_4a hx hc₁ h12 hxc₂]
  rintro ⟨hlt, hle2, hc1, hmax⟩
  have hxp : 0 < x p₁ := lt_of_lt_of_le hxc₂ (mb_x_anti hx hle2)
  have hp1c : c₁ ≤ p₁ := by
    by_contra h; push Not at h
    have h0 := hmax c₁ hc1
    simp only [sub_self, zero_mul] at h0
    have : (p₁ - c₁) * x p₁ < 0 := mul_neg_of_neg_of_pos (by linarith) hxp
    linarith
  set p := (p₁ + min p₂ pm) / 2 with hp
  have hm1 : p₁ < min p₂ pm := lt_min hlt (by linarith)
  have hpp2 : p < p₂ := by rw [hp]; linarith [min_le_left p₂ pm]
  have hppm : p ≤ pm := by rw [hp]; linarith [min_le_right p₂ pm]
  have := hmono ⟨hp1c, by linarith⟩ ⟨by rw [hp]; linarith, hppm⟩ (show p₁ < p by rw [hp]; linarith)
  linarith [hmax p hpp2]

/-- Linear demand `x(p) = max{0, a − p}`. -/
noncomputable def bcLinDemand (a p : ℝ) : ℝ := max 0 (a - p)

theorem bcLinDemand_isBertrand (a : ℝ) : IsBertrandDemand (bcLinDemand a) a where
  cont := continuous_const.max (continuous_const.sub continuous_id)
  nonneg _ := le_max_left _ _
  strictAnti p p' h h0 := by
    unfold bcLinDemand at h0 ⊢
    have : 0 < a - p' := by
      by_contra hle; push Not at hle; rw [max_eq_left hle] at h0; exact lt_irrefl _ h0
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    linarith
  zero p hp := by unfold bcLinDemand; exact max_eq_left (by linarith)

/-- **Exercise 12.C.4(a), instance** (MWG, p. 430). With `x(p) = max{0, 10 − p}`, `c₁ = 1`,
`c₂ = 2`, firm 1's monopoly price `11/2` exceeds `c₂` and there is no pure-strategy
equilibrium. -/
theorem exercise_12_C_4a_none_instance (p₁ p₂ : ℝ) :
    ¬ IsNashEquilibrium (bcGame ℝ (mbProfit (bcLinDemand 10) 1) (mbProfit (bcLinDemand 10) 2))
      ![p₁, p₂] := by
  refine exercise_12_C_4a_none (pm := 11 / 2) (bcLinDemand_isBertrand 10) (by norm_num)
    (by norm_num) (by norm_num [bcLinDemand]) (by norm_num) ?_ p₁ p₂
  intro p hp q hq hpq
  simp only [bcLinDemand]
  rw [max_eq_right (by linarith [hp.2]), max_eq_right (by linarith [hq.2])]
  nlinarith [hp.1, hq.2]

/-- **Exercise 12.C.4(a), a drastic cost advantage** (MWG, p. 430). With `x(p) = max{0, 10 − p}`,
`c₁ = 1`, `c₂ = 8`, firm 1's monopoly price `11/2` is below `c₂` and `(11/2, 9)` is an
equilibrium. -/
theorem exercise_12_C_4a_drastic_instance :
    IsNashEquilibrium (bcGame ℝ (mbProfit (bcLinDemand 10) 1) (mbProfit (bcLinDemand 10) 8))
      ![11 / 2, 9] := by
  rw [exercise_12_C_4a (bcLinDemand_isBertrand 10) (by norm_num) (by norm_num)
    (by norm_num [bcLinDemand])]
  refine ⟨by norm_num, by norm_num, by norm_num, fun p _ => ?_⟩
  simp only [bcLinDemand]
  rw [max_eq_right (by norm_num : (0 : ℝ) ≤ 10 - 11 / 2)]
  rcases le_total (10 - p) 0 with h | h
  · rw [max_eq_left h]; norm_num
  · rw [max_eq_right h]; nlinarith [sq_nonneg (p - 11 / 2)]

/-- Firm 1's profit when ties go to firm 1: it sells `x(p)` whenever `p ≤ q`. -/
noncomputable def bcTieProfit₁ (x : ℝ → ℝ) (c p q : ℝ) : ℝ :=
  (p - c) * (if p ≤ q then x p else 0)

/-- Firm 2's profit when ties go to firm 1: it sells `x(p)` only if `p < q`. -/
noncomputable def bcTieProfit₂ (x : ℝ → ℝ) (c p q : ℝ) : ℝ :=
  (p - c) * (if p < q then x p else 0)

/-- **Exercise 12.C.4(a), ties to the low-cost firm** (MWG, p. 430). If ties are resolved in
favour of firm 1 and firm 1's monopoly price exceeds `c₂` (`g₁` strictly increasing on
`[c₁, pᵐ]`, `pᵐ > c₂`), the pure-strategy Nash equilibria are exactly `p₁ = p₂ ∈ [c₁, c₂]`; in
particular `p₁ = p₂ = c₂` is one, and in every equilibrium firm 2's price is weakly dominated. -/
theorem exercise_12_C_4a_tieRule {x : ℝ → ℝ} {pbar c₁ c₂ pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hxc₂ : 0 < x c₂) (hpm : c₂ < pm)
    (hmono : StrictMonoOn (fun p => (p - c₁) * x p) (Icc c₁ pm)) :
    (∀ p₁ p₂, IsNashEquilibrium (bcGame ℝ (bcTieProfit₁ x c₁) (bcTieProfit₂ x c₂)) ![p₁, p₂] ↔
      p₁ = p₂ ∧ c₁ ≤ p₁ ∧ p₁ ≤ c₂) ∧
    IsNashEquilibrium (bcGame ℝ (bcTieProfit₁ x c₁) (bcTieProfit₂ x c₂)) ![c₂, c₂] ∧
    ∀ p₂, p₂ ≤ c₂ → WeaklyDominated (bcGame ℝ (bcTieProfit₁ x c₁) (bcTieProfit₂ x c₂)) 1 p₂ := by
  have _ := hc₁
  have hxc₁ : 0 < x c₁ := lt_of_lt_of_le hxc₂ (mb_x_anti hx h12.le)
  have hxpos : ∀ p, p ≤ c₂ → 0 < x p := fun p hp => lt_of_lt_of_le hxc₂ (mb_x_anti hx hp)
  have hhigh1 : ∀ q, bcTieProfit₁ x c₁ (|q| + 1) q = 0 := fun q => by
    unfold bcTieProfit₁; rw [ite_eq_right (by linarith [le_abs_self q])]; ring
  have hhigh2 : ∀ q, bcTieProfit₂ x c₂ (|q| + 1) q = 0 := fun q => by
    unfold bcTieProfit₂; rw [ite_eq_right (by linarith [le_abs_self q])]; ring
  have hchar : ∀ p₁ p₂,
      IsNashEquilibrium (bcGame ℝ (bcTieProfit₁ x c₁) (bcTieProfit₂ x c₂)) ![p₁, p₂] ↔
        p₁ = p₂ ∧ c₁ ≤ p₁ ∧ p₁ ≤ c₂ := by
    intro p₁ p₂
    rw [bcGame_nash_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hπ1 : 0 ≤ bcTieProfit₁ x c₁ p₁ p₂ := by have := h1 (|p₂| + 1); rwa [hhigh1] at this
      have hπ2 : 0 ≤ bcTieProfit₂ x c₂ p₂ p₁ := by have := h2 (|p₁| + 1); rwa [hhigh2] at this
      have hle : p₁ ≤ p₂ := by
        by_contra h; push Not at h
        have hπ1' : bcTieProfit₁ x c₁ p₁ p₂ = 0 := by
          unfold bcTieProfit₁; rw [ite_eq_right (not_le.2 h)]; ring
        -- firm 1 can earn a positive profit by tying at `p₂` or pricing at `c₂`
        have hpos : 0 < bcTieProfit₁ x c₁ (min p₂ c₂) p₂ := by
          unfold bcTieProfit₁
          rw [ite_eq_left (min_le_left _ _)]
          by_cases hp2 : c₁ < p₂
          · exact mul_pos (by
              rcases le_total p₂ c₂ with h' | h'
              · rw [min_eq_left h']; linarith
              · rw [min_eq_right h']; linarith) (hxpos _ (min_le_right _ _))
          · push Not at hp2
            exfalso
            unfold bcTieProfit₂ at hπ2
            rw [ite_eq_left h] at hπ2
            have : (p₂ - c₂) * x p₂ < 0 :=
              mul_neg_of_neg_of_pos (by linarith) (hxpos p₂ (by linarith))
            linarith
        linarith [h1 (min p₂ c₂)]
      have hπ2' : bcTieProfit₂ x c₂ p₂ p₁ = 0 := by
        unfold bcTieProfit₂; rw [ite_eq_right (not_lt.2 hle)]; ring
      have hle2 : p₁ ≤ c₂ := by
        by_contra h; push Not at h
        obtain ⟨p', hp'c, hp'm, hgain⟩ := bertrand_deviation hx hxc₂ h
        have := h2 p'
        rw [hπ2'] at this
        unfold bcTieProfit₂ at this
        rw [ite_eq_left hp'm] at this
        have : 0 ≤ (p₁ - c₂) * x p₁ / 2 := div_nonneg (mul_nonneg (by linarith) (hx.nonneg _))
          (by norm_num)
        linarith
      have hc1 : c₁ ≤ p₁ := by
        by_contra h; push Not at h
        unfold bcTieProfit₁ at hπ1
        rw [ite_eq_left hle] at hπ1
        have : (p₁ - c₁) * x p₁ < 0 := mul_neg_of_neg_of_pos (by linarith) (hxpos p₁ hle2)
        linarith
      refine ⟨?_, hc1, hle2⟩
      by_contra hne
      have hlt : p₁ < p₂ := lt_of_le_of_ne hle hne
      set p := (p₁ + min p₂ pm) / 2 with hp
      have hm1 : p₁ < min p₂ pm := lt_min hlt (by linarith)
      have hpp2 : p ≤ p₂ := by rw [hp]; linarith [min_le_left p₂ pm]
      have hppm : p ≤ pm := by rw [hp]; linarith [min_le_right p₂ pm]
      have hinc := hmono ⟨hc1, by linarith⟩ ⟨by rw [hp]; linarith, hppm⟩
        (show p₁ < p by rw [hp]; linarith)
      have := h1 p
      unfold bcTieProfit₁ at this
      rw [ite_eq_left hpp2, ite_eq_left hle] at this
      exact absurd this (not_le.2 hinc)
    · rintro ⟨rfl, hc1, hle2⟩
      refine ⟨fun p => ?_, fun p => ?_⟩
      · unfold bcTieProfit₁
        rw [ite_eq_left le_rfl]
        split_ifs with h
        · rcases lt_or_ge p c₁ with h' | h'
          · have : (p - c₁) * x p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
            have : 0 ≤ (p₁ - c₁) * x p₁ := mul_nonneg (by linarith) (hx.nonneg _)
            linarith
          · rcases eq_or_lt_of_le h with h'' | h''
            · rw [h'']
            · exact (hmono ⟨h', by linarith⟩ ⟨hc1, by linarith⟩ h'').le
        · rw [mul_zero]; exact mul_nonneg (by linarith) (hx.nonneg _)
      · unfold bcTieProfit₂
        rw [ite_eq_right (lt_irrefl _), mul_zero]
        split_ifs with h
        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
        · rw [mul_zero]
  refine ⟨hchar, (hchar c₂ c₂).2 ⟨rfl, h12.le, le_rfl⟩, fun p₂ hp₂ => ?_⟩
  -- a price `p' > c₂` with `x(p') > 0` weakly dominates
  obtain ⟨p', hp'c, -, hgain⟩ := bertrand_deviation hx hxc₂ (show c₂ < c₂ + 1 by linarith)
  have hg' : 0 < (p' - c₂) * x p' := by
    have : 0 ≤ (c₂ + 1 - c₂) * x (c₂ + 1) / 2 := div_nonneg (mul_nonneg (by linarith)
      (hx.nonneg _)) (by norm_num)
    linarith
  rw [bcGame_weaklyDominated_one]
  refine ⟨p', fun r => ?_, p' + 1, ?_⟩
  · unfold bcTieProfit₂
    have h1 : (p₂ - c₂) * (if p₂ < r then x p₂ else 0) ≤ 0 := by
      split_ifs
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
      · rw [mul_zero]
    have h2 : 0 ≤ (p' - c₂) * (if p' < r then x p' else 0) := by
      split_ifs
      · exact hg'.le
      · rw [mul_zero]
    linarith
  · unfold bcTieProfit₂
    rw [ite_eq_left (by linarith : p' < p' + 1)]
    have h1 : (p₂ - c₂) * (if p₂ < p' + 1 then x p₂ else 0) ≤ 0 := by
      split_ifs
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
      · rw [mul_zero]
    linarith

/-! ### Exercise 12.C.4(b): prices on a grid -/

/-- The duopoly with costs `c₁, c₂` and prices restricted to the grid `Δℤ` (MWG, Exercise
12.C.4(b), p. 431): firm `j` names `nⱼ ∈ ℤ`, i.e. the price `nⱼΔ`. -/
noncomputable def bcGridGame (x : ℝ → ℝ) (c₁ c₂ Δ : ℝ) : NormalForm (Fin 2) (fun _ => ℤ) :=
  bcGame ℤ (fun n m => mbProfit x c₁ (n * Δ) (m * Δ)) (fun n m => mbProfit x c₂ (n * Δ) (m * Δ))

theorem mbProfit_nonpos {x : ℝ → ℝ} (hx0 : ∀ p, 0 ≤ x p) {c p : ℝ} (h : p ≤ c) (q : ℝ) :
    mbProfit x c p q ≤ 0 := by
  rcases lt_trichotomy p q with h' | h' | h'
  · rw [mbProfit_of_lt x h']; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx0 p)
  · rw [h', mbProfit_self]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx0 q)) (by norm_num)
  · rw [mbProfit_of_gt x h']

theorem mbProfit_nonneg {x : ℝ → ℝ} (hx0 : ∀ p, 0 ≤ x p) {c p : ℝ} (h : c ≤ p) (q : ℝ) :
    0 ≤ mbProfit x c p q := by
  rcases lt_trichotomy p q with h' | h' | h'
  · rw [mbProfit_of_lt x h']; exact mul_nonneg (by linarith) (hx0 p)
  · rw [h', mbProfit_self]
    exact div_nonneg (mul_nonneg (by linarith) (hx0 q)) (by norm_num)
  · rw [mbProfit_of_gt x h']

/-- **Exercise 12.C.4(b)** (MWG, p. 431). Prices on the grid `Δℤ`, `c₁ < c₂`. Suppose
`x(p̂₂) > 0` at the smallest grid price `p̂₂` above `c₂`, firm 1's profit
`g₁(p) = (p − c₁)x(p)` is strictly increasing on `[c₁, p̂₂]`, and the grid is fine enough that
`g₁(p) < 2g₁(p − Δ)` whenever `p ≥ c₂` and `x(p) > 0`. Then `(n₁Δ, n₂Δ)` is a pure-strategy Nash
equilibrium iff `n₂ = n₁ + 1`, `c₁ ≤ n₁Δ ≤ c₂` and `g₁((n₁ + 1)Δ) ≤ 2g₁(n₁Δ)`: firm 1 sells
at a grid price between `c₁` and `c₂`, firm 2 names the next grid price. -/
theorem exercise_12_C_4b {x : ℝ → ℝ} {pbar c₁ c₂ Δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hxc₂ : 0 < x c₂) (hΔ : 0 < Δ)
    (hxN : 0 < x (gridPrice Δ c₂))
    (hmono : StrictMonoOn (fun p => (p - c₁) * x p) (Icc c₁ (gridPrice Δ c₂)))
    (hhalf : ∀ p, c₂ ≤ p → 0 < x p → (p - c₁) * x p < 2 * ((p - Δ - c₁) * x (p - Δ)))
    (n₁ n₂ : ℤ) :
    IsNashEquilibrium (bcGridGame x c₁ c₂ Δ) ![n₁, n₂] ↔
      n₂ = n₁ + 1 ∧ c₁ ≤ n₁ * Δ ∧ n₁ * Δ ≤ c₂ ∧
        (((n₁ : ℝ) + 1) * Δ - c₁) * x (((n₁ : ℝ) + 1) * Δ) ≤ 2 * ((n₁ * Δ - c₁) * x (n₁ * Δ)) := by
  have _ := hc₁
  set N := ⌊c₂ / Δ⌋ with hNdef
  obtain ⟨hgp1, -, hgp3⟩ := gridPrice_spec (c := c₂) hΔ
  have hN2 : ((N : ℝ) + 1) * Δ = gridPrice Δ c₂ := by rw [gridPrice]
  have hfl1 : ∀ n : ℤ, (n : ℝ) * Δ ≤ c₂ → n ≤ N := fun n h =>
    Int.le_floor.2 ((le_div_iff₀ hΔ).2 h)
  have hfl2 : ∀ n : ℤ, c₂ < n * Δ → N + 1 ≤ n := fun n h => by
    have : N < n := Int.floor_lt.2 ((div_lt_iff₀ hΔ).2 h)
    omega
  have hcl : ∀ n m : ℤ, n < m → (n : ℝ) * Δ < m * Δ := fun n m h =>
    mul_lt_mul_of_pos_right (Int.cast_lt.2 h) hΔ
  have hcle : ∀ n m : ℤ, n ≤ m → (n : ℝ) * Δ ≤ m * Δ := fun n m h =>
    mul_le_mul_of_nonneg_right (Int.cast_le.2 h) hΔ.le
  have hxpos : ∀ p, p ≤ c₂ → 0 < x p := fun p hp => lt_of_lt_of_le hxc₂ (mb_x_anti hx hp)
  have hgN : 0 < (gridPrice Δ c₂ - c₁) * x (gridPrice Δ c₂) := mul_pos (by linarith) hxN
  have hNc : ((N + 1 : ℤ) : ℝ) * Δ = gridPrice Δ c₂ := by push_cast; exact hN2
  have hsub1 : ∀ n : ℤ, ((n - 1 : ℤ) : ℝ) * Δ = n * Δ - Δ := fun n => by push_cast; ring
  have hadd1 : ∀ n : ℤ, ((n + 1 : ℤ) : ℝ) * Δ = ((n : ℝ) + 1) * Δ := fun n => by push_cast; ring
  unfold bcGridGame
  rw [bcGame_nash_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hπ1 : 0 ≤ mbProfit x c₁ (n₁ * Δ) (n₂ * Δ) := by
      have := h1 (n₂ + 1); rwa [mbProfit_of_gt x (hcl _ _ (by omega))] at this
    have hπ2 : 0 ≤ mbProfit x c₂ (n₂ * Δ) (n₁ * Δ) := by
      have := h2 (n₁ + 1); rwa [mbProfit_of_gt x (hcl _ _ (by omega))] at this
    -- if `n` sells nothing at a price above `c₂`, firm 1 profits by naming `N + 1 < n`
    have hzero : x (n₂ * Δ) = 0 → mbProfit x c₁ (n₁ * Δ) (n₂ * Δ) ≤ 0 → False := by
      intro hx0 hle
      have hgt : c₂ < n₂ * Δ := by
        by_contra h; push Not at h; exact (hxpos _ h).ne' hx0
      have hN1 := hfl2 n₂ hgt
      rcases eq_or_lt_of_le hN1 with h | h
      · rw [← h, hNc] at hx0; linarith
      · have := h1 (N + 1)
        rw [mbProfit_of_lt x (hcl _ _ h), hNc] at this
        linarith
    rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
    · have hπ2' : mbProfit x c₂ (n₂ * Δ) (n₁ * Δ) = 0 := mbProfit_of_gt x (hcl _ _ hlt)
      have hπ1' : mbProfit x c₁ (n₁ * Δ) (n₂ * Δ) = (n₁ * Δ - c₁) * x (n₁ * Δ) :=
        mbProfit_of_lt x (hcl _ _ hlt)
      by_cases hx1 : x (n₁ * Δ) = 0
      · exfalso
        have hgt : c₂ < n₁ * Δ := by
          by_contra h; push Not at h; exact (hxpos _ h).ne' hx1
        have := hfl2 n₁ hgt
        have h3 := h1 (N + 1)
        rw [mbProfit_of_lt x (by rw [hNc, ← hNc]; exact hcl _ _ (by omega)), hNc, hπ1', hx1,
          mul_zero] at h3
        linarith
      have hx1' : 0 < x (n₁ * Δ) := lt_of_le_of_ne (hx.nonneg _) (Ne.symm hx1)
      have hle2 : n₁ * Δ ≤ c₂ := by
        have := h2 n₁
        rw [mbProfit_self, hπ2'] at this
        by_contra h; push Not at h
        have : 0 < (n₁ * Δ - c₂) * x (n₁ * Δ) := mul_pos (by linarith) hx1'
        linarith
      have hc1 : c₁ ≤ n₁ * Δ := by
        by_contra h; push Not at h
        rw [hπ1'] at hπ1
        have : (n₁ * Δ - c₁) * x (n₁ * Δ) < 0 := mul_neg_of_neg_of_pos (by linarith) hx1'
        linarith
      have hn1N := hfl1 n₁ hle2
      have hstep : n₂ = n₁ + 1 := by
        by_contra hne
        have hlt2 : n₁ + 1 < n₂ := by omega
        have := h1 (n₁ + 1)
        rw [mbProfit_of_lt x (hcl _ _ hlt2), hπ1'] at this
        have hup : ((n₁ + 1 : ℤ) : ℝ) * Δ ≤ gridPrice Δ c₂ := by
          rw [← hNc]; exact hcle _ _ (by omega)
        have hinc := hmono ⟨hc1, by linarith⟩ ⟨by linarith [hcl n₁ (n₁ + 1) (by omega)], hup⟩
          (hcl n₁ (n₁ + 1) (by omega))
        exact absurd this (not_le.2 hinc)
      refine ⟨hstep, hc1, hle2, ?_⟩
      have := h1 n₂
      rw [mbProfit_self, hπ1', hstep, hadd1] at this
      linarith
    · exfalso
      subst heq
      rw [mbProfit_self] at hπ1 hπ2
      by_cases hx1 : x (n₁ * Δ) = 0
      · exact hzero hx1 (by rw [mbProfit_self, hx1]; simp)
      have hx1' : 0 < x (n₁ * Δ) := lt_of_le_of_ne (hx.nonneg _) (Ne.symm hx1)
      have hge : c₂ ≤ n₁ * Δ := by
        by_contra h; push Not at h
        have : (n₁ * Δ - c₂) * x (n₁ * Δ) < 0 := mul_neg_of_neg_of_pos (by linarith) hx1'
        linarith
      have hh := hhalf _ hge hx1'
      have := h1 (n₁ - 1)
      rw [mbProfit_of_lt x (hcl _ _ (by omega)), mbProfit_self, hsub1] at this
      linarith
    · exfalso
      have hπ1' : mbProfit x c₁ (n₁ * Δ) (n₂ * Δ) = 0 := mbProfit_of_gt x (hcl _ _ hgt)
      rw [mbProfit_of_lt x (hcl _ _ hgt)] at hπ2
      by_cases hx2 : x (n₂ * Δ) = 0
      · exact hzero hx2 hπ1'.le
      have hx2' : 0 < x (n₂ * Δ) := lt_of_le_of_ne (hx.nonneg _) (Ne.symm hx2)
      have hge : c₂ ≤ n₂ * Δ := by
        by_contra h; push Not at h
        have : (n₂ * Δ - c₂) * x (n₂ * Δ) < 0 := mul_neg_of_neg_of_pos (by linarith) hx2'
        linarith
      have := h1 n₂
      rw [mbProfit_self, hπ1'] at this
      have : 0 < (n₂ * Δ - c₁) * x (n₂ * Δ) := mul_pos (by linarith) hx2'
      linarith
  · rintro ⟨hstep, hc1, hle2, hhalf1⟩
    subst hstep
    have hn1N := hfl1 n₁ hle2
    have hg1 : 0 ≤ (n₁ * Δ - c₁) * x (n₁ * Δ) := mul_nonneg (by linarith) (hx.nonneg _)
    have hπ1' : mbProfit x c₁ (n₁ * Δ) (((n₁ + 1 : ℤ) : ℝ) * Δ) =
        (n₁ * Δ - c₁) * x (n₁ * Δ) := mbProfit_of_lt x (hcl _ _ (by omega))
    refine ⟨fun s => ?_, fun s => ?_⟩
    · rw [hπ1']
      rcases lt_trichotomy s (n₁ + 1) with h | h | h
      · rw [mbProfit_of_lt x (hcl _ _ h)]
        have hs : s ≤ n₁ := by omega
        rcases lt_or_ge ((s : ℝ) * Δ) c₁ with h' | h'
        · have : ((s : ℝ) * Δ - c₁) * x (s * Δ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
          linarith
        · rcases eq_or_lt_of_le hs with h'' | h''
          · rw [h'']
          · have hup : (n₁ : ℝ) * Δ ≤ gridPrice Δ c₂ := by linarith
            exact (hmono ⟨h', by linarith [hcl _ _ h'']⟩ ⟨hc1, hup⟩ (hcl _ _ h'')).le
      · rw [h, mbProfit_self, hadd1]; linarith
      · rw [mbProfit_of_gt x (hcl _ _ h)]; exact hg1
    · rw [mbProfit_of_gt x (hcl _ _ (by omega : n₁ < n₁ + 1))]
      rcases le_or_gt s n₁ with h | h
      · exact mbProfit_nonpos hx.nonneg (le_trans (hcle _ _ h) hle2) _
      · rw [mbProfit_of_gt x (hcl _ _ h)]

/-- **Exercise 12.C.4(b), the equilibrium in undominated strategies** (MWG, p. 431). Under the
hypotheses of `exercise_12_C_4b` and `c₁ < p̂₂ − Δ`, firm 1 naming the largest grid price
`p̂₂ − Δ ≤ c₂` and firm 2 naming `p̂₂`, the smallest grid price above `c₂`, is a Nash
equilibrium. -/
theorem exercise_12_C_4b_eqm {x : ℝ → ℝ} {pbar c₁ c₂ Δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hxc₂ : 0 < x c₂) (hΔ : 0 < Δ)
    (hxN : 0 < x (gridPrice Δ c₂)) (hgap : c₁ < gridPrice Δ c₂ - Δ)
    (hmono : StrictMonoOn (fun p => (p - c₁) * x p) (Icc c₁ (gridPrice Δ c₂)))
    (hhalf : ∀ p, c₂ ≤ p → 0 < x p → (p - c₁) * x p < 2 * ((p - Δ - c₁) * x (p - Δ))) :
    IsNashEquilibrium (bcGridGame x c₁ c₂ Δ) ![⌊c₂ / Δ⌋, ⌊c₂ / Δ⌋ + 1] := by
  obtain ⟨hgp1, -, hgp3⟩ := gridPrice_spec (c := c₂) hΔ
  have hN2 : ((⌊c₂ / Δ⌋ : ℝ) + 1) * Δ = gridPrice Δ c₂ := by rw [gridPrice]
  have hN1 : (⌊c₂ / Δ⌋ : ℝ) * Δ = gridPrice Δ c₂ - Δ := by rw [← hN2]; ring
  rw [exercise_12_C_4b hx hc₁ h12 hxc₂ hΔ hxN hmono hhalf, hN2, hN1]
  refine ⟨rfl, hgap.le, hgp3, ?_⟩
  have := hhalf _ hgp1.le hxN
  linarith

/-- **Exercise 12.C.4(b), weakly dominated strategies** (MWG, p. 431). Any grid price `nΔ ≤ c₂`
is weakly dominated for firm 2 (by `p̂₂`, the smallest grid price above `c₂`, when
`x(p̂₂) > 0`). Hence in every equilibrium of `exercise_12_C_4b` other than `(p̂₂ − Δ, p̂₂)`,
firm 2 plays a weakly dominated strategy. -/
theorem exercise_12_C_4b_dominated {x : ℝ → ℝ} {pbar c₁ c₂ Δ : ℝ}
    (hx : IsBertrandDemand x pbar) (hc₁ : 0 < c₁) (h12 : c₁ < c₂) (hxc₂ : 0 < x c₂)
    (hΔ : 0 < Δ) (hxN : 0 < x (gridPrice Δ c₂))
    (hmono : StrictMonoOn (fun p => (p - c₁) * x p) (Icc c₁ (gridPrice Δ c₂)))
    (hhalf : ∀ p, c₂ ≤ p → 0 < x p → (p - c₁) * x p < 2 * ((p - Δ - c₁) * x (p - Δ))) :
    (∀ n : ℤ, (n : ℝ) * Δ ≤ c₂ → WeaklyDominated (bcGridGame x c₁ c₂ Δ) 1 n) ∧
    ∀ n₁ n₂ : ℤ, IsNashEquilibrium (bcGridGame x c₁ c₂ Δ) ![n₁, n₂] → n₁ ≠ ⌊c₂ / Δ⌋ →
      WeaklyDominated (bcGridGame x c₁ c₂ Δ) 1 n₂ := by
  obtain ⟨hgp1, -, -⟩ := gridPrice_spec (c := c₂) hΔ
  have hN2 : (((⌊c₂ / Δ⌋ + 1 : ℤ) : ℝ)) * Δ = gridPrice Δ c₂ := by push_cast; rw [gridPrice]
  have hdom : ∀ n : ℤ, (n : ℝ) * Δ ≤ c₂ → WeaklyDominated (bcGridGame x c₁ c₂ Δ) 1 n := by
    intro n hn
    unfold bcGridGame
    rw [bcGame_weaklyDominated_one]
    refine ⟨⌊c₂ / Δ⌋ + 1, fun r => ?_, ⌊c₂ / Δ⌋ + 2, ?_⟩
    · exact (mbProfit_nonpos hx.nonneg hn _).trans
        (mbProfit_nonneg hx.nonneg (by rw [hN2]; exact hgp1.le) _)
    · have hlt : (((⌊c₂ / Δ⌋ + 1 : ℤ) : ℝ)) * Δ < (((⌊c₂ / Δ⌋ + 2 : ℤ) : ℝ)) * Δ :=
        mul_lt_mul_of_pos_right (Int.cast_lt.2 (by omega)) hΔ
      rw [mbProfit_of_lt x hlt, hN2]
      have : 0 < (gridPrice Δ c₂ - c₂) * x (gridPrice Δ c₂) := mul_pos (by linarith) hxN
      linarith [mbProfit_nonpos hx.nonneg hn ((((⌊c₂ / Δ⌋ + 2 : ℤ) : ℝ)) * Δ)]
  refine ⟨hdom, fun n₁ n₂ hne hn₁ => hdom n₂ ?_⟩
  obtain ⟨hstep, -, hle, -⟩ := (exercise_12_C_4b hx hc₁ h12 hxc₂ hΔ hxN hmono hhalf n₁ n₂).1 hne
  have hn1N : n₁ ≤ ⌊c₂ / Δ⌋ := Int.le_floor.2 ((le_div_iff₀ hΔ).2 hle)
  have hlt : n₂ ≤ ⌊c₂ / Δ⌋ := by omega
  have := Int.floor_le (c₂ / Δ)
  rw [le_div_iff₀ hΔ] at this
  exact le_trans (mul_le_mul_of_nonneg_right (Int.cast_le.2 hlt) hΔ.le) this

/-- **Exercise 12.C.4(b), the undominated equilibrium** (MWG, p. 431). In the equilibrium
`(p̂₂ − Δ, p̂₂)` of `exercise_12_C_4b_eqm` neither firm plays a weakly dominated strategy. -/
theorem exercise_12_C_4b_undominated {x : ℝ → ℝ} {pbar c₁ c₂ Δ : ℝ}
    (hx : IsBertrandDemand x pbar) (hΔ : 0 < Δ)
    (hxN : 0 < x (gridPrice Δ c₂)) (hgap : c₁ < gridPrice Δ c₂ - Δ)
    (hmono : StrictMonoOn (fun p => (p - c₁) * x p) (Icc c₁ (gridPrice Δ c₂)))
    (hhalf : ∀ p, c₂ ≤ p → 0 < x p → (p - c₁) * x p < 2 * ((p - Δ - c₁) * x (p - Δ))) :
    ¬ WeaklyDominated (bcGridGame x c₁ c₂ Δ) 0 ⌊c₂ / Δ⌋ ∧
    ¬ WeaklyDominated (bcGridGame x c₁ c₂ Δ) 1 (⌊c₂ / Δ⌋ + 1) := by
  obtain ⟨hgp1, -, hgp3⟩ := gridPrice_spec (c := c₂) hΔ
  set N := ⌊c₂ / Δ⌋ with hNdef
  have hN2 : (((N + 1 : ℤ) : ℝ)) * Δ = gridPrice Δ c₂ := by push_cast; rw [gridPrice]
  have hN1 : (N : ℝ) * Δ = gridPrice Δ c₂ - Δ := by
    have : ((N : ℝ) + 1) * Δ = gridPrice Δ c₂ := by rw [gridPrice]
    rw [← this]; ring
  have hcl : ∀ n m : ℤ, n < m → (n : ℝ) * Δ < m * Δ := fun n m h =>
    mul_lt_mul_of_pos_right (Int.cast_lt.2 h) hΔ
  have hxN1 : 0 < x (N * Δ) := lt_of_lt_of_le hxN (mb_x_anti hx (by rw [hN1]; linarith))
  have hg1 : 0 < (N * Δ - c₁) * x (N * Δ) := mul_pos (by rw [hN1]; linarith) hxN1
  constructor
  · unfold bcGridGame
    rw [bcGame_weaklyDominated_zero]
    rintro ⟨s', hall, r, hr⟩
    have hs' : s' ≠ N := by rintro rfl; exact lt_irrefl _ hr
    have hle := hall (N + 1)
    rw [mbProfit_of_lt x (hcl _ _ (by omega))] at hle
    rcases lt_trichotomy s' (N + 1) with h | h | h
    · rw [mbProfit_of_lt x (hcl _ _ h)] at hle
      have h' : s' < N := by omega
      rcases lt_or_ge ((s' : ℝ) * Δ) c₁ with h'' | h''
      · have : ((s' : ℝ) * Δ - c₁) * x (s' * Δ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
        linarith
      · have := hmono ⟨h'', by linarith [hcl _ _ h']⟩ ⟨by rw [hN1]; linarith, by
          rw [hN1]; linarith⟩ (hcl _ _ h')
        linarith
    · rw [h, mbProfit_self, hN2] at hle
      have := hhalf _ hgp1.le hxN
      rw [← hN1] at this
      linarith
    · rw [mbProfit_of_gt x (hcl _ _ h)] at hle
      linarith
  · unfold bcGridGame
    rw [bcGame_weaklyDominated_one]
    rintro ⟨s', hall, r, hr⟩
    have hs' : s' ≠ N + 1 := by rintro rfl; exact lt_irrefl _ hr
    obtain ⟨-, h3a⟩ := exercise_12_C_3a (c := c₂) hx hΔ
    obtain ⟨r', hr'⟩ := h3a hxN s' hs'
    have e : ∀ n : ℤ, (fun k : Fin 2 => (((if k = 0 then n else r' : ℤ)) : ℝ) * Δ) =
        ![(n : ℝ) * Δ, (r' : ℝ) * Δ] := fun n => by
      funext k; fin_cases k <;> simp
    rw [e, e, mbProfit_fst, mbProfit_fst] at hr'
    exact absurd (hall r') (not_le.2 hr')

/-- **Exercise 12.C.4(b), the limit** (MWG, p. 431). As the grid becomes finer, the prices
`p̂₂ − Δ` and `p̂₂` of the undominated equilibrium both converge to `c₂`. -/
theorem exercise_12_C_4b_limit (c₂ : ℝ) :
    Tendsto (fun Δ => gridPrice Δ c₂ - Δ) (𝓝[>] 0) (𝓝 c₂) ∧
    Tendsto (fun Δ => gridPrice Δ c₂) (𝓝[>] 0) (𝓝 c₂) := by
  have h := exercise_12_C_3b c₂
  refine ⟨?_, h⟩
  have hid : Tendsto (fun Δ : ℝ => Δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  simpa using h.sub hid

/-- **Exercise 12.C.4(b), instance** (MWG, p. 431). For `x(p) = max{0, 10 − p}`, `c₁ = 1`,
`c₂ = 2` and `Δ = 1/2` the hypotheses of `exercise_12_C_4b_eqm` hold, and `(2, 5/2)` (grid
indices `(4, 5)`) is the equilibrium in undominated strategies. -/
theorem exercise_12_C_4b_instance :
    IsNashEquilibrium (bcGridGame (bcLinDemand 10) 1 2 (1 / 2)) ![4, 5] := by
  have hfl : ⌊(2 : ℝ) / (1 / 2)⌋ = 4 := by
    rw [Int.floor_eq_iff]; norm_num
  have hgp : gridPrice (1 / 2) 2 = 5 / 2 := by rw [gridPrice, hfl]; norm_num
  have h := exercise_12_C_4b_eqm (x := bcLinDemand 10) (c₁ := 1) (c₂ := 2) (Δ := 1 / 2)
    (bcLinDemand_isBertrand 10) (by norm_num) (by norm_num) (by norm_num [bcLinDemand])
    (by norm_num) (by rw [hgp]; norm_num [bcLinDemand]) (by rw [hgp]; norm_num) ?_ ?_
  · rw [hfl] at h; exact h
  · rw [hgp]
    intro p hp q hq hpq
    simp only [bcLinDemand]
    rw [max_eq_right (by linarith [hp.2]), max_eq_right (by linarith [hq.2])]
    nlinarith [hp.1, hq.2]
  · intro p hp hxp
    simp only [bcLinDemand] at hxp ⊢
    have hp10 : p < 10 := by
      by_contra h; push Not at h; rw [max_eq_left (by linarith)] at hxp; exact lt_irrefl _ hxp
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    nlinarith

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bidding for a limited number of units

MWG, Exercise 12.C.5, p. 431.

There are `I` buyers `0, …, I − 1` (buyer `i` is MWG's buyer `i + 1`), each wanting one unit;
buyer `i` values it at `vᵢ`, with `v₀ > v₁ > ⋯` (`StrictAnti v`). There are `q < I` units.
Buyers submit bids `bᵢ`; the units go to the `q` highest bidders, who pay their bids. Ties are
broken in favour of the buyer with the smaller index (the higher valuation): this is the reading
under which, as MWG states, the profile with every bid equal to `v_{q+1}` assigns the units to
buyers `1, …, q`. Buyer `i` wins iff fewer than `q` buyers rank above it (`ubAbove`), where `k`
ranks above `i` if `bₖ > bᵢ`, or `bₖ = bᵢ` and `k < i`.

* `exercise_12_C_5a`: every buyer bidding `v_{q+1}` (index `q`), with the units going to buyers
  `1, …, q`, is a Nash equilibrium.
* `exercise_12_C_5_competitive`: at the price `v_{q+1}` exactly `q` buyers strictly want a unit,
  buyer `q + 1` is indifferent and the others do not want one: a competitive equilibrium price.
* `exercise_12_C_5b`: in any pure-strategy Nash equilibrium, buyers `1, …, q` receive a unit and
  buyers `q + 1, …, I` do not. The proof: a losing buyer could outbid any winner `i` by `ε`, so
  its value is at most `bᵢ ≤ vᵢ`; and exactly `q` buyers win (`ub_card_winners`).
-/

namespace MWG.MarketPower

open Finset Function

variable {I : ℕ}

/-- The buyers ranked above buyer `i` at the bid profile `b`. -/
noncomputable def ubAbove (b : Fin I → ℝ) (i : Fin I) : Finset (Fin I) :=
  univ.filter fun k => b i < b k ∨ (b k = b i ∧ k < i)

/-- Buyer `i`'s payoff: `vᵢ − bᵢ` if it is among the `q` highest-ranked bidders, else `0`. -/
noncomputable def ubPayoff (v : Fin I → ℝ) (q : ℕ) (b : Fin I → ℝ) (i : Fin I) : ℝ :=
  if (ubAbove b i).card < q then v i - b i else 0

/-- A pure-strategy Nash equilibrium of the bidding game. -/
def IsUBNash (v : Fin I → ℝ) (q : ℕ) (b : Fin I → ℝ) : Prop :=
  ∀ i y, ubPayoff v q (update b i y) i ≤ ubPayoff v q b i

theorem ubAbove_irrefl (b : Fin I → ℝ) (i : Fin I) : i ∉ ubAbove b i := by
  simp [ubAbove]

theorem ubAbove_total (b : Fin I → ℝ) {i k : Fin I} (h : k ≠ i) :
    k ∈ ubAbove b i ∨ i ∈ ubAbove b k := by
  simp only [ubAbove, mem_filter, mem_univ, true_and]
  rcases lt_trichotomy (b i) (b k) with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_or_gt_of_ne h with h2 | h2
    · exact Or.inl (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl h1)

theorem ubAbove_ssubset (b : Fin I → ℝ) {i k : Fin I} (h : k ∈ ubAbove b i) :
    ubAbove b k ⊂ ubAbove b i := by
  simp only [ubAbove, mem_filter, mem_univ, true_and] at h
  refine Finset.ssubset_iff_subset_ne.2 ⟨fun l hl => ?_, fun he => ?_⟩
  · simp only [ubAbove, mem_filter, mem_univ, true_and] at hl ⊢
    rcases h with h | ⟨h1, h2⟩ <;> rcases hl with hl | ⟨hl1, hl2⟩
    · exact Or.inl (h.trans hl)
    · exact Or.inl (hl1 ▸ h)
    · exact Or.inl (h1 ▸ hl)
    · exact Or.inr ⟨hl1.trans h1, hl2.trans h2⟩
  · have hk : k ∈ ubAbove b i := by simpa [ubAbove] using h
    rw [← he] at hk
    exact ubAbove_irrefl b k hk

theorem ubAbove_card_injective (b : Fin I → ℝ) : Injective fun i => (ubAbove b i).card := by
  intro i k hik
  have hik' : (ubAbove b i).card = (ubAbove b k).card := hik
  by_contra hne
  rcases ubAbove_total b hne with h | h
  · exact absurd hik' (Finset.card_lt_card (ubAbove_ssubset b h)).ne
  · exact absurd hik' (Finset.card_lt_card (ubAbove_ssubset b h)).ne'

theorem ubAbove_card_lt (b : Fin I → ℝ) (i : Fin I) : (ubAbove b i).card < I := by
  have : ubAbove b i ⊆ univ.erase i := fun k hk =>
    mem_erase.2 ⟨fun h => ubAbove_irrefl b i (h ▸ hk), mem_univ _⟩
  have h1 := Finset.card_le_card this
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h1
  have := i.2
  omega

/-- Exactly `min q I` buyers win; with `q ≤ I`, exactly `q`. -/
theorem ub_card_winners (b : Fin I → ℝ) {q : ℕ} (hq : q ≤ I) :
    (univ.filter fun i => (ubAbove b i).card < q).card = q := by
  set r : Fin I → ℕ := fun i => (ubAbove b i).card with hr
  have hinj : Injective r := ubAbove_card_injective b
  have himg : univ.image r = range I := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨i, -, rfl⟩ := mem_image.1 hm
      exact mem_range.2 (ubAbove_card_lt b i)
    · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin, card_range]
  have h1 : (univ.filter fun i => r i < q).card =
      ((univ.filter fun i => r i < q).image r).card :=
    (card_image_of_injective _ hinj).symm
  have h2 : (univ.filter fun i => r i < q).image r = (univ.image r).filter (· < q) := by
    rw [Finset.filter_image]
  change (univ.filter fun i => r i < q).card = q
  rw [h1, h2, himg]
  have : (range I).filter (· < q) = range q := by
    ext m; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-- Ranks at the constant bid profile: buyer `i` has exactly `i` buyers above it. -/
theorem ubAbove_const (w : ℝ) (i : Fin I) : (ubAbove (fun _ => w) i).card = i := by
  have : ubAbove (fun _ => w) i = Finset.Iio i := by
    ext k; simp [ubAbove]
  rw [this, Fin.card_Iio]

theorem ubAbove_update_lt {w y : ℝ} (h : y < w) (i : Fin I) :
    (ubAbove (update (fun _ => w) i y) i).card = I - 1 := by
  have : ubAbove (update (fun _ => w) i y) i = univ.erase i := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [ubAbove]
    · simp [ubAbove, hk, h]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem ubAbove_update_gt {w y : ℝ} (h : w < y) (i : Fin I) :
    ubAbove (update (fun _ => w) i y) i = ∅ := by
  ext k
  by_cases hk : k = i
  · subst hk; simp [ubAbove]
  · simp [ubAbove, hk, h.not_gt, h.ne]

/-- **Exercise 12.C.5, first part** (MWG, p. 431). With `v₀ > v₁ > ⋯` and `q < I`, every buyer
bidding `v_q` (MWG's `v_{q+1}`) is a Nash equilibrium, and in it the units go to the buyers
`i < q` (MWG's buyers `1, …, q`). -/
theorem exercise_12_C_5a {v : Fin I → ℝ} (hv : StrictAnti v) {q : ℕ} (hq : q < I) :
    IsUBNash v q (fun _ => v ⟨q, hq⟩) ∧
      ∀ i : Fin I, (ubAbove (fun _ => v ⟨q, hq⟩) i).card < q ↔ (i : ℕ) < q := by
  set w := v ⟨q, hq⟩ with hw
  refine ⟨fun i y => ?_, fun i => by rw [ubAbove_const]⟩
  have hpay : ubPayoff v q (fun _ => w) i = if (i : ℕ) < q then v i - w else 0 := by
    unfold ubPayoff; rw [ubAbove_const]
  rw [hpay]
  -- the equilibrium payoff is nonnegative, and at least `v i − w`
  have hge0 : 0 ≤ if (i : ℕ) < q then v i - w else 0 := by
    split_ifs with h
    · have : v ⟨q, hq⟩ < v i := hv (Fin.mk_lt_mk.2 h |>.trans_eq' rfl)
      linarith
    · exact le_rfl
  have hge : v i - w ≤ if (i : ℕ) < q then v i - w else 0 := by
    split_ifs with h
    · exact le_rfl
    · push Not at h
      have : v i ≤ v ⟨q, hq⟩ := hv.antitone (show (⟨q, hq⟩ : Fin I) ≤ i from h)
      linarith
  unfold ubPayoff
  rcases lt_trichotomy y w with h | h | h
  · rw [ubAbove_update_lt h, ite_eq_right (by omega)]
    exact hge0
  · subst h
    have : update (fun _ : Fin I => w) i w = fun _ => w := by
      funext k; by_cases hk : k = i <;> simp [hk]
    rw [this, ← hpay]
    rfl
  · rw [ubAbove_update_gt h, card_empty]
    by_cases h1 : 0 < q
    · rw [ite_eq_left h1, update_self]; linarith
    · rw [ite_eq_right h1]; exact hge0

/-- **Exercise 12.C.5, `v_{q+1}` is a competitive price** (MWG, p. 431). At the price `v_q`
(MWG's `v_{q+1}`) the buyers `i < q` strictly want a unit, the buyers `i > q` strictly do not,
and buyer `q` is indifferent; exactly `q` buyers strictly want a unit, which equals supply. -/
theorem exercise_12_C_5_competitive {v : Fin I → ℝ} (hv : StrictAnti v) {q : ℕ} (hq : q < I) :
    (∀ i : Fin I, (i : ℕ) < q → v ⟨q, hq⟩ < v i) ∧
    (∀ i : Fin I, q < (i : ℕ) → v i < v ⟨q, hq⟩) ∧
    (univ.filter fun i => v ⟨q, hq⟩ < v i).card = q := by
  refine ⟨fun i h => hv (Fin.mk_lt_mk.2 h |>.trans_eq' rfl), fun i h => hv
    (show (⟨q, hq⟩ : Fin I) < i from h), ?_⟩
  have : (univ.filter fun i => v ⟨q, hq⟩ < v i) = Finset.Iio ⟨q, hq⟩ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Finset.mem_Iio]
    exact hv.lt_iff_gt
  rw [this, Fin.card_Iio]

/-- A bid below every other bid loses. -/
theorem ub_lose_bid (b : Fin I → ℝ) (i : Fin I) {q : ℕ} (hq : q < I) :
    q ≤ (ubAbove (update b i (-(∑ k, |b k|) - 1)) i).card := by
  have hlow : ∀ k, -(∑ k, |b k|) - 1 < b k := by
    intro k
    have h1 : |b k| ≤ ∑ k, |b k| :=
      Finset.single_le_sum (f := fun k => |b k|) (fun k _ => abs_nonneg _) (mem_univ k)
    have h2 := neg_abs_le (b k)
    linarith
  have : ubAbove (update b i (-(∑ k, |b k|) - 1)) i = univ.erase i := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [ubAbove]
    · simp [ubAbove, hk, hlow k]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

/-- **Exercise 12.C.5, second part** (MWG, p. 431). In any pure-strategy Nash equilibrium of
the bidding game (`v₀ > v₁ > ⋯`, `q < I` units), buyers `i < q` (MWG's `1, …, q`) receive a unit
and buyers `i ≥ q` (MWG's `q + 1, …, I`) do not. -/
theorem exercise_12_C_5b {v : Fin I → ℝ} (hv : StrictAnti v) {q : ℕ} (hq : q < I)
    {b : Fin I → ℝ} (hb : IsUBNash v q b) (i : Fin I) :
    (ubAbove b i).card < q ↔ (i : ℕ) < q := by
  -- winners bid at most their value
  have hwin : ∀ i, (ubAbove b i).card < q → b i ≤ v i := by
    intro i hi
    have := hb i (-(∑ k, |b k|) - 1)
    unfold ubPayoff at this
    rw [ite_eq_right (not_lt.2 (ub_lose_bid b i hq)), ite_eq_left hi] at this
    linarith
  -- a loser's value is below every winner's value
  have hpair : ∀ i j, (ubAbove b i).card < q → ¬ (ubAbove b j).card < q → v j < v i := by
    intro i j hi hj
    have hle : v j ≤ b i := by
      by_contra hlt
      push Not at hlt
      set y := (b i + v j) / 2 with hy
      have hsub : ubAbove (update b j y) j ⊆ ubAbove b i := by
        intro k hk
        simp only [ubAbove, mem_filter, mem_univ, true_and] at hk ⊢
        by_cases hkj : k = j
        · subst hkj; simp at hk
        · simp only [update_self, update_of_ne hkj] at hk
          rcases hk with hk | ⟨hk, -⟩
          · left; linarith
          · left; linarith
      have hwins : (ubAbove (update b j y) j).card < q :=
        lt_of_le_of_lt (Finset.card_le_card hsub) hi
      have := hb j y
      unfold ubPayoff at this
      rw [ite_eq_left hwins, ite_eq_right hj, update_self] at this
      linarith
    have hne : j ≠ i := by rintro rfl; exact hj hi
    rcases lt_or_gt_of_ne (hv.injective.ne hne) with h | h
    · exact h
    · linarith [hwin i hi]
  have hW := ub_card_winners b hq.le
  constructor
  · intro hi
    by_contra hiq
    push Not at hiq
    -- every loser has a larger index than the winner `i`
    have hsub : (univ.filter fun j => ¬ (ubAbove b j).card < q) ⊆ Finset.Ioi i := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      exact Finset.mem_Ioi.2 (hv.lt_iff_gt.1 (hpair i j hi hj))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at h1
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin I))) (fun j => (ubAbove b j).card < q)
    rw [hW, card_univ, Fintype.card_fin] at h2
    omega
  · intro hi
    by_contra hlose
    -- every winner has a smaller index than the loser `i`
    have hsub : (univ.filter fun j => (ubAbove b j).card < q) ⊆ Finset.Iio i := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      exact Finset.mem_Iio.2 (hv.lt_iff_gt.1 (hpair j i hj hlose))
    have h1 := Finset.card_le_card hsub
    rw [hW, Fin.card_Iio] at h1
    omega

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Cournot competition with different costs

MWG, Exercises 12.C.9(a)-(b), 12.C.10, 12.C.19 and 12.C.20, pp. 431-433.

* `exercise_12_C_9a`: the linear duopoly `p(q) = a − bq` with unit costs `c₁ > c₂`, `a > c₁`:
  if `a + c₂ > 2c₁` the unique Nash equilibrium is `qⱼ = (a − 2cⱼ + cₖ)/(3b)`; if
  `a + c₂ ≤ 2c₁` it is `q₁ = 0`, `q₂ = (a − c₂)/(2b)`: only the low-cost firm 2 produces.
* `exercise_12_C_9b`: in the interior case, `dq₁/dc₁ = −2/(3b) < 0`, `dq₂/dc₁ = 1/(3b) > 0`; the
  profits are `πⱼ = bqⱼ²`, with `dπ₁/dc₁ < 0 < dπ₂/dc₁`.
* `exercise_12_C_10a`: `J` firms with costs `αⱼc̃(q)`, `c̃` strictly increasing, convex and
  differentiable, the `αⱼ` distinct: if two firms produce positive output in a Nash equilibrium,
  moving output between them lowers total cost, so `Q*` is not produced efficiently.
* `exercise_12_C_10b`: the correct measure of welfare loss is `S(Q°) − W(q*)`, where
  `S(Q) = ∫₀^Q p − C(Q)` uses the efficient (minimum) cost `C(Q)` of producing `Q` and `Q°`
  maximizes `S`; it splits into the loss from the output level, `S(Q°) − S(Q*)`, and the
  production inefficiency `∑ⱼ cⱼ(qⱼ*) − C(Q*)`, both nonnegative; the second is positive when
  two firms produce (`exercise_12_C_10b_strict`).
* `exercise_12_C_10c`: in the model of Exercise 12.C.9 (`c̃(q) = q`, `αⱼ = cⱼ`), welfare at the
  Cournot equilibrium has derivative `(11c₁ − 4a − 7c₂)/(9b)` in `c₁`; with `a = 10`, `b = 1`,
  `c₂ = 1`, lowering `c₁` from `5` to `9/2` lowers welfare from `268/9` to `2123/72`.
* `exercise_12_C_19a`, `exercise_12_C_19b`: Exercise 8.B.5, proved in Chapter 8.
* `exercise_12_C_20`: Proposition 12.C.2 with a convex differentiable cost `c(q)`: in a Cournot
  duopoly equilibrium the price exceeds each firm's marginal cost and is below the monopoly
  price.

Departures: costs and inverse demand are differentiable on all of `ℝ` (as in
`MWGMarketPower.CournotBestResponse`); in 12.C.10(b) costs are nonnegative on `[0, ∞)`.
-/

namespace MWG.MarketPower

open Set Function Filter Topology

/-! ### Exercise 12.C.9 -/

/-- The cost functions `cⱼq` of the two firms of Exercise 12.C.9. -/
noncomputable def ccLinCost (c₁ c₂ : ℝ) : Fin 2 → ℝ → ℝ := ![fun z => c₁ * z, fun z => c₂ * z]

theorem ccLin_profit0 (a b c₁ c₂ : ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) (update q 0 y) 0 =
      (a - b * (y + q 1)) * y - c₁ * y := by
  simp [cournotGenProfit, ccLinCost, Fin.sum_univ_two]

theorem ccLin_profit1 (a b c₁ c₂ : ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) (update q 1 y) 1 =
      (a - b * (y + q 0)) * y - c₂ * y := by
  simp [cournotGenProfit, ccLinCost, Fin.sum_univ_two, add_comm]

/-- A best response in the linear model, in Kuhn-Tucker form: `q ≥ 0`, `A − br ≤ 2bq`, with
equality if `q > 0` (where `A = a − c`, `r` the rival's output). -/
theorem cc_br_kkt {A b r : ℝ} (hb : 0 < b) :
    0 ≤ max 0 ((A - b * r) / (2 * b)) ∧ A - b * r ≤ 2 * b * max 0 ((A - b * r) / (2 * b)) ∧
      (0 < max 0 ((A - b * r) / (2 * b)) → 2 * b * max 0 ((A - b * r) / (2 * b)) = A - b * r) := by
  rcases le_total ((A - b * r) / (2 * b)) 0 with h | h
  · rw [max_eq_left h]
    refine ⟨le_rfl, ?_, fun h' => absurd h' (lt_irrefl 0)⟩
    rw [div_nonpos_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · linarith
  · rw [max_eq_right h]
    refine ⟨h, ?_, fun _ => ?_⟩
    · field_simp; exact le_rfl
    · field_simp

/-- The Nash equilibria of the linear duopoly with costs `c₁, c₂` are the mutual best responses
`qⱼ = max{0, (a − cⱼ − bqₖ)/(2b)}`. -/
theorem ccLin_ne_iff {a b c₁ c₂ : ℝ} (hb : 0 < b) (q : Fin 2 → ℝ) :
    IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q ↔
      0 ≤ q 1 ∧ 0 ≤ q 0 ∧ q 0 = max 0 ((a - c₁ - b * q 1) / (2 * b)) ∧
        q 1 = max 0 ((a - c₂ - b * q 0) / (2 * b)) := by
  constructor
  · rintro ⟨hnn, hbr⟩
    refine ⟨hnn 1, hnn 0, ?_, ?_⟩
    · obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₁) hb (hnn 1)
      by_contra hne
      have h1 := huniq (q 0) (hnn 0) hne
      have h2 := hbr 0 (max 0 ((a - c₁ - b * q 1) / (2 * b))) (le_max_left _ _)
      rw [ccLin_profit0] at h2
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 0 =
          (a - b * (q 0 + q 1)) * q 0 - c₁ * q 0 := by
        rw [← ccLin_profit0 a b c₁ c₂ q (q 0), update_eq_self]
      rw [h3] at h2
      linarith
    · obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₂) hb (hnn 0)
      by_contra hne
      have h1 := huniq (q 1) (hnn 1) hne
      have h2 := hbr 1 (max 0 ((a - c₂ - b * q 0) / (2 * b))) (le_max_left _ _)
      rw [ccLin_profit1] at h2
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 1 =
          (a - b * (q 1 + q 0)) * q 1 - c₂ * q 1 := by
        rw [← ccLin_profit1 a b c₁ c₂ q (q 1), update_eq_self]
      rw [h3] at h2
      linarith
  · rintro ⟨h1, h0, e0, e1⟩
    refine ⟨fun j => by fin_cases j <;> assumption, fun j y hy => ?_⟩
    fin_cases j
    · simp only [Fin.zero_eta]
      rw [ccLin_profit0]
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 0 =
          (a - b * (q 0 + q 1)) * q 0 - c₁ * q 0 := by
        rw [← ccLin_profit0 a b c₁ c₂ q (q 0), update_eq_self]
      rw [h3]
      obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₁) hb h1
      by_cases hy' : y = q 0
      · rw [hy']
      · rw [e0] at hy' ⊢
        exact (huniq y hy hy').le
    · simp only [Fin.mk_one]
      rw [ccLin_profit1]
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 1 =
          (a - b * (q 1 + q 0)) * q 1 - c₂ * q 1 := by
        rw [← ccLin_profit1 a b c₁ c₂ q (q 1), update_eq_self]
      rw [h3]
      obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₂) hb h0
      by_cases hy' : y = q 1
      · rw [hy']
      · rw [e1] at hy' ⊢
        exact (huniq y hy hy').le

/-- **Exercise 12.C.9(a)** (MWG, p. 431). The linear Cournot duopoly with `p(q) = a − bq`,
`b > 0`, and unit costs `c₁ > c₂` with `a > c₁`. If `a + c₂ > 2c₁` the unique Nash equilibrium is
`q₁ = (a − 2c₁ + c₂)/(3b)`, `q₂ = (a − 2c₂ + c₁)/(3b)` (both positive); if `a + c₂ ≤ 2c₁` the
unique Nash equilibrium is `q₁ = 0`, `q₂ = (a − c₂)/(2b)`: only the low-cost firm 2 produces,
at its monopoly output. -/
theorem exercise_12_C_9a {a b c₁ c₂ : ℝ} (hb : 0 < b) (h21 : c₂ < c₁) (hca : c₁ < a) :
    (2 * c₁ < a + c₂ → ∀ q, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q ↔
      q = ![(a - 2 * c₁ + c₂) / (3 * b), (a - 2 * c₂ + c₁) / (3 * b)]) ∧
    (a + c₂ ≤ 2 * c₁ → ∀ q, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q ↔
      q = ![0, (a - c₂) / (2 * b)]) := by
  -- the mutual best responses, in Kuhn-Tucker form
  have hsolve : ∀ q : Fin 2 → ℝ, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q →
      0 ≤ q 0 ∧ 0 ≤ q 1 ∧ a - c₁ - b * q 1 ≤ 2 * b * q 0 ∧
        (0 < q 0 → 2 * b * q 0 = a - c₁ - b * q 1) ∧ a - c₂ - b * q 0 ≤ 2 * b * q 1 ∧
        (0 < q 1 → 2 * b * q 1 = a - c₂ - b * q 0) := by
    intro q hq
    obtain ⟨h1, h0, e0, e1⟩ := (ccLin_ne_iff hb q).1 hq
    obtain ⟨-, k0, k0'⟩ := cc_br_kkt (A := a - c₁) (r := q 1) hb
    obtain ⟨-, k1, k1'⟩ := cc_br_kkt (A := a - c₂) (r := q 0) hb
    rw [← e0] at k0 k0'
    rw [← e1] at k1 k1'
    exact ⟨h0, h1, k0, k0', k1, k1'⟩
  -- firm 2 always produces
  have hq1pos : ∀ q : Fin 2 → ℝ, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q →
      0 < q 1 := by
    intro q hq
    obtain ⟨h0, h1, k0, k0', k1, -⟩ := hsolve q hq
    by_contra h
    have hz : q 1 = 0 := le_antisymm (not_lt.1 h) h1
    rw [hz] at k0 k1
    have hq0 : 0 < q 0 := by nlinarith
    have := k0' hq0
    rw [hz] at this
    nlinarith
  constructor
  · intro hint q
    constructor
    · intro hq
      obtain ⟨h0, h1, k0, k0', k1, k1'⟩ := hsolve q hq
      have hp1 := hq1pos q hq
      have e1 := k1' hp1
      have hp0 : 0 < q 0 := by
        by_contra h
        have hz : q 0 = 0 := le_antisymm (not_lt.1 h) h0
        rw [hz] at e1 k0
        nlinarith
      have e0 := k0' hp0
      funext j
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        field_simp; nlinarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp; nlinarith
    · rintro rfl
      rw [ccLin_ne_iff hb]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hq0 : 0 < (a - 2 * c₁ + c₂) / (3 * b) := div_pos (by linarith) (by positivity)
      have hq1 : 0 < (a - 2 * c₂ + c₁) / (3 * b) := div_pos (by linarith) (by positivity)
      refine ⟨hq1.le, hq0.le, ?_, ?_⟩
      · rw [max_eq_right (by field_simp; linarith)]; field_simp; ring
      · rw [max_eq_right (by field_simp; linarith)]; field_simp; ring
  · intro hcorner q
    constructor
    · intro hq
      obtain ⟨h0, h1, k0, k0', k1, k1'⟩ := hsolve q hq
      have hp1 := hq1pos q hq
      have e1 := k1' hp1
      have hz : q 0 = 0 := by
        by_contra h
        have hp0 : 0 < q 0 := lt_of_le_of_ne h0 (Ne.symm h)
        have e0 := k0' hp0
        nlinarith
      funext j
      fin_cases j
      · simpa using hz
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [hz] at e1
        field_simp; linarith
    · rintro rfl
      rw [ccLin_ne_iff hb]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hq1 : 0 < (a - c₂) / (2 * b) := div_pos (by linarith) (by positivity)
      refine ⟨hq1.le, le_rfl, ?_, ?_⟩
      · rw [max_eq_left]
        rw [div_nonpos_iff]
        right
        refine ⟨?_, by positivity⟩
        field_simp
        linarith
      · rw [max_eq_right (by simpa using hq1.le)]
        field_simp
        ring

/-- **Exercise 12.C.9(b)** (MWG, p. 431). In the equilibrium with both firms producing
(`a − 2c₁ + c₂ > 0`, `a − 2c₂ + c₁ > 0`), firm `j`'s profit is `bqⱼ²`; as `c₁` rises, firm 1's
output `(a − 2c₁ + c₂)/(3b)` and profit `(a − 2c₁ + c₂)²/(9b)` fall (derivatives `−2/(3b)` and
`−4(a − 2c₁ + c₂)/(9b)`), while firm 2's output `(a − 2c₂ + c₁)/(3b)` and profit
`(a − 2c₂ + c₁)²/(9b)` rise (derivatives `1/(3b)` and `2(a − 2c₂ + c₁)/(9b)`). -/
theorem exercise_12_C_9b {a b c₂ : ℝ} (hb : 0 < b) (c₁ : ℝ) (h1 : 0 < a - 2 * c₁ + c₂)
    (h2 : 0 < a - 2 * c₂ + c₁) :
    (a - b * ((a - 2 * c₁ + c₂) / (3 * b) + (a - 2 * c₂ + c₁) / (3 * b)) - c₁) *
        ((a - 2 * c₁ + c₂) / (3 * b)) = (a - 2 * c₁ + c₂) ^ 2 / (9 * b) ∧
    (a - b * ((a - 2 * c₁ + c₂) / (3 * b) + (a - 2 * c₂ + c₁) / (3 * b)) - c₂) *
        ((a - 2 * c₂ + c₁) / (3 * b)) = (a - 2 * c₂ + c₁) ^ 2 / (9 * b) ∧
    HasDerivAt (fun c => (a - 2 * c + c₂) / (3 * b)) (-2 / (3 * b)) c₁ ∧ -2 / (3 * b) < 0 ∧
    HasDerivAt (fun c => (a - 2 * c₂ + c) / (3 * b)) (1 / (3 * b)) c₁ ∧ 0 < 1 / (3 * b) ∧
    HasDerivAt (fun c => (a - 2 * c + c₂) ^ 2 / (9 * b))
      (-4 * (a - 2 * c₁ + c₂) / (9 * b)) c₁ ∧ -4 * (a - 2 * c₁ + c₂) / (9 * b) < 0 ∧
    HasDerivAt (fun c => (a - 2 * c₂ + c) ^ 2 / (9 * b))
      (2 * (a - 2 * c₂ + c₁) / (9 * b)) c₁ ∧ 0 < 2 * (a - 2 * c₂ + c₁) / (9 * b) := by
  have hl1 : HasDerivAt (fun c => a - 2 * c + c₂) (-2) c₁ := by
    have := (((hasDerivAt_id c₁).const_mul 2).const_sub a).add_const c₂
    simpa using this
  have hl2 : HasDerivAt (fun c => a - 2 * c₂ + c) 1 c₁ := by
    simpa using (hasDerivAt_id c₁).const_add (a - 2 * c₂)
  refine ⟨by field_simp; ring, by field_simp; ring, ?_, ?_, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · simpa using hl1.div_const (3 * b)
  · exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · simpa using hl2.div_const (3 * b)
  · convert (hl1.pow 2).div_const (9 * b) using 1; ring
  · exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  · convert (hl2.pow 2).div_const (9 * b) using 1; ring
  · positivity

/-! ### Exercise 12.C.19 -/

/-- **Exercise 12.C.19(a)** (MWG, p. 433): Exercise 8.B.5(a), proved in Chapter 8 as
`MWG.SimultaneousMoveGames.exercise_8_B_5a`. With two firms, iterated deletion of strictly
dominated strategies in the linear Cournot model leaves exactly `(a − c)/(3b)` in the limit. -/
theorem exercise_12_C_19a {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ i, ⋂ n, MWG.SimultaneousMoveGames.sdIter
        (MWG.SimultaneousMoveGames.cournot (Fin 2) a b c) n i =
      {MWG.SimultaneousMoveGames.cournotStar a b c hb hA}) ∧
    ∀ n i, (MWG.SimultaneousMoveGames.sdIter
      (MWG.SimultaneousMoveGames.cournot (Fin 2) a b c) n i).Nontrivial :=
  MWG.SimultaneousMoveGames.exercise_8_B_5a hb hA

/-- **Exercise 12.C.19(b)** (MWG, p. 433): Exercise 8.B.5(b), proved in Chapter 8 as
`MWG.SimultaneousMoveGames.exercise_8_B_5b`. With three firms the deletion process stops after
one round at the interval `[0, (a − c)/(2b)]`. -/
theorem exercise_12_C_19b {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ n i, MWG.SimultaneousMoveGames.sdIter
        (MWG.SimultaneousMoveGames.cournot (Fin 3) a b c) (n + 1) i =
      MWG.SimultaneousMoveGames.qIval 0 ((a - c) / (2 * b))) ∧
    MWG.SimultaneousMoveGames.SDTerminal (MWG.SimultaneousMoveGames.cournot (Fin 3) a b c)
      (fun _ => MWG.SimultaneousMoveGames.qIval 0 ((a - c) / (2 * b))) ∧
    ∀ i, (⋂ n, MWG.SimultaneousMoveGames.sdIter
      (MWG.SimultaneousMoveGames.cournot (Fin 3) a b c) n i).Nontrivial :=
  MWG.SimultaneousMoveGames.exercise_8_B_5b hb hA

/-! ### Exercise 12.C.10 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Moving output between two firms changes a separable sum only in two terms. -/
theorem cc_sum_update_two (F : ι → ℝ → ℝ) (q : ι → ℝ) {h l : ι} (hhl : h ≠ l) (a b : ℝ) :
    ∑ k, F k (update (update q h a) l b k) =
      ∑ k, F k (q k) - F h (q h) - F l (q l) + F h a + F l b := by
  have hl : l ∈ Finset.univ.erase h := Finset.mem_erase.2 ⟨hhl.symm, Finset.mem_univ l⟩
  have e1 := Finset.add_sum_erase Finset.univ (fun k => F k (update (update q h a) l b k))
    (Finset.mem_univ h)
  have e2 := Finset.add_sum_erase (Finset.univ.erase h)
    (fun k => F k (update (update q h a) l b k)) hl
  have e3 := Finset.add_sum_erase Finset.univ (fun k => F k (q k)) (Finset.mem_univ h)
  have e4 := Finset.add_sum_erase (Finset.univ.erase h) (fun k => F k (q k)) hl
  have e5 : ∑ k ∈ (Finset.univ.erase h).erase l, F k (update (update q h a) l b k) =
      ∑ k ∈ (Finset.univ.erase h).erase l, F k (q k) :=
    Finset.sum_congr rfl fun k hk => by
      obtain ⟨hkl, hk'⟩ := Finset.mem_erase.1 hk
      obtain ⟨hkh, -⟩ := Finset.mem_erase.1 hk'
      rw [update_of_ne hkl, update_of_ne hkh]
  simp only [update_self, update_of_ne hhl] at e1 e2
  linarith

/-- The first-order condition of a producing firm in a Cournot equilibrium with cost functions
`Cₖ`: `P'(Q)qₖ + P(Q) = Cₖ'(qₖ)`. -/
theorem cc_foc {P P' : ℝ → ℝ} {C C' : ι → ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hC : ∀ k y, HasDerivAt (C k) (C' k y) y) {q : ι → ℝ} (hq : IsCournotGenNE P C q) {k : ι}
    (hk : 0 < q k) : P' (∑ j, q j) * q k + P (∑ j, q j) = C' k (q k) := by
  set R := ∑ j, q j - q k with hR
  have hQ : q k + R = ∑ j, q j := by rw [hR]; ring
  set f : ℝ → ℝ := fun y => P (y + R) * y - C k y with hf
  have hfeq : ∀ y, cournotGenProfit P C (update q k y) k = f y := by
    intro y
    simp only [cournotGenProfit, update_self, sum_update_eq, hf]
    rfl
  have hd : HasDerivAt f (P' (q k + R) * 1 * q k + P (q k + R) * 1 - C' k (q k)) (q k) := by
    have h1 : HasDerivAt (fun y => y + R) 1 (q k) := (hasDerivAt_id _).add_const R
    have h2 := (hP (q k + R)).comp (q k) h1
    exact (h2.mul (hasDerivAt_id _)).sub (hC k (q k))
  have hmax : IsLocalMax f (q k) := by
    filter_upwards [Ioi_mem_nhds hk] with y hy
    rw [← hfeq, ← hfeq, update_eq_self]
    exact hq.2 k y (le_of_lt hy)
  have := hmax.hasDerivAt_eq_zero hd
  rw [hQ] at this
  linarith

omit [DecidableEq ι] in
/-- If two producing firms' marginal costs differ, moving a little output from the firm with
the higher marginal cost to the other lowers total cost. -/
theorem cc_move {ct ct' : ℝ → ℝ} {α : ι → ℝ} (hct : ∀ y, HasDerivAt ct (ct' y) y)
    {q : ι → ℝ} (hq : ∀ k, 0 ≤ q k) {h l : ι} (hhl : h ≠ l) (hh : 0 < q h)
    (hmc : α l * ct' (q l) < α h * ct' (q h)) :
    ∃ q' : ι → ℝ, (∀ k, 0 ≤ q' k) ∧ ∑ k, q' k = ∑ k, q k ∧
      ∑ k, α k * ct (q' k) < ∑ k, α k * ct (q k) := by
  classical
  set φ : ℝ → ℝ := fun t => α l * ct (q l + t) + α h * ct (q h - t) with hφ
  have hd : HasDerivAt φ (α l * ct' (q l) - α h * ct' (q h)) 0 := by
    have h1 : HasDerivAt (fun t => ct (q l + t)) (ct' (q l)) 0 := by
      have := (hct (q l + 0)).comp_const_add (q l) 0
      rwa [add_zero] at this
    have h2 : HasDerivAt (fun t => ct (q h - t)) (-ct' (q h)) 0 := by
      have := (hct (q h - 0)).comp_const_sub (q h) 0
      rwa [sub_zero] at this
    have := (h1.const_mul (α l)).add (h2.const_mul (α h))
    convert this using 1
    ring
  have hT := hd.tendsto_slope_zero_right
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (φ (0 + t) - φ 0) < 0 :=
    (tendsto_order.1 hT).2 0 (by linarith)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (q h) := Ioo_mem_nhdsGT hh
  obtain ⟨t, ht1, ht2, ht3⟩ := (hneg.and hsmall).exists
  have hφt : φ t < φ 0 := by
    rw [smul_eq_mul, zero_add] at ht1
    by_contra hge
    push Not at hge
    have := mul_nonneg (inv_pos.2 ht2).le (sub_nonneg.2 hge)
    linarith
  refine ⟨update (update q h (q h - t)) l (q l + t), fun k => ?_, ?_, ?_⟩
  · by_cases hkl : k = l
    · subst hkl; simp only [update_self]; linarith [hq k]
    · rw [update_of_ne hkl]
      by_cases hkh : k = h
      · subst hkh; simp only [update_self]; linarith
      · rw [update_of_ne hkh]; exact hq k
  · rw [cc_sum_update_two (fun _ y => y) q hhl]
    ring
  · rw [cc_sum_update_two (fun k y => α k * ct y) q hhl]
    simp only [hφ, add_zero, sub_zero] at hφt
    linarith

/-- **Exercise 12.C.10(a)** (MWG, pp. 431-432). `J`-firm Cournot model with costs
`cⱼ(q) = αⱼc̃(q)`, `c̃` strictly increasing and convex on `[0, ∞)` (and differentiable), the
`αⱼ` distinct (`α₁ > ⋯ > α_J`), inverse demand differentiable with `P' < 0`. If two firms make
positive sales in a Nash equilibrium, the aggregate output `Q*` is produced inefficiently: some
reallocation of `Q*` among the firms has strictly lower total cost. -/
theorem exercise_12_C_10a {P P' ct ct' : ℝ → ℝ} {α : ι → ℝ} (hα : Injective α)
    (hP : ∀ Q, HasDerivAt P (P' Q) Q) (hP' : ∀ Q, 0 ≤ Q → P' Q < 0)
    (hct : ∀ y, HasDerivAt ct (ct' y) y) (hmono : StrictMonoOn ct (Ici 0))
    (hconv : ConvexOn ℝ (Ici 0) ct) {q : ι → ℝ}
    (hq : IsCournotGenNE P (fun k y => α k * ct y) q) {i j : ι} (hij : i ≠ j) (hi : 0 < q i)
    (hj : 0 < q j) :
    ∃ q' : ι → ℝ, (∀ k, 0 ≤ q' k) ∧ ∑ k, q' k = ∑ k, q k ∧
      ∑ k, α k * ct (q' k) < ∑ k, α k * ct (q k) := by
  -- marginal cost is positive at positive output
  have hct'pos : ∀ y, 0 < y → 0 < ct' y := by
    intro y hy
    have h1 := hconv.slope_le_deriv (x := 0) (y := y) (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy
      (hct y).differentiableAt
    rw [(hct y).deriv] at h1
    have h2 : 0 < slope ct 0 y := by
      rw [slope_def_field]
      exact div_pos (sub_pos.2 (hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy)) (by linarith)
    linarith
  have hC : ∀ k y, HasDerivAt ((fun k y => α k * ct y) k) (α k * ct' y) y :=
    fun k y => (hct y).const_mul (α k)
  have hfi := cc_foc (C' := fun k y => α k * ct' y) hP hC hq hi
  have hfj := cc_foc (C' := fun k y => α k * ct' y) hP hC hq hj
  have hQ : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq.1 k
  have hne : α i * ct' (q i) ≠ α j * ct' (q j) := by
    intro heq
    have hqq : q i = q j := by
      have : P' (∑ k, q k) * (q i - q j) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hP' _ hQ).ne
      · linarith
    rw [hqq] at heq
    exact hij (hα (mul_right_cancel₀ (hct'pos _ hj).ne' heq))
  rcases lt_or_gt_of_ne hne with h | h
  · exact cc_move hct hq.1 hij.symm hj h
  · exact cc_move hct hq.1 hij hi h

/-- The minimum total cost of producing `Q ≥ 0` with the firms' cost functions `Cₖ`: the
aggregate cost function with efficient production (MWG, Section 10.E). -/
noncomputable def efficientCost (C : ι → ℝ → ℝ) (Q : ℝ) : ℝ :=
  sInf {s | ∃ q : ι → ℝ, (∀ k, 0 ≤ q k) ∧ ∑ k, q k = Q ∧ s = ∑ k, C k (q k)}

/-- Aggregate surplus of an allocation `q`: `∫₀^Q P(s) ds − ∑ₖ Cₖ(qₖ)` (MWG, Section 10.E). -/
noncomputable def allocWelfare (P : ℝ → ℝ) (C : ι → ℝ → ℝ) (q : ι → ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..∑ k, q k, P s) - ∑ k, C k (q k)

/-- Aggregate surplus `S(Q) = ∫₀^Q P(s) ds − C(Q)` with efficient production. -/
noncomputable def efficientSurplus (P : ℝ → ℝ) (C : ι → ℝ → ℝ) (Q : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..Q, P s) - efficientCost C Q

omit [DecidableEq ι] in
theorem efficientCost_le {C : ι → ℝ → ℝ} (hC : ∀ k y, 0 ≤ y → 0 ≤ C k y) {q : ι → ℝ}
    (hq : ∀ k, 0 ≤ q k) : efficientCost C (∑ k, q k) ≤ ∑ k, C k (q k) := by
  refine csInf_le ⟨0, ?_⟩ ⟨q, hq, rfl, rfl⟩
  rintro s ⟨q', hq', -, rfl⟩
  exact Finset.sum_nonneg fun k _ => hC k _ (hq' k)

omit [DecidableEq ι] in
/-- **Exercise 12.C.10(b)** (MWG, p. 432). With nonnegative costs, let `Q°` maximize the
efficient surplus `S(Q) = ∫₀^Q p − C(Q)` over `Q ≥ 0`. Then `S(Q°)` bounds the surplus of every
allocation (it is the fully efficient outcome), and for the Cournot allocation `q*` the welfare
loss `S(Q°) − W(q*)` splits into `S(Q°) − S(Q*)`, the loss from the level of output valued with
efficient costs, plus `∑ⱼ cⱼ(qⱼ*) − C(Q*)`, the loss from inefficient production; both are
nonnegative. Measuring the loss only by the first term (the triangle under an efficient cost
curve) would omit the second. -/
theorem exercise_12_C_10b {P : ℝ → ℝ} {C : ι → ℝ → ℝ} (hC : ∀ k y, 0 ≤ y → 0 ≤ C k y)
    {Qo : ℝ} (hmax : ∀ Q, 0 ≤ Q → efficientSurplus P C Q ≤ efficientSurplus P C Qo)
    {q : ι → ℝ} (hq : ∀ k, 0 ≤ q k) :
    (∀ q' : ι → ℝ, (∀ k, 0 ≤ q' k) → allocWelfare P C q' ≤ efficientSurplus P C Qo) ∧
    efficientSurplus P C Qo - allocWelfare P C q =
      (efficientSurplus P C Qo - efficientSurplus P C (∑ k, q k)) +
        (∑ k, C k (q k) - efficientCost C (∑ k, q k)) ∧
    0 ≤ efficientSurplus P C Qo - efficientSurplus P C (∑ k, q k) ∧
    0 ≤ ∑ k, C k (q k) - efficientCost C (∑ k, q k) := by
  refine ⟨fun q' hq' => ?_, by unfold allocWelfare efficientSurplus; ring, ?_, ?_⟩
  · have h1 := efficientCost_le hC hq'
    have h2 := hmax _ (Finset.sum_nonneg (fun k _ => hq' k) : 0 ≤ ∑ k, q' k)
    unfold allocWelfare
    unfold efficientSurplus at h2 ⊢
    linarith
  · linarith [hmax _ (Finset.sum_nonneg (fun k _ => hq k) : 0 ≤ ∑ k, q k)]
  · linarith [efficientCost_le hC hq]

/-- **Exercise 12.C.10(b), strict loss** (MWG, p. 432). In the setting of
`exercise_12_C_10a`, with nonnegative costs, if two firms produce in a Nash equilibrium then
the production-inefficiency term `∑ⱼ cⱼ(qⱼ*) − C(Q*)` is strictly positive. -/
theorem exercise_12_C_10b_strict {P P' ct ct' : ℝ → ℝ} {α : ι → ℝ} (hα : Injective α)
    (hP : ∀ Q, HasDerivAt P (P' Q) Q) (hP' : ∀ Q, 0 ≤ Q → P' Q < 0)
    (hct : ∀ y, HasDerivAt ct (ct' y) y) (hmono : StrictMonoOn ct (Ici 0))
    (hconv : ConvexOn ℝ (Ici 0) ct) (hC : ∀ k y, 0 ≤ y → 0 ≤ α k * ct y) {q : ι → ℝ}
    (hq : IsCournotGenNE P (fun k y => α k * ct y) q) {i j : ι} (hij : i ≠ j) (hi : 0 < q i)
    (hj : 0 < q j) :
    0 < ∑ k, α k * ct (q k) - efficientCost (fun k y => α k * ct y) (∑ k, q k) := by
  obtain ⟨q', hq', hsum, hlt⟩ := exercise_12_C_10a hα hP hP' hct hmono hconv hq hij hi hj
  have := efficientCost_le (C := fun k y => α k * ct y) hC hq'
  rw [hsum] at this
  linarith

/-- **Exercise 12.C.10(a)-(b), instance** (MWG, pp. 431-432). With `P(Q) = 10 − Q`,
`c̃(q) = q`, `α = (2, 1)` the unique equilibrium `(7/3, 10/3)` has both firms producing, so its
output is produced inefficiently and the production-inefficiency loss is positive. -/
theorem exercise_12_C_10_instance :
    IsCournotGenNE (fun z => 10 - 1 * z) (fun k y => ![(2 : ℝ), 1] k * id y) ![7 / 3, 10 / 3] ∧
    0 < ∑ k, ![(2 : ℝ), 1] k * id (![(7 : ℝ) / 3, 10 / 3] k) -
      efficientCost (fun k y => ![(2 : ℝ), 1] k * id y) (∑ k, ![(7 : ℝ) / 3, 10 / 3] k) := by
  have hC : (fun k y => ![(2 : ℝ), 1] k * id y) = ccLinCost 2 1 := by
    funext k y; fin_cases k <;> simp [ccLinCost]
  have hne : IsCournotGenNE (fun z => 10 - 1 * z) (fun k y => ![(2 : ℝ), 1] k * id y)
      ![7 / 3, 10 / 3] := by
    rw [hC, ((exercise_12_C_9a (a := 10) (b := 1) (c₁ := 2) (c₂ := 1) (by norm_num) (by norm_num)
      (by norm_num)).1 (by norm_num) _)]
    funext j; fin_cases j <;> norm_num
  refine ⟨hne, exercise_12_C_10b_strict (P' := fun _ => -1) (ct' := fun _ => 1) ?_ ?_ ?_ ?_
    ?_ ?_ ?_ hne (i := 0) (j := 1) (by decide) (by norm_num) (by norm_num)⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro Q; simpa using ((hasDerivAt_id Q).const_mul 1).const_sub 10
  · intro Q _; norm_num
  · intro y; exact hasDerivAt_id y
  · exact strictMono_id.strictMonoOn _
  · exact convexOn_id (convex_Ici 0)
  · intro k y hy; fin_cases k <;> simp [hy]

/-- The surplus `∫₀^Q (a − bs) ds = aQ − bQ²/2`. -/
theorem cc_lin_integral (a b Q : ℝ) : ∫ s in (0 : ℝ)..Q, (a - b * s) = a * Q - b * Q ^ 2 / 2 := by
  have h : ∫ s in (0 : ℝ)..Q, (a - b * s) =
      (∫ _ in (0 : ℝ)..Q, a) - ∫ s in (0 : ℝ)..Q, b * s :=
    intervalIntegral.integral_sub intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
  rw [h, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- **Exercise 12.C.10(c)** (MWG, p. 432). In the model of Exercise 12.C.9 (`c̃(q) = q`,
`αⱼ = cⱼ`) with both firms producing, welfare at the Cournot equilibrium,
`aQ − bQ²/2 − c₁q₁ − c₂q₂`, has derivative `(11c₁ − 4a − 7c₂)/(9b)` in `c₁`, which is positive
when `11c₁ > 4a + 7c₂`: then a fall in the high-cost firm's `α₁ = c₁` lowers welfare. Example:
`a = 10`, `b = 1`, `c₂ = 1`; the unique equilibria at `c₁ = 5` and `c₁ = 9/2` are `(1/3, 13/3)`
and `(2/3, 25/6)`, and welfare falls from `268/9` to `2123/72`. (Output shifts towards the
inefficient firm 1, raising production costs by more than the gain in consumer surplus.) -/
theorem exercise_12_C_10c {a b c₂ : ℝ} (hb : 0 < b) (c₁ : ℝ) :
    HasDerivAt (fun c => a * ((2 * a - c - c₂) / (3 * b)) -
        b * ((2 * a - c - c₂) / (3 * b)) ^ 2 / 2 -
        c * ((a - 2 * c + c₂) / (3 * b)) - c₂ * ((a - 2 * c₂ + c) / (3 * b)))
      ((11 * c₁ - 4 * a - 7 * c₂) / (9 * b)) c₁ ∧
    (∀ q, IsCournotGenNE (fun z => 10 - 1 * z) (ccLinCost 5 1) q ↔ q = ![1 / 3, 13 / 3]) ∧
    (∀ q, IsCournotGenNE (fun z => 10 - 1 * z) (ccLinCost (9 / 2) 1) q ↔ q = ![2 / 3, 25 / 6]) ∧
    allocWelfare (fun z => 10 - 1 * z) (ccLinCost 5 1) ![1 / 3, 13 / 3] = 268 / 9 ∧
    allocWelfare (fun z => 10 - 1 * z) (ccLinCost (9 / 2) 1) ![2 / 3, 25 / 6] = 2123 / 72 ∧
    (2123 : ℝ) / 72 < 268 / 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · have hQ : HasDerivAt (fun c => (2 * a - c - c₂) / (3 * b)) (-1 / (3 * b)) c₁ := by
      have := (((hasDerivAt_id c₁).const_sub (2 * a)).sub_const c₂).div_const (3 * b)
      simpa [neg_div] using this
    have hq1 : HasDerivAt (fun c => (a - 2 * c + c₂) / (3 * b)) (-2 / (3 * b)) c₁ := by
      have := ((((hasDerivAt_id c₁).const_mul 2).const_sub a).add_const c₂).div_const (3 * b)
      simpa [neg_div] using this
    have hq2 : HasDerivAt (fun c => (a - 2 * c₂ + c) / (3 * b)) (1 / (3 * b)) c₁ := by
      simpa using ((hasDerivAt_id c₁).const_add (a - 2 * c₂)).div_const (3 * b)
    have h := ((((hQ.const_mul a).sub ((hQ.pow 2).const_mul b |>.div_const 2)).sub
      ((hasDerivAt_id c₁).mul hq1)).sub (hq2.const_mul c₂))
    have hb' : b ≠ 0 := hb.ne'
    convert h using 1
    · funext c
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp
      ring
  · intro q
    have := (exercise_12_C_9a (a := 10) (b := 1) (c₁ := 5) (c₂ := 1) (by norm_num) (by norm_num)
      (by norm_num)).1 (by norm_num) q
    rw [this]; norm_num
  · intro q
    have := (exercise_12_C_9a (a := 10) (b := 1) (c₁ := 9 / 2) (c₂ := 1) (by norm_num)
      (by norm_num) (by norm_num)).1 (by norm_num) q
    rw [this]; norm_num
  · unfold allocWelfare
    rw [cc_lin_integral]
    simp [Fin.sum_univ_two, ccLinCost]
    norm_num
  · unfold allocWelfare
    rw [cc_lin_integral]
    simp [Fin.sum_univ_two, ccLinCost]
    norm_num

/-! ### Exercise 12.C.20 -/

/-- Increments of a convex differentiable function grow when shifted right. -/
theorem cc_convex_increment {c c' : ℝ → ℝ} (hc : ∀ y, HasDerivAt c (c' y) y)
    (hconv : ConvexOn ℝ (Ici 0) c) {s t d : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hd : 0 ≤ d) :
    c t - c s ≤ c (t + d) - c (s + d) := by
  have hmono : MonotoneOn c' (Ici 0) := by
    have := hconv.monotoneOn_deriv (fun x _ => (hc x).differentiableAt)
    intro x hx y hy hxy
    have h := this hx hy hxy
    rwa [(hc x).deriv, (hc y).deriv] at h
  have hg : MonotoneOn (fun u => c (u + d) - c u) (Ici 0) := by
    have hderiv : ∀ u, HasDerivAt (fun u => c (u + d) - c u) (c' (u + d) - c' u) u := fun u =>
      ((hc (u + d)).comp_add_const u d).sub (hc u)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
      (fun u _ => (hderiv u).differentiableAt.differentiableWithinAt) fun u hu => ?_
    rw [(hderiv u).deriv]
    rw [interior_Ici] at hu
    have hu' : 0 ≤ u := le_of_lt hu
    have := hmono (mem_Ici.2 hu') (mem_Ici.2 (by linarith)) (by linarith : u ≤ u + d)
    linarith
  have := hg (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst
  simp only at this
  linarith

/-- **Exercise 12.C.20** (MWG, p. 433): Proposition 12.C.2 with a general convex cost `c(q)`.
Let `p` be differentiable with `p'(Q) < 0` for `Q ≥ 0`, let `c` be convex on `[0, ∞)` and
differentiable, and `p(0) > c'(0)`. In any Nash equilibrium `(q₁, q₂)` of the Cournot duopoly
(each `qⱼ ≥ 0` a best response to the other) the price exceeds each firm's marginal cost,
`c'(qⱼ) < p(q₁ + q₂)`, and is below the monopoly price `p(qᵐ)`, for any `qᵐ` solving the
monopoly problem with cost `c`. -/
theorem exercise_12_C_20 {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hP' : ∀ Q, 0 ≤ Q → P' Q < 0) (hc : ∀ y, HasDerivAt c (c' y) y)
    (hconv : ConvexOn ℝ (Ici 0) c) (h0 : c' 0 < P 0) {q₁ q₂ : ℝ}
    (h1 : IsBROn P c (Ici 0) q₂ q₁) (h2 : IsBROn P c (Ici 0) q₁ q₂) {qm : ℝ}
    (hqm : IsMonopolyOptimum P c qm) :
    c' q₁ < P (q₁ + q₂) ∧ c' q₂ < P (q₁ + q₂) ∧ P (q₁ + q₂) < P qm := by
  have hmono : MonotoneOn c' (Ici 0) := by
    have := hconv.monotoneOn_deriv (fun x _ => (hc x).differentiableAt)
    intro x hx y hy hxy
    have h := this hx hy hxy
    rwa [(hc x).deriv, (hc y).deriv] at h
  have hq1 : 0 ≤ q₁ := h1.1
  have hq2 : 0 ≤ q₂ := h2.1
  obtain ⟨f1, f1'⟩ := cbr_foc hP hc h1
  obtain ⟨f2, f2'⟩ := cbr_foc hP hc h2
  rw [add_comm q₂ q₁] at f1 f1'
  have hQ : 0 ≤ q₁ + q₂ := by linarith
  -- both firms produce
  have hpos : ∀ y z, 0 ≤ y → 0 ≤ z → P (y + z) + y * P' (y + z) ≤ c' y →
      (0 < z → P (y + z) + z * P' (y + z) = c' z) → 0 < y := by
    intro y z hy hz fy fz
    by_contra hy0
    have hy0' : y = 0 := le_antisymm (not_lt.1 hy0) hy
    subst hy0'
    simp only [zero_add, zero_mul, add_zero] at fy fz
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · subst hz0; linarith
    · have := fz hz0
      have hm := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
      have := mul_neg_of_pos_of_neg hz0 (hP' z hz)
      linarith
  have hp1 : 0 < q₁ := hpos q₁ q₂ hq1 hq2 f1 f2'
  have hp2 : 0 < q₂ := hpos q₂ q₁ hq2 hq1 (by rw [add_comm q₂ q₁]; exact f2)
    (fun h => by rw [add_comm q₂ q₁]; exact f1' h)
  have e1 := f1' hp1
  have e2 := f2' hp2
  have hm1 : c' q₁ < P (q₁ + q₂) := by nlinarith [mul_neg_of_pos_of_neg hp1 (hP' _ hQ)]
  have hm2 : c' q₂ < P (q₁ + q₂) := by nlinarith [mul_neg_of_pos_of_neg hp2 (hP' _ hQ)]
  refine ⟨hm1, hm2, ?_⟩
  have hPd : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt P (P' z) (Ici 0) z :=
    fun z _ => (hP z).hasDerivWithinAt
  have hanti := strictAntiOn_of_deriv_neg' hPd hP'
  -- the monopoly first-order condition
  obtain ⟨hqmpos, hfm⟩ := eq_12_B_4 (hP qm).hasDerivWithinAt (hc qm).hasDerivWithinAt hqm h0
  -- `Q* ≥ qᵐ`
  have hge : qm ≤ q₁ + q₂ := by
    by_contra hlt
    push Not at hlt
    have hdev := h1.2 (qm - q₂) (mem_Ici.2 (by linarith))
    unfold cbrProfit at hdev
    rw [show q₂ + (qm - q₂) = qm by ring, show q₂ + q₁ = q₁ + q₂ by ring] at hdev
    have hmon := hqm.2 (q₁ + q₂) hQ
    unfold monopolyProfit at hmon
    have hinc := cc_convex_increment hc hconv hq1 (show q₁ ≤ qm - q₂ by linarith) hq2
    rw [show qm - q₂ + q₂ = qm by ring] at hinc
    have hpl : P qm < P (q₁ + q₂) := hanti (mem_Ici.2 hQ) (mem_Ici.2 hqmpos.le) hlt
    nlinarith [mul_lt_mul_of_pos_right hpl hp2]
  rcases eq_or_lt_of_le hge with heq | hlt
  · exfalso
    rw [← heq] at e1
    have hm := hmono (mem_Ici.2 hq1) (mem_Ici.2 hqmpos.le) (by rw [heq]; linarith)
    have : P' qm * q₂ < 0 := mul_neg_of_neg_of_pos (hP' qm hqmpos.le) hp2
    have hsum : qm = q₁ + q₂ := heq
    nlinarith
  · exact hanti (mem_Ici.2 hqm.1) (mem_Ici.2 hQ) hlt

/-- **Exercise 12.C.20, instance** (MWG, p. 433). With `p(Q) = 10 − Q` and `c(q) = q²`, the
outputs `q₁ = q₂ = 2` are mutual best responses and `qᵐ = 5/2` is the monopoly output; the
equilibrium price `6` exceeds marginal cost `4` and is below the monopoly price `15/2`. -/
theorem exercise_12_C_20_instance :
    (2 * 2 : ℝ) < 10 - (2 + 2) ∧ (10 : ℝ) - (2 + 2) < 10 - 5 / 2 := by
  have hP : ∀ Q : ℝ, HasDerivAt (fun Q => 10 - Q) (-1) Q := fun Q => by
    simpa using (hasDerivAt_id Q).const_sub 10
  have hc : ∀ y : ℝ, HasDerivAt (fun y => y ^ 2) (2 * y) y := fun y => by
    simpa using hasDerivAt_pow 2 y
  have hconv : ConvexOn ℝ (Ici 0) (fun y : ℝ => y ^ 2) := (convexOn_pow 2).subset
    (subset_refl _) (convex_Ici 0)
  have hbr : IsBROn (fun Q => 10 - Q) (fun y => y ^ 2) (Ici 0) 2 2 := by
    refine ⟨mem_Ici.2 (by norm_num), fun y _ => ?_⟩
    unfold cbrProfit
    nlinarith [sq_nonneg (y - 2)]
  have hm : IsMonopolyOptimum (fun Q => 10 - Q) (fun y => y ^ 2) (5 / 2) := by
    refine ⟨by norm_num, fun q _ => ?_⟩
    unfold monopolyProfit
    nlinarith [sq_nonneg (q - 5 / 2)]
  obtain ⟨h1, -, h3⟩ := exercise_12_C_20 (P' := fun _ => -1) (c' := fun y => 2 * y) hP
    (fun _ _ => by norm_num) hc hconv (by norm_num) hbr hbr hm
  exact ⟨h1, h3⟩

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Slopes of best responses and the Stackelberg model

MWG, Exercises 12.C.12 and 12.C.18, pp. 432-433.

* `sc_strictMonoOn_diff`, `sc_topkis`: if a player's marginal profit is strictly increasing in
  the rival's choice, the profit has strictly increasing differences and every selection of
  maximizers is nondecreasing (a revealed-preference argument).
* (12.C.12(a)) `exercise_12_C_12a`: for profits `πⱼ(qⱼ, qₖ)` differentiable on `[0, q̄]`, the
  best response is nondecreasing if `∂²πⱼ/∂qⱼ∂qₖ > 0` and nonincreasing if
  `∂²πⱼ/∂qⱼ∂qₖ < 0`, strictly so where it is interior; `exercise_12_C_12a_unique`: strict
  concavity makes the best response unique.
* (12.C.12(b)) `exercise_12_C_12b`: in the Cournot model `πⱼ = p(qⱼ + qₖ)qⱼ − cⱼ(qⱼ)` the cross
  partial is `p'(Q) + p''(Q)qⱼ`; when it is negative best responses slope down.
  `exercise_12_C_12b_normal`: it is negative whenever `p' < 0` and `p'(Q) + p''(Q)Q < 0` (in
  particular for concave demand), which is why downward-sloping best responses are the normal
  case; `exercise_12_C_12b_instance`: linear demand.
* (12.C.18(a)) `exercise_12_C_18a`: with `p' < 0`, `p'(q) + p''(q)q < 0` for `q ≥ 0`, constant
  unit cost `c < p(0)`, a Cournot equilibrium, a follower best-response function and a leader
  optimum (existence is assumed explicitly): the leader produces more than its Cournot output and
  earns strictly more, aggregate output is larger and the follower earns strictly less.
  `exercise_12_C_18a_instance`: linear demand `p(q) = 1 − q`, `c = 0`.
  (12.C.18(b) is graphical.)

The leader's strict gain is proved by parametrizing the follower's reaction by aggregate output
`Q`: the follower's first-order condition gives `y(Q) = (p(Q) − c)/(−p'(Q))`, the leader output
`r(Q) = Q − y(Q)` and the leader profit `Π(Q) = (p(Q) − c)r(Q)`, whose derivative at the Cournot
output is `−q̂(p' + q̂p'') > 0`.

Departures: `p` is twice differentiable on `ℝ`; MWG's hypotheses are completed by `p(0) > c`
(otherwise nothing is produced) and the existence of the equilibria compared.
-/

namespace MWG.MarketPower

open Set Filter Topology

/-- Increasing differences from a marginal-profit comparison: if `∂π/∂u(u, r) < ∂π/∂u(u, r')`
on the interior of the convex set `S`, then `u ↦ π(u, r') − π(u, r)` is strictly increasing
on `S`. -/
theorem sc_strictMonoOn_diff {π D : ℝ → ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S) {r r' : ℝ}
    (hπr : ∀ y ∈ S, HasDerivWithinAt (fun u => π u r) (D y r) S y)
    (hπr' : ∀ y ∈ S, HasDerivWithinAt (fun u => π u r') (D y r') S y)
    (hlt : ∀ y ∈ interior S, D y r < D y r') :
    StrictMonoOn (fun u => π u r' - π u r) S := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun y => D y r' - D y r) hS
    (fun y hy => ((hπr' y hy).sub (hπr y hy)).continuousWithinAt) (fun y hy => ?_)
    (fun y hy => sub_pos.2 (hlt y hy))
  exact ((hπr' y (interior_subset hy)).sub (hπr y (interior_subset hy))).mono interior_subset

/-- **Monotone comparative statics** (revealed preference). If `π(u, r') − π(u, r)` is strictly
increasing in `u` on `S`, `y` maximizes `π(·, r)` and `y'` maximizes `π(·, r')` on `S`, then
`y ≤ y'`. -/
theorem sc_topkis {π : ℝ → ℝ → ℝ} {S : Set ℝ} {r r' y y' : ℝ}
    (hID : StrictMonoOn (fun u => π u r' - π u r) S) (hy : y ∈ S) (hy' : y' ∈ S)
    (hmax : ∀ u ∈ S, π u r ≤ π y r) (hmax' : ∀ u ∈ S, π u r' ≤ π y' r') : y ≤ y' := by
  by_contra hlt
  push Not at hlt
  have h1 := hID hy' hy hlt
  have h2 := hmax y' hy'
  have h3 := hmax' y hy
  simp only at h1
  linarith

/-- A maximizer in the interior of `[0, q̄]` satisfies the first-order condition. -/
theorem sc_foc_interior {f : ℝ → ℝ} {d qbar y : ℝ} (hd : HasDerivWithinAt f d (Icc 0 qbar) y)
    (hy : y ∈ Ioo 0 qbar) (hmax : ∀ u ∈ Icc 0 qbar, f u ≤ f y) : d = 0 := by
  have hmem : Icc 0 qbar ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
  have hloc : IsLocalMax f y := Filter.eventually_of_mem hmem hmax
  exact hloc.hasDerivAt_eq_zero (hd.hasDerivAt hmem)

/-- **Exercise 12.C.12(a)** (MWG, p. 432). Let `π(qⱼ, qₖ)` be firm `j`'s profit on
`[0, q̄]²`, differentiable in `qⱼ` with partial derivative `D(qⱼ, qₖ)`, itself differentiable in
`qₖ` with partial derivative `D₂(qⱼ, qₖ) = ∂²π/∂qⱼ∂qₖ`, and let `b(qₖ)` maximize `π(·, qₖ)` on
`[0, q̄]`. If `∂²π/∂qⱼ∂qₖ > 0` the best response is nondecreasing, and strictly increasing
from any interior point; if `∂²π/∂qⱼ∂qₖ < 0` it is nonincreasing, and strictly decreasing from
any interior point. -/
theorem exercise_12_C_12a {π D D₂ : ℝ → ℝ → ℝ} {qbar : ℝ}
    (hπ : ∀ r ∈ Icc 0 qbar, ∀ y ∈ Icc 0 qbar,
      HasDerivWithinAt (fun u => π u r) (D y r) (Icc 0 qbar) y)
    (hD : ∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, HasDerivWithinAt (D y) (D₂ y r) (Icc 0 qbar) r)
    {b : ℝ → ℝ}
    (hb : ∀ r ∈ Icc 0 qbar, b r ∈ Icc 0 qbar ∧ ∀ u ∈ Icc 0 qbar, π u r ≤ π (b r) r) :
    ((∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, 0 < D₂ y r) →
      MonotoneOn b (Icc 0 qbar) ∧
        ∀ r ∈ Icc 0 qbar, ∀ r' ∈ Icc 0 qbar, r < r' → b r ∈ Ioo 0 qbar → b r < b r') ∧
    ((∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, D₂ y r < 0) →
      AntitoneOn b (Icc 0 qbar) ∧
        ∀ r ∈ Icc 0 qbar, ∀ r' ∈ Icc 0 qbar, r < r' → b r ∈ Ioo 0 qbar → b r' < b r) := by
  have hcont : ∀ y ∈ Icc 0 qbar, ContinuousOn (D y) (Icc 0 qbar) := fun y hy r hr =>
    (hD y hy r hr).continuousWithinAt
  have hint : ∀ y ∈ Icc 0 qbar, ∀ r ∈ interior (Icc (0 : ℝ) qbar),
      HasDerivWithinAt (D y) (D₂ y r) (interior (Icc 0 qbar)) r := fun y hy r hr =>
    (hD y hy r (interior_subset hr)).mono interior_subset
  -- the first-order condition at an interior best response
  have hfoc : ∀ r ∈ Icc 0 qbar, b r ∈ Ioo 0 qbar → D (b r) r = 0 := fun r hr hbr =>
    sc_foc_interior (hπ r hr (b r) (hb r hr).1) hbr (hb r hr).2
  constructor
  · intro hpos
    have hmono : ∀ y ∈ Icc 0 qbar, StrictMonoOn (D y) (Icc 0 qbar) := fun y hy =>
      strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 qbar) (hcont y hy) (hint y hy)
        fun r hr => hpos y hy r (interior_subset hr)
    have hle : MonotoneOn b (Icc 0 qbar) := by
      intro r hr r' hr' hrr
      rcases eq_or_lt_of_le hrr with h | h
      · rw [h]
      have hID := sc_strictMonoOn_diff (π := π) (D := D) (convex_Icc 0 qbar)
        (fun y hy => hπ r hr y hy) (fun y hy => hπ r' hr' y hy)
        (fun y hy => hmono y (interior_subset hy) hr hr' h)
      exact sc_topkis hID (hb r hr).1 (hb r' hr').1 (hb r hr).2 (hb r' hr').2
    refine ⟨hle, fun r hr r' hr' hrr hbr => lt_of_le_of_ne (hle hr hr' hrr.le) fun heq => ?_⟩
    have h0 := hfoc r hr hbr
    have h1 : D (b r) r' = 0 := by
      have := sc_foc_interior (hπ r' hr' (b r) (hb r hr).1) hbr (by
        rw [heq]; exact (hb r' hr').2)
      exact this
    have := hmono (b r) (hb r hr).1 hr hr' hrr
    linarith
  · intro hneg
    have hanti : ∀ y ∈ Icc 0 qbar, StrictAntiOn (D y) (Icc 0 qbar) := fun y hy =>
      strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 qbar) (hcont y hy) (hint y hy)
        fun r hr => hneg y hy r (interior_subset hr)
    have hle : AntitoneOn b (Icc 0 qbar) := by
      intro r hr r' hr' hrr
      rcases eq_or_lt_of_le hrr with h | h
      · rw [h]
      have hID := sc_strictMonoOn_diff (π := π) (D := D) (convex_Icc 0 qbar)
        (fun y hy => hπ r' hr' y hy) (fun y hy => hπ r hr y hy)
        (fun y hy => hanti y (interior_subset hy) hr hr' h)
      exact sc_topkis hID (hb r' hr').1 (hb r hr).1 (hb r' hr').2 (hb r hr).2
    refine ⟨hle, fun r hr r' hr' hrr hbr =>
      lt_of_le_of_ne (hle hr hr' hrr.le) fun heq => ?_⟩
    have h0 := hfoc r hr hbr
    have h1 : D (b r) r' = 0 :=
      sc_foc_interior (hπ r' hr' (b r) (hb r hr).1) hbr (by rw [← heq]; exact (hb r' hr').2)
    have := hanti (b r) (hb r hr).1 hr hr' hrr
    linarith

/-- **Exercise 12.C.12(a), uniqueness** (MWG, p. 432). If `π(·, qₖ)` is strictly concave on
`[0, q̄]`, it has at most one maximizer there, so the best response is a function. -/
theorem exercise_12_C_12a_unique {f : ℝ → ℝ} {qbar : ℝ} (hconc : StrictConcaveOn ℝ (Icc 0 qbar) f)
    {y y' : ℝ} (hy : y ∈ Icc 0 qbar) (hy' : y' ∈ Icc 0 qbar) (hmax : ∀ u ∈ Icc 0 qbar, f u ≤ f y)
    (hmax' : ∀ u ∈ Icc 0 qbar, f u ≤ f y') : y = y' := by
  by_contra hne
  have h := hconc.2 hy hy' hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y' ∈ Icc 0 qbar :=
    (convex_Icc 0 qbar) hy hy' (by norm_num) (by norm_num) (by norm_num)
  have h1 := hmax _ hmid
  have h2 := hmax y' hy'
  have h3 := hmax' y hy
  simp only [smul_eq_mul] at h h1
  linarith

/-- The cross partial of the Cournot profit is negative when `p' < 0` and marginal revenue
falls with output: `p'(Q) + p''(Q)y < 0` for `0 ≤ y ≤ Q`. -/
theorem exercise_12_C_12b_normal {p' p'' : ℝ → ℝ} (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {Q y : ℝ} (hy : 0 ≤ y) (hyQ : y ≤ Q) :
    p' Q + p'' Q * y < 0 := by
  rcases le_total 0 (p'' Q) with h | h
  · nlinarith [hmr Q (hy.trans hyQ)]
  · nlinarith [hneg Q (hy.trans hyQ)]

/-- **Exercise 12.C.12(b)** (MWG, p. 432). In the Cournot model, firm `j`'s profit
`p(qⱼ + qₖ)qⱼ − c(qⱼ)` has cross partial `p'(Q) + p''(Q)qⱼ`. If this is negative on `[0, q̄]²`
(e.g. under `exercise_12_C_12b_normal`), any best-response function on `[0, q̄]` is
nonincreasing, and strictly decreasing from an interior point. -/
theorem exercise_12_C_12b {p p' p'' c c' : ℝ → ℝ} {qbar : ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hc : ∀ y, HasDerivAt c (c' y) y)
    (hcross : ∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, p' (y + r) + p'' (y + r) * y < 0)
    {b : ℝ → ℝ} (hb : ∀ r ∈ Icc 0 qbar, b r ∈ Icc 0 qbar ∧
      ∀ u ∈ Icc 0 qbar, p (u + r) * u - c u ≤ p (b r + r) * b r - c (b r)) :
    AntitoneOn b (Icc 0 qbar) ∧
      ∀ r ∈ Icc 0 qbar, ∀ r' ∈ Icc 0 qbar, r < r' → b r ∈ Ioo 0 qbar → b r' < b r := by
  have hπ : ∀ r ∈ Icc (0 : ℝ) qbar, ∀ y ∈ Icc (0 : ℝ) qbar,
      HasDerivWithinAt (fun u => p (u + r) * u - c u) (p' (y + r) * y + p (y + r) - c' y)
        (Icc 0 qbar) y := by
    intro r _ y _
    have h1 : HasDerivAt (fun u => p (u + r)) (p' (y + r)) y := (hp (y + r)).comp_add_const y r
    have := (h1.mul (hasDerivAt_id y)).sub (hc y)
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id]; ring
  have hD : ∀ y ∈ Icc (0 : ℝ) qbar, ∀ r ∈ Icc (0 : ℝ) qbar,
      HasDerivWithinAt (fun r => p' (y + r) * y + p (y + r) - c' y)
        (p'' (y + r) * y + p' (y + r)) (Icc 0 qbar) r := by
    intro y _ r _
    have h1 : HasDerivAt (fun r => p' (y + r)) (p'' (y + r)) r := (hp' (y + r)).comp_const_add y r
    have h2 : HasDerivAt (fun r => p (y + r)) (p' (y + r)) r := (hp (y + r)).comp_const_add y r
    exact (((h1.mul_const y).add h2).sub_const (c' y)).hasDerivWithinAt
  exact (exercise_12_C_12a (π := fun u r => p (u + r) * u - c u)
    (D := fun y r => p' (y + r) * y + p (y + r) - c' y)
    (D₂ := fun y r => p'' (y + r) * y + p' (y + r)) hπ hD hb).2
    (fun y hy r hr => by have := hcross y hy r hr; linarith)

/-- **Exercise 12.C.12(b), instance** (MWG, p. 432). With linear demand `p(Q) = 1 − Q` and
`c = 0`, the cross partial is `−1 < 0`, so the hypotheses of `exercise_12_C_12b` hold on any
`[0, q̄]`. -/
theorem exercise_12_C_12b_instance (qbar : ℝ) :
    (∀ Q : ℝ, HasDerivAt (fun Q => 1 - Q) (-1) Q) ∧ (∀ Q : ℝ, HasDerivAt (fun _ => (-1 : ℝ)) 0 Q) ∧
    ∀ y ∈ Icc (0 : ℝ) qbar, ∀ r ∈ Icc (0 : ℝ) qbar,
      (fun _ => (-1 : ℝ)) (y + r) + (fun _ => (0 : ℝ)) (y + r) * y < 0 := by
  refine ⟨fun Q => by simpa using (hasDerivAt_id Q).const_sub 1, fun Q => hasDerivAt_const Q _,
    fun y _ r _ => by norm_num⟩

/-! ### Exercise 12.C.18: the Stackelberg model -/

/-- The follower's marginal profit `p(r + y) + yp'(r + y) − c`. -/
theorem sb_hasDerivAt {p p' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q) (c r y : ℝ) :
    HasDerivAt (fun u => cbrProfit p (fun y => c * y) r u) (p (r + y) + y * p' (r + y) - c) y := by
  have h1 : HasDerivAt (fun u => p (r + u)) (p' (r + y)) y := (hp (r + y)).comp_const_add r y
  have h2 : HasDerivAt (fun u => p (r + u) * u - c * u)
      (p' (r + y) * y + p (r + y) * 1 - c * 1) y :=
    (h1.mul (hasDerivAt_id' y)).sub ((hasDerivAt_id' y).const_mul c)
  unfold cbrProfit
  exact h2.congr_deriv (by ring)

/-- The marginal profit is strictly decreasing in own output. -/
theorem sb_anti_own {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    StrictAntiOn (fun u => p (r + u) + u * p' (r + u) - c) (Ici 0) := by
  have hd : ∀ u, HasDerivAt (fun u => p (r + u) + u * p' (r + u) - c)
      (p' (r + u) + (1 * p' (r + u) + u * p'' (r + u))) u := by
    intro u
    have h1 : HasDerivAt (fun u => p (r + u)) (p' (r + u)) u := (hp (r + u)).comp_const_add r u
    have h2 : HasDerivAt (fun u => p' (r + u)) (p'' (r + u)) u := (hp' (r + u)).comp_const_add r u
    exact (h1.add ((hasDerivAt_id u).mul h2)).sub_const c
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => (hd u).hasDerivWithinAt)
    fun u hu => ?_
  rw [interior_Ici] at hu
  have hu' : (0 : ℝ) < u := hu
  have h1 := hneg (r + u) (by linarith)
  have h2 := exercise_12_C_12b_normal hneg hmr hu'.le (show u ≤ r + u by linarith)
  linarith

/-- The marginal profit is strictly decreasing in the rival's output. -/
theorem sb_anti_rival {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) (c : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    StrictAntiOn (fun r => p (r + u) + u * p' (r + u) - c) (Ici 0) := by
  have hd : ∀ r, HasDerivAt (fun r => p (r + u) + u * p' (r + u) - c)
      (p' (r + u) + u * p'' (r + u)) r := by
    intro r
    have h1 : HasDerivAt (fun r => p (r + u)) (p' (r + u)) r := (hp (r + u)).comp_add_const r u
    have h2 : HasDerivAt (fun r => p' (r + u)) (p'' (r + u)) r := (hp' (r + u)).comp_add_const r u
    exact (h1.add (h2.const_mul u)).sub_const c
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (fun r _ => (hd r).continuousAt.continuousWithinAt) (fun r _ => (hd r).hasDerivWithinAt)
    fun r hr => ?_
  rw [interior_Ici] at hr
  have hr' : (0 : ℝ) < r := hr
  have := exercise_12_C_12b_normal hneg hmr hu (show u ≤ r + u by linarith)
  linarith

/-- The follower's best response to `r ≥ 0` is unique. -/
theorem sb_br_unique {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {c r y₁ y₂ : ℝ} (hr : 0 ≤ r)
    (h1 : IsBROn p (fun y => c * y) (Ici 0) r y₁) (h2 : IsBROn p (fun y => c * y) (Ici 0) r y₂) :
    y₁ = y₂ := by
  have hC : ∀ y, HasDerivAt (fun y => c * y) ((fun _ => c) y) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul c
  obtain ⟨f1, f1'⟩ := cbr_foc hp hC h1
  obtain ⟨f2, f2'⟩ := cbr_foc hp hC h2
  have hanti := sb_anti_own hp hp' hneg hmr c hr
  have hy1 : (0 : ℝ) ≤ y₁ := h1.1
  have hy2 : (0 : ℝ) ≤ y₂ := h2.1
  rcases lt_trichotomy y₁ y₂ with h | h | h
  · have := hanti (mem_Ici.2 hy1) (mem_Ici.2 hy2) h
    have := f2' (by linarith)
    simp only at *
    linarith
  · exact h
  · have := hanti (mem_Ici.2 hy2) (mem_Ici.2 hy1) h
    have := f1' (by linarith)
    simp only at *
    linarith

/-- The first-order condition is sufficient for the follower's best response. -/
theorem sb_br_of_foc {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {c r y : ℝ} (hr : 0 ≤ r) (hy : 0 ≤ y)
    (hfoc : p (r + y) + y * p' (r + y) - c = 0) : IsBROn p (fun y => c * y) (Ici 0) r y := by
  have hanti := sb_anti_own hp hp' hneg hmr c hr
  have hd := sb_hasDerivAt hp c r
  refine ⟨mem_Ici.2 hy, fun u hu => ?_⟩
  have hu' : (0 : ℝ) ≤ u := hu
  rcases lt_trichotomy u y with h | h | h
  · have hmono : StrictMonoOn (fun u => cbrProfit p (fun y => c * y) r u) (Icc 0 y) := by
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 y)
        (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
        fun x hx => ?_
      rw [interior_Icc] at hx
      have := hanti (mem_Ici.2 hx.1.le) (mem_Ici.2 hy) hx.2
      simp only at this
      linarith
    exact (hmono ⟨hu', h.le⟩ ⟨hy, le_rfl⟩ h).le
  · rw [h]
  · have hanti' : StrictAntiOn (fun u => cbrProfit p (fun y => c * y) r u) (Ici y) := by
      refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici y)
        (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
        fun x hx => ?_
      rw [interior_Ici] at hx
      have hx' : y < x := hx
      have := hanti (mem_Ici.2 hy) (mem_Ici.2 (by linarith)) hx'
      simp only at this
      linarith
    exact (hanti' (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h).le

/-- The follower's best response is nonincreasing in the leader's output. -/
theorem sb_br_anti {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {c r r' y y' : ℝ} (hr : 0 ≤ r) (hrr : r < r')
    (hy : IsBROn p (fun y => c * y) (Ici 0) r y) (hy' : IsBROn p (fun y => c * y) (Ici 0) r' y') :
    y' ≤ y := by
  have hID := sc_strictMonoOn_diff (π := fun u s => cbrProfit p (fun y => c * y) s u)
    (D := fun u s => p (s + u) + u * p' (s + u) - c) (r := r') (r' := r) (convex_Ici 0)
    (fun u _ => (sb_hasDerivAt hp c r' u).hasDerivWithinAt)
    (fun u _ => (sb_hasDerivAt hp c r u).hasDerivWithinAt) (fun u hu => by
      rw [interior_Ici] at hu
      exact sb_anti_rival hp hp' hneg hmr c (le_of_lt hu) (mem_Ici.2 hr)
        (mem_Ici.2 (by linarith)) hrr)
  exact sc_topkis (π := fun u s => cbrProfit p (fun y => c * y) s u) hID hy'.1 hy.1
    (fun u hu => hy'.2 u hu) (fun u hu => hy.2 u hu)

/-- **Exercise 12.C.18(a)** (MWG, p. 433), the Stackelberg leadership model. Inverse demand
`p` is twice differentiable with `p'(q) < 0` and `p'(q) + p''(q)q < 0` for `q ≥ 0`; both firms
have unit cost `c < p(0)`. Let `(q₁ᶜ, q₂ᶜ)` be a Cournot equilibrium, `b` the follower's
best-response function and `q₁ˢ` an optimal output of the leader, who anticipates `b`. Then
`q₁ˢ > q₁ᶜ`, the leader's profit is strictly larger than in the Cournot equilibrium, aggregate
output `q₁ˢ + b(q₁ˢ)` is strictly larger, and the follower's profit is strictly smaller. -/
theorem exercise_12_C_18a {p p' p'' : ℝ → ℝ} {c : ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) (hc0 : c < p 0) {q1c q2c : ℝ}
    (hc1 : IsBROn p (fun y => c * y) (Ici 0) q2c q1c)
    (hc2 : IsBROn p (fun y => c * y) (Ici 0) q1c q2c) {b : ℝ → ℝ}
    (hb : ∀ r, 0 ≤ r → IsBROn p (fun y => c * y) (Ici 0) r (b r)) {q1s : ℝ} (hq1s : 0 ≤ q1s)
    (hlead : ∀ r, 0 ≤ r → cbrProfit p (fun y => c * y) (b r) r ≤
      cbrProfit p (fun y => c * y) (b q1s) q1s) :
    q1c < q1s ∧
    cbrProfit p (fun y => c * y) q2c q1c < cbrProfit p (fun y => c * y) (b q1s) q1s ∧
    q1c + q2c < q1s + b q1s ∧
    cbrProfit p (fun y => c * y) q1s (b q1s) < cbrProfit p (fun y => c * y) q1c q2c := by
  have hC : ∀ y, HasDerivAt (fun y => c * y) ((fun _ => c) y) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul c
  have hanti : StrictAntiOn p (Ici 0) := strictAntiOn_of_deriv_neg'
    (fun z _ => (hp z).hasDerivWithinAt) hneg
  have h1 : (0 : ℝ) ≤ q1c := hc1.1
  have h2 : (0 : ℝ) ≤ q2c := hc2.1
  obtain ⟨f1, f1'⟩ := cbr_foc hp hC hc1
  obtain ⟨f2, f2'⟩ := cbr_foc hp hC hc2
  rw [add_comm q2c q1c] at f1 f1'
  -- both Cournot firms produce
  have hpos : ∀ y z, 0 ≤ y → 0 ≤ z → p (y + z) + y * p' (y + z) ≤ c →
      (0 < z → p (y + z) + z * p' (y + z) = c) → 0 < y := by
    intro y z hy hz fy fz
    by_contra hy0
    have hy0' : y = 0 := le_antisymm (not_lt.1 hy0) hy
    subst hy0'
    simp only [zero_add, zero_mul, add_zero] at fy fz
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · subst hz0; linarith
    · have := fz hz0
      have := mul_neg_of_pos_of_neg hz0 (hneg z hz)
      linarith
  have hq1 : 0 < q1c := hpos q1c q2c h1 h2 f1 f2'
  have hq2 : 0 < q2c := hpos q2c q1c h2 h1 (by rw [add_comm q2c q1c]; exact f2)
    (fun h => by rw [add_comm q2c q1c]; exact f1' h)
  set Qc := q1c + q2c with hQcdef
  have hQc : 0 < Qc := by linarith
  have hd1 : p' Qc < 0 := hneg Qc hQc.le
  have e1 := f1' hq1
  have e2 := f2' hq2
  have hsym : q1c = q2c := by
    have : p' Qc * (q1c - q2c) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hbc : b q1c = q2c := sb_br_unique hp hp' hneg hmr h1 (hb q1c h1) hc2
  have hstrict1 : ∀ r, 0 ≤ r → r ≠ q1c →
      cbrProfit p (fun y => c * y) q2c r < cbrProfit p (fun y => c * y) q2c q1c := by
    intro r hr hne
    by_contra hle
    push Not at hle
    have hbr : IsBROn p (fun y => c * y) (Ici 0) q2c r := ⟨mem_Ici.2 hr, fun u hu =>
      (hc1.2 u hu).trans hle⟩
    exact hne (sb_br_unique hp hp' hneg hmr h2 hbr hc1)
  -- the leader never produces less than its Cournot output
  have hge : q1c ≤ q1s := by
    by_contra hlt
    push Not at hlt
    have hbs : q2c ≤ b q1s := by
      rw [← hbc]; exact sb_br_anti hp hp' hneg hmr hq1s hlt (hb q1s hq1s) (hb q1c h1)
    have hbs0 : (0 : ℝ) ≤ b q1s := (hb q1s hq1s).1
    have hL1 : cbrProfit p (fun y => c * y) (b q1s) q1s ≤ cbrProfit p (fun y => c * y) q2c q1s := by
      unfold cbrProfit
      have : p (b q1s + q1s) ≤ p (q2c + q1s) :=
        hanti.antitoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right this hq1s]
    have h3 := hstrict1 q1s hq1s (ne_of_lt hlt)
    have h4 := hlead q1c h1
    rw [hbc] at h4
    linarith
  -- the leader can strictly improve on its Cournot profit
  have himp : ∃ r, 0 ≤ r ∧
      cbrProfit p (fun y => c * y) q2c q1c < cbrProfit p (fun y => c * y) (b r) r := by
    set y : ℝ → ℝ := fun Q => (p Q - c) / (-p' Q) with hy
    set rr : ℝ → ℝ := fun Q => Q - y Q with hrr
    set Lf : ℝ → ℝ := fun Q => (p Q - c) * rr Q with hLf
    have hne : -p' Qc ≠ 0 := by linarith
    have hne1 : p' Qc ≠ 0 := hd1.ne
    have hyd : HasDerivAt y ((p' Qc * -p' Qc - (p Qc - c) * -p'' Qc) / (-p' Qc) ^ 2) Qc :=
      ((hp Qc).sub_const c).div (hp' Qc).neg hne
    have hrd : HasDerivAt rr (1 - (p' Qc * -p' Qc - (p Qc - c) * -p'' Qc) / (-p' Qc) ^ 2) Qc :=
      (hasDerivAt_id Qc).sub hyd
    have hLd := ((hp Qc).sub_const c).mul hrd
    have hpc : p Qc - c = -p' Qc * q2c := by linarith
    have hyc : y Qc = q2c := by
      simp only [hy]; rw [hpc]; field_simp
    have hrc : rr Qc = q1c := by
      simp only [hrr]; rw [hyc, hQcdef]; ring
    have hnorm := exercise_12_C_12b_normal hneg hmr h2 (show q2c ≤ Qc by linarith)
    have hdpos : 0 < p' Qc * rr Qc + (p Qc - c) *
        (1 - (p' Qc * -p' Qc - (p Qc - c) * -p'' Qc) / (-p' Qc) ^ 2) := by
      rw [hrc, hpc, hsym]
      have key : p' Qc * q2c + -p' Qc * q2c *
          (1 - (p' Qc * -p' Qc - -p' Qc * q2c * -p'' Qc) / (-p' Qc) ^ 2) =
          -q2c * (p' Qc + p'' Qc * q2c) := by
        field_simp
        ring
      rw [key]
      nlinarith
    have hT := hLd.tendsto_slope_zero_right
    have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (Lf (Qc + t) - Lf Qc) :=
      (tendsto_order.1 hT).1 0 hdpos
    have hshift : Tendsto (fun t : ℝ => Qc + t) (𝓝 0) (𝓝 Qc) := by
      have := (tendsto_const_nhds (x := Qc)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
      simpa using this
    have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < y (Qc + t) ∧ 0 < rr (Qc + t) ∧ 0 < Qc + t :=
      ((hyd.continuousAt.tendsto.comp hshift).eventually (lt_mem_nhds (by rw [hyc]; exact hq2))).and
        (((hrd.continuousAt.tendsto.comp hshift).eventually
          (lt_mem_nhds (by rw [hrc]; exact hq1))).and
          (hshift.eventually (lt_mem_nhds hQc)))
    have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht1, ⟨hyt, hrt, hQt⟩, ht⟩ :=
      (hev1.and ((hev2.filter_mono nhdsWithin_le_nhds).and hev3)).exists
    have hsum : rr (Qc + t) + y (Qc + t) = Qc + t := by simp only [hrr]; ring
    have hfoc : p (rr (Qc + t) + y (Qc + t)) + y (Qc + t) * p' (rr (Qc + t) + y (Qc + t)) - c
        = 0 := by
      rw [hsum]
      have hne' : p' (Qc + t) ≠ 0 := (hneg _ hQt.le).ne
      simp only [hy]
      field_simp
      ring
    have hbr := sb_br_of_foc hp hp' hneg hmr hrt.le hyt.le hfoc
    have hbQ : b (rr (Qc + t)) = y (Qc + t) :=
      sb_br_unique hp hp' hneg hmr hrt.le (hb _ hrt.le) hbr
    refine ⟨rr (Qc + t), hrt.le, ?_⟩
    have hLQ : cbrProfit p (fun y => c * y) (b (rr (Qc + t))) (rr (Qc + t)) = Lf (Qc + t) := by
      rw [hbQ]
      unfold cbrProfit
      simp only [hLf]
      rw [add_comm (y (Qc + t)), hsum]
      ring
    have hLc : cbrProfit p (fun y => c * y) q2c q1c = Lf Qc := by
      unfold cbrProfit
      simp only [hLf]
      rw [hrc, add_comm q2c q1c]
      ring
    rw [hLQ, hLc]
    rw [smul_eq_mul] at ht1
    by_contra hle
    push Not at hle
    have := mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 ht).le (sub_nonpos.2 hle)
    linarith
  obtain ⟨r, hr, hrL⟩ := himp
  have hprofit : cbrProfit p (fun y => c * y) q2c q1c < cbrProfit p (fun y => c * y) (b q1s) q1s :=
    lt_of_lt_of_le hrL (hlead r hr)
  have hlt : q1c < q1s := lt_of_le_of_ne hge fun h => by
    rw [← h, hbc] at hprofit; exact lt_irrefl _ hprofit
  have hbs0 : (0 : ℝ) ≤ b q1s := (hb q1s hq1s).1
  -- aggregate output rises
  have hagg : q1c + q2c < q1s + b q1s := by
    have hconv : ConvexOn ℝ (Ici 0) (fun y : ℝ => c * y) := by
      refine ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
      simp only [smul_eq_mul]
      ring
    have hw := exercise_12_C_8c (P := p) (c := fun y => c * y) (S := Ici 0) hanti hconv
      ordConnected_Ici (subset_refl _) h1 hlt hc2 (hb q1s hq1s)
    rcases eq_or_lt_of_le hw with heq | hlt'
    · exfalso
      obtain ⟨g, g'⟩ := cbr_foc hp hC (hb q1s hq1s)
      have hQ : q1s + b q1s = Qc := by rw [hQcdef]; linarith
      rw [hQ] at g g'
      rcases eq_or_lt_of_le hbs0 with h0 | h0
      · rw [← h0] at g
        simp only [zero_mul, add_zero] at g
        nlinarith [mul_neg_of_pos_of_neg hq2 hd1]
      · have := g' h0
        have hbs : b q1s < q2c := by linarith
        have : p' Qc * (b q1s - q2c) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h <;> linarith
    · linarith
  refine ⟨hlt, hprofit, hagg, ?_⟩
  -- the follower's profit falls
  rcases eq_or_lt_of_le hbs0 with h0 | h0
  · rw [← h0]
    unfold cbrProfit
    simp only [mul_zero, sub_zero]
    have hpc : p Qc - c = -p' Qc * q2c := by linarith
    nlinarith [mul_pos (neg_pos.2 hd1) (mul_pos hq2 hq2)]
  · have hlt2 : p (q1s + b q1s) < p (q1c + b q1s) :=
      hanti (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith)
    have h3 := hc2.2 (b q1s) (mem_Ici.2 hbs0)
    unfold cbrProfit at h3 ⊢
    nlinarith [mul_lt_mul_of_pos_right hlt2 h0]

/-- **Exercise 12.C.18(a), instance** (MWG, p. 433). With `p(q) = 1 − q` (`p' = −1`,
`p'' = 0`) and `c = 0`: the Cournot outputs are `1/3`, the follower's best response is
`b(r) = max{0, (1 − r)/2}`, and the leader's optimum is `1/2`; the leader produces more
(`1/2 > 1/3`) and earns more (`1/8 > 1/9`), total output rises to `3/4 > 2/3`, and the follower
earns less (`1/16 < 1/9`). -/
theorem exercise_12_C_18a_instance :
    (1 : ℝ) / 3 < 1 / 2 ∧
    cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (1 / 3) (1 / 3) <
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (max 0 ((1 - 1 / 2) / 2)) (1 / 2) ∧
    (1 : ℝ) / 3 + 1 / 3 < 1 / 2 + max 0 ((1 - 1 / 2) / 2) ∧
    cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (1 / 2) (max 0 ((1 - 1 / 2) / 2)) <
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (1 / 3) (1 / 3) := by
  have hp : ∀ Q : ℝ, HasDerivAt (fun Q => 1 - Q) ((fun _ => (-1 : ℝ)) Q) Q := fun Q => by
    simpa using (hasDerivAt_id Q).const_sub 1
  have hp' : ∀ Q : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) Q) Q :=
    fun Q => hasDerivAt_const Q _
  have hbr : ∀ r : ℝ, 0 ≤ r → IsBROn (fun Q => 1 - Q) (fun y => 0 * y) (Ici 0) r
      (max 0 ((1 - r) / 2)) := by
    intro r hr
    obtain ⟨h0, huniq⟩ := example_12_C_1_br (a := 1) (b := 1) (c := 0) (qk := r) one_pos hr
    have e : max 0 ((1 - 0 - 1 * r) / (2 * 1)) = max 0 ((1 - r) / 2) := by ring_nf
    rw [e] at h0 huniq
    refine ⟨mem_Ici.2 h0, fun u hu => ?_⟩
    by_cases hu' : u = max 0 ((1 - r) / 2)
    · rw [hu']
    · have := huniq u hu hu'
      unfold cbrProfit
      nlinarith
  have hlead : ∀ r : ℝ, 0 ≤ r →
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (max 0 ((1 - r) / 2)) r ≤
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (max 0 ((1 - 1 / 2) / 2)) (1 / 2) := by
    intro r hr
    unfold cbrProfit
    rw [max_eq_right (by norm_num : (0 : ℝ) ≤ (1 - 1 / 2) / 2)]
    rcases le_total ((1 - r) / 2) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith [sq_nonneg (r - 1 / 2)]
  have hc1 : IsBROn (fun Q => 1 - Q) (fun y => 0 * y) (Ici 0) (1 / 3) (1 / 3) := by
    have := hbr (1 / 3) (by norm_num)
    rwa [show max 0 ((1 - (1 : ℝ) / 3) / 2) = 1 / 3 by norm_num] at this
  have h := exercise_12_C_18a (p := fun Q => 1 - Q) (p' := fun _ => -1) (p'' := fun _ => 0)
    (c := 0) hp hp' (fun _ _ => by norm_num) (fun _ _ => by norm_num) (by norm_num) hc1 hc1
    (b := fun r => max 0 ((1 - r) / 2)) hbr (q1s := 1 / 2) (by norm_num) hlead
  exact h

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The linear city with different costs

MWG, Exercise 12.C.17, p. 433.

The linear city of Example 12.C.2 (`lcDemand`, `lcProfit`; nonpurchase ignored) with unit
costs `c₁ ≤ c₂`.

* `exercise_12_C_17`: if `c₂ − c₁ < 3t` the unique Nash equilibrium is
  `p₁ = t + (2c₁ + c₂)/3`, `p₂ = t + (c₁ + 2c₂)/3`, with both firms making positive sales
  `x₁ = M(t + (c₂ − c₁)/3)/(2t)`, `x₂ = M(t − (c₂ − c₁)/3)/(2t)`; if `c₂ − c₁ ≥ 3t` the Nash
  equilibria are exactly `p₁ = p₂ − t` with `c₁ + 3t ≤ p₂ ≤ c₂`, and in all of them firm 2 makes
  no sales and firm 1 serves the whole market. So an equilibrium with one firm making no sales
  occurs exactly when `c₂ − c₁ ≥ 3t`.
* `exercise_12_C_17_statics`: in the interior equilibrium `dp₁/dc₁ = 2/3`, `dp₂/dc₁ = 1/3`, firm
  1's profit `M(t + (c₂ − c₁)/3)²/(2t)` falls and firm 2's profit `M(t − (c₂ − c₁)/3)²/(2t)`
  rises with `c₁`.
-/

namespace MWG.MarketPower

/-- A Nash equilibrium of the linear-city pricing game with costs `c₁, c₂`. -/
def IsLCNash2 (t M c₁ c₂ p₁ p₂ : ℝ) : Prop :=
  (∀ q, lcProfit t M c₁ q p₂ ≤ lcProfit t M c₁ p₁ p₂) ∧
    ∀ q, lcProfit t M c₂ q p₁ ≤ lcProfit t M c₂ p₂ p₁

/-- A best response in the middle region is the unique one. -/
theorem lc2_br_mid {t M c p pj : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p)
    (h2 : p < c + 3 * t) (hbr : ∀ q, lcProfit t M c q p ≤ lcProfit t M c pj p) :
    pj = (t + p + c) / 2 := by
  by_contra hne
  linarith [(lcBR_mid ht hM h1 h2).2 pj hne, hbr ((t + p + c) / 2)]

/-- A best response in the upper region is the unique one. -/
theorem lc2_br_high {t M c p pj : ℝ} (ht : 0 < t) (hM : 0 < M) (h : c + 3 * t ≤ p)
    (hbr : ∀ q, lcProfit t M c q p ≤ lcProfit t M c pj p) : pj = p - t := by
  by_contra hne
  linarith [(lcBR_high ht hM h).2 pj hne, hbr (p - t)]

/-- Against a rival price above `c − t` the best response is unique. -/
theorem lc2_br {t M c p pj : ℝ} (ht : 0 < t) (hM : 0 < M) (h1 : c - t < p)
    (hbr : ∀ q, lcProfit t M c q p ≤ lcProfit t M c pj p) :
    (p < c + 3 * t ∧ pj = (t + p + c) / 2) ∨ (c + 3 * t ≤ p ∧ pj = p - t) := by
  rcases lt_or_ge p (c + 3 * t) with h | h
  · exact Or.inl ⟨h, lc2_br_mid ht hM h1 h hbr⟩
  · exact Or.inr ⟨h, lc2_br_high ht hM h hbr⟩

/-- **Exercise 12.C.17** (MWG, p. 433). In the linear city with costs `c₁ ≤ c₂` (and `v` large):
if `c₂ − c₁ < 3t`, the unique Nash equilibrium is `p₁ = t + (2c₁ + c₂)/3`,
`p₂ = t + (c₁ + 2c₂)/3`, in which both firms make strictly positive sales; if `c₂ − c₁ ≥ 3t`, the
Nash equilibria are exactly the price pairs `p₁ = p₂ − t` with `c₁ + 3t ≤ p₂ ≤ c₂`, in which
firm 2 makes no sales and firm 1 sells to all `M` consumers. -/
theorem exercise_12_C_17 {t M c₁ c₂ : ℝ} (ht : 0 < t) (hM : 0 < M) (h12 : c₁ ≤ c₂) :
    (c₂ - c₁ < 3 * t → (∀ p₁ p₂, IsLCNash2 t M c₁ c₂ p₁ p₂ ↔
        p₁ = t + (2 * c₁ + c₂) / 3 ∧ p₂ = t + (c₁ + 2 * c₂) / 3) ∧
      lcDemand t M (t + (2 * c₁ + c₂) / 3) (t + (c₁ + 2 * c₂) / 3) =
        M * (t + (c₂ - c₁) / 3) / (2 * t) ∧
      lcDemand t M (t + (c₁ + 2 * c₂) / 3) (t + (2 * c₁ + c₂) / 3) =
        M * (t - (c₂ - c₁) / 3) / (2 * t) ∧
      0 < M * (t + (c₂ - c₁) / 3) / (2 * t) ∧ 0 < M * (t - (c₂ - c₁) / 3) / (2 * t)) ∧
    (3 * t ≤ c₂ - c₁ → (∀ p₁ p₂, IsLCNash2 t M c₁ c₂ p₁ p₂ ↔
        p₁ = p₂ - t ∧ c₁ + 3 * t ≤ p₂ ∧ p₂ ≤ c₂) ∧
      ∀ p₂, lcDemand t M p₂ (p₂ - t) = 0 ∧ lcDemand t M (p₂ - t) p₂ = M) := by
  -- every equilibrium is interior or a corner
  have hnec : ∀ p₁ p₂, IsLCNash2 t M c₁ c₂ p₁ p₂ →
      (p₁ = t + (2 * c₁ + c₂) / 3 ∧ p₂ = t + (c₁ + 2 * c₂) / 3 ∧ c₂ - c₁ < 3 * t) ∨
      (p₁ = p₂ - t ∧ c₁ + 3 * t ≤ p₂ ∧ p₂ ≤ c₂) := by
    rintro p₁ p₂ ⟨h1, h2⟩
    have hπ1 : 0 ≤ lcProfit t M c₁ p₁ p₂ := by
      have := h1 (p₂ + t + 1); rwa [lcProfit_high (by linarith)] at this
    have hπ2 : 0 ≤ lcProfit t M c₂ p₂ p₁ := by
      have := h2 (p₁ + t + 1); rwa [lcProfit_high (by linarith)] at this
    -- firm 2's price exceeds `c₁ − t`
    have hp2 : c₁ - t < p₂ := by
      by_contra hle
      push Not at hle
      have h0 : lcProfit t M c₁ p₁ p₂ = 0 := le_antisymm ((lcBR_low ht hM hle).2 p₁) hπ1
      rcases lt_trichotomy (p₂ + t) p₁ with h | h | h
      · have : lcProfit t M c₂ p₂ p₁ = (p₂ - c₂) * M := lcProfit_low ht (by linarith)
        have : (p₂ - c₂) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
        linarith
      · have : lcProfit t M c₂ p₂ p₁ = (p₂ - c₂) * M := by
          rw [lcProfit_mid (by linarith) (by linarith), ← h]; field_simp; ring
        have : (p₂ - c₂) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
        linarith
      · rcases lt_or_ge p₁ (p₂ - t) with h' | h'
        · rw [lcProfit_low ht h'] at h0
          have : (p₁ - c₁) * M < 0 := mul_neg_of_neg_of_pos (by linarith) hM
          linarith
        · rw [lcProfit_mid h.le h'] at h0
          have : (p₁ - c₁) * ((t + p₂ - p₁) * M / (2 * t)) < 0 :=
            mul_neg_of_neg_of_pos (by linarith) (div_pos (mul_pos (by linarith) hM) (by positivity))
          linarith
    rcases le_or_gt p₁ (c₂ - t) with hA | hB
    · -- firm 2 cannot earn a positive profit
      have h20 : lcProfit t M c₂ p₂ p₁ = 0 := le_antisymm ((lcBR_low ht hM hA).2 p₂) hπ2
      rcases lc2_br ht hM hp2 h1 with ⟨hlt, he⟩ | ⟨hge, he⟩
      · exfalso
        have hsale : 0 < (t + p₁ - p₂) * M / (2 * t) :=
          div_pos (mul_pos (by rw [he]; linarith) hM) (by positivity)
        rw [lcProfit_mid (by rw [he]; linarith) (by rw [he]; linarith)] at h20
        have hp2c : p₂ = c₂ := by
          rcases mul_eq_zero.1 h20 with h | h
          · linarith
          · linarith
        rw [he, hp2c] at hA
        linarith
      · exact Or.inr ⟨he, hge, by linarith⟩
    · rcases lc2_br ht hM hB h2 with ⟨hlt2, he2⟩ | ⟨hge2, he2⟩
      · rcases lc2_br ht hM hp2 h1 with ⟨hlt1, he1⟩ | ⟨hge1, he1⟩
        · left
          refine ⟨by linarith, by linarith, ?_⟩
          have : p₁ = t + (2 * c₁ + c₂) / 3 := by linarith
          linarith
        · exfalso
          have : p₁ = c₂ - t := by linarith
          linarith
      · exfalso
        rcases lc2_br ht hM hp2 h1 with ⟨hlt1, he1⟩ | ⟨hge1, he1⟩
        · linarith
        · linarith
  constructor
  · intro hlt
    refine ⟨fun p₁ p₂ => ⟨fun hne => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rcases hnec p₁ p₂ hne with ⟨e1, e2, -⟩ | ⟨-, hge, hle⟩
      · exact ⟨e1, e2⟩
      · exfalso; linarith
    · rintro ⟨rfl, rfl⟩
      obtain ⟨hb1, hb2⟩ := linearCity_two_costs (M := M) ht hM (by linarith) hlt
      refine ⟨fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = t + (2 * c₁ + c₂) / 3
        · rw [hq]
        · exact (hb1 q hq).le
      · by_cases hq : q = t + (c₁ + 2 * c₂) / 3
        · rw [hq]
        · exact (hb2 q hq).le
    · unfold lcDemand
      split_ifs with a b
      · exfalso; linarith
      · exfalso; linarith
      · field_simp; ring
    · unfold lcDemand
      split_ifs with a b
      · exfalso; linarith
      · exfalso; linarith
      · field_simp; ring
    · exact div_pos (mul_pos hM (by linarith)) (by positivity)
    · exact div_pos (mul_pos hM (by linarith)) (by positivity)
  · intro hge
    refine ⟨fun p₁ p₂ => ⟨fun hne => ?_, ?_⟩, fun p₂ => ⟨?_, ?_⟩⟩
    · rcases hnec p₁ p₂ hne with ⟨-, -, hlt⟩ | h
      · exfalso; linarith
      · exact h
    · rintro ⟨rfl, hlo, hhi⟩
      refine ⟨fun q => ?_, fun q => ?_⟩
      · by_cases hq : q = p₂ - t
        · rw [hq]
        · exact ((lcBR_high ht hM hlo).2 q hq).le
      · have hlow := lcBR_low (M := M) ht hM (show p₂ - t ≤ c₂ - t by linarith)
        rw [show p₂ - t + t = p₂ by ring] at hlow
        rw [hlow.1]
        exact hlow.2 q
    · unfold lcDemand
      split_ifs with a b
      · rfl
      · exfalso; linarith
      · rw [show t + (p₂ - t) - p₂ = 0 by ring]; simp
    · unfold lcDemand
      split_ifs with a b
      · exfalso; linarith
      · rfl
      · field_simp; ring

/-- **Exercise 12.C.17, local comparative statics** (MWG, p. 433). In the interior equilibrium
(`c₂ − c₁ < 3t`), `p₁ = t + (2c₁ + c₂)/3` and `p₂ = t + (c₁ + 2c₂)/3` rise with `c₁` at rates
`2/3` and `1/3`; firm 1's profit `M(t + (c₂ − c₁)/3)²/(2t)` falls and firm 2's profit
`M(t − (c₂ − c₁)/3)²/(2t)` rises with `c₁`. -/
theorem exercise_12_C_17_statics {t M c₂ : ℝ} (ht : 0 < t) (hM : 0 < M) (c₁ : ℝ)
    (h12 : c₁ ≤ c₂) (hlt : c₂ - c₁ < 3 * t) :
    lcProfit t M c₁ (t + (2 * c₁ + c₂) / 3) (t + (c₁ + 2 * c₂) / 3) =
      M * (t + (c₂ - c₁) / 3) ^ 2 / (2 * t) ∧
    lcProfit t M c₂ (t + (c₁ + 2 * c₂) / 3) (t + (2 * c₁ + c₂) / 3) =
      M * (t - (c₂ - c₁) / 3) ^ 2 / (2 * t) ∧
    HasDerivAt (fun c => t + (2 * c + c₂) / 3) (2 / 3) c₁ ∧
    HasDerivAt (fun c => t + (c + 2 * c₂) / 3) (1 / 3) c₁ ∧
    HasDerivAt (fun c => M * (t + (c₂ - c) / 3) ^ 2 / (2 * t))
      (-(M * (t + (c₂ - c₁) / 3) / (3 * t))) c₁ ∧ -(M * (t + (c₂ - c₁) / 3) / (3 * t)) < 0 ∧
    HasDerivAt (fun c => M * (t - (c₂ - c) / 3) ^ 2 / (2 * t))
      (M * (t - (c₂ - c₁) / 3) / (3 * t)) c₁ ∧ 0 < M * (t - (c₂ - c₁) / 3) / (3 * t) := by
  have hd1 := (exercise_12_C_17 (M := M) ht hM h12).1 hlt
  obtain ⟨-, hx1, hx2, -, -⟩ := hd1
  have hA : HasDerivAt (fun c => t + (c₂ - c) / 3) (-1 / 3) c₁ := by
    have := (((hasDerivAt_id c₁).const_sub c₂).div_const 3).const_add t
    simpa [neg_div] using this
  have hB : HasDerivAt (fun c => t - (c₂ - c) / 3) (1 / 3) c₁ := by
    have := (((hasDerivAt_id c₁).const_sub c₂).div_const 3).const_sub t
    simpa [neg_div] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lcProfit; rw [hx1]; field_simp; ring
  · unfold lcProfit; rw [hx2]; field_simp; ring
  · have := (((hasDerivAt_id c₁).const_mul 2).add_const c₂).div_const 3 |>.const_add t
    simpa using this
  · have := (((hasDerivAt_id c₁).add_const (2 * c₂)).div_const 3).const_add t
    simpa using this
  · convert ((hA.pow 2).const_mul M).div_const (2 * t) using 1
    field_simp; ring
  · have : 0 < M * (t + (c₂ - c₁) / 3) / (3 * t) :=
      div_pos (mul_pos hM (by linarith)) (by positivity)
    linarith
  · convert ((hB.pow 2).const_mul M).div_const (2 * t) using 1
    field_simp; ring
  · exact div_pos (mul_pos hM (by linarith)) (by positivity)

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The finitely repeated Bertrand game

MWG, Section 12.D, p. 401.

The `T`-period repetition of a stage game `g` is Chapter 9's multi-stage game with observed
actions (`OSHist`, `OSProfile`): a pure strategy maps histories to actions. Player `i`'s payoff
over the `k` periods following the history `h` is `fhValue g δ σ k h i`, the discounted sum
`∑_{n<k} δⁿ g_i(q_n)` defined by the one-step recursion. A history `h` with `|h| ≤ T` starts a
subgame of `T − |h|` periods; `IsFiniteRepeatedSPNE` is subgame perfection: at every such
history no player gains by any change of strategy.

* `finite_repeated_unique_spne`: if the stage game has a unique pure Nash equilibrium `q*`, then
  in every SPNE `q*` is played after every history of length `< T` (any discount factor `δ`,
  backward induction); `finite_repeated_spne_iff`: for `δ ≥ 0` these are exactly the SPNE.
* `bertrandStage_nash_iff`: the unique Nash equilibrium of the Bertrand duopoly with prices
  `p ≥ 0` is `p₁ = p₂ = c` (from `proposition_12_C_1`).
* `finite_repeated_bertrand` (MWG, p. 401): the unique SPNE of the `T`-period Bertrand duopoly
  has both firms charging `c` in every period after every history, with zero profits;
  `finite_repeated_bertrand_instance`: linear demand.

The discount factor is arbitrary in the uniqueness part; existence (that charging `c` always is
an SPNE) uses `δ ≥ 0`. Stage-game Nash equilibrium is the pure-strategy notion of
`IsStageNash` (Appendix A); strategies are pure, as in Section 12.D.
-/

namespace MWG.MarketPower

open MWG.DynamicGames MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function Set

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- Player `i`'s discounted payoff `∑_{n<k} δⁿ g_i(q_n)` over the `k` periods following the
history `h` when the profile `σ` is played. -/
noncomputable def fhValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (σ : OSProfile A) :
    ℕ → OSHist A → I → ℝ
  | 0, _, _ => 0
  | k + 1, h, i => g i (osPlay σ h) + δ * fhValue g δ σ k (osPlay σ h :: h) i

/-- **Subgame perfection in the `T`-period repeated game** (MWG, pp. 275 and 401). At every
history `h` with `|h| ≤ T` (the start of a subgame of `T − |h|` periods), no player `i` gains by
switching to any other strategy `τ`. -/
def IsFiniteRepeatedSPNE (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (T : ℕ) (σ : OSProfile A) :
    Prop :=
  ∀ h : OSHist A, h.length ≤ T → ∀ i (τ : OSHist A → A i),
    fhValue g δ (update σ i τ) (T - h.length) h i ≤ fhValue g δ σ (T - h.length) h i

/-- The payoff `∑_{n<k} δⁿ g_i(q*)` of playing `q*` for `k` periods. -/
noncomputable def finiteNashValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ)
    (qs : (i : I) → A i) : ℕ → I → ℝ
  | 0, _ => 0
  | k + 1, i => g i qs + δ * finiteNashValue g δ qs k i

omit [DecidableEq I] in
/-- The `k`-period payoff from `h` depends only on play at histories at least as long as `h`. -/
theorem fhValue_congr {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} {σ σ' : OSProfile A} {L : ℕ}
    (hag : ∀ h : OSHist A, L ≤ h.length → osPlay σ' h = osPlay σ h) (k : ℕ) :
    ∀ h : OSHist A, L ≤ h.length → ∀ i, fhValue g δ σ' k h i = fhValue g δ σ k h i := by
  induction k with
  | zero => intro h _ i; rfl
  | succ k ih =>
    intro h hh i
    simp only [fhValue, hag h hh]
    rw [ih _ (by simp only [List.length_cons]; omega)]

/-- **Backward induction, one step.** If `σ` is subgame perfect and the payoff over the last `k`
periods is `∑_{n<k} δⁿ g_i(q*)` after every history of length `T − k`, then after every history
of length `T − k − 1` the profile played is a stage Nash equilibrium. -/
theorem finite_repeated_step {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} {T : ℕ} {σ : OSProfile A}
    {qs : (i : I) → A i} (hspne : IsFiniteRepeatedSPNE g δ T σ) {k : ℕ}
    (ih : ∀ h : OSHist A, h.length + k = T → ∀ i, fhValue g δ σ k h i = finiteNashValue g δ qs k i)
    {h : OSHist A} (hh : h.length + (k + 1) = T) : IsStageNash g (osPlay σ h) := by
  intro i a
  set τ : OSHist A → A i := fun h' => if h'.length = h.length then a else σ i h' with hτ
  have hsp := hspne h (by omega) i τ
  rw [show T - h.length = k + 1 by omega] at hsp
  simp only [fhValue] at hsp
  rw [osPlay_update σ i τ h, show τ h = a by simp [hτ]] at hsp
  have hcong : fhValue g δ (update σ i τ) k (update (osPlay σ h) i a :: h) i =
      fhValue g δ σ k (update (osPlay σ h) i a :: h) i := by
    refine fhValue_congr (L := h.length + 1) (fun h' hh' => ?_) k _ (by simp) i
    rw [osPlay_update]
    have hne : h'.length ≠ h.length := by omega
    have : τ h' = σ i h' := by simp [hτ, hne]
    rw [this]
    funext j
    by_cases hj : j = i
    · subst hj; simp [osPlay]
    · simp [update_of_ne hj]
  rw [hcong, ih _ (by simp only [List.length_cons]; omega),
    ih _ (by simp only [List.length_cons]; omega)] at hsp
  linarith

/-- **Unique SPNE of a finitely repeated game** (MWG, p. 401; Proposition 9.B.4 for pure
strategies). If the stage game has the unique pure Nash equilibrium `q*`, then for every
discount factor `δ`, every SPNE of the `T`-period repetition plays `q*` after every history of
length `< T`, and gives every player `∑_{n<T−|h|} δⁿ g_i(q*)` from every history `h`. -/
theorem finite_repeated_unique_spne {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} {T : ℕ}
    {qs : (i : I) → A i} (huniq : ∀ q, IsStageNash g q → q = qs) {σ : OSProfile A}
    (hspne : IsFiniteRepeatedSPNE g δ T σ) :
    (∀ h : OSHist A, h.length < T → osPlay σ h = qs) ∧
      ∀ h : OSHist A, h.length ≤ T → ∀ i,
        fhValue g δ σ (T - h.length) h i = finiteNashValue g δ qs (T - h.length) i := by
  have hP : ∀ k, ∀ h : OSHist A, h.length + k = T → ∀ i,
      fhValue g δ σ k h i = finiteNashValue g δ qs k i := by
    intro k
    induction k with
    | zero => intro h _ i; rfl
    | succ k ih =>
      intro h hh i
      have hplay := huniq _ (finite_repeated_step hspne ih hh)
      simp only [fhValue, finiteNashValue, hplay]
      rw [ih _ (by simp only [List.length_cons]; omega)]
  refine ⟨fun h hh => huniq _ (finite_repeated_step (k := T - h.length - 1) hspne
    (hP _) (by omega)), fun h hh i => hP _ h (by omega) i⟩

/-- **The finitely repeated game: characterization** (MWG, p. 401). With a unique pure stage
Nash equilibrium `q*` and `δ ≥ 0`, a profile is an SPNE of the `T`-period repetition iff it plays
`q*` after every history of length `< T`. -/
theorem finite_repeated_spne_iff {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) {T : ℕ}
    {qs : (i : I) → A i} (hqs : IsStageNash g qs) (huniq : ∀ q, IsStageNash g q → q = qs)
    (σ : OSProfile A) :
    IsFiniteRepeatedSPNE g δ T σ ↔ ∀ h : OSHist A, h.length < T → osPlay σ h = qs := by
  refine ⟨fun h => (finite_repeated_unique_spne huniq h).1, fun hplay => ?_⟩
  have hQ : ∀ k, ∀ h : OSHist A, h.length + k = T → ∀ i (τ : OSHist A → A i),
      fhValue g δ (update σ i τ) k h i ≤ finiteNashValue g δ qs k i ∧
        fhValue g δ σ k h i = finiteNashValue g δ qs k i := by
    intro k
    induction k with
    | zero => intro h _ i τ; exact ⟨le_rfl, rfl⟩
    | succ k ih =>
      intro h hh i τ
      have hp := hplay h (by omega)
      have hlen : (osPlay (update σ i τ) h :: h).length + k = T := by
        simp only [List.length_cons]; omega
      have hlen' : (osPlay σ h :: h).length + k = T := by simp only [List.length_cons]; omega
      constructor
      · simp only [fhValue, finiteNashValue]
        have h1 := (ih _ hlen i τ).1
        rw [osPlay_update σ i τ h, hp] at h1 ⊢
        have h2 := hqs i (τ h)
        nlinarith [mul_le_mul_of_nonneg_left h1 hδ]
      · simp only [fhValue, finiteNashValue]
        rw [(ih _ hlen' i τ).2, hp]
  intro h hh i τ
  have := hQ (T - h.length) h (by omega) i τ
  rw [this.2]
  exact this.1

/-! ### The Bertrand duopoly -/

/-- **The stage game has a unique Nash equilibrium** (Proposition 12.C.1, prices `p ≥ 0`). In the
Bertrand duopoly with `c > 0` and `x(c) > 0`, the unique pure Nash equilibrium is
`p₁ = p₂ = c`. -/
theorem bertrandStage_nash_iff {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (hc : 0 < (cc : ℝ)) (hxc : 0 < x cc) (q : Fin 2 → Ici (0 : ℝ)) :
    IsStageNash (bertrandStage x cc) q ↔ q = constPrice (Fin 2) cc := by
  constructor
  · intro hq
    have hval : ∀ (j : Fin 2) (a : Ici (0 : ℝ)),
        (fun k => ((update q j a k : Ici (0 : ℝ)) : ℝ)) = update (fun k => (q k : ℝ)) j a := by
      intro j a
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [update_of_ne hk]
    have hne : IsNashEquilibrium (bertrandGame (Fin 2) x cc) (fun k => (q k : ℝ)) := by
      intro j t
      change bertrandProfit x cc (update (fun k => (q k : ℝ)) j t) j ≤
        bertrandProfit x cc (fun k => (q k : ℝ)) j
      have h0 : 0 ≤ bertrandProfit x cc (fun k => (q k : ℝ)) j := by
        have := hq j cc
        unfold bertrandStage at this
        rw [hval] at this
        refine le_trans ?_ this
        unfold bertrandProfit
        simp
      rcases le_or_gt 0 t with ht | ht
      · have := hq j ⟨t, ht⟩
        unfold bertrandStage at this
        rw [hval] at this
        exact this
      · exact le_trans (bertrandProfit_le_zero (ι := Fin 2) hx.nonneg
          (by rw [update_self]; linarith [cc.2])) h0
    have := (proposition_12_C_1 hx hc hxc).2 _ hne
    funext k
    exact Subtype.ext (congrFun this k)
  · rintro rfl
    exact bertrandStage_nash hx cc (by simp)

/-- **The finitely repeated Bertrand duopoly** (MWG, p. 401). Let demand satisfy the Bertrand
assumptions, `c > 0` and `x(c) > 0`. For any discount factor `δ` and horizon `T`, every SPNE of
the `T`-period repeated Bertrand duopoly has both firms charging `c` after every history of
length `< T`, and gives both firms zero profit from every history; for `δ ≥ 0`, the profile that
charges `c` after every history is an SPNE (so it is the unique SPNE). -/
theorem finite_repeated_bertrand {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (hc : 0 < (cc : ℝ)) (hxc : 0 < x cc) (T : ℕ)
    (σ : OSProfile fun _ : Fin 2 => Ici (0 : ℝ)) :
    (IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ T σ →
      (∀ h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)), h.length < T →
        osPlay σ h = constPrice (Fin 2) cc) ∧
      ∀ h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)), h.length ≤ T → ∀ j,
        fhValue (bertrandStage (ι := Fin 2) x cc) δ σ (T - h.length) h j = 0) ∧
    (0 ≤ δ → IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ T
      (fun _ _ => cc : OSProfile fun _ : Fin 2 => Ici (0 : ℝ))) := by
  have huniq : ∀ q, IsStageNash (bertrandStage (ι := Fin 2) x cc) q → q = constPrice (Fin 2) cc :=
    fun q hq => (bertrandStage_nash_iff hx cc hc hxc q).1 hq
  have hqs : IsStageNash (bertrandStage (ι := Fin 2) x cc) (constPrice (Fin 2) cc) :=
    (bertrandStage_nash_iff hx cc hc hxc _).2 rfl
  have hzero : ∀ k j,
      finiteNashValue (bertrandStage (ι := Fin 2) x cc) δ (constPrice (Fin 2) cc) k j = 0 := by
    intro k j
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [finiteNashValue, ih, mul_zero, add_zero]
      simp [bertrandStage, bertrandProfit, constPrice]
  refine ⟨fun hs => ⟨(finite_repeated_unique_spne huniq hs).1, fun h hh j => ?_⟩, fun hδ => ?_⟩
  · rw [(finite_repeated_unique_spne huniq hs).2 h hh j, hzero]
  · exact (finite_repeated_spne_iff hδ hqs huniq _).2 fun _ _ => rfl

/-- The hypotheses of `finite_repeated_bertrand` hold for `x(p) = max{0, 10 − p}` and `c = 1`:
for every `T` and `δ ≥ 0` the unique SPNE charges `1` in every period. -/
theorem finite_repeated_bertrand_instance (T : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) (bcLinDemand 10) cexC1) δ T
      (fun _ _ => cexC1) ∧
    ∀ σ : OSProfile fun _ : Fin 2 => Ici (0 : ℝ),
      IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) (bcLinDemand 10) cexC1) δ T σ →
      ∀ h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)), h.length < T →
        osPlay σ h = constPrice (Fin 2) cexC1 := by
  have hxc : 0 < bcLinDemand 10 (cexC1 : ℝ) := by
    simp only [bcLinDemand, cexC1]; norm_num
  have hc : 0 < (cexC1 : ℝ) := by simp only [cexC1]; norm_num
  refine ⟨(finite_repeated_bertrand (bcLinDemand_isBertrand 10) _ hc hxc T
    (fun _ _ => cexC1)).2 hδ, fun σ hs => ?_⟩
  exact ((finite_repeated_bertrand (bcLinDemand_isBertrand 10) _ hc hxc T σ).1 hs).1

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Repeated Bertrand exercises: cost changes and Rotemberg-Saloner

MWG, Exercises 12.D.4 and 12.D.5, p. 434.

The stage game is the Bertrand duopoly with prices `p ≥ 0` (`bertrandStage`); `R(p) = (p − c)x(p)`
is the profit of a firm serving the whole market.

**Exercise 12.D.4** (`δ ∈ [1/2, 1)`; we treat the duopoly, the case in which `δ ≥ 1/2` is the
threshold of Proposition 12.D.1).
* (a) `exercise_12_D_4a`: after a (permanent) change of the cost to `c'`, the monopoly price
  `pᵐ(c')` at the new cost is sustained by Nash reversion and no stationary price earns more, so
  it is the most profitable sustainable price; `exercise_12_D_4a_monotone`: `pᵐ(c)` is weakly
  increasing in `c`.
* (b) The cost is `c₁` in period 1 and `c₂` from period 2 on. The game is Chapter 9's multi-stage
  game with per-period payoffs depending on the period (`costChangeU`); the profile
  `costChangeProfile p₁ p₂` is Nash reversion along the path `(p₁, p₂, p₂, …)` with reversion to
  `c₂`. `costChange_spne_iff`: with `p₂ = pᵐ(c₂)` (the most profitable continuation, by (a)) it is
  an SPNE iff no period-1 deviation pays against the continuation value `Γ/2`, where
  `Γ = δR₂(pᵐ(c₂))/(1 − δ)`. `exercise_12_D_4b`: a price `p₁ ∈ (c₁, pᵐ(c₁)]` is sustainable iff
  `R₁(p₁) ≤ Γ`; if `Γ ≥ R₁(pᵐ(c₁))` the period-1 monopoly price is sustainable, and otherwise the
  maximal sustainable period-1 price is the `p̂ ∈ (c₁, pᵐ(c₁))` with `R₁(p̂) = Γ`, strictly below
  the period-1 monopoly price; `exercise_12_D_4b_compare`: a cost increase lowers the monopoly
  profit, so at `δ = 1/2` the second case always obtains. Instance: `exercise_12_D_4b_instance`.

**Exercise 12.D.5** (Rotemberg and Saloner). Demand is `x(p)` with probability `λ` and `αx(p)`
with probability `1 − λ`, i.i.d. across periods and observed before prices are set. Nash
reversion with state-contingent prices `(p_H, p_L)` (`IsRSNashReversion`) is formalized by its
one-shot deviation conditions: in state `s`, following earns `π_s(p_s)/2 + δV` where
`V = [λπ_H(p_H)/2 + (1 − λ)π_L(p_L)/2]/(1 − δ)` is the expected value from the next period
(`rsValue`); a deviation to `a` earns the stage profit from `a` and then zero (reversion to `c`,
whose stage profits are zero in both states); after a deviation, `c` must be a stage Nash
equilibrium in both states. Reduction: with bounded payoffs and `δ ∈ [0, 1)`, the one-shot
deviation principle (Chapter 9, `oneShot_deviation_principle_discounted_iff`, whose proof
carries over verbatim to i.i.d. states with expected continuation values) makes these conditions
equivalent to subgame perfection of the Nash reversion profile in the stochastic game; the
stochastic game itself is not built here.
* (a) `exercise_12_D_5a`: for `δ ≥ δ̂ = 1/(1 + λ + (1 − λ)α)`, `p_H = p_L = pᵐ` is an SPNE.
* (b) `exercise_12_D_5b`: `1/2 < δ̂ < 1`; for `δ < δ̂` charging `pᵐ` in the high state is never
  sustainable (whatever `p_L`); for `δ ∈ [1/2, δ̂)` the highest sustainable `p_H` with
  `p_L = pᵐ` is the `p̂ ∈ (c, pᵐ)` with `R(p̂) = δ(1 − λ)αR(pᵐ)/(1 − δ(1 + λ))`, and
  `(p̂, pᵐ)` is sustainable: prices are countercyclical, `p_H < p_L`.
* (c) `exercise_12_D_5c`: for `δ < 1/2` every Nash reversion profile of this form has
  `p_H = p_L = c`. (The book's claim concerns these strategies; we prove it for all of them.)
Instances: `exercise_12_D_5_instance`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

/-- If every price `a ∈ [0, p)` earns at most `B`, so does `p` (continuity from the left). -/
theorem rbx_le_of_below {x : ℝ → ℝ} (hx : Continuous x) {c p B : ℝ} (hc : 0 ≤ c) (hpc : c < p)
    (h : ∀ a, 0 ≤ a → a < p → (a - c) * x a ≤ B) : (p - c) * x p ≤ B := by
  have hf : Continuous fun a : ℝ => (a - c) * x a := (continuous_id.sub continuous_const).mul hx
  refine le_of_tendsto ((hf.tendsto p).mono_left (nhdsWithin_le_nhds (s := Iio p))) ?_
  filter_upwards [Ioo_mem_nhdsLT hpc] with a ha
  exact h a (by linarith [ha.1]) ha.2

/-- A scaled Bertrand demand `αx` (`α > 0`) is a Bertrand demand. -/
theorem rbx_scaled_isBertrand {x : ℝ → ℝ} {pbar α : ℝ} (hx : IsBertrandDemand x pbar)
    (hα : 0 < α) : IsBertrandDemand (fun p => α * x p) pbar where
  cont := continuous_const.mul hx.cont
  nonneg p := mul_nonneg hα.le (hx.nonneg p)
  strictAnti p p' h h0 := by
    have : 0 < x p' := by
      rcases (hx.nonneg p').lt_or_eq with h' | h'
      · exact h'
      · rw [← h', mul_zero] at h0; exact absurd h0 (lt_irrefl 0)
    exact mul_lt_mul_of_pos_left (hx.strictAnti p p' h this) hα
  zero p hp := by simp [hx.zero p hp]

/-- Deviation payoffs in the duopoly against a common price `p`: undercutting to `a < p` earns
`(a − c)x(a)`, overpricing earns `0`, matching earns `(p − c)x(p)/2`. -/
theorem rbx_update {x : ℝ → ℝ} {c : ℝ} (p a : Ici (0 : ℝ)) (j : Fin 2) :
    ((a : ℝ) < p → bertrandStage x c j (update (constPrice (Fin 2) p) j a) = (a - c) * x a) ∧
    ((p : ℝ) < a → bertrandStage x c j (update (constPrice (Fin 2) p) j a) = 0) ∧
    bertrandStage x c j (constPrice (Fin 2) p) = (p - c) * (x p / 2) := by
  have := bertrandStage_update (x := x) (c := c) p a j (by simp)
  simpa using this

/-- Linear demand `max{0, 10 − p}` with cost `c ∈ [0, 10)`: `pᵐ = (10 + c)/2` maximizes
`(p − c)x(p)` over `p ≥ 0`, profit is strictly increasing on `[c, pᵐ]`, and `x(pᵐ) > 0`. -/
theorem rbx_lin_facts {c : ℝ} (hc : c < 10) :
    (∀ a : ℝ, (a - c) * bcLinDemand 10 a ≤
      ((10 + c) / 2 - c) * bcLinDemand 10 ((10 + c) / 2)) ∧
    StrictMonoOn (fun p => (p - c) * bcLinDemand 10 p) (Icc c ((10 + c) / 2)) ∧
    0 < bcLinDemand 10 ((10 + c) / 2) := by
  have hm : bcLinDemand 10 ((10 + c) / 2) = (10 - c) / 2 := by
    simp only [bcLinDemand]; rw [max_eq_right (by linarith)]; ring
  refine ⟨fun a => ?_, fun p hp q hq hpq => ?_, by rw [hm]; linarith⟩
  · rw [hm]
    simp only [bcLinDemand]
    rcases le_total (10 - a) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith [sq_nonneg (a - (10 + c) / 2)]
  · simp only [bcLinDemand]
    rw [max_eq_right (by linarith [hp.2]), max_eq_right (by linarith [hq.2])]
    nlinarith [hp.1, hq.2]

/-! ### Exercise 12.D.4(a) -/

/-- **Exercise 12.D.4(a)** (MWG, p. 434). After the cost changes to `c'` (from then on), the
most profitable sustainable price is the monopoly price `pᵐ(c')` at the new cost: for
`δ ∈ [1/2, 1)` Nash reversion sustains it (Proposition 12.D.1 at cost `c'`), and no stationary
price earns a firm more per period. -/
theorem exercise_12_D_4a {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc' pm' : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1)
    (hpc : (cc' : ℝ) < pm') (hxp : 0 < x pm')
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - cc') * x a ≤ (pm' - cc') * x pm') :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc') δ
        (nashReversion (fun _ => constPrice (Fin 2) pm') (constPrice (Fin 2) cc')) ∧
      ∀ (p : Ici (0 : ℝ)) (j : Fin 2), bertrandStage x cc' j (constPrice (Fin 2) p) ≤
        bertrandStage x cc' j (constPrice (Fin 2) pm') := by
  refine ⟨(proposition_12_D_1 hx cc' pm' hpbar (by linarith) hδ1 hpc hxp hmono).2 hδ,
    fun p j => ?_⟩
  rw [(rbx_update p p j).2.2, (rbx_update pm' pm' j).2.2]
  have := hmono p p.2
  linarith

/-- **Exercise 12.D.4(a), comparative statics** (MWG, p. 434). The monopoly price is weakly
increasing in the cost: if `c < c'`, `pᵐ(c)` and `pᵐ(c')` maximize `(p − c)x(p)` and
`(p − c')x(p)`, and `x(pᵐ(c)) > 0`, then `pᵐ(c) ≤ pᵐ(c')`. So a cost increase (weakly) raises
the most profitable sustainable price. -/
theorem exercise_12_D_4a_monotone {x : ℝ → ℝ} {pbar c c' pm pm' : ℝ}
    (hx : IsBertrandDemand x pbar) (hcc : c < c')
    (hm : (pm' - c) * x pm' ≤ (pm - c) * x pm) (hm' : (pm - c') * x pm ≤ (pm' - c') * x pm')
    (hxp : 0 < x pm) : pm ≤ pm' := by
  by_contra hlt
  push Not at hlt
  have hx' := hx.strictAnti pm' pm hlt hxp
  nlinarith [mul_pos (sub_pos.2 hcc) (sub_pos.2 hx')]

/-- **Exercise 12.D.4(a), instance.** Linear demand `max{0, 10 − p}`, cost rising from `1` to
`2`: the monopoly price rises from `11/2` to `6`, and at `δ = 1/2` Nash reversion sustains `6`. -/
theorem exercise_12_D_4a_instance :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) (bcLinDemand 10) cexP2) (1 / 2)
        (nashReversion (fun _ => constPrice (Fin 2) ⟨6, by norm_num⟩)
          (constPrice (Fin 2) cexP2)) ∧ (11 / 2 : ℝ) ≤ 6 := by
  obtain ⟨h1, -, h3⟩ := rbx_lin_facts (c := 2) (by norm_num)
  norm_num at h1 h3
  refine ⟨(exercise_12_D_4a (bcLinDemand_isBertrand 10) cexP2 ⟨6, by norm_num⟩ (by norm_num)
    (by norm_num) (by norm_num) (by simp [cexP2]; norm_num) h3 fun a _ => ?_).1, by norm_num⟩
  have := h1 a
  simp only [cexP2]
  norm_num at this ⊢
  exact this

/-! ### Exercise 12.D.4(b) -/

/-- Per-period payoffs of the repeated Bertrand duopoly whose unit cost is `c₁` in period 1 (the
empty history) and `c₂` from period 2 on. -/
noncomputable def costChangeU (x : ℝ → ℝ) (c₁ c₂ : Ici (0 : ℝ)) :
    Fin 2 → OSHist (fun _ : Fin 2 => Ici (0 : ℝ)) → (Fin 2 → Ici (0 : ℝ)) → ℝ :=
  fun j h q => bertrandStage x (if h.length = 0 then (c₁ : ℝ) else c₂) j q

/-- The outcome path `(p₁, p₂, p₂, …)`. -/
def costChangePath (p₁ p₂ : Ici (0 : ℝ)) : ℕ → Fin 2 → Ici (0 : ℝ) :=
  fun t => if t = 0 then constPrice (Fin 2) p₁ else constPrice (Fin 2) p₂

/-- Nash reversion along `(p₁, p₂, p₂, …)`, reverting to the price `c₂` (strategies (12.D.1)
adapted to the cost change). -/
noncomputable def costChangeProfile (p₁ p₂ c₂ : Ici (0 : ℝ)) :
    OSProfile fun _ : Fin 2 => Ici (0 : ℝ) :=
  nashReversion (costChangePath p₁ p₂) (constPrice (Fin 2) c₂)

/-- Subgame perfection of `costChangeProfile p₁ p₂ c₂` in the game with the cost change. -/
def CostChangeSustains (x : ℝ → ℝ) (δ : ℝ) (c₁ c₂ p₁ p₂ : Ici (0 : ℝ)) : Prop :=
  ∀ i (τ : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)) → Ici (0 : ℝ)) h,
    osValue (costChangeU x c₁ c₂) δ (update (costChangeProfile p₁ p₂ c₂) i τ) h i ≤
      osValue (costChangeU x c₁ c₂) δ (costChangeProfile p₁ p₂ c₂) h i

open Classical in
/-- The continuation values of `costChangeProfile`: `R₁(p₁)/2 + δW` at the start, `W` on the path
afterwards and `0` after a deviation, where `W = (p₂ − c₂)x(p₂)/(2(1 − δ))`. -/
noncomputable def costChangeValue (x : ℝ → ℝ) (δ : ℝ) (c₁ c₂ p₁ p₂ : Ici (0 : ℝ))
    (h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ))) : ℝ :=
  if h = [] then (p₁ - c₁) * (x p₁ / 2) + δ * ((p₂ - c₂) * (x p₂ / 2) / (1 - δ))
  else if h = pathHist (costChangePath p₁ p₂) h.length then (p₂ - c₂) * (x p₂ / 2) / (1 - δ)
  else 0

theorem costChangeValue_on {x : ℝ → ℝ} {δ : ℝ} {c₁ c₂ p₁ p₂ : Ici (0 : ℝ)} {t : ℕ}
    (ht : t ≠ 0) : costChangeValue x δ c₁ c₂ p₁ p₂ (pathHist (costChangePath p₁ p₂) t) =
      (p₂ - c₂) * (x p₂ / 2) / (1 - δ) := by
  have hne : pathHist (costChangePath p₁ p₂) t ≠ [] := by
    intro h; have := congrArg List.length h; simp [pathHist_length] at this; omega
  simp [costChangeValue, hne, pathHist_length]

theorem costChangeValue_off {x : ℝ → ℝ} {δ : ℝ} {c₁ c₂ p₁ p₂ : Ici (0 : ℝ)}
    {h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ))}
    (hh : h ≠ pathHist (costChangePath p₁ p₂) h.length) :
    costChangeValue x δ c₁ c₂ p₁ p₂ h = 0 := by
  have hne : h ≠ [] := by rintro rfl; exact hh rfl
  simp [costChangeValue, hne, hh]

/-- The value of `costChangeProfile` is `costChangeValue`. -/
theorem osValue_costChange {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (c₁ c₂ p₁ p₂ : Ici (0 : ℝ)) (j : Fin 2)
    (h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ))) :
    osValue (costChangeU x c₁ c₂) δ (costChangeProfile p₁ p₂ c₂) h j =
      costChangeValue x δ c₁ c₂ p₁ p₂ h := by
  have hx0 := hx.nonneg 0
  have hu : ∀ i h q, |costChangeU x c₁ c₂ i h q| ≤ (pbar + c₁) * x 0 + (pbar + c₂) * x 0 := by
    intro i h q
    have h1 := bertrandStage_bound hx c₁.2 hpbar i q
    have h2 := bertrandStage_bound hx c₂.2 hpbar i q
    have h3 : 0 ≤ (pbar + c₁) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₁.2]) hx0
    have h4 : 0 ≤ (pbar + c₂) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₂.2]) hx0
    unfold costChangeU
    split_ifs <;> linarith
  unfold costChangeProfile
  set W := ((p₂ : ℝ) - c₂) * (x p₂ / 2) / (1 - δ) with hW
  set Q := costChangePath p₁ p₂ with hQ
  refine osValue_eq_of_rec hδ0 hδ1 hu _ j _
    (B := |((p₁ : ℝ) - c₁) * (x p₁ / 2) + δ * W| + |W|) (fun h => ?_) (fun h => ?_) h
  · unfold costChangeValue
    split_ifs
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
    · simp only [abs_zero]; positivity
  · have hupd : ∀ (c : Ici (0 : ℝ)) (p : Ici (0 : ℝ)),
        bertrandStage x c j (constPrice (Fin 2) p) = (p - c) * (x p / 2) :=
      fun c p => (rbx_update (c := c) p p j).2.2
    by_cases h0 : h = []
    · subst h0
      have hplay : osPlay (nashReversion Q (constPrice (Fin 2) c₂)) [] =
          constPrice (Fin 2) p₁ := by
        have := osPlay_nashReversion_on (Q := Q) (qs := constPrice (Fin 2) c₂) 0
        simpa [hQ, costChangePath, pathHist] using this
      rw [hplay]
      have hnext : [constPrice (Fin 2) p₁] = pathHist Q 1 := by
        simp [hQ, pathHist, costChangePath]
      rw [hnext, costChangeValue_on one_ne_zero]
      simp [costChangeValue, costChangeU, hupd, ← hW]
    · by_cases hp : h = pathHist Q h.length
      · set t := h.length with ht
        have ht0 : t ≠ 0 := by intro h'; exact h0 (List.length_eq_zero_iff.1 h')
        rw [hp, osPlay_nashReversion_on (Q := Q), pathHist_succ_eq,
          costChangeValue_on ht0, costChangeValue_on (Nat.succ_ne_zero t)]
        have hQt : Q t = constPrice (Fin 2) p₂ := by simp [hQ, costChangePath, ht0]
        rw [hQt]
        simp only [costChangeU, pathHist_length, ht0, ite_false, hupd]
        have : (1 - δ) ≠ 0 := by linarith
        field_simp
        ring
      · rw [osPlay_nashReversion_off hp, costChangeValue_off hp,
          costChangeValue_off (not_pathHist_cons hp _)]
        have hl : h.length ≠ 0 := fun h' => h0 (List.length_eq_zero_iff.1 h')
        simp [costChangeU, hl, hupd]

/-- **Exercise 12.D.4(b): the SPNE condition** (MWG, p. 434). Let `δ ∈ [1/2, 1)` and let `pᵐ₂`
be a monopoly price at the period-2 cost `c₂` (`pᵐ₂ > c₂`, `x(pᵐ₂) > 0`). Nash reversion along
`(p₁, pᵐ₂, pᵐ₂, …)` is an SPNE iff no period-1 deviation `a ≠ p₁` earns more than
`R₁(p₁)/2 + δW`, `W = R₂(pᵐ₂)/(2(1 − δ))`: from period 2 on the condition is that of
Proposition 12.D.1. -/
theorem costChange_spne_iff {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) (c₁ c₂ p₁ pm₂ : Ici (0 : ℝ))
    (hpc₂ : (c₂ : ℝ) < pm₂) (hxp₂ : 0 < x pm₂)
    (hmono₂ : ∀ a : ℝ, 0 ≤ a → (a - c₂) * x a ≤ (pm₂ - c₂) * x pm₂) :
    CostChangeSustains x δ c₁ c₂ p₁ pm₂ ↔
      ∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ p₁ →
        bertrandStage x c₁ j (update (constPrice (Fin 2) p₁) j a) ≤
          (p₁ - c₁) * (x p₁ / 2) + δ * ((pm₂ - c₂) * (x pm₂ / 2) / (1 - δ)) := by
  have hδ0 : 0 ≤ δ := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hx0 := hx.nonneg 0
  have hu : ∀ i h q, |costChangeU x c₁ c₂ i h q| ≤ (pbar + c₁) * x 0 + (pbar + c₂) * x 0 := by
    intro i h q
    have h1 := bertrandStage_bound hx c₁.2 hpbar i q
    have h2 := bertrandStage_bound hx c₂.2 hpbar i q
    have h3 : 0 ≤ (pbar + c₁) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₁.2]) hx0
    have h4 : 0 ≤ (pbar + c₂) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₂.2]) hx0
    unfold costChangeU
    split_ifs <;> linarith
  set Q := costChangePath p₁ pm₂ with hQ
  set W := ((pm₂ : ℝ) - c₂) * (x pm₂ / 2) / (1 - δ) with hW
  have hR₂ : 0 < ((pm₂ : ℝ) - c₂) * x pm₂ := mul_pos (by linarith) hxp₂
  have hWge : ((pm₂ : ℝ) - c₂) * x pm₂ ≤ W := by
    rw [hW, le_div_iff₀ h1δ]; nlinarith
  have hval := fun i h => osValue_costChange (j := i) hx hpbar hδ0 hδ1 c₁ c₂ p₁ pm₂ h
  have hplay0 : osPlay (nashReversion Q (constPrice (Fin 2) c₂)) [] = constPrice (Fin 2) p₁ := by
    have := osPlay_nashReversion_on (Q := Q) (qs := constPrice (Fin 2) c₂) 0
    simpa [hQ, costChangePath, pathHist] using this
  unfold CostChangeSustains
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 hu]
  simp only [hval]
  unfold costChangeProfile
  rw [← hQ]
  constructor
  · intro hos j a ha
    have := hos j [] a
    rw [hplay0] at this
    have hoff : update (Q 0) j a :: pathHist Q 0 ≠
        pathHist Q (update (Q 0) j a :: pathHist Q 0).length :=
      update_cons_off (by simpa [hQ, costChangePath, constPrice] using ha)
    have hQ0 : Q 0 = constPrice (Fin 2) p₁ := by simp [hQ, costChangePath]
    rw [hQ0] at hoff
    have e := costChangeValue_off (x := x) (δ := δ) (c₁ := c₁) (c₂ := c₂) hoff
    change costChangeValue x δ c₁ c₂ p₁ pm₂ [update (constPrice (Fin 2) p₁) j a] = 0 at e
    rw [e] at this
    simpa [costChangeU, costChangeValue] using this
  · intro hcond i h a
    by_cases h0 : h = []
    · subst h0
      rw [hplay0]
      by_cases ha : a = p₁
      · subst ha
        have : update (constPrice (Fin 2) a) i a = constPrice (Fin 2) a := by
          funext k; by_cases hk : k = i
          · subst hk; simp [constPrice]
          · simp [update_of_ne hk, constPrice]
        rw [this]
        have hnext : [constPrice (Fin 2) a] = pathHist Q 1 := by
          simp [hQ, pathHist, costChangePath]
        rw [hnext, costChangeValue_on one_ne_zero]
        simp [costChangeU, costChangeValue, (rbx_update (c := c₁) a a i).2.2, ← hW]
      · have hoff : update (Q 0) i a :: pathHist Q 0 ≠
            pathHist Q (update (Q 0) i a :: pathHist Q 0).length :=
          update_cons_off (by simpa [hQ, costChangePath, constPrice] using ha)
        have hQ0 : Q 0 = constPrice (Fin 2) p₁ := by simp [hQ, costChangePath]
        rw [hQ0] at hoff
        have e := costChangeValue_off (x := x) (δ := δ) (c₁ := c₁) (c₂ := c₂) hoff
        change costChangeValue x δ c₁ c₂ p₁ pm₂ [update (constPrice (Fin 2) p₁) i a] = 0 at e
        rw [e]
        have := hcond i a ha
        simpa [costChangeU, costChangeValue, ← hW] using this
    · have hl : h.length ≠ 0 := fun h' => h0 (List.length_eq_zero_iff.1 h')
      by_cases hp : h = pathHist Q h.length
      · set t := h.length with ht
        have hQt : Q t = constPrice (Fin 2) pm₂ := by simp [hQ, costChangePath, hl]
        rw [hp, osPlay_nashReversion_on (Q := Q), costChangeValue_on hl, hQt]
        by_cases ha : a = pm₂
        · subst ha
          have : update (constPrice (Fin 2) a) i a = constPrice (Fin 2) a := by
            funext k; by_cases hk : k = i
            · subst hk; simp [constPrice]
            · simp [update_of_ne hk, constPrice]
          rw [this, ← hQt, pathHist_succ_eq, costChangeValue_on (Nat.succ_ne_zero t), hQt]
          simp only [costChangeU, pathHist_length, hl, ite_false]
          rw [(rbx_update (c := c₂) a a i).2.2]
          have hne : (1 - δ) ≠ 0 := by linarith
          apply le_of_eq
          field_simp
          ring
        · have hoff : update (Q t) i a :: pathHist Q t ≠
              pathHist Q (update (Q t) i a :: pathHist Q t).length :=
            update_cons_off (by simpa [hQt, constPrice] using ha)
          rw [hQt] at hoff
          rw [costChangeValue_off hoff, mul_zero, add_zero]
          simp only [costChangeU, pathHist_length, hl, ite_false]
          rcases lt_trichotomy (a : ℝ) pm₂ with h' | h' | h'
          · rw [(rbx_update pm₂ a i).1 h']
            linarith [hmono₂ a a.2]
          · exact absurd (Subtype.ext h') ha
          · rw [(rbx_update pm₂ a i).2.1 h']
            linarith
      · rw [osPlay_nashReversion_off hp, costChangeValue_off hp,
          costChangeValue_off (not_pathHist_cons hp _), mul_zero, add_zero]
        simp only [costChangeU, hl, ite_false]
        have := bertrandStage_nash (ι := Fin 2) hx c₂ (by simp) i a
        rw [(rbx_update (c := c₂) c₂ c₂ i).2.2] at this
        simpa using this

/-- **Exercise 12.D.4(b)** (MWG, p. 434). The cost is `c₁` in period 1 and `c₂` afterwards; play
from period 2 on follows Nash reversion at the monopoly price `pᵐ₂` for `c₂`, and
`δ ∈ [1/2, 1)`. Let `R₁(p) = (p − c₁)x(p)`, `Γ = δR₂(pᵐ₂)/(1 − δ)`, and suppose `pᵐ₁ > c₁`
maximizes `R₁` with `R₁` strictly increasing on `[c₁, pᵐ₁]`. Then:
* a period-1 price `p₁ ∈ (c₁, pᵐ₁]` is sustainable iff `R₁(p₁) ≤ Γ`;
* if `Γ ≥ R₁(pᵐ₁)`, the period-1 monopoly price is sustainable;
* if `Γ < R₁(pᵐ₁)`, the maximal sustainable period-1 price is the `p̂ ∈ (c₁, pᵐ₁)` with
  `R₁(p̂) = Γ`: strictly below the monopoly price for the period-1 cost. -/
theorem exercise_12_D_4b {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) (c₁ c₂ pm₁ pm₂ : Ici (0 : ℝ))
    (hpc₂ : (c₂ : ℝ) < pm₂) (hxp₂ : 0 < x pm₂)
    (hmono₂ : ∀ a : ℝ, 0 ≤ a → (a - c₂) * x a ≤ (pm₂ - c₂) * x pm₂)
    (hpc₁ : (c₁ : ℝ) < pm₁) (hmono₁ : ∀ a : ℝ, 0 ≤ a → (a - c₁) * x a ≤ (pm₁ - c₁) * x pm₁)
    (hsm₁ : StrictMonoOn (fun p => (p - c₁) * x p) (Icc (c₁ : ℝ) pm₁)) :
    (∀ p₁ : Ici (0 : ℝ), (c₁ : ℝ) < p₁ → (p₁ : ℝ) ≤ pm₁ →
      (CostChangeSustains x δ c₁ c₂ p₁ pm₂ ↔
        (p₁ - c₁) * x p₁ ≤ δ * ((pm₂ - c₂) * x pm₂) / (1 - δ))) ∧
    ((pm₁ - c₁) * x pm₁ ≤ δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) →
      CostChangeSustains x δ c₁ c₂ pm₁ pm₂) ∧
    (δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) < (pm₁ - c₁) * x pm₁ →
      ∃ ph : Ici (0 : ℝ), (c₁ : ℝ) < ph ∧ (ph : ℝ) < pm₁ ∧
        (ph - c₁) * x ph = δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) ∧
        IsGreatest {q : Ici (0 : ℝ) | CostChangeSustains x δ c₁ c₂ q pm₂} ph) := by
  have h1δ : 0 < 1 - δ := by linarith
  have hc₁0 : (0 : ℝ) ≤ c₁ := c₁.2
  set Γ := δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) with hΓ
  have hR₂ : 0 < ((pm₂ : ℝ) - c₂) * x pm₂ := mul_pos (by linarith) hxp₂
  have hΓpos : 0 < Γ := div_pos (mul_pos (by linarith) hR₂) h1δ
  have hB : ∀ p₁ : Ici (0 : ℝ), ((p₁ : ℝ) - c₁) * (x p₁ / 2) +
      δ * ((pm₂ - c₂) * (x pm₂ / 2) / (1 - δ)) = ((p₁ - c₁) * x p₁ + Γ) / 2 := by
    intro p₁; rw [hΓ]; field_simp
  have hiff := fun p₁ => costChange_spne_iff hx hpbar hδ hδ1 c₁ c₂ p₁ pm₂ hpc₂ hxp₂ hmono₂
  have hbelow : ∀ (p₁ : Ici (0 : ℝ)) (a : ℝ), (c₁ : ℝ) < p₁ → (p₁ : ℝ) ≤ pm₁ → a < p₁ →
      (a - c₁) * x a ≤ (p₁ - c₁) * x p₁ := by
    intro p₁ a hp1 hp2 hap
    rcases le_or_gt (c₁ : ℝ) a with hac | hac
    · exact hsm₁.monotoneOn ⟨hac, by linarith⟩ ⟨hp1.le, hp2⟩ hap.le
    · have h1 : (a - c₁) * x a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg a)
      have h2 : 0 ≤ ((p₁ : ℝ) - c₁) * x p₁ := mul_nonneg (by linarith) (hx.nonneg _)
      linarith
  have part1 : ∀ p₁ : Ici (0 : ℝ), (c₁ : ℝ) < p₁ → (p₁ : ℝ) ≤ pm₁ →
      (CostChangeSustains x δ c₁ c₂ p₁ pm₂ ↔ (p₁ - c₁) * x p₁ ≤ Γ) := by
    intro p₁ hp1 hp2
    rw [hiff p₁]
    simp only [hB]
    constructor
    · intro h
      have := rbx_le_of_below hx.cont hc₁0 hp1 (B := ((p₁ - c₁) * x p₁ + Γ) / 2)
        (fun a ha hap => by
          have h' := h 0 ⟨a, ha⟩ (fun heq => by
            have := congrArg Subtype.val heq; simp at this; linarith)
          rwa [(rbx_update p₁ ⟨a, ha⟩ 0).1 hap] at h')
      linarith
    · intro hle j a ha
      rcases lt_trichotomy (a : ℝ) p₁ with h' | h' | h'
      · rw [(rbx_update p₁ a j).1 h']
        linarith [hbelow p₁ a hp1 hp2 h']
      · exact absurd (Subtype.ext h') ha
      · rw [(rbx_update p₁ a j).2.1 h']
        have : 0 ≤ ((p₁ : ℝ) - c₁) * x p₁ := mul_nonneg (by linarith) (hx.nonneg _)
        linarith
  refine ⟨part1, fun h => (part1 pm₁ hpc₁ le_rfl).2 h, fun hlt => ?_⟩
  have hcont : ContinuousOn (fun p => (p - (c₁ : ℝ)) * x p) (Icc (c₁ : ℝ) pm₁) :=
    ((continuous_id.sub continuous_const).mul hx.cont).continuousOn
  obtain ⟨ph, hph, hval⟩ := intermediate_value_Icc hpc₁.le hcont
    (show Γ ∈ Icc (((c₁ : ℝ) - c₁) * x c₁) ((pm₁ - c₁) * x pm₁) by
      rw [sub_self, zero_mul]; exact ⟨hΓpos.le, hlt.le⟩)
  simp only at hval
  have hph1 : (c₁ : ℝ) < ph := by
    rcases eq_or_lt_of_le hph.1 with h | h
    · rw [← h, sub_self, zero_mul] at hval; linarith
    · exact h
  have hph2 : ph < (pm₁ : ℝ) := by
    rcases eq_or_lt_of_le hph.2 with h | h
    · rw [h] at hval; linarith
    · exact h
  refine ⟨⟨ph, by simp only [mem_Ici]; linarith⟩, hph1, hph2, hval, ?_, ?_⟩
  · exact (part1 ⟨ph, _⟩ hph1 hph2.le).2 hval.le
  · intro q hq
    change (q : ℝ) ≤ ph
    rcases le_or_gt (q : ℝ) c₁ with h | h
    · linarith
    rcases le_or_gt (q : ℝ) pm₁ with h' | h'
    · have hRq := (part1 q h h').1 hq
      exact (hsm₁.le_iff_le ⟨h.le, h'⟩ hph).1 (by linarith)
    · exfalso
      have hc := (hiff q).1 hq 0 pm₁ (fun heq => by
        have := congrArg Subtype.val heq; linarith)
      rw [(rbx_update q pm₁ 0).1 h', hB] at hc
      have := hmono₁ q q.2
      linarith

/-- **Exercise 12.D.4(b), comparison** (MWG, p. 434). A cost increase lowers the monopoly profit:
if `c₁ < c₂`, `x(pᵐ₂) > 0` and `pᵐ₁` maximizes `R₁`, then `R₂(pᵐ₂) < R₁(pᵐ₁)`. Hence at
`δ = 1/2` (where `Γ = R₂(pᵐ₂)`) the maximal sustainable period-1 price is strictly below the
period-1 monopoly price. -/
theorem exercise_12_D_4b_compare {x : ℝ → ℝ} {c₁ c₂ pm₁ pm₂ : ℝ} (hc : c₁ < c₂)
    (hxp₂ : 0 < x pm₂) (hmono₁ : (pm₂ - c₁) * x pm₂ ≤ (pm₁ - c₁) * x pm₁) :
    (pm₂ - c₂) * x pm₂ < (pm₁ - c₁) * x pm₁ ∧
      (1 / 2 : ℝ) * ((pm₂ - c₂) * x pm₂) / (1 - 1 / 2) < (pm₁ - c₁) * x pm₁ := by
  have : (pm₂ - c₂) * x pm₂ < (pm₂ - c₁) * x pm₂ := by nlinarith
  constructor
  · linarith
  · norm_num; linarith

/-- **Exercise 12.D.4(b), instance.** Linear demand `max{0, 10 − p}`, cost `1` in period 1 and
`2` afterwards, `δ = 1/2`: `Γ = 16 < 81/4 = R₁(11/2)`, so the maximal sustainable period-1 price
lies strictly between `1` and the period-1 monopoly price `11/2`. -/
theorem exercise_12_D_4b_instance :
    ∃ ph : Ici (0 : ℝ), (1 : ℝ) < ph ∧ (ph : ℝ) < 11 / 2 ∧
      IsGreatest {q : Ici (0 : ℝ) |
        CostChangeSustains (bcLinDemand 10) (1 / 2) cexC1 cexP2 q ⟨6, by norm_num⟩} ph := by
  obtain ⟨m1, s1, x1⟩ := rbx_lin_facts (c := 1) (by norm_num)
  obtain ⟨m2, -, x2⟩ := rbx_lin_facts (c := 2) (by norm_num)
  norm_num at m1 s1 x1 m2 x2
  obtain ⟨ph, h1, h2, -, h4⟩ := (exercise_12_D_4b (bcLinDemand_isBertrand 10) (by norm_num)
    (le_refl _) (by norm_num) cexC1 cexP2 ⟨11 / 2, by norm_num⟩ ⟨6, by norm_num⟩
    (by simp [cexP2]; norm_num) x2 (fun a _ => by simp only [cexP2]; norm_num; exact m2 a)
    (by simp [cexC1]; norm_num) (fun a _ => by simp only [cexC1]; norm_num; exact m1 a)
    (by simpa [cexC1] using s1)).2.2 (by
      simp only [cexC1, cexP2, bcLinDemand]; norm_num)
  exact ⟨ph, by simpa [cexC1] using h1, by simpa using h2, h4⟩

/-! ### Exercise 12.D.5 (Rotemberg and Saloner) -/

/-- The expected discounted value `V`, measured before the state is drawn, of following Nash
reversion with prices `(p_H, p_L)`:
`V = [λ(p_H − c)x(p_H)/2 + (1 − λ)(p_L − c)αx(p_L)/2]/(1 − δ)`. -/
noncomputable def rsValue (x : ℝ → ℝ) (α lam δ : ℝ) (c pH pL : Ici (0 : ℝ)) : ℝ :=
  (lam * ((pH - c) * (x pH / 2)) + (1 - lam) * ((pL - c) * (α * x pL / 2))) / (1 - δ)

/-- **Exercise 12.D.5: Nash reversion with state-contingent prices** (MWG, p. 434). The one-shot
deviation conditions of the strategies "charge `p_H` in the high state (demand `x`) and `p_L` in
the low state (demand `αx`) if no one has deviated, and `c` otherwise": after a deviation, `c` is
a stage Nash equilibrium in both states; on the path, in each state no deviation `a` beats
following, `π_s(a) + δ·0 ≤ π_s(p_s)/2 + δV` (`V = rsValue`). See the module docstring for the
reduction from subgame perfection in the stochastic game. -/
def IsRSNashReversion (x : ℝ → ℝ) (α lam δ : ℝ) (c pH pL : Ici (0 : ℝ)) : Prop :=
  IsStageNash (bertrandStage (ι := Fin 2) x c) (constPrice (Fin 2) c) ∧
  IsStageNash (bertrandStage (ι := Fin 2) (fun p => α * x p) c) (constPrice (Fin 2) c) ∧
  (∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ pH →
    bertrandStage x c j (update (constPrice (Fin 2) pH) j a) ≤
      bertrandStage x c j (constPrice (Fin 2) pH) + δ * rsValue x α lam δ c pH pL) ∧
  (∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ pL →
    bertrandStage (fun p => α * x p) c j (update (constPrice (Fin 2) pL) j a) ≤
      bertrandStage (fun p => α * x p) c j (constPrice (Fin 2) pL) +
        δ * rsValue x α lam δ c pH pL)

/-- The no-deviation condition in one state, against a common price `p` with continuation
`δV`: no undercut `a < p` earns more than `(p − c)y(p)/2 + δV`, which is nonnegative. -/
theorem rs_state_iff (y : ℝ → ℝ) (c p : Ici (0 : ℝ)) (B : ℝ) :
    (∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ p →
      bertrandStage y c j (update (constPrice (Fin 2) p) j a) ≤
        bertrandStage y c j (constPrice (Fin 2) p) + B) ↔
    (∀ a : ℝ, 0 ≤ a → a < p → (a - c) * y a ≤ (p - c) * (y p / 2) + B) ∧
      0 ≤ (p - c) * (y p / 2) + B := by
  constructor
  · intro h
    refine ⟨fun a ha hap => ?_, ?_⟩
    · have h' := h 0 ⟨a, ha⟩ (fun heq => by
        have := congrArg Subtype.val heq; simp at this; linarith)
      rwa [(rbx_update p ⟨a, ha⟩ 0).1 hap, (rbx_update p p 0).2.2] at h'
    · have h' := h 0 ⟨p + 1, by simp only [mem_Ici]; linarith [Set.mem_Ici.1 p.2]⟩
        (fun heq => by have := congrArg Subtype.val heq; simp at this)
      rwa [(rbx_update p ⟨p + 1, _⟩ 0).2.1 (by simp), (rbx_update p p 0).2.2] at h'
  · rintro ⟨h1, h2⟩ j a ha
    rw [(rbx_update p p j).2.2]
    rcases lt_trichotomy (a : ℝ) p with h' | h' | h'
    · rw [(rbx_update p a j).1 h']; exact h1 a a.2 h'
    · exact absurd (Subtype.ext h') ha
    · rw [(rbx_update p a j).2.1 h']; exact h2

/-- The threshold argument: if the monopoly profit `R > 0` is not beaten by the deviation in the
high state although on-path profits are at most `R`, then `δ(1 + λ + (1 − λ)α) ≥ 1`. -/
theorem rs_threshold {R RH RL lam α δ : ℝ} (hR : 0 < R) (hRH : RH ≤ R) (hRL : RL ≤ R)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hα0 : 0 ≤ α) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h : R ≤ RH / 2 + δ * ((lam * (RH / 2) + (1 - lam) * (α * RL / 2)) / (1 - δ))) :
    1 ≤ δ * (1 + lam + (1 - lam) * α) := by
  have h1δ : 0 < 1 - δ := by linarith
  set V := (lam * (RH / 2) + (1 - lam) * (α * RL / 2)) / (1 - δ) with hV
  have hVe : V * (1 - δ) = lam * (RH / 2) + (1 - lam) * (α * RL / 2) := by
    rw [hV]; field_simp
  have hs : lam * (RH / 2) + (1 - lam) * (α * RL / 2) ≤ (lam + (1 - lam) * α) * (R / 2) := by
    have := mul_le_mul_of_nonneg_left hRH hlam0
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRL hα0)
      (sub_nonneg.2 hlam1)
    nlinarith
  have h2 : R / 2 ≤ δ * V := by linarith
  have h3 : R / 2 * (1 - δ) ≤ δ * (V * (1 - δ)) := by nlinarith
  rw [hVe] at h3
  have h4 : R / 2 * (1 - δ) ≤ δ * ((lam + (1 - lam) * α) * (R / 2)) :=
    h3.trans (mul_le_mul_of_nonneg_left hs hδ0)
  nlinarith

/-- **Exercise 12.D.5(a)** (MWG, p. 434). Let `pᵐ > c` maximize `R(p) = (p − c)x(p)` with
`x(pᵐ) > 0`, `0 < α ≤ 1`, `λ ∈ [0, 1]`. If `δ ≥ δ̂ = 1/(1 + λ + (1 − λ)α)` (and `δ < 1`), then
`p_H = p_L = pᵐ` is sustained by Nash reversion. -/
theorem exercise_12_D_5a {x : ℝ → ℝ} {pbar α lam δ : ℝ} (hx : IsBertrandDemand x pbar)
    (c pm : Ici (0 : ℝ)) (hpc : (c : ℝ) < pm) (hxp : 0 < x pm)
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - c) * x a ≤ (pm - c) * x pm) (hα : 0 < α) (hα1 : α ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hδ1 : δ < 1)
    (hδ : 1 / (1 + lam + (1 - lam) * α) ≤ δ) :
    IsRSNashReversion x α lam δ c pm pm := by
  have h1δ : 0 < 1 - δ := by linarith
  set R := ((pm : ℝ) - c) * x pm with hR
  have hRpos : 0 < R := mul_pos (by linarith) hxp
  have hs0 : 0 < 1 + lam + (1 - lam) * α := by nlinarith
  have hδs : 1 ≤ δ * (1 + lam + (1 - lam) * α) := by
    rw [div_le_iff₀ hs0] at hδ; linarith
  have hδ0 : 0 ≤ δ := by nlinarith
  have hV : δ * rsValue x α lam δ c pm pm =
      δ * (lam + (1 - lam) * α) * R / (2 * (1 - δ)) := by
    unfold rsValue; rw [hR]; field_simp
  have hkey : R / 2 ≤ δ * rsValue x α lam δ c pm pm := by
    rw [hV, le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨bertrandStage_nash hx c (by simp),
    bertrandStage_nash (rbx_scaled_isBertrand hx hα) c (by simp), ?_, ?_⟩
  · rw [rs_state_iff]
    refine ⟨fun a ha _ => ?_, ?_⟩
    · have := hmono a ha
      linarith
    · linarith
  · rw [rs_state_iff]
    refine ⟨fun a ha _ => ?_, ?_⟩
    · have h1 : (a - c) * (α * x a) = α * ((a - c) * x a) := by ring
      have h2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * (R / 2) := by rw [hR]; ring
      rw [h1, h2]
      nlinarith [hmono a ha]
    · have h2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * (R / 2) := by rw [hR]; ring
      rw [h2]; nlinarith

/-- A sustained high-state price at or below `c`, or in `(c, pᵐ]`, or above `pᵐ`: the high-state
condition of Nash reversion with `p_L = pᵐ`, in terms of `R(p_H)`. -/
theorem rs_high_nec {x : ℝ → ℝ} {pbar α lam δ : ℝ} (hx : IsBertrandDemand x pbar)
    (c pH pL : Ici (0 : ℝ)) (hpc : (c : ℝ) < pH)
    (h : IsRSNashReversion x α lam δ c pH pL) :
    (pH - c) * x pH ≤ (pH - c) * (x pH / 2) + δ * rsValue x α lam δ c pH pL := by
  have h3 := ((rs_state_iff x c pH _).1 h.2.2.1).1
  exact rbx_le_of_below hx.cont c.2 hpc h3

/-- **Exercise 12.D.5(b)** (MWG, p. 434). With `0 < α < 1`, `0 < λ < 1` and the hypotheses of
(a), let `δ̂ = 1/(1 + λ + (1 − λ)α)`. Then `1/2 < δ̂ < 1`; for `0 ≤ δ < δ̂` the monopoly price
cannot be sustained in the high state, whatever `p_L`; and if `R` is strictly increasing on
`[c, pᵐ]` and `1/2 ≤ δ < δ̂`, the highest `p_H` sustainable together with `p_L = pᵐ` is the
`p̂ ∈ (c, pᵐ)` with `R(p̂) = δ(1 − λ)αR(pᵐ)/(1 − δ(1 + λ))`, and `(p̂, pᵐ)` is sustainable:
prices are countercyclical (`p_H = p̂ < pᵐ = p_L`). -/
theorem exercise_12_D_5b {x : ℝ → ℝ} {pbar α lam : ℝ} (hx : IsBertrandDemand x pbar)
    (c pm : Ici (0 : ℝ)) (hpc : (c : ℝ) < pm) (hxp : 0 < x pm)
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - c) * x a ≤ (pm - c) * x pm) (hα : 0 < α) (hα1 : α < 1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (1 / 2 < 1 / (1 + lam + (1 - lam) * α) ∧ 1 / (1 + lam + (1 - lam) * α) < 1) ∧
    (∀ δ, 0 ≤ δ → δ < 1 / (1 + lam + (1 - lam) * α) →
      ∀ pL, ¬ IsRSNashReversion x α lam δ c pm pL) ∧
    (StrictMonoOn (fun p => (p - c) * x p) (Icc (c : ℝ) pm) →
      ∀ δ, 1 / 2 ≤ δ → δ < 1 / (1 + lam + (1 - lam) * α) →
      ∃ ph : Ici (0 : ℝ), (c : ℝ) < ph ∧ (ph : ℝ) < pm ∧
        (ph - c) * x ph = δ * (1 - lam) * α * ((pm - c) * x pm) / (1 - δ * (1 + lam)) ∧
        IsGreatest {q : Ici (0 : ℝ) | IsRSNashReversion x α lam δ c q pm} ph) := by
  set R := ((pm : ℝ) - c) * x pm with hR
  have hRpos : 0 < R := mul_pos (by linarith) hxp
  set s := lam + (1 - lam) * α with hs
  have hs1 : s < 1 := by rw [hs]; nlinarith
  have hs0 : 0 < s := by rw [hs]; nlinarith
  have hc0 : (0 : ℝ) ≤ c := c.2
  -- part (ii)
  have part2 : ∀ δ, 0 ≤ δ → δ < 1 / (1 + lam + (1 - lam) * α) →
      ∀ (pH pL : Ici (0 : ℝ)), (pm : ℝ) ≤ pH → ¬ IsRSNashReversion x α lam δ c pH pL := by
    intro δ hδ0 hδ pH pL hpH h
    have hδ1 : δ < 1 := lt_of_lt_of_le hδ (by rw [div_le_one (by nlinarith)]; nlinarith)
    have hdev : R ≤ (pH - c) * (x pH / 2) + δ * rsValue x α lam δ c pH pL := by
      rcases eq_or_lt_of_le hpH with heq | hlt
      · have := rs_high_nec hx c pH pL (by rw [← heq]; exact hpc) h
        have e : pm = pH := Subtype.ext heq
        rw [← e] at this ⊢; exact this
      · have := ((rs_state_iff x c pH _).1 h.2.2.1).1 pm pm.2 hlt
        exact this
    have hth := rs_threshold (R := R) (RH := (pH - c) * x pH) (RL := (pL - c) * x pL) hRpos
      (hmono pH pH.2) (hmono pL pL.2) hlam0.le hlam1.le hα.le hδ0 hδ1 (by
        unfold rsValue at hdev
        convert hdev using 2 <;> ring)
    rw [lt_div_iff₀ (by nlinarith)] at hδ
    linarith
  refine ⟨⟨?_, ?_⟩, fun δ hδ0 hδ pL => part2 δ hδ0 hδ pm pL le_rfl, fun hsm δ hδ hδh => ?_⟩
  · rw [lt_div_iff₀ (by nlinarith)]; nlinarith
  · rw [div_lt_one (by nlinarith)]; nlinarith
  -- part (iii)
  have hδs : δ * (1 + s) < 1 := by
    rw [lt_div_iff₀ (by nlinarith)] at hδh; rw [hs]; linarith
  have hD : 0 < 1 - δ * (1 + lam) := by nlinarith
  have h1δ : 0 < 1 - δ := by nlinarith
  set Rs := δ * (1 - lam) * α * R / (1 - δ * (1 + lam)) with hRs
  have hRs0 : 0 < Rs := div_pos (by
    have : 0 < 1 - lam := by linarith
    have : 0 < δ := by linarith
    positivity) hD
  have hRsR : Rs < R := by
    rw [hRs, div_lt_iff₀ hD]; rw [hs] at hδs; nlinarith
  have hcont : ContinuousOn (fun p => (p - (c : ℝ)) * x p) (Icc (c : ℝ) pm) :=
    ((continuous_id.sub continuous_const).mul hx.cont).continuousOn
  obtain ⟨ph, hph, hval⟩ := intermediate_value_Icc hpc.le hcont
    (show Rs ∈ Icc (((c : ℝ) - c) * x c) ((pm - c) * x pm) by
      rw [sub_self, zero_mul]; exact ⟨hRs0.le, hRsR.le⟩)
  simp only at hval
  have hph1 : (c : ℝ) < ph := by
    rcases eq_or_lt_of_le hph.1 with h | h
    · rw [← h, sub_self, zero_mul] at hval; linarith
    · exact h
  have hph2 : ph < (pm : ℝ) := by
    rcases eq_or_lt_of_le hph.2 with h | h
    · rw [h] at hval; linarith
    · exact h
  set PH : Ici (0 : ℝ) := ⟨ph, by simp only [mem_Ici]; linarith⟩ with hPH
  -- the value at `(p̂, pᵐ)`: `δV = R*/2`
  have hV : δ * rsValue x α lam δ c PH pm = Rs / 2 := by
    unfold rsValue
    have e1 : ((PH : ℝ) - c) * (x PH / 2) = Rs / 2 := by
      simp only [hPH]; rw [← hval]; ring
    have e2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * R / 2 := by rw [hR]; ring
    rw [e1, e2, hRs]
    field_simp
    ring
  have hbelow : ∀ a : ℝ, a < ph → (a - c) * x a ≤ (ph - c) * x ph := by
    intro a hap
    rcases le_or_gt (c : ℝ) a with hac | hac
    · exact hsm.monotoneOn ⟨hac, by linarith⟩ ⟨hph1.le, hph2.le⟩ hap.le
    · have h1 : (a - c) * x a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg a)
      linarith
  refine ⟨PH, hph1, hph2, hval, ⟨bertrandStage_nash hx c (by simp),
    bertrandStage_nash (rbx_scaled_isBertrand hx hα) c (by simp), ?_, ?_⟩, ?_⟩
  · rw [rs_state_iff, hV]
    have e1 : ((PH : ℝ) - c) * (x PH / 2) = Rs / 2 := by
      simp only [hPH]; rw [← hval]; ring
    rw [e1]
    refine ⟨fun a _ hap => ?_, by linarith⟩
    have := hbelow a hap
    linarith
  · rw [rs_state_iff, hV]
    have e2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * R / 2 := by rw [hR]; ring
    rw [e2]
    have hαR : α * R ≤ Rs := by
      rw [hRs, le_div_iff₀ hD]
      have : 1 - δ * (1 + lam) ≤ δ * (1 - lam) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_pos hα hRpos).le]
    refine ⟨fun a ha _ => ?_, by positivity⟩
    have h1 : (a - c) * (α * x a) = α * ((a - c) * x a) := by ring
    rw [h1]
    nlinarith [hmono a ha]
  · intro q hq
    change (q : ℝ) ≤ ph
    rcases le_or_gt (q : ℝ) c with h | h
    · linarith
    rcases le_or_gt (q : ℝ) pm with h' | h'
    · have hn := rs_high_nec hx c q pm h hq
      unfold rsValue at hn
      have hRq : ((q : ℝ) - c) * x q ≤ Rs := by
        rw [hRs, le_div_iff₀ hD]
        have e : (pm - c) * (α * x pm / 2) = α * R / 2 := by rw [hR]; ring
        rw [e] at hn
        set Rq := ((q : ℝ) - c) * x q
        have e3 : ((q : ℝ) - c) * (x q / 2) = Rq / 2 := by ring
        rw [e3] at hn
        have hn' : Rq / 2 ≤ δ * ((lam * (Rq / 2) + (1 - lam) * (α * R / 2)) / (1 - δ)) := by
          linarith
        have hVe : (lam * (Rq / 2) + (1 - lam) * (α * R / 2)) / (1 - δ) * (1 - δ) =
            lam * (Rq / 2) + (1 - lam) * (α * R / 2) := by field_simp
        have h2 : Rq / 2 * (1 - δ) ≤ δ * (lam * (Rq / 2) + (1 - lam) * (α * R / 2)) := by
          have := mul_le_mul_of_nonneg_right hn' h1δ.le
          rw [mul_assoc, hVe] at this; exact this
        linarith
      rw [← hval] at hRq
      exact (hsm.le_iff_le ⟨h.le, h'⟩ hph).1 hRq
    · exact absurd hq (part2 δ (by linarith) hδh q pm h'.le)

/-- A price with zero profit that no undercut can beat with a positive profit equals `c`
(demand positive at `c`). -/
theorem rbx_price_eq_c {y : ℝ → ℝ} {pbar : ℝ} (hy : IsBertrandDemand y pbar) (c p : Ici (0 : ℝ))
    (hyc : 0 < y c) (hR : ((p : ℝ) - c) * y p = 0)
    (hdev : ∀ a : ℝ, 0 ≤ a → a < p → (a - c) * y a ≤ 0) : (p : ℝ) = c := by
  rcases lt_trichotomy (p : ℝ) c with h | h | h
  · have hyp : 0 < y p := lt_trans hyc (hy.strictAnti p c h hyc)
    have : ((p : ℝ) - c) * y p < 0 := mul_neg_of_neg_of_pos (by linarith) hyp
    linarith
  · exact h
  · exfalso
    have hev : ∀ᶠ a in 𝓝[>] (c : ℝ), 0 < y a ∧ a < p ∧ (c : ℝ) < a := by
      have h1 : ∀ᶠ a in 𝓝[>] (c : ℝ), 0 < y a :=
        (hy.cont.continuousAt.eventually (lt_mem_nhds hyc)).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, Ioo_mem_nhdsGT h] with a ha1 ha2
      exact ⟨ha1, ha2.2, ha2.1⟩
    obtain ⟨a, ha1, ha2, ha3⟩ := hev.exists
    have := hdev a (by linarith [Set.mem_Ici.1 c.2]) ha2
    have : 0 < (a - c) * y a := mul_pos (by linarith) ha1
    linarith

/-- **Exercise 12.D.5(c)** (MWG, p. 434). If `δ < 1/2` (with `δ ≥ 0`, `0 < α`, `λ ∈ [0, 1]`,
`c ≥ 0` and `x(c) > 0`), every Nash reversion profile of this form has `p_H = p_L = c`; and
`p_H = p_L = c` is one (for every `δ`). The book's claim concerns these Nash reversion
strategies; we prove it for all of them. -/
theorem exercise_12_D_5c {x : ℝ → ℝ} {pbar α lam δ : ℝ} (hx : IsBertrandDemand x pbar)
    (c : Ici (0 : ℝ)) (hxc : 0 < x c) (hα : 0 < α) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) :
    (∀ pH pL : Ici (0 : ℝ), IsRSNashReversion x α lam δ c pH pL →
      (pH : ℝ) = c ∧ (pL : ℝ) = c) ∧ IsRSNashReversion x α lam δ c c c := by
  have hδ1 : δ < 1 := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hxα := rbx_scaled_isBertrand hx hα
  have hc0 : (0 : ℝ) ≤ c := c.2
  constructor
  · intro pH pL h
    obtain ⟨-, -, hH, hL⟩ := h
    rw [rs_state_iff] at hH hL
    set V := rsValue x α lam δ c pH pL with hV
    set RH := ((pH : ℝ) - c) * x pH with hRH
    set RL := ((pL : ℝ) - c) * (α * x pL) with hRL
    have eH : ((pH : ℝ) - c) * (x pH / 2) = RH / 2 := by rw [hRH]; ring
    have eL : ((pL : ℝ) - c) * (α * x pL / 2) = RL / 2 := by rw [hRL]; ring
    rw [eH] at hH; rw [eL] at hL
    have hVe : V * (1 - δ) = lam * (RH / 2) + (1 - lam) * (RL / 2) := by
      rw [hV]; unfold rsValue; rw [eH, eL]; field_simp
    -- a state with positive profit gives `R ≤ R/2 + δV`
    have hposH : 0 < RH → RH ≤ RH / 2 + δ * V := by
      intro hpos
      have hpc : (c : ℝ) < pH := by
        by_contra hle; push Not at hle
        have : RH ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
        linarith
      exact rbx_le_of_below hx.cont hc0 hpc hH.1
    have hposL : 0 < RL → RL ≤ RL / 2 + δ * V := by
      intro hpos
      have hpc : (c : ℝ) < pL := by
        by_contra hle; push Not at hle
        have : RL ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hxα.nonneg _)
        linarith
      exact rbx_le_of_below hxα.cont hc0 hpc hL.1
    have hle : RH ≤ 0 ∧ RL ≤ 0 := by
      by_contra hn
      rw [not_and_or] at hn
      set M := max RH RL with hM
      have hMpos : 0 < M := by
        rcases hn with h | h
        · push Not at h; exact lt_of_lt_of_le h (le_max_left _ _)
        · push Not at h; exact lt_of_lt_of_le h (le_max_right _ _)
      have hVM : V * (1 - δ) ≤ M / 2 := by
        rw [hVe]
        have := mul_le_mul_of_nonneg_left (le_max_left RH RL) hlam0
        have := mul_le_mul_of_nonneg_left (le_max_right RH RL) (sub_nonneg.2 hlam1)
        nlinarith
      have hMle : M ≤ M / 2 + δ * V := by
        rcases le_total RL RH with h | h
        · rw [hM, max_eq_left h] at hMpos ⊢; exact hposH hMpos
        · rw [hM, max_eq_right h] at hMpos ⊢; exact hposL hMpos
      have h3 : M / 2 * (1 - δ) ≤ δ * (V * (1 - δ)) := by nlinarith
      have h4 : M / 2 * (1 - δ) ≤ δ * (M / 2) := h3.trans (mul_le_mul_of_nonneg_left hVM hδ0)
      nlinarith
    have hV0 : V ≤ 0 := by
      have : V * (1 - δ) ≤ 0 := by
        rw [hVe]; nlinarith [mul_nonneg hlam0 (show 0 ≤ -RH by linarith),
          mul_nonneg (sub_nonneg.2 hlam1) (show 0 ≤ -RL by linarith)]
      by_contra hpos; push Not at hpos
      nlinarith
    have hδV : δ * V ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ0 hV0
    have hRH0 : RH = 0 := by linarith [hH.2, hle.1]
    have hRL0 : RL = 0 := by linarith [hL.2, hle.2]
    have hVz : δ * V = 0 := by
      have : V * (1 - δ) = 0 := by rw [hVe, hRH0, hRL0]; ring
      have : V = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · linarith
      rw [this, mul_zero]
    refine ⟨rbx_price_eq_c hx c pH hxc hRH0 fun a ha hap => ?_,
      rbx_price_eq_c hxα c pL (by simpa using mul_pos hα hxc) hRL0 fun a ha hap => ?_⟩
    · have := hH.1 a ha hap; rw [hRH0, hVz] at this; linarith
    · have := hL.1 a ha hap; rw [hRL0, hVz] at this; linarith
  · refine ⟨bertrandStage_nash hx c (by simp), bertrandStage_nash hxα c (by simp), ?_, ?_⟩
    · intro j a ha
      have h1 := bertrandStage_nash (ι := Fin 2) hx c (by simp) j a
      have hV : rsValue x α lam δ c c c = 0 := by simp [rsValue]
      rw [hV, mul_zero, add_zero]
      exact h1
    · intro j a ha
      have h1 := bertrandStage_nash (ι := Fin 2) hxα c (by simp) j a
      have hV : rsValue x α lam δ c c c = 0 := by simp [rsValue]
      rw [hV, mul_zero, add_zero]
      exact h1

/-- **Exercise 12.D.5, instance.** Linear demand `max{0, 10 − p}`, `c = 1` (`pᵐ = 11/2`),
`λ = α = 1/2`, so `δ̂ = 4/7`: at `δ = 4/7` the monopoly price is sustained in both states; at
`δ = 1/2` it is not sustained in the high state, and the highest sustainable `p_H` (with
`p_L = 11/2`) lies strictly between `1` and `11/2`; at `δ = 1/4` both prices must equal `1`. -/
theorem exercise_12_D_5_instance :
    IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (4 / 7) cexC1 ⟨11 / 2, by norm_num⟩
      ⟨11 / 2, by norm_num⟩ ∧
    ¬ IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (1 / 2) cexC1 ⟨11 / 2, by norm_num⟩
      ⟨11 / 2, by norm_num⟩ ∧
    (∃ ph : Ici (0 : ℝ), (1 : ℝ) < ph ∧ (ph : ℝ) < 11 / 2 ∧
      IsGreatest {q : Ici (0 : ℝ) | IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (1 / 2)
        cexC1 q ⟨11 / 2, by norm_num⟩} ph) ∧
    ∀ pH pL : Ici (0 : ℝ), IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (1 / 4) cexC1 pH pL →
      (pH : ℝ) = 1 ∧ (pL : ℝ) = 1 := by
  obtain ⟨m1, s1, x1⟩ := rbx_lin_facts (c := 1) (by norm_num)
  norm_num at m1 s1 x1
  have hm : ∀ a : ℝ, 0 ≤ a → (a - (cexC1 : ℝ)) * bcLinDemand 10 a ≤
      (((⟨11 / 2, by norm_num⟩ : Ici (0 : ℝ)) : ℝ) - cexC1) *
        bcLinDemand 10 ((⟨11 / 2, by norm_num⟩ : Ici (0 : ℝ)) : ℝ) := by
    intro a _; simp only [cexC1]; norm_num; exact m1 a
  have hpc : (cexC1 : ℝ) < ((⟨11 / 2, by norm_num⟩ : Ici (0 : ℝ)) : ℝ) := by
    simp only [cexC1]; norm_num
  have hb := exercise_12_D_5b (α := 1 / 2) (lam := 1 / 2) (bcLinDemand_isBertrand 10) cexC1
    ⟨11 / 2, by norm_num⟩ hpc x1 hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨exercise_12_D_5a (bcLinDemand_isBertrand 10) cexC1 _ hpc x1 hm (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hb.2.1 (1 / 2) (by norm_num) (by norm_num) _, ?_, fun pH pL h => ?_⟩
  · obtain ⟨ph, h1, h2, -, h4⟩ := hb.2.2 (by simpa [cexC1] using s1) (1 / 2) le_rfl
      (by norm_num)
    exact ⟨ph, by simpa [cexC1] using h1, by simpa using h2, h4⟩
  · have := (exercise_12_D_5c (bcLinDemand_isBertrand 10) cexC1
      (by simp [cexC1, bcLinDemand]) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).1 pH pL h
    simpa [cexC1] using this

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# One-stage entry and contestable markets

MWG, Section 12.E, pp. 409-411: footnote 24, the one-stage entry game, Example 12.E.4 and
footnotes 26-27.

* `footnote_12_24`: with strict (A1) and `p` strictly decreasing, Proposition 12.E.1 holds with
  `π_{J°−1} > K`, so `J* ≥ J° − 1` even if firms do not enter when indifferent.
* **The one-stage entry game with price competition** (p. 410). Potential firms `ι` (at least
  two) name prices simultaneously; a firm incurs the setup cost `K` only if it sells. As in
  footnote 26, the whole demand goes to one of the firms naming the lowest price, selected by a
  rule `w` (`IsLowestPriceRule`); firm `j` earns `(p_j − c)x(p_j) − K` if it is the selected firm
  and `x(p_j) > 0`, and `0` otherwise (`oneStageProfit`). `IsOneStageEq` is pure-strategy Nash
  equilibrium.
* `oneStagePrice` is `p* = min{p : (p − c)x(p) ≥ K}`; `example_12_E_4_set`: for `x(p) > 0` this
  is MWG's set `{p : p ≥ [K + cx(p)]/x(p)}`. `oneStagePrice_spec`: `c < p* < pᵐ`, `R(p*) = K`,
  `R < K` below `p*`, `R > K` on `(p*, pᵐ]`.
* `example_12_E_4`: under MWG's hypothesis `(p − c)x(p) > K` for some `p` and **single
  peakedness** (`R` strictly increasing on `[c, pᵐ]`; added, see below), for every rule `w` every
  equilibrium has the selected firm charging `p*` with positive sales, and every firm earns zero;
  `example_12_E_4_exists`: all firms charging `p*` is an equilibrium for every rule;
  `example_12_E_4_welfare`: welfare at `p*` strictly exceeds welfare at the monopoly price of
  Example 12.E.2.
* `example_12_E_4_counterexample` (correction): without single peakedness the claim fails: a
  Bertrand demand with a flat stretch of `R = K` has an equilibrium at a price above `p*`.
* `footnote_12_26`: with MWG's earlier equal-sharing rule (`bertrandSales`) the one-stage game
  has no pure-strategy equilibrium, so giving the demand to one firm is needed.
* `footnote_12_27`: the outcome solves the problem of a planner who controls outputs subject to
  nonnegative profit for every active firm: one firm producing the largest `Q` with
  `(P(Q) − c)Q ≥ K`.
-/

namespace MWG.MarketPower

open Set Function Filter Topology MWG.CompetitiveMarkets

/-! ### Footnote 24 -/

/-- **Footnote 24** (MWG, p. 409). Under the hypotheses of Proposition 12.E.1 with (A1) strict
(`J' < J → J'q_{J'} < Jq_J`) and `p` strictly decreasing (MWG's `p' < 0`), the inequality
(12.E.8) is strict and `π_{J°−1} > K`; hence `J* ≥ J° − 1` also when firms do not enter when
indifferent (equilibrium conditions `π_J ≥ K ≥ π_{J+1}`, footnote 22). -/
theorem footnote_12_24 {p c c' : ℝ → ℝ} {q : ℕ → ℝ} {K : ℝ} (hp : StrictAnti p)
    (hpc : Continuous p)
    (hc : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' x) (Ici 0) x) (hc' : MonotoneOn c' (Ici 0))
    (hq0 : ∀ J, 0 ≤ q J)
    (hA1 : ∀ J J' : ℕ, J' < J → J' * q J' < J * q J) (hA2 : ∀ J J' : ℕ, J' ≤ J → q J ≤ q J')
    (hA3 : ∀ J : ℕ, c' (q J) ≤ p (J * q J)) {Jo : ℕ} (hJo : 1 ≤ Jo)
    (hmax : ∀ J, 1 ≤ J → entryWelfare p c q K J ≤ entryWelfare p c q K Jo) :
    (2 ≤ Jo → K < p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1))) ∧
    ∀ J, 1 ≤ J → K ≤ p (J * q J) * q J - c (q J) →
      p ((J + 1 : ℕ) * q (J + 1)) * q (J + 1) - c (q (J + 1)) ≤ K → Jo - 1 ≤ J := by
  have hA1w : ∀ J J' : ℕ, J' ≤ J → J' * q J' ≤ J * q J := by
    intro J J' h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact (hA1 J J' h').le
  have hanti := exercise_12_E_2 hp.antitone hc hc' hq0 hA1w hA2 hA3
  have key : 2 ≤ Jo → K < p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1)) := by
    intro h2
    set J' := Jo - 1 with hJ'
    have hJo' : Jo = J' + 1 := by omega
    have hW := hmax J' (by omega)
    unfold entryWelfare at hW
    set Q := (Jo : ℝ) * q Jo with hQ
    set Q' := (J' : ℝ) * q J' with hQ'
    have hQQ : Q' < Q := hA1 Jo J' (by omega)
    have hint : (∫ s in (0 : ℝ)..Q, p s) - ∫ s in (0 : ℝ)..Q', p s = ∫ s in Q'..Q, p s :=
      intervalIntegral.integral_interval_sub_left (hpc.intervalIntegrable _ _)
        (hpc.intervalIntegrable _ _)
    have hbound : (∫ s in Q'..Q, p s) < p Q' * (Q - Q') := by
      have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hQQ
        hpc.continuousOn (continuousOn_const (c := p Q'))
        (fun s hs => (hp hs.1).le) ⟨Q, ⟨hQQ.le, le_rfl⟩, hp hQQ⟩
      simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
    have htan := foc_le_tangent_convex hc hc' (hq0 J') (hq0 Jo)
    have hA3' := hA3 J'
    have hA2' : q Jo ≤ q J' := hA2 Jo J' (by omega)
    have hJ'cast : (Jo : ℝ) = J' + 1 := by rw [hJo']; push_cast; ring
    have e : q J' + Q' - Q = Jo * (q J' - q Jo) := by
      rw [hQ, hQ', hJ'cast]; ring
    have hJo0 : (0 : ℝ) ≤ Jo := Nat.cast_nonneg _
    have hfinal : 0 ≤ (p Q' - c' (q J')) * (Jo * (q J' - q Jo)) :=
      mul_nonneg (by linarith) (mul_nonneg hJo0 (by linarith))
    have step1 : K ≤ (∫ s in Q'..Q, p s) - Jo * c (q Jo) + J' * c (q J') := by
      rw [← hint]; rw [hJ'cast] at hW ⊢; linarith
    rw [hJ'cast] at hfinal step1 e
    have e2 : p Q' * (q J' + Q' - Q) = p Q' * ((J' + 1) * (q J' - q Jo)) := by rw [e]
    have h4 := mul_le_mul_of_nonneg_left htan (show (0 : ℝ) ≤ J' + 1 by positivity)
    linarith
  refine ⟨key, fun J _ _ hJ2 => ?_⟩
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Jo := by omega
  have := hanti (show J + 1 ≤ Jo - 1 by omega)
  simp only at this
  linarith [key h2]

/-- **Footnote 24, instance.** The linear Cournot model of Example 12.E.1 (`a = 3`, `b = 1`,
`c = 0`, so `p(Q) = 3 − Q`, `q_J = 3/(J + 1)`) satisfies strict (A1), (A2), (A3) with `p`
strictly decreasing. -/
theorem footnote_12_24_instance :
    StrictAnti (fun s : ℝ => 3 - s) ∧
    (∀ J J' : ℕ, J' < J → (J' : ℝ) * (3 / (J' + 1)) < J * (3 / (J + 1))) ∧
    (∀ J J' : ℕ, J' ≤ J → (3 : ℝ) / (J + 1) ≤ 3 / (J' + 1)) ∧
    (∀ J : ℕ, (0 : ℝ) ≤ 3 - J * (3 / (J + 1))) := by
  refine ⟨fun a b h => by linarith, fun J J' h => ?_, fun J J' h => ?_, fun J => ?_⟩
  · have : (J' : ℝ) < J := by exact_mod_cast h
    rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have : (J' : ℝ) ≤ J := by exact_mod_cast h
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  · have : (J : ℝ) * (3 / (J + 1)) ≤ 3 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-! ### The one-stage entry game with price competition -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rule selecting, at every price profile, one of the firms naming the lowest price
(footnote 26: the whole demand may go to one firm when several name the same price). -/
def IsLowestPriceRule (w : (ι → ℝ) → ι) : Prop := ∀ (p : ι → ℝ) (k : ι), p (w p) ≤ p k

/-- Firm `j`'s profit in the one-stage entry game (MWG, p. 410): the selected lowest-price firm
sells `x(p_j)` and, if this is positive, pays `K + cx(p_j)`; every other firm sells nothing and
pays nothing. -/
noncomputable def oneStageProfit (x : ℝ → ℝ) (c K : ℝ) (w : (ι → ℝ) → ι) (p : ι → ℝ)
    (j : ι) : ℝ :=
  if j = w p ∧ 0 < x (p j) then (p j - c) * x (p j) - K else 0

/-- Pure-strategy Nash equilibrium of the one-stage entry game. -/
def IsOneStageEq (x : ℝ → ℝ) (c K : ℝ) (w : (ι → ℝ) → ι) (p : ι → ℝ) : Prop :=
  ∀ j a, oneStageProfit x c K w (update p j a) j ≤ oneStageProfit x c K w p j

/-- The price `p* = min{p : (p − c)x(p) ≥ K}` of Example 12.E.4. -/
noncomputable def oneStagePrice (x : ℝ → ℝ) (c K : ℝ) : ℝ := sInf {p | K ≤ (p - c) * x p}

omit [Fintype ι] [DecidableEq ι] in
/-- A lowest-price rule exists (choose a minimizer). -/
theorem exists_lowestPriceRule [Finite ι] [Nonempty ι] :
    ∃ w : (ι → ℝ) → ι, IsLowestPriceRule w :=
  ⟨fun p => Classical.choose (Finite.exists_min p),
    fun p => Classical.choose_spec (Finite.exists_min p)⟩

/-- **Example 12.E.4: the set defining `p*`** (MWG, p. 410). For `x(p) > 0`,
`p ≥ [K + cx(p)]/x(p)` iff `(p − c)x(p) ≥ K`. -/
theorem example_12_E_4_set {x : ℝ → ℝ} {c K p : ℝ} (hxp : 0 < x p) :
    (K + c * x p) / x p ≤ p ↔ K ≤ (p - c) * x p := by
  rw [div_le_iff₀ hxp]; constructor <;> intro h <;> nlinarith

/-- **The price `p*`** (MWG, p. 410). Let demand be Bertrand, `c ≥ 0`, `K > 0`, and let
`(p − c)x(p) > K` at some `pᵐ > c` (MWG's hypothesis), with `R(p) = (p − c)x(p)` strictly
increasing on `[c, pᵐ]`. Then `p* = min{p : R(p) ≥ K}` exists, `c < p* < pᵐ`, `R(p*) = K`,
`R(a) < K` for `a < p*`, and `R(a) > K` for `p* < a ≤ pᵐ`. -/
theorem oneStagePrice_spec {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) :
    c < oneStagePrice x c K ∧ oneStagePrice x c K < pm ∧
    (oneStagePrice x c K - c) * x (oneStagePrice x c K) = K ∧
    (∀ a, a < oneStagePrice x c K → (a - c) * x a < K) ∧
    (∀ a, oneStagePrice x c K < a → a ≤ pm → K < (a - c) * x a) := by
  set S := {p : ℝ | K ≤ (p - c) * x p} with hS
  have hf : Continuous fun p : ℝ => (p - c) * x p :=
    (continuous_id.sub continuous_const).mul hx.cont
  have hgt : ∀ p ∈ S, c < p := by
    intro p hp
    by_contra hle; push Not at hle
    have : (p - c) * x p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg p)
    change K ≤ (p - c) * x p at hp
    linarith
  have hne : S.Nonempty := ⟨pm, hpm.le⟩
  have hbdd : BddBelow S := ⟨c, fun p hp => (hgt p hp).le⟩
  have hclosed : IsClosed S := isClosed_le continuous_const hf
  have hmem : oneStagePrice x c K ∈ S := hclosed.csInf_mem hne hbdd
  have hpmc : c < pm := hgt pm hpm.le
  have hle : oneStagePrice x c K ≤ pm := csInf_le hbdd hpm.le
  have hbelow : ∀ a, a < oneStagePrice x c K → (a - c) * x a < K := by
    intro a ha
    by_contra hge; push Not at hge
    exact absurd (csInf_le hbdd hge) (not_le.2 ha)
  have hc1 := hgt _ hmem
  have heq : (oneStagePrice x c K - c) * x (oneStagePrice x c K) = K := by
    refine le_antisymm ?_ hmem
    exact rbx_le_of_below hx.cont hc hc1 fun a _ ha => (hbelow a ha).le
  have hlt : oneStagePrice x c K < pm := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at heq; linarith
    · exact h
  refine ⟨hc1, hlt, heq, hbelow, fun a ha hapm => ?_⟩
  have := hsm ⟨hc1.le, hle⟩ ⟨by linarith, hapm⟩ ha
  simp only at this
  linarith

omit [Fintype ι] in
/-- A firm naming a price strictly below all others is selected. -/
theorem lowestRule_update_lt {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) {p : ι → ℝ} {k : ι}
    {a : ℝ} (h : ∀ l, l ≠ k → a < p l) : w (update p k a) = k := by
  by_contra hne
  have h1 := hw (update p k a) k
  rw [update_self, update_of_ne hne] at h1
  linarith [h _ hne]

omit [Fintype ι] in
/-- A firm naming a price above someone else's is not selected. -/
theorem lowestRule_update_gt {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) {p : ι → ℝ} {k l : ι}
    (hlk : l ≠ k) {a : ℝ} (h : p l < a) : w (update p k a) ≠ k := by
  intro heq
  have h1 := hw (update p k a) l
  rw [heq, update_self, update_of_ne hlk] at h1
  linarith

omit [Fintype ι] in
/-- The profit of a firm selected with a positive demand. -/
theorem oneStageProfit_of_win {x : ℝ → ℝ} {c K : ℝ} {w : (ι → ℝ) → ι} {p : ι → ℝ} {j : ι}
    (hj : j = w p) (hx : 0 < x (p j)) : oneStageProfit x c K w p j = (p j - c) * x (p j) - K := by
  unfold oneStageProfit
  split_ifs with h
  · rfl
  · exact absurd ⟨hj, hx⟩ h

omit [Fintype ι] in
theorem oneStageProfit_of_lose {x : ℝ → ℝ} {c K : ℝ} {w : (ι → ℝ) → ι} {p : ι → ℝ} {j : ι}
    (hj : j ≠ w p) : oneStageProfit x c K w p j = 0 := by
  simp [oneStageProfit, hj]

omit [Fintype ι] in
/-- A firm earns at most `max(R(p_j) − K, 0)`. -/
theorem oneStageProfit_le {x : ℝ → ℝ} {c K : ℝ} (w : (ι → ℝ) → ι) (p : ι → ℝ) (j : ι)
    {B : ℝ} (hB : 0 ≤ B) (hR : 0 < x (p j) → (p j - c) * x (p j) - K ≤ B) :
    oneStageProfit x c K w p j ≤ B := by
  unfold oneStageProfit
  split_ifs with h
  · exact hR h.2
  · exact hB

/-- **Example 12.E.4** (MWG, pp. 410-411), with single peakedness added. Let demand be Bertrand,
`c ≥ 0`, `K > 0`, `(pᵐ − c)x(pᵐ) > K` with `R` strictly increasing on `[c, pᵐ]`, and at least two
potential firms. For every lowest-price rule, in every equilibrium the selected firm charges
`p* = min{p : R(p) ≥ K}` and sells `x(p*) > 0` (all sales occur at `p*`), and every firm earns
zero. -/
theorem example_12_E_4 {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) (h2 : 2 ≤ Fintype.card ι)
    {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) {p : ι → ℝ} (hp : IsOneStageEq x c K w p) :
    p (w p) = oneStagePrice x c K ∧ 0 < x (oneStagePrice x c K) ∧
      ∀ j, oneStageProfit x c K w p j = 0 := by
  obtain ⟨hc1, hlt, heq, hbelow, habove⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K with hps
  set j0 := w p with hj0
  set m := p j0 with hm
  have hxps : 0 < x ps := by
    rcases (hx.nonneg ps).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at heq; linarith
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j0
  -- every firm earns at least `0` (it can name `p̄`, where demand is zero)
  have hnn : ∀ j, 0 ≤ oneStageProfit x c K w p j := by
    intro j
    refine le_trans ?_ (hp j pbar)
    unfold oneStageProfit
    rw [update_self, hx.zero pbar le_rfl]
    simp
  -- a positive-profit undercut by `k`
  have hundercut : ∀ a, a < m → K < (a - c) * x a → False := by
    intro a ham hRa
    have hxa : 0 < x a := by
      rcases (hx.nonneg a).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hRa; linarith
    have hlow : ∀ l, l ≠ k → a < p l := fun l _ => lt_of_lt_of_le ham (hw p l)
    have hwin := lowestRule_update_lt hw hlow
    have h1 := hp k a
    rw [oneStageProfit_of_win hwin.symm (by rw [update_self]; exact hxa), update_self,
      oneStageProfit_of_lose hk] at h1
    linarith
  have hmle : m ≤ ps := by
    by_contra hgt; push Not at hgt
    set a := (ps + min m pm) / 2 with ha
    have h1 : ps < min m pm := lt_min hgt hlt
    exact hundercut a (by linarith [min_le_left m pm]) (habove a (by linarith)
      (by linarith [min_le_right m pm]))
  have hmge : ps ≤ m := by
    by_contra hlt'; push Not at hlt'
    have hxm : 0 < x m := lt_trans hxps (hx.strictAnti m ps hlt' hxps)
    have := hnn j0
    rw [oneStageProfit_of_win rfl hxm] at this
    linarith [hbelow m hlt']
  have hmps : m = ps := le_antisymm hmle hmge
  refine ⟨hmps, hxps, fun j => ?_⟩
  by_cases hj : j = j0
  · rw [hj, oneStageProfit_of_win rfl (by change 0 < x m; rw [hmps]; exact hxps)]
    change (m - c) * x m - K = 0
    rw [hmps, heq, sub_self]
  · exact oneStageProfit_of_lose hj

/-- **Example 12.E.4, existence** (MWG, p. 411). Under the hypotheses of `example_12_E_4`, all
firms naming `p*` is an equilibrium for every lowest-price rule. -/
theorem example_12_E_4_exists {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) (h2 : 2 ≤ Fintype.card ι)
    {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) :
    IsOneStageEq x c K w (fun _ : ι => oneStagePrice x c K) := by
  obtain ⟨_, _, heq, hbelow, _⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K with hps
  have hzero : ∀ j, oneStageProfit x c K w (fun _ : ι => ps) j = 0 := by
    intro j
    unfold oneStageProfit
    split_ifs
    · rw [heq, sub_self]
    · rfl
  intro j a
  rw [hzero]
  obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
  unfold oneStageProfit
  split_ifs with hsel
  · rw [update_self] at hsel ⊢
    rcases lt_trichotomy a ps with h | h | h
    · linarith [hbelow a h]
    · rw [h, heq, sub_self]
    · exact absurd hsel.1.symm (lowestRule_update_gt (p := fun _ : ι => ps) hw hl h)
  · exact le_rfl

/-- Aggregate surplus when one firm sells `x(p)` at the price `p` and pays `K`: consumer surplus
`∫_p^{p̄} x` plus profit `(p − c)x(p) − K`. -/
noncomputable def oneStageWelfare (x : ℝ → ℝ) (pbar c K p : ℝ) : ℝ :=
  (∫ s in p..pbar, x s) + (p - c) * x p - K

/-- **Example 12.E.4, welfare** (MWG, p. 411). The one-stage outcome (one firm at `p*`) is
strictly better than the two-stage outcome of Example 12.E.2 (one firm at the monopoly price
`pᵐ`). -/
theorem example_12_E_4_welfare {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) :
    oneStageWelfare x pbar c K pm < oneStageWelfare x pbar c K (oneStagePrice x c K) := by
  obtain ⟨hc1, hlt, _, _, _⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K
  have hxpm : 0 < x pm := by
    rcases (hx.nonneg pm).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpm; linarith
  have hxps : x pm < x ps := hx.strictAnti ps pm hlt hxpm
  have hadd : (∫ s in ps..pm, x s) + (∫ s in pm..pbar, x s) = ∫ s in ps..pbar, x s :=
    intervalIntegral.integral_add_adjacent_intervals (hx.cont.intervalIntegrable _ _)
      (hx.cont.intervalIntegrable _ _)
  have hint : (pm - ps) * x pm ≤ ∫ s in ps..pm, x s := by
    have := intervalIntegral.integral_mono_on hlt.le
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := x pm))
      (hx.cont.intervalIntegrable _ _) (fun s hs => by
        rcases eq_or_lt_of_le hs.2 with h | h
        · rw [h]
        · exact (hx.strictAnti s pm h hxpm).le)
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
  unfold oneStageWelfare
  rw [← hadd]
  nlinarith [mul_pos (sub_pos.2 hc1) (sub_pos.2 hxps)]

/-- **Example 12.E.4, instance** (MWG, p. 410). Demand `max{0, 10 − p}`, `c = 1`, `K = 8`:
`R(11/2) = 81/4 > 8`, `R` is strictly increasing on `[1, 11/2]`, and `p* = 2`. -/
theorem example_12_E_4_instance :
    (8 : ℝ) < (11 / 2 - 1) * bcLinDemand 10 (11 / 2) ∧
    StrictMonoOn (fun p => (p - 1) * bcLinDemand 10 p) (Icc 1 (11 / 2)) ∧
    oneStagePrice (bcLinDemand 10) 1 8 = 2 := by
  obtain ⟨_, s1, _⟩ := rbx_lin_facts (c := 1) (by norm_num)
  norm_num at s1
  refine ⟨by norm_num [bcLinDemand], s1, ?_⟩
  refine IsLeast.csInf_eq ⟨by norm_num [bcLinDemand], fun p hp => ?_⟩
  change (8 : ℝ) ≤ (p - 1) * bcLinDemand 10 p at hp
  by_contra hlt; push Not at hlt
  simp only [bcLinDemand] at hp
  rw [max_eq_right (by linarith)] at hp
  nlinarith

/-! ### Example 12.E.4 without single peakedness: a counterexample -/

/-- A Bertrand demand (with `c = 1`, `K = 1`) whose profit `R(p) = (p − 1)x(p)` equals `K` on the
whole interval `[2, 3]`: `x(p) = 3 − p` for `p ≤ 2`, `1/(p − 1)` on `[2, 3]`, `(7 − p)/8` on
`[3, 7]` and `0` above. `R(4) = 9/8 > K`. -/
noncomputable def osCexDemand (p : ℝ) : ℝ :=
  if p ≤ 2 then 3 - p else if p ≤ 3 then 1 / max (p - 1) 1 else if p ≤ 7 then (7 - p) / 8 else 0

theorem osCexDemand_mid {p : ℝ} (h1 : ¬ p ≤ 2) (h2 : p ≤ 3) : osCexDemand p = 1 / (p - 1) := by
  simp only [osCexDemand, h1, h2, ite_false, ite_true]
  rw [max_eq_left (by linarith)]

theorem osCexDemand_isBertrand : IsBertrandDemand osCexDemand 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold osCexDemand
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact continuous_const.div ((continuous_id.sub continuous_const).max continuous_const)
          fun p => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
      · refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
        intro p hp; rw [hp]; norm_num
      · intro p hp; rw [hp]; norm_num
    · intro p hp; rw [hp]; norm_num
  · intro p; unfold osCexDemand
    split_ifs
    · linarith
    · positivity
    · exact div_nonneg (by linarith) (by norm_num)
    · exact le_rfl
  · intro p p' hpp' hpos
    by_cases h1 : p' ≤ 2
    · have : p ≤ 2 := by linarith
      simp only [osCexDemand, h1, this, ite_true]; linarith
    by_cases h2 : p' ≤ 3
    · rw [osCexDemand_mid h1 h2]
      by_cases h3 : p ≤ 2
      · simp only [osCexDemand, h3, ite_true]
        rw [div_lt_iff₀ (by linarith)]; nlinarith
      · rw [osCexDemand_mid h3 (by linarith)]
        exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
    by_cases h4 : p' ≤ 7
    · have hx' : osCexDemand p' = (7 - p') / 8 := by simp [osCexDemand, h1, h2, h4]
      rw [hx']
      by_cases h3 : p ≤ 2
      · simp only [osCexDemand, h3, ite_true]; linarith
      by_cases h5 : p ≤ 3
      · rw [osCexDemand_mid h3 h5, lt_div_iff₀ (by linarith)]; nlinarith
      · have hx : osCexDemand p = (7 - p) / 8 := by
          simp [osCexDemand, h3, h5, show p ≤ 7 by linarith]
        rw [hx]; linarith
    · have : osCexDemand p' = 0 := by simp [osCexDemand, h1, h2, h4]
      rw [this] at hpos; exact absurd hpos (lt_irrefl 0)
  · intro p hp; unfold osCexDemand
    split_ifs <;> linarith

/-- **Example 12.E.4 is false without single peakedness** (MWG, p. 410; correction). With the
demand `osCexDemand`, `c = 1`, `K = 1`: MWG's hypothesis holds (`(4 − 1)x(4) = 9/8 > K`) and
`p* = 2`, yet for every lowest-price rule all firms naming `3` is an equilibrium, so sales take
place at `3 ≠ p*`. -/
theorem example_12_E_4_counterexample (h2 : 2 ≤ Fintype.card ι) {w : (ι → ℝ) → ι}
    (hw : IsLowestPriceRule w) :
    IsBertrandDemand osCexDemand 7 ∧ (1 : ℝ) < (4 - 1) * osCexDemand 4 ∧
    oneStagePrice osCexDemand 1 1 = 2 ∧
    IsOneStageEq osCexDemand 1 1 w (fun _ : ι => 3) ∧
      (fun _ : ι => (3 : ℝ)) (w fun _ => 3) ≠ 2 := by
  have hR : ∀ p : ℝ, p ≤ 3 → (p - 1) * osCexDemand p ≤ 1 := by
    intro p hp
    by_cases h1 : p ≤ 2
    · simp only [osCexDemand, h1, ite_true]; nlinarith [sq_nonneg (p - 2)]
    · rw [osCexDemand_mid h1 hp]
      rw [mul_one_div, div_self (by linarith)]
  have h3 : (3 - 1) * osCexDemand 3 = 1 := by
    rw [osCexDemand_mid (by norm_num) le_rfl]; norm_num
  refine ⟨osCexDemand_isBertrand, by norm_num [osCexDemand], ?_, ?_, by norm_num⟩
  · refine IsLeast.csInf_eq ⟨by norm_num [osCexDemand], fun p hp => ?_⟩
    change (1 : ℝ) ≤ (p - 1) * osCexDemand p at hp
    by_contra hlt; push Not at hlt
    simp only [osCexDemand, hlt.le, ite_true] at hp
    nlinarith [sq_nonneg (p - 2)]
  · have hzero : ∀ j, oneStageProfit osCexDemand 1 1 w (fun _ : ι => 3) j = 0 := by
      intro j
      unfold oneStageProfit
      split_ifs
      · rw [h3, sub_self]
      · rfl
    intro j a
    rw [hzero]
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
    unfold oneStageProfit
    split_ifs with hsel
    · rw [update_self] at hsel ⊢
      rcases le_or_gt a 3 with h | h
      · linarith [hR a h]
      · exact absurd hsel.1.symm (lowestRule_update_gt (p := fun _ : ι => (3 : ℝ)) hw hl h)
    · exact le_rfl

/-! ### Footnote 26: no equilibrium under equal sharing -/

/-- Firm `j`'s profit in the one-stage game when the lowest-price firms share demand equally
(`bertrandSales`, the rule of Section 12.C): `(p_j − c)x_j − K` if it sells, `0` otherwise. -/
noncomputable def shareProfit (x : ℝ → ℝ) (c K : ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  if 0 < bertrandSales x p j then (p j - c) * bertrandSales x p j - K else 0

/-- Pure-strategy Nash equilibrium of the one-stage game with equal sharing. -/
def IsShareEq (x : ℝ → ℝ) (c K : ℝ) (p : ι → ℝ) : Prop :=
  ∀ j a, shareProfit x c K (update p j a) j ≤ shareProfit x c K p j

omit [Fintype ι] in
theorem shareProfit_of_lowest {x : ℝ → ℝ} {c K a : ℝ} {p : ι → ℝ} {k : ι} [Fintype ι]
    (h : ∀ l, l ≠ k → a < p l) (hxa : 0 < x a) :
    shareProfit x c K (update p k a) k = (a - c) * x a - K := by
  have hs : bertrandSales x (update p k a) k = x a := by
    rw [bertrandSales_of_lt (fun l hl => by simp [update_of_ne hl, h l hl])]
    simp
  unfold shareProfit
  rw [hs, update_self]
  simp [hxa]

omit [Fintype ι] [DecidableEq ι] in
theorem shareProfit_of_gt {x : ℝ → ℝ} {c K : ℝ} {p : ι → ℝ} {j l : ι} [Fintype ι]
    (h : p l < p j) : shareProfit x c K p j = 0 := by
  unfold shareProfit
  rw [bertrandSales_of_gt h]
  simp

/-- **Footnote 26** (MWG, p. 411). Under the hypotheses of `example_12_E_4`, if the firms naming
the lowest price share demand equally (the division used before), the one-stage entry game has
no pure-strategy equilibrium: giving the whole demand to one firm is needed for the equilibrium
of Example 12.E.4. -/
theorem footnote_12_26 {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) (h2 : 2 ≤ Fintype.card ι)
    (p : ι → ℝ) : ¬ IsShareEq x c K p := by
  intro hp
  obtain ⟨hc1, hlt, heq, hbelow, habove⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K with hps
  have hpos : ∀ a, c < a → K < (a - c) * x a → 0 < x a := by
    intro a _ hRa
    rcases (hx.nonneg a).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hRa; linarith
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨j0, hj0⟩ := Finite.exists_min p
  set m := p j0 with hm
  -- every firm earns at least `0`
  have hnn : ∀ j, 0 ≤ shareProfit x c K p j := by
    intro j
    refine le_trans (le_of_eq ?_) (hp j pbar)
    unfold shareProfit
    have h1 := bertrandSales_le hx.nonneg (update p j pbar) j
    rw [update_self, hx.zero pbar le_rfl] at h1
    split_ifs with hh
    · linarith
    · rfl
  -- a profitable undercut of all prices is impossible for a firm earning `0`
  have hund : ∀ k a, (∀ l, l ≠ k → a < p l) → c < a → K < (a - c) * x a →
      shareProfit x c K p k = 0 → False := by
    intro k a hlow hac hRa h0
    have := hp k a
    rw [shareProfit_of_lowest hlow (hpos a hac hRa), h0] at this
    linarith
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j0
  rcases (hx.nonneg m).lt_or_eq with hxm | hxm
  · -- positive demand at the lowest price
    have hsales : 0 < bertrandSales x p j0 := by
      unfold bertrandSales
      split_ifs with hh
      · exact div_pos hxm (by exact_mod_cast Finset.card_pos.2 ⟨j0, by simp⟩)
      · exact absurd hj0 hh
    have hprof : shareProfit x c K p j0 = (m - c) * bertrandSales x p j0 - K := by
      unfold shareProfit
      split_ifs
      rfl
    have hmc : c < m := by
      have := hnn j0
      rw [hprof] at this
      by_contra hle; push Not at hle
      nlinarith
    by_cases htie : ∃ l, l ≠ j0 ∧ p l = m
    · obtain ⟨l, hl, hlm⟩ := htie
      have hxc : 0 < x c := lt_trans hxm (hx.strictAnti c m hmc hxm)
      obtain ⟨a, hac, ham, hgain⟩ := bertrand_deviation hx hxc hmc
      have hhalf : bertrandSales x p j0 ≤ x m / 2 := by
        unfold bertrandSales
        have hcard : 2 ≤ (Finset.univ.filter fun k => p k = p j0).card :=
          Finset.one_lt_card.2 ⟨j0, by simp, l, by simp [hlm, hm], hl.symm⟩
        split_ifs with hh
        · exact div_le_div_of_nonneg_left (hx.nonneg _) (by norm_num) (by exact_mod_cast hcard)
        · exact absurd hj0 hh
      have hRa : 0 < (a - c) * x a := lt_of_le_of_lt
        (div_nonneg (mul_nonneg (by linarith) (hx.nonneg m)) (by norm_num)) hgain
      have hxa : 0 < x a := by
        rcases (hx.nonneg a).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hRa; linarith
      have := hp j0 a
      rw [shareProfit_of_lowest (fun l' _ => lt_of_lt_of_le ham (hj0 l')) hxa, hprof] at this
      have := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ m - c by linarith)
      nlinarith
    · push Not at htie
      have hlow : ∀ l, l ≠ j0 → m < p l := fun l hl =>
        lt_of_le_of_ne (hj0 l) (fun h => htie l hl h.symm)
      have hprof' : shareProfit x c K p j0 = (m - c) * x m - K := by
        rw [hprof, bertrandSales_of_lt hlow]
      have hmps : ps ≤ m := by
        by_contra h; push Not at h
        have := hnn j0; rw [hprof'] at this; linarith [hbelow m h]
      rcases eq_or_lt_of_le hmps with he | hgt
      · -- `m = p*`: the selected firm raises its price towards the second-lowest price
        obtain ⟨k₂, hk₂, hmin⟩ := Finset.exists_min_image (Finset.univ.erase j0) p
          ⟨k, by simp [hk]⟩
        have hm₂ : m < p k₂ := hlow k₂ (Finset.ne_of_mem_erase hk₂)
        set a := (ps + min (p k₂) pm) / 2 with ha
        have hmin' : ps < min (p k₂) pm := lt_min (by rw [he]; exact hm₂) hlt
        have hRa := habove a (by linarith) (by linarith [min_le_right (p k₂) pm])
        have hlow' : ∀ l, l ≠ j0 → a < p l := fun l hl =>
          lt_of_lt_of_le (by linarith [min_le_left (p k₂) pm])
            (hmin l (Finset.mem_erase.2 ⟨hl, Finset.mem_univ l⟩))
        have := hp j0 a
        rw [shareProfit_of_lowest hlow' (hpos a (by linarith) hRa), hprof', ← he, heq] at this
        linarith
      · -- `m > p*`: another firm undercuts profitably
        set a := (ps + min m pm) / 2 with ha
        have hmin' : ps < min m pm := lt_min hgt hlt
        have hRa := habove a (by linarith) (by linarith [min_le_right m pm])
        refine hund k a (fun l hl => lt_of_lt_of_le (by linarith [min_le_left m pm]) (hj0 l))
          (by linarith) hRa (shareProfit_of_gt (l := j0) (hlow k hk))
  · -- zero demand at the lowest price: nobody sells, and an undercut to `(p* + pᵐ)/2` pays
    set a := (ps + pm) / 2 with ha
    have hRa := habove a (by linarith) (by linarith)
    have hxa := hpos a (by linarith) hRa
    have ham : a < m := by
      by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with h | h
      · rw [← h, ← hxm] at hxa; exact lt_irrefl 0 hxa
      · have := hx.strictAnti m a h hxa; rw [← hxm] at this; linarith [hx.nonneg a]
    have h0 : shareProfit x c K p j0 = 0 := by
      unfold shareProfit
      have h1 := bertrandSales_le hx.nonneg p j0
      rw [← hm, ← hxm] at h1
      split_ifs with hh
      · linarith
      · rfl
    exact hund j0 a (fun l _ => lt_of_lt_of_le ham (hj0 l)) (by linarith) hRa h0

/-! ### Footnote 27: the planner's problem -/

/-- **Footnote 27** (MWG, p. 411). A planner chooses outputs `y_j ≥ 0` for `n` firms, subject to
nonnegative profit `P(Q)y_j ≥ cy_j + K` for every active firm (`y_j > 0`), `Q = ∑ y_j`, to
maximize aggregate surplus `∫₀^Q P − cQ − K·#{active firms}`. If `Q*` is the largest `Q ≥ 0`
with `(P(Q) − c)Q ≥ K` (`P` nonincreasing and continuous, `K > 0`), no feasible plan beats one
firm producing `Q*`, which is feasible. In Example 12.E.4, `Q* = x(p*)`: the one-stage
equilibrium outcome (`footnote_12_27_instance`). -/
theorem footnote_12_27 {P : ℝ → ℝ} {c K Qs : ℝ} (hP : Antitone P) (hPc : Continuous P)
    (hK : 0 < K) (hQs : IsGreatest {Q | 0 ≤ Q ∧ K ≤ (P Q - c) * Q} Qs) {n : ℕ}
    (y : Fin n → ℝ) (hy0 : ∀ j, 0 ≤ y j)
    (hfeas : ∀ j, 0 < y j → c * y j + K ≤ P (∑ k, y k) * y j) :
    (∫ s in (0 : ℝ)..∑ k, y k, P s) - c * ∑ k, y k - K * ∑ k, (if 0 < y k then (1 : ℝ) else 0)
      ≤ (∫ s in (0 : ℝ)..Qs, P s) - c * Qs - K ∧ c * Qs + K ≤ P Qs * Qs := by
  obtain ⟨⟨hQs0, hQsK⟩, hQsmax⟩ := hQs
  refine ⟨?_, by linarith⟩
  set Q := ∑ k, y k with hQ
  set N := ∑ k, (if 0 < y k then (1 : ℝ) else 0) with hN
  have hPQs : c < P Qs := by
    by_contra hle; push Not at hle
    nlinarith
  -- `∫_a^{Qs} P ≥ P(Qs)(Qs − a)` for `0 ≤ a ≤ Qs`
  have hint : ∀ a, a ≤ Qs → (∫ s in (0 : ℝ)..a, P s) + P Qs * (Qs - a) ≤
      ∫ s in (0 : ℝ)..Qs, P s := by
    intro a ha
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hPc.intervalIntegrable (μ := MeasureTheory.volume) 0 a) (hPc.intervalIntegrable a Qs)
    have hm := intervalIntegral.integral_mono_on ha
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := P Qs))
      (hPc.intervalIntegrable _ _) (fun s hs => hP hs.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    linarith
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
  have hsum : c * Q + K * N ≤ P Q * Q := by
    rw [hQ, hN, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · simpa using hfeas j h
    · have : y j = 0 := le_antisymm (not_lt.1 h) (hy0 j)
      simp [this]
  by_cases hact : ∃ j, 0 < y j
  · obtain ⟨j, hj⟩ := hact
    have hN1 : 1 ≤ N := by
      rw [hN]
      have := Finset.single_le_sum (f := fun k => if 0 < y k then (1 : ℝ) else 0)
        (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa [hj] using this
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => hy0 k
    have hQle : Q ≤ Qs := hQsmax ⟨hQ0, by nlinarith⟩
    have := hint Q hQle
    nlinarith
  · push Not at hact
    have hy : ∀ k, y k = 0 := fun k => le_antisymm (hact k) (hy0 k)
    have hQ0 : Q = 0 := by simp [hQ, hy]
    have hNz : N = 0 := by simp [hN, hy]
    rw [hQ0, hNz]
    have := hint 0 hQs0
    simp only [intervalIntegral.integral_same] at this ⊢
    nlinarith

/-- **Footnote 27, instance.** With `P(Q) = 10 − Q`, `c = 1`, `K = 8`, the largest `Q` with
`(P(Q) − c)Q ≥ K` is `8 = x(p*)`, the output of the one-stage equilibrium (`p* = 2`). -/
theorem footnote_12_27_instance :
    IsGreatest {Q : ℝ | 0 ≤ Q ∧ 8 ≤ (10 - Q - 1) * Q} 8 ∧
      bcLinDemand 10 (oneStagePrice (bcLinDemand 10) 1 8) = 8 := by
  refine ⟨⟨⟨by norm_num, by norm_num⟩, fun Q hQ => ?_⟩, ?_⟩
  · by_contra h; push Not at h; nlinarith [hQ.2]
  · rw [example_12_E_4_instance.2.2]; norm_num [bcLinDemand]

end MWG.MarketPower

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Entry exercises

MWG, Exercises 12.E.1 and 12.E.3-12.E.7, pp. 434-435.

* `exercise_12_E_1`: two-stage entry with price competition and firms of different efficiency
  (costs `1 < 2`, demand `max{0, 10 − p}`, entry cost `10`; in the duopoly subgame ties go to the
  low-cost firm, Exercise 12.C.4). For every selection of stage-2 equilibria, "only the
  inefficient firm enters" is an equilibrium of the entry stage: the most efficient firm need not
  be active.
* `exercise_12_E_3_cournot`, `exercise_12_E_3_bertrand`: the welfare loss of free entry relative
  to the optimal number of firms. In Example 12.E.1 it is
  `((a − c)²/2b)(1/(J* + 1)² − 1/(J° + 1)²) − (J° − J*)K` (`26K/25` when `J° = 2`) and tends to
  `0` as `K → 0`; in Example 12.E.2 it is `max{0, (a − c)²/8b − K}`, which tends to the monopoly
  deadweight loss `(a − c)²/8b > 0`.
* `exercise_12_E_4`: a perfect cartel after entry: welfare `S − JK` is maximized by one firm; free
  entry gives `J* = ⌊πᵐ/K⌋` firms, which dissipate the monopoly profit (`πᵐ − K < J*K ≤ πᵐ`), so
  welfare falls by `(J* − 1)K` to within `K` of the monopoly consumer surplus.
* `exercise_12_E_5`: the circular city with quadratic travel cost (Exercise 12.C.16): the
  welfare-maximizing number of firms, the same whether the planner controls entry and pricing or
  only entry, is at most the free-entry number; `exercise_12_E_5_instance`: `J° = 3 < 6 = J*`.
* `exercise_12_E_6_two_to_one`, `exercise_12_E_6_fewer`, `exercise_12_E_6_converse_fails`:
  Cournot entry with cost `cq`: every two-stage equilibrium number of firms is a one-stage one;
  not conversely; one-stage equilibria never have more firms.
* `exercise_12_E_7`: one-stage entry with announced prices and U-shaped average cost: if
  `x(c̄) = J*q̄` with `J* ≥ 2`, every equilibrium is perfectly competitive and efficient
  (`exercise_12_E_7_efficient`); `exercise_12_E_7_counterexample` (correction): with `J* = 1`
  the claim fails.

Departures are listed in the theorem docstrings and in `docs/corrections.md`.
-/

namespace MWG.MarketPower

open Set Function Filter Topology MWG.NoncooperativeGames MWG.SimultaneousMoveGames

/-! ### Exercise 12.E.1 -/

/-- Gross stage-2 profits in the entry game of `exercise_12_E_1` (demand `max{0, 10 − p}`, firm
`0` with cost `1`, firm `1` with cost `2`): a lone entrant earns its monopoly profit (`81/4`,
`16`); if both enter they play the duopoly equilibrium `p₁ = p₂ = pd` (ties to firm `0`), where
firm `0` earns `(pd − 1)x(pd)` and firm `1` nothing. -/
noncomputable def e1Profit (pd : ℝ) (j : Fin 2) (e : Fin 2 → Bool) : ℝ :=
  if e 0 = true ∧ e 1 = true then (if j = 0 then (pd - 1) * bcLinDemand 10 pd else 0)
  else if e j = true then (if j = 0 then 81 / 4 else 16) else 0

/-- Equilibrium of the entry stage given stage-2 profits `Pr` and entry cost `K`: entrants earn
at least `K`, and no outsider would earn more than `K` by entering. -/
def IsEntryStageEq (Pr : Fin 2 → (Fin 2 → Bool) → ℝ) (K : ℝ) (e : Fin 2 → Bool) : Prop :=
  ∀ j, (e j = true → K ≤ Pr j e) ∧ (e j = false → Pr j (update e j true) ≤ K)

/-- **Exercise 12.E.1** (MWG, p. 434). Two-stage entry with price competition; potential firm `0`
has unit cost `1`, firm `1` unit cost `2`; demand `max{0, 10 − p}`; entry cost `K = 10`; in the
duopoly ties go to the low-cost firm. Then: the duopoly subgame's equilibria are `p₀ = p₁ = pd`
with `pd ∈ [1, 2]` (Exercise 12.C.4); the monopoly profits are `81/4` (firm 0, at `11/2`) and
`16` (firm 1, at `6`); and for every such `pd`, "firm 1 enters, firm 0 stays out" is an
equilibrium of the entry stage. So the most efficient firm need not be active. -/
theorem exercise_12_E_1 :
    (∀ p₀ p₁, IsNashEquilibrium (bcGame ℝ (bcTieProfit₁ (bcLinDemand 10) 1)
      (bcTieProfit₂ (bcLinDemand 10) 2)) ![p₀, p₁] ↔ p₀ = p₁ ∧ 1 ≤ p₀ ∧ p₀ ≤ 2) ∧
    (∀ p, (p - 1) * bcLinDemand 10 p ≤ 81 / 4) ∧ (11 / 2 - 1) * bcLinDemand 10 (11 / 2) = 81 / 4 ∧
    (∀ p, (p - 2) * bcLinDemand 10 p ≤ 16) ∧ (6 - 2) * bcLinDemand 10 6 = 16 ∧
    ∀ pd : ℝ, 1 ≤ pd → pd ≤ 2 → IsEntryStageEq (e1Profit pd) 10 ![false, true] := by
  obtain ⟨m1, s1, _⟩ := rbx_lin_facts (c := 1) (by norm_num)
  obtain ⟨m2, -, _⟩ := rbx_lin_facts (c := 2) (by norm_num)
  norm_num at m1 s1 m2
  have hv1 : (11 / 2 - 1) * bcLinDemand 10 (11 / 2) = 81 / 4 := by norm_num [bcLinDemand]
  have hv2 : (6 - 2) * bcLinDemand 10 6 = 16 := by norm_num [bcLinDemand]
  refine ⟨(exercise_12_C_4a_tieRule (bcLinDemand_isBertrand 10) (by norm_num) (by norm_num)
    (by norm_num [bcLinDemand]) (show (2 : ℝ) < 11 / 2 by norm_num) s1).1,
    fun p => by have := m1 p; norm_num [bcLinDemand] at this ⊢; linarith, hv1,
    fun p => by have := m2 p; norm_num [bcLinDemand] at this ⊢; linarith, hv2,
    fun pd h1 h2 => ?_⟩
  intro j
  fin_cases j
  · refine ⟨fun h => by simp at h, fun _ => ?_⟩
    have hupd : update ![false, true] (0 : Fin 2) true = ![true, true] := by
      funext k; fin_cases k <;> simp
    change e1Profit pd 0 (update ![false, true] (0 : Fin 2) true) ≤ 10
    rw [hupd]
    have h0 : e1Profit pd 0 ![true, true] = (pd - 1) * bcLinDemand 10 pd := by
      simp [e1Profit]
    rw [h0]
    simp only [bcLinDemand]
    rw [max_eq_right (by linarith)]
    nlinarith
  · refine ⟨fun _ => ?_, fun h => by simp at h⟩
    norm_num [e1Profit]

/-! ### Exercise 12.E.3 -/

/-- **Exercise 12.E.3, the Cournot model of Example 12.E.1** (MWG, p. 434). With
`W(J) = ((a − c)²/b)(J² + 2J)/(2(J + 1)²) − JK`, the welfare loss of `J*` firms relative to `J°`
firms is `((a − c)²/2b)(1/(J* + 1)² − 1/(J° + 1)²) − (J° − J*)K`; it is nonnegative when `J°`
maximizes welfare; when `J° = 2` (i.e. `(a − c)²/b = 27K`, so `J* = 4`) it equals `26K/25`; and
it tends to `0` as `K → 0`. -/
theorem exercise_12_E_3_cournot {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ K (J Jo : ℕ), entryWelfare (fun s => a - b * s) (fun q => c * q)
        (fun J => (a - c) / (b * (J + 1))) K Jo -
      entryWelfare (fun s => a - b * s) (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K J =
      (a - c) ^ 2 / (2 * b) * (1 / ((J : ℝ) + 1) ^ 2 - 1 / ((Jo : ℝ) + 1) ^ 2) -
        ((Jo : ℝ) - J) * K) ∧
    (∀ K, 0 < K → (a - c) ^ 2 / b = 27 * K →
      IsEntryEquilibrium (cournotEntryProfit a b c) K 4 ∧
      (∀ J : ℕ, entryWelfare (fun s => a - b * s) (fun q => c * q)
        (fun J => (a - c) / (b * (J + 1))) K J ≤ entryWelfare (fun s => a - b * s)
        (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K 2) ∧
      entryWelfare (fun s => a - b * s) (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K 2 -
        entryWelfare (fun s => a - b * s) (fun q => c * q)
          (fun J => (a - c) / (b * (J + 1))) K 4 = 26 * K / 25) ∧
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ K, 0 < K → K < δ → ∀ J,
      IsEntryEquilibrium (cournotEntryProfit a b c) K J → ∀ Jo : ℕ, 1 ≤ Jo →
        entryWelfare (fun s => a - b * s) (fun q => c * q)
            (fun J => (a - c) / (b * (J + 1))) K Jo -
          entryWelfare (fun s => a - b * s) (fun q => c * q)
            (fun J => (a - c) / (b * (J + 1))) K J < ε := by
  refine ⟨fun K J Jo => ?_, fun K hK hA => ?_, fun ε hε => ?_⟩
  · rw [entryWelfare_linear hb, entryWelfare_linear hb]
    field_simp
    ring
  · have h27 : (a - c) ^ 2 / b = ((2 : ℕ) + 1 : ℝ) ^ 3 * K := by rw [hA]; norm_num
    have h3 := example_12_E_3 hb hK 2 (by norm_num) h27
    refine ⟨h3.2.1 rfl, h3.1, ?_⟩
    rw [entryWelfare_linear hb, entryWelfare_linear hb, hA]
    norm_num
    ring
  · obtain ⟨δ, hδ, h⟩ := (exercise_12_F_3 hac hb).2.2 ε hε
    exact ⟨δ, hδ, fun K hK hKδ J hJ Jo hJo => (h K hK hKδ J hJ).2 Jo _ hJo⟩

/-- Output per firm with Bertrand competition after entry (Example 12.E.2): the monopoly output
`(a − c)/2b` with one firm, and an equal share of the competitive output `(a − c)/b` with
`J ≥ 2` firms. -/
noncomputable def bertrandEntryOutput (a b c : ℝ) (J : ℕ) : ℝ :=
  if J = 1 then (a - c) / (2 * b) else (a - c) / (b * J)

/-- **Exercise 12.E.3, the Bertrand model of Example 12.E.2** (MWG, p. 434). With linear demand
and Bertrand competition after entry, `W(1) = 3(a − c)²/8b − K` and `W(J) = (a − c)²/2b − JK`
for `J ≥ 2`. If `K ≤ πᵐ = (a − c)²/4b` the free-entry number is `J* = 1`; when also
`K ≤ (a − c)²/8b`, `J° = 2` is welfare-optimal and the loss is `(a − c)²/8b − K`, which tends to
the monopoly deadweight loss `(a − c)²/8b > 0` as `K → 0`: unlike Example 12.E.1, the loss does
not vanish. -/
theorem exercise_12_E_3_bertrand {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ K, entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 1 =
      3 * (a - c) ^ 2 / (8 * b) - K) ∧
    (∀ K (J : ℕ), 2 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K J =
        (a - c) ^ 2 / (2 * b) - J * K) ∧
    (∀ K, 0 < K → K ≤ (a - c) ^ 2 / (8 * b) →
      (∀ J : ℕ, 1 ≤ J →
        entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K J ≤
        entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 2) ∧
      entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 2 -
        entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 1 =
        (a - c) ^ 2 / (8 * b) - K) ∧
    Tendsto (fun K => (a - c) ^ 2 / (8 * b) - K) (𝓝[>] 0) (𝓝 ((a - c) ^ 2 / (8 * b))) ∧
    0 < (a - c) ^ 2 / (8 * b) := by
  have hW1 : ∀ K, entryWelfare (fun s => a - b * s) (fun q => c * q)
      (bertrandEntryOutput a b c) K 1 = 3 * (a - c) ^ 2 / (8 * b) - K := by
    intro K
    rw [entryWelfare_linear_general]
    simp only [bertrandEntryOutput, ite_true, Nat.cast_one]
    field_simp
    ring
  have hWJ : ∀ K (J : ℕ), 2 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K J =
        (a - c) ^ 2 / (2 * b) - J * K := by
    intro K J hJ
    rw [entryWelfare_linear_general]
    have hJ1 : J ≠ 1 := by omega
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    simp only [bertrandEntryOutput, hJ1, ite_false]
    field_simp
    ring
  have hpos : 0 < (a - c) ^ 2 / (8 * b) := by have := sub_pos.2 hac; positivity
  refine ⟨hW1, hWJ, fun K hK hKle => ⟨fun J hJ => ?_, ?_⟩, ?_, hpos⟩
  · rw [hWJ K 2 le_rfl]
    rcases eq_or_lt_of_le hJ with h | h
    · subst h; rw [hW1]
      have : (a - c) ^ 2 / (2 * b) = 3 * (a - c) ^ 2 / (8 * b) + (a - c) ^ 2 / (8 * b) := by
        field_simp; ring
      push_cast; linarith
    · rw [hWJ K J h]
      have : (2 : ℝ) ≤ J := by exact_mod_cast h
      push_cast; nlinarith
  · rw [hWJ K 2 le_rfl, hW1]
    push_cast
    field_simp
    ring
  · have := (tendsto_const_nhds (x := (a - c) ^ 2 / (8 * b))).sub
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    simpa using this

/-! ### Exercise 12.E.4 -/

/-- **Exercise 12.E.4** (MWG, p. 434). After entry the `J` firms (unit cost `c`) form a perfect
cartel, so the market outcome is the monopoly one whatever `J`: total surplus is `S − JK`, where
`S` is the monopoly consumer surplus plus the monopoly profit `πᵐ`, and each firm earns `πᵐ/J`.
* A planner who controls entry but not the cartel chooses `J° = 1`, the unique maximizer.
* With free entry (and `K ≤ πᵐ`), `J*` is an equilibrium number iff `J* = ⌊πᵐ/K⌋`.
* Entry costs then dissipate the monopoly profit, `πᵐ − K < J*K ≤ πᵐ`, so welfare falls by
  `(J* − 1)K` relative to `J° = 1`, to within `K` of the monopoly consumer surplus `S − πᵐ`. -/
theorem exercise_12_E_4 {S πm K : ℝ} (hK : 0 < K) (hπ : K ≤ πm) :
    (∀ J : ℕ, 1 ≤ J → S - J * K ≤ S - 1 * K ∧ (S - J * K = S - 1 * K → J = 1)) ∧
    (∀ J : ℕ, IsEntryEquilibrium (fun J : ℕ => πm / J) K J ↔ J = ⌊πm / K⌋₊) ∧
    (πm - K < ⌊πm / K⌋₊ * K ∧ (⌊πm / K⌋₊ : ℝ) * K ≤ πm) ∧
    (S - 1 * K) - (S - ⌊πm / K⌋₊ * K) = (⌊πm / K⌋₊ - 1) * K ∧
    S - πm ≤ S - ⌊πm / K⌋₊ * K ∧ S - ⌊πm / K⌋₊ * K < S - πm + K := by
  have hr : 0 ≤ πm / K := div_nonneg (by linarith) hK.le
  have hfl := Nat.floor_le hr
  have hfl2 := Nat.lt_floor_add_one (πm / K)
  have h1 : (⌊πm / K⌋₊ : ℝ) * K ≤ πm := by rwa [le_div_iff₀ hK] at hfl
  have h2 : πm < (⌊πm / K⌋₊ + 1) * K := by rwa [div_lt_iff₀ hK] at hfl2
  refine ⟨fun J hJ => ?_, fun J => ?_, ⟨by linarith, h1⟩, by ring, by linarith, by linarith⟩
  · have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    refine ⟨by nlinarith, fun h => ?_⟩
    have : (J : ℝ) = 1 := by
      have := mul_right_cancel₀ hK.ne' (show (J : ℝ) * K = 1 * K by linarith)
      exact this
    exact_mod_cast this
  · unfold IsEntryEquilibrium
    dsimp only
    rw [eq_comm, Nat.floor_eq_iff hr]
    constructor
    · rintro ⟨hJ, h1', h2'⟩
      have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
      push_cast at h2'
      rw [le_div_iff₀ hJ'] at h1'
      rw [div_lt_iff₀ (by positivity)] at h2'
      exact ⟨by rw [le_div_iff₀ hK]; linarith, by rw [div_lt_iff₀ hK]; linarith⟩
    · rintro ⟨h1', h2'⟩
      have hJ : 1 ≤ J := by
        by_contra h0; push Not at h0
        have : J = 0 := by omega
        rw [this] at h2'
        have : 1 ≤ πm / K := by rw [le_div_iff₀ hK]; linarith
        push_cast at h2'; linarith
      have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
      rw [le_div_iff₀ hK] at h1'
      rw [div_lt_iff₀ hK] at h2'
      refine ⟨hJ, by rw [le_div_iff₀ hJ']; linarith, ?_⟩
      push_cast
      rw [div_lt_iff₀ (by positivity)]; linarith

/-! ### Exercise 12.E.5 -/

/-- Total travel cost in the circular city (circumference `1`, `M` consumers, quadratic travel
cost `td²`) when `J` equally spaced firms each serve the consumers nearest to them: each of the
`2J` half-arcs of length `1/(2J)` contributes `M∫₀^{1/(2J)} tx² dx`. -/
noncomputable def circTravelCost (t M : ℝ) (J : ℕ) : ℝ :=
  2 * J * M * ∫ x in (0 : ℝ)..1 / (2 * J), t * x ^ 2

theorem circTravelCost_eq {t M : ℝ} {J : ℕ} (hJ : 1 ≤ J) :
    circTravelCost t M J = t * M / (12 * (J : ℝ) ^ 2) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold circTravelCost
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  field_simp
  ring

/-- Aggregate surplus in the circular city with `J` firms, valuation `v`, unit cost `c` and entry
cost `K`, when every consumer buys from the nearest firm: `M(v − c) − JK − tM/(12J²)` (prices are
transfers). -/
noncomputable def circWelfare (v c t M K : ℝ) (J : ℕ) : ℝ :=
  M * (v - c) - J * K - circTravelCost t M J

/-- **Exercise 12.E.5** (MWG, p. 434). Two-stage entry into the circular city of Exercise 12.C.16
(quadratic travel cost, `v` large): with `J` firms each earns `tM/J³` (`exercise_12_C_16`).
(a) A planner controlling entry and pricing has every consumer buy from the nearest firm and
maximizes `circWelfare`; (b) a planner controlling only entry faces the equilibrium prices
`c + t/J²`, which are equal, so consumers again buy from the nearest firm and welfare is again
`circWelfare`. Both choose `J°` maximizing `M(v − c) − JK − tM/(12J²)`. Every such `J°` is at most
the free-entry number `J*`: there is (weakly) excessive entry. -/
theorem exercise_12_E_5 {v c t M K : ℝ} (ht : 0 < t) (hM : 0 < M) (hK : 0 < K) {Js Jo : ℕ}
    (hJs : IsEntryEquilibrium (fun J : ℕ => t * M / (J : ℝ) ^ 3) K Js)
    (hmax : ∀ J : ℕ, 1 ≤ J → circWelfare v c t M K J ≤ circWelfare v c t M K Jo) :
    Jo ≤ Js := by
  obtain ⟨hJs1, -, hJs2⟩ := hJs
  have htM : 0 < t * M := mul_pos ht hM
  -- welfare strictly decreases from `J*` on
  have hstep : ∀ n : ℕ, Js ≤ n →
      circWelfare v c t M K (n + 1) < circWelfare v c t M K n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hJs1 hn
    have hlt : t * M < K * ((n : ℝ) + 1) ^ 3 := by
      have h := hJs2
      simp only at h
      push_cast at h
      rw [div_lt_iff₀ (by positivity)] at h
      have : ((Js : ℝ) + 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by
        have : (Js : ℝ) ≤ n := by exact_mod_cast hn
        gcongr
      nlinarith
    unfold circWelfare
    rw [circTravelCost_eq (by omega), circTravelCost_eq (by omega)]
    push_cast
    have hn0 : (0 : ℝ) < n := by linarith
    rw [← sub_pos]
    have key : M * (v - c) - n * K - t * M / (12 * (n : ℝ) ^ 2) -
        (M * (v - c) - (n + 1) * K - t * M / (12 * ((n : ℝ) + 1) ^ 2)) =
        (12 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 * K - t * M * (2 * n + 1)) /
          (12 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
      field_simp; ring
    rw [key]
    apply div_pos _ (by positivity)
    have h1 : t * M * (2 * n + 1) < K * ((n : ℝ) + 1) ^ 3 * (2 * n + 1) :=
      mul_lt_mul_of_pos_right hlt (by linarith)
    have h2 : ((n : ℝ) + 1) * (2 * n + 1) ≤ 12 * (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ K * ((n : ℝ) + 1) ^ 2 by positivity)]
  have hdec : ∀ k : ℕ, circWelfare v c t M K (Js + k + 1) < circWelfare v c t M K Js := by
    intro k
    induction k with
    | zero => simpa using hstep Js le_rfl
    | succ k ih =>
      have := hstep (Js + k + 1) (by omega)
      rw [show Js + (k + 1) + 1 = Js + k + 1 + 1 by ring]
      linarith
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ : ∃ k, Jo = Js + k + 1 := ⟨Jo - Js - 1, by omega⟩
  have := hdec k
  rw [← hk] at this
  linarith [hmax Js hJs1]

/-- **Exercise 12.E.5, instance** (MWG, p. 434). With `t = M = 1` and `K = 1/216`: the free-entry
number of firms is `J* = 6` (profit `1/J³`), while welfare is maximized at `J° = 3`. -/
theorem exercise_12_E_5_instance (v c : ℝ) :
    IsEntryEquilibrium (fun J : ℕ => 1 * 1 / (J : ℝ) ^ 3) (1 / 216) 6 ∧
    ∀ J : ℕ, 1 ≤ J → circWelfare v c 1 1 (1 / 216) J ≤ circWelfare v c 1 1 (1 / 216) 3 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, fun J hJ => ?_⟩
  unfold circWelfare
  rw [circTravelCost_eq hJ, circTravelCost_eq (by norm_num)]
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  rw [← sub_nonneg]
  have hnum : 0 ≤ ((J : ℝ) - 3) * ((J : ℝ) ^ 2 - 2 * J - 6) := by
    rcases le_or_gt J 3 with h | h
    · interval_cases J <;> norm_num
    · have : (4 : ℝ) ≤ J := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by nlinarith)
  have hpos : 0 ≤ ((J : ℝ) - 3) * ((J : ℝ) ^ 2 - 2 * J - 6) / (216 * (J : ℝ) ^ 2) :=
    div_nonneg hnum (by positivity)
  convert hpos using 1
  push_cast
  field_simp
  ring

/-! ### Exercise 12.E.6 -/

/-- **A one-stage Cournot entry equilibrium with `J` active firms** (MWG, p. 410 and
Exercise 12.E.6), cost `c(q) = cq` plus `K` for a firm producing a positive amount, and the
symmetric Cournot outputs `q_J` of the `J`-firm market: the `J` active firms produce `q_J` (a
best response among active firms) and earn at least `K` (so not producing does not pay), and no
inactive firm can earn a positive net profit by producing any `y ≥ 0` against them. The linear
case is `IsOneStageCournotEntry` (`CompetitiveLimitExercises`). -/
def IsOneStageCournotEntryGen (p : ℝ → ℝ) (c K : ℝ) (q : ℕ → ℝ) (J : ℕ) : Prop :=
  1 ≤ J ∧ K ≤ (p (J * q J) - c) * q J ∧ ∀ y, 0 ≤ y → (p (J * q J + y) - c) * y - K ≤ 0

/-- **Exercise 12.E.6, two-stage outcomes are one-stage outcomes** (MWG, p. 434). Let `p` be
nonincreasing, `q_J ≥ 0` the symmetric Cournot outputs (`q_{J+1}` a best response to `J` rivals
producing `q_{J+1}`), with business stealing `q_{J+1} ≤ q_J` (A2). If `J` firms is a two-stage
equilibrium (`π_J ≥ K > π_{J+1}`), it is a one-stage equilibrium: an entrant facing `J` firms
producing `q_J ≥ q_{J+1}` can earn at most `π_{J+1} < K`. -/
theorem exercise_12_E_6_two_to_one {p : ℝ → ℝ} {c K : ℝ} {q : ℕ → ℝ} (hp : Antitone p)
    (hA2 : ∀ J, q (J + 1) ≤ q J)
    (hBR : ∀ (J : ℕ) (y : ℝ), 0 ≤ y →
      (p (J * q (J + 1) + y) - c) * y ≤ (p ((J + 1 : ℕ) * q (J + 1)) - c) * q (J + 1))
    {J : ℕ} (hJ : IsEntryEquilibrium (fun J : ℕ => (p (J * q J) - c) * q J) K J) :
    IsOneStageCournotEntryGen p c K q J := by
  obtain ⟨h1, h2, h3⟩ := hJ
  refine ⟨h1, h2, fun y hy => ?_⟩
  have hmono : p (J * q J + y) ≤ p (J * q (J + 1) + y) :=
    hp (by have := hA2 J; have : (0 : ℝ) ≤ J := Nat.cast_nonneg J; nlinarith)
  have := hBR J y hy
  simp only at h3
  nlinarith [mul_le_mul_of_nonneg_right hmono hy]

/-- **Exercise 12.E.6, no more firms in the one-stage game** (MWG, p. 434). If `π_J` is
nonincreasing, a one-stage equilibrium never has more active firms than a two-stage
equilibrium. -/
theorem exercise_12_E_6_fewer {p : ℝ → ℝ} {c K : ℝ} {q : ℕ → ℝ}
    (hπ : Antitone fun J : ℕ => (p (J * q J) - c) * q J) {J Js : ℕ}
    (h1 : IsOneStageCournotEntryGen p c K q J)
    (h2 : IsEntryEquilibrium (fun J : ℕ => (p (J * q J) - c) * q J) K Js) : J ≤ Js := by
  by_contra hlt
  push Not at hlt
  have := hπ (show Js + 1 ≤ J by omega)
  simp only at this
  linarith [h1.2.1, h2.2.2]

/-- The linear Cournot model satisfies the hypotheses of `exercise_12_E_6_two_to_one`: with
`p(Q) = A − BQ` and `q_J = (A − c)/(B(J + 1))`, an entrant facing `J` firms producing `q_{J+1}`
earns at most `π_{J+1}` (the difference is `B(y − q_{J+1})²`), and `q_J` is decreasing; the
general one-stage notion is MWG's linear one. -/
theorem exercise_12_E_6_linear {A B c K : ℝ} (hB : 0 < B) :
    (∀ (J : ℕ) (y : ℝ), 0 ≤ y →
      (A - B * (J * ((A - c) / (B * ((J + 1 : ℕ) + 1))) + y) - c) * y ≤
        (A - B * ((J + 1 : ℕ) * ((A - c) / (B * ((J + 1 : ℕ) + 1)))) - c) *
          ((A - c) / (B * ((J + 1 : ℕ) + 1)))) ∧
    (c ≤ A → ∀ J : ℕ, (A - c) / (B * ((J + 1 : ℕ) + 1)) ≤ (A - c) / (B * (J + 1))) ∧
    (∀ J, IsOneStageCournotEntryGen (fun s => A - B * s) c K (fun J => (A - c) / (B * (J + 1))) J
      ↔ IsOneStageCournotEntry A B c K J) ∧
    (∀ J : ℕ, (A - B * (J * ((A - c) / (B * (J + 1)))) - c) * ((A - c) / (B * (J + 1))) =
      cournotEntryProfit A B c J) := by
  refine ⟨fun J y _ => ?_, fun hAc J => ?_, fun J => ?_, fun J => ?_⟩
  · set u := (A - c) / (B * ((J + 1 : ℕ) + 1)) with hu
    have key : A - c - B * (J * u) = 2 * B * u := by
      rw [hu]; push_cast; field_simp; ring
    have key2 : A - c - B * ((J + 1 : ℕ) * u) = B * u := by
      push_cast; linarith
    have hL : A - B * (J * u + y) - c = 2 * B * u - B * y := by linarith [key]
    have hR : A - B * ((J + 1 : ℕ) * u) - c = B * u := by linarith [key2]
    rw [hL, hR]
    nlinarith [mul_nonneg hB.le (sq_nonneg (y - u))]
  · push_cast
    exact div_le_div_of_nonneg_left (by linarith) (by positivity)
      (by nlinarith)
  · unfold IsOneStageCournotEntryGen IsOneStageCournotEntry
    have e : (A - B * (J * ((A - c) / (B * (J + 1)))) - c) * ((A - c) / (B * (J + 1))) =
        cournotEntryProfit A B c J := by
      unfold cournotEntryProfit; field_simp; ring
    simp only [e]
  · unfold cournotEntryProfit; field_simp; ring

/-- **Exercise 12.E.6, the converse fails** (MWG, p. 434). Linear demand `p(Q) = 6 − Q`, `c = 0`,
`K = 4`: one active firm is a one-stage equilibrium (`π₁ = 9 ∈ [K, 4K]`), but not a two-stage
equilibrium (`π₂ = 4 ≥ K`, so a second firm would enter); the two-stage equilibrium has two
firms. -/
theorem exercise_12_E_6_converse_fails :
    IsOneStageCournotEntry 6 1 0 4 1 ∧ ¬ IsEntryEquilibrium (cournotEntryProfit 6 1 0) 4 1 ∧
      IsEntryEquilibrium (cournotEntryProfit 6 1 0) 4 2 := by
  refine ⟨⟨le_rfl, by norm_num [cournotEntryProfit], fun y _ => ?_⟩, fun h => ?_,
    ⟨by norm_num, by norm_num [cournotEntryProfit], by norm_num [cournotEntryProfit]⟩⟩
  · norm_num; nlinarith [sq_nonneg (y - 3 / 2)]
  · have := h.2.2; norm_num [cournotEntryProfit] at this

/-! ### Exercise 12.E.7 -/

/-- **An equilibrium of the one-stage entry game with announced prices** (MWG, Exercise 12.E.7),
formalized as a sustainable configuration: inverse demand `P`, average cost `AC(y)` for output
`y > 0` (including setup costs); firms `j` produce `q_j ≥ 0` and all sales occur at the price `m`
with `P(∑ q_j) = m`; active firms cover their costs (`AC(q_j) ≤ m`); and no firm can profit by
announcing a lower price `p' < m` and serving any amount `y > 0` that consumers demand at `p'`
(`p' ≤ P(y)`), i.e. `p' ≤ AC(y)`. (Departure: an undercutting firm may serve part of the demand
it attracts; MWG does not specify how demand is rationed.) -/
def IsPriceEntryConfig {n : ℕ} (P AC : ℝ → ℝ) (m : ℝ) (q : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ P (∑ j, q j) = m ∧ (∀ j, 0 < q j → AC (q j) ≤ m) ∧
    ∀ p' y, p' < m → 0 < y → p' ≤ P y → p' ≤ AC y

/-- **Exercise 12.E.7** (MWG, pp. 434-435), for `J* ≥ 2`. Let `P` be strictly decreasing on
`[0, ∞)`, and let the average cost satisfy `AC(y) ≥ c̄` for `y > 0` with the minimum `c̄` reached
only at `q̄ > 0`. If `P(J*q̄) = c̄` (i.e. `x(c̄) = J*q̄`) with `J* ≥ 2`, then in every equilibrium
the price is `c̄`, every active firm produces `q̄`, and exactly `J*` firms are active: the
perfectly competitive outcome. -/
theorem exercise_12_E_7 {n : ℕ} {P AC : ℝ → ℝ} {cbar qbar m : ℝ} {Js : ℕ}
    (hP : StrictAntiOn P (Ici 0)) (hq : 0 < qbar) (hAC : ∀ y, 0 < y → cbar ≤ AC y)
    (hmin : AC qbar = cbar) (huniq : ∀ y, 0 < y → AC y = cbar → y = qbar) (hJs : 2 ≤ Js)
    (hclear : P (Js * qbar) = cbar) {q : Fin n → ℝ} (hq_eq : IsPriceEntryConfig P AC m q) :
    m = cbar ∧ (∀ j, 0 < q j → q j = qbar) ∧ ∑ j, q j = Js * qbar ∧
      ∑ j, (if 0 < q j then (1 : ℝ) else 0) = Js := by
  obtain ⟨hq0, hclr, hcov, hund⟩ := hq_eq
  have hJs' : (2 : ℝ) ≤ Js := by exact_mod_cast hJs
  have hQ0 : 0 ≤ ∑ j, q j := Finset.sum_nonneg fun j _ => hq0 j
  have hQs0 : (0 : ℝ) ≤ Js * qbar := by positivity
  have hPq : cbar < P qbar := by
    rw [← hclear]
    exact hP (mem_Ici.2 hq.le) (mem_Ici.2 hQs0) (by nlinarith)
  have hmle : m ≤ cbar := by
    by_contra hgt; push Not at hgt
    have hmin' : cbar < min m (P qbar) := lt_min hgt hPq
    have := hund ((cbar + min m (P qbar)) / 2) qbar (by linarith [min_le_left m (P qbar)]) hq
      (by linarith [min_le_right m (P qbar)])
    rw [hmin] at this
    linarith
  have hmge : cbar ≤ m := by
    by_contra hlt; push Not at hlt
    have hQ : Js * qbar < ∑ j, q j := by
      by_contra hle; push Not at hle
      have := hP.antitoneOn (mem_Ici.2 hQ0) (mem_Ici.2 hQs0) hle
      rw [hclr, hclear] at this; linarith
    obtain ⟨j, hj⟩ : ∃ j, 0 < q j := by
      by_contra hall; push Not at hall
      have : ∑ j, q j ≤ 0 := Finset.sum_nonpos fun j _ => hall j
      linarith
    linarith [hcov j hj, hAC (q j) hj]
  have hm : m = cbar := le_antisymm hmle hmge
  have hQ : ∑ j, q j = Js * qbar := by
    have := hclr.trans (hm.trans hclear.symm)
    exact hP.injOn (mem_Ici.2 hQ0) (mem_Ici.2 hQs0) this
  have hact : ∀ j, 0 < q j → q j = qbar := fun j hj =>
    huniq (q j) hj (le_antisymm (hm ▸ hcov j hj) (hAC (q j) hj))
  refine ⟨hm, hact, hQ, ?_⟩
  have hsplit : ∑ j, q j = (∑ j, (if 0 < q j then (1 : ℝ) else 0)) * qbar := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [hact j h, one_mul]
    · rw [zero_mul]; exact le_antisymm (not_lt.1 h) (hq0 j)
  rw [hQ] at hsplit
  exact (mul_right_cancel₀ hq.ne' hsplit).symm

/-- **Exercise 12.E.7, the competitive configuration is an equilibrium and efficient** (MWG,
p. 435). Under the hypotheses of `exercise_12_E_7` (any `J* ≥ 1`), `J*` firms producing `q̄` at
the price `c̄` form an equilibrium; and with `P` nonincreasing and continuous, no outputs
`y_1, …, y_n ≥ 0` (costs `y_j AC(y_j)` for active firms) give more aggregate surplus than
`∫₀^{J*q̄} P − c̄J*q̄`, which the competitive configuration attains: it is first-best efficient. -/
theorem exercise_12_E_7_efficient {P AC : ℝ → ℝ} {cbar qbar : ℝ} {Js : ℕ}
    (hPa : Antitone P) (hPc : Continuous P) (hq : 0 < qbar) (hAC : ∀ y, 0 < y → cbar ≤ AC y)
    (hmin : AC qbar = cbar) (hclear : P (Js * qbar) = cbar) :
    IsPriceEntryConfig P AC cbar (fun _ : Fin Js => qbar) ∧
    (∀ (n : ℕ) (y : Fin n → ℝ), (∀ j, 0 ≤ y j) →
      (∫ s in (0 : ℝ)..∑ j, y j, P s) - ∑ j, (if 0 < y j then y j * AC (y j) else 0) ≤
        (∫ s in (0 : ℝ)..Js * qbar, P s) - cbar * (Js * qbar)) ∧
    (∫ s in (0 : ℝ)..∑ _j : Fin Js, qbar, P s) -
        ∑ _j : Fin Js, (if 0 < qbar then qbar * AC qbar else 0) =
      (∫ s in (0 : ℝ)..Js * qbar, P s) - cbar * (Js * qbar) := by
  have hsum : ∑ _j : Fin Js, qbar = Js * qbar := by simp
  refine ⟨⟨fun _ => hq.le, by rw [hsum, hclear], fun _ _ => by rw [hmin],
    fun p' y hp' hy _ => le_trans hp'.le (hAC y hy)⟩, fun n y hy0 => ?_, ?_⟩
  · set Q := ∑ j, y j
    set Qs := (Js : ℝ) * qbar
    have hcost : cbar * Q ≤ ∑ j, (if 0 < y j then y j * AC (y j) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h
      · nlinarith [hAC (y j) h]
      · rw [le_antisymm (not_lt.1 h) (hy0 j), mul_zero]
    -- `∫₀^Q P − c̄Q ≤ ∫₀^{Qs} P − c̄Qs` since `P ≥ c̄` below `Qs` and `P ≤ c̄` above
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hPc.intervalIntegrable (μ := MeasureTheory.volume) 0 Qs) (hPc.intervalIntegrable Qs Q)
    have hmid : (∫ s in Qs..Q, P s) ≤ cbar * (Q - Qs) := by
      rcases le_total Qs Q with h | h
      · have := intervalIntegral.integral_mono_on h (hPc.intervalIntegrable _ _)
          (intervalIntegrable_const (μ := MeasureTheory.volume) (c := cbar))
          (fun s hs => by rw [← hclear]; exact hPa hs.1)
        simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
      · rw [intervalIntegral.integral_symm]
        have := intervalIntegral.integral_mono_on h
          (intervalIntegrable_const (μ := MeasureTheory.volume) (c := cbar))
          (hPc.intervalIntegrable _ _) (fun s hs => by rw [← hclear]; exact hPa hs.2)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at this
        linarith
    linarith
  · rw [hsum]
    simp [hq, hmin]
    ring

/-- **Exercise 12.E.7, instance** (`J* = 2`). `P(Q) = 4 − Q`, `AC(y) = y + 1/y` (setup cost `1`,
variable cost `y²`): `c̄ = 2` at `q̄ = 1`, uniquely, and `P(2·1) = 2`. -/
theorem exercise_12_E_7_instance :
    StrictAntiOn (fun Q : ℝ => 4 - Q) (Ici 0) ∧ (∀ y : ℝ, 0 < y → 2 ≤ y + 1 / y) ∧
    (1 : ℝ) + 1 / 1 = 2 ∧ (∀ y : ℝ, 0 < y → y + 1 / y = 2 → y = 1) ∧
    (4 : ℝ) - ((2 : ℕ) : ℝ) * 1 = 2 := by
  refine ⟨fun a _ b _ h => by linarith, fun y hy => ?_, by norm_num, fun y hy h => ?_,
    by norm_num⟩
  · rw [← sub_nonneg]
    have : y + 1 / y - 2 = (y - 1) ^ 2 / y := by field_simp; ring
    rw [this]; positivity
  · have : (y - 1) ^ 2 / y = 0 := by
      have e : y + 1 / y - 2 = (y - 1) ^ 2 / y := by field_simp; ring
      rw [← e, h, sub_self]
    rcases div_eq_zero_iff.1 this with h' | h'
    · nlinarith [pow_eq_zero_iff (n := 2) (a := y - 1) two_ne_zero |>.1 h']
    · linarith

/-- Average cost of the counterexample to Exercise 12.E.7 with `J* = 1`: `2 − y` up to `y = 1`
and `y` above (minimum `c̄ = 1`, reached only at `q̄ = 1`). -/
noncomputable def e7CexAC (y : ℝ) : ℝ := if y ≤ 1 then 2 - y else y

/-- **Exercise 12.E.7 fails for `J* = 1`** (MWG, p. 435; correction). With `P(Q) = 2 − Q` and
`AC = e7CexAC`, the hypotheses hold with `q̄ = 1`, `c̄ = 1`, `J* = 1` (`P(1) = 1`), yet one firm
producing `1/2` at the price `3/2` is an equilibrium: the price exceeds `c̄` and output falls
short of the efficient `1`. (For `J* ≥ 2` the claim holds: `exercise_12_E_7`.) -/
theorem exercise_12_E_7_counterexample :
    StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) ∧ (∀ y, 0 < y → 1 ≤ e7CexAC y) ∧
    e7CexAC 1 = 1 ∧ (∀ y, 0 < y → e7CexAC y = 1 → y = 1) ∧ (2 : ℝ) - ((1 : ℕ) : ℝ) * 1 = 1 ∧
    IsPriceEntryConfig (fun Q : ℝ => 2 - Q) e7CexAC (3 / 2) ![1 / 2] ∧ (3 / 2 : ℝ) ≠ 1 := by
  refine ⟨fun a _ b _ h => by linarith, fun y _ => ?_, by norm_num [e7CexAC], fun y _ h => ?_,
    by norm_num, ⟨fun j => ?_, by simp; norm_num, fun j _ => ?_, fun p' y hp' hy hpy => ?_⟩,
    by norm_num⟩
  · unfold e7CexAC; split_ifs with h <;> linarith
  · unfold e7CexAC at h; split_ifs at h with h' <;> linarith
  · fin_cases j; norm_num
  · fin_cases j; norm_num [e7CexAC]
  · unfold e7CexAC; split_ifs with h <;> linarith

end MWG.MarketPower

set_option linter.style.longLine false
#print axioms MWG.MarketPower.monopolyProfit
#print axioms MWG.MarketPower.IsMonopolyOptimum
#print axioms MWG.MarketPower.hasDerivWithinAt_monopolyProfit
#print axioms MWG.MarketPower.eq_12_B_3
#print axioms MWG.MarketPower.eq_12_B_4
#print axioms MWG.MarketPower.monopoly_price_gt_mc
#print axioms MWG.MarketPower.monopoly_quantity_lt
#print axioms MWG.MarketPower.footnote_12_5
#print axioms MWG.MarketPower.cexP
#print axioms MWG.MarketPower.cexC
#print axioms MWG.MarketPower.cexMC
#print axioms MWG.MarketPower.cexDP
#print axioms MWG.MarketPower.cexC_hasDerivAt
#print axioms MWG.MarketPower.cexP_hasDerivAt
#print axioms MWG.MarketPower.footnote_12_5_counterexample
#print axioms MWG.MarketPower.footnote_12_6
#print axioms MWG.MarketPower.footnote_12_6_not_concave
#print axioms MWG.MarketPower.deadweight_loss_pos
#print axioms MWG.MarketPower.flat_demand_no_distortion
#print axioms MWG.MarketPower.example_12_B_1
#print axioms MWG.MarketPower.perfect_discrimination
#print axioms MWG.MarketPower.perfect_discrimination_optimal
#print axioms MWG.MarketPower.priceElasticity
#print axioms MWG.MarketPower.priceElasticity_eq_demand
#print axioms MWG.MarketPower.exercise_12_B_1a
#print axioms MWG.MarketPower.exercise_12_B_1b
#print axioms MWG.MarketPower.ceProfit
#print axioms MWG.MarketPower.ceProfit_eq
#print axioms MWG.MarketPower.exercise_12_B_2a
#print axioms MWG.MarketPower.ceProfit_hasDerivAt
#print axioms MWG.MarketPower.exercise_12_B_2b
#print axioms MWG.MarketPower.exercise_12_B_2b_dwl
#print axioms MWG.MarketPower.implicit_slope
#print axioms MWG.MarketPower.exercise_12_B_3_cost
#print axioms MWG.MarketPower.exercise_12_B_3_demand
#print axioms MWG.MarketPower.exercise_12_B_4_cost
#print axioms MWG.MarketPower.exercise_12_B_4_param
#print axioms MWG.MarketPower.exercise_12_B_6
#print axioms MWG.MarketPower.groupBenefit
#print axioms MWG.MarketPower.widgetWelfare
#print axioms MWG.MarketPower.exercise_12_B_7a
#print axioms MWG.MarketPower.exercise_12_B_7b
#print axioms MWG.MarketPower.exercise_12_B_7c
#print axioms MWG.MarketPower.exercise_12_B_7d
#print axioms MWG.MarketPower.exercise_12_B_7d_one_served
#print axioms MWG.MarketPower.lbdProfit
#print axioms MWG.MarketPower.lbdWelfare
#print axioms MWG.MarketPower.exercise_12_B_8a
#print axioms MWG.MarketPower.exercise_12_B_8b
#print axioms MWG.MarketPower.exercise_12_B_8c
#print axioms MWG.MarketPower.exercise_12_B_9a
#print axioms MWG.MarketPower.exercise_12_B_9b
#print axioms MWG.MarketPower.exercise_12_B_9c
#print axioms MWG.MarketPower.exercise_12_B_10
#print axioms MWG.MarketPower.consumerSurplus_strictMono
#print axioms MWG.MarketPower.ceDWL
#print axioms MWG.MarketPower.ceDWLShape
#print axioms MWG.MarketPower.ceDWL_eq
#print axioms MWG.MarketPower.exercise_12_B_2c_derivation
#print axioms MWG.MarketPower.ceDWL_y_bounds
#print axioms MWG.MarketPower.ceDWL_rpow_eq
#print axioms MWG.MarketPower.ceDWL_exp_mul
#print axioms MWG.MarketPower.ceDWLShape_pos
#print axioms MWG.MarketPower.ceDWLShape_hasDerivAt
#print axioms MWG.MarketPower.ceDWLShape_strictAntiOn
#print axioms MWG.MarketPower.ceDWLShape_scaled_eq
#print axioms MWG.MarketPower.ceDWLShape_scaled_tendsto
#print axioms MWG.MarketPower.ceDWLShape_tendsto_atTop
#print axioms MWG.MarketPower.ceDWLShape_tendsto_one
#print axioms MWG.MarketPower.exercise_12_B_2c
#print axioms MWG.MarketPower.exercise_12_B_2c_eps2
#print axioms MWG.MarketPower.exercise_12_B_2c_eps3
#print axioms MWG.MarketPower.unitUtility
#print axioms MWG.MarketPower.unitMenu_highPrice
#print axioms MWG.MarketPower.unitMenu_core
#print axioms MWG.MarketPower.exercise_12_B_5a
#print axioms MWG.MarketPower.exercise_12_B_5a_instance
#print axioms MWG.MarketPower.IsResaleEquilibrium
#print axioms MWG.MarketPower.isResaleEquilibrium_iff
#print axioms MWG.MarketPower.exercise_12_B_5b
#print axioms MWG.MarketPower.exercise_12_B_5b_instance
#print axioms MWG.MarketPower.exercise_12_B_5b_needs_resale
#print axioms MWG.MarketPower.IsBertrandDemand
#print axioms MWG.MarketPower.IsBertrandDemand.mk
#print axioms MWG.MarketPower.IsBertrandDemand.cont
#print axioms MWG.MarketPower.IsBertrandDemand.nonneg
#print axioms MWG.MarketPower.IsBertrandDemand.strictAnti
#print axioms MWG.MarketPower.IsBertrandDemand.zero
#print axioms MWG.MarketPower.bertrandSales
#print axioms MWG.MarketPower.bertrandProfit
#print axioms MWG.MarketPower.bertrandGame
#print axioms MWG.MarketPower.bertrandSales_duopoly
#print axioms MWG.MarketPower.bertrandSales_nonneg
#print axioms MWG.MarketPower.bertrandSales_le
#print axioms MWG.MarketPower.bertrandSales_of_lt
#print axioms MWG.MarketPower.bertrandSales_of_gt
#print axioms MWG.MarketPower.bertrand_deviation
#print axioms MWG.MarketPower.bertrandProfit_le_zero
#print axioms MWG.MarketPower.bertrandProfit_nonneg
#print axioms MWG.MarketPower.exercise_12_C_1
#print axioms MWG.MarketPower.proposition_12_C_1
#print axioms MWG.MarketPower.gridPrice
#print axioms MWG.MarketPower.gridPrice_spec
#print axioms MWG.MarketPower.gridBertrandGame
#print axioms MWG.MarketPower.exercise_12_C_3a
#print axioms MWG.MarketPower.exercise_12_C_3b
#print axioms MWG.MarketPower.cournotProfit
#print axioms MWG.MarketPower.IsCournotNE
#print axioms MWG.MarketPower.sum_update_eq
#print axioms MWG.MarketPower.cournot_foc
#print axioms MWG.MarketPower.footnote_12_12
#print axioms MWG.MarketPower.eq_12_C_6
#print axioms MWG.MarketPower.eq_12_C_5
#print axioms MWG.MarketPower.eq_12_C_6_one
#print axioms MWG.MarketPower.strictAntiOn_of_deriv_neg'
#print axioms MWG.MarketPower.proposition_12_C_2
#print axioms MWG.MarketPower.cournot_competitive_limit
#print axioms MWG.MarketPower.example_12_C_1_br
#print axioms MWG.MarketPower.example_12_C_1
#print axioms MWG.MarketPower.example_12_C_1_joint
#print axioms MWG.MarketPower.exercise_12_C_6
#print axioms MWG.MarketPower.exercise_12_C_7
#print axioms MWG.MarketPower.exercise_12_C_7_limits
#print axioms MWG.MarketPower.lcHat
#print axioms MWG.MarketPower.lcHat_spec
#print axioms MWG.MarketPower.linearCity_prefers
#print axioms MWG.MarketPower.lcDemand
#print axioms MWG.MarketPower.lcProfit
#print axioms MWG.MarketPower.lcProfit_mid
#print axioms MWG.MarketPower.lcProfit_low
#print axioms MWG.MarketPower.lcProfit_high
#print axioms MWG.MarketPower.lcBR_mid
#print axioms MWG.MarketPower.lcBR_high
#print axioms MWG.MarketPower.lcBR_low
#print axioms MWG.MarketPower.IsLCNash
#print axioms MWG.MarketPower.example_12_C_2
#print axioms MWG.MarketPower.stageU
#print axioms MWG.MarketPower.IsRepeatedSPNE
#print axioms MWG.MarketPower.osValue_eq_of_rec
#print axioms MWG.MarketPower.stageU_bound
#print axioms MWG.MarketPower.pathValue
#print axioms MWG.MarketPower.pathValue_summable
#print axioms MWG.MarketPower.pathValue_succ
#print axioms MWG.MarketPower.pathValue_abs_le
#print axioms MWG.MarketPower.pathValue_const
#print axioms MWG.MarketPower.pathHist
#print axioms MWG.MarketPower.pathHist_length
#print axioms MWG.MarketPower.not_pathHist_cons
#print axioms MWG.MarketPower.nashReversion
#print axioms MWG.MarketPower.osPlay_nashReversion_on
#print axioms MWG.MarketPower.osPlay_nashReversion_off
#print axioms MWG.MarketPower.IsStageNash
#print axioms MWG.MarketPower.nashReversionValue
#print axioms MWG.MarketPower.nashReversionValue_on
#print axioms MWG.MarketPower.nashReversionValue_off
#print axioms MWG.MarketPower.pathHist_succ_eq
#print axioms MWG.MarketPower.update_cons_off
#print axioms MWG.MarketPower.osValue_nashReversion
#print axioms MWG.MarketPower.nashReversion_spne_iff
#print axioms MWG.MarketPower.stage_nash_spne
#print axioms MWG.MarketPower.bestReplyValue
#print axioms MWG.MarketPower.le_bestReplyValue
#print axioms MWG.MarketPower.lemma_12_AA_1_if
#print axioms MWG.MarketPower.eq_12_AA_2
#print axioms MWG.MarketPower.eq_12_AA_3
#print axioms MWG.MarketPower.cexG0
#print axioms MWG.MarketPower.cexG1
#print axioms MWG.MarketPower.cexG
#print axioms MWG.MarketPower.cexG_bound
#print axioms MWG.MarketPower.cexG_unique_nash
#print axioms MWG.MarketPower.counterexample_12_AA
#print axioms MWG.MarketPower.proposition_12_AA_2_corrected
#print axioms MWG.MarketPower.proposition_12_AA_3
#print axioms MWG.MarketPower.exercise_12_AA_1_corrected
#print axioms MWG.MarketPower.exercise_12_AA_1_printed_condition
#print axioms MWG.MarketPower.minimaxValue
#print axioms MWG.MarketPower.bestReplyValue_ge
#print axioms MWG.MarketPower.minimax_le_nash
#print axioms MWG.MarketPower.minimax_le_spne_value
#print axioms MWG.MarketPower.schedK
#print axioms MWG.MarketPower.schedStep
#print axioms MWG.MarketPower.schedG
#print axioms MWG.MarketPower.schedIdx
#print axioms MWG.MarketPower.schedK_spec
#print axioms MWG.MarketPower.sched_invariant
#print axioms MWG.MarketPower.sched_lower
#print axioms MWG.MarketPower.schedCont
#print axioms MWG.MarketPower.schedCont_rec
#print axioms MWG.MarketPower.schedCont_close
#print axioms MWG.MarketPower.FolkState
#print axioms MWG.MarketPower.folkPresc
#print axioms MWG.MarketPower.folkTrans
#print axioms MWG.MarketPower.folkStateOf
#print axioms MWG.MarketPower.folkProfile
#print axioms MWG.MarketPower.osPlay_folkProfile
#print axioms MWG.MarketPower.folkTrans_conform
#print axioms MWG.MarketPower.folkTrans_deviate
#print axioms MWG.MarketPower.folkStateOf_le
#print axioms MWG.MarketPower.folkVal
#print axioms MWG.MarketPower.osValue_folkProfile
#print axioms MWG.MarketPower.folk_div_helper
#print axioms MWG.MarketPower.proposition_12_AA_5
#print axioms MWG.MarketPower.folk_theorem
#print axioms MWG.MarketPower.pdPay
#print axioms MWG.MarketPower.folk_theorem_instance
#print axioms MWG.MarketPower.scPresc
#print axioms MWG.MarketPower.scTrans
#print axioms MWG.MarketPower.scStateOf
#print axioms MWG.MarketPower.scProfile
#print axioms MWG.MarketPower.scVal
#print axioms MWG.MarketPower.scTrans_conform
#print axioms MWG.MarketPower.scTrans_deviate
#print axioms MWG.MarketPower.scProfile_spne
#print axioms MWG.MarketPower.stage_local_pos
#print axioms MWG.MarketPower.stage_local_neg
#print axioms MWG.MarketPower.bestReplyValue_update
#print axioms MWG.MarketPower.hasDerivAt_along
#print axioms MWG.MarketPower.L_apply_two
#print axioms MWG.MarketPower.LocalGameData
#print axioms MWG.MarketPower.LocalGameData.mk
#print axioms MWG.MarketPower.LocalGameData.L0
#print axioms MWG.MarketPower.LocalGameData.L1
#print axioms MWG.MarketPower.LocalGameData.deriv0
#print axioms MWG.MarketPower.LocalGameData.deriv1
#print axioms MWG.MarketPower.LocalGameData.own0
#print axioms MWG.MarketPower.LocalGameData.own1
#print axioms MWG.MarketPower.LocalGameData.cross0
#print axioms MWG.MarketPower.LocalGameData.cross1
#print axioms MWG.MarketPower.LocalGameData.env0
#print axioms MWG.MarketPower.LocalGameData.env1
#print axioms MWG.MarketPower.localGame_slopes
#print axioms MWG.MarketPower.bestReplyValue_nash
#print axioms MWG.MarketPower.proposition_12_AA_1
#print axioms MWG.MarketPower.proposition_12_AA_4
#print axioms MWG.MarketPower.locPhi
#print axioms MWG.MarketPower.locPsi
#print axioms MWG.MarketPower.locG
#print axioms MWG.MarketPower.locPhi_abs
#print axioms MWG.MarketPower.locPsi_nonneg
#print axioms MWG.MarketPower.locPsi_le
#print axioms MWG.MarketPower.locG_bound
#print axioms MWG.MarketPower.locG_nash
#print axioms MWG.MarketPower.locPhi_hasDerivAt
#print axioms MWG.MarketPower.locPsi_hasDerivAt
#print axioms MWG.MarketPower.locG_bestReply
#print axioms MWG.MarketPower.locG_data
#print axioms MWG.MarketPower.proposition_12_AA_1_instance
#print axioms MWG.MarketPower.proposition_12_AA_4_instance
#print axioms MWG.MarketPower.sclClamp
#print axioms MWG.MarketPower.sclRoot
#print axioms MWG.MarketPower.sclG
#print axioms MWG.MarketPower.sclClamp_abs
#print axioms MWG.MarketPower.sclClamp_of_abs_le
#print axioms MWG.MarketPower.sclClamp_eq_zero
#print axioms MWG.MarketPower.sclG_clamp
#print axioms MWG.MarketPower.sclClamp_zero
#print axioms MWG.MarketPower.sclRoot_nonneg
#print axioms MWG.MarketPower.sclRoot_zero
#print axioms MWG.MarketPower.sclRoot_sq
#print axioms MWG.MarketPower.sclRoot_le_one
#print axioms MWG.MarketPower.sclRoot_sq_ge
#print axioms MWG.MarketPower.sclRoot_sq_ge_four
#print axioms MWG.MarketPower.sclG_bound
#print axioms MWG.MarketPower.sclG_zero_update
#print axioms MWG.MarketPower.sclG_one_update
#print axioms MWG.MarketPower.sclG_zero_val
#print axioms MWG.MarketPower.sclG_br0
#print axioms MWG.MarketPower.sclG_br1
#print axioms MWG.MarketPower.sclG_nash
#print axioms MWG.MarketPower.sclG_nash_unique
#print axioms MWG.MarketPower.sclG_deriv0
#print axioms MWG.MarketPower.sclG_deriv1
#print axioms MWG.MarketPower.sclG_hypotheses
#print axioms MWG.MarketPower.proposition_12_AA_1_false
#print axioms MWG.MarketPower.sclG_spne_action_sq
#print axioms MWG.MarketPower.sclG_spne_value_nonneg
#print axioms MWG.MarketPower.proposition_12_AA_4_false
#print axioms MWG.MarketPower.counterexample_12_AA_1_4
#print axioms MWG.MarketPower.scl_own_partial_zero
#print axioms MWG.MarketPower.scl_hasDerivAt_squeeze
#print axioms MWG.MarketPower.scl_env_of_upper
#print axioms MWG.MarketPower.scl_upper_of_hasDerivAt
#print axioms MWG.MarketPower.sclLocalData
#print axioms MWG.MarketPower.proposition_12_AA_1_upper
#print axioms MWG.MarketPower.proposition_12_AA_4_upper
#print axioms MWG.MarketPower.scl_locG_upper
#print axioms MWG.MarketPower.scl_upper_instance_1
#print axioms MWG.MarketPower.scl_upper_instance_4
#print axioms MWG.MarketPower.cfG
#print axioms MWG.MarketPower.cfG_update_sum
#print axioms MWG.MarketPower.cfG_update_own
#print axioms MWG.MarketPower.example_12_AA_1
#print axioms MWG.MarketPower.example_12_AA_1_qbar
#print axioms MWG.MarketPower.pLin4
#print axioms MWG.MarketPower.example_12_AA_1_instance
#print axioms MWG.MarketPower.bertrandStage
#print axioms MWG.MarketPower.constPrice
#print axioms MWG.MarketPower.bertrandStage_bound
#print axioms MWG.MarketPower.bertrandStage_nash
#print axioms MWG.MarketPower.bertrandStage_update
#print axioms MWG.MarketPower.bertrand_nashReversion_iff
#print axioms MWG.MarketPower.proposition_12_D_1
#print axioms MWG.MarketPower.exercise_12_D_2_corrected
#print axioms MWG.MarketPower.proposition_12_D_2_part1_corrected
#print axioms MWG.MarketPower.cexDemand
#print axioms MWG.MarketPower.cexDemand_isBertrand
#print axioms MWG.MarketPower.cexC1
#print axioms MWG.MarketPower.cexP2
#print axioms MWG.MarketPower.proposition_12_D_2_counterexample
#print axioms MWG.MarketPower.osPath_succ'
#print axioms MWG.MarketPower.duopoly_profit_lt
#print axioms MWG.MarketPower.duopoly_profit_eq
#print axioms MWG.MarketPower.duopoly_profit_gt
#print axioms MWG.MarketPower.proposition_12_D_2_part2
#print axioms MWG.MarketPower.cournot_gain
#print axioms MWG.MarketPower.CournotNR
#print axioms MWG.MarketPower.exercise_12_D_3b_corrected
#print axioms MWG.MarketPower.exercise_12_D_3a
#print axioms MWG.MarketPower.exercise_12_D_3b_printed_false
#print axioms MWG.MarketPower.exercise_12_D_3b_threshold
#print axioms MWG.MarketPower.exercise_12_C_9c
#print axioms MWG.MarketPower.exercise_12_D_1a
#print axioms MWG.MarketPower.exercise_12_D_1b
#print axioms MWG.MarketPower.exercise_12_D_1c
#print axioms MWG.MarketPower.IsEntryEquilibrium
#print axioms MWG.MarketPower.entry_equilibrium_unique
#print axioms MWG.MarketPower.entry_equilibrium_exists
#print axioms MWG.MarketPower.entry_equilibrium_iff
#print axioms MWG.MarketPower.footnote_12_22
#print axioms MWG.MarketPower.cournotEntryProfit
#print axioms MWG.MarketPower.example_12_E_1
#print axioms MWG.MarketPower.example_12_E_1_number
#print axioms MWG.MarketPower.example_12_E_1_statics
#print axioms MWG.MarketPower.example_12_E_2
#print axioms MWG.MarketPower.entryWelfare
#print axioms MWG.MarketPower.entryWelfare_linear
#print axioms MWG.MarketPower.example_12_E_3_aux
#print axioms MWG.MarketPower.example_12_E_3
#print axioms MWG.MarketPower.exercise_12_E_2
#print axioms MWG.MarketPower.proposition_12_E_1
#print axioms MWG.MarketPower.eq_12_G_1
#print axioms MWG.MarketPower.figure_12_G_1
#print axioms MWG.MarketPower.eq_12_G_2
#print axioms MWG.MarketPower.cournot_two_costs
#print axioms MWG.MarketPower.linearCity_two_costs
#print axioms MWG.MarketPower.example_12_G_1
#print axioms MWG.MarketPower.exercise_12_G_1
#print axioms MWG.MarketPower.cbrProfit
#print axioms MWG.MarketPower.IsBROn
#print axioms MWG.MarketPower.cgProfit
#print axioms MWG.MarketPower.IsCournotGameNE
#print axioms MWG.MarketPower.IsCournotEqm
#print axioms MWG.MarketPower.cgProfit_update
#print axioms MWG.MarketPower.exercise_12_C_8a
#print axioms MWG.MarketPower.cbrDemandB
#print axioms MWG.MarketPower.exercise_12_C_8b
#print axioms MWG.MarketPower.cbr_convex_pair
#print axioms MWG.MarketPower.exercise_12_C_8c
#print axioms MWG.MarketPower.exercise_12_C_8c_monotone
#print axioms MWG.MarketPower.exercise_12_C_8c_jump
#print axioms MWG.MarketPower.exercise_12_C_8c_deriv
#print axioms MWG.MarketPower.exercise_12_C_8d_counterexample
#print axioms MWG.MarketPower.cbr_exists_Icc
#print axioms MWG.MarketPower.cbr_symmetric_fixed_point
#print axioms MWG.MarketPower.exercise_12_C_8d
#print axioms MWG.MarketPower.cbrSelLinear
#print axioms MWG.MarketPower.exercise_12_C_8c_instance
#print axioms MWG.MarketPower.exercise_12_C_8d_instance
#print axioms MWG.MarketPower.cbrDemandE
#print axioms MWG.MarketPower.cbrDemandE_br
#print axioms MWG.MarketPower.exercise_12_C_8e
#print axioms MWG.MarketPower.cbr_foc
#print axioms MWG.MarketPower.cournotEqm_foc
#print axioms MWG.MarketPower.exercise_12_C_8f
#print axioms MWG.MarketPower.exercise_12_C_8f_instance
#print axioms MWG.MarketPower.sizedDemand
#print axioms MWG.MarketPower.sizedDemand_strictAntiOn
#print axioms MWG.MarketPower.entryNetProfit
#print axioms MWG.MarketPower.IsCournotEntrySPNE
#print axioms MWG.MarketPower.BRDecreasing
#print axioms MWG.MarketPower.entry_incumbents_no_expand
#print axioms MWG.MarketPower.entry_step_ii
#print axioms MWG.MarketPower.entry_price_ge
#print axioms MWG.MarketPower.competitive_limit
#print axioms MWG.MarketPower.proposition_12_F_1
#print axioms MWG.MarketPower.footnote_12_29
#print axioms MWG.MarketPower.exercise_12_F_1_core
#print axioms MWG.MarketPower.sized_br_le
#print axioms MWG.MarketPower.exercise_12_F_1
#print axioms MWG.MarketPower.proposition_12_F_1_of_exercise_12_F_1
#print axioms MWG.MarketPower.gaussDemand
#print axioms MWG.MarketPower.gaussDemand'
#print axioms MWG.MarketPower.gaussDemand''
#print axioms MWG.MarketPower.gaussDemand_hasDerivAt
#print axioms MWG.MarketPower.gaussDemand'_hasDerivAt
#print axioms MWG.MarketPower.gaussDemand_bounds
#print axioms MWG.MarketPower.gaussDemand_model
#print axioms MWG.MarketPower.gaussFOC
#print axioms MWG.MarketPower.gauss_br_foc
#print axioms MWG.MarketPower.gaussFOC_anti
#print axioms MWG.MarketPower.gaussFOC_mono
#print axioms MWG.MarketPower.exercise_12_F_1_counterexample
#print axioms MWG.MarketPower.exercise_12_F_1_false
#print axioms MWG.MarketPower.linear_br_unique
#print axioms MWG.MarketPower.linear_brDecreasing
#print axioms MWG.MarketPower.proposition_12_F_1_instance
#print axioms MWG.MarketPower.footnote_12_29_instance
#print axioms MWG.MarketPower.exercise_12_F_1_instance
#print axioms MWG.MarketPower.entry_spne_instance
#print axioms MWG.MarketPower.exercise_12_F_2a
#print axioms MWG.MarketPower.fqJ
#print axioms MWG.MarketPower.linCS
#print axioms MWG.MarketPower.linCS_eq
#print axioms MWG.MarketPower.IsOneStageCournotEntry
#print axioms MWG.MarketPower.cournot_entry_profit_bounds
#print axioms MWG.MarketPower.exercise_12_F_2b
#print axioms MWG.MarketPower.exercise_12_F_2b_instance
#print axioms MWG.MarketPower.firstBestWelfare
#print axioms MWG.MarketPower.entryWelfare_linear_general
#print axioms MWG.MarketPower.exercise_12_F_3
#print axioms MWG.MarketPower.dpProfit
#print axioms MWG.MarketPower.IsDPBR
#print axioms MWG.MarketPower.exercise_12_F_4_br
#print axioms MWG.MarketPower.exercise_12_F_4_root
#print axioms MWG.MarketPower.exercise_12_F_4_no_br
#print axioms MWG.MarketPower.exercise_12_F_4_symmetric
#print axioms MWG.MarketPower.exercise_12_F_4_indeterminate
#print axioms MWG.MarketPower.appendixB_concave_increment
#print axioms MWG.MarketPower.appendixB_profit_strictConcave
#print axioms MWG.MarketPower.appendixB_br_antitone
#print axioms MWG.MarketPower.figure_12_BB_1
#print axioms MWG.MarketPower.figure_12_BB_2
#print axioms MWG.MarketPower.exercise_12_BB_1
#print axioms MWG.MarketPower.exercise_12_BB_1_instance
#print axioms MWG.MarketPower.edProfit
#print axioms MWG.MarketPower.edProfit_eq
#print axioms MWG.MarketPower.appendixB_quad_max
#print axioms MWG.MarketPower.appendixB_quad_max_Ici
#print axioms MWG.MarketPower.edKB
#print axioms MWG.MarketPower.edQI
#print axioms MWG.MarketPower.edQE
#print axioms MWG.MarketPower.edQM
#print axioms MWG.MarketPower.edProfE
#print axioms MWG.MarketPower.edKZ
#print axioms MWG.MarketPower.edKPi
#print axioms MWG.MarketPower.IsStage3Nash
#print axioms MWG.MarketPower.edKB_pos
#print axioms MWG.MarketPower.edQI_le
#print axioms MWG.MarketPower.edQI_le_kB
#print axioms MWG.MarketPower.edQI_nonneg
#print axioms MWG.MarketPower.edQI_of_le
#print axioms MWG.MarketPower.edProfE_eq
#print axioms MWG.MarketPower.figure_12_BB_2_linear
#print axioms MWG.MarketPower.figure_12_BB_3
#print axioms MWG.MarketPower.figure_12_BB_3_range
#print axioms MWG.MarketPower.figure_12_BB_4
#print axioms MWG.MarketPower.appendixB_stage3_noEntry
#print axioms MWG.MarketPower.figure_12_BB_1_linear
#print axioms MWG.MarketPower.appendixB_stage2
#print axioms MWG.MarketPower.edPayI
#print axioms MWG.MarketPower.EDEntryOptimal
#print axioms MWG.MarketPower.IsEDSPNE
#print axioms MWG.MarketPower.edBookRule
#print axioms MWG.MarketPower.edStayOutRule
#print axioms MWG.MarketPower.edBookRule_optimal
#print axioms MWG.MarketPower.edStayOutRule_optimal
#print axioms MWG.MarketPower.edPayI_true_eq
#print axioms MWG.MarketPower.edPayI_false_eq
#print axioms MWG.MarketPower.edPayI_true_le
#print axioms MWG.MarketPower.edPayI_false_le
#print axioms MWG.MarketPower.figure_12_BB_5
#print axioms MWG.MarketPower.figure_12_BB_6
#print axioms MWG.MarketPower.figure_12_BB_6_firstMover
#print axioms MWG.MarketPower.figure_12_BB_6_rightOfB
#print axioms MWG.MarketPower.appendixB_deter_region
#print axioms MWG.MarketPower.appendixB_linear_S_le_Z
#print axioms MWG.MarketPower.appendixB_deter_entry
#print axioms MWG.MarketPower.appendixB_deter_noEntry
#print axioms MWG.MarketPower.figure_12_BB_8
#print axioms MWG.MarketPower.figure_12_BB_7_deter
#print axioms MWG.MarketPower.appendixB_bookRule_no_spne
#print axioms MWG.MarketPower.figure_12_BB_7_accommodate
#print axioms MWG.MarketPower.edSurplus
#print axioms MWG.MarketPower.edSurplus_eq_integral
#print axioms MWG.MarketPower.appendixB_deterrence_raises_output
#print axioms MWG.MarketPower.exercise_12_BB_2
#print axioms MWG.MarketPower.appendixB_general_instance
#print axioms MWG.MarketPower.figure_12_BB_5_instance
#print axioms MWG.MarketPower.figure_12_BB_6_instance
#print axioms MWG.MarketPower.figure_12_BB_6_rightOfB_instance
#print axioms MWG.MarketPower.figure_12_BB_7_deter_instance
#print axioms MWG.MarketPower.figure_12_BB_7_accommodate_instance
#print axioms MWG.MarketPower.exercise_12_BB_2_instance
#print axioms MWG.MarketPower.bb3Cl
#print axioms MWG.MarketPower.bb3Cl_nonneg
#print axioms MWG.MarketPower.bb3Cl_le_one
#print axioms MWG.MarketPower.bb3Cl_mono
#print axioms MWG.MarketPower.bb3Cl_le_max
#print axioms MWG.MarketPower.bb3Cl_le_of_pos
#print axioms MWG.MarketPower.bb3Cl_lip
#print axioms MWG.MarketPower.bb3Cl_of_mem
#print axioms MWG.MarketPower.bb3D
#print axioms MWG.MarketPower.bb3ShareE
#print axioms MWG.MarketPower.bb3ShareE_nonneg
#print axioms MWG.MarketPower.bb3ShareE_le
#print axioms MWG.MarketPower.bb3D_nonneg
#print axioms MWG.MarketPower.bb3D_le
#print axioms MWG.MarketPower.bb3D_anti
#print axioms MWG.MarketPower.bb3D_lip
#print axioms MWG.MarketPower.bb3_coloc_zero
#print axioms MWG.MarketPower.bb3ProfitE2
#print axioms MWG.MarketPower.bb3ProfitI2
#print axioms MWG.MarketPower.IsBB3Coloc2Nash
#print axioms MWG.MarketPower.bb3ProfitE1
#print axioms MWG.MarketPower.bb3ProfitI1
#print axioms MWG.MarketPower.IsBB3Coloc1Nash
#print axioms MWG.MarketPower.bb3_shareE_profit_le
#print axioms MWG.MarketPower.bb3_I_term_le
#print axioms MWG.MarketPower.exercise_12_BB_3_coloc_two
#print axioms MWG.MarketPower.exercise_12_BB_3_coloc_one
#print axioms MWG.MarketPower.exercise_12_BB_3_monopoly_one
#print axioms MWG.MarketPower.exercise_12_BB_3_monopoly_two
#print axioms MWG.MarketPower.exercise_12_BB_3_duopoly
#print axioms MWG.MarketPower.bb3PayOne
#print axioms MWG.MarketPower.bb3PayTwo
#print axioms MWG.MarketPower.exercise_12_BB_3
#print axioms MWG.MarketPower.bb3_transport_one
#print axioms MWG.MarketPower.bb3_transport_two
#print axioms MWG.MarketPower.bb3Welfare
#print axioms MWG.MarketPower.exercise_12_BB_3_welfare
#print axioms MWG.MarketPower.exercise_12_BB_3_instance
#print axioms MWG.MarketPower.cournotGenProfit
#print axioms MWG.MarketPower.smallType_12_C_393
#print axioms MWG.MarketPower.smallType_12_C_393_unbounded
#print axioms MWG.MarketPower.smallType_12_C_393_linear
#print axioms MWG.MarketPower.IsCournotGenNE
#print axioms MWG.MarketPower.cnxP
#print axioms MWG.MarketPower.cnxC
#print axioms MWG.MarketPower.cnxP_rev
#print axioms MWG.MarketPower.cournotGenProfit_fin0
#print axioms MWG.MarketPower.cournotGenProfit_fin1
#print axioms MWG.MarketPower.smallType_12_C_393_nonexistence
#print axioms MWG.MarketPower.diffProducts_profitable
#print axioms MWG.MarketPower.diffProducts_br_above_cost
#print axioms MWG.MarketPower.diffProducts_eqm_above_cost
#print axioms MWG.MarketPower.diffProducts_instance
#print axioms MWG.MarketPower.footnote_12_13
#print axioms MWG.MarketPower.footnote_12_13_instance
#print axioms MWG.MarketPower.capSales
#print axioms MWG.MarketPower.capProfit
#print axioms MWG.MarketPower.IsCapNE
#print axioms MWG.MarketPower.IsCournotBRc
#print axioms MWG.MarketPower.capSales_lt
#print axioms MWG.MarketPower.capSales_gt
#print axioms MWG.MarketPower.capSales_eq
#print axioms MWG.MarketPower.capSales_nonneg
#print axioms MWG.MarketPower.cap_P_x
#print axioms MWG.MarketPower.cap_P_anti
#print axioms MWG.MarketPower.cap_P_concave
#print axioms MWG.MarketPower.cap_pi_three
#print axioms MWG.MarketPower.cap_pi_pos
#print axioms MWG.MarketPower.capacity_bertrand_not_eqm
#print axioms MWG.MarketPower.capacity_bertrand_not_eqm_three_quarters
#print axioms MWG.MarketPower.capacity_assured_sales
#print axioms MWG.MarketPower.cap_eqm_side
#print axioms MWG.MarketPower.exercise_12_C_11a
#print axioms MWG.MarketPower.cap_undercut
#print axioms MWG.MarketPower.capNE_eq
#print axioms MWG.MarketPower.capacity_unique
#print axioms MWG.MarketPower.cap_no_eqm_side
#print axioms MWG.MarketPower.exercise_12_C_11b
#print axioms MWG.MarketPower.capDemandEx
#print axioms MWG.MarketPower.capDemandEx_cont
#print axioms MWG.MarketPower.capDemandEx_nonneg
#print axioms MWG.MarketPower.capDemandEx_anti
#print axioms MWG.MarketPower.capDemandEx_concave
#print axioms MWG.MarketPower.capDemandEx_inv
#print axioms MWG.MarketPower.exercise_12_C_11a_instance
#print axioms MWG.MarketPower.exercise_12_C_11b_instance
#print axioms MWG.MarketPower.exercise_12_C_11b_counterexample_zero_capacity
#print axioms MWG.MarketPower.exercise_12_C_11b_counterexample_zero_br
#print axioms MWG.MarketPower.lcvShare
#print axioms MWG.MarketPower.lcvProfit
#print axioms MWG.MarketPower.IsLCVNash
#print axioms MWG.MarketPower.IsLCVUniqueBR
#print axioms MWG.MarketPower.lcv_buys_iff
#print axioms MWG.MarketPower.volume_unit_inter_Iio
#print axioms MWG.MarketPower.lcvShare_spec
#print axioms MWG.MarketPower.lcHat_symm
#print axioms MWG.MarketPower.lcvShare_nonneg
#print axioms MWG.MarketPower.lcvShare_eq_of
#print axioms MWG.MarketPower.lcvShare_eq_zero
#print axioms MWG.MarketPower.lcv_le_zero_of_lt
#print axioms MWG.MarketPower.lcv_mul_le
#print axioms MWG.MarketPower.lcv_le_of_share
#print axioms MWG.MarketPower.lcv_le_one
#print axioms MWG.MarketPower.lcv_le_A
#print axioms MWG.MarketPower.lcv_le_B
#print axioms MWG.MarketPower.lcv_uniqueBR_of
#print axioms MWG.MarketPower.lcv_eq_of_uniqueBR
#print axioms MWG.MarketPower.lcv_max_of_uniqueBR
#print axioms MWG.MarketPower.lcvNash_of_BR
#print axioms MWG.MarketPower.lcvBR_low
#print axioms MWG.MarketPower.lcvBR_duo
#print axioms MWG.MarketPower.lcvBR_kink
#print axioms MWG.MarketPower.lcvBR_mono
#print axioms MWG.MarketPower.lcvBR_cover
#print axioms MWG.MarketPower.lcvBR_capture
#print axioms MWG.MarketPower.lcvBRLow
#print axioms MWG.MarketPower.lcvBRMid
#print axioms MWG.MarketPower.lcvBRHigh
#print axioms MWG.MarketPower.lcvBRLow_spec
#print axioms MWG.MarketPower.lcvBRMid_spec
#print axioms MWG.MarketPower.lcvBRHigh_spec
#print axioms MWG.MarketPower.lcv_rival_low
#print axioms MWG.MarketPower.lcvNash_ge_c
#print axioms MWG.MarketPower.lcvShare_symm_half
#print axioms MWG.MarketPower.smallType_12_C_398
#print axioms MWG.MarketPower.smallType_12_C_398_kink
#print axioms MWG.MarketPower.exercise_12_C_13
#print axioms MWG.MarketPower.exercise_12_C_14a
#print axioms MWG.MarketPower.exercise_12_C_14b
#print axioms MWG.MarketPower.exercise_12_C_14c
#print axioms MWG.MarketPower.exercise_12_C_14c_counterexample
#print axioms MWG.MarketPower.exercise_12_C_14d
#print axioms MWG.MarketPower.exercise_12_C_14e
#print axioms MWG.MarketPower.quadCity_prefers
#print axioms MWG.MarketPower.lcDemand_eq_share
#print axioms MWG.MarketPower.exercise_12_C_15
#print axioms MWG.MarketPower.circLin_prefers
#print axioms MWG.MarketPower.circLin_beyond
#print axioms MWG.MarketPower.circQuad_prefers
#print axioms MWG.MarketPower.circQuad_beyond
#print axioms MWG.MarketPower.circDemand
#print axioms MWG.MarketPower.circ_symmetric_eqm
#print axioms MWG.MarketPower.circ_symmetric_unique
#print axioms MWG.MarketPower.circularCity_linear
#print axioms MWG.MarketPower.exercise_12_C_16
#print axioms MWG.MarketPower.exercise_12_C_16_limits
#print axioms MWG.MarketPower.repWelfare
#print axioms MWG.MarketPower.repUtility_budget
#print axioms MWG.MarketPower.repWelfare_update
#print axioms MWG.MarketPower.eq_12_C_13
#print axioms MWG.MarketPower.repTangent
#print axioms MWG.MarketPower.repTangent_strict
#print axioms MWG.MarketPower.eq_12_C_13_sufficient
#print axioms MWG.MarketPower.eq_12_C_13_unique
#print axioms MWG.MarketPower.eq_12_C_13_instance
#print axioms MWG.MarketPower.monComp_demand
#print axioms MWG.MarketPower.monComp_index_update
#print axioms MWG.MarketPower.monComp_no_interaction
#print axioms MWG.MarketPower.IsMonCompEqm
#print axioms MWG.MarketPower.monComp_example
#print axioms MWG.MarketPower.mbProfit
#print axioms MWG.MarketPower.mbProfit_fst
#print axioms MWG.MarketPower.mbProfit_snd
#print axioms MWG.MarketPower.mbWin
#print axioms MWG.MarketPower.mbProfit_indicator
#print axioms MWG.MarketPower.mbProfit_integral
#print axioms MWG.MarketPower.IsMixedPrice
#print axioms MWG.MarketPower.mbPayoff
#print axioms MWG.MarketPower.IsMixedBertrandNE
#print axioms MWG.MarketPower.mbPayoff_eq
#print axioms MWG.MarketPower.mbPayoff_dirac
#print axioms MWG.MarketPower.isMixedPrice_dirac
#print axioms MWG.MarketPower.mbWin_nonneg
#print axioms MWG.MarketPower.mbWin_le_Ici
#print axioms MWG.MarketPower.mbWin_le_one
#print axioms MWG.MarketPower.mbWin_antitone
#print axioms MWG.MarketPower.mb_x_anti
#print axioms MWG.MarketPower.mb_bound
#print axioms MWG.MarketPower.mb_exists_mem
#print axioms MWG.MarketPower.mb_ae_nonneg
#print axioms MWG.MarketPower.mb_ae_eq
#print axioms MWG.MarketPower.mb_gap
#print axioms MWG.MarketPower.mb_win_one
#print axioms MWG.MarketPower.mb_rival_pos
#print axioms MWG.MarketPower.mb_ae_Ici_ne_zero
#print axioms MWG.MarketPower.mb_top_atom
#print axioms MWG.MarketPower.mb_undercut
#print axioms MWG.MarketPower.mb_above_null
#print axioms MWG.MarketPower.mb_low_price
#print axioms MWG.MarketPower.mb_below_null
#print axioms MWG.MarketPower.mb_eq_dirac
#print axioms MWG.MarketPower.exercise_12_C_2
#print axioms MWG.MarketPower.bcGame
#print axioms MWG.MarketPower.bcGame_nash_iff
#print axioms MWG.MarketPower.bcGame_weaklyDominated_one
#print axioms MWG.MarketPower.bcGame_weaklyDominated_zero
#print axioms MWG.MarketPower.mbProfit_of_lt
#print axioms MWG.MarketPower.mbProfit_self
#print axioms MWG.MarketPower.mbProfit_of_gt
#print axioms MWG.MarketPower.mbProfit_high
#print axioms MWG.MarketPower.exercise_12_C_4a
#print axioms MWG.MarketPower.exercise_12_C_4a_none
#print axioms MWG.MarketPower.bcLinDemand
#print axioms MWG.MarketPower.bcLinDemand_isBertrand
#print axioms MWG.MarketPower.exercise_12_C_4a_none_instance
#print axioms MWG.MarketPower.exercise_12_C_4a_drastic_instance
#print axioms MWG.MarketPower.bcTieProfit₁
#print axioms MWG.MarketPower.bcTieProfit₂
#print axioms MWG.MarketPower.exercise_12_C_4a_tieRule
#print axioms MWG.MarketPower.bcGridGame
#print axioms MWG.MarketPower.mbProfit_nonpos
#print axioms MWG.MarketPower.mbProfit_nonneg
#print axioms MWG.MarketPower.exercise_12_C_4b
#print axioms MWG.MarketPower.exercise_12_C_4b_eqm
#print axioms MWG.MarketPower.exercise_12_C_4b_dominated
#print axioms MWG.MarketPower.exercise_12_C_4b_undominated
#print axioms MWG.MarketPower.exercise_12_C_4b_limit
#print axioms MWG.MarketPower.exercise_12_C_4b_instance
#print axioms MWG.MarketPower.ubAbove
#print axioms MWG.MarketPower.ubPayoff
#print axioms MWG.MarketPower.IsUBNash
#print axioms MWG.MarketPower.ubAbove_irrefl
#print axioms MWG.MarketPower.ubAbove_total
#print axioms MWG.MarketPower.ubAbove_ssubset
#print axioms MWG.MarketPower.ubAbove_card_injective
#print axioms MWG.MarketPower.ubAbove_card_lt
#print axioms MWG.MarketPower.ub_card_winners
#print axioms MWG.MarketPower.ubAbove_const
#print axioms MWG.MarketPower.ubAbove_update_lt
#print axioms MWG.MarketPower.ubAbove_update_gt
#print axioms MWG.MarketPower.exercise_12_C_5a
#print axioms MWG.MarketPower.exercise_12_C_5_competitive
#print axioms MWG.MarketPower.ub_lose_bid
#print axioms MWG.MarketPower.exercise_12_C_5b
#print axioms MWG.MarketPower.ccLinCost
#print axioms MWG.MarketPower.ccLin_profit0
#print axioms MWG.MarketPower.ccLin_profit1
#print axioms MWG.MarketPower.cc_br_kkt
#print axioms MWG.MarketPower.ccLin_ne_iff
#print axioms MWG.MarketPower.exercise_12_C_9a
#print axioms MWG.MarketPower.exercise_12_C_9b
#print axioms MWG.MarketPower.exercise_12_C_19a
#print axioms MWG.MarketPower.exercise_12_C_19b
#print axioms MWG.MarketPower.cc_sum_update_two
#print axioms MWG.MarketPower.cc_foc
#print axioms MWG.MarketPower.cc_move
#print axioms MWG.MarketPower.exercise_12_C_10a
#print axioms MWG.MarketPower.efficientCost
#print axioms MWG.MarketPower.allocWelfare
#print axioms MWG.MarketPower.efficientSurplus
#print axioms MWG.MarketPower.efficientCost_le
#print axioms MWG.MarketPower.exercise_12_C_10b
#print axioms MWG.MarketPower.exercise_12_C_10b_strict
#print axioms MWG.MarketPower.exercise_12_C_10_instance
#print axioms MWG.MarketPower.cc_lin_integral
#print axioms MWG.MarketPower.exercise_12_C_10c
#print axioms MWG.MarketPower.cc_convex_increment
#print axioms MWG.MarketPower.exercise_12_C_20
#print axioms MWG.MarketPower.exercise_12_C_20_instance
#print axioms MWG.MarketPower.sc_strictMonoOn_diff
#print axioms MWG.MarketPower.sc_topkis
#print axioms MWG.MarketPower.sc_foc_interior
#print axioms MWG.MarketPower.exercise_12_C_12a
#print axioms MWG.MarketPower.exercise_12_C_12a_unique
#print axioms MWG.MarketPower.exercise_12_C_12b_normal
#print axioms MWG.MarketPower.exercise_12_C_12b
#print axioms MWG.MarketPower.exercise_12_C_12b_instance
#print axioms MWG.MarketPower.sb_hasDerivAt
#print axioms MWG.MarketPower.sb_anti_own
#print axioms MWG.MarketPower.sb_anti_rival
#print axioms MWG.MarketPower.sb_br_unique
#print axioms MWG.MarketPower.sb_br_of_foc
#print axioms MWG.MarketPower.sb_br_anti
#print axioms MWG.MarketPower.exercise_12_C_18a
#print axioms MWG.MarketPower.exercise_12_C_18a_instance
#print axioms MWG.MarketPower.IsLCNash2
#print axioms MWG.MarketPower.lc2_br_mid
#print axioms MWG.MarketPower.lc2_br_high
#print axioms MWG.MarketPower.lc2_br
#print axioms MWG.MarketPower.exercise_12_C_17
#print axioms MWG.MarketPower.exercise_12_C_17_statics
#print axioms MWG.MarketPower.fhValue
#print axioms MWG.MarketPower.IsFiniteRepeatedSPNE
#print axioms MWG.MarketPower.finiteNashValue
#print axioms MWG.MarketPower.fhValue_congr
#print axioms MWG.MarketPower.finite_repeated_step
#print axioms MWG.MarketPower.finite_repeated_unique_spne
#print axioms MWG.MarketPower.finite_repeated_spne_iff
#print axioms MWG.MarketPower.bertrandStage_nash_iff
#print axioms MWG.MarketPower.finite_repeated_bertrand
#print axioms MWG.MarketPower.finite_repeated_bertrand_instance
#print axioms MWG.MarketPower.rbx_le_of_below
#print axioms MWG.MarketPower.rbx_scaled_isBertrand
#print axioms MWG.MarketPower.rbx_update
#print axioms MWG.MarketPower.rbx_lin_facts
#print axioms MWG.MarketPower.exercise_12_D_4a
#print axioms MWG.MarketPower.exercise_12_D_4a_monotone
#print axioms MWG.MarketPower.exercise_12_D_4a_instance
#print axioms MWG.MarketPower.costChangeU
#print axioms MWG.MarketPower.costChangePath
#print axioms MWG.MarketPower.costChangeProfile
#print axioms MWG.MarketPower.CostChangeSustains
#print axioms MWG.MarketPower.costChangeValue
#print axioms MWG.MarketPower.costChangeValue_on
#print axioms MWG.MarketPower.costChangeValue_off
#print axioms MWG.MarketPower.osValue_costChange
#print axioms MWG.MarketPower.costChange_spne_iff
#print axioms MWG.MarketPower.exercise_12_D_4b
#print axioms MWG.MarketPower.exercise_12_D_4b_compare
#print axioms MWG.MarketPower.exercise_12_D_4b_instance
#print axioms MWG.MarketPower.rsValue
#print axioms MWG.MarketPower.IsRSNashReversion
#print axioms MWG.MarketPower.rs_state_iff
#print axioms MWG.MarketPower.rs_threshold
#print axioms MWG.MarketPower.exercise_12_D_5a
#print axioms MWG.MarketPower.rs_high_nec
#print axioms MWG.MarketPower.exercise_12_D_5b
#print axioms MWG.MarketPower.rbx_price_eq_c
#print axioms MWG.MarketPower.exercise_12_D_5c
#print axioms MWG.MarketPower.exercise_12_D_5_instance
#print axioms MWG.MarketPower.footnote_12_24
#print axioms MWG.MarketPower.footnote_12_24_instance
#print axioms MWG.MarketPower.IsLowestPriceRule
#print axioms MWG.MarketPower.oneStageProfit
#print axioms MWG.MarketPower.IsOneStageEq
#print axioms MWG.MarketPower.oneStagePrice
#print axioms MWG.MarketPower.exists_lowestPriceRule
#print axioms MWG.MarketPower.example_12_E_4_set
#print axioms MWG.MarketPower.oneStagePrice_spec
#print axioms MWG.MarketPower.lowestRule_update_lt
#print axioms MWG.MarketPower.lowestRule_update_gt
#print axioms MWG.MarketPower.oneStageProfit_of_win
#print axioms MWG.MarketPower.oneStageProfit_of_lose
#print axioms MWG.MarketPower.oneStageProfit_le
#print axioms MWG.MarketPower.example_12_E_4
#print axioms MWG.MarketPower.example_12_E_4_exists
#print axioms MWG.MarketPower.oneStageWelfare
#print axioms MWG.MarketPower.example_12_E_4_welfare
#print axioms MWG.MarketPower.example_12_E_4_instance
#print axioms MWG.MarketPower.osCexDemand
#print axioms MWG.MarketPower.osCexDemand_mid
#print axioms MWG.MarketPower.osCexDemand_isBertrand
#print axioms MWG.MarketPower.example_12_E_4_counterexample
#print axioms MWG.MarketPower.shareProfit
#print axioms MWG.MarketPower.IsShareEq
#print axioms MWG.MarketPower.shareProfit_of_lowest
#print axioms MWG.MarketPower.shareProfit_of_gt
#print axioms MWG.MarketPower.footnote_12_26
#print axioms MWG.MarketPower.footnote_12_27
#print axioms MWG.MarketPower.footnote_12_27_instance
#print axioms MWG.MarketPower.e1Profit
#print axioms MWG.MarketPower.IsEntryStageEq
#print axioms MWG.MarketPower.exercise_12_E_1
#print axioms MWG.MarketPower.exercise_12_E_3_cournot
#print axioms MWG.MarketPower.bertrandEntryOutput
#print axioms MWG.MarketPower.exercise_12_E_3_bertrand
#print axioms MWG.MarketPower.exercise_12_E_4
#print axioms MWG.MarketPower.circTravelCost
#print axioms MWG.MarketPower.circTravelCost_eq
#print axioms MWG.MarketPower.circWelfare
#print axioms MWG.MarketPower.exercise_12_E_5
#print axioms MWG.MarketPower.exercise_12_E_5_instance
#print axioms MWG.MarketPower.IsOneStageCournotEntryGen
#print axioms MWG.MarketPower.exercise_12_E_6_two_to_one
#print axioms MWG.MarketPower.exercise_12_E_6_fewer
#print axioms MWG.MarketPower.exercise_12_E_6_linear
#print axioms MWG.MarketPower.exercise_12_E_6_converse_fails
#print axioms MWG.MarketPower.IsPriceEntryConfig
#print axioms MWG.MarketPower.exercise_12_E_7
#print axioms MWG.MarketPower.exercise_12_E_7_efficient
#print axioms MWG.MarketPower.exercise_12_E_7_instance
#print axioms MWG.MarketPower.e7CexAC
#print axioms MWG.MarketPower.exercise_12_E_7_counterexample
