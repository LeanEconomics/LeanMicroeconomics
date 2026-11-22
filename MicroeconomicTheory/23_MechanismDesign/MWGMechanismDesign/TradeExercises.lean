/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Auctions23B
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bargaining, trading and auction exercises

MWG, Exercises 23.D.1, 23.D.4, 23.D.5, 23.D.6 (pp. 920-921) and 23.E.4, 23.E.5, 23.E.6
(p. 922).

* **Exercise 23.D.1** (Myerson): (a) the alternatives (`BargainX`); (b) with seller types
  `{0, 9}`, buyer value `10`, prices `(10 + θₛ)/2`, immediate trade for `θₛ = 0` and trade in
  period `n + 1` for `θₛ = 9`, the outcome is incentive compatible iff `19δⁿ ≤ 10`, i.e. iff
  `n ≥ ⌈log(10/19)/log δ⌉` (`exercise_23_D_1b`): the earliest trade time is
  `1 + ⌈log(10/19)/log δ⌉`.
* **Exercise 23.D.4** (first-price auction): (a) the interim probability of winning is
  nondecreasing in the type and bids are nondecreasing among types that win with positive
  probability (`exercise_23_D_4a`); (b) no interval of types bids the same amount when tying
  bidders win with positive probability and winning ties for sure is a discrete gain
  (`exercise_23_D_4b`), so equilibrium bids are strictly increasing
  (`exercise_23_D_4b_strictMono`); (c) revenue equivalence with the second-price auction
  (`exercise_23_D_4c`). Non-vacuity: the two-bidder uniform equilibrium `b(θ) = θ/2`
  (`exercise_23_D_4_instance`).
* **Exercise 23.D.5** (all-pay auction): monotonicity (`exercise_23_D_5_monotone`) and revenue
  equivalence (`exercise_23_D_5`).
* **Exercise 23.D.6** (queue): `I = n + 1` individuals with uniform values; waiting `w` hours
  before the office opens costs `βw` to the first in line only (a first-price auction with bid
  `βw`). `w(θ) = nθ/((n + 1)β)` is a symmetric equilibrium (`exercise_23_D_6_bne`) and the
  expected wait of the first in line is `(I - 1)/((I + 1)β)` (`exercise_23_D_6`): doubling `β`
  halves it, doubling `I` raises it.
* **Exercise 23.E.4** (discounting): ex post efficiency requires immediate trade when `θ₂ > θ₁`
  and no trade when `θ₁ > θ₂` (`exercise_23_E_4_efficient`); with `ȳ = δ^(t-1)` the trading
  process is a bilateral trade social choice function (`exercise_23_E_4_payoffs`), and
  Proposition 23.E.1 rules out ex post efficiency (`exercise_23_E_4`).
* **Exercise 23.E.5** (continuum of traders): (a) the threshold rule at a market-clearing price
  maximises the gains from trade among all mass-balanced trades (`exercise_23_E_5a`); (b) the
  competitive (posted price) mechanism makes truth telling dominant (hence Bayesian incentive
  compatible), is individually rational and balances the budget (`exercise_23_E_5b`).
* **Exercise 23.E.6** (partnership): (a) the higher valuation gets both units
  (`exercise_23_E_6a`); (b) `b(θ) = 2θ/3` is a symmetric Bayesian Nash equilibrium of "highest
  bidder buys and pays his bid" (`exercise_23_E_6b`); (c) the implemented social choice function
  is Bayesian incentive compatible, ex post efficient and individually rational, with
  `Uᵢ(θᵢ) = θᵢ² + 1/3 > θᵢ` (`exercise_23_E_6c`).

**Departures.** Exercise 23.D.4(a) is proved for types with positive winning probability (bids
that never win are payoff irrelevant and are not pinned down by the equilibrium conditions);
the auction-theoretic primitives of 23.D.4(a), (b) and 23.D.5 are stated for a general
winning-probability function `P(b)` (nondecreasing in the bid, as it is whatever the others'
strategies). In 23.D.6 the probability that a given individual is first in line, given his
value `θ`, is the independence formula `θⁿ`. In 23.E.5 traders are modelled by finite
measures of sellers' and buyers' values (equal masses are not needed).
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-! ## Exercise 23.D.1 -/

/-- **Exercise 23.D.1(a)** (MWG, p. 920). The set of alternatives of the bargaining problem:
`none` is "no trade" and `some (n, p)` is "trade in period `n + 1` at price `p`", that is
`X = {no trade} ∪ ({1, 2, …} × ℝ)`. -/
def BargainX : Type := Option (ℕ × ℝ)

/-- **Exercise 23.D.1(a)**: the seller's (discounted) gain from an alternative,
`δ^(t-1)(p - θₛ)` if trade occurs in period `t` at price `p`, `0` without trade. -/
noncomputable def bargSellerU (δ θs : ℝ) (x : BargainX) : ℝ :=
  Option.elim x 0 fun np => δ ^ np.1 * (np.2 - θs)

/-- **Exercise 23.D.1(a)**: the buyer's (discounted) gain `δ^(t-1)(θ_b - p)`. -/
noncomputable def bargBuyerU (δ θb : ℝ) (x : BargainX) : ℝ :=
  Option.elim x 0 fun np => δ ^ np.1 * (θb - np.2)

/-- The outcome of Exercise 23.D.1(b): price `(10 + θₛ)/2`, immediate trade when `θₛ = 0`
(`false`) and trade in period `n + 1` when `θₛ = 9` (`true`). -/
noncomputable def bargOutcome (n : ℕ) (high : Bool) : BargainX :=
  if high then some (n, 19 / 2) else some (0, 5)

/-- The seller's valuation: `0` (`false`) or `9` (`true`). -/
def bargSellerVal (high : Bool) : ℝ := if high then 9 else 0

/-- **Exercise 23.D.1(b)** (MWG, pp. 920-921). By the revelation principle the outcome of a
Bayesian Nash equilibrium is incentive compatible for the seller (the buyer's value `10` is
known). With discount factor `0 < δ < 1`, the outcome (immediate trade at `5` when `θₛ = 0`,
trade in period `n + 1` at `9.5` when `θₛ = 9`) is incentive compatible and individually
rational iff `19δⁿ ≤ 10`, iff `n ≥ log(10/19)/log δ`, iff `n ≥ ⌈log(10/19)/log δ⌉`. So the
earliest possible time of trade when `θₛ = 9` is period `1 + ⌈log(10/19)/log δ⌉`. -/
theorem exercise_23_D_1b {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) :
    ((∀ θ θh : Bool, bargSellerU δ (bargSellerVal θ) (bargOutcome n θh) ≤
        bargSellerU δ (bargSellerVal θ) (bargOutcome n θ)) ∧
      (∀ θ, 0 ≤ bargSellerU δ (bargSellerVal θ) (bargOutcome n θ)) ∧
      ∀ θ, 0 ≤ bargBuyerU δ 10 (bargOutcome n θ)) ↔ 19 * δ ^ n ≤ 10 ∧
      (19 * δ ^ n ≤ 10 ↔ Real.log (10 / 19) / Real.log δ ≤ n) ∧
      (19 * δ ^ n ≤ 10 ↔ ⌈Real.log (10 / 19) / Real.log δ⌉₊ ≤ n) := by
  have hpos : 0 < δ ^ n := pow_pos hδ0 n
  have hlog : Real.log δ < 0 := Real.log_neg hδ0 hδ1
  have hiff : 19 * δ ^ n ≤ 10 ↔ Real.log (10 / 19) / Real.log δ ≤ n := by
    rw [div_le_iff_of_neg hlog, ← Real.log_pow, Real.log_le_log_iff hpos (by norm_num)]
    constructor <;> intro h <;> linarith
  have hiff2 : 19 * δ ^ n ≤ 10 ↔ ⌈Real.log (10 / 19) / Real.log δ⌉₊ ≤ n := by
    rw [Nat.ceil_le, hiff]
  constructor
  · rintro ⟨hic, -, -⟩
    have h := hic false true
    simp [bargSellerU, bargOutcome, bargSellerVal] at h
    exact ⟨by linarith, hiff, hiff2⟩
  · rintro ⟨h, -, -⟩
    refine ⟨fun θ θh => ?_, fun θ => ?_, fun θ => ?_⟩
    · cases θ <;> cases θh <;> simp [bargSellerU, bargOutcome, bargSellerVal] <;> nlinarith
    · cases θ <;> simp [bargSellerU, bargOutcome, bargSellerVal]
      nlinarith
    · cases θ <;> simp [bargBuyerU, bargOutcome] <;> nlinarith

/-! ## Exercise 23.E.4 -/

/-- **Exercise 23.E.4** (MWG, p. 922). A (deterministic) trading process: `τ(θ) = some n` is
trade in period `n + 1`, `none` no trade. The seller (agent `0`) holds the good with
"probability" `ȳ₀ = 1 - δⁿ` and the buyer with `ȳ₁ = δⁿ` (expected discounted trade). -/
noncomputable def discY (δ : ℝ) (τ : (Fin 2 → ℝ) → Option ℕ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => Option.elim (τ θ) ![1, 0] fun n => ![1 - δ ^ n, δ ^ n]

/-- **Exercise 23.E.4** (MWG, p. 922). With trade in period `n + 1` at price `p` the seller gets
`θ₁ + δⁿ(p - θ₁) = θ₁(1 - δⁿ) + δⁿp` and the buyer `δⁿ(θ₂ - p) = θ₂δⁿ - δⁿp`: utilities of the
form `θᵢȳᵢ + tᵢ` with `ȳ = discY` and discounted transfers, so the discounted setting is the
bilateral trade setting of Section 23.E. -/
theorem exercise_23_E_4_payoffs (δ θs θb p : ℝ) (n : ℕ) :
    θs + δ ^ n * (p - θs) = θs * (1 - δ ^ n) + δ ^ n * p ∧
      δ ^ n * (θb - p) = θb * δ ^ n + -(δ ^ n * p) := by
  constructor <;> ring

/-- Total surplus of a trading outcome: `θ₁ + δⁿ(θ₂ - θ₁)` with trade in period `n + 1`, `θ₁`
without trade. -/
noncomputable def discSurplus (δ : ℝ) (θ : Fin 2 → ℝ) (o : Option ℕ) : ℝ :=
  θ 0 + Option.elim o 0 (fun n => δ ^ n) * (θ 1 - θ 0)

/-- **Exercise 23.E.4** (MWG, p. 922), "Note that ex post efficiency requires that trade occur
in period 1 whenever `θ₂ > θ₁`, and that trade not occur whenever `θ₁ > θ₂`": with
`0 < δ < 1`, an outcome maximises total surplus iff it has these two properties. -/
theorem exercise_23_E_4_efficient {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (θ : Fin 2 → ℝ)
    (o : Option ℕ) :
    (∀ o', discSurplus δ θ o' ≤ discSurplus δ θ o) ↔
      (θ 0 < θ 1 → o = some 0) ∧ (θ 1 < θ 0 → o = none) := by
  have hw : ∀ o' : Option ℕ, 0 ≤ Option.elim o' 0 (fun n => δ ^ n) ∧
      Option.elim o' 0 (fun n => δ ^ n) ≤ 1 := by
    intro o'
    cases o' with
    | none => simp
    | some n => exact ⟨by simp [(pow_pos hδ0 n).le], by simp [pow_le_one₀ hδ0.le hδ1.le]⟩
  constructor
  · intro h
    refine ⟨fun hlt => ?_, fun hlt => ?_⟩
    · have h0 := h (some 0)
      cases o with
      | none => simp only [discSurplus, Option.elim] at h0; norm_num at h0; linarith
      | some n =>
        rcases n with _ | n
        · rfl
        · simp only [discSurplus, Option.elim, pow_zero] at h0
          have : δ ^ (n + 1) < 1 := pow_lt_one₀ hδ0.le hδ1 (by omega)
          nlinarith
    · have h0 := h none
      cases o with
      | none => rfl
      | some n =>
        simp only [discSurplus, Option.elim] at h0
        have := pow_pos hδ0 n
        nlinarith
  · rintro ⟨h1, h2⟩ o'
    obtain ⟨hw0, hw1⟩ := hw o'
    have e1 : Option.elim (some 0) (0 : ℝ) (fun n => δ ^ n) = 1 := by simp
    have e0 : Option.elim (none : Option ℕ) (0 : ℝ) (fun n => δ ^ n) = 0 := rfl
    rcases lt_trichotomy (θ 0) (θ 1) with hlt | heq | hgt
    · rw [h1 hlt]
      simp only [discSurplus, e1]
      nlinarith
    · simp only [discSurplus, heq, sub_self, mul_zero, le_refl]
    · rw [h2 hgt]
      simp only [discSurplus, e0]
      nlinarith

/-- **Exercise 23.E.4** (MWG, p. 922). Under the assumptions of Proposition 23.E.1 (independent
valuations with strictly positive densities, `(θ̲₂, θ̄₂) ∩ (θ̲₁, θ̄₁) ≠ ∅`) and discounting
`0 < δ < 1`, no voluntary trading process achieves ex post efficiency: no trading process with
immediate trade when `θ₂ > θ₁` and no trade when `θ₁ > θ₂`, budget balanced (discounted)
transfers, Bayesian incentive compatibility and interim individual rationality exists. (The
seller is agent `0`, the buyer agent `1`; the process enters through `ȳ = discY δ τ`.) -/
theorem exercise_23_E_4 (D : Fin 2 → TypeDensity)
    (hov : (Set.Ioo (D 0).lo (D 0).hi ∩ Set.Ioo (D 1).lo (D 1).hi).Nonempty) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {τ : (Fin 2 → ℝ) → Option ℕ} {t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable (discY δ τ))
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV (discY δ τ) t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (heff : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ →
      (θ 0 < θ 1 → τ θ = some 0) ∧ (θ 1 < θ 0 → τ θ = none))
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hbic : BayesianICOn (Measure.pi fun j => (D j).measure) allocV (discY δ τ) t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) (discY δ τ) t (fun i => (D i).lo)
      fun i => (D i).hi) : False := by
  refine proposition_23_E_1 D hov hym hint ht (fun θ hθ => ?_) hbb hbic hir
  obtain ⟨h1, h2⟩ := heff θ hθ
  have hb : ∀ n : ℕ, 0 ≤ δ ^ n ∧ δ ^ n ≤ 1 := fun n =>
    ⟨(pow_pos hδ0 n).le, pow_le_one₀ hδ0.le hδ1.le⟩
  refine ⟨?_, ?_, ?_, fun hlt => ?_, fun hlt => ?_⟩
  · simp only [discY]
    cases τ θ <;> simp
  · simp only [discY]
    cases τ θ <;> simp [hb]
  · simp only [discY]
    cases τ θ <;> simp [hb]
  · simp [discY, h1 hlt]
  · simp [discY, h2 hlt]

/-! ## Exercise 23.E.5 -/

/-- **Exercise 23.E.5** (MWG, p. 922). A price `p` clears the market: the mass of sellers with
valuation below `p` equals the mass of buyers with valuation above `p`. -/
def MarketClears (μS μB : Measure ℝ) (p : ℝ) : Prop :=
  μS.real (Set.Iio p) = μB.real (Set.Ioi p)

/-- **Exercise 23.E.5(a)** (MWG, p. 922). With a continuum of sellers (valuations distributed
by the finite measure `μS`) and buyers (`μB`), let `p` clear the market. Among all trades in
which a measurable set `S` of seller valuations sells and a measurable set `B` of buyer
valuations buys, with equal masses `μS(S) = μB(B)`, the gains from trade
`∫_B θ dμB - ∫_S θ dμS` are maximised by the threshold rule: sellers with `θ₁ < p` sell and
buyers with `θ₂ > p` buy. -/
theorem exercise_23_E_5a {μS μB : Measure ℝ} [IsFiniteMeasure μS] [IsFiniteMeasure μB]
    (hS : Integrable (fun x : ℝ => x) μS) (hB : Integrable (fun x : ℝ => x) μB) {p : ℝ}
    (hp : MarketClears μS μB p) {S B : Set ℝ} (hSm : MeasurableSet S) (hBm : MeasurableSet B)
    (hbal : μS.real S = μB.real B) :
    (∫ x in B, x ∂μB) - (∫ x in S, x ∂μS) ≤
      (∫ x in Set.Ioi p, x ∂μB) - ∫ x in Set.Iio p, x ∂μS := by
  have hgS : Integrable (fun x : ℝ => x - p) μS := hS.sub (integrable_const p)
  have hgB : Integrable (fun x : ℝ => x - p) μB := hB.sub (integrable_const p)
  have split : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ], Integrable (fun x : ℝ => x) μ →
      ∀ A : Set ℝ, ∫ x in A, x ∂μ = (∫ x in A, (x - p) ∂μ) + μ.real A * p := by
    intro μ _ hμ A
    rw [integral_sub hμ.integrableOn (integrableOn_const), setIntegral_const, smul_eq_mul]
    ring
  rw [split μB hB B, split μS hS S, split μB hB (Set.Ioi p), split μS hS (Set.Iio p), hbal, hp]
  have hB' : ∫ x in B, (x - p) ∂μB ≤ ∫ x in Set.Ioi p, (x - p) ∂μB := by
    rw [← integral_indicator hBm, ← integral_indicator measurableSet_Ioi]
    refine integral_mono (hgB.indicator hBm) (hgB.indicator measurableSet_Ioi) fun x => ?_
    by_cases hxB : x ∈ B <;> by_cases hxp : p < x <;>
      simp [Set.indicator, hxB, hxp] <;> linarith
  have hS' : ∫ x in Set.Iio p, (x - p) ∂μS ≤ ∫ x in S, (x - p) ∂μS := by
    rw [← integral_indicator hSm, ← integral_indicator measurableSet_Iio]
    refine integral_mono (hgS.indicator measurableSet_Iio) (hgS.indicator hSm) fun x => ?_
    by_cases hxS : x ∈ S <;> by_cases hxp : x < p <;>
      simp [Set.indicator, hxS, hxp] <;> linarith
  linarith

/-- The competitive mechanism of Exercise 23.E.5(b) for a seller of valuation `θ` who reports
`r`: he sells at the market price `p` iff `r < p`. -/
noncomputable def compSellerU (p θ r : ℝ) : ℝ := if r < p then p else θ

/-- The competitive mechanism for a buyer of valuation `θ` who reports `r`: he buys at `p` iff
`r > p`. -/
noncomputable def compBuyerU (p θ r : ℝ) : ℝ := if p < r then θ - p else 0

/-- **Exercise 23.E.5(b)** (MWG, p. 922). In the competitive mechanism (a single trader's report
does not affect the market-clearing price `p` of a continuum economy) truth telling is a dominant
strategy for every seller and buyer, hence Bayesian incentive compatible; it is individually
rational (a seller gets at least his valuation, a buyer at least `0`); it implements the
threshold trading rule of (a); and with a market-clearing price the payments balance. -/
theorem exercise_23_E_5b (p : ℝ) :
    (∀ θ r, compSellerU p θ r ≤ compSellerU p θ θ) ∧
      (∀ θ r, compBuyerU p θ r ≤ compBuyerU p θ θ) ∧
      (∀ θ, θ ≤ compSellerU p θ θ) ∧ (∀ θ, 0 ≤ compBuyerU p θ θ) ∧
      ∀ μS μB : Measure ℝ, MarketClears μS μB p →
        p * μB.real (Set.Ioi p) - p * μS.real (Set.Iio p) = 0 := by
  refine ⟨fun θ r => ?_, fun θ r => ?_, fun θ => ?_, fun θ => ?_, fun μS μB h => ?_⟩
  · simp only [compSellerU]; split_ifs <;> linarith
  · simp only [compBuyerU]; split_ifs <;> linarith
  · simp only [compSellerU]; split_ifs <;> linarith
  · simp only [compBuyerU]; split_ifs <;> linarith
  · rw [h]; ring

/-! ## Exercise 23.E.6 -/

/-- **Exercise 23.E.6(a)** (MWG, p. 922). Each partner owns one unit and values each unit
consumed at `θᵢ`. Among allocations `x₀ + x₁ = 2`, `xᵢ ≥ 0`, total value is at most
`2 max(θ₀, θ₁)`, attained by giving both units to the higher valuation; when `θ₀ < θ₁` it is
attained only by `x₁ = 2` (the efficient trading rule: the higher valuation buys the other's
unit). -/
theorem exercise_23_E_6a (θ0 θ1 x0 x1 : ℝ) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hsum : x0 + x1 = 2) :
    θ0 * x0 + θ1 * x1 ≤ 2 * max θ0 θ1 ∧
      (θ0 < θ1 → (θ0 * x0 + θ1 * x1 = 2 * max θ0 θ1 ↔ x1 = 2)) := by
  have hx0' : x0 = 2 - x1 := by linarith
  subst hx0'
  refine ⟨?_, fun hlt => ?_⟩
  · rcases le_total θ0 θ1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right hlt.le]
    constructor
    · intro h
      by_contra hne
      have : x1 < 2 := lt_of_le_of_ne (by linarith) hne
      nlinarith
    · intro h; rw [h]; ring

/-- `x ↦ 1{x ≤ τ} A` is interval integrable on `[0, 1]`. -/
theorem trade_ii_le (τ A : ℝ) :
    IntervalIntegrable (fun x : ℝ => if x ≤ τ then A else 0) volume 0 1 := by
  have h : (fun x : ℝ => if x ≤ τ then A else 0) = (Set.Iic τ).indicator fun _ => A := by
    funext x; simp [Set.indicator_apply]
  rw [h, intervalIntegrable_iff]
  exact (intervalIntegrable_const (c := A) (a := (0 : ℝ)) (b := 1)).def'.indicator
    measurableSet_Iic

/-- Exercise 23.E.6(b): the expected utility of a partner with valuation `θ` who bids `β` when
the other (valuation `s ~ U[0, 1]`) bids `2s/3`: if `β ≥ 2s/3` he buys the other's unit and pays
`β` (utility `2θ - β`), otherwise the other buys and pays him `2s/3`. -/
noncomputable def partnerEU (β θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, if 2 * s / 3 ≤ β then 2 * θ - β else 2 * s / 3

/-- Closed form of `partnerEU`: with `c = clamp(3β/2)`, `(2θ - β)c + (1 - c²)/3`. -/
theorem partnerEU_eq (β θ : ℝ) :
    partnerEU β θ = (2 * θ - β) * clamp01 (3 * β / 2) + (1 - clamp01 (3 * β / 2) ^ 2) / 3 := by
  have e : (fun s : ℝ => if 2 * s / 3 ≤ β then 2 * θ - β else 2 * s / 3) =
      fun s => (if s ≤ 3 * β / 2 then 2 * θ - β else 0) +
        (if 3 * β / 2 < s then 0 + 2 / 3 * s else 0) := by
    funext s
    by_cases h : 2 * s / 3 ≤ β
    · have h1 : s ≤ 3 * β / 2 := by linarith
      simp [h, h1, not_lt.2 h1]
    · have h1 : ¬s ≤ 3 * β / 2 := by intro h'; apply h; linarith
      have h2 : 3 * β / 2 < s := lt_of_not_ge h1
      simp only [h, h1, h2, ite_false, ite_true]
      ring
  rw [partnerEU, e, intervalIntegral.integral_add (trade_ii_le _ _) (au_ii_gt _ _ _),
    au_int_le, au_int_gt, au_int_affine, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Exercise 23.E.6(b)** (MWG, p. 922). In the mechanism "each partner bids; the highest
bidder buys the other's unit and pays him his bid", with valuations independent and uniform on
`[0, 1]`, the linear strategy `b(θ) = 2θ/3` is a symmetric Bayesian Nash equilibrium: against
`b`, no bid `β ∈ ℝ` does better than `2θ/3`. -/
theorem exercise_23_E_6b {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (β : ℝ) :
    partnerEU β θ ≤ partnerEU (2 * θ / 3) θ := by
  have e : 3 * (2 * θ / 3) / 2 = θ := by ring
  rw [partnerEU_eq, partnerEU_eq, e, clamp01_of_mem hθ]
  rcases le_or_gt (3 * β / 2) 0 with h | h
  · rw [clamp01_of_nonpos h]; nlinarith
  · rcases le_or_gt 1 (3 * β / 2) with h1 | h1
    · rw [clamp01_of_one_le h1]; nlinarith [hθ.2]
    · rw [clamp01_of_mem ⟨h.le, h1.le⟩]; nlinarith [sq_nonneg (θ - 3 * β / 2)]

/-- The interim utility of the equilibrium of Exercise 23.E.6(b): `U(θ) = θ² + 1/3`. -/
theorem partnerEU_eq_equilibrium {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    partnerEU (2 * θ / 3) θ = θ ^ 2 + 1 / 3 := by
  have e : 3 * (2 * θ / 3) / 2 = θ := by ring
  rw [partnerEU_eq, e, clamp01_of_mem hθ]
  ring

/-- The social choice function implemented in Exercise 23.E.6(c): agent `0` gets both units
(`2`) iff `θ₁ ≤ θ₀`, and the buyer pays the seller `2θ_buyer/3`. -/
noncomputable def partnerSCF (θ : Fin 2 → ℝ) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  if θ 1 ≤ θ 0 then (![2, 0], ![-(2 * θ 0 / 3), 2 * θ 0 / 3])
  else (![0, 2], ![2 * θ 1 / 3, -(2 * θ 1 / 3)])

/-- **Exercise 23.E.6(c)** (MWG, p. 922). The social choice function implemented by the
equilibrium of (b) (the higher valuation buys the other's unit at two thirds of his valuation)
is Bayesian incentive compatible (announcing `r` amounts to bidding `2r/3`), ex post efficient
(both units go to the higher valuation and transfers balance), and individually rational:
`Uᵢ(θᵢ) = θᵢ² + 1/3 > θᵢ`, the value of consuming one's own unit. Unlike the
Myerson-Satterthwaite setting, ownership is split, so every type is a potential buyer and
seller. -/
theorem exercise_23_E_6c :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      partnerEU (2 * r / 3) θ ≤ partnerEU (2 * θ / 3) θ) ∧
      (∀ θ : Fin 2 → ℝ, θ 0 * (partnerSCF θ).1 0 + θ 1 * (partnerSCF θ).1 1 =
        2 * max (θ 0) (θ 1) ∧ (partnerSCF θ).2 0 + (partnerSCF θ).2 1 = 0) ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, partnerEU (2 * θ / 3) θ = θ ^ 2 + 1 / 3 ∧
        θ < partnerEU (2 * θ / 3) θ := by
  refine ⟨fun θ hθ r _ => exercise_23_E_6b hθ _, fun θ => ?_, fun θ hθ => ?_⟩
  · simp only [partnerSCF]
    split_ifs with h
    · simp [max_eq_left h]; ring
    · simp [max_eq_right (le_of_lt (lt_of_not_ge h))]; ring
  · rw [partnerEU_eq_equilibrium hθ]
    exact ⟨rfl, by nlinarith [sq_nonneg (θ - 1 / 2)]⟩

/-! ## Exercises 23.D.4 and 23.D.5 -/

/-- **Exercise 23.D.4(a)** (MWG, p. 921). In a first-price auction let `P(b)` be a bidder's
probability of winning with bid `b` given the others' strategies (nondecreasing in `b`), and let
`b*(θ)` be a best response for every type in `[θ̲, θ̄]`: `(θ - b)P(b) ≤ (θ - b*(θ))P(b*(θ))`.
Then for `θ < θ'`: the interim probability of winning is nondecreasing,
`P(b*(θ)) ≤ P(b*(θ'))` (the monotonicity of `ȳ` that Bayesian incentive compatibility
requires), and if `θ` wins with positive probability then `b*(θ) ≤ b*(θ')`. -/
theorem exercise_23_D_4a {P b : ℝ → ℝ} (hP : Monotone P) {lo hi : ℝ}
    (hBR : ∀ θ ∈ Set.Icc lo hi, ∀ β, (θ - β) * P β ≤ (θ - b θ) * P (b θ)) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc lo hi) (hθ' : θ' ∈ Set.Icc lo hi) (hlt : θ < θ') :
    P (b θ) ≤ P (b θ') ∧ (0 < P (b θ) → b θ ≤ b θ') := by
  have h1 := hBR θ hθ (b θ')
  have h2 := hBR θ' hθ' (b θ)
  have hy : P (b θ) ≤ P (b θ') := by nlinarith
  refine ⟨hy, fun hpos => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have heq : P (b θ') = P (b θ) := le_antisymm (hP hcon.le) hy
  rw [heq] at h1
  nlinarith

/-- **Exercise 23.D.4(b)** (MWG, p. 921). Suppose types in `(θ', θ'')`, `θ' < θ''`, all bid the
same `β` in a symmetric equilibrium. Then tying bidders win with positive probability,
`P(β) > 0`, and bidding slightly more wins all ties: `P(β) + q ≤ P(β')` for all `β' > β`, for
some `q > 0`. Under these conditions no such interval of types can be best responding. -/
theorem exercise_23_D_4b {P b : ℝ → ℝ} {θ' θ'' β : ℝ} (hlt : θ' < θ'')
    (hBR : ∀ θ ∈ Set.Ioo θ' θ'', ∀ β', (θ - β') * P β' ≤ (θ - b θ) * P (b θ))
    (hflat : ∀ θ ∈ Set.Ioo θ' θ'', b θ = β) (hpos : 0 < P β)
    (hjump : ∃ q > 0, ∀ β' > β, P β + q ≤ P β') : False := by
  obtain ⟨q, hq, hj⟩ := hjump
  -- a type in the interval different from `β`
  obtain ⟨θ, hθ, hne⟩ : ∃ θ ∈ Set.Ioo θ' θ'', θ ≠ β := by
    by_cases h : (θ' + θ'') / 2 = β
    · refine ⟨(3 * θ' + θ'') / 4, ⟨by linarith, by linarith⟩, ?_⟩
      intro h'; linarith
    · exact ⟨(θ' + θ'') / 2, ⟨by linarith, by linarith⟩, h⟩
  have hb := hflat θ hθ
  rcases hne.lt_or_gt with hθβ | hθβ
  · -- bidding `θ` gives `0 > (θ - β)P(β)`
    have := hBR θ hθ θ
    rw [hb] at this
    nlinarith
  · -- bidding `β + ε` with `ε = (θ - β)q/(2(P(β) + q))` is better
    set d := θ - β with hd
    have hd0 : 0 < d := by linarith
    set ε := d * q / (2 * (P β + q)) with hε
    have hε0 : 0 < ε := by positivity
    have hεd : ε < d := by
      rw [hε, div_lt_iff₀ (by positivity)]
      nlinarith
    have h1 := hBR θ hθ (β + ε)
    have h2 := hj (β + ε) (by linarith)
    rw [hb] at h1
    have h3 : (θ - (β + ε)) * (P β + q) ≤ (θ - (β + ε)) * P (β + ε) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : (θ - (β + ε)) * (P β + q) = d * P β + (d * q - ε * (P β + q)) := by ring
    have h5 : ε * (P β + q) = d * q / 2 := by
      rw [hε]; field_simp
    nlinarith

/-- **Exercise 23.D.4(b)**, conclusion (MWG, p. 921): bids that are nondecreasing on an interval
and constant on no subinterval are strictly increasing there. -/
theorem exercise_23_D_4b_strictMono {b : ℝ → ℝ} {lo hi : ℝ}
    (hmono : MonotoneOn b (Set.Icc lo hi))
    (hnoflat : ∀ θ' θ'', lo ≤ θ' → θ' < θ'' → θ'' ≤ hi → ¬∀ θ ∈ Set.Ioo θ' θ'', b θ = b θ') :
    StrictMonoOn b (Set.Icc lo hi) := by
  intro x hx y hy hxy
  rcases (hmono hx hy hxy.le).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hnoflat x y hx.1 hxy hy.2
    intro θ hθ
    have h1 := hmono hx ⟨hx.1.trans hθ.1.le, hθ.2.le.trans hy.2⟩ hθ.1.le
    have h2 := hmono ⟨hx.1.trans hθ.1.le, hθ.2.le.trans hy.2⟩ hy hθ.2.le
    rw [← h] at h2
    exact le_antisymm h2 h1

/-- Non-vacuity of Exercise 23.D.4(a): with two bidders uniform on `[0, 1]`, against the other's
bid `θ/2` the winning probability is `P(b) = clamp(2b)` and `b*(θ) = θ/2` is a best response for
every type (Example 23.B.5). -/
theorem exercise_23_D_4_instance :
    Monotone (fun β : ℝ => clamp01 (2 * β)) ∧ ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ β,
      (θ - β) * clamp01 (2 * β) ≤ (θ - θ / 2) * clamp01 (2 * (θ / 2)) := by
  refine ⟨fun x y hxy => ?_, fun θ hθ β => ?_⟩
  · simp only [clamp01]
    exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)
  · have e : 2 * (θ / 2) = θ := by ring
    rw [e, clamp01_of_mem hθ]
    rcases le_or_gt (2 * β) 0 with h | h
    · rw [clamp01_of_nonpos h]; nlinarith [hθ.1]
    · rcases le_or_gt 1 (2 * β) with h1 | h1
      · rw [clamp01_of_one_le h1]; nlinarith [hθ.2]
      · rw [clamp01_of_mem ⟨h.le, h1.le⟩]; nlinarith [sq_nonneg (θ - 2 * β)]

/-- **Exercise 23.D.4(c)** (MWG, p. 921). By the revenue equivalence theorem: the social choice
function of any symmetric equilibrium of the first-price auction and that of the dominant
strategy equilibrium of the second-price auction are Bayesian incentive compatible, have the same
allocation `y` (by (b), the highest valuation wins) and give the lowest types `Uᵢ(θ̲ᵢ) = 0`;
hence they yield the same expected revenue (`proposition_23_D_3`). -/
theorem exercise_23_D_4c {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {y tFP tSP : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y tFP lo hi)
    (hint' : InterimIntegrable (Measure.pi μ) allocV y tSP lo hi)
    (ht : ∀ i, Integrable (fun θ => tFP θ i) (Measure.pi μ))
    (ht' : ∀ i, Integrable (fun θ => tSP θ i) (Measure.pi μ))
    (hFP : BayesianICOn (Measure.pi μ) allocV y tFP lo hi)
    (hSP : BayesianICOn (Measure.pi μ) allocV y tSP lo hi)
    (hU : ∀ i, interimU (Measure.pi μ) allocV y tFP i (lo i) = 0)
    (hU' : ∀ i, interimU (Measure.pi μ) allocV y tSP i (lo i) = 0) :
    ∑ i, ∫ θ, -tFP θ i ∂Measure.pi μ = ∑ i, ∫ θ, -tSP θ i ∂Measure.pi μ :=
  (proposition_23_D_3 μ hsupp hint hint' ht ht' hFP hSP fun i => (hU i).trans (hU' i).symm).2

/-- **Exercise 23.D.5** (MWG, p. 921), the all-pay auction, monotonicity step (as in
Exercise 23.D.4(a)): if every type best responds, `θP(β) - β ≤ θP(b(θ)) - b(θ)`, then the
interim winning probability and the bid are nondecreasing in the type. -/
theorem exercise_23_D_5_monotone {P b : ℝ → ℝ} (hP : Monotone P) {lo hi : ℝ}
    (hBR : ∀ θ ∈ Set.Icc lo hi, ∀ β, θ * P β - β ≤ θ * P (b θ) - b θ) {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc lo hi) (hθ' : θ' ∈ Set.Icc lo hi) (hlt : θ < θ') :
    P (b θ) ≤ P (b θ') ∧ b θ ≤ b θ' := by
  have h1 := hBR θ hθ (b θ')
  have h2 := hBR θ' hθ' (b θ)
  have hy : P (b θ) ≤ P (b θ') := by nlinarith
  refine ⟨hy, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have heq : P (b θ') = P (b θ) := le_antisymm (hP hcon.le) hy
  rw [heq] at h1
  linarith

/-- **Exercise 23.D.5** (MWG, p. 921). The all-pay auction: its symmetric equilibrium social
choice function (every buyer pays his bid, the highest bidder wins) is Bayesian incentive
compatible with the same allocation as the second-price auction and `Uᵢ(θ̲ᵢ) = 0`, so by the
revenue equivalence theorem it yields the same expected revenue. -/
theorem exercise_23_D_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {y tAP tSP : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y tAP lo hi)
    (hint' : InterimIntegrable (Measure.pi μ) allocV y tSP lo hi)
    (ht : ∀ i, Integrable (fun θ => tAP θ i) (Measure.pi μ))
    (ht' : ∀ i, Integrable (fun θ => tSP θ i) (Measure.pi μ))
    (hAP : BayesianICOn (Measure.pi μ) allocV y tAP lo hi)
    (hSP : BayesianICOn (Measure.pi μ) allocV y tSP lo hi)
    (hU : ∀ i, interimU (Measure.pi μ) allocV y tAP i (lo i) = 0)
    (hU' : ∀ i, interimU (Measure.pi μ) allocV y tSP i (lo i) = 0) :
    ∑ i, ∫ θ, -tAP θ i ∂Measure.pi μ = ∑ i, ∫ θ, -tSP θ i ∂Measure.pi μ :=
  exercise_23_D_4c μ hsupp hint hint' ht ht' hAP hSP hU hU'

/-! ## Exercise 23.D.6 -/

/-- `(n + 1)θxⁿ - nxⁿ⁺¹ ≤ θⁿ⁺¹` for `x > 0`, `θ ≥ 0` (Bernoulli's inequality). -/
theorem queue_bernoulli (n : ℕ) {θ x : ℝ} (hθ : 0 ≤ θ) (hx : 0 < x) :
    (n + 1) * θ * x ^ n - n * x ^ (n + 1) ≤ θ ^ (n + 1) := by
  have hb := one_add_mul_le_pow (a := θ / x - 1) (by have := div_nonneg hθ hx.le; linarith)
    (n + 1)
  have e : 1 + (θ / x - 1) = θ / x := by ring
  rw [e, div_pow] at hb
  have hxn : 0 < x ^ (n + 1) := pow_pos hx _
  rw [le_div_iff₀ hxn] at hb
  have e2 : (1 + ((n + 1 : ℕ) : ℝ) * (θ / x - 1)) * x ^ (n + 1) =
      (n + 1) * θ * x ^ n - n * x ^ (n + 1) := by
    push_cast
    field_simp
    ring
  linarith

/-- **Exercise 23.D.6** (MWG, p. 921), equilibrium. `I = n + 1` individuals with values
independent and uniform on `[0, 1]`; waiting `w` hours costs `βw` (`β > 0`) to the first in line
only. Against others who wait `w*(s) = ns/((n + 1)β)`, waiting `w` gets the ticket with
probability `clamp((n + 1)βw/n)ⁿ` (independence), and `w*(θ)` is a best response for every
`θ ∈ [0, 1]` (this is the first-price auction with bid `βw`). -/
theorem exercise_23_D_6_bne (n : ℕ) (hn : 1 ≤ n) {β : ℝ} (hβ : 0 < β) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) :
    (θ - β * w) * clamp01 ((n + 1) * β * w / n) ^ n ≤
      (θ - β * (n * θ / ((n + 1) * β))) *
        clamp01 ((n + 1) * β * (n * θ / ((n + 1) * β)) / n) ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (n + 1) * β * (n * θ / ((n + 1) * β)) / n = θ := by field_simp
  have e2 : θ - β * (n * θ / ((n + 1) * β)) = θ / (n + 1) := by field_simp; ring
  rw [e1, e2, clamp01_of_mem hθ]
  have hR : θ / (n + 1) * θ ^ n = θ ^ (n + 1) / (n + 1) := by rw [pow_succ]; ring
  rw [hR]
  set z := (n + 1) * β * w / n with hz
  have hw : β * w = n * z / (n + 1) := by rw [hz]; field_simp
  rcases le_or_gt z 0 with h | h
  · rw [clamp01_of_nonpos h, zero_pow (by omega), mul_zero]
    have := pow_nonneg hθ.1 (n + 1)
    positivity
  · rcases le_or_gt 1 z with h1 | h1
    · rw [clamp01_of_one_le h1, one_pow, mul_one, hw]
      have hb := queue_bernoulli n hθ.1 one_pos
      simp only [one_pow, mul_one] at hb
      rw [le_div_iff₀ (by positivity)]
      have : n * z / (n + 1) * (n + 1) = n * z := by field_simp
      nlinarith
    · rw [clamp01_of_mem ⟨h.le, h1.le⟩, hw]
      have hb := queue_bernoulli n hθ.1 h
      rw [le_div_iff₀ (by positivity)]
      have e3 : (θ - n * z / (n + 1)) * z ^ n * (n + 1) =
          (n + 1) * θ * z ^ n - n * z ^ (n + 1) := by
        field_simp
        ring
      linarith

/-- The expected wait of the first in line in Exercise 23.D.6: each of the `n + 1` individuals
is first in line with probability `θⁿ` given his value `θ` and then waits `w*(θ)`, so the
expected wait is `(n + 1)∫₀¹ w*(θ)θⁿ dθ`. -/
noncomputable def queueExpectedWait (n : ℕ) (β : ℝ) : ℝ :=
  (n + 1) * ∫ θ in (0 : ℝ)..1, n * θ / ((n + 1) * β) * θ ^ n

/-- **Exercise 23.D.6** (MWG, p. 921). With `I = n + 1` individuals the expected number of hours
the first in line waits is `(I - 1)/((I + 1)β) = n/((n + 2)β)`; it halves when `β` doubles and
rises when `I` doubles (`n ↦ 2n + 1`). -/
theorem exercise_23_D_6 (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    queueExpectedWait n β = n / ((n + 2) * β) ∧
      queueExpectedWait n (2 * β) = queueExpectedWait n β / 2 ∧
      (1 ≤ n → queueExpectedWait n β < queueExpectedWait (2 * n + 1) β) := by
  have key : ∀ (m : ℕ) (γ : ℝ), 0 < γ → queueExpectedWait m γ = m / ((m + 2) * γ) := by
    intro m γ hγ
    have e : (fun θ : ℝ => m * θ / ((m + 1) * γ) * θ ^ m) =
        fun θ => m / ((m + 1) * γ) * θ ^ (m + 1) := by
      funext θ; rw [pow_succ]; ring
    rw [queueExpectedWait, e, intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    field_simp
    ring
  refine ⟨key n β hβ, ?_, fun hn => ?_⟩
  · rw [key n (2 * β) (by positivity), key n β hβ]
    field_simp
  · rw [key n β hβ, key (2 * n + 1) β hβ, div_lt_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith

end MWG.MechanismDesign
