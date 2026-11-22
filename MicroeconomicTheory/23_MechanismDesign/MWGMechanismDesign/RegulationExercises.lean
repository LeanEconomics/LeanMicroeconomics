/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.OptimalContract

/-!
# Optimal selling, regulation and production-rights exercises

MWG, Exercises 23.F.2, 23.F.5, 23.F.6 and 23.F.7 (pp. 923-924).

* **Exercise 23.F.2** (Maskin-Riley): the consumer's utility `θv(x) - t` is the agent's utility
  of Example 23.F.1 with effort `x`, `g = v` and transfer `-t`; the monopolist's profit `t - cx` is
  the principal's payoff with `v(e) = -ce`. Hence (`exercise_23_F_2`): if `x*(θ)` maximises the
  virtual surplus `J(θ)v(x) - cx` over `x ≥ 0` for every type, and `(x*, t*)` is incentive
  compatible and individually rational with `U*(θ̲) = 0`, it is the optimal selling mechanism.
  At interior quantities `J(θ)v'(x*) = c` (`exercise_23_F_2_foc`); types with `J(θ) ≤ 0` are
  excluded (`exercise_23_F_2_exclusion`); `x*` is nondecreasing (`oc_maximizer_monotoneOn`).
* **Exercise 23.F.5**: (a) quantities `qᵢ` (prices `pᵢ = Pᵢ(qᵢ)`) are optimal when each `qᵢ`
  maximises `Rᵢ(q) - λq` for a common `λ ≥ 0` with complementary slackness
  (`exercise_23_F_5a`): marginal revenues are equalised (`exercise_23_F_5a_foc`); (b) with demand
  `x(p) = 1 - Φ(p)`, marginal revenue in quantity is the virtual valuation
  `J(p) = p - (1 - Φ(p))/φ(p)` of Example 23.F.2 (`exercise_23_F_5b`).
* **Exercise 23.F.6** (Baron-Myerson): (a) with profit `π = (p - θ)x(p) + t`, incentive
  compatibility iff `x(p(·))` is nonincreasing and `Π(θ) = Π(θ̲) - ∫_{θ̲}^{θ} x(p(s)) ds`
  (`exercise_23_F_6a`); `x(p(·))` nonincreasing iff `p(·)` nondecreasing (`exercise_23_F_6a_price`);
  individual rationality iff `Π(θ̄) ≥ 0` (`exercise_23_F_6a_ir`). (b) expected welfare equals
  `E[S(p) + (p - θ - (1 - α)Φ/φ)x(p)] - (1 - α)Π(θ̄)` (`exercise_23_F_6b_objective`); for
  `α < 1` the pointwise maximiser with `Π(θ̄) = 0` is optimal (`exercise_23_F_6b`), and
  `p*(θ) = θ + (1 - α)Φ(θ)/φ(θ)` (`exercise_23_F_6b_price`); for `α = 1` the objective is
  `E[S(p) + (p - θ)x(p)]` (marginal-cost pricing, transfers irrelevant) and for `α > 1` it is
  unbounded (`exercise_23_F_6b_alpha_ge_one`).
* **Exercise 23.F.7** (Dana-Spier): the Cournot outcomes with `p = 1 - x` and marginal cost `c`
  (`exercise_23_F_7_monopoly`, `exercise_23_F_7_duopoly`); the virtual welfare of a market
  structure (`dsVirtualWelfare`) with virtual cost `λθⱼ + (λ - 1)Φ(θⱼ)/φ(θⱼ)`; and its
  monotonicity: lowering a firm's virtual cost never makes excluding it better
  (`exercise_23_F_7`).

**Corrections.** Exercise 23.F.6(b) as printed maximises `∫_{p}^{∞} x + απ` with consumer surplus
gross of the transfer; then raising `t` by `c` preserves incentive compatibility and individual
rationality and raises the objective by `αc`, so for `α > 0` there is no optimum
(`exercise_23_F_6b_printed_unbounded`). We use consumer surplus net of the transfer,
`S(p) - t + απ` (as in Baron-Myerson). **Departures.** Prices are restricted to `p ≥ 0`
(MWG: `p > 0`). Exercise 23.F.7: the reduction of the planner's expected welfare to the expected
virtual welfare (the two-firm analogue of (23.F.4)) is not formalised; we prove the pointwise
characterisation and its monotonicity.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-! ## Exercise 23.F.2 -/

/-- **Exercise 23.F.2** (MWG, p. 923), Maskin-Riley. A consumer of type `θ ∈ [θ̲, θ̄]` (`θ̲ > 0`,
density `φ > 0`) gets `θv(x) - t`; the monopolist's unit cost is `c`. In the notation of
Example 23.F.1 the consumer is the agent with effort `x`, `g = v`, transfer `-t` and reservation
utility `0`, and the monopolist's profit `t - cx` is the principal's payoff with `v(e) = -ce`
(`OCFeasible` = incentive compatible, individually rational, expectations exist). If `x*(θ)`
maximises the virtual surplus `v(x)J(θ) - cx` over `x ≥ 0` for every type and `(x*, t*)` is
feasible with `U*(θ̲) = 0`, then `(x*, t*)` maximises expected profit
`E[t(θ) - cx(θ)]` among all feasible mechanisms. -/
theorem exercise_23_F_2 (D : TypeDensity) {v : ℝ → ℝ} {c : ℝ} {xs ts : ℝ → ℝ}
    (hs : OCFeasible D (fun q => -(c * q)) v 0 xs fun θ => -ts θ)
    (hU : ocU v xs (fun θ => -ts θ) D.lo = 0)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi,
      OCArgmax (fun q => -(c * q) + v q * D.virtualValue θ) (xs θ))
    {x t : ℝ → ℝ} (h : OCFeasible D (fun q => -(c * q)) v 0 x fun θ => -t θ) :
    ∫ θ, (t θ - c * x θ) ∂D.measure ≤ ∫ θ, (ts θ - c * xs θ) ∂D.measure := by
  have := example_23_F_1 D hs hU hmax h
  simp only [ocPayoff, sub_neg_eq_add] at this
  have e : ∀ (y s : ℝ → ℝ), (fun θ => -(c * y θ) + s θ) = fun θ => s θ - c * y θ :=
    fun y s => funext fun θ => by ring
  rwa [e, e] at this

/-- **Exercise 23.F.2** (MWG, p. 923): at an interior optimal quantity `x*(θ) > 0`,
`J(θ)v'(x*) = c` (marginal virtual surplus equals marginal cost). -/
theorem exercise_23_F_2_foc {v : ℝ → ℝ} {v' c J q : ℝ} (hv : HasDerivAt v v' q) (hq : 0 < q)
    (hmax : OCArgmax (fun x => -(c * x) + v x * J) q) : J * v' = c := by
  have := eq_23_F_6 ((hasDerivAt_id q).const_mul c).neg hv hq hmax
  simp only [mul_one] at this
  linarith

/-- **Exercise 23.F.2** (MWG, p. 923): with `c > 0`, `v(0) = 0` and `v ≥ 0` on `x ≥ 0`, a type
with `J(θ) ≤ 0` is excluded: `0` is the unique maximiser of `v(x)J(θ) - cx`. -/
theorem exercise_23_F_2_exclusion {v : ℝ → ℝ} {c J : ℝ} (hc : 0 < c) (hv0 : v 0 = 0)
    (hv : ∀ x, 0 ≤ x → 0 ≤ v x) (hJ : J ≤ 0) :
    OCArgmax (fun x => -(c * x) + v x * J) 0 ∧
      ∀ q, OCArgmax (fun x => -(c * x) + v x * J) q → q = 0 := by
  have key : ∀ x, 0 ≤ x → -(c * x) + v x * J ≤ -(c * x) := fun x hx => by
    nlinarith [hv x hx]
  refine ⟨⟨le_rfl, fun x hx => ?_⟩, fun q hq => ?_⟩
  · simp only [mul_zero, neg_zero, hv0, zero_mul, add_zero]
    have := key x hx
    nlinarith
  · by_contra hne
    have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hne)
    have h1 := hq.2 0 le_rfl
    have h2 := key q hq.1
    simp only [mul_zero, neg_zero, hv0, zero_mul, add_zero] at h1
    nlinarith

/-! ## Exercise 23.F.5 -/

/-- **Exercise 23.F.5(a)** (MWG, p. 923). A monopolist with one divisible unit and two buyers with
decreasing demands sells `qᵢ` to buyer `i` at the price `Pᵢ(qᵢ)` (`Pᵢ` the inverse demand), with
revenue `Rᵢ(q) = Pᵢ(q)q`. If for some `λ ≥ 0` each `qᵢ` maximises `Rᵢ(q) - λq` over `q ≥ 0` and
`λ(1 - q₁ - q₂) = 0`, then no feasible `q₁' + q₂' ≤ 1` earns more; so when also
`q₁ + q₂ ≤ 1`, the prices `Pᵢ(qᵢ)` are optimal. -/
theorem exercise_23_F_5a {R1 R2 : ℝ → ℝ} {q1 q2 lam : ℝ} (hlam : 0 ≤ lam)
    (h1 : ∀ q, 0 ≤ q → R1 q - lam * q ≤ R1 q1 - lam * q1)
    (h2 : ∀ q, 0 ≤ q → R2 q - lam * q ≤ R2 q2 - lam * q2) (hcs : lam * (1 - q1 - q2) = 0)
    {q1' q2' : ℝ} (hq1 : 0 ≤ q1') (hq2 : 0 ≤ q2') (hq' : q1' + q2' ≤ 1) :
    R1 q1' + R2 q2' ≤ R1 q1 + R2 q2 := by
  have := h1 q1' hq1
  have := h2 q2' hq2
  nlinarith

/-- **Exercise 23.F.5(a)** (MWG, p. 923): at interior quantities the marginal revenues are equal
to the shadow value `λ` of the unit. -/
theorem exercise_23_F_5a_foc {R1 R2 : ℝ → ℝ} {R1' R2' q1 q2 lam : ℝ}
    (hR1 : HasDerivAt R1 R1' q1) (hR2 : HasDerivAt R2 R2' q2) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (h1 : ∀ q, 0 ≤ q → R1 q - lam * q ≤ R1 q1 - lam * q1)
    (h2 : ∀ q, 0 ≤ q → R2 q - lam * q ≤ R2 q2 - lam * q2) : R1' = lam ∧ R2' = lam := by
  have l1 : IsLocalMax (fun q => R1 q - lam * q) q1 :=
    Filter.mem_of_superset (Ioi_mem_nhds hq1) fun q hq => h1 q (le_of_lt hq)
  have l2 : IsLocalMax (fun q => R2 q - lam * q) q2 :=
    Filter.mem_of_superset (Ioi_mem_nhds hq2) fun q hq => h2 q (le_of_lt hq)
  have d1 := l1.hasDerivAt_eq_zero (hR1.sub ((hasDerivAt_id q1).const_mul lam))
  have d2 := l2.hasDerivAt_eq_zero (hR2.sub ((hasDerivAt_id q2).const_mul lam))
  simp only [mul_one] at d1 d2
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 23.F.5(b)** (MWG, p. 923). Relation to the optimal auction of Example 23.F.2: if a
buyer's demand is `x(p) = 1 - Φ(p)` (the probability that his valuation exceeds `p`), with
`x'(p) = -φ(p) ≠ 0`, then the marginal revenue with respect to quantity,
`(d(p x(p))/dp)/(dx/dp) = (x(p) + p x'(p))/x'(p)`, is the virtual valuation
`J(p) = p - (1 - Φ(p))/φ(p)`. So the monopolist's rule "equalise marginal revenues" is the
optimal auction's rule "allocate by virtual valuations" (Bulow and Roberts). -/
theorem exercise_23_F_5b (D : TypeDensity) {p : ℝ} (hp : D.dens p ≠ 0) :
    ((1 - D.cdf p) + p * (-D.dens p)) / (-D.dens p) = D.virtualValue p := by
  simp only [TypeDensity.virtualValue]
  field_simp
  ring

/-! ## Exercise 23.F.6 -/

/-- The truthful profit `Π(θ) = (p(θ) - θ)x(p(θ)) + t(θ)` of Exercise 23.F.6. -/
def bmProfit (x p t : ℝ → ℝ) (θ : ℝ) : ℝ := (p θ - θ) * x (p θ) + t θ

/-- **Exercise 23.F.6(a)** (MWG, pp. 923-924), Proposition 23.D.2 adapted. The type-`θ` firm's
profit from announcing `θ̂` is `θ·(-x(p(θ̂))) + (p(θ̂)x(p(θ̂)) + t(θ̂))`, linear in `θ`. The scheme
`(p, t)` is incentive compatible iff `-x(p(·))` is nondecreasing and
`Π(θ) = Π(θ̲) - ∫_{θ̲}^{θ} x(p(s)) ds`. -/
theorem exercise_23_F_6a {x p t : ℝ → ℝ} {lo hi : ℝ} :
    LinearIC (fun θ => -x (p θ)) (fun θ => p θ * x (p θ) + t θ) lo hi ↔
      MonotoneOn (fun θ => -x (p θ)) (Set.Icc lo hi) ∧
        ∀ θ ∈ Set.Icc lo hi, bmProfit x p t θ = bmProfit x p t lo - ∫ s in lo..θ, x (p s) := by
  rw [linearIC_iff]
  simp only [bmProfit, intervalIntegral.integral_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, fun θ hθ => ?_⟩ <;> have := h2 θ hθ <;>
    linarith

/-- **Exercise 23.F.6(a)**: with `x` strictly decreasing on prices `p ≥ 0`, `x(p(·))` is
nonincreasing iff the price `p(·)` is nondecreasing in the cost. -/
theorem exercise_23_F_6a_price {x p : ℝ → ℝ} {S : Set ℝ} (hx : StrictAntiOn x (Set.Ici 0))
    (hp : ∀ θ, 0 ≤ p θ) : MonotoneOn (fun θ => -x (p θ)) S ↔ MonotoneOn p S := by
  have hg : StrictMonoOn (fun q => -x q) (Set.Ici 0) := fun a ha b hb hab =>
    neg_lt_neg (hx ha hb hab)
  exact oc_monotone_comp_iff hg hp

/-- **Exercise 23.F.6(a)**: given the profit formula and `x ≥ 0`, the firm is guaranteed a
nonnegative profit at every cost iff `Π(θ̄) ≥ 0`. -/
theorem exercise_23_F_6a_ir {x p t : ℝ → ℝ} {lo hi : ℝ} (hle : lo ≤ hi)
    (hx0 : ∀ θ, 0 ≤ x (p θ)) (hint : IntervalIntegrable (fun s => x (p s)) volume lo hi)
    (hii : ∀ θ ∈ Set.Icc lo hi, bmProfit x p t θ = bmProfit x p t lo - ∫ s in lo..θ, x (p s)) :
    (∀ θ ∈ Set.Icc lo hi, 0 ≤ bmProfit x p t θ) ↔ 0 ≤ bmProfit x p t hi := by
  refine ⟨fun h => h hi ⟨hle, le_rfl⟩, fun h θ hθ => ?_⟩
  have hmono : ∫ s in lo..θ, x (p s) ≤ ∫ s in lo..hi, x (p s) :=
    intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
      (Filter.Eventually.of_forall fun s => hx0 s) hint
  rw [hii θ hθ]
  rw [hii hi ⟨hle, le_rfl⟩] at h
  linarith

/-- The regulator's weighted welfare at cost `θ` for Exercise 23.F.6(b), with consumer surplus net
of the transfer: `S(p(θ)) - t(θ) + απ(p(θ), t(θ), θ)`, where `S(p) = ∫_p^∞ x(s) ds`. -/
def bmWelfare (S x p t : ℝ → ℝ) (α θ : ℝ) : ℝ := S (p θ) - t θ + α * bmProfit x p t θ

/-- The virtual welfare of price `q` at cost `θ`:
`S(q) + (q - θ - (1 - α)Φ(θ)/φ(θ))x(q)`. -/
noncomputable def bmVirtual (D : TypeDensity) (S x : ℝ → ℝ) (α θ q : ℝ) : ℝ :=
  S q + (q - θ - (1 - α) * (D.cdf θ / D.dens θ)) * x q

/-- A feasible regulatory scheme for Exercise 23.F.6: incentive compatible, individually rational
(`Π(θ) ≥ 0`), with the expectations involved existing. -/
def BMFeasible (D : TypeDensity) (S x p t : ℝ → ℝ) : Prop :=
  LinearIC (fun θ => -x (p θ)) (fun θ => p θ * x (p θ) + t θ) D.lo D.hi ∧
    (∀ θ ∈ Set.Icc D.lo D.hi, 0 ≤ bmProfit x p t θ) ∧
    Integrable (fun θ => S (p θ)) D.measure ∧
    Integrable (fun θ => (p θ - θ) * x (p θ)) D.measure ∧ Integrable t D.measure ∧
    Integrable (fun θ => x (p θ) * (D.cdf θ / D.dens θ)) D.measure

/-- **Exercise 23.F.6(b)** (MWG, p. 924). For a feasible scheme the expected weighted welfare is
`E[S(p) + (p - θ - (1 - α)Φ/φ)x(p)] - (1 - α)Π(θ̄)` (the analogue of (23.F.4), by the Fubini form
of the integration by parts). -/
theorem exercise_23_F_6b_objective (D : TypeDensity) {S x p t : ℝ → ℝ} {α : ℝ}
    (hf : BMFeasible D S x p t) :
    ∫ θ, bmWelfare S x p t α θ ∂D.measure =
      ∫ θ, bmVirtual D S x α θ (p θ) ∂D.measure - (1 - α) * bmProfit x p t D.hi := by
  have := D.isProbabilityMeasure
  obtain ⟨hIC, -, hS, hpx, ht, hr⟩ := hf
  obtain ⟨hmono, hii⟩ := exercise_23_F_6a.1 hIC
  have hle : D.lo ≤ D.hi := D.lo_lt_hi.le
  have hw : IntervalIntegrable (fun s => x (p s)) volume D.lo D.hi := by
    have h1 : IntervalIntegrable (fun s => -x (p s)) volume D.lo D.hi := by
      apply MonotoneOn.intervalIntegrable; rw [Set.uIcc_of_le hle]; exact hmono
    convert h1.neg using 1
    funext s; simp
  have hProf : Integrable (bmProfit x p t) D.measure := hpx.add ht
  have hae : ∀ᵐ θ ∂D.measure, θ ∈ Set.Icc D.lo D.hi := mem_ae_iff.2 D.measure_compl_Icc
  have hP : (fun θ => bmProfit x p t D.lo - bmProfit x p t θ) =ᵐ[D.measure]
      fun θ => ∫ s in D.lo..θ, x (p s) := by
    filter_upwards [hae] with θ hθ
    rw [hii θ hθ]; ring
  have hPint : Integrable (fun θ => ∫ s in D.lo..θ, x (p s)) D.measure :=
    ((integrable_const _).sub hProf).congr hP
  have hEP : ∫ θ, (∫ s in D.lo..θ, x (p s)) ∂D.measure =
      ∫ s in D.lo..D.hi, x (p s) * (1 - D.cdf s) := by
    rw [td_integral_integral_eq D.measure hle D.measure_compl_Icc hw]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    simp only [D.measureReal_Ici hs]
  have hEProf : ∫ θ, bmProfit x p t θ ∂D.measure =
      bmProfit x p t D.lo - ∫ s in D.lo..D.hi, x (p s) * (1 - D.cdf s) := by
    rw [← hEP]
    have e1 : ∫ θ, bmProfit x p t θ ∂D.measure =
        ∫ θ, (bmProfit x p t D.lo - ∫ s in D.lo..θ, x (p s)) ∂D.measure := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with θ hθ
      rw [hii θ hθ]
    rw [e1, integral_sub (integrable_const _) hPint, integral_const, probReal_univ, one_smul]
  have hhi := hii D.hi ⟨hle, le_rfl⟩
  have hcdf : IntervalIntegrable (fun s => x (p s) * D.cdf s) volume D.lo D.hi :=
    hw.mul_continuousOn D.continuous_cdf.continuousOn
  have hsplit : ∫ s in D.lo..D.hi, x (p s) * (1 - D.cdf s) =
      (∫ s in D.lo..D.hi, x (p s)) - ∫ s in D.lo..D.hi, x (p s) * D.cdf s := by
    rw [← intervalIntegral.integral_sub hw hcdf]
    congr 1; funext s; ring
  have hr' : ∫ θ, x (p θ) * (D.cdf θ / D.dens θ) ∂D.measure =
      ∫ s in D.lo..D.hi, x (p s) * D.cdf s := by
    rw [D.integral_eq]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    have := (D.dens_pos s hs).ne'
    field_simp
  have eW : ∫ θ, bmWelfare S x p t α θ ∂D.measure = ∫ θ, S (p θ) ∂D.measure +
      ∫ θ, (p θ - θ) * x (p θ) ∂D.measure - (1 - α) * ∫ θ, bmProfit x p t θ ∂D.measure := by
    have e : (fun θ => bmWelfare S x p t α θ) = fun θ =>
        (S (p θ) + (p θ - θ) * x (p θ)) - (1 - α) * bmProfit x p t θ := by
      funext θ; simp only [bmWelfare, bmProfit]; ring
    have i1 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ) - (1 - α) * bmProfit x p t θ) ∂D.measure =
        ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure -
          ∫ θ, (1 - α) * bmProfit x p t θ ∂D.measure :=
      integral_sub (hS.add hpx) (hProf.const_mul _)
    have i2 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure =
        ∫ θ, S (p θ) ∂D.measure + ∫ θ, (p θ - θ) * x (p θ) ∂D.measure := integral_add hS hpx
    rw [e, i1, i2, integral_const_mul]
  have eV : ∫ θ, bmVirtual D S x α θ (p θ) ∂D.measure = ∫ θ, S (p θ) ∂D.measure +
      ∫ θ, (p θ - θ) * x (p θ) ∂D.measure -
        (1 - α) * ∫ θ, x (p θ) * (D.cdf θ / D.dens θ) ∂D.measure := by
    have e : (fun θ => bmVirtual D S x α θ (p θ)) = fun θ =>
        (S (p θ) + (p θ - θ) * x (p θ)) - (1 - α) * (x (p θ) * (D.cdf θ / D.dens θ)) := by
      funext θ; simp only [bmVirtual]; ring
    have i1 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ) -
        (1 - α) * (x (p θ) * (D.cdf θ / D.dens θ))) ∂D.measure =
        ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure -
          ∫ θ, (1 - α) * (x (p θ) * (D.cdf θ / D.dens θ)) ∂D.measure :=
      integral_sub (hS.add hpx) (hr.const_mul _)
    have i2 : ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure =
        ∫ θ, S (p θ) ∂D.measure + ∫ θ, (p θ - θ) * x (p θ) ∂D.measure := integral_add hS hpx
    rw [e, i1, i2, integral_const_mul]
  rw [eW, eV, hEProf, hsplit, hr']
  rw [hhi]
  ring

/-- **Exercise 23.F.6(b)** (MWG, p. 924), `α < 1`. If `p*(θ) ≥ 0` maximises the virtual welfare
`S(q) + (q - θ - (1 - α)Φ(θ)/φ(θ))x(q)` over prices `q ≥ 0` for every cost, and `(p*, t*)` is
feasible with `Π*(θ̄) = 0`, then it maximises expected welfare among all feasible schemes with
nonnegative prices. -/
theorem exercise_23_F_6b (D : TypeDensity) {S x : ℝ → ℝ} {α : ℝ} (hα : α < 1)
    {ps ts : ℝ → ℝ} (hs : BMFeasible D S x ps ts) (hProf : bmProfit x ps ts D.hi = 0)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi, ∀ q, 0 ≤ q →
      bmVirtual D S x α θ q ≤ bmVirtual D S x α θ (ps θ))
    {p t : ℝ → ℝ} (h : BMFeasible D S x p t) (hp : ∀ θ, 0 ≤ p θ) :
    ∫ θ, bmWelfare S x p t α θ ∂D.measure ≤ ∫ θ, bmWelfare S x ps ts α θ ∂D.measure := by
  rw [exercise_23_F_6b_objective D h, exercise_23_F_6b_objective D hs, hProf]
  have hIR := h.2.1 D.hi ⟨D.lo_lt_hi.le, le_rfl⟩
  have hV : ∀ {p t : ℝ → ℝ}, BMFeasible D S x p t →
      Integrable (fun θ => bmVirtual D S x α θ (p θ)) D.measure := by
    intro p t hf
    obtain ⟨-, -, hS, hpx, -, hr⟩ := hf
    refine ((hS.add hpx).sub (hr.const_mul (1 - α))).congr
      (Filter.Eventually.of_forall fun θ => ?_)
    simp only [bmVirtual, Pi.add_apply, Pi.sub_apply]
    ring
  have hle := integral_mono_ae (hV h) (hV hs) (by
    filter_upwards [mem_ae_iff.2 D.measure_compl_Icc] with θ hθ
    exact hmax θ hθ (p θ) (hp θ))
  have : 0 ≤ (1 - α) * bmProfit x p t D.hi := mul_nonneg (by linarith) hIR
  linarith

/-- **Exercise 23.F.6(b)** (MWG, p. 924), the optimal price: if `S' = -x`, `x` is differentiable
with `x'(q) ≠ 0`, and `q` is a local maximiser of the virtual welfare at cost `θ`, then
`q = θ + (1 - α)Φ(θ)/φ(θ)`: the price exceeds marginal cost by `(1 - α)Φ/φ` (nondecreasing in
`θ` when `Φ/φ` is). -/
theorem exercise_23_F_6b_price (D : TypeDensity) {S x : ℝ → ℝ} {α θ q x' : ℝ}
    (hS : HasDerivAt S (-x q) q) (hx : HasDerivAt x x' q) (hx' : x' ≠ 0)
    (hloc : IsLocalMax (bmVirtual D S x α θ) q) :
    q = θ + (1 - α) * (D.cdf θ / D.dens θ) := by
  have hd : HasDerivAt (bmVirtual D S x α θ)
      (-x q + (1 * x q + (q - θ - (1 - α) * (D.cdf θ / D.dens θ)) * x')) q :=
    hS.add ((((hasDerivAt_id' q).sub_const θ).sub_const _).fun_mul hx)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have h1 : (q - θ - (1 - α) * (D.cdf θ / D.dens θ)) * x' = 0 := by linarith
  rcases mul_eq_zero.1 h1 with h | h
  · linarith
  · exact absurd h hx'

/-- **Exercise 23.F.6(b)** (MWG, p. 924), "What if `α ≥ 1`?". Raising every transfer by `c ≥ 0`
keeps the scheme feasible and changes expected welfare by `(α - 1)c`: for `α > 1` the objective
is unbounded (no optimal scheme), and for `α = 1` expected welfare is
`E[S(p) + (p - θ)x(p)]`, independent of transfers, maximised by marginal-cost pricing. -/
theorem exercise_23_F_6b_alpha_ge_one (D : TypeDensity) {S x p t : ℝ → ℝ} {α : ℝ}
    (hf : BMFeasible D S x p t) {c : ℝ} (hc : 0 ≤ c) :
    BMFeasible D S x p (fun θ => t θ + c) ∧
      ∫ θ, bmWelfare S x p (fun θ => t θ + c) α θ ∂D.measure =
        ∫ θ, bmWelfare S x p t α θ ∂D.measure + (α - 1) * c ∧
      (α = 1 → ∫ θ, bmWelfare S x p t α θ ∂D.measure =
        ∫ θ, (S (p θ) + (p θ - θ) * x (p θ)) ∂D.measure) := by
  have := D.isProbabilityMeasure
  obtain ⟨hIC, hIR, hS, hpx, ht, hr⟩ := hf
  have hf' : BMFeasible D S x p (fun θ => t θ + c) := by
    refine ⟨fun θ hθ θh hθh => ?_, fun θ hθ => ?_, hS, hpx, ht.add (integrable_const c), hr⟩
    · have := hIC θ hθ θh hθh; simp only at this ⊢; linarith
    · have := hIR θ hθ; simp only [bmProfit] at this ⊢; linarith
  refine ⟨hf', ?_, fun hα => ?_⟩
  · have hW : Integrable (fun θ => bmWelfare S x p t α θ) D.measure := by
      refine ((hS.sub ht).add ((hpx.add ht).const_mul α)).congr
        (Filter.Eventually.of_forall fun θ => ?_)
      simp only [bmWelfare, bmProfit, Pi.add_apply, Pi.sub_apply]
    have e : (fun θ => bmWelfare S x p (fun θ => t θ + c) α θ) =
        fun θ => bmWelfare S x p t α θ + (α - 1) * c := by
      funext θ; simp only [bmWelfare, bmProfit]; ring
    rw [e, integral_add hW (integrable_const _), integral_const, probReal_univ, one_smul]
  · have h := exercise_23_F_6b_objective (α := α) D ⟨hIC, hIR, hS, hpx, ht, hr⟩
    rw [hα] at h ⊢
    rw [h]
    simp only [sub_self, zero_mul, sub_zero, bmVirtual]

/-- **Exercise 23.F.6(b)**, correction (MWG, p. 924): with the printed objective
`∫_{p(θ)}^{∞} x + απ` (consumer surplus gross of the transfer), raising every transfer by `c`
keeps the scheme feasible (`exercise_23_F_6b_alpha_ge_one`) and raises the objective by `αc`, so
for `α > 0` no optimal scheme exists. -/
theorem exercise_23_F_6b_printed_unbounded (D : TypeDensity) {S x p t : ℝ → ℝ} {α : ℝ}
    (hf : BMFeasible D S x p t) (c : ℝ) :
    ∫ θ, (S (p θ) + α * bmProfit x p (fun θ => t θ + c) θ) ∂D.measure =
      ∫ θ, (S (p θ) + α * bmProfit x p t θ) ∂D.measure + α * c := by
  have := D.isProbabilityMeasure
  obtain ⟨-, -, hS, hpx, ht, -⟩ := hf
  have hI : Integrable (fun θ => S (p θ) + α * bmProfit x p t θ) D.measure :=
    hS.add ((hpx.add ht).const_mul α)
  have e : (fun θ => S (p θ) + α * bmProfit x p (fun θ => t θ + c) θ) =
      fun θ => (S (p θ) + α * bmProfit x p t θ) + α * c := by
    funext θ; simp only [bmProfit]; ring
  rw [e, integral_add hI (integrable_const _), integral_const, probReal_univ, one_smul]

/-- Non-vacuity of `BMFeasible`: costs uniform on `[0, 1]`, unit demand `x = 1`, `S = 0`,
marginal-cost prices `p(θ) = θ` and transfers `t(θ) = 1 - θ` (so `Π(θ) = 1 - θ`, `Π(θ̄) = 0`). -/
theorem bmFeasible_instance :
    BMFeasible uniform01 (fun _ => 0) (fun _ => 1) (fun θ => θ) (fun θ => 1 - θ) ∧
      bmProfit (fun _ => 1) (fun θ => θ) (fun θ => 1 - θ) uniform01.hi = 0 := by
  have := uniform01.isProbabilityMeasure
  have hb : ∀ {f : ℝ → ℝ}, Measurable f → (∀ θ ∈ Set.Icc (0 : ℝ) 1, |f θ| ≤ 1) →
      Integrable f uniform01.measure := fun hf hC => oc_integrable_of_bound uniform01 hf 1 hC
  refine ⟨⟨fun θ _ θh _ => ?_, fun θ hθ => ?_, integrable_const _, ?_, ?_, ?_⟩, ?_⟩
  · simp only; linarith
  · simp only [bmProfit]; change θ ∈ Set.Icc (0 : ℝ) 1 at hθ; linarith [hθ.2]
  · simp only [sub_self, zero_mul]; exact integrable_const _
  · exact hb (by fun_prop) fun θ hθ => by
      rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · refine hb ((uniform01.continuous_cdf.measurable.div uniform01.measurable_dens).const_mul 1)
      fun θ hθ => ?_
    have hd : uniform01.dens θ = 1 := by
      change (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) θ = 1
      rw [Set.indicator_of_mem hθ]; norm_num
    rw [hd, uniform01_cdf hθ, div_one, one_mul, abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  · simp [bmProfit, uniform01, uniformDensity]

/-! ## Exercise 23.F.7 -/

/-- **Exercise 23.F.7** (MWG, p. 924), the unregulated monopoly: with inverse demand
`p = 1 - x` and marginal cost `c`, output `(1 - c)/2` maximises the gross profit
`(1 - q - c)q`, which is then `(1 - c)²/4`; consumer surplus is `((1 - c)/2)²/2 = (1 - c)²/8`. -/
theorem exercise_23_F_7_monopoly (c : ℝ) :
    (∀ q, (1 - q - c) * q ≤ (1 - (1 - c) / 2 - c) * ((1 - c) / 2)) ∧
      (1 - (1 - c) / 2 - c) * ((1 - c) / 2) = (1 - c) ^ 2 / 4 ∧
      ((1 - c) / 2) ^ 2 / 2 = (1 - c) ^ 2 / 8 := by
  refine ⟨fun q => ?_, by ring, by ring⟩
  nlinarith [sq_nonneg (q - (1 - c) / 2)]

/-- **Exercise 23.F.7** (MWG, p. 924), the Cournot duopoly: each firm producing `(1 - c)/3` is a
Nash equilibrium (each output is a best response to the other), each gross profit is
`(1 - c)²/9` and consumer surplus is `(2(1 - c)/3)²/2 = 2(1 - c)²/9`. -/
theorem exercise_23_F_7_duopoly (c : ℝ) :
    (∀ q, (1 - q - (1 - c) / 3 - c) * q ≤
      (1 - (1 - c) / 3 - (1 - c) / 3 - c) * ((1 - c) / 3)) ∧
      (1 - (1 - c) / 3 - (1 - c) / 3 - c) * ((1 - c) / 3) = (1 - c) ^ 2 / 9 ∧
      (2 * (1 - c) / 3) ^ 2 / 2 = 2 * (1 - c) ^ 2 / 9 := by
  refine ⟨fun q => ?_, by ring, by ring⟩
  nlinarith [sq_nonneg (q - (1 - c) / 3)]

/-- Whether firm `j` (`false` = firm 1, `true` = firm 2) is awarded production rights in the
market structure `y`. -/
def dsProduces (y : Bool × Bool) (j : Bool) : Bool := if j then y.2 else y.1

/-- The Cournot gross profit of firm `j` in market structure `y` (Exercise 23.F.7). -/
noncomputable def dsGross (c : ℝ) (y : Bool × Bool) (j : Bool) : ℝ :=
  if dsProduces y j then (if y.1 && y.2 then (1 - c) ^ 2 / 9 else (1 - c) ^ 2 / 4) else 0

/-- Consumer surplus in market structure `y` (Exercise 23.F.7). -/
noncomputable def dsSurplus (c : ℝ) (y : Bool × Bool) : ℝ :=
  if y.1 && y.2 then 2 * (1 - c) ^ 2 / 9 else if y.1 || y.2 then (1 - c) ^ 2 / 8 else 0

/-- A firm's virtual cost in Exercise 23.F.7, `λθ + (λ - 1)Φ(θ)/φ(θ)`: the expected welfare cost
of letting a firm with fixed cost `θ` produce when transfers carry shadow cost `λ > 1`. -/
noncomputable def dsVirtualCost (D : TypeDensity) (lam θ : ℝ) : ℝ :=
  lam * θ + (lam - 1) * (D.cdf θ / D.dens θ)

/-- The planner's virtual welfare of market structure `y` given the firms' virtual costs `vc`:
`S(y) + ∑_{j producing} (λπⱼ(y) - vcⱼ)`. -/
noncomputable def dsVirtualWelfare (c lam : ℝ) (vc : Bool → ℝ) (y : Bool × Bool) : ℝ :=
  dsSurplus c y + (if dsProduces y false then lam * dsGross c y false - vc false else 0) +
    (if dsProduces y true then lam * dsGross c y true - vc true else 0)

/-- **Exercise 23.F.7** (MWG, p. 924): with `λ > 1` and `Φ/φ` increasing the virtual cost is
strictly increasing in the fixed cost. -/
theorem dsVirtualCost_strictMono (D : TypeDensity) {lam : ℝ} (hlam : 1 < lam)
    (hΦ : MonotoneOn (fun θ => D.cdf θ / D.dens θ) (Set.Icc D.lo D.hi)) :
    StrictMonoOn (dsVirtualCost D lam) (Set.Icc D.lo D.hi) := by
  intro a ha b hb hab
  have := hΦ ha hb hab.le
  simp only [dsVirtualCost] at this ⊢
  nlinarith

/-- **Exercise 23.F.7** (MWG, p. 924), the characterisation of the optimal auction of production
rights at each profile: the market structure maximises the virtual welfare
`S(y) + ∑_{j producing}(λπⱼ(y) - λθⱼ - (λ - 1)Φ(θⱼ)/φ(θⱼ))` (`dsVirtualWelfare`), and this rule
satisfies the monotonicity required by incentive compatibility: if `y*` is optimal at virtual
costs `vc` and awards rights to firm `j`, then after lowering `j`'s virtual cost (the other
firm's unchanged) no structure excluding `j` does better than `y*`. -/
theorem exercise_23_F_7 (c lam : ℝ) {vc vc' : Bool → ℝ} {j : Bool} (hj : vc' j ≤ vc j)
    (hother : vc' (!j) = vc (!j)) {ys : Bool × Bool}
    (hopt : ∀ y, dsVirtualWelfare c lam vc y ≤ dsVirtualWelfare c lam vc ys)
    (hys : dsProduces ys j = true) {y : Bool × Bool} (hy : dsProduces y j = false) :
    dsVirtualWelfare c lam vc' y ≤ dsVirtualWelfare c lam vc' ys := by
  have h := hopt y
  cases j <;> simp only [Bool.not_false, Bool.not_true] at hother <;>
    simp only [dsVirtualWelfare, hys, hy, ite_true, hother] at h ⊢ <;>
    split_ifs at h ⊢ <;> linarith

end MWG.MechanismDesign
