/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Several
import MWGEquilibriumTime.Euler
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Overlapping generations (MWG Section 20.H, pp. 769-777)

MWG, Chapter 20, Section 20.H and Exercise 20.H.1 (p. 786). One good per period; generation `t`
lives at `t` (young, consumption `c_{bt}`) and `t + 1` (old, `c_{at}`) with utility
`u(c_b, c_a)` (a function on `ℝ × ℝ`), is endowed with `1 - ε` when young, and generation `0` owns
the asset paying `ε` per period plus a bubble `M ≥ 0`.

* The budget constraints (20.H.1)-(20.H.2) (`olgWealth`) and **Definition 20.H.1** (`OLGEq`), with
  a proved instance (`olg_autarky_linear`).
* The fundamental value of the asset is a lower bound for its no-arbitrage price
  (`fundamental_value_bound`, footnote 34).
* The steady state of Figure 20.H.1: `α = (1 - ε - γ)/(1 - γ) < 1` (`olg_steady_alpha`).
* **Proposition 20.H.1** (`proposition_20_H_1`) and **Proposition 20.H.2** (`proposition_20_H_2`).
* The nominal case: `p_{t+1} c_{at} = M` (`olg_nominal_identity`), so `M = 0` exactly at the
  no-trade equilibrium (`olg_bubble_zero_iff_autarky`); autarky is an equilibrium
  (`olg_autarky_equilibrium`) and, when the marginal rate of substitution at `(1, 0)` is below
  one, it is strictly Pareto dominated (`olg_autarky_dominated`).
* **Exercise 20.H.1**: no bubbles with finitely many consumers (`exercise_20_H_1`).
* The backward shift: a linear onto map of sequences with a nonzero kernel (`backward_shift`).
* Correction: in the monetary steady state the price sequence is constant only from `t = 1`
  (generation 0's choice fixes `p_1/p_0`; `monetary_steady_state_prices_log`).

The module `Closer20H` proves the optimality of the monetary steady state, the bubble
characterization of optimal nominal equilibria and Exercise 20.H.2(b) in the `√b + √a` economy,
and the cycles of Figures 20.H.5-20.H.6. OPEN: existence of equilibrium (Wilson 1981), the
general determinacy analysis (20.H.3) and Exercise 20.H.2(a), (c), (d).
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- The wealth of generation `t` (MWG, (20.H.1)-(20.H.2)): `(1 - ε) p_t` for `t > 0`, and for
generation `0` also the asset at its fundamental value `ε ∑_t p_t` plus the bubble `M`. -/
noncomputable def olgWealth (ε M : ℝ) (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then (1 - ε) * p 0 + ε * ∑' s, p s + M else (1 - ε) * p t

/-- **Definition 20.H.1** (MWG, p. 771): positive prices `p`, a bubble `M ≥ 0` and consumptions
`(c_{bt}, c_{at})` form a Walrasian equilibrium if every generation maximizes `u` on its budget set
and `c_{a,t-1} + c_{bt} = 1` (with `c_{a,-1} = 0`). Departures: prices are positive, and for a
real asset (`ε > 0`) the value `∑_t p_t` is finite (MWG, p. 773: otherwise generation 0 cannot be
in equilibrium). -/
structure OLGEq (u : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℕ → ℝ) (M : ℝ) (cb ca : ℕ → ℝ) : Prop where
  /-- Prices are positive. -/
  pricesPos : ∀ t, 0 < p t
  /-- The bubble is nonnegative. -/
  bubble_nonneg : 0 ≤ M
  /-- A real asset has finite value. -/
  assetFinite : 0 < ε → Summable p
  /-- Consumption is nonnegative. -/
  cons_nonneg : ∀ t, 0 ≤ cb t ∧ 0 ≤ ca t
  /-- The budget constraint holds. -/
  budget : ∀ t, p t * cb t + p (t + 1) * ca t ≤ olgWealth ε M p t
  /-- Utility maximization. -/
  optimal : ∀ t b a, 0 ≤ b → 0 ≤ a → p t * b + p (t + 1) * a ≤ olgWealth ε M p t →
    u (b, a) ≤ u (cb t, ca t)
  /-- Feasibility at `t = 0`. -/
  feasible_zero : cb 0 = 1
  /-- Feasibility at `t + 1`. -/
  feasible : ∀ t, ca t + cb (t + 1) = 1

/-- **Footnote 34** (MWG, p. 771): if the asset's prices `A_t` (paid by the young at `t`) admit no
arbitrage, `A_t ≥ ε p_{t+1} + A_{t+1}` and `A ≥ 0`, then `A_0 ≥ ε (p_1 + ... + p_n)` for every
`n`; hence the value `ε p_0 + A_0` to generation 0 is at least the fundamental value `ε ∑_t p_t`. -/
theorem fundamental_value_bound {ε : ℝ} (hε : 0 ≤ ε) {p A : ℕ → ℝ} (hp : ∀ t, 0 ≤ p t)
    (hA : ∀ t, 0 ≤ A t) (hnoarb : ∀ t, ε * p (t + 1) + A (t + 1) ≤ A t) :
    (∀ n, ε * ∑ s ∈ Finset.range n, p (s + 1) ≤ A 0) ∧
      (Summable p → ε * ∑' s, p s ≤ ε * p 0 + A 0) := by
  have hgen : ∀ n t, ε * ∑ s ∈ Finset.range n, p (t + s + 1) + A (t + n) ≤ A t := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have h1 := ih (t + 1)
      have h2 := hnoarb t
      rw [Finset.sum_range_succ']
      simp only [show ∀ s, t + 1 + s + 1 = t + (s + 1) + 1 by omega,
        show t + 1 + n = t + (n + 1) by omega] at h1
      simp only [add_zero]
      nlinarith
  have hfin : ∀ n, ε * ∑ s ∈ Finset.range n, p (s + 1) ≤ A 0 := fun n => by
    have := hgen n 0
    simp only [zero_add] at this
    linarith [hA n]
  refine ⟨hfin, fun hs => ?_⟩
  have hs1 : Summable fun s => p (s + 1) := (summable_nat_add_iff 1).2 hs
  have hle : ∑' s, p (s + 1) ≤ A 0 / ε ∨ ε = 0 := by
    rcases eq_or_lt_of_le hε with h | h
    · exact Or.inr h.symm
    · left
      exact Real.tsum_le_of_sum_range_le (fun s => hp (s + 1)) fun n => by
        rw [le_div_iff₀ h]; linarith [hfin n]
  rw [hs.tsum_eq_zero_add]
  rcases hle with h | h
  · rcases eq_or_lt_of_le hε with h0 | h0
    · subst h0; simpa using hA 0
    · rw [le_div_iff₀ h0] at h; nlinarith
  · subst h; simpa using hA 0

/-- **The steady state of Figure 20.H.1** (MWG, p. 772): generations `t ≥ 1` consuming `(γ, 1 - γ)`
at prices `p_t = α^t` exhaust their budgets `(1 - ε) p_t` exactly when
`α = (1 - ε - γ)/(1 - γ)`, and `α < 1` when `ε > 0`. -/
theorem olg_steady_alpha {ε γ α : ℝ} (hγ : γ < 1) (t : ℕ) (hαpos : 0 < α) :
    (α ^ t * γ + α ^ (t + 1) * (1 - γ) = (1 - ε) * α ^ t ↔ α = (1 - ε - γ) / (1 - γ)) ∧
      (0 < ε → (1 - ε - γ) / (1 - γ) < 1) := by
  have h1γ : (1 : ℝ) - γ ≠ 0 := by linarith
  have hαt : 0 < α ^ t := pow_pos hαpos t
  constructor
  · rw [eq_div_iff h1γ, pow_succ]
    constructor
    · intro h
      have : α ^ t * (γ + α * (1 - γ) - (1 - ε)) = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hαt.ne'
      linarith
    · intro h
      have : α * (1 - γ) = 1 - ε - γ := h
      nlinarith
  · intro hε
    rw [div_lt_one (by linarith)]
    linarith

/-- The budget of an OLG generation binds when `u` is strictly increasing in first-period
consumption. -/
theorem olg_budget_binds {u : ℝ × ℝ → ℝ} (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a))
    {ε : ℝ} {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (t : ℕ) :
    p t * cb t + p (t + 1) * ca t = olgWealth ε M p t := by
  refine le_antisymm (he.budget t) ?_
  by_contra hlt
  push Not at hlt
  set gap := olgWealth ε M p t - (p t * cb t + p (t + 1) * ca t)
  have hgap : 0 < gap := by simp only [gap]; linarith
  have hpt := he.pricesPos t
  have := he.optimal t (cb t + gap / p t) (ca t) (by
    have := (he.cons_nonneg t).1; have := div_pos hgap hpt; linarith) (he.cons_nonneg t).2 (by
    rw [mul_add, mul_div_cancel₀ _ hpt.ne']; simp only [gap]; linarith)
  have hlt' := hmono (cb t) (cb t + gap / p t) (ca t) (he.cons_nonneg t).1
    (by have := div_pos hgap hpt; linarith)
  linarith

/-- A bundle that is at least as good as the optimum costs at least the wealth (local
nonsatiation in first-period consumption). -/
theorem olg_cost_ge {u : ℝ × ℝ → ℝ} (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a))
    {ε : ℝ} {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (t : ℕ) {b a : ℝ}
    (hb : 0 ≤ b) (ha : 0 ≤ a) (hge : u (cb t, ca t) ≤ u (b, a)) :
    olgWealth ε M p t ≤ p t * b + p (t + 1) * a := by
  by_contra hlt
  push Not at hlt
  set gap := olgWealth ε M p t - (p t * b + p (t + 1) * a)
  have hgap : 0 < gap := by simp only [gap]; linarith
  have hpt := he.pricesPos t
  have := he.optimal t (b + gap / p t) a (by have := div_pos hgap hpt; linarith) ha (by
    rw [mul_add, mul_div_cancel₀ _ hpt.ne']; simp only [gap]; linarith)
  have := hmono b (b + gap / p t) a hb (by have := div_pos hgap hpt; linarith)
  linarith

/-- A strictly better bundle costs strictly more than the wealth. -/
theorem olg_cost_gt {u : ℝ × ℝ → ℝ} {ε : ℝ} {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq u ε p M cb ca) (t : ℕ) {b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hgt : u (cb t, ca t) < u (b, a)) : olgWealth ε M p t < p t * b + p (t + 1) * a := by
  by_contra hle
  push Not at hle
  exact absurd (he.optimal t b a hb ha hle) (not_le.2 hgt)

/-- The total wealth of all generations is `∑_t p_t + M` when `∑_t p_t < ∞`. -/
theorem olg_total_wealth {ε M : ℝ} {p : ℕ → ℝ} (hs : Summable p) :
    HasSum (olgWealth ε M p) (∑' t, p t + M) := by
  have hsum : Summable fun t => (1 - ε) * p t := hs.mul_left _
  have h := hsum.hasSum.add (hasSum_ite_eq 0 (ε * ∑' s, p s + M))
  have heq : (1 - ε) * ∑' t, p t + (ε * ∑' s, p s + M) = ∑' t, p t + M := by ring
  rw [tsum_mul_left, heq] at h
  refine h.congr_fun fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp [olgWealth]; ring
  · simp [olgWealth, ht]

/-- **Proposition 20.H.1** (MWG, p. 773): an equilibrium with `∑_t p_t < ∞` is Pareto optimal: no
feasible consumptions (`c'_{b0} ≤ 1`, `c'_{at} + c'_{b,t+1} ≤ 1`) make every generation at least as
well off and one strictly better off. `u` is strictly increasing in first-period consumption. -/
theorem proposition_20_H_1 {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {ε : ℝ} {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (hs : Summable p) :
    ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
      (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧ (∀ t, u (cb t, ca t) ≤ u (cb' t, ca' t)) ∧
      ∃ s, u (cb s, ca s) < u (cb' s, ca' s) := by
  rintro ⟨cb', ca', hnn, h0, hfeas, hge, s, hs'⟩
  have hp := he.pricesPos
  -- the costs `p_t c'_{bt} + p_{t+1} c'_{at}`
  set cost : ℕ → ℝ := fun t => p t * cb' t + p (t + 1) * ca' t with hcost
  have hcost0 : ∀ t, 0 ≤ cost t := fun t =>
    add_nonneg (mul_nonneg (hp t).le (hnn t).1) (mul_nonneg (hp (t + 1)).le (hnn t).2)
  -- partial sums of the costs are bounded by `∑ p`
  have hpart : ∀ T, ∑ t ∈ Finset.range T, cost t ≤ ∑' t, p t := by
    intro T
    have hle : ∀ T, ∑ t ∈ Finset.range T, cost t
        ≤ ∑ t ∈ Finset.range (T + 1), p t - p T * cb' T := by
      intro T
      induction T with
      | zero => simp; nlinarith [hp 0, h0]
      | succ T ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => p t) (T + 1)]
        have := hfeas T
        have hpT1 := hp (T + 1)
        simp only [hcost]
        nlinarith [mul_le_mul_of_nonneg_left this hpT1.le, (hnn (T + 1)).1]
    calc ∑ t ∈ Finset.range T, cost t ≤ ∑ t ∈ Finset.range (T + 1), p t - p T * cb' T := hle T
      _ ≤ ∑ t ∈ Finset.range (T + 1), p t := by
          linarith [mul_nonneg (hp T).le (hnn T).1]
      _ ≤ ∑' t, p t := hs.sum_le_tsum _ (fun t _ => (hp t).le)
  have hcs : Summable cost := summable_of_sum_range_le hcost0 hpart
  have hcle : ∑' t, cost t ≤ ∑' t, p t := Real.tsum_le_of_sum_range_le hcost0 hpart
  -- costs are at least the wealths, strictly for `s`
  have hw := olg_total_wealth (ε := ε) (M := M) hs
  have hge' : ∀ t, olgWealth ε M p t ≤ cost t := fun t =>
    olg_cost_ge hmono he t (hnn t).1 (hnn t).2 (hge t)
  have hgt' : olgWealth ε M p s < cost s := olg_cost_gt he s (hnn s).1 (hnn s).2 hs'
  have := hasSum_lt hge' hgt' hw hcs.hasSum
  linarith [he.bubble_nonneg]

/-- The value of total consumption up to `T`: `∑_{t ≤ T} (p_t c_{bt} + p_{t+1} c_{at}) =
∑_{t ≤ T} p_t + p_{T+1} c_{aT}`, by feasibility. -/
theorem olg_consumption_value {p cb ca : ℕ → ℝ} (h0 : cb 0 = 1) (hf : ∀ t, ca t + cb (t + 1) = 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (p t * cb t + p (t + 1) * ca t)
      = ∑ t ∈ Finset.range (T + 1), p t + p (T + 1) * ca T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun t => p t) (T + 1)]
    have := hf T
    have e : cb (T + 1) = 1 - ca T := by linarith
    rw [e]
    ring

/-- **Proposition 20.H.2** (MWG, p. 775): at an equilibrium with `∑_t p_t < ∞` there is no
bubble, `M = 0`: total wealth `∑ p_t + M` is spent, and total consumption is worth `∑ p_t`. -/
theorem proposition_20_H_2 {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {ε : ℝ} {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (hs : Summable p) : M = 0 := by
  have hbind := olg_budget_binds hmono he
  have hw := olg_total_wealth (ε := ε) (M := M) hs
  have hp := he.pricesPos
  have hca1 : ∀ t, ca t ≤ 1 := fun t => by
    have := he.feasible t; linarith [(he.cons_nonneg (t + 1)).1]
  have hcons : HasSum (fun t => p t * cb t + p (t + 1) * ca t) (∑' t, p t) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun t => add_nonneg
      (mul_nonneg (hp t).le (he.cons_nonneg t).1) (mul_nonneg (hp (t + 1)).le
        (he.cons_nonneg t).2)) _).2 ?_
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    have h1 := (hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun T => p (T + 1) * ca T) atTop (𝓝 0) := by
      have hp0 := ((summable_nat_add_iff 1).2 hs).tendsto_atTop_zero
      refine squeeze_zero_norm (fun T => ?_) hp0
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hp (T + 1)), abs_of_nonneg (he.cons_nonneg T).2]
      exact mul_le_of_le_one_right (hp (T + 1)).le (hca1 T)
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr fun T => (olg_consumption_value he.feasible_zero he.feasible T).symm
  have := hw.unique (hcons.congr_fun fun t => (hbind t).symm)
  linarith

/-! ### The purely nominal asset -/

/-- **The nominal identity** (MWG, p. 774): with a purely nominal asset (`ε = 0`) and binding
budgets, `p_{t+1} c_{at} = p_t (1 - c_{bt}) = p_t c_{a,t-1} = ⋯ = M` for every `t`. -/
theorem olg_nominal_identity {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u 0 p M cb ca) (t : ℕ) : p (t + 1) * ca t = M := by
  have hbind := olg_budget_binds hmono he
  induction t with
  | zero =>
    have := hbind 0
    simp [olgWealth, he.feasible_zero] at this
    linarith
  | succ t ih =>
    have := hbind (t + 1)
    simp only [olgWealth, show t + 1 ≠ 0 by omega, ↓reduceIte, sub_zero, one_mul] at this
    have hf := he.feasible t
    have e : cb (t + 1) = 1 - ca t := by linarith
    rw [e] at this
    nlinarith

/-- **`M = 0` only at the no-trade equilibrium** (MWG, p. 774): in the nominal case, the bubble
vanishes if and only if no generation consumes when old (and every generation consumes its
endowment `1` when young). -/
theorem olg_bubble_zero_iff_autarky {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u 0 p M cb ca) :
    M = 0 ↔ (∀ t, ca t = 0) ∧ ∀ t, cb t = 1 := by
  have hid := olg_nominal_identity hmono he
  constructor
  · intro hM
    have hca : ∀ t, ca t = 0 := fun t => by
      have := hid t
      rw [hM] at this
      exact (mul_eq_zero.1 this).resolve_left (he.pricesPos (t + 1)).ne'
    refine ⟨hca, fun t => ?_⟩
    cases t with
    | zero => exact he.feasible_zero
    | succ t => have := he.feasible t; rw [hca t] at this; linarith
  · rintro ⟨hca, -⟩
    have := hid 0
    rw [hca 0, mul_zero] at this
    exact this.symm

/-- **The no-trade (nonmonetary) steady state is an equilibrium** (MWG, p. 773): if `u` is concave
on `ℝ²_+`, differentiable at `(1, 0)` with marginal utilities `u_b, u_a > 0`, and `β = u_b/u_a`
is the marginal rate of substitution there, then `M = 0`, the prices `p_t = β^{-t}` (so
`p_t / p_{t+1} = β`) and autarky `(1, 0)` form an equilibrium with a purely nominal asset. -/
theorem olg_autarky_equilibrium {u : ℝ × ℝ → ℝ}
    (hconc : ConcaveOn ℝ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} u) {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt u D (1, 0)) {ub ua : ℝ} (hub : 0 < ub) (hua : 0 < ua)
    (hDf : ∀ v w, D (v, w) = ub * v + ua * w) :
    OLGEq u 0 (fun t => (ub / ua)⁻¹ ^ t) 0 (fun _ => 1) (fun _ => 0) := by
  have hβ : 0 < ub / ua := div_pos hub hua
  refine ⟨fun t => pow_pos (inv_pos.2 hβ) t, le_rfl, fun h => absurd h (lt_irrefl 0),
    fun t => ⟨zero_le_one, le_rfl⟩, fun t => ?_, fun t b a hb ha hbud => ?_, rfl,
    fun t => by norm_num⟩
  · rcases eq_or_ne t 0 with rfl | ht <;> simp [olgWealth, *]
  · have hw : olgWealth 0 0 (fun t => (ub / ua)⁻¹ ^ t) t = (ub / ua)⁻¹ ^ t := by
      rcases eq_or_ne t 0 with rfl | ht <;> simp [olgWealth, *]
    rw [hw] at hbud
    have hpt : 0 < (ub / ua)⁻¹ ^ t := pow_pos (inv_pos.2 hβ) t
    -- the budget is `b + (ua/ub) a ≤ 1`
    have hbud' : b + ua / ub * a ≤ 1 := by
      have : (ub / ua)⁻¹ ^ t * (b + ua / ub * a) ≤ (ub / ua)⁻¹ ^ t * 1 := by
        rw [pow_succ] at hbud
        have : (ub / ua)⁻¹ = ua / ub := inv_div ub ua
        rw [this] at hbud ⊢
        nlinarith
      exact le_of_mul_le_mul_left this hpt
    have g := concave_le_fderiv_normed hconc (by simp) (show (b, a) ∈ _ from ⟨hb, ha⟩) hD
    rw [Prod.mk_sub_mk, hDf] at g
    have : ub * (b - 1) + ua * (a - 0) ≤ 0 := by
      have h' : ua * a = ub * (ua / ub * a) := by field_simp
      nlinarith
    simpa using g.trans (by linarith)

/-- A proved instance of `OLGEq`: `u(b, a) = b + 2a`, autarky at prices `p_t = 2^t`. -/
theorem olg_autarky_linear :
    OLGEq (fun x => x.1 + 2 * x.2) 0 (fun t => (1 / 2 : ℝ)⁻¹ ^ t) 0 (fun _ => 1) (fun _ => 0) := by
  have hD : HasFDerivAt (fun x : ℝ × ℝ => x.1 + 2 * x.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ + (2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) :=
    hasFDerivAt_fst.add (hasFDerivAt_snd.const_mul 2)
  have h := olg_autarky_equilibrium (u := fun x : ℝ × ℝ => x.1 + 2 * x.2)
    ((LinearMap.fst ℝ ℝ ℝ + (2 : ℝ) • LinearMap.snd ℝ ℝ ℝ).concaveOn
      (by
        intro x hx y hy a b ha hb hab
        simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul] at *
        constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]))
    hD one_pos two_pos (fun v w => by simp)
  simpa using h

/-- **Autarky is Pareto dominated when `β < 1`** (MWG, p. 773, Figure 20.H.2): if `u` is strictly
increasing in second-period consumption and differentiable at `(1, 0)` with `u_a > u_b`, then for
some `x ∈ (0, 1)` the feasible allocation in which generation 0 consumes `(1, x)` and every other
generation `(1 - x, x)` makes every generation strictly better off than autarky. -/
theorem olg_autarky_dominated {u : ℝ × ℝ → ℝ}
    (hmono_a : ∀ b a a', 0 ≤ a → a < a' → u (b, a) < u (b, a')) {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt u D (1, 0)) {ub ua : ℝ} (hDf : ∀ v w, D (v, w) = ub * v + ua * w)
    (hβ : ub < ua) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ u (1, 0) < u (1, x) ∧ u (1, 0) < u (1 - x, x) := by
  have hline : HasDerivAt (fun x : ℝ => ((1 - x, x) : ℝ × ℝ)) (-1, 1) 0 :=
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).prodMk (hasDerivAt_id 0)
      |>.congr_deriv (by simp)
  have hd : HasDerivAt (fun x => u (1 - x, x) - u (1, 0)) (ua - ub) 0 := by
    have := (hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).sub_const (u (1, 0))
    rw [hDf] at this
    exact this.congr_deriv (by ring)
  have hev := eventually_pos_of_hasDerivAt hd (by simp) (by linarith)
  have hlt1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  obtain ⟨x, hx, hx1, hxpos⟩ := (hev.and (hlt1.and self_mem_nhdsWithin)).exists
  refine ⟨x, hxpos, hx1, hmono_a 1 0 x le_rfl hxpos, ?_⟩
  linarith

/-- **Correction on the monetary steady state** (MWG, p. 774): with `u(b, a) = ln b + ln a` the
monetary steady state has generations `t ≥ 1` consuming `(1/2, 1/2)` at constant prices, but
generation 0 must consume `(1, 1/2)`, and its optimality forces `p₁ = 2 p₀`: the price sequence is
constant only from `t = 1` on. Precisely, if `(1, 1/2)` maximizes `ln b + ln a` on
`{b, a > 0 : p₀ b + p₁ a ≤ p₀ + p₁/2}`, then `p₁ = 2 p₀`. -/
theorem monetary_steady_state_prices_log {p₀ p₁ : ℝ}
    (hopt : ∀ b a, 0 < b → 0 < a → p₀ * b + p₁ * a ≤ p₀ * 1 + p₁ * (1 / 2) →
      Real.log b + Real.log a ≤ Real.log 1 + Real.log (1 / 2)) : p₁ = 2 * p₀ := by
  -- move along the budget line `b = 1 + s p₁`, `a = 1/2 - s p₀`
  have h1 : HasDerivAt (fun s : ℝ => 1 + s * p₁) p₁ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const p₁).const_add 1
    simp only [id, one_mul] at this
    exact this
  have h2 : HasDerivAt (fun s : ℝ => 1 / 2 - s * p₀) (-p₀) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const p₀).const_sub (1 / 2)
    simp only [id, one_mul] at this
    exact this
  have hd : HasDerivAt (fun s => Real.log (1 + s * p₁) + Real.log (1 / 2 - s * p₀))
      (p₁ - 2 * p₀) 0 := by
    have := ((Real.hasDerivAt_log (by norm_num : (1 + 0 * p₁ : ℝ) ≠ 0)).comp 0 h1).add
      ((Real.hasDerivAt_log (by norm_num : (1 / 2 - 0 * p₀ : ℝ) ≠ 0)).comp 0 h2)
    exact this.congr_deriv (by norm_num; ring)
  set φ : ℝ → ℝ := fun s => Real.log (1 + s * p₁) + Real.log (1 / 2 - s * p₀) with hφ
  have hloc : IsLocalMax φ 0 := by
    have c1 : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < 1 + s * p₁ :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually
        (lt_mem_nhds (by norm_num))
    have c2 : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < 1 / 2 - s * p₀ :=
      (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.eventually
        (lt_mem_nhds (by norm_num))
    filter_upwards [c1, c2] with s h1 h2
    have := hopt _ _ h1 h2 (by nlinarith)
    simpa [hφ] using this
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **The backward shift** (MWG, p. 777): `f(x)_t = x_{t+1}` is linear and maps bounded sequences
onto bounded sequences, yet `f(x) = 0` has the nonzero bounded solution `(1, 0, 0, ...)`: an onto
linear map of an infinite-dimensional space need not be injective. -/
theorem backward_shift :
    let f : (ℕ → ℝ) → ℕ → ℝ := fun x t => x (t + 1)
    IsLinearMap ℝ f ∧
      (∀ y : ℕ → ℝ, (∃ B, ∀ t, |y t| ≤ B) → ∃ x : ℕ → ℝ, (∃ B, ∀ t, |x t| ≤ B) ∧ f x = y) ∧
      ∃ x : ℕ → ℝ, x ≠ 0 ∧ (∃ B, ∀ t, |x t| ≤ B) ∧ f x = 0 := by
  intro f
  refine ⟨⟨fun x y => rfl, fun c x => rfl⟩, fun y ⟨B, hB⟩ => ?_, ?_⟩
  · refine ⟨fun t => if t = 0 then 0 else y (t - 1), ⟨max B 0, fun t => ?_⟩, ?_⟩
    · change |(if t = 0 then 0 else y (t - 1))| ≤ max B 0
      split_ifs
      · simp
      · exact (hB _).trans (le_max_left _ _)
    · funext t; simp [f]
  · refine ⟨fun t => if t = 0 then 1 else 0, fun h => ?_, ⟨1, fun t => ?_⟩, ?_⟩
    · have := congrFun h 0; simp at this
    · change |(if t = 0 then (1 : ℝ) else 0)| ≤ 1
      split_ifs <;> simp
    · funext t; simp [f]

/-- **Exercise 20.H.1** (MWG, p. 786): with finitely many consumers there are no bubbles. If the
consumers of Section 20.G had extra wealth `M_i ≥ 0` (all budgets binding:
`∑_t p_t · c_{it} = w_i + M_i`), feasibility, short-run profit maximization and truncation force
`M_i = 0` for every consumer. -/
theorem exercise_20_H_1 {L : ℕ} {ι : Type*} [Fintype ι] {Y : Set (ProdPlan (Fin L))}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)}
    (hmy : MyopicProfitMax Y p y) {ω c : ι → ℕ → Fin L → ℝ} {θ : ι → ℕ → ℝ}
    (hθ0 : ∀ i t, 0 ≤ θ i t) (hθ1 : ∀ t, ∑ i, θ i t = 1)
    (hπ : Summable (periodProfit p y)) (hω : ∀ i, Summable fun t => p t ⬝ᵥ ω i t)
    (hfeas : ∀ t, ∑ i, c i t = netOutput y t + ∑ i, ω i t) {Mb : ι → ℝ} (hM : ∀ i, 0 ≤ Mb i)
    (hbind : ∀ i, HasSum (fun t => p t ⬝ᵥ c i t) (wealthI θ p y ω i + Mb i)) :
    ∀ i, Mb i = 0 := by
  obtain ⟨hWs, hW⟩ := sum_wealthI hθ0 hθ1 hπ hω
  have htot : HasSum (fun t => p t ⬝ᵥ ∑ i, c i t) (∑ i, (wealthI θ p y ω i + Mb i)) := by
    have := hasSum_sum (s := Finset.univ) fun i _ => hbind i
    exact this.congr_fun fun t => by rw [dotProduct_sum]
  -- partial sums of the value of consumption are below those of wealth
  have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ ∑ i, c i t
      ≤ ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) := by
    intro T
    have h1 := sum_value_netOutput p y T
    have h2 : 0 ≤ p (T + 1) ⬝ᵥ (y T).2 := by
      have := hmy.2 T _ (htr _ (hmy.1 T))
      simp [periodProfit, planValue] at this
      linarith
    simp only [hfeas, dotProduct_add, Finset.sum_add_distrib] at h1 ⊢
    linarith
  have hle := le_of_tendsto_of_tendsto
    ((htot.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
    ((hWs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)) (Eventually.of_forall hpart)
  rw [← hW, Finset.sum_add_distrib] at hle
  have hsum0 : ∑ i, Mb i ≤ 0 := by linarith
  intro i
  have := Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  linarith [hM i]

end MWG.EquilibriumTime
