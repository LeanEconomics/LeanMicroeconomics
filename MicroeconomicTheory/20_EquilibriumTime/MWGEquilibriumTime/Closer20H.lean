/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.OLG
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Overlapping generations: optimality, bubbles and cycles (MWG Section 20.H)

MWG, Chapter 20, Section 20.H, p. 774 and Figure 20.H.3 ("the monetary steady state is Pareto
optimal. We will not give a rigorous proof of this").

The monetary steady state of the purely nominal economy (generation 0 consumes `(1, 1 - γ)`,
every later generation `(γ, 1 - γ)`) is Pareto optimal (`monetary_steady_state_optimal`) when
`u` is continuous on `ℝ²_+`, nondecreasing in first-period and strictly increasing in
second-period consumption, and `(γ, 1 - γ)` is the unique maximizer of `u` on
`{b + a ≤ 1}` (the budget set of a generation `t ≥ 1` at the constant steady-state prices,
which is the equilibrium condition of the steady state plus strict quasiconcavity).

The proof makes Figure 20.H.3's "unfeasible chain of compensations" precise. With
`d_t = c'_{at} - (1 - γ)` the extra old-age consumption of generation `t`, feasibility and
the uniqueness of the maximizer give `0 ≤ d_0 ≤ d_1 ≤ ⋯ ≤ γ`, and a strict improvement for some
generation makes some `d_s > 0`. The limit `D > 0` of `d_t` then gives, by continuity,
`u(γ - D, 1 - γ + D) ≥ u(γ, 1 - γ)` on the line `b + a = 1`, a contradiction.

A proved instance: `u(b, a) = √b + √a` with `γ = 1/2` (`sqrt_utility_unique_max`,
`monetary_steady_state_optimal_sqrt`).

**Optimal nominal equilibria and the bubble** (p. 774, "which we leave without proof"): in the
stationary economy `u(b, a) = √b + √a` with a purely nominal asset, an equilibrium is Pareto
optimal (`OLGParetoOptimal`) if and only if its real bubble `M/p_{t+1}` is bounded away from zero
(`olg_sqrt_optimal_iff_bubble`). Every equilibrium is either the monetary steady state or has
relative prices `r_k = p_{k+2}/p_{k+1}` with `r_{k+1} = r_k² + r_k - 1`, `r_0 > 1`, a vanishing real
bubble, and is Pareto dominated by the steady state (`olg_sqrt_classification`; demand:
`sqrt_demand`, `olg_sqrt_demand`). This economy satisfies the determinacy condition (20.H.3)
(`sqrt_determinacy_condition`), and its monetary steady state is the only Pareto optimal
nominal equilibrium: Exercise 20.H.2(b) for this economy (`exercise_20_H_2b_sqrt`).

**Cycles** (Figures 20.H.5-20.H.6, p. 777): explicit period-2 and period-3 equilibrium paths of the
nominal economy with concave, increasing, piecewise linear utilities
(`figure_20_H_5_period_two`, `figure_20_H_6_period_three`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- First-period consumption in the monetary steady state: `1` for generation 0, `γ` after. -/
noncomputable def monetaryCb (γ : ℝ) (t : ℕ) : ℝ := if t = 0 then 1 else γ

/-- **The monetary steady state is Pareto optimal** (MWG, p. 774, Figure 20.H.3). Let `u` be
continuous on `ℝ²_+`, nondecreasing in first-period consumption, strictly increasing in
second-period consumption, and let `(γ, 1 - γ)` be the unique maximizer of `u` on
`{(b, a) ≥ 0 : b + a ≤ 1}`. Then no feasible allocation (`c'_{b0} ≤ 1`,
`c'_{at} + c'_{b,t+1} ≤ 1`) makes every generation at least as well off as in the monetary
steady state (generation 0 at `(1, 1 - γ)`, generation `t ≥ 1` at `(γ, 1 - γ)`) and some
generation strictly better off. -/
theorem monetary_steady_state_optimal {u : ℝ × ℝ → ℝ} {γ : ℝ}
    (hcont : ContinuousOn u {x | 0 ≤ x.1 ∧ 0 ≤ x.2})
    (hmono_b : ∀ b b' a, 0 ≤ b → b ≤ b' → 0 ≤ a → u (b, a) ≤ u (b', a))
    (hmono_a : ∀ b a a', 0 ≤ b → 0 ≤ a → a < a' → u (b, a) < u (b, a'))
    (hmax : ∀ b a, 0 ≤ b → 0 ≤ a → b + a ≤ 1 → (b, a) ≠ (γ, 1 - γ) → u (b, a) < u (γ, 1 - γ)) :
    ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
      (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧
      (∀ t, u (monetaryCb γ t, 1 - γ) ≤ u (cb' t, ca' t)) ∧
      ∃ s, u (monetaryCb γ s, 1 - γ) < u (cb' s, ca' s) := by
  rintro ⟨cb', ca', hnn, h0, hfeas, hge, s, hs⟩
  -- a later generation at least as well off consumes at least `1` in total
  have hsum : ∀ t, u (γ, 1 - γ) ≤ u (cb' (t + 1), ca' (t + 1)) →
      1 ≤ cb' (t + 1) + ca' (t + 1) := fun t h => by
    by_contra hlt
    push Not at hlt
    have hne : (cb' (t + 1), ca' (t + 1)) ≠ (γ, 1 - γ) := fun he => by
      simp only [Prod.mk.injEq] at he
      linarith [he.1, he.2]
    linarith [hmax _ _ (hnn _).1 (hnn _).2 hlt.le hne]
  have hgeS : ∀ t, u (γ, 1 - γ) ≤ u (cb' (t + 1), ca' (t + 1)) := fun t => by
    simpa [monetaryCb] using hge (t + 1)
  -- generation 0 cannot lose old-age consumption
  have hca0 : 1 - γ ≤ ca' 0 := by
    by_contra hlt
    push Not at hlt
    have h1 := hmono_b _ _ _ (hnn 0).1 h0 (hnn 0).2
    have h2 := hmono_a 1 _ _ zero_le_one (hnn 0).2 hlt
    have h3 := hge 0
    simp only [monetaryCb, ↓reduceIte] at h3
    linarith
  -- the extra old-age consumption `d_t` is nondecreasing
  set d : ℕ → ℝ := fun t => ca' t - (1 - γ) with hd
  have hstep : ∀ t, d t ≤ d (t + 1) := fun t => by
    have := hsum t (hgeS t)
    have := hfeas t
    simp only [hd]
    linarith
  have hmono : Monotone d := monotone_nat_of_le_succ hstep
  have hd0 : 0 ≤ d 0 := by simp only [hd]; linarith
  have hdγ : ∀ t, d t ≤ γ - cb' (t + 1) := fun t => by
    have := hfeas t
    simp only [hd]
    linarith
  have hdle : ∀ t, d t ≤ γ := fun t => by linarith [hdγ t, (hnn (t + 1)).1]
  -- some `d_s` is positive
  have hpos : ∃ s, 0 < d s := by
    rcases s with _ | r
    · refine ⟨0, ?_⟩
      by_contra hle
      push Not at hle
      have hca : ca' 0 ≤ 1 - γ := by simp only [hd] at hle; linarith
      have h1 := hmono_b _ _ _ (hnn 0).1 h0 (hnn 0).2
      have h2 : u (1, ca' 0) ≤ u (1, 1 - γ) := by
        rcases eq_or_lt_of_le hca with h | h
        · rw [h]
        · exact (hmono_a 1 _ _ zero_le_one (hnn 0).2 h).le
      simp only [monetaryCb, ↓reduceIte] at hs
      linarith
    · refine ⟨r + 1, ?_⟩
      have hs' : u (γ, 1 - γ) < u (cb' (r + 1), ca' (r + 1)) := by
        simpa [monetaryCb] using hs
      have hgt : 1 < cb' (r + 1) + ca' (r + 1) := by
        by_contra hle
        push Not at hle
        rcases eq_or_ne (cb' (r + 1), ca' (r + 1)) (γ, 1 - γ) with he | hne
        · rw [he] at hs'; exact lt_irrefl _ hs'
        · linarith [hmax _ _ (hnn _).1 (hnn _).2 hle hne]
      have := hfeas r
      have := hmono (Nat.zero_le r)
      simp only [hd] at this ⊢
      linarith
  obtain ⟨s, hds⟩ := hpos
  -- the limit `D` of `d_t`
  have hbdd : BddAbove (Set.range d) := ⟨γ, by rintro _ ⟨t, rfl⟩; exact hdle t⟩
  set D := ⨆ t, d t with hD
  have hlim : Tendsto d atTop (𝓝 D) := tendsto_atTop_ciSup hmono hbdd
  have hDpos : 0 < D := lt_of_lt_of_le hds (le_ciSup hbdd s)
  have hDle : D ≤ γ := ciSup_le hdle
  -- every generation `t + 1` is at least as well off at `(γ - d_t, 1 - γ + d_{t+1})`
  have hpt : ∀ t, u (γ, 1 - γ) ≤ u (γ - d t, 1 - γ + d (t + 1)) := fun t => by
    have e : ca' (t + 1) = 1 - γ + d (t + 1) := by simp only [hd]; ring
    have h1 := hmono_b (cb' (t + 1)) (γ - d t) (ca' (t + 1)) (hnn _).1 (by linarith [hdγ t])
      (hnn _).2
    calc u (γ, 1 - γ) ≤ u (cb' (t + 1), ca' (t + 1)) := hgeS t
      _ ≤ u (γ - d t, ca' (t + 1)) := h1
      _ = u (γ - d t, 1 - γ + d (t + 1)) := by rw [e]
  -- pass to the limit
  have hseq : Tendsto (fun t => ((γ - d t, 1 - γ + d (t + 1)) : ℝ × ℝ)) atTop
      (𝓝 (γ - D, 1 - γ + D)) :=
    (tendsto_const_nhds.sub hlim).prodMk_nhds
      (tendsto_const_nhds.add (hlim.comp (tendsto_add_atTop_nat 1)))
  have hmem : ∀ t, ((γ - d t, 1 - γ + d (t + 1)) : ℝ × ℝ) ∈ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} :=
    fun t => ⟨by linarith [hdγ t, (hnn (t + 1)).1], by
      have := (hnn (t + 1)).2; simp only [hd] at this ⊢; linarith⟩
  have hDmem : ((γ - D, 1 - γ + D) : ℝ × ℝ) ∈ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} :=
    ⟨by simp only; linarith, by
      have h1 : d 0 ≤ D := le_ciSup hbdd 0
      have h2 : d 0 = ca' 0 - (1 - γ) := rfl
      simp only
      linarith [(hnn 0).2]⟩
  have hu : Tendsto (fun t => u (γ - d t, 1 - γ + d (t + 1))) atTop (𝓝 (u (γ - D, 1 - γ + D))) :=
    (hcont _ hDmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hseq, Eventually.of_forall hmem⟩)
  have hlimge : u (γ, 1 - γ) ≤ u (γ - D, 1 - γ + D) :=
    ge_of_tendsto hu (Eventually.of_forall hpt)
  have hne : ((γ - D, 1 - γ + D) : ℝ × ℝ) ≠ (γ, 1 - γ) := fun he => by
    simp only [Prod.mk.injEq] at he
    linarith [he.1]
  have := hmax _ _ hDmem.1 hDmem.2 (by linarith) hne
  linarith

/-- The instance `u(b, a) = √b + √a`: on `{(b, a) ≥ 0 : b + a ≤ 1}` it has the unique maximizer
`(1/2, 1/2)`. -/
theorem sqrt_utility_unique_max (b a : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hba : b + a ≤ 1)
    (hne : (b, a) ≠ (1 / 2, 1 - 1 / 2)) :
    Real.sqrt b + Real.sqrt a < Real.sqrt (1 / 2) + Real.sqrt (1 - 1 / 2) := by
  have sb := Real.sq_sqrt hb
  have sa := Real.sq_sqrt ha
  have s2 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hpos2 : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.2 (by norm_num)
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e] at hne ⊢
  -- `(√b + √a)² ≤ 2(b + a) ≤ 2`, with equality only at `b = a = 1/2`
  have hx := Real.sqrt_nonneg b
  have hy := Real.sqrt_nonneg a
  by_contra hge
  push Not at hge
  have hsq : 2 ≤ (Real.sqrt b + Real.sqrt a) ^ 2 := by nlinarith
  have heq : Real.sqrt b = Real.sqrt a := by nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a)]
  have hb2 : b = 1 / 2 := by nlinarith
  have ha2 : a = 1 / 2 := by nlinarith
  exact hne (by rw [hb2, ha2])

/-- **The monetary steady state is Pareto optimal**, proved instance (MWG, p. 774):
`u(b, a) = √b + √a`, `γ = 1/2`. -/
theorem monetary_steady_state_optimal_sqrt :
    ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
      (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧
      (∀ t, Real.sqrt (monetaryCb (1 / 2) t) + Real.sqrt (1 - 1 / 2)
        ≤ Real.sqrt (cb' t) + Real.sqrt (ca' t)) ∧
      ∃ s, Real.sqrt (monetaryCb (1 / 2) s) + Real.sqrt (1 - 1 / 2)
        < Real.sqrt (cb' s) + Real.sqrt (ca' s) :=
  monetary_steady_state_optimal (u := fun x => Real.sqrt x.1 + Real.sqrt x.2)
    ((Real.continuous_sqrt.comp continuous_fst).add
      (Real.continuous_sqrt.comp continuous_snd)).continuousOn
    (fun b b' a _ hbb' _ => by
      simp only
      linarith [Real.sqrt_le_sqrt hbb'])
    (fun b a a' _ ha haa' => by
      simp only
      linarith [Real.sqrt_lt_sqrt ha haa'])
    (fun b a hb ha hba hne => sqrt_utility_unique_max b a hb ha hba hne)

/-! ### A period-2 equilibrium path (Figure 20.H.5) -/

/-- The utility of the period-2 example: `u(b, a) = min(b + 2a, 2b + a - 1/4)`, concave,
piecewise linear and increasing (complementary consumptions, no inferior goods). Its kink line
`b = a + 1/4` is the offer curve for relative prices `p_{t+1}/p_t ∈ [1/2, 2]`. -/
noncomputable def cycleU (x : ℝ × ℝ) : ℝ := min (x.1 + 2 * x.2) (2 * x.1 + x.2 - 1 / 4)

/-- Old-age consumption on the period-2 path: `1/3` for even `t`, `5/12` for odd `t`. -/
noncomputable def cycleCa (t : ℕ) : ℝ := if t % 2 = 0 then 1 / 3 else 5 / 12

/-- Young-age consumption on the period-2 path: `1` for generation 0, then `1 - c_{a,t-1}`. -/
noncomputable def cycleCb (t : ℕ) : ℝ := if t = 0 then 1 else 1 - cycleCa (t - 1)

/-- The prices of the period-2 path: `1, 2, 8/5, 2, 8/5, ...`. -/
noncomputable def cyclePrice (t : ℕ) : ℝ := if t = 0 then 1 else if t % 2 = 0 then 8 / 5 else 2

/-- **Figure 20.H.5** (MWG, p. 777): a period-2 equilibrium path with complementary
consumptions, in the purely nominal case. With `u(b, a) = min(b + 2a, 2b + a - 1/4)`, the
prices `1, 2, 8/5, 2, 8/5, ...`, the bubble `M = 2/3` and generations alternating between
`(2/3, 5/12)` (odd `t`) and `(7/12, 1/3)` (even `t ≥ 2`) form an equilibrium (Definition 20.H.1)
whose allocation has period exactly 2. -/
theorem figure_20_H_5_period_two :
    OLGEq cycleU 0 cyclePrice (2 / 3) cycleCb cycleCa ∧
      (∀ t, 1 ≤ t → cycleCb (t + 2) = cycleCb t ∧ cycleCa (t + 2) = cycleCa t) ∧
      (cycleCb 1, cycleCa 1) ≠ (cycleCb 2, cycleCa 2) := by
  have hpar : ∀ t : ℕ, (t + 2) % 2 = t % 2 := fun t => by omega
  refine ⟨⟨fun t => ?_, by norm_num, fun h => absurd h (lt_irrefl 0), fun t => ?_,
    fun t => ?_, fun t b a hb ha hbud => ?_, by simp [cycleCb], fun t => ?_⟩, fun t ht => ?_, ?_⟩
  · unfold cyclePrice; split_ifs <;> norm_num
  · unfold cycleCb cycleCa; split_ifs <;> norm_num
  · rcases t with _ | t
    · simp [olgWealth, cyclePrice, cycleCb, cycleCa]; norm_num
    rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
    · have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * k) % 2 = 0 := by omega
      simp [olgWealth, cyclePrice, cycleCb, cycleCa, h1, h2, h3]; norm_num
    · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * k + 1 + 1 + 1) % 2 = 1 := by omega
      have h3 : (2 * k + 1) % 2 = 1 := by omega
      simp [olgWealth, cyclePrice, cycleCb, cycleCa, h1, h2, h3]; norm_num
  · have hu1 : cycleU (b, a) ≤ b + 2 * a := min_le_left _ _
    have hu2 : cycleU (b, a) ≤ 2 * b + a - 1 / 4 := min_le_right _ _
    rcases t with _ | t
    · simp [olgWealth, cyclePrice] at hbud
      have : cycleU (cycleCb 0, cycleCa 0) = 5 / 3 := by
        simp [cycleU, cycleCb, cycleCa]; norm_num
      rw [this]; linarith
    rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
    · have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * k) % 2 = 0 := by omega
      have hw : olgWealth 0 (2 / 3) cyclePrice (2 * k + 1) = 2 := by
        simp [olgWealth, cyclePrice, h1]
      have hp1 : cyclePrice (2 * k + 1) = 2 := by simp [cyclePrice, h1]
      have hp2 : cyclePrice (2 * k + 1 + 1) = 8 / 5 := by simp [cyclePrice, h2]
      rw [hw, hp1, hp2] at hbud
      have : cycleU (cycleCb (2 * k + 1), cycleCa (2 * k + 1)) = 3 / 2 := by
        simp [cycleU, cycleCb, cycleCa, h1, h3]; norm_num
      rw [this]; linarith
    · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * k + 1 + 1 + 1) % 2 = 1 := by omega
      have h3 : (2 * k + 1) % 2 = 1 := by omega
      have hw : olgWealth 0 (2 / 3) cyclePrice (2 * k + 1 + 1) = 8 / 5 := by
        simp [olgWealth, cyclePrice, h1]
      have hp1 : cyclePrice (2 * k + 1 + 1) = 8 / 5 := by simp [cyclePrice, h1]
      have hp2 : cyclePrice (2 * k + 1 + 1 + 1) = 2 := by simp [cyclePrice, h2]
      rw [hw, hp1, hp2] at hbud
      have : cycleU (cycleCb (2 * k + 1 + 1), cycleCa (2 * k + 1 + 1)) = 5 / 4 := by
        simp [cycleU, cycleCb, cycleCa, h1, h3]; norm_num
      rw [this]; linarith
  · simp [cycleCb]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have e1 : (s + 1 + 2) % 2 = (s + 1) % 2 := by omega
    have e2 : (s + 2) % 2 = s % 2 := by omega
    simp only [cycleCb, cycleCa, show s + 1 + 2 ≠ 0 by omega, show s + 1 ≠ 0 by omega,
      ↓reduceIte, show s + 1 + 2 - 1 = s + 2 by omega, show s + 1 - 1 = s by omega, e1, e2,
      and_self]
  · simp [cycleCb, cycleCa]
    norm_num

/-! ### A period-3 equilibrium path (Figure 20.H.6) -/

/-- The utility of the period-3 example: the minimum of four affine functions (concave,
piecewise linear and increasing), built by Afriat's construction from the four consumption
points of the path and their budget lines. -/
noncomputable def cycle3U (x : ℝ × ℝ) : ℝ :=
  min (min (min (24 * x.1 + 12 * x.2 - 27) (96 * x.1 + 288 * x.2 - 129))
    (48 * x.1 + 24 * x.2 - 51)) (144 * x.1 + 96 * x.2 - 149)

/-- Old-age consumption on the period-3 path: `1/4, 1/12, 1/6` according to `t mod 3`. -/
noncomputable def cycle3Ca (t : ℕ) : ℝ :=
  if t % 3 = 0 then 1 / 4 else if t % 3 = 1 then 1 / 12 else 1 / 6

/-- Young-age consumption on the period-3 path: `1` for generation 0, then `1 - c_{a,t-1}`. -/
noncomputable def cycle3Cb (t : ℕ) : ℝ := if t = 0 then 1 else 1 - cycle3Ca (t - 1)

/-- The prices of the period-3 path: `2`, then `1, 3, 3/2` according to `t mod 3 = 1, 2, 0`. -/
noncomputable def cycle3Price (t : ℕ) : ℝ :=
  if t = 0 then 2 else if t % 3 = 1 then 1 else if t % 3 = 2 then 3 else 3 / 2

/-- **Figure 20.H.6** (MWG, p. 777): a period-3 equilibrium path with complementary
consumptions, in the purely nominal case ("chaos rears its head"). With the piecewise linear
concave utility `cycle3U`, the bubble `M = 1/4` and the prices `2, 1, 3, 3/2, 1, 3, 3/2, ...`,
generations `t ≥ 1` cycle through `(3/4, 1/12)`, `(11/12, 1/6)`, `(5/6, 1/4)`: an equilibrium
(Definition 20.H.1) whose allocation has period exactly 3. -/
theorem figure_20_H_6_period_three :
    OLGEq cycle3U 0 cycle3Price (1 / 4) cycle3Cb cycle3Ca ∧
      (∀ t, 1 ≤ t → cycle3Cb (t + 3) = cycle3Cb t ∧ cycle3Ca (t + 3) = cycle3Ca t) ∧
      (cycle3Cb 1, cycle3Ca 1) ≠ (cycle3Cb 2, cycle3Ca 2) ∧
      (cycle3Cb 2, cycle3Ca 2) ≠ (cycle3Cb 3, cycle3Ca 3) ∧
      (cycle3Cb 1, cycle3Ca 1) ≠ (cycle3Cb 3, cycle3Ca 3) := by
  refine ⟨⟨fun t => ?_, by norm_num, fun h => absurd h (lt_irrefl 0), fun t => ?_,
    fun t => ?_, fun t b a hb ha hbud => ?_, by simp [cycle3Cb], fun t => ?_⟩, fun t ht => ?_,
    ?_, ?_, ?_⟩
  · unfold cycle3Price; split_ifs <;> norm_num
  · unfold cycle3Cb cycle3Ca; split_ifs <;> norm_num
  · rcases t with _ | t
    · simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca]
    have hc : (t + 1) % 3 = 0 ∨ (t + 1) % 3 = 1 ∨ (t + 1) % 3 = 2 := by omega
    rcases hc with h | h | h
    · have h1 : (t + 1 + 1) % 3 = 1 := by omega
      have h2 : t % 3 = 2 := by omega
      simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca, h, h1, h2]; norm_num
    · have h1 : (t + 1 + 1) % 3 = 2 := by omega
      have h2 : t % 3 = 0 := by omega
      simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca, h, h1, h2]; norm_num
    · have h1 : (t + 1 + 1) % 3 = 0 := by omega
      have h2 : t % 3 = 1 := by omega
      simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca, h, h1, h2]; norm_num
  · have hu0 : cycle3U (b, a) ≤ 24 * b + 12 * a - 27 :=
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    have hu1 : cycle3U (b, a) ≤ 96 * b + 288 * a - 129 :=
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have hu2 : cycle3U (b, a) ≤ 48 * b + 24 * a - 51 :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hu3 : cycle3U (b, a) ≤ 144 * b + 96 * a - 149 := min_le_right _ _
    rcases t with _ | t
    · have hw : olgWealth 0 (1 / 4) cycle3Price 0 = 9 / 4 := by
        simp [olgWealth, cycle3Price]; norm_num
      have hp1 : cycle3Price 0 = 2 := by simp [cycle3Price]
      have hp2 : cycle3Price (0 + 1) = 1 := by simp [cycle3Price]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb 0, cycle3Ca 0) = 0 := by
        simp [cycle3U, cycle3Cb, cycle3Ca]; norm_num
      rw [this]; linarith
    have hc : (t + 1) % 3 = 0 ∨ (t + 1) % 3 = 1 ∨ (t + 1) % 3 = 2 := by omega
    rcases hc with h | h | h
    · have h1 : (t + 1 + 1) % 3 = 1 := by omega
      have h2 : t % 3 = 2 := by omega
      have hw : olgWealth 0 (1 / 4) cycle3Price (t + 1) = 3 / 2 := by
        simp [olgWealth, cycle3Price, h]
      have hp1 : cycle3Price (t + 1) = 3 / 2 := by simp [cycle3Price, h]
      have hp2 : cycle3Price (t + 1 + 1) = 1 := by simp [cycle3Price, h1]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb (t + 1), cycle3Ca (t + 1)) = -5 := by
        simp [cycle3U, cycle3Cb, cycle3Ca, h, h2]; norm_num
      rw [this]; linarith
    · have h1 : (t + 1 + 1) % 3 = 2 := by omega
      have h2 : t % 3 = 0 := by omega
      have hw : olgWealth 0 (1 / 4) cycle3Price (t + 1) = 1 := by
        simp [olgWealth, cycle3Price, h]
      have hp1 : cycle3Price (t + 1) = 1 := by simp [cycle3Price, h]
      have hp2 : cycle3Price (t + 1 + 1) = 3 := by simp [cycle3Price, h1]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb (t + 1), cycle3Ca (t + 1)) = -33 := by
        simp [cycle3U, cycle3Cb, cycle3Ca, h, h2]; norm_num
      rw [this]; linarith
    · have h1 : (t + 1 + 1) % 3 = 0 := by omega
      have h2 : t % 3 = 1 := by omega
      have hw : olgWealth 0 (1 / 4) cycle3Price (t + 1) = 3 := by
        simp [olgWealth, cycle3Price, h]
      have hp1 : cycle3Price (t + 1) = 3 := by simp [cycle3Price, h]
      have hp2 : cycle3Price (t + 1 + 1) = 3 / 2 := by simp [cycle3Price, h1]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb (t + 1), cycle3Ca (t + 1)) = -3 := by
        simp [cycle3U, cycle3Cb, cycle3Ca, h, h2]; norm_num
      rw [this]; linarith
  · simp [cycle3Cb]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have e1 : (s + 1 + 3) % 3 = (s + 1) % 3 := by omega
    have e2 : (s + 3) % 3 = s % 3 := by omega
    simp only [cycle3Cb, cycle3Ca, show s + 1 + 3 ≠ 0 by omega, show s + 1 ≠ 0 by omega,
      ↓reduceIte, show s + 1 + 3 - 1 = s + 3 by omega, show s + 1 - 1 = s by omega, e1, e2,
      and_self]
  · simp [cycle3Cb, cycle3Ca]
  · simp [cycle3Cb, cycle3Ca]
  · simp [cycle3Cb, cycle3Ca]

/-! ### Optimal nominal equilibria have a bubble bounded away from zero -/

/-- Pareto optimality of an OLG allocation (as in Proposition 20.H.1): no feasible allocation
makes every generation at least as well off and one strictly better off. -/
def OLGParetoOptimal (u : ℝ × ℝ → ℝ) (cb ca : ℕ → ℝ) : Prop :=
  ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
    (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧ (∀ t, u (cb t, ca t) ≤ u (cb' t, ca' t)) ∧
    ∃ s, u (cb s, ca s) < u (cb' s, ca' s)

/-- The utility `u(b, a) = √b + √a` of the stationary example. -/
noncomputable def sqrtU (x : ℝ × ℝ) : ℝ := Real.sqrt x.1 + Real.sqrt x.2

/-- A proved instance of `OLGParetoOptimal`: the monetary steady state of `sqrtU`. -/
theorem olgParetoOptimal_monetary :
    OLGParetoOptimal sqrtU (monetaryCb (1 / 2)) (fun _ => 1 - 1 / 2) :=
  monetary_steady_state_optimal_sqrt

/-- The demand of `√b + √a` on the budget `b + r a ≤ 1`: the unique maximizer is
`(r/(1 + r), 1/(r(1 + r)))`. -/
theorem sqrt_demand {r b a : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (ha : 0 ≤ a) (hbud : b + r * a ≤ 1)
    (hopt : ∀ b' a', 0 ≤ b' → 0 ≤ a' → b' + r * a' ≤ 1 →
      Real.sqrt b' + Real.sqrt a' ≤ Real.sqrt b + Real.sqrt a) :
    b = r / (1 + r) ∧ a = 1 / (r * (1 + r)) := by
  have h1r : 0 < 1 + r := by linarith
  set as := 1 / (r * (1 + r)) with has
  have has0 : 0 < as := by rw [has]; positivity
  have hbs : r / (1 + r) = r ^ 2 * as := by rw [has]; field_simp
  have hsum : r ^ 2 * as + r * as = 1 := by rw [has]; field_simp; ring
  have hys := Real.sq_sqrt has0.le
  have hxs : Real.sqrt (r ^ 2 * as) = r * Real.sqrt as := by
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  have hval := hopt (r ^ 2 * as) as (by positivity) has0.le (by linarith)
  rw [hxs] at hval
  set x := Real.sqrt b with hx
  set y := Real.sqrt a with hy
  set ys := Real.sqrt as with hysd
  have hx2 : x ^ 2 = b := Real.sq_sqrt hb
  have hy2 : y ^ 2 = a := Real.sq_sqrt ha
  have hx0 : 0 ≤ x := Real.sqrt_nonneg b
  have hy0 : 0 ≤ y := Real.sqrt_nonneg a
  have hys0 : 0 ≤ ys := Real.sqrt_nonneg as
  -- `(1 + r) ≤ r (x + y)²` from optimality, `r (x + y)² + (x - r y)² ≤ 1 + r` from the budget
  have hlow : (1 + r) ≤ r * (x + y) ^ 2 := by
    have hsq : ((1 + r) * ys) ^ 2 ≤ (x + y) ^ 2 := by
      have : (1 + r) * ys ≤ x + y := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have : ((1 + r) * ys) ^ 2 = (1 + r) ^ 2 * as := by rw [mul_pow, hys]
    rw [this] at hsq
    have e : r * ((1 + r) ^ 2 * as) = 1 + r := by rw [has]; field_simp
    nlinarith
  have hident : r * (x + y) ^ 2 + (x - r * y) ^ 2 = (1 + r) * (x ^ 2 + r * y ^ 2) := by ring
  have hxy : x = r * y := by
    have : (x - r * y) ^ 2 ≤ 0 := by rw [hx2, hy2] at hident; nlinarith
    nlinarith [sq_nonneg (x - r * y)]
  have hbind : b + r * a = 1 := by
    rw [hx2, hy2] at hident
    have : (x - r * y) ^ 2 = 0 := by rw [hxy]; ring
    nlinarith
  have hba : b = r ^ 2 * a := by rw [← hx2, ← hy2, hxy]; ring
  have haeq : a = as := by
    have : (r ^ 2 + r) * a = (r ^ 2 + r) * as := by nlinarith
    exact mul_left_cancel₀ (by positivity) this
  refine ⟨by rw [hba, haeq, hbs], haeq⟩

/-- In a nominal equilibrium of the `√b + √a` economy, every generation `t ≥ 1` consumes its
demand at the relative price `r_t = p_{t+1}/p_t`. -/
theorem olg_sqrt_demand {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ} (he : OLGEq sqrtU 0 p M cb ca)
    {t : ℕ} (ht : t ≠ 0) :
    cb t = p (t + 1) / p t / (1 + p (t + 1) / p t) ∧
      ca t = 1 / (p (t + 1) / p t * (1 + p (t + 1) / p t)) := by
  have hpt := he.pricesPos t
  have hpt1 := he.pricesPos (t + 1)
  have hw : olgWealth 0 M p t = p t := by simp [olgWealth, ht]
  have hr : 0 < p (t + 1) / p t := div_pos hpt1 hpt
  have hscale : ∀ b a, p t * b + p (t + 1) * a = p t * (b + p (t + 1) / p t * a) := by
    intro b a; field_simp
  refine sqrt_demand hr (he.cons_nonneg t).1 (he.cons_nonneg t).2 ?_ fun b' a' hb' ha' hbud => ?_
  · have := he.budget t
    rw [hw, hscale] at this
    nlinarith
  · have := he.optimal t b' a' hb' ha' (by rw [hw, hscale]; nlinarith)
    simpa [sqrtU] using this

/-- **Classification of the nominal equilibria of the `√b + √a` economy** (MWG, p. 774, Figures
20.H.2-20.H.3). With `r_k = p_{k+2}/p_{k+1}`, market clearing gives `r_{k+1} = r_k² + r_k - 1`;
positivity forces `r_k ≥ 1`. If `r_0 = 1` the equilibrium is the monetary steady state; if
`r_0 > 1`, `r_k ≥ 1 + (k + 1)(r_0 - 1)`, the real bubble `M/p_{t+1} = c_{at}` is not bounded away
from zero, and the monetary steady state Pareto dominates the equilibrium. -/
theorem olg_sqrt_classification {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq sqrtU 0 p M cb ca) :
    ((∀ t, cb t = monetaryCb (1 / 2) t) ∧ ∀ t, ca t = 1 - 1 / 2) ∨
      (¬ OLGParetoOptimal sqrtU cb ca ∧ ¬ ∃ η : ℝ, 0 < η ∧ ∀ t, η ≤ M / p (t + 1)):= by
  have hmono : ∀ b b' a, 0 ≤ b → b < b' → sqrtU (b, a) < sqrtU (b', a) := fun b b' a hb hbb' => by
    simp only [sqrtU]; linarith [Real.sqrt_lt_sqrt hb hbb']
  have hid := olg_nominal_identity hmono he
  have hreal : ∀ t, M / p (t + 1) = ca t := fun t => by
    rw [← hid t]; field_simp [(he.pricesPos (t + 1)).ne']
  simp only [hreal]
  set R : ℕ → ℝ := fun k => p (k + 2) / p (k + 1) with hR
  have hRpos : ∀ k, 0 < R k := fun k => div_pos (he.pricesPos _) (he.pricesPos _)
  have hdem : ∀ k, cb (k + 1) = R k / (1 + R k) ∧ ca (k + 1) = 1 / (R k * (1 + R k)) :=
    fun k => olg_sqrt_demand he (t := k + 1) (by omega)
  have hrec : ∀ k, R (k + 1) = R k ^ 2 + R k - 1 := by
    intro k
    have hf := he.feasible (k + 1)
    rw [(hdem k).2, (hdem (k + 1)).1] at hf
    have h1 := hRpos k
    have h2 := hRpos (k + 1)
    field_simp at hf
    nlinarith
  -- `r_k ≥ 1`
  have hge1 : ∀ k, 1 ≤ R k := by
    intro k
    by_contra hlt
    push Not at hlt
    have hneg : ∀ n, R (k + n) - 1 ≤ 2 ^ n * (R k - 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [← add_assoc, hrec]
        have hp := hRpos (k + n)
        have hle1 : R (k + n) - 1 ≤ 0 := by
          have : 2 ^ n * (R k - 1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
          linarith
        have : R (k + n) ^ 2 + R (k + n) - 1 - 1 ≤ 2 * (R (k + n) - 1) := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hp.le hle1]
        have e : (2 : ℝ) ^ (n + 1) * (R k - 1) = 2 * (2 ^ n * (R k - 1)) := by ring
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - R k))
    have h2n : (n : ℝ) ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this.le
    have hpos := hRpos (k + n)
    have := hneg n
    have hd : 0 < 1 - R k := by linarith
    have : (n : ℝ) * (1 - R k) > 1 := by
      rw [div_lt_iff₀ hd] at hn; linarith
    nlinarith
  -- steady state or exploding prices
  rcases eq_or_lt_of_le (hge1 0) with h0 | h0
  · -- `r_0 = 1`: the monetary steady state
    have hR1 : ∀ k, R k = 1 := by
      intro k
      induction k with
      | zero => exact h0.symm
      | succ k ih => rw [hrec, ih]; norm_num
    have hcb : ∀ t, cb t = monetaryCb (1 / 2) t := by
      intro t
      rcases t with _ | k
      · simp [monetaryCb, he.feasible_zero]
      · rw [(hdem k).1, hR1]; simp [monetaryCb]; norm_num
    have hca : ∀ t, ca t = 1 - 1 / 2 := by
      intro t
      have := he.feasible t
      rw [hcb (t + 1)] at this
      simp [monetaryCb] at this
      linarith
    exact Or.inl ⟨hcb, hca⟩
  · -- `r_0 > 1`: the bubble vanishes and the steady state dominates
    have hgrow : ∀ n, 1 + (n + 1) * (R 0 - 1) ≤ R n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hrec]
        push_cast
        have := hge1 n
        nlinarith
    right
    constructor
    · intro hpo
      apply hpo
      refine ⟨monetaryCb (1 / 2), fun _ => 1 - 1 / 2, fun t => ⟨?_, by norm_num⟩,
        by simp [monetaryCb], fun t => by simp [monetaryCb], fun t => ?_, 0, ?_⟩
      · unfold monetaryCb; split_ifs <;> norm_num
      · rcases t with _ | k
        · -- generation 0 consumes `(1, 1/(1 + r_0)) ≤ (1, 1/2)`
          have hca0 : ca 0 = 1 / (1 + R 0) := by
            have hfe := he.feasible 0
            rw [(hdem 0).1] at hfe
            have h1 : R 0 / (1 + R 0) = 1 - 1 / (1 + R 0) := by
              rw [eq_sub_iff_add_eq, ← add_div, add_comm,
                div_self (by linarith [hRpos 0])]
            linarith
          simp only [sqrtU, he.feasible_zero, monetaryCb, ↓reduceIte, hca0]
          have : 1 / (1 + R 0) ≤ 1 - 1 / 2 := by
            rw [div_le_iff₀ (by linarith)]; linarith
          linarith [Real.sqrt_le_sqrt this]
        · -- generation `k + 1` has utility `√(1 + 1/r_k) ≤ √2`
          rw [(hdem k).1, (hdem k).2]
          simp only [sqrtU, monetaryCb, show k + 1 ≠ 0 by omega, ↓reduceIte]
          have hr := hRpos k
          have hr1 := hge1 k
          set x := Real.sqrt (R k / (1 + R k)) with hx
          set y := Real.sqrt (1 / (R k * (1 + R k))) with hy
          have hx2 : x ^ 2 = R k / (1 + R k) := Real.sq_sqrt (by positivity)
          have hy2 : y ^ 2 = 1 / (R k * (1 + R k)) := Real.sq_sqrt (by positivity)
          have hx0 : 0 ≤ x := Real.sqrt_nonneg _
          have hy0 : 0 ≤ y := Real.sqrt_nonneg _
          have hxy : x = R k * y := by
            have e : R k / (1 + R k) = R k ^ 2 * (1 / (R k * (1 + R k))) := by field_simp
            rw [hx, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
          have hs : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
          have hs0 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
          have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
          rw [e]
          -- `(x + y)² = 1 + 1/r_k ≤ 2`
          have hsq : (x + y) ^ 2 ≤ (Real.sqrt (1 / 2) + Real.sqrt (1 / 2)) ^ 2 := by
            have h1 : (x + y) ^ 2 = (R k + 1) ^ 2 * y ^ 2 := by rw [hxy]; ring
            rw [h1, hy2]
            have : (R k + 1) ^ 2 * (1 / (R k * (1 + R k))) = 1 + 1 / R k := by
              field_simp; ring
            rw [this]
            have : 1 / R k ≤ 1 := by rw [div_le_one hr]; exact hr1
            nlinarith
          nlinarith [sq_nonneg (x + y - (Real.sqrt (1 / 2) + Real.sqrt (1 / 2)))]
      · -- strictly better for generation 0
        have hca0 : ca 0 = 1 / (1 + R 0) := by
          have hfe := he.feasible 0
          rw [(hdem 0).1] at hfe
          have h1 : R 0 / (1 + R 0) = 1 - 1 / (1 + R 0) := by
            rw [eq_sub_iff_add_eq, ← add_div, add_comm,
              div_self (by linarith [hRpos 0])]
          linarith
        simp only [sqrtU, he.feasible_zero, monetaryCb, ↓reduceIte, hca0]
        have : 1 / (1 + R 0) < 1 - 1 / 2 := by
          rw [div_lt_iff₀ (by linarith)]; linarith
        linarith [Real.sqrt_lt_sqrt (by positivity) this]
    · rintro ⟨η, hη, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (η * (R 0 - 1)))
      have hd : 0 < R 0 - 1 := by linarith
      have hg := hgrow n
      have hca := hb (n + 1)
      rw [(hdem n).2] at hca
      have hRn := hRpos n
      have hbig : 1 / η < R n := by
        have : 1 / (η * (R 0 - 1)) * (η * (R 0 - 1)) = 1 := by field_simp
        have h1 : (1 / η) = 1 / (η * (R 0 - 1)) * (R 0 - 1) := by field_simp
        rw [h1]
        nlinarith
      have : 1 / (R n * (1 + R n)) < η := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hη] at hbig
        nlinarith
      linarith

/-- **Optimal nominal equilibria are those, and only those, whose bubble is bounded away from
zero** (MWG, p. 774, a claim "we leave without proof"), in the stationary economy
`u(b, a) = √b + √a` with a purely nominal asset. -/
theorem olg_sqrt_optimal_iff_bubble {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq sqrtU 0 p M cb ca) :
    OLGParetoOptimal sqrtU cb ca ↔ ∃ η : ℝ, 0 < η ∧ ∀ t, η ≤ M / p (t + 1) := by
  have hmono : ∀ b b' a, 0 ≤ b → b < b' → sqrtU (b, a) < sqrtU (b', a) := fun b b' a hb hbb' => by
    simp only [sqrtU]; linarith [Real.sqrt_lt_sqrt hb hbb']
  have hid := olg_nominal_identity hmono he
  rcases olg_sqrt_classification he with ⟨hcb, hca⟩ | ⟨hnpo, hnb⟩
  · constructor
    · intro _
      refine ⟨1 / 2, by norm_num, fun t => ?_⟩
      rw [← hid t, hca t, mul_div_assoc, mul_div_cancel₀ _ (he.pricesPos (t + 1)).ne']
      norm_num
    · intro _
      rw [show cb = monetaryCb (1 / 2) from funext hcb, show ca = (fun _ => 1 - 1 / 2) from
        funext hca]
      exact olgParetoOptimal_monetary
  · exact ⟨fun h => absurd h hnpo, fun h => absurd h hnb⟩

/-- **Exercise 20.H.2(b)** for the `√b + √a` economy (MWG, p. 786): its excess demand satisfies
the determinacy condition (20.H.3) (`sqrt_determinacy_condition`), and the monetary steady state
is the only nominal equilibrium that is a Pareto optimum. -/
theorem exercise_20_H_2b_sqrt {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq sqrtU 0 p M cb ca) (hpo : OLGParetoOptimal sqrtU cb ca) :
    (∀ t, cb t = monetaryCb (1 / 2) t) ∧ ∀ t, ca t = 1 - 1 / 2 := by
  rcases olg_sqrt_classification he with h | ⟨hnpo, _⟩
  · exact h
  · exact absurd hpo hnpo

/-- **The determinacy condition (20.H.3) for `√b + √a`** (MWG, p. 776): with endowment `(1, 0)`
the excess demands are `z_b(p_b, p_a) = p_a/(p_b + p_a) - 1` and
`z_a(p_b, p_a) = p_b²/(p_a (p_b + p_a))`, and `∇₁z_b(p_b, p_a) < ∇₁z_a(p_b, p_a)` at all
positive prices (`z_b` decreases and `z_a` increases in `p_b`). -/
theorem sqrt_determinacy_condition {pb pa : ℝ} (hb : 0 < pb) (ha : 0 < pa) :
    HasDerivAt (fun x => pa / (x + pa) - 1) (-pa / (pb + pa) ^ 2) pb ∧
      HasDerivAt (fun x => x ^ 2 / (pa * (x + pa)))
        (pb * (pb + 2 * pa) / (pa * (pb + pa) ^ 2)) pb ∧
      -pa / (pb + pa) ^ 2 < pb * (pb + 2 * pa) / (pa * (pb + pa) ^ 2) := by
  have hs : pb + pa ≠ 0 := by positivity
  have hlin : HasDerivAt (fun x : ℝ => x + pa) 1 pb := (hasDerivAt_id pb).add_const pa
  refine ⟨?_, ?_, ?_⟩
  · have := ((hasDerivAt_const pb pa).div hlin hs).sub_const 1
    convert this using 1
    field_simp
    ring
  · have h2 : HasDerivAt (fun x : ℝ => pa * (x + pa)) pa pb := by
      simpa using hlin.const_mul pa
    have := (hasDerivAt_pow 2 pb).div h2 (by positivity)
    convert this using 1
    field_simp
    ring
  · have h1 : -pa / (pb + pa) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    have h2 : 0 < pb * (pb + 2 * pa) / (pa * (pb + pa) ^ 2) := by positivity
    linarith

end MWG.EquilibriumTime
