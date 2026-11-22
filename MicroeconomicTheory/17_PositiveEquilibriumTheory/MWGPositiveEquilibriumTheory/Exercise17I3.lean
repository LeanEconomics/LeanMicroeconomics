/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

/-!
# Exercise 17.I.3: high- and low-quality goods (MWG, p. 649)

Three commodities: a high-quality good (`1`), a low-quality good (`2`) and labor. Production
`f₁(v) = min {v, 1}`, `f₂(v) = min {v^β, 1}`, `0 < β < 1`; one unit of labor in the aggregate,
of no utility value. Two equally sized classes, "rich" and "poor", each of a very large number
of agents with one unit of labor each; the rich own all the firms and spend all their wealth on
good `1` (utility `x₁`); the poor consume either good `1` or good `2`, not both, with utility
`x₁ + x₂/2` on `{x ≥ 0 : x₁x₂ = 0}` (`ex17I3XP`).

Modelling (corrections): the large classes are a continuum of mass `1/2` each (the setting of
Section 17.I's limit economy), so a fraction `a` of the poor may choose one optimal bundle and
`1 - a` another (`IsEx17I3Eqm`); labor is supplied inelastically; prices `(p₁, p₂, w)`.

* (a) The standard hypothesis that fails: the poor's consumption set is not convex
  (`exercise_17_I_3a`).
* (b) In every equilibrium both qualities are produced (`exercise_17_I_3b`): `w ≥ 0` (else
  sector 1's profit is unbounded), `p₂ > 0` and `p₁ > 0` (else the poor, resp. the rich, have no
  optimum), `w > 0` (else both sectors demand at least one unit of labor), so sector 2's profit
  `p₂v^β - wv` is positive for small `v` and `v₂ > 0`; the rich have positive wealth, so good `1`
  is demanded.
* (c) An equilibrium exists (`exercise_17_I_3c`): `w = p₁ = 1`, `p₂ = 1/2`,
  `v₂ = (β/2)^{1/(1-β)}`, `v₁ = 1 - v₂`, and a fraction `1 - v₂^β` of the poor buys good `1`
  (sector 2's profit maximization by the weighted AM-GM inequality).
-/

namespace MWG.PositiveEquilibriumTheory

/-- **Exercise 17.I.3** (MWG, p. 649). `f₁(v) = min {v, 1}`. -/
noncomputable def ex17I3f1 (v : ℝ) : ℝ := min v 1

/-- **Exercise 17.I.3** (MWG, p. 649). `f₂(v) = min {v^β, 1}`. -/
noncomputable def ex17I3f2 (β v : ℝ) : ℝ := min (v ^ β) 1

/-- **Exercise 17.I.3** (MWG, p. 649). The poor's consumption set `{(x₁, x₂) ≥ 0 : x₁ = 0 or
x₂ = 0}`: one quality or the other, not both. -/
def ex17I3XP : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ (x 0 = 0 ∨ x 1 = 0)}

/-- **Exercise 17.I.3** (MWG, p. 649). The poor's utility `u(x₁, x₂) = x₁ + x₂/2`. -/
noncomputable def ex17I3uP (x : Fin 2 → ℝ) : ℝ := x 0 + x 1 / 2

/-- A poor agent's optimal choice at prices `(p₁, p₂)` and wage `w`. -/
def ex17I3PoorOpt (p₁ p₂ w : ℝ) (x : Fin 2 → ℝ) : Prop :=
  x ∈ ex17I3XP ∧ p₁ * x 0 + p₂ * x 1 ≤ w ∧
    ∀ y ∈ ex17I3XP, p₁ * y 0 + p₂ * y 1 ≤ w → ex17I3uP y ≤ ex17I3uP x

/-- A rich agent's optimal choice with wealth `W` (utility `x₁` on `ℝ²₊`). -/
def ex17I3RichOpt (p₁ p₂ W : ℝ) (x : Fin 2 → ℝ) : Prop :=
  0 ≤ x 0 ∧ 0 ≤ x 1 ∧ p₁ * x 0 + p₂ * x 1 ≤ W ∧
    ∀ y : Fin 2 → ℝ, 0 ≤ y 0 → 0 ≤ y 1 → p₁ * y 0 + p₂ * y 1 ≤ W → y 0 ≤ x 0

/-- A state of the economy of Exercise 17.I.3: prices, labor inputs, the fraction `a` of the
poor choosing `xa` (the rest `xb`), and the rich bundle. -/
structure Ex17I3State where
  /-- Price of the high-quality good. -/
  p₁ : ℝ
  /-- Price of the low-quality good. -/
  p₂ : ℝ
  /-- The wage. -/
  w : ℝ
  /-- Labor in sector 1. -/
  v₁ : ℝ
  /-- Labor in sector 2. -/
  v₂ : ℝ
  /-- The fraction of the poor consuming `xa`. -/
  a : ℝ
  /-- The bundle of a rich agent. -/
  xR : Fin 2 → ℝ
  /-- The first bundle chosen by the poor. -/
  xa : Fin 2 → ℝ
  /-- The second bundle chosen by the poor. -/
  xb : Fin 2 → ℝ

/-- Profit of sector 1. -/
noncomputable def Ex17I3State.profit₁ (e : Ex17I3State) : ℝ :=
  e.p₁ * ex17I3f1 e.v₁ - e.w * e.v₁

/-- Profit of sector 2. -/
noncomputable def Ex17I3State.profit₂ (β : ℝ) (e : Ex17I3State) : ℝ :=
  e.p₂ * ex17I3f2 β e.v₂ - e.w * e.v₂

/-- Wealth of a rich agent: his wage plus his share of all profits (the rich have mass `1/2`). -/
noncomputable def Ex17I3State.wealthR (β : ℝ) (e : Ex17I3State) : ℝ :=
  e.w + 2 * (e.profit₁ + e.profit₂ β)

/-- **Exercise 17.I.3** (MWG, p. 649). Walrasian equilibrium of the large economy (classes of
mass `1/2`, one unit of labor per agent): profit maximization in both sectors, optimal choices of
the rich and of the poor, and market clearing for both goods and labor. -/
def IsEx17I3Eqm (β : ℝ) (e : Ex17I3State) : Prop :=
  (0 ≤ e.v₁ ∧ ∀ v, 0 ≤ v → e.p₁ * ex17I3f1 v - e.w * v ≤ e.profit₁) ∧
  (0 ≤ e.v₂ ∧ ∀ v, 0 ≤ v → e.p₂ * ex17I3f2 β v - e.w * v ≤ e.profit₂ β) ∧
  ex17I3RichOpt e.p₁ e.p₂ (e.wealthR β) e.xR ∧
  (0 ≤ e.a ∧ e.a ≤ 1 ∧ ex17I3PoorOpt e.p₁ e.p₂ e.w e.xa ∧ ex17I3PoorOpt e.p₁ e.p₂ e.w e.xb) ∧
  e.xR 0 / 2 + (e.a * e.xa 0 + (1 - e.a) * e.xb 0) / 2 = ex17I3f1 e.v₁ ∧
  e.xR 1 / 2 + (e.a * e.xa 1 + (1 - e.a) * e.xb 1) / 2 = ex17I3f2 β e.v₂ ∧
  e.v₁ + e.v₂ = 1

/-- **Exercise 17.I.3(a)** (MWG, p. 649). The poor's consumption set is not convex: the
convexity of consumption sets fails. -/
theorem exercise_17_I_3a : ¬ Convex ℝ ex17I3XP := by
  intro hc
  have h1 : (![1, 0] : Fin 2 → ℝ) ∈ ex17I3XP := ⟨by norm_num, le_refl 0, Or.inr rfl⟩
  have h2 : (![0, 1] : Fin 2 → ℝ) ∈ ex17I3XP := ⟨le_refl 0, by norm_num, Or.inl rfl⟩
  obtain ⟨-, -, h⟩ := hc h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  rcases h with h | h <;> norm_num at h

/-- **Exercise 17.I.3(b)** (MWG, p. 649). In every equilibrium both qualities are produced. -/
theorem exercise_17_I_3b {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {e : Ex17I3State}
    (h : IsEx17I3Eqm β e) : 0 < ex17I3f1 e.v₁ ∧ 0 < ex17I3f2 β e.v₂ := by
  obtain ⟨⟨hv1, hπ1⟩, ⟨hv2, hπ2⟩, ⟨hxR0, hxR1, hbR, hoptR⟩, ⟨ha0, ha1, hpa, hpb⟩, hc1, -, hlab⟩ :=
    h
  have hf1 : ∀ v, 0 ≤ v → 0 ≤ ex17I3f1 v ∧ ex17I3f1 v ≤ 1 := fun v hv =>
    ⟨le_min hv zero_le_one, min_le_right _ _⟩
  have hf10 : ex17I3f1 0 = 0 := by simp [ex17I3f1]
  have hf20 : ex17I3f2 β 0 = 0 := by simp [ex17I3f2, Real.zero_rpow hβ0.ne']
  -- the wage is nonnegative
  have hw0 : 0 ≤ e.w := by
    by_contra hw
    push Not at hw
    set t := (|e.p₁| + 1) / (-e.w) with ht
    have ht0 : 0 < t := div_pos (by positivity) (by linarith)
    have hwt : e.w * t = -(|e.p₁| + 1) := by
      rw [ht]
      field_simp [hw.ne]
    have hle := hπ1 (e.v₁ + t) (by linarith)
    unfold Ex17I3State.profit₁ at hle
    rw [mul_add] at hle
    obtain ⟨a0, a1⟩ := hf1 (e.v₁ + t) (by linarith)
    obtain ⟨b0, b1⟩ := hf1 e.v₁ hv1
    have hab : -|e.p₁| ≤ e.p₁ * ex17I3f1 (e.v₁ + t) - e.p₁ * ex17I3f1 e.v₁ := by
      rcases abs_cases e.p₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> nlinarith
    linarith
  -- the price of the low-quality good is positive
  have hp2 : 0 < e.p₂ := by
    by_contra hp
    push Not at hp
    obtain ⟨-, -, hopta⟩ := hpa
    set t := 2 * |ex17I3uP e.xa| + 2 with ht
    have ht0 : 0 ≤ t := by positivity
    have hle := hopta ![0, t] ⟨le_refl (0 : ℝ), ht0, Or.inl rfl⟩
      (by
        change e.p₁ * 0 + e.p₂ * t ≤ e.w
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hp ht0])
    change (0 : ℝ) + t / 2 ≤ ex17I3uP e.xa at hle
    have := le_abs_self (ex17I3uP e.xa)
    linarith
  -- the price of the high-quality good is positive
  have hp1 : 0 < e.p₁ := by
    by_contra hp
    push Not at hp
    have hle := hoptR ![e.xR 0 + 1, e.xR 1]
      (by change 0 ≤ e.xR 0 + 1; linarith) (by change 0 ≤ e.xR 1; exact hxR1)
      (by
        change e.p₁ * (e.xR 0 + 1) + e.p₂ * e.xR 1 ≤ e.wealthR β
        linarith)
    change e.xR 0 + 1 ≤ e.xR 0 at hle
    linarith
  -- profits are nonnegative
  have hπ1nn : 0 ≤ e.profit₁ := by
    have := hπ1 0 le_rfl
    rw [hf10] at this
    linarith
  have hπ2nn : 0 ≤ e.profit₂ β := by
    have := hπ2 0 le_rfl
    rw [hf20] at this
    linarith
  -- the wage is positive
  have hw : 0 < e.w := by
    rcases hw0.lt_or_eq with hw | hw
    · exact hw
    · exfalso
      have h1 := hπ1 1 zero_le_one
      have h2 := hπ2 1 zero_le_one
      unfold Ex17I3State.profit₁ at h1
      unfold Ex17I3State.profit₂ at h2
      rw [← hw] at h1 h2
      have hf11 : ex17I3f1 1 = 1 := by simp [ex17I3f1]
      have hf21 : ex17I3f2 β 1 = 1 := by simp [ex17I3f2]
      rw [hf11] at h1
      rw [hf21] at h2
      have hge1 : 1 ≤ ex17I3f1 e.v₁ := by nlinarith
      have hge2 : 1 ≤ ex17I3f2 β e.v₂ := by nlinarith
      have hv1' : 1 ≤ e.v₁ := hge1.trans (min_le_left _ _)
      have hv2' : 1 ≤ e.v₂ := by
        by_contra hlt
        push Not at hlt
        have := Real.rpow_lt_one hv2 hlt hβ0
        exact absurd (hge2.trans (min_le_left _ _)) (not_le.2 this)
      linarith
  -- sector 2 hires labor
  have hv2pos : 0 < e.v₂ := by
    by_contra hv
    push Not at hv
    have hv20 : e.v₂ = 0 := le_antisymm hv hv2
    have h1β : (0 : ℝ) < 1 - β := by linarith
    set c := min 1 ((e.p₂ / (2 * e.w)) ^ (1 / (1 - β))) with hc
    have hc0 : 0 < c := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
    have hc1 : c ≤ 1 := min_le_left _ _
    have hcβ1 : c ^ β ≤ 1 := Real.rpow_le_one hc0.le hc1 hβ0.le
    have hcpow : c ^ (1 - β) ≤ e.p₂ / (2 * e.w) := by
      calc c ^ (1 - β) ≤ ((e.p₂ / (2 * e.w)) ^ (1 / (1 - β))) ^ (1 - β) :=
            Real.rpow_le_rpow hc0.le (min_le_right _ _) h1β.le
        _ = e.p₂ / (2 * e.w) := by
            rw [one_div, Real.rpow_inv_rpow (by positivity) h1β.ne']
    have hsplit : c ^ (1 - β) * c ^ β = c := by
      rw [← Real.rpow_add hc0, sub_add_cancel, Real.rpow_one]
    have hcβpos : 0 < c ^ β := Real.rpow_pos_of_pos hc0 β
    have hle := hπ2 c hc0.le
    unfold Ex17I3State.profit₂ at hle
    rw [hv20, hf20] at hle
    have hf2c : ex17I3f2 β c = c ^ β := min_eq_left hcβ1
    rw [hf2c] at hle
    have hwc : e.w * c ≤ e.p₂ / 2 * c ^ β := by
      calc e.w * c = e.w * (c ^ (1 - β) * c ^ β) := by rw [hsplit]
        _ ≤ e.w * (e.p₂ / (2 * e.w) * c ^ β) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcpow hcβpos.le) hw.le
        _ = e.p₂ / 2 * c ^ β := by field_simp
    nlinarith [mul_pos hp2 hcβpos]
  refine ⟨?_, lt_min (Real.rpow_pos_of_pos hv2pos β) one_pos⟩
  -- the rich have positive wealth, so good 1 is demanded
  have hW : 0 < e.wealthR β := by
    unfold Ex17I3State.wealthR
    linarith
  have hxR0pos : 0 < e.xR 0 := by
    have e1 : e.p₁ * (e.wealthR β / e.p₁) = e.wealthR β := by field_simp
    have hle := hoptR ![e.wealthR β / e.p₁, 0]
      (by change 0 ≤ e.wealthR β / e.p₁; exact (div_pos hW hp1).le)
      (le_refl (0 : ℝ))
      (by change e.p₁ * (e.wealthR β / e.p₁) + e.p₂ * 0 ≤ e.wealthR β; rw [e1]; linarith)
    change e.wealthR β / e.p₁ ≤ e.xR 0 at hle
    linarith [div_pos hW hp1]
  have hxa0 := hpa.1.1
  have hxb0 := hpb.1.1
  rw [← hc1]
  nlinarith [mul_nonneg ha0 hxa0, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - e.a) hxb0]

/-- **Exercise 17.I.3(c)** (MWG, p. 649). An equilibrium exists, for every `0 < β < 1`:
`w = p₁ = 1`, `p₂ = 1/2`, `v₂ = (β/2)^{1/(1-β)}`, `v₁ = 1 - v₂`; the rich buy
`1 + (1 - β)v₂^β` units of good 1; a fraction `1 - v₂^β` of the poor buys `(1, 0)` and the rest
`(0, 2)`. -/
theorem exercise_17_I_3c {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : ∃ e, IsEx17I3Eqm β e := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set c : ℝ := (β / 2) ^ (1 / (1 - β)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hc1 : c < 1 := Real.rpow_lt_one (by positivity) (by linarith) (by positivity)
  have hcpow : c ^ (1 - β) = β / 2 := by
    rw [hc, one_div, Real.rpow_inv_rpow (by positivity) h1β.ne']
  set d : ℝ := c ^ β with hd
  have hd0 : 0 < d := Real.rpow_pos_of_pos hc0 β
  have hd1 : d < 1 := Real.rpow_lt_one hc0.le hc1 hβ0
  have hK : c = β / 2 * d := by
    rw [← hcpow, hd, ← Real.rpow_add hc0, sub_add_cancel, Real.rpow_one]
  set e : Ex17I3State := ⟨1, 1 / 2, 1, 1 - c, c, 1 - d, ![1 + (1 - β) * d, 0], ![1, 0], ![0, 2]⟩
    with he
  have hf1 : ex17I3f1 e.v₁ = 1 - c := min_eq_left (by change 1 - c ≤ 1; linarith)
  have hf2 : ex17I3f2 β e.v₂ = d := min_eq_left hd1.le
  have hπ1 : e.profit₁ = 0 := by
    unfold Ex17I3State.profit₁
    rw [hf1]
    change (1 : ℝ) * (1 - c) - 1 * (1 - c) = 0
    ring
  have hπ2 : e.profit₂ β = d / 2 - c := by
    unfold Ex17I3State.profit₂
    rw [hf2]
    change (1 / 2 : ℝ) * d - 1 * c = d / 2 - c
    ring
  have hW : e.wealthR β = 1 + (1 - β) * d := by
    unfold Ex17I3State.wealthR
    rw [hπ1, hπ2]
    change (1 : ℝ) + 2 * (0 + (d / 2 - c)) = 1 + (1 - β) * d
    rw [hK]
    ring
  refine ⟨e, ⟨⟨?_, fun v hv => ?_⟩, ⟨hc0.le, fun v hv => ?_⟩, ⟨?_, le_refl (0 : ℝ), ?_, ?_⟩,
    ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_⟩⟩
  · change 0 ≤ 1 - c
    linarith
  · rw [hπ1]
    change (1 : ℝ) * ex17I3f1 v - 1 * v ≤ 0
    have : ex17I3f1 v ≤ v := min_le_left _ _
    linarith
  · rw [hπ2]
    change (1 / 2 : ℝ) * ex17I3f2 β v - 1 * v ≤ d / 2 - c
    have hfv : ex17I3f2 β v ≤ v ^ β := min_le_left _ _
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hβ0.le h1β.le (div_nonneg hv hc0.le)
      zero_le_one (by ring)
    rw [Real.one_rpow, mul_one, Real.div_rpow hv hc0.le, ← hd, div_le_iff₀ hd0] at hamgm
    have e2 : (β * (v / c) + (1 - β) * 1) * d = 2 * v + (1 - β) * d := by
      rw [hK]
      field_simp
    rw [e2] at hamgm
    rw [hK]
    nlinarith
  · change (0 : ℝ) ≤ 1 + (1 - β) * d
    nlinarith
  · rw [hW]
    change (1 : ℝ) * (1 + (1 - β) * d) + 1 / 2 * 0 ≤ 1 + (1 - β) * d
    linarith
  · intro y hy0 hy1 hb
    rw [hW] at hb
    change (1 : ℝ) * y 0 + 1 / 2 * y 1 ≤ 1 + (1 - β) * d at hb
    change y 0 ≤ 1 + (1 - β) * d
    linarith
  · change (0 : ℝ) ≤ 1 - d
    linarith
  · change 1 - d ≤ (1 : ℝ)
    linarith
  · exact ⟨(by norm_num : (0 : ℝ) ≤ 1), le_refl (0 : ℝ), Or.inr rfl⟩
  · change (1 : ℝ) * 1 + 1 / 2 * 0 ≤ 1
    norm_num
  · rintro y ⟨hy0, hy1, -⟩ hb
    change (1 : ℝ) * y 0 + 1 / 2 * y 1 ≤ 1 at hb
    change y 0 + y 1 / 2 ≤ (1 : ℝ) + 0 / 2
    linarith
  · exact ⟨le_refl (0 : ℝ), (by norm_num : (0 : ℝ) ≤ 2), Or.inl rfl⟩
  · change (1 : ℝ) * 0 + 1 / 2 * 2 ≤ 1
    norm_num
  · rintro y ⟨hy0, hy1, -⟩ hb
    change (1 : ℝ) * y 0 + 1 / 2 * y 1 ≤ 1 at hb
    change y 0 + y 1 / 2 ≤ (0 : ℝ) + 2 / 2
    linarith
  · rw [hf1]
    change (1 + (1 - β) * d) / 2 + ((1 - d) * 1 + (1 - (1 - d)) * 0) / 2 = 1 - c
    rw [hK]
    ring
  · rw [hf2]
    change (0 : ℝ) / 2 + ((1 - d) * 0 + (1 - (1 - d)) * 2) / 2 = d
    ring
  · change 1 - c + c = 1
    ring

end MWG.PositiveEquilibriumTheory
