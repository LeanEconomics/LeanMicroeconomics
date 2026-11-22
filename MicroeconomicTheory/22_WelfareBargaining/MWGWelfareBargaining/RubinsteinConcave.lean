/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Rubinstein
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact

/-!
# Rubinstein bargaining with concave utilities

MWG, Exercise 22.E.11 (p. 854), building on Example 9.AA.2 (imported from `MWGDynamicGames`).

Two agents divide `m > 0`; agent `i` values `mᵢ` at `uᵢ(mᵢ)`, `uᵢ` increasing and concave with
`uᵢ(0) = 0`; common discount factor `δ ∈ (0, 1)`. In stationary strategies agent 1 proposes the
split `(x, m - x)` and agent 2 the split `(w, m - w)`, and each responder is indifferent between
accepting and proposing next period (`IsStationary`):
`u₂(m - x) = δu₂(m - w)` and `u₁(w) = δu₁(x)`.

* `exercise_22_E_11a`: there is at most one stationary configuration. In log terms
  `ln u₁(x) - ln u₁(w) = -ln δ = ln u₂(m - w) - ln u₂(m - x)`; two solutions would give two
  intervals `[w, x]`, `[w', x']` (shifted to the right) on which the strictly concave
  `ln u₁` and `ln u₂(m - ·)` have the same increments, forcing both a longer and a shorter
  second interval.
* `exercise_22_E_11a_exists`: with `u₁`, `u₂` also continuous on `[0, m]` a stationary
  configuration exists. `w(x)` solves `u₁(w) = δu₁(x)` and `T(x) = m - z` with
  `u₂(z) = δu₂(m - w(x))` (intermediate value theorem); `T` is monotone on `[0, m]`, so the
  supremum of `{x : x ≤ T x}` is a fixed point (Knaster-Tarski), which needs no continuity of
  the implicit map `w`.
* `exercise_22_E_11b_bracket`: the Nash product `u₁(z)u₂(m - z)` takes the same value at `w` and
  `x`, so the Nash solution `z*` lies between them; `exercise_22_E_11b`: as `δ → 1` both shares
  converge to `z*` (since `u₁(x) - u₁(w) = (1 - δ)u₁(x) → 0`), i.e. the stationary SPNE
  agreement converges to the Nash bargaining solution.
* `exercise_22_E_11c_linear`: for linear utilities the stationary solution is
  `x = m/(1 + δ)`, and by Rubinstein's theorem (`example_9_AA_2`, imported) every SPNE of the
  alternating-offer game gives exactly these payoffs. Part (c) for general concave utilities
  (every SPNE payoff is stationary) is `exercise_22_E_11c` in `RubinsteinGame`, on the
  alternating-offer game with utility payoffs.
-/

namespace MWG.WelfareBargaining

/-- **Exercise 22.E.11(a)** (MWG, p. 854). The stationary SPNE conditions: agent 1 proposes
`(x, m - x)`, agent 2 proposes `(w, m - w)`, and responders are indifferent. -/
def IsStationary (u₁ u₂ : ℝ → ℝ) (m δ x w : ℝ) : Prop :=
  0 ≤ w ∧ w ≤ m ∧ 0 ≤ x ∧ x ≤ m ∧ u₂ (m - x) = δ * u₂ (m - w) ∧ u₁ w = δ * u₁ x

/-- The standing assumptions of Exercise 22.E.11 on the utility functions. -/
structure RubinsteinData (u₁ u₂ : ℝ → ℝ) (m δ : ℝ) : Prop where
  m_pos : 0 < m
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  mono₁ : StrictMonoOn u₁ (Set.Icc 0 m)
  mono₂ : StrictMonoOn u₂ (Set.Icc 0 m)
  conc₁ : ConcaveOn ℝ (Set.Icc 0 m) u₁
  conc₂ : ConcaveOn ℝ (Set.Icc 0 m) u₂
  zero₁ : u₁ 0 = 0
  zero₂ : u₂ 0 = 0

variable {u₁ u₂ : ℝ → ℝ} {m δ : ℝ}

theorem RubinsteinData.pos₁ (hD : RubinsteinData u₁ u₂ m δ) {z : ℝ} (hz : 0 < z) (hzm : z ≤ m) :
    0 < u₁ z := by
  have := hD.mono₁ (Set.left_mem_Icc.2 hD.m_pos.le) ⟨hz.le, hzm⟩ hz
  rwa [hD.zero₁] at this

theorem RubinsteinData.pos₂ (hD : RubinsteinData u₁ u₂ m δ) {z : ℝ} (hz : 0 < z) (hzm : z ≤ m) :
    0 < u₂ z := by
  have := hD.mono₂ (Set.left_mem_Icc.2 hD.m_pos.le) ⟨hz.le, hzm⟩ hz
  rwa [hD.zero₂] at this

/-- A stationary configuration is interior: `0 < w < x < m`. -/
theorem stationary_interior (hD : RubinsteinData u₁ u₂ m δ) {x w : ℝ}
    (h : IsStationary u₁ u₂ m δ x w) : 0 < w ∧ w < x ∧ x < m := by
  obtain ⟨hw0, hwm, hx0, hxm, e₁, e₂⟩ := h
  have hx : 0 < x := by
    rcases hx0.lt_or_eq with hx | hx
    · exact hx
    · subst hx
      rw [hD.zero₁, mul_zero] at e₂
      have hw : w = 0 := by
        by_contra hw
        have := hD.pos₁ (lt_of_le_of_ne hw0 (Ne.symm hw)) hwm
        linarith
      subst hw
      simp only [sub_zero] at e₁
      have := hD.pos₂ hD.m_pos le_rfl
      nlinarith [hD.δ_lt_one]
  have hu₁x := hD.pos₁ hx hxm
  have hwx : w < x := by
    by_contra hle
    have hle : x ≤ w := not_lt.1 hle
    have := hD.mono₁.monotoneOn ⟨hx0, hxm⟩ ⟨hw0, hwm⟩ hle
    nlinarith [hD.δ_lt_one]
  have hw : 0 < w := by
    rcases hw0.lt_or_eq with hw | hw
    · exact hw
    · subst hw
      rw [hD.zero₁] at e₂
      nlinarith [hD.δ_pos]
  refine ⟨hw, hwx, lt_of_le_of_ne hxm fun hxm' => ?_⟩
  subst hxm'
  rw [sub_self, hD.zero₂] at e₁
  have := hD.pos₂ (by linarith : 0 < x - w) (by linarith)
  nlinarith [hD.δ_pos]

/-- `ln ∘ u` is strictly concave on `(0, m]` for `u` concave and strictly increasing. -/
theorem log_comp_strictConcave {u : ℝ → ℝ} (hm : 0 < m) (hmono : StrictMonoOn u (Set.Icc 0 m))
    (hconc : ConcaveOn ℝ (Set.Icc 0 m) u) (h0 : u 0 = 0) :
    StrictConcaveOn ℝ (Set.Ioc 0 m) fun z => Real.log (u z) := by
  have hpos : ∀ z ∈ Set.Ioc (0 : ℝ) m, 0 < u z := fun z hz => by
    have := hmono (Set.left_mem_Icc.2 hm.le) ⟨hz.1.le, hz.2⟩ hz.1
    rwa [h0] at this
  refine ⟨convex_Ioc 0 m, fun a ha b hb hab s t hs ht hst => ?_⟩
  have hsub : ∀ z ∈ Set.Ioc (0 : ℝ) m, z ∈ Set.Icc (0 : ℝ) m := fun z hz => ⟨hz.1.le, hz.2⟩
  have hmid : s • a + t • b ∈ Set.Ioc (0 : ℝ) m := convex_Ioc 0 m ha hb hs.le ht.le hst
  have h1 := hconc.2 (hsub a ha) (hsub b hb) hs.le ht.le hst
  have hne : u a ≠ u b := hmono.injOn.ne (hsub a ha) (hsub b hb) hab
  have h2 := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 (hpos a ha)) (Set.mem_Ioi.2 (hpos b hb))
    hne hs ht hst
  simp only [smul_eq_mul] at h1 h2 ⊢
  have hp : 0 < s * u a + t * u b := by
    have := hpos a ha; have := hpos b hb; positivity
  have h3 := Real.log_le_log hp h1
  linarith

/-- Strict concavity: on two intervals `[w, x]`, `[w', x']` with `w < w'`, `x < x'`, the slope over
the second is smaller. -/
theorem slope_shift {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f) {w x w' x' : ℝ}
    (hw : w ∈ S) (hx : x ∈ S) (hw' : w' ∈ S) (hx' : x' ∈ S) (h1 : w < x) (h2 : w' < x')
    (h3 : w < w') (h4 : x < x') :
    (f x' - f w') / (x' - w') < (f x - f w) / (x - w) := by
  have a := hf.secant_strict_mono hw hx hx' h1.ne' (by linarith) h4
  have b := hf.secant_strict_mono hx' hw hw' (by linarith) h2.ne h3
  have e1 : (f w - f x') / (w - x') = (f x' - f w) / (x' - w) := by
    rw [← neg_sub, ← neg_sub x' w, neg_div_neg_eq]
  have e2 : (f w' - f x') / (w' - x') = (f x' - f w') / (x' - w') := by
    rw [← neg_sub, ← neg_sub x' w', neg_div_neg_eq]
  rw [e1, e2] at b
  linarith

/-- **Exercise 22.E.11(a)** (MWG, p. 854). With increasing concave utilities there is a single
configuration of stationary SPNE proposals, hence of stationary SPNE utility payoffs. -/
theorem exercise_22_E_11a (hD : RubinsteinData u₁ u₂ m δ) {x w x' w' : ℝ}
    (h : IsStationary u₁ u₂ m δ x w) (h' : IsStationary u₁ u₂ m δ x' w') : x = x' ∧ w = w' := by
  -- reduce to `x ≤ x'`
  suffices key : ∀ {x w x' w' : ℝ}, IsStationary u₁ u₂ m δ x w →
      IsStationary u₁ u₂ m δ x' w' → x ≤ x' → x = x' ∧ w = w' by
    rcases le_total x x' with hle | hle
    · exact key h h' hle
    · obtain ⟨e1, e2⟩ := key h' h hle; exact ⟨e1.symm, e2.symm⟩
  intro x w x' w' h h' hle
  obtain ⟨hw, hwx, hxm⟩ := stationary_interior hD h
  obtain ⟨hw', hwx', hxm'⟩ := stationary_interior hD h'
  have hu₁x := hD.pos₁ (hw.trans hwx) hxm.le
  have hu₁x' := hD.pos₁ (hw'.trans hwx') hxm'.le
  rcases hle.lt_or_eq with hlt | heq
  swap
  · subst heq
    refine ⟨rfl, hD.mono₁.injOn ⟨h.1, h.2.1⟩ ⟨h'.1, h'.2.1⟩ ?_⟩
    rw [h.2.2.2.2.2, h'.2.2.2.2.2]
  exfalso
  -- `w < w'`
  have hww : w < w' := by
    by_contra hle'
    have hle' : w' ≤ w := not_lt.1 hle'
    have h1 := hD.mono₁.monotoneOn ⟨h'.1, h'.2.1⟩ ⟨h.1, h.2.1⟩ hle'
    have h2 := hD.mono₁ ⟨h.2.2.1, h.2.2.2.1⟩ ⟨h'.2.2.1, h'.2.2.2.1⟩ hlt
    rw [h.2.2.2.2.2] at h1; rw [h'.2.2.2.2.2] at h1
    nlinarith [hD.δ_pos]
  -- the increments of `ln u₁` and of `ln u₂(m - ·)`
  set c := -Real.log δ with hc
  have hcpos : 0 < c := by rw [hc, neg_pos]; exact Real.log_neg hD.δ_pos hD.δ_lt_one
  have hg : ∀ {x w}, IsStationary u₁ u₂ m δ x w → 0 < w → w < x → x < m →
      Real.log (u₁ x) - Real.log (u₁ w) = c := by
    intro x w h hw hwx hxm
    have hux := hD.pos₁ (hw.trans hwx) hxm.le
    rw [h.2.2.2.2.2, Real.log_mul hD.δ_pos.ne' hux.ne', hc]; ring
  have hf : ∀ {x w}, IsStationary u₁ u₂ m δ x w → 0 < w → w < x → x < m →
      Real.log (u₂ (m - w)) - Real.log (u₂ (m - x)) = c := by
    intro x w h hw hwx hxm
    have hu := hD.pos₂ (by linarith : 0 < m - w) (by linarith)
    rw [h.2.2.2.2.1, Real.log_mul hD.δ_pos.ne' hu.ne', hc]; ring
  have hG := log_comp_strictConcave hD.m_pos hD.mono₁ hD.conc₁ hD.zero₁
  -- `ln u₂(m - ·)` is strictly concave on `[0, m)`
  have hF : StrictConcaveOn ℝ (Set.Ico 0 m) fun z => Real.log (u₂ (m - z)) := by
    have hG₂ := log_comp_strictConcave hD.m_pos hD.mono₂ hD.conc₂ hD.zero₂
    refine ⟨convex_Ico 0 m, fun a ha b hb hab s t hs ht hst => ?_⟩
    have := hG₂.2 (x := m - a) (y := m - b) ⟨by linarith [ha.2], by linarith [ha.1]⟩
      ⟨by linarith [hb.2], by linarith [hb.1]⟩ (by intro h; apply hab; linarith) hs ht hst
    simp only [smul_eq_mul] at this ⊢
    have e : s * (m - a) + t * (m - b) = m - (s * a + t * b) := by
      have : m = (s + t) * m := by rw [hst, one_mul]
      linarith [this]
    rw [e] at this
    exact this
  have sg := slope_shift hG ⟨hw, by linarith⟩ ⟨hw.trans hwx, hxm.le⟩ ⟨hw', by linarith⟩
    ⟨hw'.trans hwx', hxm'.le⟩ hwx hwx' hww hlt
  have sf := slope_shift hF ⟨hw.le, by linarith⟩ ⟨(hw.trans hwx).le, hxm⟩ ⟨hw'.le, by linarith⟩
    ⟨(hw'.trans hwx').le, hxm'⟩ hwx hwx' hww hlt
  rw [hg h hw hwx hxm, hg h' hw' hwx' hxm'] at sg
  rw [show Real.log (u₂ (m - x')) - Real.log (u₂ (m - w')) = -c by
      linarith [hf h' hw' hwx' hxm'],
    show Real.log (u₂ (m - x)) - Real.log (u₂ (m - w)) = -c by linarith [hf h hw hwx hxm]] at sf
  have hL : 0 < x - w := by linarith
  have hL' : 0 < x' - w' := by linarith
  rw [div_lt_div_iff₀ hL' hL] at sg
  rw [div_lt_div_iff₀ hL' hL] at sf
  nlinarith

/-- **Exercise 22.E.11**, instance (MWG, p. 854): linear utilities, where the stationary
configuration is `x = m/(1 + δ)`, `w = δm/(1 + δ)`. -/
theorem stationary_linear (hm : 0 < m) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    RubinsteinData id id m δ ∧ IsStationary id id m δ (m / (1 + δ)) (δ * m / (1 + δ)) := by
  refine ⟨⟨hm, hδ0, hδ1, strictMonoOn_id, strictMonoOn_id, concaveOn_id (convex_Icc 0 m),
    concaveOn_id (convex_Icc 0 m), rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · positivity
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · simp only [id]; field_simp; ring
  · simp only [id]; ring

/-- **Exercise 22.E.11(a)**, existence (MWG, p. 854). With continuous, strictly increasing,
concave utilities (`uᵢ(0) = 0`) a stationary configuration exists. For `x ∈ [0, m]` let
`w(x) ∈ [0, x]` solve `u₁(w) = δu₁(x)` and `T(x) = m - z` where `z ∈ [0, m - w(x)]` solves
`u₂(z) = δu₂(m - w(x))` (both by the intermediate value theorem). `T` is monotone on `[0, m]`,
so `x* = sup {x ∈ [0, m] : x ≤ T x}` is a fixed point (Knaster-Tarski), and `(x*, w(x*))` is
stationary. -/
theorem exercise_22_E_11a_exists (hD : RubinsteinData u₁ u₂ m δ)
    (hc₁ : ContinuousOn u₁ (Set.Icc 0 m)) (hc₂ : ContinuousOn u₂ (Set.Icc 0 m)) :
    ∃ x w, IsStationary u₁ u₂ m δ x w := by
  have hm := hD.m_pos
  -- agent 1's indifference share `w(x)`
  have hW : ∀ x ∈ Set.Icc 0 m, ∃ y, y ∈ Set.Icc 0 x ∧ u₁ y = δ * u₁ x := by
    intro x hx
    have hux : 0 ≤ u₁ x := by
      have := hD.mono₁.monotoneOn (Set.left_mem_Icc.2 hm.le) hx hx.1
      rwa [hD.zero₁] at this
    have := intermediate_value_Icc hx.1 (hc₁.mono (Set.Icc_subset_Icc le_rfl hx.2))
      (show δ * u₁ x ∈ Set.Icc (u₁ 0) (u₁ x) from
        ⟨by rw [hD.zero₁]; exact mul_nonneg hD.δ_pos.le hux,
          by nlinarith [hD.δ_lt_one]⟩)
    obtain ⟨y, hy, hy'⟩ := this
    exact ⟨y, hy, hy'⟩
  -- agent 2's indifference share `z(w)`
  have hZ : ∀ w ∈ Set.Icc 0 m, ∃ z, z ∈ Set.Icc 0 (m - w) ∧ u₂ z = δ * u₂ (m - w) := by
    intro w hw
    have hmw : m - w ∈ Set.Icc 0 m := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hu : 0 ≤ u₂ (m - w) := by
      have := hD.mono₂.monotoneOn (Set.left_mem_Icc.2 hm.le) hmw hmw.1
      rwa [hD.zero₂] at this
    obtain ⟨z, hz, hz'⟩ := intermediate_value_Icc hmw.1
      (hc₂.mono (Set.Icc_subset_Icc le_rfl hmw.2))
      (show δ * u₂ (m - w) ∈ Set.Icc (u₂ 0) (u₂ (m - w)) from
        ⟨by rw [hD.zero₂]; exact mul_nonneg hD.δ_pos.le hu, by nlinarith [hD.δ_lt_one]⟩)
    exact ⟨z, hz, hz'⟩
  set w : ℝ → ℝ := fun x => Classical.epsilon fun y => y ∈ Set.Icc 0 x ∧ u₁ y = δ * u₁ x
  have hw : ∀ x ∈ Set.Icc 0 m, w x ∈ Set.Icc 0 x ∧ u₁ (w x) = δ * u₁ x := fun x hx =>
    Classical.epsilon_spec (hW x hx)
  set z : ℝ → ℝ := fun v => Classical.epsilon fun y => y ∈ Set.Icc 0 (m - v) ∧
    u₂ y = δ * u₂ (m - v)
  have hz : ∀ v ∈ Set.Icc 0 m, z v ∈ Set.Icc 0 (m - v) ∧ u₂ (z v) = δ * u₂ (m - v) :=
    fun v hv => Classical.epsilon_spec (hZ v hv)
  have hwm : ∀ x ∈ Set.Icc 0 m, w x ∈ Set.Icc 0 m := fun x hx =>
    ⟨(hw x hx).1.1, (hw x hx).1.2.trans hx.2⟩
  set T : ℝ → ℝ := fun x => m - z (w x) with hT
  have hTm : ∀ x ∈ Set.Icc 0 m, T x ∈ Set.Icc 0 m := by
    intro x hx
    have h1 := (hz _ (hwm x hx)).1
    have h2 := (hwm x hx)
    exact ⟨by simp only [hT]; linarith [h2.1, h1.2], by simp only [hT]; linarith [h1.1]⟩
  -- `T` is monotone
  have hTmono : ∀ x ∈ Set.Icc 0 m, ∀ y ∈ Set.Icc 0 m, x ≤ y → T x ≤ T y := by
    intro x hx y hy hxy
    have h1 : w x ≤ w y := by
      rw [← hD.mono₁.le_iff_le (hwm x hx) (hwm y hy), (hw x hx).2, (hw y hy).2]
      exact mul_le_mul_of_nonneg_left (hD.mono₁.monotoneOn hx hy hxy) hD.δ_pos.le
    have hzx := hz _ (hwm x hx)
    have hzy := hz _ (hwm y hy)
    have hzxm : z (w x) ∈ Set.Icc 0 m := ⟨hzx.1.1, by linarith [hzx.1.2, (hwm x hx).1]⟩
    have hzym : z (w y) ∈ Set.Icc 0 m := ⟨hzy.1.1, by linarith [hzy.1.2, (hwm y hy).1]⟩
    have h2 : z (w y) ≤ z (w x) := by
      rw [← hD.mono₂.le_iff_le hzym hzxm, hzx.2, hzy.2]
      exact mul_le_mul_of_nonneg_left (hD.mono₂.monotoneOn
        ⟨by linarith [(hwm y hy).2], by linarith [(hwm y hy).1]⟩
        ⟨by linarith [(hwm x hx).2], by linarith [(hwm x hx).1]⟩ (by linarith)) hD.δ_pos.le
    simp only [hT]; linarith
  -- Knaster-Tarski
  set S := {x | x ∈ Set.Icc 0 m ∧ x ≤ T x}
  have hS0 : (0 : ℝ) ∈ S := ⟨Set.left_mem_Icc.2 hm.le, (hTm 0 (Set.left_mem_Icc.2 hm.le)).1⟩
  have hSb : BddAbove S := ⟨m, fun x hx => hx.1.2⟩
  set xs := sSup S
  have hxsm : xs ∈ Set.Icc 0 m := ⟨le_csSup hSb hS0, csSup_le ⟨0, hS0⟩ fun x hx => hx.1.2⟩
  have hle : xs ≤ T xs := csSup_le ⟨0, hS0⟩ fun x hx =>
    hx.2.trans (hTmono x hx.1 xs hxsm (le_csSup hSb hx))
  have hge : T xs ≤ xs := le_csSup hSb ⟨hTm xs hxsm, hTmono _ hxsm _ (hTm xs hxsm) hle⟩
  have hfix : T xs = xs := le_antisymm hge hle
  refine ⟨xs, w xs, (hwm xs hxsm).1, (hwm xs hxsm).2, hxsm.1, hxsm.2, ?_, (hw xs hxsm).2⟩
  have hzx := (hz _ (hwm xs hxsm)).2
  have : z (w xs) = m - xs := by simp only [hT] at hfix; linarith
  rw [← this, hzx]

/-- **Exercise 22.E.11(a)**, existence, instance (MWG, p. 854): linear utilities satisfy the
hypotheses (continuity included). -/
theorem exercise_22_E_11a_exists_instance (hm : 0 < m) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    RubinsteinData id id m δ ∧ ContinuousOn (id : ℝ → ℝ) (Set.Icc 0 m) ∧
      ∃ x w, IsStationary id id m δ x w :=
  ⟨(stationary_linear hm hδ0 hδ1).1, continuousOn_id,
    exercise_22_E_11a_exists (stationary_linear hm hδ0 hδ1).1 continuousOn_id continuousOn_id⟩

/-- **Exercise 22.E.11(b)** (MWG, p. 854). At a stationary configuration the Nash product
`N(z) = u₁(z)u₂(m - z)` takes the same value at `w` and at `x`; hence a maximizer `z*` of `N`
on `[0, m]` lies in `[w, x]`. -/
theorem exercise_22_E_11b_bracket (hD : RubinsteinData u₁ u₂ m δ) {x w z : ℝ}
    (h : IsStationary u₁ u₂ m δ x w) (hz : z ∈ Set.Icc 0 m)
    (hmax : ∀ y ∈ Set.Icc 0 m, u₁ y * u₂ (m - y) ≤ u₁ z * u₂ (m - z)) :
    u₁ w * u₂ (m - w) = u₁ x * u₂ (m - x) ∧ w ≤ z ∧ z ≤ x := by
  obtain ⟨hw, hwx, hxm⟩ := stationary_interior hD h
  have hN : u₁ w * u₂ (m - w) = u₁ x * u₂ (m - x) := by
    rw [h.2.2.2.2.1, h.2.2.2.2.2]; ring
  -- `ln N` is strictly concave on `(0, m)`
  have hG := log_comp_strictConcave hD.m_pos hD.mono₁ hD.conc₁ hD.zero₁
  have hG₂ := log_comp_strictConcave hD.m_pos hD.mono₂ hD.conc₂ hD.zero₂
  have hpos : ∀ y, 0 < y → y < m → 0 < u₁ y * u₂ (m - y) := fun y hy hym =>
    mul_pos (hD.pos₁ hy hym.le) (hD.pos₂ (by linarith) (by linarith))
  have hz0 : 0 < z := by
    by_contra h0
    have : z = 0 := le_antisymm (not_lt.1 h0) hz.1
    have := hmax x ⟨(hw.trans hwx).le, hxm.le⟩
    rw [‹z = 0›, hD.zero₁, zero_mul] at this
    linarith [hpos x (hw.trans hwx) hxm]
  have hzm : z < m := by
    by_contra h0
    have : z = m := le_antisymm hz.2 (not_lt.1 h0)
    have := hmax x ⟨(hw.trans hwx).le, hxm.le⟩
    rw [‹z = m›, sub_self, hD.zero₂, mul_zero] at this
    linarith [hpos x (hw.trans hwx) hxm]
  -- three points `a < b < c` in `(0, m)` with `N(b) ≤ N(a)`, `N(b) ≤ N(c)` are impossible
  have nodip : ∀ a b c, 0 < a → a < b → b < c → c < m →
      min (u₁ a * u₂ (m - a)) (u₁ c * u₂ (m - c)) < u₁ b * u₂ (m - b) := by
    intro a b c ha hab hbc hc
    set s := (c - b) / (c - a) with hs
    have hs0 : 0 < s := div_pos (by linarith) (by linarith)
    have hs1 : 0 < 1 - s := by rw [hs, sub_pos, div_lt_one (by linarith)]; linarith
    have hca : c - a ≠ 0 := by linarith
    have hb : b = s * a + (1 - s) * c := by rw [hs]; field_simp; ring
    have k1 := hG.2 (x := a) (y := c) ⟨ha, by linarith⟩ ⟨by linarith, hc.le⟩ (by linarith)
      hs0 hs1 (by ring)
    have k2 := hG₂.2 (x := m - a) (y := m - c) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith) hs0 hs1 (by ring)
    simp only [smul_eq_mul] at k1 k2
    rw [← hb] at k1
    rw [show s * (m - a) + (1 - s) * (m - c) = m - b by rw [hb]; ring] at k2
    have pa := hpos a ha (by linarith)
    have pc := hpos c (by linarith) hc
    have pb := hpos b (by linarith) (by linarith)
    rw [← Real.log_lt_log_iff (lt_min pa pc) pb]
    have hla : Real.log (min (u₁ a * u₂ (m - a)) (u₁ c * u₂ (m - c))) ≤
        s * Real.log (u₁ a * u₂ (m - a)) + (1 - s) * Real.log (u₁ c * u₂ (m - c)) := by
      have e1 := Real.log_le_log (lt_min pa pc) (min_le_left _ _)
      have e2 := Real.log_le_log (lt_min pa pc) (min_le_right _ _)
      nlinarith
    have hpa : 0 < u₁ a := hD.pos₁ ha (by linarith)
    have hpa' : 0 < u₂ (m - a) := hD.pos₂ (by linarith) (by linarith)
    have hpc : 0 < u₁ c := hD.pos₁ (by linarith) hc.le
    have hpc' : 0 < u₂ (m - c) := hD.pos₂ (by linarith) (by linarith)
    have hpb : 0 < u₁ b := hD.pos₁ (by linarith) (by linarith)
    have hpb' : 0 < u₂ (m - b) := hD.pos₂ (by linarith) (by linarith)
    rw [Real.log_mul hpa.ne' hpa'.ne', Real.log_mul hpc.ne' hpc'.ne'] at hla
    rw [Real.log_mul hpb.ne' hpb'.ne']
    linarith
  refine ⟨hN, ?_, ?_⟩
  · by_contra hlt
    have hlt : z < w := not_le.1 hlt
    have := nodip z w x hz0 hlt hwx hxm
    have hzx := hmax x ⟨(hw.trans hwx).le, hxm.le⟩
    rw [min_eq_right hzx] at this
    linarith
  · by_contra hlt
    have hlt : x < z := not_le.1 hlt
    have := nodip w x z hw hwx hlt hzm
    have hzw := hmax w ⟨hw.le, h.2.1⟩
    rw [hN] at hzw
    rw [min_eq_left (hN ▸ hzw)] at this
    linarith

/-- **Exercise 22.E.11(b)** (MWG, p. 854). As `δ → 1` the stationary SPNE shares converge to the
Nash bargaining share `z*` (the maximizer of `u₁(z)u₂(m - z)`): for every `ε > 0` there is
`δ₀ < 1` such that for `δ ∈ (δ₀, 1)` both proposals of the stationary configuration are within
`ε` of `z*`. Here `u₁` is also assumed continuous on `[0, m]`. -/
theorem exercise_22_E_11b (hm : 0 < m) (hmono : StrictMonoOn u₁ (Set.Icc 0 m))
    (hc₁ : ContinuousOn u₁ (Set.Icc 0 m)) {z : ℝ} (hz : z ∈ Set.Icc 0 m)
    (hmax : ∀ y ∈ Set.Icc 0 m, u₁ y * u₂ (m - y) ≤ u₁ z * u₂ (m - z)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ < 1, ∀ δ, δ₀ < δ → ∀ x w, RubinsteinData u₁ u₂ m δ → IsStationary u₁ u₂ m δ x w →
      |x - z| < ε ∧ |w - z| < ε := by
  by_cases hεm : m ≤ ε
  · refine ⟨0, by norm_num, fun δ _ x w hD h => ?_⟩
    obtain ⟨hw, hwx, hxm⟩ := stationary_interior hD h
    constructor <;> rw [abs_lt] <;> constructor <;> linarith [hz.1, hz.2]
  have hεm : ε < m := not_le.1 hεm
  -- the smallest utility gain of agent 1 over steps of length `ε`
  have hK : IsCompact (Set.Icc 0 (m - ε)) := isCompact_Icc
  have hne : (Set.Icc 0 (m - ε)).Nonempty := ⟨0, le_rfl, by linarith⟩
  have hcont : ContinuousOn (fun y => u₁ (y + ε) - u₁ y) (Set.Icc 0 (m - ε)) := by
    have hmaps : Set.MapsTo (fun y => y + ε) (Set.Icc 0 (m - ε)) (Set.Icc 0 m) :=
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact ContinuousOn.sub (hc₁.comp (continuousOn_id.add continuousOn_const) hmaps)
      (hc₁.mono fun y hy => ⟨hy.1, by linarith [hy.2]⟩)
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont
  set η := u₁ (y₀ + ε) - u₁ y₀ with hη
  have hηpos : 0 < η := by
    rw [hη, sub_pos]
    exact hmono ⟨hy₀.1, by linarith [hy₀.2]⟩ ⟨by linarith [hy₀.1], by linarith [hy₀.2]⟩
      (by linarith)
  set M := |u₁ m| + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨1 - η / M, by linarith [div_pos hηpos hMpos], fun δ hδ x w hD h => ?_⟩
  obtain ⟨hw, hwx, hxm⟩ := stationary_interior hD h
  obtain ⟨-, hwz, hzx⟩ := exercise_22_E_11b_bracket hD h hz hmax
  have hgap : x - w < ε := by
    by_contra hge
    have hge : ε ≤ x - w := not_lt.1 hge
    have hwin : w ∈ Set.Icc 0 (m - ε) := ⟨hw.le, by linarith⟩
    have h1 : η ≤ u₁ (w + ε) - u₁ w := hmin hwin
    have h2 : u₁ (w + ε) ≤ u₁ x := hmono.monotoneOn ⟨by linarith, by linarith⟩
      ⟨by linarith, hxm.le⟩ (by linarith)
    have h3 : u₁ x - u₁ w = (1 - δ) * u₁ x := by rw [h.2.2.2.2.2]; ring
    have h4 : u₁ x ≤ M := by
      have := hmono.monotoneOn ⟨by linarith, hxm.le⟩ ⟨hm.le, le_rfl⟩ hxm.le
      rw [hM]; linarith [le_abs_self (u₁ m)]
    have h5 : 0 < u₁ x := hD.pos₁ (hw.trans hwx) hxm.le
    have h6 : (1 - δ) * M < η := by
      have : 1 - δ < η / M := by linarith
      rwa [lt_div_iff₀ hMpos] at this
    have h7 : (1 - δ) * u₁ x ≤ (1 - δ) * M :=
      mul_le_mul_of_nonneg_left h4 (by linarith [hD.δ_lt_one])
    linarith
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

/-- **Exercise 22.E.11(c)** for linear utilities (MWG, p. 854, via Example 9.AA.2). With
`uᵢ(mᵢ) = mᵢ` the stationary configuration is `x = m/(1 + δ)`, and by Rubinstein's theorem
(imported from `MWGDynamicGames`) every SPNE of the infinite-horizon alternating-offer game, at
every feasible history, gives the proposer `x` and the responder `m - x`: all SPNE payoffs are
stationary payoffs. -/
theorem exercise_22_E_11c_linear (B : MWG.DynamicGames.BargainingGame) (hT : B.T = ⊤)
    (hδ : B.δ 0 = B.δ 1) {x w : ℝ} (hs : IsStationary id id B.v (B.δ 0) x w) :
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h →
      B.value σ h (MWG.DynamicGames.BargainingGame.proposer h.length) = x ∧
      B.value σ h (MWG.DynamicGames.BargainingGame.other
        (MWG.DynamicGames.BargainingGame.proposer h.length)) = B.v - x := by
  have hδ0 := B.δ_pos 0
  have hx : x = B.v / (1 + B.δ 0) := by
    obtain ⟨-, -, -, -, e₁, e₂⟩ := hs
    simp only [id] at e₁ e₂
    rw [eq_div_iff (by linarith)]
    rw [e₂] at e₁
    have h1 : (1 - B.δ 0) * (x * (1 + B.δ 0) - B.v) = 0 := by linear_combination -e₁
    rcases mul_eq_zero.1 h1 with h | h
    · linarith [B.δ_lt_one 0]
    · linarith
  intro σ hσ h hh
  obtain ⟨-, -, hall⟩ := B.example_9_AA_2 hT hδ
  obtain ⟨-, -, h1, h2⟩ := hall σ hσ h hh
  refine ⟨by rw [h1, hx], ?_⟩
  rw [h2, hx]
  field_simp
  ring

/-- **Exercise 22.E.11(b)**, instance (MWG, p. 854): for linear utilities the Nash product
`z(m - z)` is maximized at `z* = m/2`, and `u₁ = id` is strictly increasing and continuous. -/
theorem exercise_22_E_11b_instance (hm : 0 < m) :
    StrictMonoOn (id : ℝ → ℝ) (Set.Icc 0 m) ∧ ContinuousOn (id : ℝ → ℝ) (Set.Icc 0 m) ∧
      m / 2 ∈ Set.Icc 0 m ∧ ∀ y ∈ Set.Icc 0 m, id y * id (m - y) ≤ id (m / 2) * id (m - m / 2) :=
  ⟨strictMonoOn_id, continuousOn_id, ⟨by linarith, by linarith⟩, fun y _ => by
    simp only [id]; nlinarith [sq_nonneg (y - m / 2)]⟩

end MWG.WelfareBargaining
