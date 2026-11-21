/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.MixedBertrand

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
