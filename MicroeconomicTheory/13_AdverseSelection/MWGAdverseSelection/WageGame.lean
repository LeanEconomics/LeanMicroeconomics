/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases

/-!
# Two firms simultaneously announcing wages

MWG, Sections 13.B (pp. 443-445) and 13.C (p. 452).

In stage 1 two firms announce wages; in stage 2 each worker accepts a highest wage if it is at
least her reservation value, choosing between tied firms with equal probability (MWG, p. 443,
footnote 12). A firm whose wage is the strictly highest earns the profit `P(w)` of hiring every
worker who accepts `w`; with a tie each firm earns `P(w)/2`; a firm with the lower wage earns
nothing. Given this (optimal) behaviour of the workers, the pure strategy SPNE are the pure Nash
equilibria of the firms' wage game `wageGame P`, a normal form game of Chapter 8
(`MWG.NoncooperativeGames.NormalForm`, `MWG.SimultaneousMoveGames.IsNashEquilibrium`).

* `isNash_wageGame_iff`: the Nash condition firm by firm.
* `wageGame_unique`: if `P` is right-continuous, `P(0) ≥ 0`, `P(w*) = 0`, `P < 0` above `w*` and
  `P > 0` just below `w*`, the unique pure equilibrium is `(w*, w*)` (the argument of
  Proposition 13.B.1(i), and the Bertrand argument of Section 13.C, p. 452).
* `wageGame_flat`: if `P = 0` up to `w*` and `P < 0` above, the pure equilibria are exactly the
  profiles with both wages at most `w*` (the argument of Proposition 13.B.1(ii)).
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Filter Topology

/-- **Section 13.B** (MWG, p. 443). A firm's share of the profit `P` of its wage `own` when the
other firm offers `other`: all of it when `own` is strictly higher, half with a tie, none when
`own` is lower. -/
noncomputable def wageShare (own other P : ℝ) : ℝ :=
  if other < own then P else if own = other then P / 2 else 0

/-- **Section 13.B** (MWG, p. 443). The firms' stage-1 wage game: firm `i` announces `w i` and
earns its share of `P (w i)`. -/
noncomputable def wageGame (P : ℝ → ℝ) : NormalForm (Fin 2) (fun _ => ℝ) where
  payoff i w := wageShare (w i) (w (1 - i)) (P (w i))

/-- Firm `own`'s wage is a best reply to `other`. -/
def WageBestReply (P : ℝ → ℝ) (own other : ℝ) : Prop :=
  ∀ t, wageShare t other (P t) ≤ wageShare own other (P own)

/-- **Section 13.B** (MWG, p. 443). The Nash condition of the wage game, firm by firm. -/
theorem isNash_wageGame_iff (P : ℝ → ℝ) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔
      WageBestReply P (w 0) (w 1) ∧ WageBestReply P (w 1) (w 0) := by
  constructor
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have := h 0 t
      simpa [wageGame, Function.update] using this
    · have := h 1 t
      simpa [wageGame, Function.update] using this
  · rintro ⟨h0, h1⟩ i t
    fin_cases i
    · simpa [wageGame, Function.update] using h0 t
    · simpa [wageGame, Function.update] using h1 t

/-- A share of a nonnegative profit is nonnegative. -/
theorem wageShare_nonneg {own other P : ℝ} (h : 0 ≤ P) : 0 ≤ wageShare own other P := by
  unfold wageShare; split_ifs <;> linarith

theorem wageShare_of_gt {own other P : ℝ} (h : other < own) : wageShare own other P = P := by
  simp [wageShare, h]

theorem wageShare_of_eq {own P : ℝ} : wageShare own own P = P / 2 := by
  simp [wageShare]

theorem wageShare_of_lt {own other P : ℝ} (h : own < other) : wageShare own other P = 0 := by
  simp [wageShare, not_lt.2 h.le, h.ne]

/-- With a safe wage earning `P(0) ≥ 0`, a best reply earns at least `0`. -/
theorem WageBestReply.nonneg {P : ℝ → ℝ} {own other : ℝ} (h : WageBestReply P own other)
    (h0 : 0 ≤ P 0) : 0 ≤ wageShare own other (P own) :=
  (wageShare_nonneg h0).trans (h 0)

/-- **Proposition 13.B.1**, proof (MWG, p. 444). The weakly lower-wage firm can capture the whole
market by raising its wage slightly: at a best reply with `own ≤ other`, `P(other) ≤ 0`. Only
right-continuity of `P` is used. -/
theorem WageBestReply.profit_nonpos {P : ℝ → ℝ} (hP : ∀ x, ContinuousWithinAt P (Set.Ici x) x)
    {own other : ℝ} (h : WageBestReply P own other) (hle : own ≤ other) : P other ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hev : ∀ᶠ x in 𝓝[≥] other, P other / 2 < P x :=
    (hP other).eventually (lt_mem_nhds (by linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 hev
  have hx : P other / 2 < P u := hsub ⟨hu.le, le_rfl⟩
  have hdev := h u
  rw [wageShare_of_gt hu] at hdev
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, wageShare_of_eq] at hdev; linarith
  · rw [wageShare_of_lt hlt] at hdev; linarith

/-- **Proposition 13.B.1(i)**, the argument (MWG, p. 444); also the Bertrand argument of
Section 13.C (p. 452). Let `P` be continuous with `P(0) ≥ 0`, `P(w*) = 0`, `P(w) < 0` for
`w > w*` and `P(w) > 0` for `w ∈ (w* - ε, w*)`. Then `(w*, w*)` is the unique pure Nash
equilibrium of the wage game. -/
theorem wageGame_unique {P : ℝ → ℝ} (hP : ∀ x, ContinuousWithinAt P (Set.Ici x) x)
    (h0 : 0 ≤ P 0) {ws ε : ℝ}
    (hε : 0 < ε) (hws : P ws = 0) (habove : ∀ w, ws < w → P w < 0)
    (hbelow : ∀ w, ws - ε < w → w < ws → 0 < P w) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔ w 0 = ws ∧ w 1 = ws := by
  rw [isNash_wageGame_iff]
  -- a profitable deviation just below `w*` and above any `x < w*`
  have hdev : ∀ x, x < ws → ∃ t, x < t ∧ 0 < P t := by
    intro x hx
    refine ⟨(max x (ws - ε) + ws) / 2, ?_, hbelow _ ?_ ?_⟩
    · have := le_max_left x (ws - ε); linarith
    · have := le_max_right x (ws - ε); linarith
    · have : max x (ws - ε) < ws := max_lt hx (by linarith)
      linarith
  -- the core argument for a pair with `own ≤ other`
  have core : ∀ a b, a ≤ b → WageBestReply P a b → WageBestReply P b a → a = ws ∧ b = ws := by
    intro a b hab ha hb
    have hPb : P b ≤ 0 := ha.profit_nonpos hP hab
    have hub := hb.nonneg h0
    have hPb0 : P b = 0 := by
      rcases eq_or_lt_of_le hab with heq | hlt
      · rw [heq, wageShare_of_eq] at hub; linarith
      · rw [wageShare_of_gt hlt] at hub; linarith
    have hbws : ws ≤ b := by
      by_contra hlt
      obtain ⟨t, hbt, ht⟩ := hdev b (not_le.1 hlt)
      have := ha t
      rw [wageShare_of_gt hbt] at this
      rcases eq_or_lt_of_le hab with heq | hlt'
      · rw [heq, wageShare_of_eq, hPb0] at this; linarith
      · rw [wageShare_of_lt hlt'] at this; linarith
    have hbws' : b = ws := by
      by_contra hne
      exact absurd hPb0 (habove b (lt_of_le_of_ne hbws (Ne.symm hne))).ne
    refine ⟨?_, hbws'⟩
    by_contra hne
    have halt : a < ws := lt_of_le_of_ne (hbws' ▸ hab) hne
    obtain ⟨t, hat, ht⟩ := hdev a halt
    have := hb t
    rw [wageShare_of_gt hat, wageShare_of_gt (hbws' ▸ halt), hPb0] at this
    linarith
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total (w 0) (w 1) with hle | hle
    · exact core _ _ hle h1 h2
    · exact (core _ _ hle h2 h1).symm
  · rintro ⟨e0, e1⟩
    have br : WageBestReply P ws ws := by
      intro t
      rw [wageShare_of_eq, hws, zero_div]
      rcases lt_trichotomy t ws with ht | ht | ht
      · rw [wageShare_of_lt ht]
      · rw [ht, wageShare_of_eq, hws, zero_div]
      · rw [wageShare_of_gt ht]; exact (habove t ht).le
    rw [e0, e1]
    exact ⟨br, br⟩

/-- **Proposition 13.B.1(ii)**, the argument (MWG, pp. 444-445). If `P(w) = 0` for `w ≤ w*` and
`P(w) < 0` for `w > w*`, the pure Nash equilibria of the wage game are exactly the profiles with
both wages at most `w*`. -/
theorem wageGame_flat {P : ℝ → ℝ} {ws : ℝ} (hflat : ∀ w, w ≤ ws → P w = 0)
    (habove : ∀ w, ws < w → P w < 0) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔ w 0 ≤ ws ∧ w 1 ≤ ws := by
  rw [isNash_wageGame_iff]
  have hshare : ∀ t o, t ≤ ws → wageShare t o (P t) = 0 := by
    intro t o ht
    rw [hflat t ht]; unfold wageShare; split_ifs <;> simp
  have hneg : ∀ a b, b ≤ a → ws < a → wageShare a b (P a) < 0 := by
    intro a b hba ha
    rcases eq_or_lt_of_le hba with heq | hlt
    · rw [heq, wageShare_of_eq]; linarith [habove a ha]
    · rw [wageShare_of_gt hlt]; exact habove a ha
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    rcases le_total (w 0) (w 1) with hle | hle
    · have hw1 : ws < w 1 := hcon.elim (fun h => h.trans_le hle) id
      have := h2 ws
      rw [hshare ws _ le_rfl] at this
      linarith [hneg _ _ hle hw1]
    · have hw0 : ws < w 0 := hcon.elim id (fun h => h.trans_le hle)
      have := h1 ws
      rw [hshare ws _ le_rfl] at this
      linarith [hneg _ _ hle hw0]
  · rintro ⟨h0, h1⟩
    have br : ∀ a b, a ≤ ws → b ≤ ws → WageBestReply P a b := by
      intro a b ha hb t
      rw [hshare a b ha]
      by_cases ht : t ≤ ws
      · rw [hshare t b ht]
      · exact (hneg t b (hb.trans (not_le.1 ht).le) (not_le.1 ht)).le
    exact ⟨br _ _ h0 h1, br _ _ h1 h0⟩

/-- **Section 13.C** (MWG, p. 459, small type). If `P(w) = 0` for `w < w̄` and `P(w) < 0` for
`w ≥ w̄`, the pure Nash equilibria of the wage game are the profiles with both wages below
`w̄`. -/
theorem wageGame_flat_open {P : ℝ → ℝ} {ws : ℝ} (hflat : ∀ w, w < ws → P w = 0)
    (habove : ∀ w, ws ≤ w → P w < 0) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame P) w ↔ w 0 < ws ∧ w 1 < ws := by
  rw [isNash_wageGame_iff]
  have hshare : ∀ t o, t < ws → wageShare t o (P t) = 0 := by
    intro t o ht
    rw [hflat t ht]; unfold wageShare; split_ifs <;> simp
  have hneg : ∀ a b, b ≤ a → ws ≤ a → wageShare a b (P a) < 0 := by
    intro a b hba ha
    rcases eq_or_lt_of_le hba with heq | hlt
    · rw [heq, wageShare_of_eq]; linarith [habove a ha]
    · rw [wageShare_of_gt hlt]; exact habove a ha
  have hlow : ws - 1 < ws := by linarith
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hcon
    rw [not_and_or, not_lt, not_lt] at hcon
    rcases le_total (w 0) (w 1) with hle | hle
    · have hw1 : ws ≤ w 1 := hcon.elim (fun h => h.trans hle) id
      have := h2 (ws - 1)
      rw [hshare _ _ hlow] at this
      linarith [hneg _ _ hle hw1]
    · have hw0 : ws ≤ w 0 := hcon.elim id (fun h => h.trans hle)
      have := h1 (ws - 1)
      rw [hshare _ _ hlow] at this
      linarith [hneg _ _ hle hw0]
  · rintro ⟨h0, h1⟩
    have br : ∀ a b, a < ws → b < ws → WageBestReply P a b := by
      intro a b ha hb t
      rw [hshare a b ha]
      by_cases ht : t < ws
      · rw [hshare t b ht]
      · exact (hneg t b (hb.le.trans (not_lt.1 ht)) (not_lt.1 ht)).le
    exact ⟨br _ _ h0 h1, br _ _ h1 h0⟩

end MWG.AdverseSelection
