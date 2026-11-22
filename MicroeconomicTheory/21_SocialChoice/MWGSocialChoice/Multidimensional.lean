/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.SinglePeaked
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Majority voting with multidimensional alternatives

MWG, Section 21.D, p. 804 (Example 21.D.5 and footnote 10) and Exercise 21.D.12, p. 815.

Example 21.D.5: three agents with linear utilities on the unit square; every alternative is
beaten by majority voting (cases (i)-(iii)), each utility has a single maximal element, and the
cone spanned by the three gradients is all of `ℝ²`. Points of the square are pairs `(x₁, x₂)`.

Exercise 21.D.12: three agents share a cost `c > 0` by taxes `(t₁, t₂, t₃) ≥ 0`; each prefers a
lower own tax. (a) No strictly positive alternative is a Condorcet winner. (b) (Discussion,
made precise:) an alternative with exactly one zero tax is not a Condorcet winner, and one in
which a single agent pays everything is a (weak) Condorcet winner.
-/

namespace MWG.SocialChoice

open Finset

/-- The utilities of Example 21.D.5: `u₁ = -2x₁ - x₂`, `u₂ = x₁ + 2x₂`, `u₃ = x₁ - x₂`. -/
def ex21D5u (i : Fin 3) (x : ℝ × ℝ) : ℝ :=
  match i with
  | 0 => -2 * x.1 - x.2
  | 1 => x.1 + 2 * x.2
  | 2 => x.1 - x.2

/-- The unit square `[0, 1]²`. -/
def unitSquare : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1}

/-- **Example 21.D.5** (MWG, p. 804), case (i): if `x₁ = 0`, then `(1/2, x₂)` is preferred by
agents 2 and 3. -/
theorem example_21_D_5_i (x : ℝ × ℝ) (hx : x ∈ unitSquare) (h0 : x.1 = 0) :
    ((1 / 2, x.2) : ℝ × ℝ) ∈ unitSquare ∧ ex21D5u 1 x < ex21D5u 1 (1 / 2, x.2) ∧
      ex21D5u 2 x < ex21D5u 2 (1 / 2, x.2) := by
  obtain ⟨-, -, h3, h4⟩ := hx
  refine ⟨⟨by norm_num, by norm_num, h3, h4⟩, ?_, ?_⟩ <;> simp only [ex21D5u, h0] <;> linarith

/-- **Example 21.D.5** (MWG, p. 804), case (ii): if `x₂ = 1`, then `(x₁, 1/2)` is preferred by
agents 1 and 3. -/
theorem example_21_D_5_ii (x : ℝ × ℝ) (hx : x ∈ unitSquare) (h1 : x.2 = 1) :
    ((x.1, 1 / 2) : ℝ × ℝ) ∈ unitSquare ∧ ex21D5u 0 x < ex21D5u 0 (x.1, 1 / 2) ∧
      ex21D5u 2 x < ex21D5u 2 (x.1, 1 / 2) := by
  obtain ⟨h1', h2, -, -⟩ := hx
  refine ⟨⟨h1', h2, by norm_num, by norm_num⟩, ?_, ?_⟩ <;> simp only [ex21D5u, h1] <;> linarith

/-- **Example 21.D.5** (MWG, p. 804), case (iii): if `x₁ > 0` and `x₂ < 1`, then for
`0 < ε ≤ min(x₁, 1 - x₂)`, `(x₁ - ε, x₂ + ε)` lies in the square and is preferred by agents
1 and 2. -/
theorem example_21_D_5_iii (x : ℝ × ℝ) (hx : x ∈ unitSquare)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ x.1) (hε2 : ε ≤ 1 - x.2) :
    ((x.1 - ε, x.2 + ε) : ℝ × ℝ) ∈ unitSquare ∧ ex21D5u 0 x < ex21D5u 0 (x.1 - ε, x.2 + ε) ∧
      ex21D5u 1 x < ex21D5u 1 (x.1 - ε, x.2 + ε) := by
  obtain ⟨-, h2, h3, -⟩ := hx
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ?_, ?_⟩ <;>
    simp only [ex21D5u] <;> linarith

/-- **Example 21.D.5** (MWG, p. 804). For every `x` in the square there is `y` in the square
preferred to `x` by two of the three agents: there is no Condorcet winner. -/
theorem example_21_D_5 (x : ℝ × ℝ) (hx : x ∈ unitSquare) :
    ∃ y ∈ unitSquare, ∃ i j : Fin 3, i ≠ j ∧ ex21D5u i x < ex21D5u i y ∧
      ex21D5u j x < ex21D5u j y := by
  by_cases h0 : x.1 = 0
  · obtain ⟨hy, h1, h2⟩ := example_21_D_5_i x hx h0
    exact ⟨_, hy, 1, 2, by decide, h1, h2⟩
  by_cases h1 : x.2 = 1
  · obtain ⟨hy, h1', h2⟩ := example_21_D_5_ii x hx h1
    exact ⟨_, hy, 0, 2, by decide, h1', h2⟩
  have hpos : 0 < x.1 := lt_of_le_of_ne hx.1 (Ne.symm h0)
  have hlt : x.2 < 1 := lt_of_le_of_ne hx.2.2.2 h1
  obtain ⟨hy, h1', h2⟩ := example_21_D_5_iii x hx (ε := min x.1 (1 - x.2))
    (lt_min hpos (by linarith)) (min_le_left _ _) (min_le_right _ _)
  exact ⟨_, hy, 0, 1, by decide, h1', h2⟩

/-- **Example 21.D.5** (MWG, p. 804). Each utility has a single maximal element on the square,
at `(0, 0)`, `(1, 1)` and `(1, 0)` respectively. -/
theorem example_21_D_5_unique_max :
    (∀ y ∈ unitSquare, y ≠ (0, 0) → ex21D5u 0 y < ex21D5u 0 (0, 0)) ∧
      (∀ y ∈ unitSquare, y ≠ (1, 1) → ex21D5u 1 y < ex21D5u 1 (1, 1)) ∧
      (∀ y ∈ unitSquare, y ≠ (1, 0) → ex21D5u 2 y < ex21D5u 2 (1, 0)) := by
  refine ⟨fun y hy hne => ?_, fun y hy hne => ?_, fun y hy hne => ?_⟩ <;>
    obtain ⟨h1, h2, h3, h4⟩ := hy <;> simp only [ex21D5u] <;> by_contra hc <;> push Not at hc <;>
    apply hne <;> ext <;> simp <;> linarith

/-- **Example 21.D.5** (MWG, p. 805). The cone spanned by the gradients `(-2, -1)`, `(1, 2)`,
`(1, -1)` is all of `ℝ²`. -/
theorem example_21_D_5_cone (v : ℝ × ℝ) :
    ∃ μ : Fin 3 → ℝ, (∀ i, 0 ≤ μ i) ∧
      v = (μ 0 * -2 + μ 1 * 1 + μ 2 * 1, μ 0 * -1 + μ 1 * 2 + μ 2 * -1) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (-2 * v.1 + v.2) / 3 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (2 * v.2 - v.1) / 3 := ⟨_, rfl⟩
  refine ⟨![a + (|a| + |b|), b + (|a| + |b|), |a| + |b|], fun i => ?_, ?_⟩
  · fin_cases i <;> simp <;> linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b]
  · ext
    · change v.1 = (a + (|a| + |b|)) * -2 + (b + (|a| + |b|)) * 1 + (|a| + |b|) * 1
      rw [ha, hb]
      ring
    · change v.2 = (a + (|a| + |b|)) * -1 + (b + (|a| + |b|)) * 2 + (|a| + |b|) * -1
      rw [ha, hb]
      ring

/-- The alternatives of Exercise 21.D.12: tax shares `t ≥ 0` with `t₁ + t₂ + t₃ = c`. -/
def taxShares (c : ℝ) : Set (Fin 3 → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ t 0 + t 1 + t 2 = c}

/-- `s` defeats `t` by majority voting when each agent prefers a lower own tax: more agents
pay strictly less under `s` than under `t`. -/
def taxDefeats (s t : Fin 3 → ℝ) : Prop :=
  (univ.filter fun i => t i < s i).card < (univ.filter fun i => s i < t i).card

/-- Count a defeat through explicit sums. -/
theorem taxDefeats_iff (s t : Fin 3 → ℝ) :
    taxDefeats s t ↔ ((if t 0 < s 0 then 1 else 0) + (if t 1 < s 1 then 1 else 0) +
      (if t 2 < s 2 then 1 else 0) : ℕ) < (if s 0 < t 0 then 1 else 0) +
        (if s 1 < t 1 then 1 else 0) + (if s 2 < t 2 then 1 else 0) := by
  simp only [taxDefeats, card_filter, Fin.sum_univ_three]

/-- **Exercise 21.D.12(a)** (MWG, p. 815). No strictly positive alternative is a Condorcet
winner: lowering the taxes of agents 1 and 2 by `ε = min(t₁, t₂)` and raising agent 3's by
`2ε` gives an alternative that defeats it. -/
theorem exercise_21_D_12a {c : ℝ} {t : Fin 3 → ℝ} (ht : t ∈ taxShares c) (hpos : ∀ i, 0 < t i) :
    ∃ s ∈ taxShares c, taxDefeats s t := by
  set ε := min (t 0) (t 1) with hε
  have hε0 : 0 < ε := lt_min (hpos 0) (hpos 1)
  have h1 : ε ≤ t 0 := min_le_left _ _
  have h2 : ε ≤ t 1 := min_le_right _ _
  refine ⟨![t 0 - ε, t 1 - ε, t 2 + 2 * ε], ⟨fun i => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> simp <;> linarith [ht.1 2]
  · simp
    linarith [ht.2]
  · rw [taxDefeats_iff]
    have a0 : ¬t 0 < t 0 - ε := by linarith
    have a1 : ¬t 1 < t 1 - ε := by linarith
    have a2 : t 2 < t 2 + 2 * ε := by linarith
    have b0 : t 0 - ε < t 0 := by linarith
    have b1 : t 1 - ε < t 1 := by linarith
    have b2 : ¬t 2 + 2 * ε < t 2 := by linarith
    simp [a0, a1, a2, b0, b1, b2]

/-- **Exercise 21.D.12(b)** (MWG, p. 815). An alternative with exactly one zero tax is not a
Condorcet winner either: the two taxed agents can both pay less if the third pays more. -/
theorem exercise_21_D_12b_one_zero {c : ℝ} {t : Fin 3 → ℝ} (ht : t ∈ taxShares c) (k : Fin 3)
    (hk : t k = 0) (hpos : ∀ j, j ≠ k → 0 < t j) : ∃ s ∈ taxShares c, taxDefeats s t := by
  fin_cases k
  · set ε := min (t 1) (t 2)
    have hε0 : 0 < ε := lt_min (hpos 1 (by decide)) (hpos 2 (by decide))
    have h1 : ε ≤ t 1 := min_le_left _ _
    have h2 : ε ≤ t 2 := min_le_right _ _
    refine ⟨![t 0 + 2 * ε, t 1 - ε, t 2 - ε], ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [ht.1 0]
    · simp
      linarith [ht.2]
    · rw [taxDefeats_iff]
      have a : ¬t 1 < t 1 - ε ∧ ¬t 2 < t 2 - ε ∧ t 0 < t 0 + 2 * ε ∧ t 1 - ε < t 1 ∧
          t 2 - ε < t 2 ∧ ¬t 0 + 2 * ε < t 0 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      simp [a]
  · set ε := min (t 0) (t 2)
    have hε0 : 0 < ε := lt_min (hpos 0 (by decide)) (hpos 2 (by decide))
    have h1 : ε ≤ t 0 := min_le_left _ _
    have h2 : ε ≤ t 2 := min_le_right _ _
    refine ⟨![t 0 - ε, t 1 + 2 * ε, t 2 - ε], ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [ht.1 1]
    · simp
      linarith [ht.2]
    · rw [taxDefeats_iff]
      have a : ¬t 0 < t 0 - ε ∧ ¬t 2 < t 2 - ε ∧ t 1 < t 1 + 2 * ε ∧ t 0 - ε < t 0 ∧
          t 2 - ε < t 2 ∧ ¬t 1 + 2 * ε < t 1 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      simp [a]
  · set ε := min (t 0) (t 1)
    have hε0 : 0 < ε := lt_min (hpos 0 (by decide)) (hpos 1 (by decide))
    have h1 : ε ≤ t 0 := min_le_left _ _
    have h2 : ε ≤ t 1 := min_le_right _ _
    refine ⟨![t 0 - ε, t 1 - ε, t 2 + 2 * ε], ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> linarith [ht.1 2]
    · simp
      linarith [ht.2]
    · rw [taxDefeats_iff]
      have a : ¬t 0 < t 0 - ε ∧ ¬t 1 < t 1 - ε ∧ t 2 < t 2 + 2 * ε ∧ t 0 - ε < t 0 ∧
          t 1 - ε < t 1 ∧ ¬t 2 + 2 * ε < t 2 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
      simp [a]

/-- **Exercise 21.D.12(b)** (MWG, p. 815). An alternative in which one agent pays the whole
cost is a Condorcet winner: no alternative is preferred by more agents than prefer it. -/
theorem exercise_21_D_12b_one_payer {c : ℝ} {t : Fin 3 → ℝ} (ht : t ∈ taxShares c) (k : Fin 3)
    (hk : ∀ j, j ≠ k → t j = 0) : ∀ s ∈ taxShares c, ¬taxDefeats s t ∧
      (s ≠ t → (univ.filter fun i => t i < s i).Nonempty) := by
  intro s hs
  have hs0 := hs.1
  have hsum := ht.2
  refine ⟨fun hd => ?_, fun hne => ?_⟩
  · have hsub : (univ.filter fun i => s i < t i) ⊆ {k} := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      by_contra hik
      have := hk i (by simpa using hik)
      linarith [hs0 i]
    have c1 := card_le_card hsub
    rw [card_singleton] at c1
    have : (univ.filter fun i => t i < s i).card = 0 := by
      unfold taxDefeats at hd
      omega
    rw [card_eq_zero, filter_eq_empty_iff] at this
    have hle : ∀ i, s i ≤ t i := fun i => not_lt.1 (this (mem_univ i))
    have hsk : s k < t k := by
      have hc := card_pos.1 (by unfold taxDefeats at hd; omega :
        0 < (univ.filter fun i => s i < t i).card)
      obtain ⟨i, hi⟩ := hc
      have hik : i = k := mem_singleton.1 (hsub hi)
      subst hik
      simpa using hi
    have hsum' : s 0 + s 1 + s 2 < t 0 + t 1 + t 2 := by
      fin_cases k <;> simp at hsk <;> linarith [hle 0, hle 1, hle 2]
    linarith [hs.2]
  · by_contra hem
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hem
    have hle : ∀ i, s i ≤ t i := fun i => not_lt.1 (hem (mem_univ i))
    apply hne
    funext i
    have htot : s 0 + s 1 + s 2 = t 0 + t 1 + t 2 := by rw [hs.2, hsum]
    fin_cases i <;> simp <;> linarith [hle 0, hle 1, hle 2]

end MWG.SocialChoice
