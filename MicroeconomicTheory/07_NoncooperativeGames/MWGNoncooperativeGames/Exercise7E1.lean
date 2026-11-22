/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.Kuhn
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exercise 7.E.1: realization equivalence in the game of Figure 7.Ex.1

MWG, Exercise 7.E.1 and Figure 7.Ex.1, pp. 233-234.

Figure 7.Ex.1: player 1 chooses L, M or R at the initial node; L ends the game (`T₀`). After
M or R, player 2 chooses `ℓ` or `r` without observing which (one information set). Player 1
then chooses `x` or `y`, knowing whether she played M or R but not player 2's move: her two
nodes after M form one information set, her two nodes after R another. The terminal nodes are
`T₁, …, T₈`.

Encoding. Players `Fin 2` (`0` = player 1). Actions `Fin 7`: `0, 1, 2` = L, M, R; `3, 4` =
`ℓ, r`; `5, 6` = `x, y`. Information sets `Fin 4`: `0` the initial node, `1` player 2's,
`2` player 1's after M, `3` player 1's after R. In the game of part (d), `exercise7E1Merged`,
player 1's last two information sets are merged into `2` (labels `Fin 3`).
Payoffs are not specified by the exercise and are set to `0`.

* (a) `exercise_7_E_1a`: player 1 has `3 · 2 · 2 = 12` pure strategies, player 2 has `2`.
* (b) `exercise_7_E_1b`: every behaviour strategy of player 1 has a realization-equivalent
  mixed strategy (an instance of `kuhn_behavior_to_mixed`; the game has perfect recall).
* (c) `exercise_7_E_1c`: every mixed strategy of player 1 has a realization-equivalent
  behaviour strategy (an instance of `kuhn_mixed_to_behavior`).
* (d) `exercise_7_E_1d`: after merging, the game violates perfect recall (player 1 forgets
  whether she played M or R), the result of (b) still holds (no information set is crossed
  twice), and the result of (c) fails: the mixed strategy `½ (M, x) + ½ (R, y)` has no
  realization-equivalent behaviour strategy.
-/

namespace MWG.NoncooperativeGames

open ExtensiveForm

/-- The nodes of Figure 7.Ex.1 (most recent action first). -/
def ex7E1Nodes : Finset (List (Fin 7)) :=
  {[], [0], [1], [2], [3, 1], [4, 1], [3, 2], [4, 2],
    [5, 3, 1], [6, 3, 1], [5, 4, 1], [6, 4, 1], [5, 3, 2], [6, 3, 2], [5, 4, 2], [6, 4, 2]}

/-- The information sets of Figure 7.Ex.1. -/
def ex7E1Info (x : List (Fin 7)) : Fin 4 :=
  if x = [] then 0 else if x.length = 1 then 1 else if x.getLast? = some 1 then 2 else 3

/-- **Exercise 7.E.1, Figure 7.Ex.1** (MWG, pp. 233-234). The game of Figure 7.Ex.1. -/
def exercise7E1 : ExtensiveForm (Fin 2) (Fin 7) (Fin 4) where
  nodes := ex7E1Nodes
  nil_mem := by decide
  tail_mem := by decide
  info := ex7E1Info
  avail := ![{0, 1, 2}, {3, 4}, {5, 6}, {5, 6}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 0, some 0]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

/-- **Exercise 7.E.1(a)** (MWG, p. 233). Player 1's pure strategies choose one of L, M, R
and one of `x, y` at each of her two later information sets: `3 · 2 · 2 = 12` of them. Player
2 has the two strategies `ℓ` and `r`. -/
theorem exercise_7_E_1a :
    Fintype.card (exercise7E1.PureStrategy 0) = 12 ∧
      Fintype.card (exercise7E1.PureStrategy 1) = 2 := by
  rw [card_pureStrategy, card_pureStrategy]
  decide

/-- The game of Figure 7.Ex.1 has perfect recall. -/
theorem exercise7E1_perfectRecall : exercise7E1.PerfectRecall := by
  refine ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩
  unfold ExtensiveForm.RecallFor
  fin_cases i <;> decide

/-- **Exercise 7.E.1(b)** (MWG, p. 233). For any behaviour strategy of player 1 there is a
realization-equivalent mixed strategy. -/
theorem exercise_7_E_1b (β : Fin 4 → Fin 7 → ℝ) (hβ : exercise7E1.IsBehaviorStrategy 0 β) :
    ∃ σ : exercise7E1.PureStrategy 0 → ℝ,
      IsMixedStrategy σ ∧ exercise7E1.RealizationEquivalent 0 σ β :=
  exercise7E1.kuhn_behavior_to_mixed exercise7E1_perfectRecall.1 hβ

/-- **Exercise 7.E.1(c)** (MWG, p. 234). For any mixed strategy of player 1 there is a
realization-equivalent behaviour strategy. -/
theorem exercise_7_E_1c (σ : exercise7E1.PureStrategy 0 → ℝ) (hσ : IsMixedStrategy σ) :
    ∃ β : Fin 4 → Fin 7 → ℝ,
      exercise7E1.IsBehaviorStrategy 0 β ∧ exercise7E1.RealizationEquivalent 0 σ β :=
  exercise7E1.kuhn_mixed_to_behavior (exercise7E1_perfectRecall.2 0) hσ

/-- A pure strategy of each player in Figure 7.Ex.1 (L, `ℓ`, `x`, `x`). -/
def ex7E1Pure (j : Fin 2) : exercise7E1.PureStrategy j :=
  exercise7E1.pureOfFun j ![0, 3, 5, 5] (by revert j; decide)

/-- **Exercise 7.E.1(c)** (MWG, p. 234), against mixed rivals: an instance of
`kuhn_mixed_rivals` with player 1's induced behaviour strategy. -/
theorem exercise_7_E_1c_mixed_rivals :
    ∀ z ∈ exercise7E1.terminals,
      exercise7E1.mixedOutcome (fun j => pureMixed (ex7E1Pure j)) z =
        ∑ s : (j : Fin 2) → exercise7E1.PureStrategy j,
          (∏ j, pureMixed (ex7E1Pure j) (s j)) *
            exercise7E1.reach (exercise7E1.assemble (Function.update
              (fun j => exercise7E1.pureBeh (s j)) 0
              (exercise7E1.behaviorOfMixed (pureMixed (ex7E1Pure 0))))) z :=
  exercise7E1.kuhn_mixed_rivals (exercise7E1_perfectRecall.2 0) _
    (isMixedStrategy_pureMixed _)

/-- The information sets of the merged game of Exercise 7.E.1(d). -/
def ex7E1MergedInfo (x : List (Fin 7)) : Fin 3 :=
  if x = [] then 0 else if x.length = 1 then 1 else 2

/-- **Exercise 7.E.1(d)** (MWG, p. 234). Figure 7.Ex.1 with player 1's second-round
information sets merged into one. -/
def exercise7E1Merged : ExtensiveForm (Fin 2) (Fin 7) (Fin 3) where
  nodes := ex7E1Nodes
  nil_mem := by decide
  tail_mem := by decide
  info := ex7E1MergedInfo
  avail := ![{0, 1, 2}, {3, 4}, {5, 6}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 0]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

theorem exercise7E1Merged_info : exercise7E1Merged.info = ex7E1MergedInfo := rfl

theorem exercise7E1Merged_player :
    exercise7E1Merged.player = ![some 0, some 1, some 0] := rfl

/-- Player 1's pure strategy "M, then `x`" in the merged game. -/
def ex7E1MX : exercise7E1Merged.PureStrategy 0 :=
  exercise7E1Merged.pureOfFun 0 (fun k => if k = 0 then 1 else 5) (by decide)

/-- Player 1's pure strategy "R, then `y`" in the merged game. -/
def ex7E1RY : exercise7E1Merged.PureStrategy 0 :=
  exercise7E1Merged.pureOfFun 0 (fun k => if k = 0 then 2 else 6) (by decide)

/-- The mixed strategy `½ (M, x) + ½ (R, y)` of Exercise 7.E.1(d). -/
noncomputable def ex7E1Sigma : exercise7E1Merged.PureStrategy 0 → ℝ :=
  fun s => (1 / 2) * pureMixed ex7E1MX s + (1 / 2) * pureMixed ex7E1RY s

theorem ex7E1MX_ne_RY : ex7E1MX ≠ ex7E1RY := by
  intro h
  have := congrArg (fun s => (s ⟨0, rfl⟩).1) h
  simp [ex7E1MX, ex7E1RY, pureOfFun] at this

theorem isMixedStrategy_ex7E1Sigma : IsMixedStrategy ex7E1Sigma := by
  refine ⟨fun s => ?_, ?_⟩
  · unfold ex7E1Sigma pureMixed
    split_ifs <;> norm_num
  · simp [ex7E1Sigma, pureMixed, Finset.sum_add_distrib]
    norm_num

/-- **Exercise 7.E.1(d)** (MWG, p. 234). After merging player 1's second-round information
sets: (i) perfect recall fails, because player 1 forgets whether she played M or R
(condition (ii) fails for player 1) although no information set is crossed twice;
(ii) the result of (b) still holds; (iii) the result of (c) fails: the mixed strategy
`½ (M, x) + ½ (R, y)` has no realization-equivalent behaviour strategy. -/
theorem exercise_7_E_1d :
    ¬ exercise7E1Merged.PerfectRecall ∧ ¬ exercise7E1Merged.RecallFor 0 ∧
    exercise7E1Merged.NoAbsentMindedness ∧
    (∀ β : Fin 3 → Fin 7 → ℝ, exercise7E1Merged.IsBehaviorStrategy 0 β →
      ∃ σ : exercise7E1Merged.PureStrategy 0 → ℝ,
        IsMixedStrategy σ ∧ exercise7E1Merged.RealizationEquivalent 0 σ β) ∧
    IsMixedStrategy ex7E1Sigma ∧
    ¬ ∃ β : Fin 3 → Fin 7 → ℝ, exercise7E1Merged.IsBehaviorStrategy 0 β ∧
        exercise7E1Merged.RealizationEquivalent 0 ex7E1Sigma β := by
  have hNR : ¬ exercise7E1Merged.RecallFor 0 := by
    unfold ExtensiveForm.RecallFor; decide
  have hNA : exercise7E1Merged.NoAbsentMindedness := by
    unfold ExtensiveForm.NoAbsentMindedness; decide
  refine ⟨fun h => hNR (h.2 0), hNR, hNA, fun β hβ => exercise7E1Merged.kuhn_behavior_to_mixed
    hNA hβ, isMixedStrategy_ex7E1Sigma, ?_⟩
  rintro ⟨β, -, hRE⟩
  -- player 2 plays `ℓ`
  let F : Fin 2 → Fin 3 → Fin 7 → ℝ := fun _ _ a => if a = 3 then 1 else 0
  have key : ∀ z ∈ exercise7E1Merged.terminals,
      ((1 / 2) * exercise7E1Merged.weight (some 0) (exercise7E1Merged.pureBeh ex7E1MX) z +
        (1 / 2) * exercise7E1Merged.weight (some 0) (exercise7E1Merged.pureBeh ex7E1RY) z) *
          (exercise7E1Merged.weight none exercise7E1Merged.natureProb z *
            ∏ j, if j = 0 then 1 else exercise7E1Merged.weight (some j) (F j) z) =
        exercise7E1Merged.weight (some 0) β z *
          (exercise7E1Merged.weight none exercise7E1Merged.natureProb z *
            ∏ j, if j = 0 then 1 else exercise7E1Merged.weight (some j) (F j) z) := by
    intro z hz
    have h := hRE F z hz
    simp_rw [exercise7E1Merged.reach_update_factor 0 F] at h
    rw [← h]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    simp only [ex7E1Sigma, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp [pureMixed]
  have h1 := key [5, 3, 1] (by decide)
  have h2 := key [6, 3, 1] (by decide)
  have h6 := key [6, 3, 2] (by decide)
  have h1' : (2 : ℝ)⁻¹ = β 0 1 * β 2 5 := by
    simpa [weight_cons, F, ex7E1MX, ex7E1RY, pureBeh, pureOfFun, exercise7E1Merged_info,
      exercise7E1Merged_player, ex7E1MergedInfo, Fin.prod_univ_two] using h1
  have h2' : β 0 1 = 0 ∨ β 2 6 = 0 := by
    simpa [weight_cons, F, ex7E1MX, ex7E1RY, pureBeh, pureOfFun, exercise7E1Merged_info,
      exercise7E1Merged_player, ex7E1MergedInfo, Fin.prod_univ_two] using h2
  have h6' : (2 : ℝ)⁻¹ = β 0 2 * β 2 6 := by
    simpa [weight_cons, F, ex7E1MX, ex7E1RY, pureBeh, pureOfFun, exercise7E1Merged_info,
      exercise7E1Merged_player, ex7E1MergedInfo, Fin.prod_univ_two] using h6
  rcases h2' with h | h
  · rw [h, zero_mul] at h1'
    norm_num at h1'
  · rw [h, mul_zero] at h6'
    norm_num at h6'

end MWG.NoncooperativeGames
