/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.MatchingPennies
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Meeting in New York, Exercise 7.C.1, and two games without perfect recall

MWG, Example 7.B.3 (p. 221), Exercise 7.C.1 (p. 233) and Figure 7.C.4 (pp. 224-225).

* `meetingNY P`: the normal form of Meeting in New York with a set `P` of meeting places;
  payoffs are 100 dollars to each if they meet and 0 otherwise. The players' interests are
  completely aligned (`example_7_B_3_aligned`), yet each player's optimal choice depends on
  where he thinks the other will go (`example_7_B_3_best_reply`).
* `exercise7C1`: the game tree of Exercise 7.C.1 with the two places Grand Central Station
  (`0`) and the Empire State Building (`1`); the players choose simultaneously, which is
  drawn as Mr. Schelling not observing Mr. Thomas's choice. Its normal form is
  `meetingNY (Fin 2)` (`exercise_7_C_1`).
* `figure7C4a`, `figure7C4b`: the two games of Figure 7.C.4. In (a) player 2 forgets player
  1's first move, in (b) player 1 forgets her own first move; both violate condition (ii) of
  perfect recall for that player, while condition (i) holds.
-/

namespace MWG.NoncooperativeGames

open ExtensiveForm

/-- **Example 7.B.3** (MWG, p. 221). Meeting in New York: Mr. Thomas (`0`) and Mr. Schelling
(`1`) each choose a place in `P`; each gets 100 dollars if they choose the same place and
0 otherwise. -/
def meetingNY (P : Type*) [DecidableEq P] : NormalForm (Fin 2) (fun _ => P) where
  payoff _ s := if s 0 = s 1 then 100 else 0

/-- **Example 7.B.3** (MWG, p. 221). The players' interests are completely aligned: their
payoffs coincide at every strategy profile. -/
theorem example_7_B_3_aligned (P : Type*) [DecidableEq P] (s : (i : Fin 2) → P) :
    (meetingNY P).payoff 0 s = (meetingNY P).payoff 1 s := rfl

/-- **Example 7.B.3** (MWG, p. 221). Each player's optimal action depends on what he thinks
the other will do: against a place `p`, going to `p` is strictly better than going anywhere
else. Hence with two or more places, different beliefs call for different actions. -/
theorem example_7_B_3_best_reply (P : Type*) [DecidableEq P] (p q : P) (hq : q ≠ p) :
    (meetingNY P).payoff 0 (![q, p]) < (meetingNY P).payoff 0 (![p, p]) ∧
      (meetingNY P).payoff 1 (![p, q]) < (meetingNY P).payoff 1 (![p, p]) := by
  simp [meetingNY, hq, Ne.symm hq]

/-- **Example 7.B.3** (MWG, p. 221). Unlike Matching Pennies, Meeting in New York is not a
situation of pure conflict: it is not zero-sum. -/
theorem example_7_B_3_not_zeroSum : ¬ (meetingNY (Fin 2)).IsZeroSum := by
  intro h
  have := h (fun _ => 0)
  rw [Fin.sum_univ_two] at this
  norm_num [meetingNY] at this

/-- **Example 7.B.3** (MWG, p. 221). With the two places of Exercise 7.C.1, Mr. Thomas's best
reply to Grand Central (`0`) is Grand Central and to the Empire State Building (`1`) is the
Empire State Building. -/
theorem example_7_B_3_two_places :
    (meetingNY (Fin 2)).payoff 0 (![1, 0]) < (meetingNY (Fin 2)).payoff 0 (![0, 0]) ∧
      (meetingNY (Fin 2)).payoff 0 (![0, 1]) < (meetingNY (Fin 2)).payoff 0 (![1, 1]) :=
  ⟨(example_7_B_3_best_reply (Fin 2) 0 1 (by decide)).1,
    (example_7_B_3_best_reply (Fin 2) 1 0 (by decide)).1⟩

/-- Payoff of each player at a terminal node of the Exercise 7.C.1 tree. -/
def nyTermPay (z : List (Fin 2)) : ℝ :=
  match z with
  | b :: a :: _ => if a = b then 100 else 0
  | _ => 0

/-- **Exercise 7.C.1** (MWG, p. 233). The extensive form of Meeting in New York with two
places, Grand Central Station (`0`) and the Empire State Building (`1`): Mr. Thomas chooses
first, Mr. Schelling chooses without observing that choice (one information set). -/
def exercise7C1 : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := fun x => if x = [] then 0 else 1
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some k
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ z => nyTermPay z

theorem exercise7C1_terminals :
    exercise7C1.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

/-- **Exercise 7.C.1** (MWG, p. 233). The tree has imperfect information and perfect recall,
and its normal form is Meeting in New York with the two places. -/
theorem exercise_7_C_1 :
    ¬ exercise7C1.PerfectInformation ∧ exercise7C1.PerfectRecall ∧
    ∀ (s : (i : Fin 2) → exercise7C1.PureStrategy i) (i : Fin 2),
      exercise7C1.toNormalForm.payoff i s = (meetingNY (Fin 2)).payoff i
        (fun j => (s j ⟨j, rfl⟩).1) := by
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide,
    ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩, fun s i => ?_⟩
  · unfold ExtensiveForm.RecallFor; fin_cases i <;> decide
  have hz : [(s 1 ⟨1, rfl⟩).1, (s 0 ⟨0, rfl⟩).1] ∈ exercise7C1.terminals := by
    rw [exercise7C1_terminals]
    generalize (s 1 ⟨1, rfl⟩).1 = b
    generalize (s 0 ⟨0, rfl⟩).1 = a
    revert a b; decide
  rw [exercise7C1.toNormalForm_payoff_of_reach (by decide) s hz]
  · simp [exercise7C1, meetingNY, nyTermPay]
  · rw [reach_cons, reach_cons, reach_nil,
      show exercise7C1.info [] = 0 from rfl,
      show exercise7C1.info [(s 0 ⟨0, rfl⟩).1] = 1 from rfl,
      pureProfile_apply _ s (k := 0) (j := 0) rfl, pureProfile_apply _ s (k := 1) (j := 1) rfl]
    simp

/-- The information sets of Figure 7.C.4(a). Actions: `0, 1` = `ℓ, r`; `2, 3` = L, R;
`4, 5` = `x, y`; `6, 7` = `a, b`. -/
def fig7C4aInfo (x : List (Fin 8)) : Fin 6 :=
  if x = [] then 0 else if x = [0] then 1 else if x = [1] then 2 else if x = [3, 0] then 3
  else if x = [2, 1] then 4 else 5

/-- **Figure 7.C.4(a)** (MWG, p. 225). Player 1 chooses `ℓ` or `r`; player 2, seeing it,
chooses L or R; after (`ℓ`, R) and after (`r`, L) player 1 chooses `x` or `y`; after `x`
player 2 moves again (`a` or `b`) at one information set containing both nodes, so she no
longer knows whether player 1 chose `ℓ` or `r`. Payoffs are not given and set to `0`. -/
def figure7C4a : ExtensiveForm (Fin 2) (Fin 8) (Fin 6) where
  nodes := {[], [0], [1], [2, 0], [3, 0], [2, 1], [3, 1], [4, 3, 0], [5, 3, 0], [4, 2, 1],
    [5, 2, 1], [6, 4, 3, 0], [7, 4, 3, 0], [6, 4, 2, 1], [7, 4, 2, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := fig7C4aInfo
  avail := ![{0, 1}, {2, 3}, {2, 3}, {4, 5}, {4, 5}, {6, 7}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1, some 0, some 0, some 1]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

/-- **Figure 7.C.4(a)** (MWG, pp. 224-225). Player 2 forgets a move of player 1 that she once
knew: condition (ii) of perfect recall fails for player 2 (it holds for player 1, and
condition (i) holds), so the game does not have perfect recall. -/
theorem figure_7_C_4a :
    ¬ figure7C4a.PerfectRecall ∧ ¬ figure7C4a.RecallFor 1 ∧ figure7C4a.RecallFor 0 ∧
      figure7C4a.NoAbsentMindedness := by
  have h1 : ¬ figure7C4a.RecallFor 1 := by unfold ExtensiveForm.RecallFor; decide
  exact ⟨fun h => h1 (h.2 1), h1, by unfold ExtensiveForm.RecallFor; decide,
    by unfold ExtensiveForm.NoAbsentMindedness; decide⟩

/-- The information sets of Figure 7.C.4(b). Actions: `0, 1` = `ℓ, r`; `2, 3` = L, R;
`4, 5` = `x, y`. -/
def fig7C4bInfo (x : List (Fin 6)) : Fin 4 :=
  if x = [] then 0 else if x = [0] then 1 else if x = [1] then 2 else 3

/-- **Figure 7.C.4(b)** (MWG, p. 225). Player 1 chooses `ℓ` or `r`, player 2 sees it and
chooses L or R, and player 1 then chooses `x` or `y` at one information set containing all
four nodes: she forgets her own first move. Payoffs are not given and set to `0`. -/
def figure7C4b : ExtensiveForm (Fin 2) (Fin 6) (Fin 4) where
  nodes := {[], [0], [1], [2, 0], [3, 0], [2, 1], [3, 1], [4, 2, 0], [5, 2, 0], [4, 3, 0],
    [5, 3, 0], [4, 2, 1], [5, 2, 1], [4, 3, 1], [5, 3, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := fig7C4bInfo
  avail := ![{0, 1}, {2, 3}, {2, 3}, {4, 5}]
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1, some 0]
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun _ _ => 0

/-- **Figure 7.C.4(b)** (MWG, pp. 224-225). Player 1 forgets her own previous move:
condition (ii) of perfect recall fails for player 1 (it holds for player 2, and condition (i)
holds), so the game does not have perfect recall. -/
theorem figure_7_C_4b :
    ¬ figure7C4b.PerfectRecall ∧ ¬ figure7C4b.RecallFor 0 ∧ figure7C4b.RecallFor 1 ∧
      figure7C4b.NoAbsentMindedness := by
  have h0 : ¬ figure7C4b.RecallFor 0 := by unfold ExtensiveForm.RecallFor; decide
  exact ⟨fun h => h0 (h.2 0), h0, by unfold ExtensiveForm.RecallFor; decide,
    by unfold ExtensiveForm.NoAbsentMindedness; decide⟩

end MWG.NoncooperativeGames
