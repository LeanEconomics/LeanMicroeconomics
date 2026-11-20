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
# Matching Pennies and its variants

MWG, Examples 7.B.1, 7.C.1, 7.C.3, 7.C.4, 7.C.5, 7.D.1, 7.D.2, 7.D.3, Exercise 7.D.2,
Figures 7.C.1, 7.C.3, 7.C.5, 7.D.1 and 7.D.2 (pp. 220-231).

Encoding. Players `Fin 2`: `0` is player 1 and `1` is player 2. Actions `Fin 2`: `0` is
heads (H) and `1` is tails (T). Histories list the most recent action first, so in a
two-move game the terminal node `[b, a]` means that the first mover chose `a` and the second
mover chose `b`. Player 1's payoff is `mpPay a b = -1` if the pennies match and `+1`
otherwise; player 2's payoff is its negative.

* `matchingPennies`: the normal form of Example 7.B.1; it is zero-sum and each player's best
  action depends on the opponent's (`example_7_B_1_zero_sum`, `example_7_B_1_best_action`).
* `matchingPenniesB` (Figure 7.C.1): perfect information. Its strategies (Example 7.D.1:
  two for player 1, four for player 2) and its normal form (Example 7.D.3, Figure 7.D.1).
* `matchingPenniesC` (Figure 7.C.3, Example 7.C.3) is also the extensive form of standard
  Matching Pennies (Example 7.C.4); `matchingPenniesReversed` is the tree with the order of
  the players reversed. Both have the normal form of Example 7.B.1 (Exercise 7.D.2).
* `matchingPenniesD` (Figure 7.C.5, Example 7.C.5): a move of nature decides who moves first.
* `figure_7_D_2`: an extensive form of imperfect information whose normal form is that of
  Figure 7.D.1 (MWG, pp. 230-231).
-/

namespace MWG.NoncooperativeGames

open ExtensiveForm

/-- Player 1's payoff in Matching Pennies when she plays `a` and player 2 plays `b`: she pays
one dollar if the pennies match and receives one dollar otherwise. -/
def mpPay (a b : Fin 2) : ℝ := if a = b then -1 else 1

/-- **Example 7.B.1** (MWG, p. 220). Matching Pennies in normal form: each player has the
actions H (`0`) and T (`1`); player 1 pays player 2 a dollar if the pennies match. -/
def matchingPennies : NormalForm (Fin 2) (fun _ => Fin 2) where
  payoff i s := if i = 0 then mpPay (s 0) (s 1) else -mpPay (s 0) (s 1)

/-- **Example 7.B.1** (MWG, p. 221). Matching Pennies is zero-sum: what one player wins, the
other loses. -/
theorem example_7_B_1_zero_sum (s : (i : Fin 2) → Fin 2) :
    matchingPennies.payoff 0 s + matchingPennies.payoff 1 s = 0 := by
  simp [matchingPennies]

/-- **Section 7.B** (MWG, p. 221). A zero-sum game: at every strategy profile the players'
payoffs sum to zero (what one player wins, the others lose). -/
def NormalForm.IsZeroSum {I : Type*} [Fintype I] {S : I → Type*} (N : NormalForm I S) : Prop :=
  ∀ s, ∑ i, N.payoff i s = 0

/-- **Example 7.B.1** (MWG, p. 221). Matching Pennies is a zero-sum game. -/
theorem example_7_B_1_isZeroSum : matchingPennies.IsZeroSum := fun s => by
  rw [Fin.sum_univ_two]
  exact example_7_B_1_zero_sum s

/-- **Example 7.B.1** (MWG, p. 221). The action that maximizes player 1's payoff depends on
what player 2 does: against H the unique best action is T, against T it is H. -/
theorem example_7_B_1_best_action :
    (∀ a : Fin 2, a ≠ 1 →
      matchingPennies.payoff 0 (![a, 0]) < matchingPennies.payoff 0 (![1, 0])) ∧
    (∀ a : Fin 2, a ≠ 0 →
      matchingPennies.payoff 0 (![a, 1]) < matchingPennies.payoff 0 (![0, 1])) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩ <;> fin_cases a <;> simp_all [matchingPennies, mpPay]

/-- Player 1's payoff at a terminal node `b :: a :: _` of a two-move Matching Pennies tree
where player 1's action is `a` and player 2's is `b`. -/
def mpTermPay (z : List (Fin 2)) : ℝ :=
  match z with
  | b :: a :: _ => mpPay a b
  | _ => 0

/-- The nodes of the two-move Matching Pennies trees (Figures 7.C.1 and 7.C.3). -/
def mpNodes : Finset (List (Fin 2)) := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}

/-- The information sets of Figure 7.C.1: the initial node (`0`), after H (`1`), after T
(`2`). -/
def mpBInfo (x : List (Fin 2)) : Fin 3 := if x = [] then 0 else if x = [0] then 1 else 2

/-- **Example 7.C.1, Figure 7.C.1** (MWG, pp. 221-222). Matching Pennies Version B: player 1
moves first, player 2 sees her move and then moves. -/
def matchingPenniesB : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := mpNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpBInfo
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => if k = 0 then some 0 else some 1
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then mpTermPay z else -mpTermPay z

/-- **Example 7.C.1** (MWG, p. 222). Version B is a game of perfect information (every
information set is a singleton), hence of perfect recall. -/
theorem example_7_C_1 :
    matchingPenniesB.PerfectInformation ∧ matchingPenniesB.PerfectRecall := by
  have h : matchingPenniesB.PerfectInformation := by
    unfold ExtensiveForm.PerfectInformation; decide
  exact ⟨h, perfectRecall_of_perfectInformation _ h⟩

/-- **Example 7.C.1** (MWG, p. 222). The terminal nodes of Version B. -/
theorem matchingPenniesB_terminals :
    matchingPenniesB.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

/-- **Example 7.D.1** (MWG, p. 229). In Version B player 1 has two pure strategies and
player 2 has four. -/
theorem example_7_D_1 :
    Fintype.card (matchingPenniesB.PureStrategy 0) = 2 ∧
      Fintype.card (matchingPenniesB.PureStrategy 1) = 4 := by
  rw [card_pureStrategy, card_pureStrategy]
  decide

/-- Player 2's four strategies in Version B (Example 7.D.1): `s₁` (`m = 0`) plays H after H
and after T, `s₂` plays H after H and T after T, `s₃` plays T after H and H after T, `s₄`
plays T after both. -/
def mpBResponse (m : Fin 4) (k : Fin 3) : Fin 2 :=
  if k = 1 then (if m.val < 2 then 0 else 1) else (if m.val % 2 = 0 then 0 else 1)

/-- The pure strategy profile of Version B in which player 1 plays `a` and player 2 plays
strategy `s_{m+1}`. -/
def mpBProfile (a : Fin 2) (m : Fin 4) : (i : Fin 2) → matchingPenniesB.PureStrategy i :=
  fun i => matchingPenniesB.pureOfFun i (fun k => if i = 0 then a else mpBResponse m k)
    (fun _ _ => Finset.mem_univ _)

theorem matchingPenniesB_info : matchingPenniesB.info = mpBInfo := rfl

theorem matchingPenniesB_payoff_def (i : Fin 2) (z : List (Fin 2)) :
    matchingPenniesB.payoff i z = if i = 0 then mpTermPay z else -mpTermPay z := rfl

theorem matchingPenniesB_no_nature : ∀ k, matchingPenniesB.player k ≠ none := by decide

theorem matchingPenniesB_root_player :
    matchingPenniesB.player (matchingPenniesB.info []) = some 0 := by
  decide

theorem matchingPenniesB_second_player (a : Fin 2) :
    matchingPenniesB.player (matchingPenniesB.info [a]) = some 1 := by
  revert a; decide

/-- **Section 7.D** (MWG, p. 230). The normal form of Version B in closed form: if player 1
plays `a` and player 2 answers `b` to `a`, payoffs are those at the terminal node `[b, a]`. -/
theorem matchingPenniesB_payoff (s : (i : Fin 2) → matchingPenniesB.PureStrategy i) (i : Fin 2) :
    matchingPenniesB.toNormalForm.payoff i s =
      matchingPenniesB.payoff i
        [(s 1 ⟨matchingPenniesB.info [(s 0 ⟨_, matchingPenniesB_root_player⟩).1],
            matchingPenniesB_second_player _⟩).1,
          (s 0 ⟨_, matchingPenniesB_root_player⟩).1] := by
  refine matchingPenniesB.toNormalForm_payoff_of_reach matchingPenniesB_no_nature s ?_ ?_ i
  · rw [matchingPenniesB_terminals]
    generalize (s 0 ⟨_, matchingPenniesB_root_player⟩).1 = a
    generalize (s 1 _).1 = b
    revert a b; decide
  · rw [reach_cons, reach_cons, reach_nil, pureProfile_apply _ s matchingPenniesB_root_player,
      pureProfile_apply _ s (matchingPenniesB_second_player _)]
    simp

/-- **Example 7.D.3, Figure 7.D.1** (MWG, p. 230). The normal form of Matching Pennies
Version B: `u₁(s₁, s₂) = +1` if `(s₁, s₂)` is (H, strategy 3 or 4) or (T, strategy 1 or 3),
`u₁ = -1` otherwise, and `u₂ = -u₁`. -/
theorem example_7_D_3 (a : Fin 2) (m : Fin 4) :
    matchingPenniesB.toNormalForm.payoff 0 (mpBProfile a m) =
      (if (a = 0 ∧ (m = 2 ∨ m = 3)) ∨ (a = 1 ∧ (m = 0 ∨ m = 2)) then 1 else -1) ∧
    matchingPenniesB.toNormalForm.payoff 1 (mpBProfile a m) =
      -matchingPenniesB.toNormalForm.payoff 0 (mpBProfile a m) := by
  rw [matchingPenniesB_payoff, matchingPenniesB_payoff]
  fin_cases a <;> fin_cases m <;>
    simp [mpBProfile, pureOfFun, matchingPenniesB_info, matchingPenniesB_payoff_def, mpBInfo,
      mpBResponse, mpTermPay, mpPay]

/-- The information sets of Figure 7.C.3: the initial node (`0`) and player 2's two nodes
(`1`). -/
def mpCInfo (x : List (Fin 2)) : Fin 2 := if x = [] then 0 else 1

/-- **Example 7.C.3, Figure 7.C.3** (MWG, pp. 223-224). Matching Pennies Version C: player 2
moves without seeing player 1's covered penny; her two nodes form one information set. By
Example 7.C.4 (MWG, p. 225) this is also the extensive form of standard Matching Pennies. -/
def matchingPenniesC : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := mpNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpCInfo
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some k
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then mpTermPay z else -mpTermPay z

/-- **Example 7.C.3** (MWG, pp. 223-224). Version C has imperfect information, satisfies
perfect recall, and player 2 has the same actions at both nodes of her information set. -/
theorem example_7_C_3 :
    ¬ matchingPenniesC.PerfectInformation ∧ matchingPenniesC.PerfectRecall ∧
      ∀ a, a :: [0] ∈ matchingPenniesC.nodes ↔ a :: [1] ∈ matchingPenniesC.nodes := by
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide, ⟨?_, fun i => ?_⟩, by decide⟩
  · unfold ExtensiveForm.NoAbsentMindedness; decide
  · unfold ExtensiveForm.RecallFor; fin_cases i <;> decide

/-- **Example 7.D.2** (MWG, p. 229). In Version C each player has exactly two pure
strategies. -/
theorem example_7_D_2 :
    Fintype.card (matchingPenniesC.PureStrategy 0) = 2 ∧
      Fintype.card (matchingPenniesC.PureStrategy 1) = 2 := by
  rw [card_pureStrategy, card_pureStrategy]
  decide

theorem matchingPenniesC_terminals :
    matchingPenniesC.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

theorem matchingPenniesC_no_nature : ∀ k, matchingPenniesC.player k ≠ none := by decide

/-- **Exercise 7.D.2** (MWG, p. 230). The normal form of Matching Pennies Version C (and so
of standard Matching Pennies, whose extensive form it is by Example 7.C.4) is the game of
Example 7.B.1, each player's strategy being her action at her single information set. -/
theorem exercise_7_D_2 (s : (i : Fin 2) → matchingPenniesC.PureStrategy i) (i : Fin 2) :
    matchingPenniesC.toNormalForm.payoff i s =
      matchingPennies.payoff i (fun j => (s j ⟨j, rfl⟩).1) := by
  have hz : [(s 1 ⟨1, rfl⟩).1, (s 0 ⟨0, rfl⟩).1] ∈ matchingPenniesC.terminals := by
    rw [matchingPenniesC_terminals]
    generalize (s 1 ⟨1, rfl⟩).1 = b
    generalize (s 0 ⟨0, rfl⟩).1 = a
    revert a b; decide
  rw [matchingPenniesC.toNormalForm_payoff_of_reach matchingPenniesC_no_nature s hz]
  · simp [matchingPenniesC, matchingPennies, mpTermPay]
  · rw [reach_cons, reach_cons, reach_nil,
      show matchingPenniesC.info [] = 0 from rfl,
      show matchingPenniesC.info [(s 0 ⟨0, rfl⟩).1] = 1 from rfl,
      pureProfile_apply _ s (k := 0) (j := 0) rfl, pureProfile_apply _ s (k := 1) (j := 1) rfl]
    simp

/-- **Example 7.C.4** (MWG, p. 225). Standard Matching Pennies can equally be drawn with the
order of the decision nodes reversed: player 2 at the initial node, player 1 at an
information set containing both successor nodes. -/
def matchingPenniesReversed : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := mpNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpCInfo
  avail := fun _ => Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some (1 - k)
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then mpTermPay z.reverse else -mpTermPay z.reverse

theorem matchingPenniesReversed_terminals :
    matchingPenniesReversed.terminals = {[0, 0], [1, 0], [0, 1], [1, 1]} := by decide

/-- **Example 7.C.4** (MWG, p. 225). The reversed tree also has the normal form of Matching
Pennies: the timing of unobserved moves is irrelevant. -/
theorem example_7_C_4 (s : (i : Fin 2) → matchingPenniesReversed.PureStrategy i)
    (i : Fin 2) :
    matchingPenniesReversed.toNormalForm.payoff i s =
      matchingPennies.payoff i (fun j => (s j ⟨1 - j, by fin_cases j <;> rfl⟩).1) := by
  have hz : [(s 0 ⟨1, rfl⟩).1, (s 1 ⟨0, rfl⟩).1] ∈ matchingPenniesReversed.terminals := by
    rw [matchingPenniesReversed_terminals]
    generalize (s 0 ⟨1, rfl⟩).1 = b
    generalize (s 1 ⟨0, rfl⟩).1 = a
    revert a b; decide
  rw [matchingPenniesReversed.toNormalForm_payoff_of_reach (by decide) s hz]
  · fin_cases i <;> simp [matchingPenniesReversed, matchingPennies, mpTermPay]
  · rw [reach_cons, reach_cons, reach_nil,
      show matchingPenniesReversed.info [] = 0 from rfl,
      show matchingPenniesReversed.info [(s 1 ⟨0, rfl⟩).1] = 1 from rfl,
      pureProfile_apply _ s (k := 0) (j := 1) rfl, pureProfile_apply _ s (k := 1) (j := 0) rfl]
    simp

/-- Nature's information set and the players' singletons in Figure 7.C.5. -/
def mpDInfo (x : List (Fin 4)) : Fin 7 :=
  if x = [] then 0 else if x = [2] then 1 else if x = [3] then 2 else if x = [0, 2] then 3
  else if x = [1, 2] then 4 else if x = [0, 3] then 5 else 6

/-- The nodes of Figure 7.C.5. Actions: `0` = H, `1` = T, `2` = "player 1 moves first",
`3` = "player 2 moves first". -/
def mpDNodes : Finset (List (Fin 4)) :=
  {[], [2], [3], [0, 2], [1, 2], [0, 3], [1, 3],
    [0, 0, 2], [1, 0, 2], [0, 1, 2], [1, 1, 2], [0, 0, 3], [1, 0, 3], [0, 1, 3], [1, 1, 3]}

/-- Player 1's payoff at a terminal node of Figure 7.C.5: `-1` if the two pennies match. -/
def mpDPay (z : List (Fin 4)) : ℝ :=
  match z with
  | b :: a :: _ => if a = b then -1 else 1
  | _ => 0

/-- **Example 7.C.5, Figure 7.C.5** (MWG, p. 226). Matching Pennies Version D: a fair coin
(a move of nature with probabilities `1/2`) decides who moves first; the second mover sees
the first mover's penny. -/
noncomputable def matchingPenniesD : ExtensiveForm (Fin 2) (Fin 4) (Fin 7) where
  nodes := mpDNodes
  nil_mem := by decide
  tail_mem := by decide
  info := mpDInfo
  avail := fun k => if k = 0 then {2, 3} else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := ![none, some 0, some 1, some 1, some 1, some 0, some 0]
  natureProb := fun k a => if k = 0 ∧ (a = 2 ∨ a = 3) then 1 / 2 else 0
  nature_nonneg := fun k _ a => by split_ifs <;> norm_num
  nature_zero := fun k hk a ha => by
    fin_cases k <;> simp_all
  nature_sum := fun k hk => by
    fin_cases k <;> simp_all
    norm_num
  payoff := fun i z => if i = 0 then mpDPay z else -mpDPay z

theorem matchingPenniesD_info : matchingPenniesD.info = mpDInfo := rfl

theorem matchingPenniesD_player :
    matchingPenniesD.player = ![none, some 0, some 1, some 1, some 1, some 0, some 0] := rfl

theorem matchingPenniesD_natureProb (k : Fin 7) (a : Fin 4) :
    matchingPenniesD.natureProb k a = if k = 0 ∧ (a = 2 ∨ a = 3) then 1 / 2 else 0 := rfl

theorem matchingPenniesD_payoff (i : Fin 2) (z : List (Fin 4)) :
    matchingPenniesD.payoff i z = if i = 0 then mpDPay z else -mpDPay z := rfl

/-- **Example 7.C.5** (MWG, p. 226). Version D is a game of perfect information whose initial
node is a move of nature with two branches of probability `1/2`. -/
theorem example_7_C_5 :
    matchingPenniesD.PerfectInformation ∧
      matchingPenniesD.player (matchingPenniesD.info []) = none ∧
      matchingPenniesD.natureProb 0 2 = 1 / 2 ∧ matchingPenniesD.natureProb 0 3 = 1 / 2 := by
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide, by decide, ?_, ?_⟩ <;>
    simp [matchingPenniesD]

/-- **Example 7.C.5** (MWG, p. 226). With a move of nature, pure strategies induce a random
outcome: if both players always play H, the two terminal nodes `(H, H)` after either coin
outcome are each reached with probability `1/2`. -/
theorem example_7_C_5_random_outcome :
    let s : (i : Fin 2) → matchingPenniesD.PureStrategy i := fun i =>
      matchingPenniesD.pureOfFun i (fun _ => 0) (fun k hk => by
        fin_cases k <;> simp_all [matchingPenniesD])
    matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 2] = 1 / 2 ∧
      matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 3] = 1 / 2 ∧
      matchingPenniesD.toNormalForm.payoff 0 s = -1 := by
  intro s
  have h2 : matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 2] = 1 / 2 := by
    simp [reach_cons, pureProfile, assemble, pureBeh, s, pureOfFun, matchingPenniesD_info,
      matchingPenniesD_player, matchingPenniesD_natureProb, mpDInfo]
  have h3 : matchingPenniesD.reach (matchingPenniesD.pureProfile s) [0, 0, 3] = 1 / 2 := by
    simp [reach_cons, pureProfile, assemble, pureBeh, s, pureOfFun, matchingPenniesD_info,
      matchingPenniesD_player, matchingPenniesD_natureProb, mpDInfo]
  refine ⟨h2, h3, ?_⟩
  have hT : matchingPenniesD.terminals = {[0, 0, 2], [1, 0, 2], [0, 1, 2], [1, 1, 2],
      [0, 0, 3], [1, 0, 3], [0, 1, 3], [1, 1, 3]} := by decide
  simp only [toNormalForm, hT]
  simp [reach_cons, pureProfile, assemble, pureBeh, s, pureOfFun, matchingPenniesD_info,
    matchingPenniesD_player, matchingPenniesD_natureProb, matchingPenniesD_payoff, mpDInfo, mpDPay]
  norm_num

/-- The nodes of Figure 7.D.2. Actions: `0` = L, `1` = R (player 1), and `2, 3, 4, 5` =
`a, b, c, d` (player 2). -/
def fig7D2Nodes : Finset (List (Fin 6)) :=
  {[], [2], [3], [4], [5], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [0, 5], [1, 5]}

/-- Player 1's payoffs in Figure 7.D.2: after player 2's `a` (`c`), L gives `-1` (`+1`) and R
gives `+1` (`+1`); after `b`, both give `-1`; after `d`, L gives `+1` and R gives `-1`. -/
def fig7D2Pay (z : List (Fin 6)) : ℝ :=
  match z with
  | [l, c] =>
    if c = 2 then (if l = 0 then -1 else 1) else if c = 3 then -1 else if c = 4 then 1
    else (if l = 0 then 1 else -1)
  | _ => 0

/-- **Figure 7.D.2** (MWG, p. 231). An extensive form in which player 2 moves first, choosing
among `a, b, c, d`, and player 1 then chooses L or R without observing player 2's choice. -/
def figure_7_D_2 : ExtensiveForm (Fin 2) (Fin 6) (Fin 2) where
  nodes := fig7D2Nodes
  nil_mem := by decide
  tail_mem := by decide
  info := fun x => if x = [] then 0 else 1
  avail := fun k => if k = 0 then {2, 3, 4, 5} else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := fun k => some (1 - k)
  natureProb := fun _ _ => 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> decide)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> decide)
  payoff := fun i z => if i = 0 then fig7D2Pay z else -fig7D2Pay z

theorem figure_7_D_2_terminals : figure_7_D_2.terminals =
    {[0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [0, 5], [1, 5]} := by decide

/-- The profile of Figure 7.D.2 where player 1 plays `L` (`a = 0`) or `R` (`a = 1`) and
player 2 plays the `m`-th of `a, b, c, d`. -/
def fig7D2Profile (a : Fin 2) (m : Fin 4) : (i : Fin 2) → figure_7_D_2.PureStrategy i :=
  fun i => figure_7_D_2.pureOfFun i
    (fun k => if i = 0 then (if a = 0 then 0 else 1) else
      (if m = 0 then 2 else if m = 1 then 3 else if m = 2 then 4 else 5))
    (fun k hk => by fin_cases i <;> fin_cases k <;> fin_cases m <;> fin_cases a <;>
      simp_all [figure_7_D_2])

theorem figure_7_D_2_payoff_def (i : Fin 2) (z : List (Fin 6)) :
    figure_7_D_2.payoff i z = if i = 0 then fig7D2Pay z else -fig7D2Pay z := rfl

/-- The normal form of Figure 7.D.2: payoffs at the terminal node `[l, c]`, where player 2
chooses `c` at the initial node and player 1 chooses `l` at her information set. -/
theorem figure_7_D_2_payoff (s : (i : Fin 2) → figure_7_D_2.PureStrategy i) (i : Fin 2) :
    figure_7_D_2.toNormalForm.payoff i s =
      figure_7_D_2.payoff i [(s 0 ⟨1, rfl⟩).1, (s 1 ⟨0, rfl⟩).1] := by
  have hz : [(s 0 ⟨1, rfl⟩).1, (s 1 ⟨0, rfl⟩).1] ∈ figure_7_D_2.terminals := by
    have h0 := (s 0 ⟨1, rfl⟩).2
    have h1 := (s 1 ⟨0, rfl⟩).2
    rw [figure_7_D_2_terminals]
    generalize (s 0 ⟨1, rfl⟩).1 = l at h0 ⊢
    generalize (s 1 ⟨0, rfl⟩).1 = c at h1 ⊢
    revert l c; decide
  refine figure_7_D_2.toNormalForm_payoff_of_reach (by decide) s hz ?_ i
  rw [reach_cons, reach_cons, reach_nil,
    show figure_7_D_2.info [] = 0 from rfl,
    show figure_7_D_2.info [(s 1 ⟨0, rfl⟩).1] = 1 from rfl,
    pureProfile_apply _ s (k := 0) (j := 1) rfl, pureProfile_apply _ s (k := 1) (j := 0) rfl]
  simp

/-- **Section 7.D, small type** (MWG, pp. 230-231). Figure 7.D.2 has the normal form of
Figure 7.D.1: relabelling player 1's L, R as H, T and player 2's `a, b, c, d` as strategies
`s₁, …, s₄`, payoffs coincide with those of Version B. Yet Version B has perfect information
and Figure 7.D.2 does not: different extensive forms can have the same normal form. -/
theorem figure_7_D_2_same_normal_form :
    (∀ (a : Fin 2) (m : Fin 4) (i : Fin 2),
      figure_7_D_2.toNormalForm.payoff i (fig7D2Profile a m) =
        matchingPenniesB.toNormalForm.payoff i (mpBProfile a m)) ∧
    Fintype.card (figure_7_D_2.PureStrategy 0) = Fintype.card (matchingPenniesB.PureStrategy 0) ∧
    Fintype.card (figure_7_D_2.PureStrategy 1) = Fintype.card (matchingPenniesB.PureStrategy 1) ∧
    matchingPenniesB.PerfectInformation ∧ ¬ figure_7_D_2.PerfectInformation := by
  refine ⟨fun a m i => ?_, ?_, ?_, example_7_C_1.1,
    by unfold ExtensiveForm.PerfectInformation; decide⟩
  · rw [matchingPenniesB_payoff, figure_7_D_2_payoff]
    fin_cases a <;> fin_cases m <;> fin_cases i <;>
      simp [fig7D2Profile, pureOfFun, figure_7_D_2_payoff_def, fig7D2Pay, mpBProfile,
        matchingPenniesB_info, matchingPenniesB_payoff_def, mpBInfo, mpBResponse, mpTermPay, mpPay]
  · rw [card_pureStrategy, card_pureStrategy]; decide
  · rw [card_pureStrategy, card_pureStrategy]; decide

end MWG.NoncooperativeGames
