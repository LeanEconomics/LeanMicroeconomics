/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry

/-!
# Counterexamples to two printed claims of Section 9.B

* **Propositions 9.B.1 and 9.B.2** (MWG, pp. 272 and 276) claim uniqueness of the
  backward-induction profile and of the SPNE whenever no player has the same payoffs at two
  terminal nodes. With moves of nature this fails (`natureGame`): a single player chooses `L`
  (payoff `1`) or `R`, after which nature picks the payoff `0` or `2` with probability `1/2`.
  The three terminal payoffs are distinct, yet `L` and `R` are both derived through backward
  induction and both SPNE (`proposition_9_B_1_nature_counterexample`,
  `proposition_9_B_2_nature_counterexample`). The corrected statements (no moves of nature)
  are `proposition_9_B_1` and `proposition_9_B_2`.
* **Exercise 9.B.4** (MWG, p. 302) claims unique SPNE payoffs in finite zero-sum games of
  perfect information. With three players it fails (`zeroSum3Game`): player 1 chooses between
  payoffs `(0, 1, −1)` and `(0, −1, 1)`; both choices are SPNE, with different payoffs for
  players 2 and 3 (`exercise_9_B_4_three_player_counterexample`). The corrected statement is the
  two-player `exercise_9_B_4`.

`assemble_pureB_pureOfChoice`: the moves of the pure profile `pureOfChoice c` are those of
`pureMoves c`.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The moves of the pure profile choosing `c k` at every information set are the sure moves
`pureMoves c` (nature moves by `ρ` in both). -/
theorem assemble_pureB_pureOfChoice {I A H : Type*} [DecidableEq A] [DecidableEq I]
    (G : ExtensiveForm I A H)
    (c : H → A) (hc : ∀ k, c k ∈ G.avail k) :
    G.assemble (pureB G (pureOfChoice G c hc)) = G.assemble (pureMoves (I := I) c) := by
  funext k a
  cases hk : G.player k with
  | none => rw [G.assemble_of_none _ hk, G.assemble_of_none _ hk]
  | some j =>
    rw [assemble_pureB, G.pureProfile_apply _ hk, G.assemble_of_some _ hk]
    simp only [pureOfChoice, pureOfFun_apply, pureMoves, dirac]
    by_cases h : a = c k
    · simp [h]
    · simp [h, Ne.symm h]

/-- Payoffs of the one-player game with a move of nature: `L` gives `1`; after `R` nature
gives `0` or `2`. -/
def naturePay (z : List (Fin 2)) : ℝ :=
  if z = [0] then 1 else if z = [0, 1] then 0 else if z = [1, 1] then 2 else 0

/-- **Correction to Propositions 9.B.1-9.B.2** (MWG, pp. 272 and 276). A one-player game of
perfect information with a move of nature: the player chooses `L` (`0`) or `R` (`1`) at
information set `0`; after `R` nature (information set `1`) chooses `0` or `1` with probability
`1/2` each. -/
noncomputable def natureGame : ExtensiveForm (Fin 1) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if k = 0 then some 0 else none
  natureProb _ _ := 1 / 2
  nature_nonneg := fun _ _ _ => by norm_num
  nature_zero := fun _ _ a ha => absurd (Finset.mem_univ a) ha
  nature_sum := fun _ _ => by norm_num [Fin.sum_univ_two]
  payoff _ := naturePay

theorem natureGame_perfectInformation : natureGame.PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  decide

/-- The continuation payoffs of `natureGame` from its two decision nodes. -/
theorem natureGame_cont (f : Fin 2 → Fin 2 → ℝ) (i : Fin 1) :
    cont natureGame f [] i = f 0 0 * 1 + f 0 1 * (f 1 0 * 0 + f 1 1 * 2) ∧
    cont natureGame f [0] i = 1 ∧ cont natureGame f [1] i = f 1 0 * 0 + f 1 1 * 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cont_unfold, natureGame, Fin.sum_univ_two, naturePay]

theorem natureGame_terminals : natureGame.terminals = {[0], [0, 1], [1, 1]} := by decide

theorem natureGame_decisionNodes : natureGame.decisionNodes = {[], [1]} := by decide

/-- No player has the same payoffs at two distinct terminal nodes of `natureGame`. -/
theorem natureGame_payoff_injective :
    ∀ i, ∀ z ∈ natureGame.terminals, ∀ z' ∈ natureGame.terminals,
      natureGame.payoff i z = natureGame.payoff i z' → z = z' := by
  intro i z hz z' hz' he
  rw [natureGame_terminals] at hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl <;>
    simp [natureGame, naturePay] at he ⊢

/-- Both sure choices are one-shot optimal at every decision node of `natureGame`: from the
root, `L` gives `1` and `R` gives `(0 + 2)/2 = 1`. -/
theorem natureGame_oneShot (b : Fin 2) :
    ∀ x, natureGame.IsDecision x → OneShotOptimalAt natureGame (pureMoves ![b, 0]) x := by
  intro x hx j hj a _
  have hx' := (mem_decisionNodes _).2 hx
  rw [natureGame_decisionNodes] at hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with rfl | rfl
  · have hasm : natureGame.assemble (pureMoves (I := Fin 1) ![b, 0]) 0 = dirac b :=
      natureGame.assemble_of_some _ rfl
    have hasm1 : natureGame.assemble (pureMoves (I := Fin 1) ![b, 0]) 1 = fun _ => 1 / 2 :=
      natureGame.assemble_of_none _ rfl
    obtain ⟨h1, h2, h3⟩ := natureGame_cont (natureGame.assemble (pureMoves ![b, 0])) j
    simp only [hasm, hasm1] at h1 h3
    fin_cases a
    · change cont _ _ [0] j ≤ _
      rw [h1, h2]
      fin_cases b <;> norm_num [dirac]
    · change cont _ _ [1] j ≤ _
      rw [h1, h3]
      fin_cases b <;> norm_num [dirac]
  · simp [natureGame] at hj

/-- **Correction to Proposition 9.B.2** (MWG, p. 276). With a move of nature, distinct terminal
payoffs do not give a unique SPNE: in `natureGame` (perfect information, no player with equal
payoffs at two terminal nodes) both `L` and `R` are SPNE, and they prescribe different moves.
So the uniqueness clause needs the hypothesis "no moves of nature" (`proposition_9_B_2`). -/
theorem proposition_9_B_2_nature_counterexample :
    natureGame.PerfectInformation ∧
    (∀ i, ∀ z ∈ natureGame.terminals, ∀ z' ∈ natureGame.terminals,
      natureGame.payoff i z = natureGame.payoff i z' → z = z') ∧
    IsSPNE natureGame (pureMoves ![0, 0]) ∧ IsSPNE natureGame (pureMoves ![1, 0]) ∧
    natureGame.assemble (pureMoves ![0, 0]) 0 ≠ natureGame.assemble (pureMoves ![1, 0]) 0 := by
  refine ⟨natureGame_perfectInformation, natureGame_payoff_injective,
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _)
      (natureGame_oneShot 0),
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _)
      (natureGame_oneShot 1), fun h => ?_⟩
  have h0 := congrFun h 0
  rw [natureGame.assemble_of_some _ (show natureGame.player 0 = some 0 from rfl),
    natureGame.assemble_of_some _ (show natureGame.player 0 = some 0 from rfl)] at h0
  simp [pureMoves, dirac] at h0

/-- **Correction to Proposition 9.B.1** (MWG, p. 272). With a move of nature, distinct terminal
payoffs do not give a unique profile derived through backward induction: `natureGame` has two
(choosing `L` and choosing `R`). The uniqueness clause of `proposition_9_B_1` assumes that
nature does not move. -/
theorem proposition_9_B_1_nature_counterexample :
    natureGame.PerfectInformation ∧
    (∀ i, ∀ z ∈ natureGame.terminals, ∀ z' ∈ natureGame.terminals,
      natureGame.payoff i z = natureGame.payoff i z' → z = z') ∧
    ¬ ∃! s : (i : Fin 1) → natureGame.PureStrategy i, IsBackwardInduction natureGame s := by
  refine ⟨natureGame_perfectInformation, natureGame_payoff_injective, ?_⟩
  rintro ⟨s, -, huniq⟩
  have hc : ∀ b : Fin 2, ∀ k, (![b, 0] : Fin 2 → Fin 2) k ∈ natureGame.avail k :=
    fun _ _ => Finset.mem_univ _
  have hBI : ∀ b : Fin 2, IsBackwardInduction natureGame (pureOfChoice natureGame _ (hc b)) := by
    intro b x hx
    unfold OneShotOptimalAt
    rw [assemble_pureB_pureOfChoice]
    exact natureGame_oneShot b x hx
  have h01 := (huniq _ (hBI 0)).trans (huniq _ (hBI 1)).symm
  have := congrArg (fun t => (t 0 ⟨0, rfl⟩).1) h01
  simp [pureOfChoice] at this

/-- Payoffs `(u₁, u₂, u₃)` of the three-player zero-sum game: `(0, 1, −1)` after `0` and
`(0, −1, 1)` after `1`. -/
def zeroSum3Pay (i : Fin 3) (z : List (Fin 2)) : ℝ :=
  if z = [0] then ![0, 1, -1] i else if z = [1] then ![0, -1, 1] i else 0

/-- **Correction to Exercise 9.B.4** (MWG, p. 302). A three-player zero-sum game of perfect
information: player 1 (`0`) chooses between the terminal nodes `[0]` and `[1]`. -/
def zeroSum3Game : ExtensiveForm (Fin 3) (Fin 2) (Fin 1) where
  nodes := {[], [0], [1]}
  nil_mem := by decide
  tail_mem := by decide
  info _ := 0
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player _ := some 0
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff := zeroSum3Pay

/-- The continuation payoffs of `zeroSum3Game` from the root. -/
theorem zeroSum3Game_cont (f : Fin 1 → Fin 2 → ℝ) (i : Fin 3) :
    cont zeroSum3Game f [] i = f 0 0 * zeroSum3Pay i [0] + f 0 1 * zeroSum3Pay i [1] ∧
    cont zeroSum3Game f [0] i = zeroSum3Pay i [0] ∧
    cont zeroSum3Game f [1] i = zeroSum3Pay i [1] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cont_unfold, zeroSum3Game, Fin.sum_univ_two]

/-- **Correction to Exercise 9.B.4** (MWG, p. 302). With three players, zero-sum games of
perfect information can have SPNE with different payoffs: in `zeroSum3Game` (payoffs summing
to zero at every node) player 1 is indifferent, both of her choices are SPNE, and player 2 gets
`1` in one and `−1` in the other. The corrected statement is the two-player
`exercise_9_B_4`. -/
theorem exercise_9_B_4_three_player_counterexample :
    zeroSum3Game.PerfectInformation ∧ (∀ z, ∑ i, zeroSum3Game.payoff i z = 0) ∧
    IsSPNE zeroSum3Game (pureMoves ![0]) ∧ IsSPNE zeroSum3Game (pureMoves ![1]) ∧
    cont zeroSum3Game (zeroSum3Game.assemble (pureMoves ![0])) [] 1 = 1 ∧
    cont zeroSum3Game (zeroSum3Game.assemble (pureMoves ![1])) [] 1 = -1 := by
  have hasm : ∀ b : Fin 2, zeroSum3Game.assemble (pureMoves (I := Fin 3) ![b]) 0 = dirac b :=
    fun _ => zeroSum3Game.assemble_of_some _ rfl
  have hopt : ∀ b : Fin 2, ∀ x, zeroSum3Game.IsDecision x →
      OneShotOptimalAt zeroSum3Game (pureMoves ![b]) x := by
    intro b x hx j hj a _
    have hx' := (mem_decisionNodes _).2 hx
    have hD : zeroSum3Game.decisionNodes = {[]} := by decide
    rw [hD, Finset.mem_singleton] at hx'
    subst hx'
    obtain rfl : j = 0 := by simpa [zeroSum3Game] using hj.symm
    obtain ⟨h1, h2, h3⟩ := zeroSum3Game_cont (zeroSum3Game.assemble (pureMoves ![b])) 0
    rw [hasm] at h1
    fin_cases a
    · change cont _ _ [0] 0 ≤ _
      rw [h1, h2]
      fin_cases b <;> norm_num [dirac, zeroSum3Pay]
    · change cont _ _ [1] 0 ≤ _
      rw [h1, h3]
      fin_cases b <;> norm_num [dirac, zeroSum3Pay]
  refine ⟨by unfold ExtensiveForm.PerfectInformation; decide, fun z => ?_,
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _) (hopt 0),
    isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _) (hopt 1),
    ?_, ?_⟩
  · simp only [zeroSum3Game, zeroSum3Pay, Fin.sum_univ_three]
    split_ifs <;> simp
  · rw [(zeroSum3Game_cont _ 1).1, hasm]
    norm_num [dirac, zeroSum3Pay]
  · rw [(zeroSum3Game_cont _ 1).1, hasm]
    norm_num [dirac, zeroSum3Pay]

end MWG.DynamicGames
