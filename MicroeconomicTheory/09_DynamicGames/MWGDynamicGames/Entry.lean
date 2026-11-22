/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Zermelo
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# The entry game

MWG, Example 9.B.1 and Figures 9.B.1-9.B.2 (pp. 268-270).

Encoding: players `Fin 2` (`0` = the entrant E, `1` = the incumbent I); information sets
`Fin 2` (`0` = E's decision, `1` = I's decision after entry), and player `k` moves at
information set `k`. Actions `Fin 2`: for E `0` = Out and `1` = In; for I `0` = Fight and
`1` = Accommodate. A pure profile is a choice `c k` at each information set; `pureMoves c` is
the behaviour profile playing `c` for sure.

* `example_9_B_1_nash`: the pure Nash equilibria are exactly (out, fight if E plays "in") and
  (in, accommodate if E plays "in").
* `example_9_B_1_not_spne`: (out, fight) is not subgame perfect: fighting is not optimal in
  the post-entry subgame (an empty threat).
* `example_9_B_1_spne`: (in, accommodate) is the unique SPNE (Proposition 9.B.2), obtained by
  backward induction (the reduced game of Figure 9.B.2 gives E the payoff 2 after "in").
* `example_9_B_1_subgames`: the game has two subgames, the whole game and the post-entry
  subgame (p. 275).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The behaviour profile in which the choice `c k` is made for sure at each information
set. -/
def pureMoves {I A H : Type*} [DecidableEq A] (c : H → A) : I → H → A → ℝ :=
  fun _ k => dirac (c k)

/-- A sure choice of available actions is a behaviour profile. -/
theorem isBehaviorProfile_pureMoves {I A H : Type*} [DecidableEq A] {G : ExtensiveForm I A H}
    {c : H → A} (hc : ∀ k, c k ∈ G.avail k) : IsBehaviorProfile G (pureMoves (I := I) c) := by
  intro i k _
  refine ⟨fun a => by unfold pureMoves dirac; split_ifs <;> norm_num, fun a ha => ?_, ?_⟩
  · have : a ≠ c k := fun h => ha (h ▸ hc k)
    simp [pureMoves, dirac, this]
  · simp only [pureMoves, dirac]
    rw [Finset.sum_ite_eq' (G.avail k)]
    simp [hc k]

/-- Payoffs `(u_E, u_I)` at the terminal nodes of the entry game (Figure 9.B.1). -/
def entryPay (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  if z = [0] then (if i = 0 then 0 else 2)
  else if z = [0, 1] then (if i = 0 then -3 else -1)
  else if z = [1, 1] then (if i = 0 then 2 else 1) else 0

/-- **Example 9.B.1, Figure 9.B.1** (MWG, pp. 268-269). The entry game: E chooses Out or In;
after entry I chooses Fight or Accommodate. -/
def entryGame : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := some k
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff := entryPay

theorem entryGame_nodes : entryGame.nodes = {[], [0], [1], [0, 1], [1, 1]} := rfl
theorem entryGame_info (x : List (Fin 2)) : entryGame.info x = if x = [] then 0 else 1 := rfl
theorem entryGame_avail (k : Fin 2) : entryGame.avail k = Finset.univ := rfl
theorem entryGame_player (k : Fin 2) : entryGame.player k = some k := rfl
theorem entryGame_payoff : entryGame.payoff = entryPay := rfl

theorem entryGame_assemble (F : Fin 2 → Fin 2 → Fin 2 → ℝ) (k : Fin 2) :
    entryGame.assemble F k = F k k := entryGame.assemble_of_some F rfl

/-- The continuation payoffs of the entry game. -/
theorem entryGame_cont (f : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    cont entryGame f [] i = f 0 0 * entryPay i [0] +
      f 0 1 * (f 1 0 * entryPay i [0, 1] + f 1 1 * entryPay i [1, 1]) ∧
    cont entryGame f [1] i = f 1 0 * entryPay i [0, 1] + f 1 1 * entryPay i [1, 1] := by
  constructor <;>
  simp [cont_unfold, entryGame, Fin.sum_univ_two]

/-- **Example 9.B.1** (MWG, p. 269). The entry game is a finite game of perfect information. -/
theorem example_9_B_1_perfectInformation : entryGame.PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  decide

/-- **Example 9.B.1** (MWG, p. 269). The pure strategy Nash equilibria are exactly
`(σ_E, σ_I) = (out, fight if E plays "in")` and `(in, accommodate if E plays "in")`. -/
theorem example_9_B_1_nash (a b : Fin 2) :
    IsNashB entryGame (pureMoves ![a, b]) ↔ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  have hB : IsBehaviorProfile entryGame (pureMoves (I := Fin 2) ![a, b]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  constructor
  · intro h
    by_contra hne
    fin_cases a <;> fin_cases b <;> simp at hne
    · -- (out, accommodate): E gains by entering
      have := h.2 0 (fun _ => dirac 1) fun k hk => by
        have hk0 : k = 0 := by simpa [entryGame] using hk
        subst hk0
        exact (isBehaviorProfile_pureMoves (G := entryGame) (c := fun _ => (1 : Fin 2))
          fun _ => Finset.mem_univ _) 0 0 rfl
      simp [(entryGame_cont _ _).1, entryGame_assemble, pureMoves, dirac, entryPay] at this
      norm_num at this
    · -- (in, fight): E gains by staying out
      have := h.2 0 (fun _ => dirac 0) fun k hk => by
        have hk0 : k = 0 := by simpa [entryGame] using hk
        subst hk0
        exact (isBehaviorProfile_pureMoves (G := entryGame) (c := fun _ => (0 : Fin 2))
          fun _ => Finset.mem_univ _) 0 0 rfl
      simp [(entryGame_cont _ _).1, entryGame_assemble, pureMoves, dirac, entryPay] at this
      norm_num at this
  · intro h
    refine ⟨hB, ?_⟩
    rw [Fin.forall_fin_two]
    constructor <;> intro g hg <;>
    · have hg0 := (hg _ rfl).1
      have hg1 := (hg _ rfl).2.2
      simp only [entryGame, Fin.sum_univ_two] at hg1
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [(entryGame_cont _ _).1, entryGame_assemble, pureMoves, dirac, entryPay] <;>
        nlinarith [hg0 0, hg0 1]

/-- The decision nodes of the entry game. -/
theorem entryGame_decisionNodes : entryGame.decisionNodes = {[], [1]} := by decide

/-- The terminal nodes of the entry game. -/
theorem entryGame_terminals : entryGame.terminals = {[0], [0, 1], [1, 1]} := by decide

/-- **Example 9.B.1** (MWG, p. 275). The game has two subgames: the game as a whole and the
post-entry subgame starting at I's decision node. -/
theorem example_9_B_1_subgames (x : List (Fin 2)) :
    IsSubgameRoot entryGame x ↔ x = [] ∨ x = [1] := by
  constructor
  · intro h
    have := (mem_decisionNodes _).2 h.1
    rw [entryGame_decisionNodes] at this
    simpa using this
  · rintro (rfl | rfl) <;>
      exact isSubgameRoot_of_perfectInformation _ example_9_B_1_perfectInformation
        (by unfold IsDecision; simp [entryGame])

/-- **Example 9.B.1** (MWG, pp. 269-275). `(out, fight if E plays "in")` is not subgame
perfect: in the post-entry subgame accommodating gives I `1 > −1`. -/
theorem example_9_B_1_not_spne : ¬ IsSPNE entryGame (pureMoves ![0, 0]) := by
  intro h
  have := h.2 [1] ((example_9_B_1_subgames _).2 (Or.inr rfl)) 1 (fun _ => dirac 1) fun k hk => by
    have hk1 : k = 1 := by simpa [entryGame] using hk
    subst hk1
    exact (isBehaviorProfile_pureMoves (G := entryGame) (c := fun _ => (1 : Fin 2))
      fun _ => Finset.mem_univ _) 1 1 rfl
  simp [(entryGame_cont _ _).2, entryGame_assemble, pureMoves, dirac, entryPay] at this
  norm_num at this

/-- **Example 9.B.1, Figure 9.B.2** (MWG, pp. 270 and 275). `(in, accommodate if E plays
"in")` is the unique subgame perfect Nash equilibrium (in behaviour strategies): backward
induction first has I accommodate, then E enter in the reduced game. -/
theorem example_9_B_1_spne :
    IsSPNE entryGame (pureMoves ![1, 1]) ∧ ∀ F, IsSPNE entryGame F →
      ∀ k, entryGame.assemble F k = entryGame.assemble (pureMoves ![1, 1]) k := by
  have hPI := example_9_B_1_perfectInformation
  have hB : IsBehaviorProfile entryGame (pureMoves (I := Fin 2) ![(1 : Fin 2), 1]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  have hS : IsSPNE entryGame (pureMoves ![1, 1]) := by
    refine isSPNE_of_oneShotOptimal _ hB fun x hx => ?_
    intro j hj a _
    have hx' := (mem_decisionNodes _).2 hx
    rw [entryGame_decisionNodes] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · obtain rfl : j = 0 := by simpa [entryGame_player, entryGame_info] using hj.symm
      fin_cases a <;>
      simp [cont_unfold, entryGame_nodes, entryGame_info, entryGame_avail, entryGame_payoff,
        Fin.sum_univ_two, entryGame_assemble, pureMoves, dirac, entryPay]
    · obtain rfl : j = 1 := by simpa [entryGame_player, entryGame_info] using hj.symm
      fin_cases a <;>
      simp [cont_unfold, entryGame_nodes, entryGame_info, entryGame_avail, entryGame_payoff,
        Fin.sum_univ_two, entryGame_assemble, pureMoves, dirac, entryPay]
  refine ⟨hS, fun F hF k => (proposition_9_B_2 _ hPI).2 (fun k => by simp [entryGame])
    (fun i z hz z' hz' he => ?_) F _ hF hS k⟩
  rw [entryGame_terminals] at hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  have hz1 := hz
  have hz2 := hz'
  fin_cases i <;> rcases hz1 with rfl | rfl | rfl <;> rcases hz2 with rfl | rfl | rfl <;>
    simp [entryGame, entryPay] at he ⊢ <;> norm_num at he

end MWG.DynamicGames
