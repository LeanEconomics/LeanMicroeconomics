/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.EntrySim
import MWGDynamicGames.Generalized
import MWGDynamicGames.Rubinstein
import MWGNoncooperativeGames.MatchingPennies
import Mathlib.Data.Fintype.Pi

/-!
# Further examples and exercises of Chapter 9

* `proposition_9_B_3_instance`: Proposition 9.B.3 applied to Example 9.B.3 with the post-entry
  subgame: the SPNE restricted to the reduced game is an SPNE of the reduced game, and splicing
  back gives an SPNE (MWG, p. 278).
* `example_9_C_1_bayes`: the Bayes computation of p. 285: if E plays Out, In₁, In₂ with
  probabilities `1/4, 1/2, 1/4`, I's information set is reached with probability `3/4` and the
  conditional probabilities of its nodes are `2/3` and `1/3`.
* `figure_9_D_1b`: in the variant of the Niche Choice game of Figure 9.D.1(b), E staying out
  with I targeting the large niche and believing E chose the small niche is a weak PBE, while
  the small niche is strictly dominated by Out for E (MWG, pp. 292-293).
* `exercise_9_B_4_instance`: Exercise 9.B.4 applied to Matching Pennies Version B (Chapter 7),
  a two-player zero-sum game of perfect information.
* `rubinsteinHalf`, `example_9_AA_2_instance`, `example_9_AA_1_instance`: the bargaining
  games with `v = 1`, `δ = 1/2`, infinite horizon and horizon `3`.
* `exercise_9_B_5b`: in Maskin's game with player 1 moving first, player 2 has `m₂ ^ m₁`
  strategies (with simultaneous moves the strategies are the actions, `m₁` and `m₂`).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- **Proposition 9.B.3, an instance** (MWG, pp. 277-278). In Example 9.B.3, with `S` the
post-entry subgame: the unique SPNE restricted to the moves outside `S` is an SPNE of the
reduced game, and playing the subgame's SPNE in `S` and the reduced game's SPNE outside it
gives an SPNE of the whole game. -/
theorem proposition_9_B_3_instance :
    IsSPNEReduced fig9B4 [1] (pureMoves ![1, 1, 1]) (pureMoves ![1, 1, 1]) ∧
      IsSPNE fig9B4 (splice fig9B4 [1] (pureMoves ![1, 1, 1]) (pureMoves ![1, 1, 1])) := by
  have h := example_9_B_3_spne.1
  have hred := proposition_9_B_3_i fig9B4 h (x₀ := [1]) (fun _ _ => rfl)
  exact ⟨hred, proposition_9_B_3_ii fig9B4
    ((entrySim_subgames _ _ [1]).2 (Or.inr rfl)) (isSPNEIn_of_isSPNE fig9B4 h [1]) hred⟩

/-- **Section 9.C** (MWG, p. 285). In Example 9.C.1, if E plays Out, In₁ and In₂ with
probabilities `1/4, 1/2, 1/4`, I's information set is reached with probability `3/4`; by
Bayes' rule the left node has conditional probability `2/3` and the right node `1/3`. -/
theorem example_9_C_1_bayes (F : Fin 2 → Fin 2 → Fin 3 → ℝ) (hF : F 0 0 = ![1 / 4, 1 / 2, 1 / 4]) :
    probInfo fig9C1 (fig9C1.assemble F) 1 = 3 / 4 ∧
      bayesBelief fig9C1 (fig9C1.assemble F) [1] = 2 / 3 ∧
      bayesBelief fig9C1 (fig9C1.assemble F) [2] = 1 / 3 := by
  have hr := entryTwo_reach ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hasm : fig9C1.assemble F 0 = F 0 0 := entryTwo_assemble _ _ F 0
  have hi1 : fig9C1.info [1] = 1 := rfl
  have hi2 : fig9C1.info [2] = 1 := rfl
  unfold bayesBelief
  rw [hi1, hi2, (hr _).2.2, (hr _).1, (hr _).2.1, hasm, hF]
  norm_num

/-- **Figure 9.D.1(b)** (MWG, p. 293): E chooses Out, Small niche or Large niche; I, without
observing E's niche, chooses Small (`0`) or Large (`1`). -/
abbrev fig9D1b : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]

/-- **Section 9.D, Figure 9.D.1(b)** (MWG, pp. 292-293). E staying out, I targeting the large
niche and believing that E chose the small niche form a weak PBE; but the small niche is
strictly dominated for E by staying out (`−6` and `−1` are below `0`), so these beliefs are
unreasonable (forward induction). -/
theorem figure_9_D_1b :
    IsWeakPBE fig9D1b (pureMoves ![0, 1]) leftBelief ∧
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q * (-6) + (1 - q) * (-1) < 0 := by
  refine ⟨?_, fun q _ hq1 => by linarith⟩
  refine entryTwo_weakPBE_of _ _ (isBehaviorProfile_pureMoves fun k => by
    fin_cases k <;> simp [entryTwo]) (by simp [leftBelief]) (by simp [leftBelief])
    (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
  · norm_num [leftBelief, pureMoves, dirac]
  · norm_num [leftBelief, pureMoves, dirac]
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
  · intro h
    simp [pureMoves, dirac] at h

/-- **Exercise 9.B.5(b)** (MWG, p. 302). If player 1 moves first and player 2 observes her
move, player 1 has `m₁` strategies and player 2's strategies are the functions `M₁ → M₂`, of
which there are `m₂ ^ m₁`. -/
theorem exercise_9_B_5b (M₁ M₂ : Type*) [Fintype M₁] [DecidableEq M₁] [Fintype M₂] :
    Fintype.card (M₁ → M₂) = Fintype.card M₂ ^ Fintype.card M₁ := Fintype.card_fun

/-- **Exercise 9.B.4, an instance** (MWG, p. 302). Matching Pennies Version B (Chapter 7,
Figure 7.C.1) is a two-player zero-sum game of perfect information; it has a pure SPNE and all
its SPNE give the same payoffs. -/
theorem exercise_9_B_4_instance :
    ∃ F, IsSPNE matchingPenniesB F ∧ ∀ F', IsSPNE matchingPenniesB F' → ∀ i,
      cont matchingPenniesB (matchingPenniesB.assemble F') [] i =
        cont matchingPenniesB (matchingPenniesB.assemble F) [] i := by
  have hPI := example_7_C_1.1
  have hzs : ∀ z, matchingPenniesB.payoff 1 z = -matchingPenniesB.payoff 0 z := fun z => by
    simp [matchingPenniesB_payoff_def]
  obtain ⟨s, hs⟩ := (proposition_9_B_2 _ hPI).1
  exact ⟨pureB _ s, hs, fun F' hF' i =>
    exercise_9_B_4 hPI hzs hF' hs matchingPenniesB.nil_mem i⟩

/-- The bargaining game with `v = 1`, `δ₁ = δ₂ = 1/2` and horizon `T`. -/
noncomputable def bargainHalf (T : ℕ∞) : BargainingGame where
  v := 1
  δ := fun _ => 1 / 2
  T := T
  v_pos := one_pos
  δ_pos := fun _ => by norm_num
  δ_lt_one := fun _ => by norm_num

/-- **Example 9.AA.2, an instance** (MWG, p. 298). With `v = 1` and `δ = 1/2` the unique SPNE
of the infinite horizon game has the proposer offer `1/3` and keep `2/3`. -/
theorem example_9_AA_2_instance :
    (bargainHalf ⊤).IsSPNE (BargainingGame.threshold (bargainHalf ⊤).rubOffer) ∧
    ∀ σ, (bargainHalf ⊤).IsSPNE σ →
      σ.prop [] = 1 / 3 ∧ (bargainHalf ⊤).value σ [] 0 = 2 / 3 := by
  have h := (bargainHalf ⊤).example_9_AA_2 rfl rfl
  refine ⟨h.1, fun σ hσ => ?_⟩
  obtain ⟨hp, -, hv, -⟩ := h.2.2 σ hσ [] (bargainHalf ⊤).validHist_nil
  refine ⟨by rw [hp]; norm_num [bargainHalf], ?_⟩
  have : BargainingGame.proposer ([] : List ℝ).length = 0 := rfl
  rw [this] at hv
  rw [hv]
  norm_num [bargainHalf]

/-- **Example 9.AA.1, an instance** (MWG, p. 297). With `v = 1`, `δ = 1/2` and three periods,
player 1 earns `v₁*(3) = 1 − 1/2 + 1/4 = 3/4` in every SPNE. -/
theorem example_9_AA_1_instance :
    ∀ σ, (bargainHalf 3).IsSPNE σ → (bargainHalf 3).value σ [] 0 = 3 / 4 := by
  intro σ hσ
  have h := ((bargainHalf 3).example_9_AA_1 3 rfl rfl).2 σ hσ [] (bargainHalf 3).validHist_nil
    (by norm_num)
  have hp : BargainingGame.proposer ([] : List ℝ).length = 0 := rfl
  rw [hp] at h
  rw [h.1]
  norm_num [BargainingGame.finP, bargainHalf]

end MWG.DynamicGames
