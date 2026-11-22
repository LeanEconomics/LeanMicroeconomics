/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry
import MWGDynamicGames.Beliefs
import Mathlib.Tactic.LinearCombination

/-!
# Bagwell's commitment game with observation noise

MWG, Exercise 9.C.7 and Figure 9.Ex.2 (pp. 304-305). Player 1 (`0`) chooses `B` (`0`) or `T`
(`1`); player 2 (`1`) chooses `D` (`0`) or `U` (`1`). Payoffs `(u₁, u₂)`: `(B, D) = (4, 2)`,
`(B, U) = (1, 1)`, `(T, D) = (5, 1)`, `(T, U) = (2, 2)`.

* (a) `bagA`, player 2 observing player 1's move: `exercise_9_C_7a`. The unique SPNE is
  `(B; D after B, U after T)`; the Nash equilibria (behaviour strategies) are exactly: player 1
  plays `B`, player 2 plays `D` after `B` and `D` after `T` with probability at most `2/3`; or
  player 1 plays `T`, player 2 plays `U` after `T` and `D` after `B` with probability at most
  `1/3` (so `(T; U, U)` is a further Nash equilibrium).
* (b) `bagB`, player 2 not observing: `exercise_9_C_7b`. `T` strictly dominates `B`, and the
  unique Nash equilibrium (mixed ones included) is `(T, U)`.
* (c) `bagC p`, player 2 observing a signal that is correct with probability `p ∈ (0, 1)`:
  nature moves after player 1 and chooses the signal; player 2 has two information sets
  (signal `B`, signal `T`). `exercise_9_C_7c`: `(T; U, U)` with beliefs on `T` is a weak PBE
  for every `p`, and it is the unique weak PBE in which player 1 plays a pure strategy
  (`exercise_9_C_7c_pure_unique`). The printed claim that the weak PBE is unique holds exactly
  when `1/3 < p < 2/3` (`exercise_9_C_7c_unique`); for `p ≥ 2/3` and for `p ≤ 1/3` there are
  further weak PBE in which player 1 mixes (`exercise_9_C_7c_mixed_high`,
  `exercise_9_C_7c_mixed_low`; docs/corrections.md).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs `(u₁, u₂)` of Figure 9.Ex.2 when player 1 plays `a` (`0` = B, `1` = T) and player
2 plays `d` (`0` = D, `1` = U). -/
def bagPay (i : Fin 2) (d a : Fin 2) : ℝ :=
  if a = 0 then (if d = 0 then ![4, 2] i else ![1, 1] i)
  else (if d = 0 then ![5, 1] i else ![2, 2] i)

/-- Terminal payoffs of the games of Exercise 9.C.7(a)-(b): the node `[d, a]`. -/
def bagPayAB (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  match z with
  | [d, a] => bagPay i d a
  | _ => 0

/-- **Exercise 9.C.7(a), Figure 9.Ex.2** (MWG, pp. 304-305). Player 2 observes player 1's
move: information sets `0` (player 1), `1` (player 2 after `B`), `2` (player 2 after `T`). -/
def bagA : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x = [0] then 1 else 2
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := bagPayAB

/-- **Exercise 9.C.7(b)** (MWG, p. 304). Player 2 does not observe player 1's move: one
information set `1 = {[0], [1]}` for player 2. -/
def bagB : ExtensiveForm (Fin 2) (Fin 2) (Fin 2) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := bagPayAB

/-- Continuation payoffs in `bagA`. -/
theorem bagA_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont bagA f [0, 0] i = bagPay i 0 0 ∧ cont bagA f [1, 0] i = bagPay i 1 0 ∧
    cont bagA f [0, 1] i = bagPay i 0 1 ∧ cont bagA f [1, 1] i = bagPay i 1 1 ∧
    cont bagA f [0] i = f 1 0 * bagPay i 0 0 + f 1 1 * bagPay i 1 0 ∧
    cont bagA f [1] i = f 2 0 * bagPay i 0 1 + f 2 1 * bagPay i 1 1 ∧
    cont bagA f [] i = f 0 0 * (f 1 0 * bagPay i 0 0 + f 1 1 * bagPay i 1 0) +
      f 0 1 * (f 2 0 * bagPay i 0 1 + f 2 1 * bagPay i 1 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cont_unfold, bagA, bagPayAB, Fin.sum_univ_two]

/-- Continuation payoffs in `bagB`. -/
theorem bagB_cont (f : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    cont bagB f [] i = f 0 0 * (f 1 0 * bagPay i 0 0 + f 1 1 * bagPay i 1 0) +
      f 0 1 * (f 1 0 * bagPay i 0 1 + f 1 1 * bagPay i 1 1) := by
  simp [cont_unfold, bagB, bagPayAB, Fin.sum_univ_two]

/-- The moves of a profile of `bagA`. -/
theorem bagA_assemble_eq (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    bagA.assemble F = fun k => F (![0, 1, 1] k) k := by
  funext k
  rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl <;>
    exact bagA.assemble_of_some _ rfl

/-- The moves of a profile of `bagB`. -/
theorem bagB_assemble_eq (F : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    bagB.assemble F = fun k => F k k := by
  funext k
  rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl <;>
    exact bagB.assemble_of_some _ rfl

/-- Facts about a behaviour profile of `bagA`. -/
theorem bagA_behavior {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile bagA F) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧ F 1 1 0 + F 1 1 1 = 1 ∧
      (∀ a, 0 ≤ F 1 2 a) ∧ F 1 2 0 + F 1 2 1 = 1 := by
  have h0 := hF 0 0 rfl
  have h1 := hF 1 1 rfl
  have h2 := hF 1 2 rfl
  exact ⟨h0.1, by simpa [bagA, Fin.sum_univ_two] using h0.2.2, h1.1,
    by simpa [bagA, Fin.sum_univ_two] using h1.2.2, h2.1,
    by simpa [bagA, Fin.sum_univ_two] using h2.2.2⟩

/-- A behaviour strategy of a player of `bagA` with an information set `k` of hers. -/
theorem bagA_beh {g : Fin 3 → Fin 2 → ℝ} {i : Fin 2} (hg : bagA.IsBehaviorStrategy i g)
    {k : Fin 3} (hk : bagA.player k = some i) : (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [bagA, Fin.sum_univ_two] using (hg k hk).2.2⟩

/-- A behaviour strategy of a player of `bagB` with an information set `k` of hers. -/
theorem bagB_beh {g : Fin 2 → Fin 2 → ℝ} {i : Fin 2} (hg : bagB.IsBehaviorStrategy i g)
    {k : Fin 2} (hk : bagB.player k = some i) : (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [bagB, Fin.sum_univ_two] using (hg k hk).2.2⟩

/-- Playing `a` at information set `k` and following `F i` elsewhere (in `bagA`). -/
theorem bagA_beh_update {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile bagA F)
    (i : Fin 2) (k : Fin 3) (a : Fin 2) :
    bagA.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bagA]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- Playing `a` at information set `k` and following `F i` elsewhere (in `bagB`). -/
theorem bagB_beh_update {F : Fin 2 → Fin 2 → Fin 2 → ℝ} (hF : IsBehaviorProfile bagB F)
    (i : Fin 2) (k : Fin 2) (a : Fin 2) :
    bagB.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bagB]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- Player 1's and player 2's expected payoffs in `bagA` under the moves of a profile. -/
theorem bagA_payoffs (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    cont bagA (bagA.assemble F) [] 0 = F 0 0 0 * (F 1 1 0 * 4 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 2 0 * 5 + F 1 2 1 * 2) ∧
    cont bagA (bagA.assemble F) [] 1 = F 0 0 0 * (F 1 1 0 * 2 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 2 0 * 1 + F 1 2 1 * 2) := by
  rw [(bagA_cont _ 0).2.2.2.2.2.2, (bagA_cont _ 1).2.2.2.2.2.2, bagA_assemble_eq]
  simp [bagPay]

/-- Player 1's and player 2's expected payoffs in `bagB` under the moves of a profile. -/
theorem bagB_payoffs (F : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    cont bagB (bagB.assemble F) [] 0 = F 0 0 0 * (F 1 1 0 * 4 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 1 0 * 5 + F 1 1 1 * 2) ∧
    cont bagB (bagB.assemble F) [] 1 = F 0 0 0 * (F 1 1 0 * 2 + F 1 1 1 * 1) +
      F 0 0 1 * (F 1 1 0 * 1 + F 1 1 1 * 2) := by
  rw [bagB_cont, bagB_cont, bagB_assemble_eq]
  simp [bagPay]

theorem bagA_perfectInformation : bagA.PerfectInformation := by
  unfold ExtensiveForm.PerfectInformation
  decide

/-- `(B; D after B, U after T)` is a subgame perfect Nash equilibrium of `bagA`. -/
theorem bagA_isSPNE : IsSPNE bagA (pureMoves ![0, 0, 1]) := by
  have hdec : bagA.decisionNodes = {[], [0], [1]} := by decide
  refine isSPNE_of_oneShotOptimal _ (isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _)
    fun x hx j hj a _ => ?_
  have hx' := (mem_decisionNodes _).2 hx
  rw [hdec] at hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  have hc := bagA_cont (bagA.assemble (pureMoves (I := Fin 2) ![0, 0, 1])) j
  rw [bagA_assemble_eq] at hc
  rcases hx' with rfl | rfl | rfl
  · obtain rfl : j = 0 := (Option.some.inj (hj : some 0 = some j)).symm
    rw [bagA_assemble_eq]
    fin_cases a
    · change cont _ _ [0] 0 ≤ _
      rw [hc.2.2.2.2.1, hc.2.2.2.2.2.2]
      norm_num [pureMoves, dirac, bagPay]
    · change cont _ _ [1] 0 ≤ _
      rw [hc.2.2.2.2.2.1, hc.2.2.2.2.2.2]
      norm_num [pureMoves, dirac, bagPay]
  · obtain rfl : j = 1 := (Option.some.inj (hj : some 1 = some j)).symm
    rw [bagA_assemble_eq]
    fin_cases a
    · change cont _ _ [0, 0] 1 ≤ cont _ _ [0] 1
      rw [hc.1, hc.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]
    · change cont _ _ [1, 0] 1 ≤ cont _ _ [0] 1
      rw [hc.2.1, hc.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]
  · obtain rfl : j = 1 := (Option.some.inj (hj : some 1 = some j)).symm
    rw [bagA_assemble_eq]
    fin_cases a
    · change cont _ _ [0, 1] 1 ≤ cont _ _ [1] 1
      rw [hc.2.2.1, hc.2.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]
    · change cont _ _ [1, 1] 1 ≤ cont _ _ [1] 1
      rw [hc.2.2.2.1, hc.2.2.2.2.2.1]
      norm_num [pureMoves, dirac, bagPay]

/-- The case analysis behind the Nash equilibria of `bagA` (`x`: probability of `B`, `q`, `r`:
probabilities of `D` after `B` and after `T`). -/
theorem bagA_nash_cases {x x' q r : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hs : x + x' = 1)
    (hq1 : q ≤ 1) (hr : 0 ≤ r) (e1 : x * (1 - q) ≤ 0) (e2 : x' * r ≤ 0)
    (e3 : x' * (3 * q - 3 * r - 1) ≤ 0) (e4 : x * (3 * r + 1 - 3 * q) ≤ 0) :
    (x = 1 ∧ q = 1 ∧ r ≤ 2 / 3) ∨ (x' = 1 ∧ r = 0 ∧ q ≤ 1 / 3) := by
  rcases hx'.lt_or_eq with h | h
  · have hr0 : r = 0 := le_antisymm (nonpos_of_mul_nonpos_right (by linarith) h) hr
    subst hr0
    rcases hx.lt_or_eq with h' | h'
    · have : q = 1 := le_antisymm hq1 (by nlinarith)
      subst this
      nlinarith
    · right
      have hx'1 : x' = 1 := by linarith
      subst hx'1
      exact ⟨rfl, rfl, by linarith⟩
  · left
    have hx1 : x = 1 := by linarith
    subst hx1
    have : q = 1 := le_antisymm hq1 (by linarith)
    subst this
    exact ⟨rfl, rfl, by linarith⟩

/-- The Nash equilibria of `bagA` (behaviour strategies). -/
theorem bagA_isNashB_iff (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    IsNashB bagA F ↔ IsBehaviorProfile bagA F ∧
      ((F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 0 ≤ 2 / 3) ∨
        (F 0 0 1 = 1 ∧ F 1 2 1 = 1 ∧ F 1 1 0 ≤ 1 / 3)) := by
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨hx0, hx1, hq0, hq1, hr0, hr1⟩ := bagA_behavior hF
    have hu := bagA_payoffs F
    have dev : ∀ (i : Fin 2) (k : Fin 3) (a : Fin 2),
        cont bagA (bagA.assemble (Function.update F i (Function.update (F i) k (dirac a))))
          [] i ≤ cont bagA (bagA.assemble F) [] i :=
      fun i k a => hN i _ (bagA_beh_update hF i k a)
    have dB := dev 0 0 0
    have dT := dev 0 0 1
    have dD := dev 1 1 0
    have dU := dev 1 2 1
    rw [(bagA_payoffs _).1, hu.1] at dB dT
    rw [(bagA_payoffs _).2, hu.2] at dD dU
    simp only [Fin.isValue, Function.update_self, dirac, ↓reduceIte, ne_eq, one_ne_zero,
      not_false_eq_true, Function.update_of_ne, mul_one, one_mul, zero_mul, add_zero,
      zero_ne_one, zero_add, Fin.reduceEq, add_le_add_iff_right, add_le_add_iff_left]
      at dB dT dD dU
    have P1 := congrArg (F 0 0 0 * ·) hq1
    have P2 := congrArg (F 0 0 1 * ·) hr1
    have P3 := congrArg (F 0 0 0 * ·) hr1
    have P4 := congrArg (F 0 0 1 * ·) hq1
    have P5 := congrArg (F 1 1 0 * ·) hx1
    have P6 := congrArg (F 1 2 0 * ·) hx1
    have P7 := congrArg (F 1 1 1 * ·) hx1
    have P8 := congrArg (F 1 2 1 * ·) hx1
    have e1 : F 0 0 0 * (1 - F 1 1 0) ≤ 0 := by linarith
    have e2 : F 0 0 1 * F 1 2 0 ≤ 0 := by linarith
    have e3 : F 0 0 1 * (3 * F 1 1 0 - 3 * F 1 2 0 - 1) ≤ 0 := by linarith
    have e4 : F 0 0 0 * (3 * F 1 2 0 + 1 - 3 * F 1 1 0) ≤ 0 := by linarith
    refine ⟨hF, ?_⟩
    rcases bagA_nash_cases (hx0 0) (hx0 1) hx1 (by linarith [hq0 1]) (hr0 0) e1 e2 e3 e4 with
      h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by linarith, h3⟩
  · rintro ⟨hF, hc⟩
    obtain ⟨hx0, hx1, hq0, hq1, hr0, hr1⟩ := bagA_behavior hF
    refine ⟨hF, fun i g hg => ?_⟩
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · obtain ⟨hg0, hg1⟩ := bagA_beh hg (k := 0) rfl
      rw [(bagA_payoffs _).1, (bagA_payoffs _).1, Function.update_self,
        Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        show g 0 1 = 1 - g 0 0 by linarith]
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2, show F 0 0 1 = 0 by linarith, show F 1 1 1 = 0 by linarith,
          show F 1 2 1 = 1 - F 1 2 0 by linarith]
        nlinarith [mul_nonneg (by linarith [hg0 1] : 0 ≤ 1 - g 0 0)
          (by linarith : 0 ≤ 2 / 3 - F 1 2 0)]
      · rw [h1, h2, show F 0 0 0 = 0 by linarith, show F 1 2 0 = 0 by linarith,
          show F 1 1 1 = 1 - F 1 1 0 by linarith]
        nlinarith [mul_nonneg (hg0 0) (by linarith : 0 ≤ 1 / 3 - F 1 1 0)]
    · obtain ⟨hg0, hg1⟩ := bagA_beh hg (k := 1) rfl
      obtain ⟨hh0, hh1⟩ := bagA_beh hg (k := 2) rfl
      rw [(bagA_payoffs _).2, (bagA_payoffs _).2, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2, show F 0 0 1 = 0 by linarith, show F 1 1 1 = 0 by linarith]
        linarith [hg0 1]
      · rw [h1, h2, show F 0 0 0 = 0 by linarith, show F 1 2 0 = 0 by linarith]
        linarith [hh0 0]

/-- Every SPNE of `bagA` is `(B; D after B, U after T)`. -/
theorem bagA_isSPNE_unique {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsSPNE bagA F) :
    F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 1 = 1 := by
  obtain ⟨hx0, hx1, hq0, hq1, hr0, hr1⟩ := bagA_behavior hF.1
  have o0 := oneShotOptimal_of_isSPNE bagA bagA_perfectInformation hF
    (x := []) ⟨by decide, 0, by decide⟩ 0 rfl 0 (Finset.mem_univ _)
  have o1 := oneShotOptimal_of_isSPNE bagA bagA_perfectInformation hF
    (x := [0]) ⟨by decide, 0, by decide⟩ 1 rfl 0 (Finset.mem_univ _)
  have o2 := oneShotOptimal_of_isSPNE bagA bagA_perfectInformation hF
    (x := [1]) ⟨by decide, 0, by decide⟩ 1 rfl 1 (Finset.mem_univ _)
  have hc0 := bagA_cont (bagA.assemble F) 0
  have hc1 := bagA_cont (bagA.assemble F) 1
  change cont _ _ [0, 0] 1 ≤ cont _ _ [0] 1 at o1
  change cont _ _ [1, 1] 1 ≤ cont _ _ [1] 1 at o2
  change cont _ _ [0] 0 ≤ cont _ _ [] 0 at o0
  rw [hc1.1, hc1.2.2.2.2.1] at o1
  rw [hc1.2.2.2.1, hc1.2.2.2.2.2.1] at o2
  rw [hc0.2.2.2.2.1, hc0.2.2.2.2.2.2] at o0
  simp only [Fin.isValue, bagA_assemble_eq, Nat.succ_eq_add_one, Nat.reduceAdd,
    Matrix.cons_val_one, Matrix.cons_val_zero, bagPay, ↓reduceIte, one_ne_zero, mul_one,
    Matrix.cons_val, Matrix.cons_val_fin_one] at o0 o1 o2
  have hq : F 1 1 0 = 1 := by nlinarith [hq0 0, hq0 1]
  have hr : F 1 2 1 = 1 := by nlinarith [hr0 0, hr0 1]
  have P1 := congrArg (F 0 0 0 * ·) hq
  have P2 := congrArg (F 0 0 0 * ·) (show F 1 1 1 = 0 by linarith)
  have P3 := congrArg (F 0 0 1 * ·) hr
  have P4 := congrArg (F 0 0 1 * ·) (show F 1 2 0 = 0 by linarith)
  exact ⟨by linarith [hx0 0, hx0 1], hq, hr⟩

/-- **Exercise 9.C.7(a)** (MWG, p. 304). In the game of Figure 9.Ex.2, `(B; D after B, U after
T)` is a subgame perfect Nash equilibrium, and it is the unique one (behaviour strategies).
The Nash equilibria are exactly the profiles in which either player 1 plays `B`, player 2 plays
`D` after `B` and `D` after `T` with probability at most `2/3`, or player 1 plays `T`, player 2
plays `U` after `T` and `D` after `B` with probability at most `1/3`; in particular
`(T; U, U)` is a Nash equilibrium that is not subgame perfect. -/
theorem exercise_9_C_7a :
    IsSPNE bagA (pureMoves ![0, 0, 1]) ∧
    (∀ F, IsSPNE bagA F → F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 1 = 1) ∧
    (∀ F, IsNashB bagA F ↔ IsBehaviorProfile bagA F ∧
      ((F 0 0 0 = 1 ∧ F 1 1 0 = 1 ∧ F 1 2 0 ≤ 2 / 3) ∨
        (F 0 0 1 = 1 ∧ F 1 2 1 = 1 ∧ F 1 1 0 ≤ 1 / 3))) ∧
    IsNashB bagA (pureMoves ![1, 1, 1]) ∧ ¬ IsSPNE bagA (pureMoves ![1, 1, 1]) := by
  refine ⟨bagA_isSPNE, fun F hF => bagA_isSPNE_unique hF, bagA_isNashB_iff, ?_, fun h => ?_⟩
  · refine (bagA_isNashB_iff _).2
      ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, Or.inr ?_⟩
    norm_num [pureMoves, dirac]
  · have := (bagA_isSPNE_unique h).1
    norm_num [pureMoves, dirac] at this

/-- **Exercise 9.C.7(b)** (MWG, p. 304). When player 2 cannot observe player 1's move
(`bagB`, one information set for player 2), `T` strictly dominates `B` for player 1 (`5 > 4`
and `2 > 1`), and the unique Nash equilibrium, mixed (behaviour) strategies included, is
`(T, U)`. -/
theorem exercise_9_C_7b (F : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    IsNashB bagB F ↔ IsBehaviorProfile bagB F ∧ F 0 0 1 = 1 ∧ F 1 1 1 = 1 := by
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨hx0, hx1⟩ := bagB_beh (hF 0) (k := 0) rfl
    obtain ⟨hq0, hq1⟩ := bagB_beh (hF 1) (k := 1) rfl
    have dT := hN 0 _ (bagB_beh_update hF 0 0 1)
    have dU := hN 1 _ (bagB_beh_update hF 1 1 1)
    rw [(bagB_payoffs _).1, (bagB_payoffs _).1] at dT
    rw [(bagB_payoffs _).2, (bagB_payoffs _).2] at dU
    simp only [Fin.isValue, Function.update_self, dirac, zero_ne_one, ↓reduceIte, ne_eq,
      one_ne_zero, not_false_eq_true, Function.update_of_ne, mul_one, zero_mul, one_mul,
      zero_add] at dT dU
    have P1 := congrArg (F 0 0 0 * ·) hq1
    have P2 := congrArg (F 0 0 1 * ·) hq1
    have hx : F 0 0 0 = 0 := le_antisymm (by nlinarith [hq0 0, hq0 1]) (hx0 0)
    have hx' : F 0 0 1 = 1 := by linarith
    have Q1 := congrArg (· * F 1 1 0) hx'
    have Q2 := congrArg (· * F 1 1 1) hx'
    have Q3 := congrArg (· * F 1 1 0) hx
    have Q4 := congrArg (· * F 1 1 1) hx
    refine ⟨hF, hx', by linarith [hq0 0]⟩
  · rintro ⟨hF, hx, hq⟩
    obtain ⟨hx0, hx1⟩ := bagB_beh (hF 0) (k := 0) rfl
    obtain ⟨hq0, hq1⟩ := bagB_beh (hF 1) (k := 1) rfl
    have hx0' : F 0 0 0 = 0 := by linarith
    have hq0' : F 1 1 0 = 0 := by linarith
    refine ⟨hF, fun i g hg => ?_⟩
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · obtain ⟨hg0, hg1⟩ := bagB_beh hg (k := 0) rfl
      rw [(bagB_payoffs _).1, (bagB_payoffs _).1, Function.update_self,
        Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), hx0', hx, hq0', hq]
      linarith [hg0 0]
    · obtain ⟨hg0, hg1⟩ := bagB_beh hg (k := 1) rfl
      rw [(bagB_payoffs _).2, (bagB_payoffs _).2, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), hx0', hx, hq0', hq]
      linarith [hg0 0]

/-- Terminal payoffs of the game of Exercise 9.C.7(c): the node `[d, s, a]` (player 1's move
`a`, the signal `s`, player 2's move `d`). -/
def bagPayC (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  match z with
  | [d, _, a] => bagPay i d a
  | _ => 0

/-- Nature's probabilities in the game of Exercise 9.C.7(c): after `B` (information set `1`)
the signal is `B` (`0`) with probability `p`; after `T` (information set `2`) it is `T` (`1`)
with probability `p`. -/
def bagNature (p : ℝ) (k : Fin 5) (s : Fin 2) : ℝ :=
  if k = 1 then (if s = 0 then p else 1 - p) else if k = 2 then (if s = 1 then p else 1 - p)
  else 0

/-- The information sets of the game of Exercise 9.C.7(c): `0` player 1; `1`, `2` nature
after `B`, `T`; `3` player 2 after signal `B` (nodes `[0, 0]`, `[0, 1]`); `4` player 2 after
signal `T` (nodes `[1, 0]`, `[1, 1]`). -/
def bagInfoC (x : List (Fin 2)) : Fin 5 :=
  if x = [] then 0 else if x = [0] then 1 else if x = [1] then 2
  else if x = [0, 0] ∨ x = [0, 1] then 3 else 4

/-- The nodes of the game of Exercise 9.C.7(c). -/
def bagCNodes : Finset (List (Fin 2)) :=
  {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 0, 0], [1, 0, 0], [0, 1, 0], [1, 1, 0],
    [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]}

/-- **Exercise 9.C.7(c)** (MWG, p. 305). Player 2 observes player 1's move correctly with
probability `p` and incorrectly with probability `1 − p`: nature chooses the signal after
player 1's move, and player 2 knows only the signal. -/
def bagC (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : ExtensiveForm (Fin 2) (Fin 2) (Fin 5) where
  nodes := bagCNodes
  nil_mem := by decide
  tail_mem := by decide
  info := bagInfoC
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, none, none, some 1, some 1]
  natureProb := bagNature p
  nature_nonneg := fun _ _ _ => by unfold bagNature; split_ifs <;> linarith [hp.1, hp.2]
  nature_zero := fun _ _ a ha => absurd (Finset.mem_univ a) ha
  nature_sum := fun k hk => by
    rcases (by decide : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) k with
      rfl | rfl | rfl | rfl | rfl
    · simp at hk
    · simp [bagNature, Fin.sum_univ_two]
    · simp [bagNature, Fin.sum_univ_two]
    · simp at hk
    · simp at hk
  payoff := bagPayC

variable {p : ℝ} {hp : p ∈ Set.Icc (0 : ℝ) 1}

/-- Continuation payoffs in `bagC p` (`f` any move function). -/
theorem bagC_cont (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (bagC p hp) f [0, 0] i = f 3 0 * bagPay i 0 0 + f 3 1 * bagPay i 1 0 ∧
    cont (bagC p hp) f [0, 1] i = f 3 0 * bagPay i 0 1 + f 3 1 * bagPay i 1 1 ∧
    cont (bagC p hp) f [1, 0] i = f 4 0 * bagPay i 0 0 + f 4 1 * bagPay i 1 0 ∧
    cont (bagC p hp) f [1, 1] i = f 4 0 * bagPay i 0 1 + f 4 1 * bagPay i 1 1 ∧
    cont (bagC p hp) f [] i =
      f 0 0 * (f 1 0 * (f 3 0 * bagPay i 0 0 + f 3 1 * bagPay i 1 0) +
        f 1 1 * (f 4 0 * bagPay i 0 0 + f 4 1 * bagPay i 1 0)) +
      f 0 1 * (f 2 0 * (f 3 0 * bagPay i 0 1 + f 3 1 * bagPay i 1 1) +
        f 2 1 * (f 4 0 * bagPay i 0 1 + f 4 1 * bagPay i 1 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [cont_unfold, bagC, bagCNodes, bagPayC, bagInfoC, Fin.sum_univ_two]

theorem bagC_infoSet : (bagC p hp).infoSet 0 = {[]} ∧ (bagC p hp).infoSet 1 = {[0]} ∧
    (bagC p hp).infoSet 2 = {[1]} ∧ (bagC p hp).infoSet 3 = {[0, 0], [0, 1]} ∧
    (bagC p hp).infoSet 4 = {[1, 0], [1, 1]} := by
  have key : ∀ k, (bagC p hp).infoSet k =
      (bagCNodes.filter fun x => ∃ b, b :: x ∈ bagCNodes).filter fun x => bagInfoC x = k :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [key] <;> decide

theorem bagC_assemble (F : Fin 2 → Fin 5 → Fin 2 → ℝ) :
    (bagC p hp).assemble F 0 = F 0 0 ∧ (bagC p hp).assemble F 1 = bagNature p 1 ∧
      (bagC p hp).assemble F 2 = bagNature p 2 ∧ (bagC p hp).assemble F 3 = F 1 3 ∧
      (bagC p hp).assemble F 4 = F 1 4 :=
  ⟨(bagC p hp).assemble_of_some _ rfl, (bagC p hp).assemble_of_none _ rfl,
    (bagC p hp).assemble_of_none _ rfl, (bagC p hp).assemble_of_some _ rfl,
    (bagC p hp).assemble_of_some _ rfl⟩

/-- Player 1's expected payoff in `bagC p` when she plays `B` with probability `x`, `T` with
probability `x'`, and player 2 plays `D` with probabilities `qB`, `qT` after the two signals. -/
theorem bagC_payoff0 (F : Fin 2 → Fin 5 → Fin 2 → ℝ) :
    cont (bagC p hp) ((bagC p hp).assemble F) [] 0 =
      F 0 0 0 * (p * (F 1 3 0 * 4 + F 1 3 1) + (1 - p) * (F 1 4 0 * 4 + F 1 4 1)) +
      F 0 0 1 * ((1 - p) * (F 1 3 0 * 5 + F 1 3 1 * 2) + p * (F 1 4 0 * 5 + F 1 4 1 * 2)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := bagC_assemble (p := p) (hp := hp) F
  rw [(bagC_cont _ 0).2.2.2.2, h0, h1, h2, h3, h4]
  simp [bagPay, bagNature]

/-- Expected payoffs at the information sets of `bagC p` given beliefs `μ`. -/
theorem bagC_condPayoff (f : Fin 5 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) (i : Fin 2) :
    condPayoff (bagC p hp) f μ 0 i = μ [] * cont (bagC p hp) f [] i ∧
    condPayoff (bagC p hp) f μ 3 i = μ [0, 0] * cont (bagC p hp) f [0, 0] i +
      μ [0, 1] * cont (bagC p hp) f [0, 1] i ∧
    condPayoff (bagC p hp) f μ 4 i = μ [1, 0] * cont (bagC p hp) f [1, 0] i +
      μ [1, 1] * cont (bagC p hp) f [1, 1] i := by
  obtain ⟨h0, -, -, h3, h4⟩ := bagC_infoSet (p := p) (hp := hp)
  unfold condPayoff
  rw [h0, h3, h4]
  refine ⟨by simp, ?_, ?_⟩ <;> rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem bagC_reach (f : Fin 5 → Fin 2 → ℝ) :
    probInfo (bagC p hp) f 0 = 1 ∧ probInfo (bagC p hp) f 1 = f 0 0 ∧
    probInfo (bagC p hp) f 2 = f 0 1 ∧
    probInfo (bagC p hp) f 3 = f 0 0 * f 1 0 + f 0 1 * f 2 0 ∧
    probInfo (bagC p hp) f 4 = f 0 0 * f 1 1 + f 0 1 * f 2 1 ∧
    (bagC p hp).reach f [] = 1 ∧ (bagC p hp).reach f [0] = f 0 0 ∧
    (bagC p hp).reach f [1] = f 0 1 ∧
    (bagC p hp).reach f [0, 0] = f 0 0 * f 1 0 ∧ (bagC p hp).reach f [0, 1] = f 0 1 * f 2 0 ∧
    (bagC p hp).reach f [1, 0] = f 0 0 * f 1 1 ∧ (bagC p hp).reach f [1, 1] = f 0 1 * f 2 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := bagC_infoSet (p := p) (hp := hp)
  have r00 : (bagC p hp).reach f [0, 0] = f 0 0 * f 1 0 := by simp [bagC, bagInfoC]
  have r01 : (bagC p hp).reach f [0, 1] = f 0 1 * f 2 0 := by simp [bagC, bagInfoC]
  have r10 : (bagC p hp).reach f [1, 0] = f 0 0 * f 1 1 := by simp [bagC, bagInfoC]
  have r11 : (bagC p hp).reach f [1, 1] = f 0 1 * f 2 1 := by simp [bagC, bagInfoC]
  have r0 : (bagC p hp).reach f [0] = f 0 0 := by simp [bagC, bagInfoC]
  have r1 : (bagC p hp).reach f [1] = f 0 1 := by simp [bagC, bagInfoC]
  have rn : (bagC p hp).reach f [] = 1 := by simp
  unfold probInfo
  rw [h0, h1, h2, h3, h4, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.sum_singleton]
  exact ⟨rn, r0, r1, by rw [r00, r01], by rw [r10, r11], rn, r0, r1, r00, r01, r10, r11⟩

/-- A behaviour strategy of a player of `bagC p` at one of her information sets. -/
theorem bagC_beh {g : Fin 5 → Fin 2 → ℝ} {i : Fin 2} (hg : (bagC p hp).IsBehaviorStrategy i g)
    {k : Fin 5} (hk : (bagC p hp).player k = some i) : (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [bagC, Fin.sum_univ_two] using (hg k hk).2.2⟩

/-- Playing `a` at information set `k` and following `F i` elsewhere (in `bagC p`). -/
theorem bagC_beh_update {F : Fin 2 → Fin 5 → Fin 2 → ℝ} (hF : IsBehaviorProfile (bagC p hp) F)
    (i : Fin 2) (k : Fin 5) (a : Fin 2) :
    (bagC p hp).IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [bagC]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- The probability of each of player 2's information sets in `bagC p` is positive. -/
theorem bagC_probInfo_pos (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {x x' : ℝ} (hx : 0 ≤ x)
    (hx' : 0 ≤ x') (hs : x + x' = 1) : 0 < x * p + x' * (1 - p) ∧ 0 < x * (1 - p) + x' * p := by
  obtain ⟨h0, h1⟩ := hp'
  rcases le_total p (1 - p) with h | h
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left h hx']
    · nlinarith [mul_le_mul_of_nonneg_left h hx]
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_left h hx]
    · nlinarith [mul_le_mul_of_nonneg_left h hx']

/-- The moves of a profile of `bagC p`. -/
theorem bagC_assemble_eq (F : Fin 2 → Fin 5 → Fin 2 → ℝ) :
    (bagC p hp).assemble F = fun k => if k = 1 then bagNature p 1 else if k = 2 then
      bagNature p 2 else F (![0, 0, 0, 1, 1] k) k := by
  funext k
  rcases (by decide : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) k with
    rfl | rfl | rfl | rfl | rfl
  · exact (bagC p hp).assemble_of_some _ rfl
  · exact (bagC p hp).assemble_of_none _ rfl
  · exact (bagC p hp).assemble_of_none _ rfl
  · exact (bagC p hp).assemble_of_some _ rfl
  · exact (bagC p hp).assemble_of_some _ rfl

/-- Player 2's expected payoff at the information set of signal `B`. -/
theorem bagC_cond3 (f : Fin 5 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) :
    condPayoff (bagC p hp) f μ 3 1 =
      μ [0, 0] * (f 3 0 * 2 + f 3 1) + μ [0, 1] * (f 3 0 + f 3 1 * 2) := by
  rw [(bagC_condPayoff f μ 1).2.1, (bagC_cont f 1).1, (bagC_cont f 1).2.1]
  simp [bagPay]

/-- Player 2's expected payoff at the information set of signal `T`. -/
theorem bagC_cond4 (f : Fin 5 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) :
    condPayoff (bagC p hp) f μ 4 1 =
      μ [1, 0] * (f 4 0 * 2 + f 4 1) + μ [1, 1] * (f 4 0 + f 4 1 * 2) := by
  rw [(bagC_condPayoff f μ 1).2.2, (bagC_cont f 1).2.2.1, (bagC_cont f 1).2.2.2.1]
  simp [bagPay]

theorem dirac_fin2 : dirac (0 : Fin 2) 0 = 1 ∧ dirac (0 : Fin 2) 1 = 0 ∧
    dirac (1 : Fin 2) 0 = 0 ∧ dirac (1 : Fin 2) 1 = 1 := by
  simp [dirac]

/-- The conditions satisfied by a weak PBE of `bagC p` (`x`, `x'`: player 1's probabilities of
`B`, `T`; `qB`, `qT`: player 2's probabilities of `D` after the signals `B`, `T`): Bayes' rule
at both of player 2's information sets, player 2's sequential rationality (`D` only if the
belief on `B` is at least `1/2`, `U` only if it is at most `1/2`), and player 1's optimality
(`T` gains `1 + 3 (qT − qB)(2p − 1)` over `B`). -/
theorem bagC_weakPBE_facts (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {F : Fin 2 → Fin 5 → Fin 2 → ℝ}
    {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ) :
    F 0 0 0 * (1 + 3 * (F 1 4 0 - F 1 3 0) * (2 * p - 1)) ≤ 0 ∧
    0 ≤ F 0 0 1 * (1 + 3 * (F 1 4 0 - F 1 3 0) * (2 * p - 1)) ∧
    (1 - F 1 3 0) * (F 0 0 0 * p - F 0 0 1 * (1 - p)) ≤ 0 ∧
    F 1 3 0 * (F 0 0 1 * (1 - p) - F 0 0 0 * p) ≤ 0 ∧
    (1 - F 1 4 0) * (F 0 0 0 * (1 - p) - F 0 0 1 * p) ≤ 0 ∧
    F 1 4 0 * (F 0 0 1 * p - F 0 0 0 * (1 - p)) ≤ 0 ∧
    μ [0, 0] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 0 * p ∧
    μ [0, 1] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 1 * (1 - p) ∧
    μ [1, 0] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 0 * (1 - p) ∧
    μ [1, 1] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 1 * p := by
  obtain ⟨hF, -, hSR, hB⟩ := h
  obtain ⟨hx0, hx1⟩ := bagC_beh (hF 0) (k := 0) rfl
  obtain ⟨hq0, hq1⟩ := bagC_beh (hF 1) (k := 3) rfl
  obtain ⟨hr0, hr1⟩ := bagC_beh (hF 1) (k := 4) rfl
  obtain ⟨P3, P4⟩ := bagC_probInfo_pos hp' (hx0 0) (hx0 1) hx1
  obtain ⟨a0, a1, a2, a3, a4⟩ := bagC_assemble (p := p) (hp := hp) F
  obtain ⟨p0, -, -, p3, p4, rn, -, -, r00, r01, r10, r11⟩ :=
    bagC_reach (p := p) (hp := hp) ((bagC p hp).assemble F)
  obtain ⟨h0, -, -, h3, h4⟩ := bagC_infoSet (p := p) (hp := hp)
  have n10 : bagNature p 1 0 = p := by simp [bagNature]
  have n11 : bagNature p 1 1 = 1 - p := by simp [bagNature]
  have n20 : bagNature p 2 0 = 1 - p := by simp [bagNature]
  have n21 : bagNature p 2 1 = p := by simp [bagNature]
  simp only [a0, a1, a2, n10, n11, n20, n21] at p3 p4 r00 r01 r10 r11
  -- Bayes' rule
  have hpos3 : 0 < probInfo (bagC p hp) ((bagC p hp).assemble F) 3 := by rw [p3]; exact P3
  have hpos4 : 0 < probInfo (bagC p hp) ((bagC p hp).assemble F) 4 := by rw [p4]; exact P4
  have b00 := hB 3 hpos3 [0, 0] (by rw [h3]; simp)
  have b01 := hB 3 hpos3 [0, 1] (by rw [h3]; simp)
  have b10 := hB 4 hpos4 [1, 0] (by rw [h4]; simp)
  have b11 := hB 4 hpos4 [1, 1] (by rw [h4]; simp)
  rw [r00, p3] at b00
  rw [r01, p3] at b01
  rw [r10, p4] at b10
  rw [r11, p4] at b11
  have e00 : μ [0, 0] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 0 * p := by
    rw [b00, div_mul_cancel₀ _ P3.ne']
  have e01 : μ [0, 1] * (F 0 0 0 * p + F 0 0 1 * (1 - p)) = F 0 0 1 * (1 - p) := by
    rw [b01, div_mul_cancel₀ _ P3.ne']
  have e10 : μ [1, 0] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 0 * (1 - p) := by
    rw [b10, div_mul_cancel₀ _ P4.ne']
  have e11 : μ [1, 1] * (F 0 0 0 * (1 - p) + F 0 0 1 * p) = F 0 0 1 * p := by
    rw [b11, div_mul_cancel₀ _ P4.ne']
  have hμn : μ [] = 1 := by
    have := hB 0 (by rw [p0]; norm_num) [] (by rw [h0]; simp)
    rw [this, rn, p0]; norm_num
  -- sequential rationality
  have K3 : ∀ a : Fin 2, μ [0, 0] * (dirac a 0 * 2 + dirac a 1) +
      μ [0, 1] * (dirac a 0 + dirac a 1 * 2) ≤
      μ [0, 0] * (F 1 3 0 * 2 + F 1 3 1) + μ [0, 1] * (F 1 3 0 + F 1 3 1 * 2) := fun a => by
    have := hSR 3 1 rfl _ (bagC_beh_update hF 1 3 a)
    rw [bagC_cond3, bagC_cond3] at this
    simpa [bagC_assemble_eq] using this
  have K4 : ∀ a : Fin 2, μ [1, 0] * (dirac a 0 * 2 + dirac a 1) +
      μ [1, 1] * (dirac a 0 + dirac a 1 * 2) ≤
      μ [1, 0] * (F 1 4 0 * 2 + F 1 4 1) + μ [1, 1] * (F 1 4 0 + F 1 4 1 * 2) := fun a => by
    have := hSR 4 1 rfl _ (bagC_beh_update hF 1 4 a)
    rw [bagC_cond4, bagC_cond4] at this
    simpa [bagC_assemble_eq] using this
  have K0 : ∀ a : Fin 2,
      dirac a 0 * (p * (F 1 3 0 * 4 + F 1 3 1) + (1 - p) * (F 1 4 0 * 4 + F 1 4 1)) +
      dirac a 1 * ((1 - p) * (F 1 3 0 * 5 + F 1 3 1 * 2) + p * (F 1 4 0 * 5 + F 1 4 1 * 2)) ≤
      F 0 0 0 * (p * (F 1 3 0 * 4 + F 1 3 1) + (1 - p) * (F 1 4 0 * 4 + F 1 4 1)) +
      F 0 0 1 * ((1 - p) * (F 1 3 0 * 5 + F 1 3 1 * 2) + p * (F 1 4 0 * 5 + F 1 4 1 * 2)) :=
    fun a => by
    have := hSR 0 0 rfl _ (bagC_beh_update hF 0 0 a)
    rwa [(bagC_condPayoff _ _ _).1, (bagC_condPayoff _ _ _).1, hμn, one_mul, one_mul,
      bagC_payoff0, bagC_payoff0, Function.update_self,
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), Function.update_self] at this
  have k30 := K3 0
  have k31 := K3 1
  have k40 := K4 0
  have k41 := K4 1
  have k00 := K0 0
  have k01 := K0 1
  obtain ⟨d00, d01, d10, d11⟩ := dirac_fin2
  have hqB : F 1 3 1 = 1 - F 1 3 0 := by linarith
  have hqT : F 1 4 1 = 1 - F 1 4 0 := by linarith
  have hx' : F 0 0 1 = 1 - F 0 0 0 := by linarith
  simp only [d00, d01, d10, d11, hqB, hqT] at k30 k31 k40 k41 k00 k01
  simp only [hx'] at k00 k01 e01 e11 e00 e10 P3 P4 ⊢
  have L3 : (1 - F 1 3 0) * (μ [0, 0] - μ [0, 1]) ≤ 0 := by linarith
  have L3' : F 1 3 0 * (μ [0, 1] - μ [0, 0]) ≤ 0 := by linarith
  have L4 : (1 - F 1 4 0) * (μ [1, 0] - μ [1, 1]) ≤ 0 := by linarith
  have L4' : F 1 4 0 * (μ [1, 1] - μ [1, 0]) ≤ 0 := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_, e00, e01, e10, e11⟩
  · have : (1 - F 1 3 0) * (F 0 0 0 * p - (1 - F 0 0 0) * (1 - p)) =
        (1 - F 1 3 0) * (μ [0, 0] - μ [0, 1]) * (F 0 0 0 * p + (1 - F 0 0 0) * (1 - p)) := by
      linear_combination (1 - F 1 3 0) * (e01 - e00)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L3 P3.le
  · have : F 1 3 0 * ((1 - F 0 0 0) * (1 - p) - F 0 0 0 * p) =
        F 1 3 0 * (μ [0, 1] - μ [0, 0]) * (F 0 0 0 * p + (1 - F 0 0 0) * (1 - p)) := by
      linear_combination F 1 3 0 * (e00 - e01)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L3' P3.le
  · have : (1 - F 1 4 0) * (F 0 0 0 * (1 - p) - (1 - F 0 0 0) * p) =
        (1 - F 1 4 0) * (μ [1, 0] - μ [1, 1]) * (F 0 0 0 * (1 - p) + (1 - F 0 0 0) * p) := by
      linear_combination (1 - F 1 4 0) * (e11 - e10)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L4 P4.le
  · have : F 1 4 0 * ((1 - F 0 0 0) * p - F 0 0 0 * (1 - p)) =
        F 1 4 0 * (μ [1, 1] - μ [1, 0]) * (F 0 0 0 * (1 - p) + (1 - F 0 0 0) * p) := by
      linear_combination F 1 4 0 * (e10 - e11)
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg L4' P4.le

/-- A profile of `bagC p`: player 1 plays `B` with probability `x`; player 2 plays `D` with
probability `qB` after signal `B` and `qT` after signal `T`. -/
def bagProfile (x qB qT : ℝ) : Fin 2 → Fin 5 → Fin 2 → ℝ := fun _ k a =>
  if k = 0 then (if a = 0 then x else 1 - x) else if k = 3 then (if a = 0 then qB else 1 - qB)
  else (if a = 0 then qT else 1 - qT)

/-- Beliefs in `bagC p`: probability `m3` on `B` after signal `B`, `m4` on `B` after signal
`T` (and one on the nodes of the singleton information sets). -/
def bagBelief (m3 m4 : ℝ) (z : List (Fin 2)) : ℝ :=
  if z = [0, 0] then m3 else if z = [0, 1] then 1 - m3 else if z = [1, 0] then m4
  else if z = [1, 1] then 1 - m4 else 1

theorem bagProfile_values (x qB qT : ℝ) :
    bagProfile x qB qT 0 0 0 = x ∧ bagProfile x qB qT 0 0 1 = 1 - x ∧
    bagProfile x qB qT 1 3 0 = qB ∧ bagProfile x qB qT 1 3 1 = 1 - qB ∧
    bagProfile x qB qT 1 4 0 = qT ∧ bagProfile x qB qT 1 4 1 = 1 - qT := by
  simp [bagProfile]

theorem bagBelief_values (m3 m4 : ℝ) :
    bagBelief m3 m4 [0, 0] = m3 ∧ bagBelief m3 m4 [0, 1] = 1 - m3 ∧
    bagBelief m3 m4 [1, 0] = m4 ∧ bagBelief m3 m4 [1, 1] = 1 - m4 ∧
    bagBelief m3 m4 [0] = 1 ∧ bagBelief m3 m4 [1] = 1 ∧ bagBelief m3 m4 [] = 1 := by
  simp [bagBelief]

/-- Player 1's sequential rationality in `bagC p` when her moves match the sign of her gain
`1 + 3 (qT − qB)(2p − 1)` from `T` over `B`. -/
theorem bagC_seq0 {x qB qT m3 m4 : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h1 : x * (1 + 3 * (qT - qB) * (2 * p - 1)) ≤ 0)
    (h1' : 0 ≤ (1 - x) * (1 + 3 * (qT - qB) * (2 * p - 1))) :
    SeqRationalAt (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) 0 := by
  intro i hi g hg
  obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
  obtain ⟨hg0, hg1⟩ := bagC_beh hg (k := 0) rfl
  obtain ⟨Q00, Q01, Q30, Q31, Q40, Q41⟩ := bagProfile_values x qB qT
  obtain ⟨-, -, -, -, -, -, Vn⟩ := bagBelief_values m3 m4
  rw [(bagC_condPayoff _ _ _).1, (bagC_condPayoff _ _ _).1, bagC_payoff0, bagC_payoff0,
    Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    show g 0 1 = 1 - g 0 0 by linarith, Vn, Q00, Q01, Q30, Q31, Q40, Q41]
  rcases lt_trichotomy (1 + 3 * (qT - qB) * (2 * p - 1)) 0 with hD | hD | hD
  · have : x = 1 := le_antisymm hx.2 (by nlinarith)
    subst this
    nlinarith [mul_nonneg (by linarith [hg0 1] : (0 : ℝ) ≤ 1 - g 0 0)
      (by linarith : (0 : ℝ) ≤ -(1 + 3 * (qT - qB) * (2 * p - 1)))]
  · nlinarith [congrArg ((x - g 0 0) * ·) hD]
  · have : x = 0 := le_antisymm (by nlinarith) hx.1
    subst this
    nlinarith [mul_nonneg (hg0 0) hD.le]

/-- Player 2's sequential rationality after signal `B` when her move matches her belief. -/
theorem bagC_seq3 {x qB qT m3 m4 : ℝ} (hqB : qB ∈ Set.Icc (0 : ℝ) 1)
    (h3 : (1 - qB) * (2 * m3 - 1) ≤ 0) (h3' : qB * (1 - 2 * m3) ≤ 0) :
    SeqRationalAt (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) 3 := by
  intro i hi g hg
  obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
  obtain ⟨hg0, hg1⟩ := bagC_beh hg (k := 3) rfl
  obtain ⟨-, -, Q30, Q31, -, -⟩ := bagProfile_values x qB qT
  obtain ⟨V00, V01, -⟩ := bagBelief_values m3 m4
  rw [bagC_cond3, bagC_cond3, (bagC_assemble _).2.2.2.1, (bagC_assemble _).2.2.2.1,
    Function.update_self, show g 3 1 = 1 - g 3 0 by linarith, V00, V01, Q30, Q31]
  rcases lt_trichotomy (2 * m3 - 1) 0 with hD | hD | hD
  · have : qB = 0 := le_antisymm (by nlinarith) hqB.1
    subst this
    nlinarith [mul_nonneg (hg0 0) (by linarith : (0 : ℝ) ≤ -(2 * m3 - 1))]
  · nlinarith [congrArg ((qB - g 3 0) * ·) hD]
  · have : qB = 1 := le_antisymm hqB.2 (by nlinarith)
    subst this
    nlinarith [mul_nonneg (by linarith [hg0 1] : (0 : ℝ) ≤ 1 - g 3 0) hD.le]

/-- Player 2's sequential rationality after signal `T` when her move matches her belief. -/
theorem bagC_seq4 {x qB qT m3 m4 : ℝ} (hqT : qT ∈ Set.Icc (0 : ℝ) 1)
    (h4 : (1 - qT) * (2 * m4 - 1) ≤ 0) (h4' : qT * (1 - 2 * m4) ≤ 0) :
    SeqRationalAt (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) 4 := by
  intro i hi g hg
  obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
  obtain ⟨hg0, hg1⟩ := bagC_beh hg (k := 4) rfl
  obtain ⟨-, -, -, -, Q40, Q41⟩ := bagProfile_values x qB qT
  obtain ⟨-, -, V10, V11, -⟩ := bagBelief_values m3 m4
  rw [bagC_cond4, bagC_cond4, (bagC_assemble _).2.2.2.2, (bagC_assemble _).2.2.2.2,
    Function.update_self, show g 4 1 = 1 - g 4 0 by linarith, V10, V11, Q40, Q41]
  rcases lt_trichotomy (2 * m4 - 1) 0 with hD | hD | hD
  · have : qT = 0 := le_antisymm (by nlinarith) hqT.1
    subst this
    nlinarith [mul_nonneg (hg0 0) (by linarith : (0 : ℝ) ≤ -(2 * m4 - 1))]
  · nlinarith [congrArg ((qT - g 4 0) * ·) hD]
  · have : qT = 1 := le_antisymm hqT.2 (by nlinarith)
    subst this
    nlinarith [mul_nonneg (by linarith [hg0 1] : (0 : ℝ) ≤ 1 - g 4 0) hD.le]

/-- Bayes' rule for `(bagProfile x qB qT, bagBelief m3 m4)` in `bagC p`. -/
theorem bagC_bayes {x qB qT m3 m4 : ℝ} (hp' : p ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hb3 : m3 * (x * p + (1 - x) * (1 - p)) = x * p)
    (hb4 : m4 * (x * (1 - p) + (1 - x) * p) = x * (1 - p)) :
    BayesConsistent (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) := by
  intro k hk z hz
  obtain ⟨P3, P4⟩ := bagC_probInfo_pos hp' hx.1 (by linarith [hx.2]) (by ring : x + (1 - x) = 1)
  obtain ⟨h0, hI1, hI2, hI3, hI4⟩ := bagC_infoSet (p := p) (hp := hp)
  obtain ⟨V00, V01, V10, V11, V0, V1, Vn⟩ := bagBelief_values m3 m4
  obtain ⟨p0, p1, p2, p3, p4, rn, r0, r1, r00, r01, r10, r11⟩ :=
    bagC_reach (p := p) (hp := hp) ((bagC p hp).assemble (bagProfile x qB qT))
  have A00 : (bagC p hp).assemble (bagProfile x qB qT) 0 0 = x := by
    simp [bagC_assemble_eq, bagProfile]
  have A01 : (bagC p hp).assemble (bagProfile x qB qT) 0 1 = 1 - x := by
    simp [bagC_assemble_eq, bagProfile]
  have A10 : (bagC p hp).assemble (bagProfile x qB qT) 1 0 = p := by
    simp [bagC_assemble_eq, bagNature]
  have A11 : (bagC p hp).assemble (bagProfile x qB qT) 1 1 = 1 - p := by
    simp [bagC_assemble_eq, bagNature]
  have A20 : (bagC p hp).assemble (bagProfile x qB qT) 2 0 = 1 - p := by
    simp [bagC_assemble_eq, bagNature]
  have A21 : (bagC p hp).assemble (bagProfile x qB qT) 2 1 = p := by
    simp [bagC_assemble_eq, bagNature]
  rcases (by decide : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) k with
    rfl | rfl | rfl | rfl | rfl
  · rw [h0, Finset.mem_singleton] at hz
    subst hz
    rw [rn, p0, Vn]
    norm_num
  · rw [hI1, Finset.mem_singleton] at hz
    subst hz
    rw [p1, A00] at hk
    rw [r0, p1, A00, V0, div_self hk.ne']
  · rw [hI2, Finset.mem_singleton] at hz
    subst hz
    rw [p2, A01] at hk
    rw [r1, p2, A01, V1, div_self hk.ne']
  · rw [hI3] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [r00, p3, A00, A01, A10, A20, V00, eq_div_iff P3.ne']
      linarith
    · rw [r01, p3, A00, A01, A10, A20, V01, eq_div_iff P3.ne']
      linarith
  · rw [hI4] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [r10, p4, A00, A01, A11, A21, V10, eq_div_iff P4.ne']
      linarith
    · rw [r11, p4, A00, A01, A11, A21, V11, eq_div_iff P4.ne']
      linarith

/-- A sufficient condition for `(bagProfile x qB qT, bagBelief m3 m4)` to be a weak PBE of
`bagC p`: probabilities in `[0, 1]`, Bayes' rule, player 2's moves matching her beliefs, and
player 1's moves matching the sign of her gain from `T`. -/
theorem bagC_isWeakPBE_of (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {x qB qT m3 m4 : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hqB : qB ∈ Set.Icc (0 : ℝ) 1) (hqT : qT ∈ Set.Icc (0 : ℝ) 1)
    (hm3 : m3 ∈ Set.Icc (0 : ℝ) 1) (hm4 : m4 ∈ Set.Icc (0 : ℝ) 1)
    (h1 : x * (1 + 3 * (qT - qB) * (2 * p - 1)) ≤ 0)
    (h1' : 0 ≤ (1 - x) * (1 + 3 * (qT - qB) * (2 * p - 1)))
    (h3 : (1 - qB) * (2 * m3 - 1) ≤ 0) (h3' : qB * (1 - 2 * m3) ≤ 0)
    (h4 : (1 - qT) * (2 * m4 - 1) ≤ 0) (h4' : qT * (1 - 2 * m4) ≤ 0)
    (hb3 : m3 * (x * p + (1 - x) * (1 - p)) = x * p)
    (hb4 : m4 * (x * (1 - p) + (1 - x) * p) = x * (1 - p)) :
    IsWeakPBE (bagC p hp) (bagProfile x qB qT) (bagBelief m3 m4) := by
  obtain ⟨h0, hI1, hI2, hI3, hI4⟩ := bagC_infoSet (p := p) (hp := hp)
  have hk5 : ∀ k : Fin 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
  have hF : IsBehaviorProfile (bagC p hp) (bagProfile x qB qT) := by
    intro i k hk
    refine ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩
    · unfold bagProfile
      split_ifs <;> linarith [hx.1, hx.2, hqB.1, hqB.2, hqT.1, hqT.2]
    · simp only [bagC, Fin.sum_univ_two, bagProfile]
      split_ifs <;> simp_all
  have hB : IsBeliefSystem (bagC p hp) (bagBelief m3 m4) := by
    refine ⟨fun z _ => ?_, fun k => ?_⟩
    · unfold bagBelief
      split_ifs <;> constructor <;> linarith [hm3.1, hm3.2, hm4.1, hm4.2]
    · rcases hk5 k with rfl | rfl | rfl | rfl | rfl
      · simp [h0, bagBelief]
      · simp [hI1, bagBelief]
      · simp [hI2, bagBelief]
      · rw [hI3, Finset.sum_insert (by decide), Finset.sum_singleton]
        simp [bagBelief]
      · rw [hI4, Finset.sum_insert (by decide), Finset.sum_singleton]
        simp [bagBelief]
  refine ⟨hF, hB, fun k => ?_, bagC_bayes hp' hx hb3 hb4⟩
  rcases hk5 k with rfl | rfl | rfl | rfl | rfl
  · exact bagC_seq0 hx h1 h1'
  · exact fun i hi => absurd hi (by simp [bagC])
  · exact fun i hi => absurd hi (by simp [bagC])
  · exact bagC_seq3 hqB h3 h3'
  · exact bagC_seq4 hqT h4 h4'

/-- **Exercise 9.C.7(c)** (MWG, p. 305). For every `p ∈ (0, 1)`, player 1 playing `T` and
player 2 playing `U` after both signals, with beliefs putting probability one on `T` at both
of player 2's information sets, is a weak perfect Bayesian equilibrium of the noisy game. -/
theorem exercise_9_C_7c (hp' : p ∈ Set.Ioo (0 : ℝ) 1) :
    IsWeakPBE (bagC p hp) (bagProfile 0 0 0) (bagBelief 0 0) := by
  refine bagC_isWeakPBE_of hp' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num

/-- In a weak PBE of `bagC p` in which player 1 never plays `B`, player 2 plays `U` after both
signals and believes `T` at both information sets. -/
theorem bagC_weakPBE_of_T (hp' : p ∈ Set.Ioo (0 : ℝ) 1) {F : Fin 2 → Fin 5 → Fin 2 → ℝ}
    {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ) (hx : F 0 0 0 = 0) :
    F 0 0 1 = 1 ∧ F 1 3 1 = 1 ∧ F 1 4 1 = 1 ∧ μ [0, 1] = 1 ∧ μ [1, 1] = 1 := by
  obtain ⟨-, -, -, f4, -, f6, -, e01, -, e11⟩ := bagC_weakPBE_facts hp' h
  obtain ⟨hx0, hx1⟩ := bagC_beh (h.1 0) (k := 0) rfl
  obtain ⟨hq0, hq1⟩ := bagC_beh (h.1 1) (k := 3) rfl
  obtain ⟨hr0, hr1⟩ := bagC_beh (h.1 1) (k := 4) rfl
  have hx' : F 0 0 1 = 1 := by linarith
  rw [hx, hx'] at f4 f6 e01 e11
  obtain ⟨h0, h1⟩ := hp'
  have hqB : F 1 3 0 = 0 := le_antisymm (by nlinarith) (hq0 0)
  have hqT : F 1 4 0 = 0 := le_antisymm (by nlinarith) (hr0 0)
  refine ⟨hx', by linarith, by linarith, ?_, ?_⟩
  · have : μ [0, 1] * (1 - p) = 1 * (1 - p) := by linarith
    exact mul_right_cancel₀ (by linarith) this
  · have : μ [1, 1] * p = 1 * p := by linarith
    exact mul_right_cancel₀ (by linarith) this

/-- **Exercise 9.C.7(c), pure strategies** (MWG, p. 305). For every `p ∈ (0, 1)`, in every weak
PBE in which player 1 plays a pure strategy, she plays `T`, player 2 plays `U` after both
signals, and player 2's beliefs put probability one on `T`: the weak PBE of
`exercise_9_C_7c` is the unique pure-strategy weak PBE. -/
theorem exercise_9_C_7c_pure_unique (hp' : p ∈ Set.Ioo (0 : ℝ) 1)
    {F : Fin 2 → Fin 5 → Fin 2 → ℝ} {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ)
    (hpure : F 0 0 0 = 0 ∨ F 0 0 0 = 1) :
    F 0 0 1 = 1 ∧ F 1 3 1 = 1 ∧ F 1 4 1 = 1 ∧ μ [0, 1] = 1 ∧ μ [1, 1] = 1 := by
  rcases hpure with hx | hx
  · exact bagC_weakPBE_of_T hp' h hx
  · exfalso
    obtain ⟨f1, -, f3, -, f5, -⟩ := bagC_weakPBE_facts hp' h
    obtain ⟨hx0, hx1⟩ := bagC_beh (h.1 0) (k := 0) rfl
    obtain ⟨hq0, hq1⟩ := bagC_beh (h.1 1) (k := 3) rfl
    obtain ⟨hr0, hr1⟩ := bagC_beh (h.1 1) (k := 4) rfl
    have hx' : F 0 0 1 = 0 := by linarith
    rw [hx, hx'] at f3 f5
    rw [hx] at f1
    obtain ⟨h0, h1⟩ := hp'
    have hqB : F 1 3 0 = 1 := le_antisymm (by linarith [hq0 1]) (by nlinarith)
    have hqT : F 1 4 0 = 1 := le_antisymm (by linarith [hr0 1]) (by nlinarith)
    rw [hqB, hqT] at f1
    linarith

/-- **Exercise 9.C.7(c), uniqueness** (MWG, p. 305). For `1/3 < p < 2/3` the weak PBE of
`exercise_9_C_7c` is the unique weak PBE (behaviour strategies, any beliefs): `T` is strictly
better than `B` against every strategy of player 2, since `|3 (2p − 1)| < 1`. -/
theorem exercise_9_C_7c_unique (hp1 : 1 / 3 < p) (hp2 : p < 2 / 3)
    {F : Fin 2 → Fin 5 → Fin 2 → ℝ} {μ : List (Fin 2) → ℝ} (h : IsWeakPBE (bagC p hp) F μ) :
    F 0 0 1 = 1 ∧ F 1 3 1 = 1 ∧ F 1 4 1 = 1 ∧ μ [0, 1] = 1 ∧ μ [1, 1] = 1 := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨f1, -⟩ := bagC_weakPBE_facts hp' h
  obtain ⟨hx0, -⟩ := bagC_beh (h.1 0) (k := 0) rfl
  obtain ⟨hq0, hq1⟩ := bagC_beh (h.1 1) (k := 3) rfl
  obtain ⟨hr0, hr1⟩ := bagC_beh (h.1 1) (k := 4) rfl
  have hD : 0 < 1 + 3 * (F 1 4 0 - F 1 3 0) * (2 * p - 1) := by
    rcases le_total 0 (2 * p - 1) with hs | hs
    · nlinarith [mul_nonneg (by linarith [hr0 0, hq0 1] : (0 : ℝ) ≤ F 1 4 0 - F 1 3 0 + 1) hs]
    · nlinarith [mul_nonneg (by linarith [hr0 1, hq0 0] : (0 : ℝ) ≤ 1 - (F 1 4 0 - F 1 3 0))
        (by linarith : (0 : ℝ) ≤ -(2 * p - 1))]
  exact bagC_weakPBE_of_T hp' h (le_antisymm (nonpos_of_mul_nonpos_left f1 hD) (hx0 0))

/-- **Correction to Exercise 9.C.7(c)** (MWG, p. 305). For `2/3 ≤ p < 1` there is a further weak
PBE: player 1 plays `T` with probability `p`, player 2 plays `D` with probability
`1 / (3 (2p − 1))` after signal `B` (where she believes `B` with probability `1/2`) and `U` after
signal `T`; player 1 is indifferent. -/
theorem exercise_9_C_7c_mixed_high (hp2 : 2 / 3 ≤ p) (hp1 : p < 1) :
    IsWeakPBE (bagC p hp) (bagProfile (1 - p) (1 / (3 * (2 * p - 1))) 0)
      (bagBelief (1 / 2) ((1 - p) ^ 2 / ((1 - p) ^ 2 + p ^ 2))) ∧
    bagProfile (1 - p) (1 / (3 * (2 * p - 1))) 0 0 0 1 ≠ 1 := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, hp1⟩
  have hc : 1 ≤ 3 * (2 * p - 1) := by linarith
  have hD : 0 < (1 - p) ^ 2 + p ^ 2 := by positivity
  have hm4 : (1 - p) ^ 2 / ((1 - p) ^ 2 + p ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  refine ⟨bagC_isWeakPBE_of hp' ⟨by linarith, by linarith⟩
    ⟨by positivity, by rw [div_le_one (by linarith)]; exact hc⟩ ⟨le_rfl, zero_le_one⟩
    ⟨by norm_num, by norm_num⟩ ⟨by positivity, by linarith⟩ ?_ ?_ (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by ring) ?_, ?_⟩
  · have : 1 + 3 * (0 - 1 / (3 * (2 * p - 1))) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 2 * p - 1).ne']; ring
    rw [this, mul_zero]
  · have : 1 + 3 * (0 - 1 / (3 * (2 * p - 1))) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 2 * p - 1).ne']; ring
    rw [this, mul_zero]
  · rw [div_mul_eq_mul_div, div_eq_iff hD.ne']
    ring
  · simp only [bagProfile_values]
    linarith

/-- **Correction to Exercise 9.C.7(c)** (MWG, p. 305). For `0 < p ≤ 1/3` there is a further weak
PBE: player 1 plays `B` with probability `p`, player 2 plays `U` after signal `B` and `D` with
probability `1 / (3 (1 − 2p))` after signal `T` (where she believes `B` with probability `1/2`);
player 1 is indifferent. -/
theorem exercise_9_C_7c_mixed_low (hp0 : 0 < p) (hp1 : p ≤ 1 / 3) :
    IsWeakPBE (bagC p hp) (bagProfile p 0 (1 / (3 * (1 - 2 * p))))
      (bagBelief (p ^ 2 / (p ^ 2 + (1 - p) ^ 2)) (1 / 2)) ∧
    bagProfile p 0 (1 / (3 * (1 - 2 * p))) 0 0 1 ≠ 1 := by
  have hp' : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, by linarith⟩
  have hc : 1 ≤ 3 * (1 - 2 * p) := by linarith
  have hD : 0 < p ^ 2 + (1 - p) ^ 2 := by positivity
  have hm3 : p ^ 2 / (p ^ 2 + (1 - p) ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]; nlinarith
  refine ⟨bagC_isWeakPBE_of hp' ⟨hp0.le, by linarith⟩ ⟨le_rfl, zero_le_one⟩
    ⟨by positivity, by rw [div_le_one (by linarith)]; exact hc⟩
    ⟨by positivity, by linarith⟩ ⟨by norm_num, by norm_num⟩ ?_ ?_ (by linarith) (by norm_num)
    (by norm_num) (by norm_num) ?_ (by ring), ?_⟩
  · have : 1 + 3 * (1 / (3 * (1 - 2 * p)) - 0) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 1 - 2 * p).ne']; ring
    rw [this, mul_zero]
  · have : 1 + 3 * (1 / (3 * (1 - 2 * p)) - 0) * (2 * p - 1) = 0 := by
      field_simp [(by linarith : (0 : ℝ) < 1 - 2 * p).ne']; ring
    rw [this, mul_zero]
  · rw [div_mul_eq_mul_div, div_eq_iff hD.ne']
    ring
  · simp only [bagProfile_values]
    linarith

/-- **Exercise 9.C.7(c), corrected** (MWG, p. 305). The weak PBE of the noisy game is unique
(player 1 plays `T` for sure in every weak PBE) if and only if `1/3 < p < 2/3`. -/
theorem exercise_9_C_7c_unique_iff (hp' : p ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ F μ, IsWeakPBE (bagC p hp) F μ → F 0 0 1 = 1) ↔ 1 / 3 < p ∧ p < 2 / 3 := by
  constructor
  · intro hU
    by_contra hn
    rcases not_and_or.1 hn with h | h
    · have h' := not_lt.1 h
      exact (exercise_9_C_7c_mixed_low (hp := hp) hp'.1 h').2 (hU _ _
        (exercise_9_C_7c_mixed_low (hp := hp) hp'.1 h').1)
    · have h' := not_lt.1 h
      exact (exercise_9_C_7c_mixed_high (hp := hp) h' hp'.2).2 (hU _ _
        (exercise_9_C_7c_mixed_high (hp := hp) h' hp'.2).1)
  · rintro ⟨h1, h2⟩ F μ h
    exact (exercise_9_C_7c_unique h1 h2 h).1

end MWG.DynamicGames
