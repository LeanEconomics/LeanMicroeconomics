/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry
import MWGDynamicGames.Beliefs
import Mathlib.Tactic.LinearCombination

/-!
# Weak PBE with unreasonable beliefs, and its unique sequential equilibrium

MWG, Example 9.C.4 and Figure 9.C.4 (pp. 289 and 291).

Nature (information set `0`) chooses left (`0`) or right (`1`) with probability `1/2`; player 1
(`0`), not observing nature, chooses `x` (`0`, ending the game with payoffs `(2, 10)`) or `y`
(`1`) at information set `1 = {[0], [1]}`; after `y`, player 2 (`1`), observing neither, chooses
`ℓ` (`0`) or `r` (`1`) at information set `2 = {[1, 0], [1, 1]}`.

* `example_9_C_4_weakPBE`: `(x, ℓ)` with beliefs `(1/2, 1/2)` for player 1 and `(0.9, 0.1)` for
  player 2 is a weak PBE (player 2's information set is off the equilibrium path).
* `example_9_C_4_consistent_beliefs`: every consistent assessment gives player 2 beliefs
  `(1/2, 1/2)` (player 1's deviation to `y` cannot depend on nature's move), so the weak PBE's
  beliefs are not consistent (`example_9_C_4_not_consistent`).
* `example_9_C_4_sequential`: `(y, r)` with beliefs `(1/2, 1/2)` at both information sets is the
  unique sequential equilibrium.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

/-- Payoffs `(u₁, u₂)` of Figure 9.C.4. -/
def ncPay (i : Fin 2) (z : List (Fin 2)) : ℝ :=
  if z = [0, 0] ∨ z = [0, 1] then ![2, 10] i
  else if z = [0, 1, 0] ∨ z = [0, 1, 1] then ![0, 5] i
  else if z = [1, 1, 0] then ![5, 2] i else if z = [1, 1, 1] then ![5, 10] i else 0

/-- **Example 9.C.4, Figure 9.C.4** (MWG, p. 289). -/
noncomputable def ncGame : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 1, 0], [1, 1, 0], [0, 1, 1],
    [1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else if x.length = 1 then 1 else 2
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![none, some 0, some 1]
  natureProb k _ := if k = 0 then 1 / 2 else 0
  nature_nonneg := fun k _ _ => by split_ifs <;> norm_num
  nature_zero := fun _ _ a ha => absurd (Finset.mem_univ a) ha
  nature_sum := fun k hk => by
    have : k = 0 := by fin_cases k <;> simp_all
    subst this
    norm_num [Fin.sum_univ_two]
  payoff := ncPay

theorem ncGame_assemble (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    ncGame.assemble F 0 = (fun _ => 1 / 2) ∧ ncGame.assemble F 1 = F 0 1 ∧
      ncGame.assemble F 2 = F 1 2 :=
  ⟨by rw [ncGame.assemble_of_none _ rfl]; rfl, ncGame.assemble_of_some _ rfl,
    ncGame.assemble_of_some _ rfl⟩

/-- Continuation payoffs in the game of Figure 9.C.4. -/
theorem ncGame_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont ncGame f [1, 0] i = f 2 0 * ![0, 5] i + f 2 1 * ![5, 2] i ∧
    cont ncGame f [1, 1] i = f 2 0 * ![0, 5] i + f 2 1 * ![5, 10] i ∧
    cont ncGame f [0] i = f 1 0 * ![2, 10] i + f 1 1 * (f 2 0 * ![0, 5] i + f 2 1 * ![5, 2] i) ∧
    cont ncGame f [1] i =
      f 1 0 * ![2, 10] i + f 1 1 * (f 2 0 * ![0, 5] i + f 2 1 * ![5, 10] i) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [cont_unfold, ncGame, ncPay, Fin.sum_univ_two]

theorem ncGame_infoSet : ncGame.infoSet 0 = {[]} ∧ ncGame.infoSet 1 = {[0], [1]} ∧
    ncGame.infoSet 2 = {[1, 0], [1, 1]} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem ncGame_condPayoff (f : Fin 3 → Fin 2 → ℝ) (μ : List (Fin 2) → ℝ) (i : Fin 2) :
    condPayoff ncGame f μ 1 i = μ [0] * cont ncGame f [0] i + μ [1] * cont ncGame f [1] i ∧
    condPayoff ncGame f μ 2 i = μ [1, 0] * cont ncGame f [1, 0] i +
      μ [1, 1] * cont ncGame f [1, 1] i := by
  obtain ⟨-, h1, h2⟩ := ncGame_infoSet
  unfold condPayoff
  rw [h1, h2]
  constructor <;> rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem ncGame_reach (f : Fin 3 → Fin 2 → ℝ) :
    ncGame.reach f [0] = f 0 0 ∧ ncGame.reach f [1] = f 0 1 ∧
    ncGame.reach f [1, 0] = f 0 0 * f 1 1 ∧ ncGame.reach f [1, 1] = f 0 1 * f 1 1 ∧
    probInfo ncGame f 0 = 1 ∧ probInfo ncGame f 1 = f 0 0 + f 0 1 ∧
    probInfo ncGame f 2 = f 0 0 * f 1 1 + f 0 1 * f 1 1 := by
  obtain ⟨h0, h1, h2⟩ := ncGame_infoSet
  refine ⟨by simp [ncGame], by simp [ncGame], by simp [ncGame], by simp [ncGame], ?_, ?_, ?_⟩ <;>
    unfold probInfo
  · rw [h0]; simp
  · rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [ncGame]
  · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; simp [ncGame]

/-- The beliefs of the weak PBE of Example 9.C.4: `(1/2, 1/2)` for player 1 and `(0.9, 0.1)` for
player 2. -/
noncomputable def ncBelief (x : List (Fin 2)) : ℝ :=
  if x = [0] ∨ x = [1] then 1 / 2 else if x = [1, 0] then 9 / 10
  else if x = [1, 1] then 1 / 10 else 1

/-- The beliefs `(1/2, 1/2)` at both information sets. -/
noncomputable def ncHalf (x : List (Fin 2)) : ℝ := if x = [] then 1 else 1 / 2

theorem ncGame_beh {g : Fin 3 → Fin 2 → ℝ} {i : Fin 2} {k : Fin 3}
    (hg : ncGame.IsBehaviorStrategy i g) (hk : ncGame.player k = some i) :
    (∀ a, 0 ≤ g k a) ∧ g k 0 + g k 1 = 1 :=
  ⟨(hg k hk).1, by simpa [ncGame, Fin.sum_univ_two] using (hg k hk).2.2⟩

theorem ncGame_k3 (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp

/-- The beliefs `ncBelief` and `ncHalf` are systems of beliefs. -/
theorem ncGame_beliefSystems : IsBeliefSystem ncGame ncBelief ∧ IsBeliefSystem ncGame ncHalf := by
  obtain ⟨h0, h1, h2⟩ := ncGame_infoSet
  refine ⟨⟨fun x _ => ?_, fun k => ?_⟩, ⟨fun x _ => ?_, fun k => ?_⟩⟩
  · unfold ncBelief; split_ifs <;> norm_num
  · rcases ncGame_k3 k with rfl | rfl | rfl
    · simp [h0, ncBelief]
    · rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncBelief]
    · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncBelief]
  · unfold ncHalf; split_ifs <;> norm_num
  · rcases ncGame_k3 k with rfl | rfl | rfl
    · simp [h0, ncHalf]
    · rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncHalf]
    · rw [h2, Finset.sum_insert (by decide), Finset.sum_singleton]; norm_num [ncHalf]

/-- **Example 9.C.4** (MWG, p. 289). Player 1 playing `x`, player 2 playing `ℓ`, with beliefs
`(1/2, 1/2)` for player 1 and `(0.9, 0.1)` for player 2, is a weak perfect Bayesian
equilibrium. -/
theorem example_9_C_4_weakPBE : IsWeakPBE ncGame (pureMoves ![0, 0, 0]) ncBelief := by
  obtain ⟨h0, h1, h2⟩ := ncGame_infoSet
  have hB : IsBehaviorProfile ncGame (pureMoves (I := Fin 2) ![0, 0, 0]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  refine ⟨hB, ncGame_beliefSystems.1, fun k i hi g hg => ?_, fun k hk x hx => ?_⟩
  · have hA := ncGame_assemble (Function.update (pureMoves ![0, 0, 0]) i g)
    have hA' := ncGame_assemble (pureMoves ![0, 0, 0])
    rcases ncGame_k3 k with rfl | rfl | rfl
    · exact absurd hi (by simp [ncGame])
    · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
      obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 1) rfl
      rw [(ncGame_condPayoff _ _ _).1, (ncGame_condPayoff _ _ _).1, (ncGame_cont _ _).2.2.1,
        (ncGame_cont _ _).2.2.1, (ncGame_cont _ _).2.2.2, (ncGame_cont _ _).2.2.2, hA.2.1,
        hA.2.2, hA'.2.1, hA'.2.2]
      simp [pureMoves, dirac, ncBelief]
      nlinarith [hg0 0, hg0 1]
    · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
      obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 2) rfl
      rw [(ncGame_condPayoff _ _ _).2, (ncGame_condPayoff _ _ _).2, (ncGame_cont _ _).1,
        (ncGame_cont _ _).1, (ncGame_cont _ _).2.1, (ncGame_cont _ _).2.1, hA.2.2, hA'.2.2]
      simp [pureMoves, dirac, ncBelief]
      nlinarith [hg0 0, hg0 1]
  · have hA' := ncGame_assemble (pureMoves ![0, 0, 0])
    obtain ⟨r0, r1, r10, r11, p0, p1, p2⟩ := ncGame_reach (ncGame.assemble (pureMoves ![0, 0, 0]))
    rcases ncGame_k3 k with rfl | rfl | rfl
    · rw [h0, Finset.mem_singleton] at hx
      subst hx
      simp [p0, ncBelief]
    · rw [h1] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [r0, p1, hA'.1]; norm_num [ncBelief]
      · rw [r1, p1, hA'.1]; norm_num [ncBelief]
    · rw [p2, hA'.2.1] at hk
      simp [pureMoves, dirac] at hk

/-- Beliefs derived from a totally mixed profile by Bayes' rule are `1/2` at the nodes of both
players' information sets. -/
theorem ncGame_bayes_half {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hTM : IsTotallyMixedB ncGame F)
    {x : List (Fin 2)} (hx : x = [1, 0] ∨ x = [1, 1] ∨ x = [0] ∨ x = [1]) :
    bayesBelief ncGame (ncGame.assemble F) x = 1 / 2 := by
  have hA := ncGame_assemble F
  obtain ⟨r0, r1, r10, r11, -, p1, p2⟩ := ncGame_reach (ncGame.assemble F)
  have hpos : 0 < F 0 1 1 := hTM.2 0 1 rfl 1 (Finset.mem_univ _)
  unfold bayesBelief
  rcases hx with rfl | rfl | rfl | rfl
  · rw [show ncGame.info [1, 0] = 2 from rfl, r10, p2, hA.1, hA.2.1]
    field_simp
    ring
  · rw [show ncGame.info [1, 1] = 2 from rfl, r11, p2, hA.1, hA.2.1]
    field_simp
    ring
  · rw [show ncGame.info [0] = 1 from rfl, r0, p1, hA.1]
    norm_num
  · rw [show ncGame.info [1] = 1 from rfl, r1, p1, hA.1]
    norm_num

/-- **Example 9.C.4 continued** (MWG, p. 291). All beliefs derived from totally mixed strategies
give equal probability to the two nodes of player 2's information set; so every consistent
assessment has `μ([y, left]) = μ([y, right]) = 1/2`, and also `1/2` at player 1's nodes. -/
theorem example_9_C_4_consistent_beliefs {F : Fin 2 → Fin 3 → Fin 2 → ℝ} {μ : List (Fin 2) → ℝ}
    (h : IsConsistent ncGame F μ) :
    μ [1, 0] = 1 / 2 ∧ μ [1, 1] = 1 / 2 ∧ μ [0] = 1 / 2 ∧ μ [1] = 1 / 2 := by
  obtain ⟨Fs, hTM, -, hbel⟩ := h
  have hconst : ∀ x, x = [1, 0] ∨ x = [1, 1] ∨ x = [0] ∨ x = [1] →
      ∀ n, bayesBelief ncGame (ncGame.assemble (Fs n)) x = 1 / 2 :=
    fun x hx n => ncGame_bayes_half (hTM n) hx
  have hlim : ∀ x, ncGame.IsDecision x → (x = [1, 0] ∨ x = [1, 1] ∨ x = [0] ∨ x = [1]) →
      μ x = 1 / 2 := fun x hd hx =>
    tendsto_nhds_unique (hbel x hd) (by simp only [hconst x hx]; exact tendsto_const_nhds)
  have hd : ∀ x ∈ ({[1, 0], [1, 1], [0], [1]} : Finset (List (Fin 2))), ncGame.IsDecision x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨by decide, 0, by decide⟩
  exact ⟨hlim _ (hd _ (by simp)) (by simp), hlim _ (hd _ (by simp)) (by simp),
    hlim _ (hd _ (by simp)) (by simp), hlim _ (hd _ (by simp)) (by simp)⟩

/-- **Example 9.C.4** (MWG, p. 289). The beliefs of the weak PBE `example_9_C_4_weakPBE` are not
consistent: no sequence of totally mixed strategies generates them. -/
theorem example_9_C_4_not_consistent (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    ¬ IsConsistent ncGame F ncBelief := fun h => by
  have := (example_9_C_4_consistent_beliefs h).1
  norm_num [ncBelief] at this

/-- Playing `a` at information set `k` and following `F i` elsewhere is a behaviour strategy. -/
theorem ncGame_beh_update {F : Fin 2 → Fin 3 → Fin 2 → ℝ} (hF : IsBehaviorProfile ncGame F)
    (i : Fin 2) (k : Fin 3) (a : Fin 2) :
    ncGame.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num,
      fun b hb => absurd (Finset.mem_univ b) hb, ?_⟩
    simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [ncGame]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- **Example 9.C.4 continued** (MWG, p. 291). `(y, r)` with beliefs `(1/2, 1/2)` at both
information sets is a sequential equilibrium, and it is the unique one: in every sequential
equilibrium player 1 plays `y` and player 2 plays `r` for sure, with beliefs `1/2`. -/
theorem example_9_C_4_sequential :
    IsSequentialEq ncGame (pureMoves ![0, 1, 1]) ncHalf ∧
    ∀ F μ, IsSequentialEq ncGame F μ → F 0 1 1 = 1 ∧ F 1 2 1 = 1 ∧
      μ [1, 0] = 1 / 2 ∧ μ [1, 1] = 1 / 2 := by
  have hB : IsBehaviorProfile ncGame (pureMoves (I := Fin 2) ![0, 1, 1]) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  constructor
  · refine ⟨hB, ncGame_beliefSystems.2, fun k i hi g hg => ?_, ?_⟩
    · have hA := ncGame_assemble (Function.update (pureMoves ![0, 1, 1]) i g)
      have hA' := ncGame_assemble (pureMoves ![0, 1, 1])
      rcases ncGame_k3 k with rfl | rfl | rfl
      · exact absurd hi (by simp [ncGame])
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 1) rfl
        rw [(ncGame_condPayoff _ _ _).1, (ncGame_condPayoff _ _ _).1, (ncGame_cont _ _).2.2.1,
          (ncGame_cont _ _).2.2.1, (ncGame_cont _ _).2.2.2, (ncGame_cont _ _).2.2.2, hA.2.1,
          hA.2.2, hA'.2.1, hA'.2.2]
        simp [pureMoves, dirac, ncHalf]
        nlinarith [hg0 0, hg0 1]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        obtain ⟨hg0, hg1⟩ := ncGame_beh hg (k := 2) rfl
        rw [(ncGame_condPayoff _ _ _).2, (ncGame_condPayoff _ _ _).2, (ncGame_cont _ _).1,
          (ncGame_cont _ _).1, (ncGame_cont _ _).2.1, (ncGame_cont _ _).2.1, hA.2.2, hA'.2.2]
        simp [pureMoves, dirac, ncHalf]
        nlinarith [hg0 0, hg0 1]
    · -- the trembles: each player puts `1 / (2 (n + 1))` on every action
      set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
      have hε0 : ∀ n, 0 < ε n := fun n => by positivity
      have hε1 : ∀ n, ε n ≤ 1 := fun n => by
        rw [hε, div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      set Fs : ℕ → Fin 2 → Fin 3 → Fin 2 → ℝ :=
        fun n i k a => (1 - ε n) * pureMoves ![0, 1, 1] i k a + ε n / 2 with hFs
      have hdir : ∀ (i : Fin 2) (k : Fin 3) (a : Fin 2),
          0 ≤ pureMoves (I := Fin 2) (![0, 1, 1] : Fin 3 → Fin 2) i k a := by
        intro i k a; unfold pureMoves dirac; split_ifs <;> norm_num
      have hTM : ∀ n, IsTotallyMixedB ncGame (Fs n) := by
        intro n
        refine ⟨fun i k _ => ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩,
          fun i k _ a _ => ?_⟩
        · have := hε0 n
          simp only [hFs]
          nlinarith [hdir i k a, hε1 n]
        · rw [show ncGame.avail k = Finset.univ from rfl]
          simp only [hFs, Fin.sum_univ_two, pureMoves, dirac]
          have h2 : ∀ c : Fin 2, (if (0 : Fin 2) = c then (1 : ℝ) else 0) +
              (if (1 : Fin 2) = c then 1 else 0) = 1 := by
            intro c; fin_cases c <;> norm_num
          linear_combination (1 - ε n) * h2 (![0, 1, 1] k)
        · have := hε0 n
          simp only [hFs]
          nlinarith [hdir i k a, hε1 n]
      have hlimε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlim : Tendsto Fs atTop (𝓝 (pureMoves ![0, 1, 1])) := by
        refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun a => ?_
        have h1 : Tendsto (fun n => (1 - ε n) * pureMoves (I := Fin 2)
            (![0, 1, 1] : Fin 3 → Fin 2) i k a + ε n / 2) atTop
            (𝓝 ((1 - 0) * pureMoves (I := Fin 2) (![0, 1, 1] : Fin 3 → Fin 2) i k a + 0 / 2)) :=
          ((tendsto_const_nhds.sub hlimε).mul tendsto_const_nhds).add (hlimε.div_const 2)
        simpa [hFs] using h1
      refine ⟨Fs, hTM, hlim, fun x hx => ?_⟩
      have hmem := (mem_decisionNodes _).2 hx
      rw [show ncGame.decisionNodes = {[], [0], [1], [1, 0], [1, 1]} by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | hx'
      · have : ∀ n, bayesBelief ncGame (ncGame.assemble (Fs n)) [] = 1 := by
          intro n
          unfold bayesBelief
          rw [show ncGame.info [] = 0 from rfl, (ncGame_reach _).2.2.2.2.1]
          simp
        simp only [this, ncHalf, ↓reduceIte]
        exact tendsto_const_nhds
      · have hne : x ≠ [] := by rcases hx' with rfl | rfl | rfl | rfl <;> simp
        have : ∀ n, bayesBelief ncGame (ncGame.assemble (Fs n)) x = 1 / 2 := fun n =>
          ncGame_bayes_half (hTM n) (by tauto)
        simp only [this, ncHalf, hne, ↓reduceIte]
        exact tendsto_const_nhds
  · intro F μ ⟨hF, hμ, hSR, hC⟩
    obtain ⟨b10, b11, b0, b1⟩ := example_9_C_4_consistent_beliefs hC
    obtain ⟨hp0, hp1⟩ := ncGame_beh (hF 0) (k := 1) rfl
    obtain ⟨hq0, hq1⟩ := ncGame_beh (hF 1) (k := 2) rfl
    -- player 2 plays r
    have hr := hSR 2 1 rfl _ (ncGame_beh_update hF 1 2 1)
    have hA := ncGame_assemble (Function.update F 1 (Function.update (F 1) 2 (dirac 1)))
    have hA' := ncGame_assemble F
    rw [(ncGame_condPayoff _ _ _).2, (ncGame_condPayoff _ _ _).2, (ncGame_cont _ _).1,
      (ncGame_cont _ _).1, (ncGame_cont _ _).2.1, (ncGame_cont _ _).2.1, hA.2.2, hA'.2.2,
      b10, b11] at hr
    simp [dirac] at hr
    have hR : F 1 2 1 = 1 := by nlinarith [hq0 0, hq0 1]
    have hR' : F 1 2 0 = 0 := by linarith
    -- player 1 plays y
    have hy := hSR 1 0 rfl _ (ncGame_beh_update hF 0 1 1)
    have hA1 := ncGame_assemble (Function.update F 0 (Function.update (F 0) 1 (dirac 1)))
    rw [(ncGame_condPayoff _ _ _).1, (ncGame_condPayoff _ _ _).1, (ncGame_cont _ _).2.2.1,
      (ncGame_cont _ _).2.2.1, (ncGame_cont _ _).2.2.2, (ncGame_cont _ _).2.2.2, hA1.2.1,
      hA1.2.2, hA'.2.1, hA'.2.2, b0, b1] at hy
    simp [dirac, hR, hR'] at hy
    have hY : F 0 1 1 = 1 := by nlinarith [hp0 0, hp0 1]
    exact ⟨hY, hR, b10, b11⟩

end MWG.DynamicGames
