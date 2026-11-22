/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry
import MWGDynamicGames.Beliefs

/-!
# The joint venture entry game

MWG, Example 9.C.2 and Figure 9.C.2 (pp. 286-287).

Players: `0` = firm E1, `1` = firm E2, `2` = the incumbent I. Information sets: `0` = E1 at the
start (Out `0`, Enter on own `1`, Propose joint venture `2`); `1` = E2 after a proposal
(Accept `0`, Decline `1`); `2` = E1 after E2 declines (In `0`, Out `1`); `3` = I's
information set `{[1], [0, 2], [0, 1, 2]}` (left: E1 alone; middle: joint venture; right: E1
alone after E2 declined), where I chooses Fight `0` or Accommodate `1`.

* `example_9_C_2_weakPBE`: ((propose joint venture, in if E2 declines), accept, accommodate)
  with belief `1` on the middle node is a weak PBE, and it is the unique weak PBE: in every
  weak PBE `(σ, μ)` (behaviour strategies) these moves are played for sure and `μ` puts
  probability one on the middle node.
* `example_9_C_2_spne`: ((out, out if E2 declines), decline, fight) is an SPNE (the only
  subgame is the whole game, and it is a Nash equilibrium).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs `(u_E1, u_E2, u_I)` of Figure 9.C.2. -/
def jvPay (i : Fin 3) (z : List (Fin 3)) : ℝ :=
  if z = [0] then ![0, 0, 3] i
  else if z = [0, 1] then ![-1, 0, 2] i else if z = [1, 1] then ![2, 0, 1] i
  else if z = [0, 0, 2] then ![1, 1, -2] i else if z = [1, 0, 2] then ![4, 4, 0] i
  else if z = [0, 0, 1, 2] then ![-1, 0, 2] i else if z = [1, 0, 1, 2] then ![2, 0, 1] i
  else if z = [1, 1, 2] then ![0, 0, 3] i else 0

/-- The information sets of Figure 9.C.2. -/
def jvInfo (x : List (Fin 3)) : Fin 4 :=
  if x = [] then 0 else if x = [2] then 1 else if x = [1, 2] then 2 else 3

/-- **Example 9.C.2, Figure 9.C.2** (MWG, pp. 286-287). The joint venture entry game. -/
def jvGame : ExtensiveForm (Fin 3) (Fin 3) (Fin 4) where
  nodes := {[], [0], [1], [2], [0, 1], [1, 1], [0, 2], [1, 2], [0, 0, 2], [1, 0, 2], [0, 1, 2],
    [1, 1, 2], [0, 0, 1, 2], [1, 0, 1, 2]}
  nil_mem := by decide
  tail_mem := by decide
  info := jvInfo
  avail k := if k = 0 then Finset.univ else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 1, some 0, some 2]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff := jvPay

/-- Continuation payoffs in the joint venture game. -/
theorem jvGame_cont (f : Fin 4 → Fin 3 → ℝ) (i : Fin 3) :
    cont jvGame f [1] i = f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i ∧
    cont jvGame f [0, 2] i = f 3 0 * ![1, 1, -2] i + f 3 1 * ![4, 4, 0] i ∧
    cont jvGame f [1, 2] i = f 2 0 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) +
      f 2 1 * ![0, 0, 3] i ∧
    cont jvGame f [2] i = f 1 0 * (f 3 0 * ![1, 1, -2] i + f 3 1 * ![4, 4, 0] i) +
      f 1 1 * (f 2 0 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) + f 2 1 * ![0, 0, 3] i) ∧
    cont jvGame f [] i = f 0 0 * ![0, 0, 3] i +
      f 0 1 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) +
      f 0 2 * (f 1 0 * (f 3 0 * ![1, 1, -2] i + f 3 1 * ![4, 4, 0] i) +
        f 1 1 * (f 2 0 * (f 3 0 * ![-1, 0, 2] i + f 3 1 * ![2, 0, 1] i) +
          f 2 1 * ![0, 0, 3] i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [cont_unfold, jvGame, jvPay, jvInfo, Fin.sum_univ_three]

theorem jvGame_infoSet : jvGame.infoSet 0 = {[]} ∧ jvGame.infoSet 1 = {[2]} ∧
    jvGame.infoSet 2 = {[1, 2]} ∧ jvGame.infoSet 3 = {[1], [0, 2], [0, 1, 2]} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem jvGame_assemble (F : Fin 3 → Fin 4 → Fin 3 → ℝ) :
    jvGame.assemble F 0 = F 0 0 ∧ jvGame.assemble F 1 = F 1 1 ∧ jvGame.assemble F 2 = F 0 2 ∧
      jvGame.assemble F 3 = F 2 3 :=
  ⟨jvGame.assemble_of_some _ rfl, jvGame.assemble_of_some _ rfl,
    jvGame.assemble_of_some _ rfl, jvGame.assemble_of_some _ rfl⟩

/-- The moves of a profile: player `![0, 1, 0, 2] k` moves at information set `k`. -/
theorem jvGame_assemble_eq (F : Fin 3 → Fin 4 → Fin 3 → ℝ) :
    jvGame.assemble F = fun k => F (![0, 1, 0, 2] k) k := by
  funext k
  have hk4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases hk4 k with rfl | rfl | rfl | rfl <;> exact jvGame.assemble_of_some _ rfl

/-- Expected payoffs at the information sets given beliefs `μ`. -/
theorem jvGame_condPayoff (f : Fin 4 → Fin 3 → ℝ) (μ : List (Fin 3) → ℝ) (i : Fin 3) :
    condPayoff jvGame f μ 0 i = μ [] * cont jvGame f [] i ∧
    condPayoff jvGame f μ 1 i = μ [2] * cont jvGame f [2] i ∧
    condPayoff jvGame f μ 2 i = μ [1, 2] * cont jvGame f [1, 2] i ∧
    condPayoff jvGame f μ 3 i = μ [1] * cont jvGame f [1] i +
      μ [0, 2] * cont jvGame f [0, 2] i + μ [0, 1, 2] * cont jvGame f [0, 1, 2] i := by
  obtain ⟨h0, h1, h2, h3⟩ := jvGame_infoSet
  unfold condPayoff
  rw [h0, h1, h2, h3]
  refine ⟨by simp, by simp, by simp, ?_⟩
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The behaviour strategy of player `i` that plays `a` at information set `k` and follows
`F i` elsewhere. -/
theorem jvGame_beh_update {F : Fin 3 → Fin 4 → Fin 3 → ℝ} (hF : IsBehaviorProfile jvGame F)
    {i : Fin 3} {k : Fin 4} {a : Fin 3} (ha : a ∈ jvGame.avail k) :
    jvGame.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [Function.update_self]
    refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num, fun b hb => ?_, ?_⟩
    · have : b ≠ a := fun h => hb (h ▸ ha)
      simp [dirac, this]
    · simp only [dirac]
      rw [Finset.sum_ite_eq']
      simp [ha]
  · simp only [Function.update_of_ne hkk]
    exact hF i k' hk'

/-- Facts about a behaviour profile of the joint venture game. -/
theorem jvGame_behavior {F : Fin 3 → Fin 4 → Fin 3 → ℝ} (hF : IsBehaviorProfile jvGame F) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧
      F 1 1 0 + F 1 1 1 = 1 ∧ (∀ a, 0 ≤ F 0 2 a) ∧ F 0 2 0 + F 0 2 1 = 1 ∧
      (∀ a, 0 ≤ F 2 3 a) ∧ F 2 3 0 + F 2 3 1 = 1 := by
  have h0 := hF 0 0 rfl
  have h1 := hF 1 1 rfl
  have h2 := hF 0 2 rfl
  have h3 := hF 2 3 rfl
  exact ⟨h0.1, by simpa [jvGame, Fin.sum_univ_three] using h0.2.2, h1.1,
    by simpa [jvGame] using h1.2.2, h2.1, by simpa [jvGame] using h2.2.2, h3.1,
    by simpa [jvGame] using h3.2.2⟩

/-- Reach probabilities in the joint venture game. -/
theorem jvGame_reach (f : Fin 4 → Fin 3 → ℝ) :
    jvGame.reach f [1] = f 0 1 ∧ jvGame.reach f [2] = f 0 2 ∧
    jvGame.reach f [0, 2] = f 0 2 * f 1 0 ∧ jvGame.reach f [1, 2] = f 0 2 * f 1 1 ∧
    jvGame.reach f [0, 1, 2] = f 0 2 * f 1 1 * f 2 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [jvGame, jvInfo]

/-- The probabilities of reaching the information sets. -/
theorem jvGame_probInfo (f : Fin 4 → Fin 3 → ℝ) :
    probInfo jvGame f 0 = 1 ∧ probInfo jvGame f 1 = f 0 2 ∧
    probInfo jvGame f 2 = f 0 2 * f 1 1 ∧
    probInfo jvGame f 3 = f 0 1 + f 0 2 * f 1 0 + f 0 2 * f 1 1 * f 2 0 := by
  obtain ⟨hI0, hI1, hI2, hI3⟩ := jvGame_infoSet
  obtain ⟨r1, r2, r3, r4, r5⟩ := jvGame_reach f
  unfold probInfo
  rw [hI0, hI1, hI2, hI3, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  simp [r1, r2, r3, r4, r5, add_assoc]

/-- The beliefs of the weak PBE: probability one on the middle node of I's information set
(and on the singleton information sets). -/
def jvBelief (x : List (Fin 3)) : ℝ := if x = [1] ∨ x = [0, 1, 2] then 0 else 1

/-- **Example 9.C.2** (MWG, pp. 286-287). ((propose joint venture, in if E2 declines), accept,
accommodate if entry occurs) with beliefs `μ(middle node) = 1` is a weak perfect Bayesian
equilibrium; and it is the unique weak PBE: in every weak PBE `(σ, μ)` E1 proposes the joint
venture, E2 accepts, I accommodates, E1 enters if E2 declines, and `μ` puts probability one on
the middle node of I's information set. -/
theorem example_9_C_2_weakPBE :
    IsWeakPBE jvGame (pureMoves ![2, 0, 0, 1]) jvBelief ∧
    ∀ F μ, IsWeakPBE jvGame F μ →
      F 0 0 2 = 1 ∧ F 1 1 0 = 1 ∧ F 2 3 1 = 1 ∧ F 0 2 0 = 1 ∧
      μ [0, 2] = 1 ∧ μ [1] = 0 ∧ μ [0, 1, 2] = 0 := by
  obtain ⟨hI0, hI1, hI2, hI3⟩ := jvGame_infoSet
  have hc := jvGame_cont
  have hcp := jvGame_condPayoff
  have hr := jvGame_reach
  have hpi := jvGame_probInfo
  have hk4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  constructor
  · have hB : IsBehaviorProfile jvGame (pureMoves (I := Fin 3) ![2, 0, 0, 1]) :=
      isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [jvGame]
    refine ⟨hB, ⟨fun x _ => ?_, fun k => ?_⟩, fun k => ?_, fun k hk x hx => ?_⟩
    · unfold jvBelief; split_ifs <;> norm_num
    · rcases hk4 k with rfl | rfl | rfl | rfl
      · simp [hI0, jvBelief]
      · simp [hI1, jvBelief]
      · simp [hI2, jvBelief]
      · rw [hI3, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
        simp [jvBelief]
    · intro i hi g hg
      rcases hk4 k with rfl | rfl | rfl | rfl
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        have h0 := (hg 0 rfl).1
        have h1 := (hg 0 rfl).2.2
        simp only [jvGame, Fin.sum_univ_three, ↓reduceIte] at h1
        rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2.2.2, (hc _ _).2.2.2.2]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1, h0 2]
      · obtain rfl : i = 1 := (Option.some.inj (hi : some 1 = some i)).symm
        have h0 := (hg 1 rfl).1
        have h1 := (hg 1 rfl).2.2
        simp [jvGame] at h1
        rw [(hcp _ _ _).2.1, (hcp _ _ _).2.1, (hc _ _).2.2.2.1, (hc _ _).2.2.2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1]
      · obtain rfl : i = 0 := (Option.some.inj (hi : some 0 = some i)).symm
        have h0 := (hg 2 rfl).1
        have h1 := (hg 2 rfl).2.2
        simp [jvGame] at h1
        rw [(hcp _ _ _).2.2.1, (hcp _ _ _).2.2.1, (hc _ _).2.2.1, (hc _ _).2.2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1]
      · obtain rfl : i = 2 := (Option.some.inj (hi : some 2 = some i)).symm
        have h0 := (hg 3 rfl).1
        have h1 := (hg 3 rfl).2.2
        simp [jvGame] at h1
        rw [(hcp _ _ _).2.2.2, (hcp _ _ _).2.2.2, (hc _ _).2.1, (hc _ _).2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        nlinarith [h0 0, h0 1]
    · rcases hk4 k with rfl | rfl | rfl | rfl
      · rw [hI0, Finset.mem_singleton] at hx
        subst hx
        rw [(hpi _).1]
        simp [jvBelief]
      · rw [hI1, Finset.mem_singleton] at hx
        subst hx
        rw [(hpi _).2.1, (hr _).2.1]
        simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
      · rw [(hpi _).2.2.1] at hk
        simp [jvGame_assemble_eq, pureMoves, dirac] at hk
      · rw [hI3] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [(hpi _).2.2.2]
        rcases hx with rfl | rfl | rfl
        · rw [(hr _).1]
          simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        · rw [(hr _).2.2.1]
          simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
        · rw [(hr _).2.2.2.2]
          simp [jvGame_assemble_eq, pureMoves, dirac, jvBelief]
  · intro F μ ⟨hF, hμ, hSR, hBy⟩
    obtain ⟨hp0, hp1, hq0, hq1, hr0, hr1, hs0, hs1⟩ := jvGame_behavior hF
    have hμ1 : μ [2] = 1 := by simpa [hI1] using hμ.2 1
    have hμ0 : μ [] = 1 := by simpa [hI0] using hμ.2 0
    have hμ2 : μ [1, 2] = 1 := by simpa [hI2] using hμ.2 2
    -- E2 accepts
    have hacc := hSR 1 1 rfl _ (jvGame_beh_update hF (i := 1) (k := 1) (a := 0) (by decide))
    rw [(hcp _ _ _).2.1, (hcp _ _ _).2.1, (hc _ _).2.2.2.1, (hc _ _).2.2.2.1] at hacc
    replace hacc : F 2 3 0 + F 2 3 1 * 4 ≤ F 1 1 0 * (F 2 3 0 + F 2 3 1 * 4) := by
      simpa [jvGame_assemble_eq, hμ1, dirac] using hacc
    have hE2 : F 1 1 0 = 1 := by nlinarith [hq0 0, hq0 1, hs0 0, hs0 1]
    have hE2' : F 1 1 1 = 0 := by linarith
    -- E1 proposes the joint venture
    have hjv := hSR 0 0 rfl _ (jvGame_beh_update hF (i := 0) (k := 0) (a := 2) (by decide))
    rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2.2.2, (hc _ _).2.2.2.2] at hjv
    replace hjv : F 2 3 0 + F 2 3 1 * 4 ≤
        F 0 0 1 * (-F 2 3 0 + F 2 3 1 * 2) + F 0 0 2 * (F 2 3 0 + F 2 3 1 * 4) := by
      simpa [jvGame_assemble_eq, hμ0, dirac, hE2, hE2'] using hjv
    have hV : 1 ≤ F 2 3 0 + 4 * F 2 3 1 := by nlinarith [hs0 0, hs0 1]
    have e : F 0 0 0 * (F 2 3 0 + F 2 3 1 * 4) + F 0 0 1 * (F 2 3 0 + F 2 3 1 * 4) +
        F 0 0 2 * (F 2 3 0 + F 2 3 1 * 4) = F 2 3 0 + F 2 3 1 * 4 := by
      rw [← add_mul, ← add_mul, hp1, one_mul]
    have e2 : F 0 0 1 * F 2 3 0 + F 0 0 1 * F 2 3 1 = F 0 0 1 := by
      rw [← mul_add, hs1, mul_one]
    have hkey : F 0 0 0 * (F 2 3 0 + 4 * F 2 3 1) + 2 * F 0 0 1 ≤ 0 := by linarith
    have hP0 : F 0 0 0 = 0 := by nlinarith [hp0 0, hp0 1]
    have hP1 : F 0 0 1 = 0 := by nlinarith [hp0 0, hp0 1]
    have hP2 : F 0 0 2 = 1 := by linarith
    -- Bayes' rule at I's information set
    have hpos : 0 < probInfo jvGame (jvGame.assemble F) 3 := by
      rw [(hpi _).2.2.2]
      norm_num [jvGame_assemble_eq, hP1, hP2, hE2, hE2']
    have hprob : probInfo jvGame (jvGame.assemble F) 3 = 1 := by
      rw [(hpi _).2.2.2]
      norm_num [jvGame_assemble_eq, hP1, hP2, hE2, hE2']
    have b1 := hBy 3 hpos [1] (by rw [hI3]; simp)
    have b2 := hBy 3 hpos [0, 2] (by rw [hI3]; simp)
    have b3 := hBy 3 hpos [0, 1, 2] (by rw [hI3]; simp)
    rw [hprob, (hr _).1] at b1
    rw [hprob, (hr _).2.2.1] at b2
    rw [hprob, (hr _).2.2.2.2] at b3
    replace b1 : μ [1] = 0 := by simpa [jvGame_assemble_eq, hP1] using b1
    replace b2 : μ [0, 2] = 1 := by simpa [jvGame_assemble_eq, hP2, hE2] using b2
    replace b3 : μ [0, 1, 2] = 0 := by simpa [jvGame_assemble_eq, hE2'] using b3
    -- I accommodates
    have hIa := hSR 3 2 rfl _ (jvGame_beh_update hF (i := 2) (k := 3) (a := 1) (by decide))
    rw [(hcp _ _ _).2.2.2, (hcp _ _ _).2.2.2, b1, b2, b3] at hIa
    simp [(hc _ _).2.1, jvGame_assemble_eq, dirac] at hIa
    have hI : F 2 3 1 = 1 := by nlinarith [hs0 0, hs0 1]
    have hI' : F 2 3 0 = 0 := by linarith
    -- E1 enters after E2 declines
    have hin := hSR 2 0 rfl _ (jvGame_beh_update hF (i := 0) (k := 2) (a := 0) (by decide))
    rw [(hcp _ _ _).2.2.1, (hcp _ _ _).2.2.1, (hc _ _).2.2.1, (hc _ _).2.2.1] at hin
    simp [jvGame_assemble_eq, hμ2, dirac, hI, hI'] at hin
    have hE1 : F 0 2 0 = 1 := by nlinarith [hr0 0, hr0 1]
    exact ⟨hP2, hE2, hI, hE1, b2, b1, b3⟩

/-- The only subgame of the joint venture game is the game as a whole: every other decision
node either shares I's information set or has a successor in it together with the node `[1]`
outside. -/
theorem jvGame_subgames {x : List (Fin 3)} (hx : IsSubgameRoot jvGame x) : x = [] := by
  have hmem := (mem_decisionNodes _).2 hx.1
  rw [show jvGame.decisionNodes = {[], [1], [2], [0, 2], [1, 2], [0, 1, 2]} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hd : ∀ y ∈ ({[1], [0, 2], [0, 1, 2]} : Finset (List (Fin 3))), jvGame.IsDecision y := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> exact ⟨by decide, 0, by decide⟩
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (hx.2.1 [0, 2] (hd _ (by simp)) rfl) (by decide)
  · exact absurd (hx.2.2 [0, 2] (hd _ (by simp)) (by decide) [1] (hd _ (by simp)) rfl)
      (by decide)
  · exact absurd (hx.2.1 [1] (hd _ (by simp)) rfl) (by decide)
  · exact absurd (hx.2.2 [0, 1, 2] (hd _ (by simp)) (by decide) [1] (hd _ (by simp)) rfl)
      (by decide)
  · exact absurd (hx.2.1 [1] (hd _ (by simp)) rfl) (by decide)

/-- **Example 9.C.2** (MWG, p. 287). The weak PBE is not the only Nash equilibrium, nor the only
SPNE: ((out, out if E2 declines), decline, fight if entry occurs) is a subgame perfect Nash
equilibrium (the only subgame is the whole game, and no player gains by deviating). -/
theorem example_9_C_2_spne : IsSPNE jvGame (pureMoves ![0, 1, 1, 0]) := by
  have hB : IsBehaviorProfile jvGame (pureMoves (I := Fin 3) ![0, 1, 1, 0]) :=
    isBehaviorProfile_pureMoves fun k => by fin_cases k <;> simp [jvGame]
  refine exercise_9_B_2a _ (fun _ hx => jvGame_subgames hx) ⟨hB, fun i g hg => ?_⟩
  rw [(jvGame_cont _ _).2.2.2.2, (jvGame_cont _ _).2.2.2.2]
  have hi3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hi3 i with rfl | rfl | rfl
  · have h0 := (hg 0 rfl).1
    have h2 := (hg 2 rfl).1
    simp [jvGame_assemble_eq, pureMoves, dirac]
    nlinarith [h0 1, h0 2, h2 0]
  · simp [jvGame_assemble_eq, pureMoves, dirac]
  · simp [jvGame_assemble_eq, pureMoves, dirac]

end MWG.DynamicGames
