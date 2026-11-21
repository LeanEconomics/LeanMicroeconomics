/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry

/-!
# A three-player game of perfect information

MWG, Example 9.B.2 (Figure 9.B.3, pp. 271-272) and Exercises 9.B.1 and 9.B.3.

Players `0, 1, 2` are MWG's players 1, 2, 3. Information sets (singletons): `0` = player 1 at
the root (`L` = `0`, `R` = `1`); `1` = player 3 after `L`; `2` = player 2 after `R` (`a` = `0`,
`b` = `1`); `3` = player 3 after `R, a`; `4` = player 3 after `R, b` (`ℓ` = `0`, `r` = `1`).
A pure profile is a choice `c k ∈ {0, 1}` at each information set.

* `example_9_B_2`: backward induction gives `σ₁ = R`, `σ₂ = a`, and `σ₃ = r` after `L`, `r`
  after `(R, a)`, `ℓ` after `(R, b)`; it is the unique SPNE (Proposition 9.B.2: no player has
  equal payoffs at two terminal nodes).
* `exercise_9_B_1`: the game has five subgames, one for each decision node.
* `exercise_9_B_3`: the pure strategy Nash equilibria (with pure deviations, Definition 8.D.1
  for the induced normal form) are exactly six profiles; the backward-induction profile is one
  of them, and the other five are not subgame perfect (they violate sequential rationality).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- The information sets of Figure 9.B.3. -/
def threeInfo (x : List (Fin 2)) : Fin 5 :=
  if x = [0] then 1 else if x = [1] then 2 else if x = [0, 1] then 3 else if x = [1, 1] then 4
  else 0

/-- The payoffs `(u₁, u₂, u₃)` of Figure 9.B.3 as integers. -/
def threePayZ (z : List (Fin 2)) : Fin 3 → ℤ :=
  if z = [0, 0] then ![2, 0, 1] else if z = [1, 0] then ![-1, 5, 6]
  else if z = [0, 0, 1] then ![3, 1, 2] else if z = [1, 0, 1] then ![5, 4, 4]
  else if z = [0, 1, 1] then ![0, -1, 7] else if z = [1, 1, 1] then ![-2, 2, 0] else 0

/-- **Example 9.B.2, Figure 9.B.3(a)** (MWG, p. 271). A three-player finite game of perfect
information. -/
def threeGame : ExtensiveForm (Fin 3) (Fin 2) (Fin 5) where
  nodes := {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1], [0, 0, 1], [1, 0, 1], [0, 1, 1],
    [1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := threeInfo
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player := ![some 0, some 2, some 1, some 2, some 2]
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_zero := fun k hk => absurd hk (by fin_cases k <;> simp)
  nature_sum := fun k hk => absurd hk (by fin_cases k <;> simp)
  payoff i z := threePayZ z i

theorem threeGame_nodes : threeGame.nodes = {[], [0], [1], [0, 0], [1, 0], [0, 1], [1, 1],
    [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]} := rfl
theorem threeGame_info : threeGame.info = threeInfo := rfl
theorem threeGame_avail (k : Fin 5) : threeGame.avail k = Finset.univ := rfl
theorem threeGame_payoff (i : Fin 3) (z : List (Fin 2)) : threeGame.payoff i z = threePayZ z i :=
  rfl

/-- The payoff of the terminal node reached by the pure choices `c`. -/
def threeOutcome (c : Fin 5 → Fin 2) (i : Fin 3) : ℤ :=
  if c 0 = 0 then threePayZ [c 1, 0] i
  else if c 2 = 0 then threePayZ [c 3, 0, 1] i else threePayZ [c 4, 1, 1] i

theorem two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

/-- The expected payoff of pure choices is the payoff of the terminal node they reach. -/
theorem threeGame_cont_pure (c : Fin 5 → Fin 2) (i : Fin 3) :
    cont threeGame (threeGame.assemble (pureMoves c)) [] i = threeOutcome c i := by
  have hasm : ∀ k, threeGame.assemble (pureMoves c) k = dirac (c k) := fun k => by
    fin_cases k <;> exact threeGame.assemble_of_some _ rfl
  rcases two_cases (c 0) with h0 | h0 <;> rcases two_cases (c 1) with h1 | h1 <;>
    rcases two_cases (c 2) with h2 | h2 <;> rcases two_cases (c 3) with h3 | h3 <;>
    rcases two_cases (c 4) with h4 | h4 <;>
    simp [cont_unfold, threeGame_nodes, threeGame_info, threeGame_avail, threeGame_payoff,
      threeInfo, hasm, dirac, h0, h1, h2, h3, h4, threeOutcome, threePayZ, Fin.sum_univ_two]

/-- Pure strategy Nash equilibrium (Definition 8.D.1 for the induced normal form): no player
gains by changing her choices at her own information sets. -/
def IsPureNash3 (c : Fin 5 → Fin 2) : Prop :=
  ∀ i c', (∀ k, threeGame.player k ≠ some i → c' k = c k) →
    cont threeGame (threeGame.assemble (pureMoves c')) [] i ≤
      cont threeGame (threeGame.assemble (pureMoves c)) [] i

/-- The backward-induction profile of Example 9.B.2. -/
def threeBI : Fin 5 → Fin 2 := ![1, 1, 0, 1, 0]

/-- **Exercise 9.B.3** (MWG, p. 301). The pure strategy Nash equilibria of the game of
Example 9.B.2 are exactly the six profiles `(σ₁; σ₃ after L; σ₂; σ₃ after (R,a); σ₃ after
(R,b))` = `(L; r; b; ℓ; r)`, `(L; r; b; r; r)`, `(R; ℓ; a; r; ℓ)`, `(R; ℓ; a; r; r)`,
`(R; r; a; r; ℓ)` (backward induction) and `(R; r; a; r; r)`. -/
theorem exercise_9_B_3_nash (c : Fin 5 → Fin 2) :
    IsPureNash3 c ↔ c ∈ ({![0, 1, 1, 0, 1], ![0, 1, 1, 1, 1], ![1, 0, 0, 1, 0],
      ![1, 0, 0, 1, 1], ![1, 1, 0, 1, 0], ![1, 1, 0, 1, 1]} : Finset (Fin 5 → Fin 2)) := by
  have key : IsPureNash3 c ↔ ∀ i c', (∀ k, threeGame.player k ≠ some i → c' k = c k) →
      threeOutcome c' i ≤ threeOutcome c i := by
    unfold IsPureNash3
    simp only [threeGame_cont_pure, Int.cast_le]
  rw [key]
  clear key
  have hp : ∀ k, threeGame.player k = ![some 0, some 2, some 1, some 2, some 2] k := fun _ => rfl
  simp only [hp]
  revert c
  decide

/-- **Example 9.B.2** (MWG, pp. 271-272). Backward induction identifies `σ₁ = R`, `σ₂ = a`
after `R`, and `σ₃ = r` after `L`, `r` after `(R, a)`, `ℓ` after `(R, b)`; this profile is the
unique subgame perfect Nash equilibrium (Proposition 9.B.2). -/
theorem example_9_B_2 :
    IsSPNE threeGame (pureMoves threeBI) ∧ ∀ F, IsSPNE threeGame F →
      ∀ k, threeGame.assemble F k = dirac (threeBI k) := by
  have hPI : threeGame.PerfectInformation := by
    unfold ExtensiveForm.PerfectInformation; decide
  have hB : IsBehaviorProfile threeGame (pureMoves (I := Fin 3) threeBI) :=
    isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  have hasm : ∀ k, threeGame.assemble (pureMoves threeBI) k = dirac (threeBI k) := fun k => by
    fin_cases k <;> exact threeGame.assemble_of_some _ rfl
  have hasm' : ∀ k, threeGame.assemble (pureMoves ![1, 1, 0, 1, 0]) k =
      dirac (![1, 1, 0, 1, 0] k) := hasm
  have hS : IsSPNE threeGame (pureMoves threeBI) := by
    refine isSPNE_of_oneShotOptimal _ hB fun x hx j hj a _ => ?_
    have hx' := (mem_decisionNodes _).2 hx
    rw [show threeGame.decisionNodes = {[], [0], [1], [0, 1], [1, 1]} by decide] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
    · cases hj
      rcases two_cases a with rfl | rfl <;>
        simp [cont_unfold, threeGame_nodes, threeGame_info, threeGame_avail, threeGame_payoff,
          threeInfo, hasm', dirac, threeBI, threePayZ, Fin.sum_univ_two] <;> norm_num
  refine ⟨hS, fun F hF k => ?_⟩
  rw [← hasm k]
  refine (proposition_9_B_2 _ hPI).2 (fun k => by fin_cases k <;> simp [threeGame])
    (fun i z hz z' hz' he => ?_) F _ hF hS k
  rw [show threeGame.terminals = {[0, 0], [1, 0], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]}
    by decide] at hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  simp only [threeGame] at he
  fin_cases i <;> rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threePayZ] at he ⊢ <;>
    norm_num at he

/-- **Exercise 9.B.1** (MWG, p. 301). The game of Example 9.B.2 has five subgames: every one of
its five decision nodes initiates a subgame (perfect information). -/
theorem exercise_9_B_1 :
    (∀ x, IsSubgameRoot threeGame x ↔ x ∈ threeGame.decisionNodes) ∧
      threeGame.decisionNodes.card = 5 := by
  have hPI : threeGame.PerfectInformation := by
    unfold ExtensiveForm.PerfectInformation; decide
  refine ⟨fun x => ⟨fun h => (mem_decisionNodes _).2 h.1, fun h =>
    isSubgameRoot_of_perfectInformation _ hPI ((mem_decisionNodes _).1 h)⟩, by decide⟩

/-- **Exercise 9.B.3** (MWG, p. 301). The backward-induction profile is a Nash equilibrium,
and the other five pure Nash equilibria are not subgame perfect: each prescribes, at some
decision node, a move that is not optimal given the continuation play (sequential
rationality fails). -/
theorem exercise_9_B_3 :
    IsPureNash3 threeBI ∧ ∀ c, IsPureNash3 c → c ≠ threeBI → ¬ IsSPNE threeGame (pureMoves c) := by
  refine ⟨(exercise_9_B_3_nash _).2 (by decide), fun c _ hne hS => hne ?_⟩
  funext k
  have h := example_9_B_2.2 _ hS k
  have hk : threeGame.assemble (pureMoves c) k = dirac (c k) := by
    fin_cases k <;> exact threeGame.assemble_of_some _ rfl
  rw [hk] at h
  have := congrFun h (c k)
  simp only [dirac, ite_true] at this
  split_ifs at this with h'
  · exact h'
  · norm_num at this

end MWG.DynamicGames
