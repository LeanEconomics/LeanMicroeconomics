/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Bimatrix
import Mathlib.Tactic.FinCases

/-!
# Maskin's first-mover game

MWG, Exercise 9.B.5(c)-(e) (p. 302). Two players choose actions `m₁ ∈ M₁` and `m₂ ∈ M₂` with
payoffs `φ₁(m₁, m₂)` and `φ₂(m₁, m₂)`. In game (a) they move simultaneously; in game (b)
player 1 moves first and player 2 observes `m₁`, so a strategy of player 2 is a function
`s₂ : M₁ → M₂` (Exercise 9.B.5(b), `exercise_9_B_5b`).

Game (b) is a finite game of perfect information whose subgames are the whole game and the
`|M₁|` subgames after player 1's moves, so its (pure) SPNE are the profiles found by backward
induction: `s₂ m₁'` is a best reply of player 2 after every `m₁'`, and `m₁` is a best reply of
player 1 against `s₂` (`IsMaskinSPNE`). A (pure) Nash equilibrium of (b) only requires player
2's reply on the path to be optimal (`IsMaskinNash`).

* `exercise_9_B_5c`: if (b) has two distinct SPNE, there are two distinct pairs of moves between
  which player 1 or player 2 is indifferent; `exercise_9_B_5c_instance`.
* `exercise_9_B_5d`: if player 2 is never indifferent between distinct pairs of moves and
  `(a, b)` is a pure Nash equilibrium of (a), every SPNE of (b) gives player 1 at least
  `φ₁(a, b)`; `exercise_9_B_5d_instance`. `exercise_9_B_5d_nash`: this fails for Nash
  equilibria of (b).
* `exercise_9_B_5e_ties`, `exercise_9_B_5e_mixed`: the conclusion of (d) fails if player 2 has
  ties, or if the pure Nash equilibrium is replaced by a mixed one.

Departure (an encoding): the SPNE of (b) are pure profiles given by their backward-induction
characterisation rather than by Chapter 7's `ExtensiveForm` (corrections, item 9).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames

variable {M₁ M₂ : Type*}

/-- **Exercise 9.B.5(b)** (MWG, p. 302). A pure subgame perfect Nash equilibrium `(m₁, s₂)` of
the game in which player 1 moves first: after every move `m₁'` player 2's reply `s₂ m₁'` is a
best reply, and `m₁` is a best reply of player 1 against `s₂` (backward induction; the subgames
are the game itself and the subgames after each `m₁'`). -/
def IsMaskinSPNE (φ₁ φ₂ : M₁ → M₂ → ℝ) (m₁ : M₁) (s₂ : M₁ → M₂) : Prop :=
  (∀ m₁' m₂', φ₂ m₁' m₂' ≤ φ₂ m₁' (s₂ m₁')) ∧ ∀ m₁', φ₁ m₁' (s₂ m₁') ≤ φ₁ m₁ (s₂ m₁)

/-- **Exercise 9.B.5(b)** (MWG, p. 302). A pure Nash equilibrium `(m₁, s₂)` of the game in which
player 1 moves first: no strategy `s₂' : M₁ → M₂` of player 2 and no move `m₁'` of player 1 is a
profitable deviation. -/
def IsMaskinNash (φ₁ φ₂ : M₁ → M₂ → ℝ) (m₁ : M₁) (s₂ : M₁ → M₂) : Prop :=
  (∀ s₂' : M₁ → M₂, φ₂ m₁ (s₂' m₁) ≤ φ₂ m₁ (s₂ m₁)) ∧ ∀ m₁', φ₁ m₁' (s₂ m₁') ≤ φ₁ m₁ (s₂ m₁)

/-- **Exercise 9.B.5(a)** (MWG, p. 302). A pure Nash equilibrium `(a, b)` of the simultaneous
game. -/
def IsMaskinSimNash (φ₁ φ₂ : M₁ → M₂ → ℝ) (a : M₁) (b : M₂) : Prop :=
  (∀ a', φ₁ a' b ≤ φ₁ a b) ∧ ∀ b', φ₂ a b' ≤ φ₂ a b

/-- Every SPNE of (b) is a Nash equilibrium of (b). -/
theorem IsMaskinSPNE.isMaskinNash {φ₁ φ₂ : M₁ → M₂ → ℝ} {m₁ : M₁} {s₂ : M₁ → M₂}
    (h : IsMaskinSPNE φ₁ φ₂ m₁ s₂) : IsMaskinNash φ₁ φ₂ m₁ s₂ :=
  ⟨fun s₂' => h.1 m₁ (s₂' m₁), h.2⟩

/-- **Exercise 9.B.5(c)** (MWG, p. 302). If the game in (b) has two distinct SPNE, then there
are two pairs of moves `(m₁, m₂) ≠ (m₁', m₂')` with `φ₁(m₁, m₂) = φ₁(m₁', m₂')` or
`φ₂(m₁, m₂) = φ₂(m₁', m₂')`. -/
theorem exercise_9_B_5c {φ₁ φ₂ : M₁ → M₂ → ℝ} {m₁ m₁' : M₁} {s₂ s₂' : M₁ → M₂}
    (h : IsMaskinSPNE φ₁ φ₂ m₁ s₂) (h' : IsMaskinSPNE φ₁ φ₂ m₁' s₂')
    (hne : (m₁, s₂) ≠ (m₁', s₂')) :
    ∃ p q : M₁ × M₂, p ≠ q ∧ (φ₁ p.1 p.2 = φ₁ q.1 q.2 ∨ φ₂ p.1 p.2 = φ₂ q.1 q.2) := by
  by_cases hs : s₂ = s₂'
  · subst hs
    have hm : m₁ ≠ m₁' := fun hm => hne (by rw [hm])
    refine ⟨(m₁, s₂ m₁), (m₁', s₂ m₁'), fun he => hm (Prod.ext_iff.1 he).1, Or.inl ?_⟩
    exact le_antisymm (h'.2 m₁) (h.2 m₁')
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hs
    refine ⟨(k, s₂ k), (k, s₂' k), fun he => hk (Prod.ext_iff.1 he).2, Or.inr ?_⟩
    exact le_antisymm (h'.1 k (s₂ k)) (h.1 k (s₂' k))

/-- **Exercise 9.B.5(d)** (MWG, p. 302). Suppose player 2 is never indifferent between two
distinct pairs of moves, and `(a, b)` is a pure strategy Nash equilibrium of the simultaneous
game (a). Then in every SPNE of (b) player 1's payoff is at least `π₁ = φ₁(a, b)`. -/
theorem exercise_9_B_5d {φ₁ φ₂ : M₁ → M₂ → ℝ}
    (hno : ∀ m₁ m₂ m₁' m₂', (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → φ₂ m₁ m₂ ≠ φ₂ m₁' m₂')
    {a : M₁} {b : M₂} (hab : IsMaskinSimNash φ₁ φ₂ a b) {m₁ : M₁} {s₂ : M₁ → M₂}
    (h : IsMaskinSPNE φ₁ φ₂ m₁ s₂) : φ₁ a b ≤ φ₁ m₁ (s₂ m₁) := by
  have hsa : s₂ a = b := by
    by_contra hne
    exact hno a (s₂ a) a b (Or.inr hne) (le_antisymm (hab.2 (s₂ a)) (h.1 a b))
  rw [← hsa]
  exact h.2 a

/-- The game of the counterexample to the Nash version of Exercise 9.B.5(d): player 1's
payoffs `[[2, 0], [1, -1]]`. -/
def maskinD₁ : Fin 2 → Fin 2 → ℝ := ![![2, 0], ![1, -1]]

/-- Player 2's payoffs `[[3, 2], [1, 0]]` (no ties). -/
def maskinD₂ : Fin 2 → Fin 2 → ℝ := ![![3, 2], ![1, 0]]

theorem maskinD₂_noTies :
    ∀ m₁ m₂ m₁' m₂' : Fin 2, (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → maskinD₂ m₁ m₂ ≠ maskinD₂ m₁' m₂' := by
  intro m₁ m₂ m₁' m₂' hne
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases m₁' <;> fin_cases m₂' <;>
    simp_all [maskinD₂]

/-- **Exercise 9.B.5(d), an instance** (MWG, p. 302). In the game `maskinD₁`, `maskinD₂` player 2
has no ties, `(0, 0)` is a pure Nash equilibrium of (a) with `π₁ = 2`, and the unique SPNE of
(b), `(0, s₂)` with `s₂ = (0 ↦ 0, 1 ↦ 0)`, gives player 1 the payoff `2`. -/
theorem exercise_9_B_5d_instance :
    IsMaskinSimNash maskinD₁ maskinD₂ 0 0 ∧ IsMaskinSPNE maskinD₁ maskinD₂ 0 ![0, 0] ∧
      maskinD₁ 0 (![0, 0] 0) = 2 := by
  refine ⟨⟨fun a' => ?_, fun b' => ?_⟩, ⟨fun m₁' m₂' => ?_, fun m₁' => ?_⟩, by simp [maskinD₁]⟩
  · fin_cases a' <;> norm_num [maskinD₁]
  · fin_cases b' <;> norm_num [maskinD₂]
  · fin_cases m₁' <;> fin_cases m₂' <;> norm_num [maskinD₂]
  · fin_cases m₁' <;> norm_num [maskinD₁]

/-- **Exercise 9.B.5(d), second question** (MWG, p. 302). The bound need not hold for a Nash
equilibrium of (b): in the game `maskinD₁`, `maskinD₂` (player 2 has no ties, `(0, 0)` is a pure
Nash equilibrium of (a) giving player 1 `π₁ = 2`), the profile in which player 1 plays `1` and
player 2 threatens `s₂ = (0 ↦ 1, 1 ↦ 0)` is a Nash equilibrium of (b) giving player 1 only `1`.
-/
theorem exercise_9_B_5d_nash :
    (∀ m₁ m₂ m₁' m₂' : Fin 2, (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → maskinD₂ m₁ m₂ ≠ maskinD₂ m₁' m₂') ∧
    IsMaskinSimNash maskinD₁ maskinD₂ 0 0 ∧ maskinD₁ 0 0 = 2 ∧
    IsMaskinNash maskinD₁ maskinD₂ 1 ![1, 0] ∧ maskinD₁ 1 (![1, 0] 1) = 1 := by
  refine ⟨maskinD₂_noTies, exercise_9_B_5d_instance.1, by simp [maskinD₁],
    ⟨fun s₂' => ?_, fun m₁' => ?_⟩, by simp [maskinD₁]⟩
  · rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) (s₂' 1) with h | h <;>
      simp [h, maskinD₂]
  · fin_cases m₁' <;> norm_num [maskinD₁]

/-- The game of Exercise 9.B.5(e) with ties for player 2: `M₁ = {0}`, `M₂ = {0, 1}`. -/
def maskinTie₁ : Fin 1 → Fin 2 → ℝ := fun _ m₂ => if m₂ = 0 then 1 else 0

/-- **Exercise 9.B.5(e), ties** (MWG, p. 302). If condition (ii) holds for some distinct pairs
the conclusion of (d) fails: with `M₁ = {0}`, player 2 indifferent everywhere and
`φ₁(0, 0) = 1`, `φ₁(0, 1) = 0`, `(0, 0)` is a pure Nash equilibrium of (a) giving `π₁ = 1`, but
`(0, 0 ↦ 1)` is an SPNE of (b) giving player 1 the payoff `0`. -/
theorem exercise_9_B_5e_ties :
    IsMaskinSimNash maskinTie₁ (fun _ _ => 0) 0 0 ∧ maskinTie₁ 0 0 = 1 ∧
      IsMaskinSPNE maskinTie₁ (fun _ _ => 0) 0 (fun _ => 1) ∧ maskinTie₁ 0 1 = 0 := by
  refine ⟨⟨fun a' => ?_, fun _ => le_rfl⟩, by simp [maskinTie₁],
    ⟨fun _ _ => le_rfl, fun m₁' => ?_⟩, by simp [maskinTie₁]⟩
  · fin_cases a'
    exact le_rfl
  · fin_cases m₁'
    exact le_rfl

/-- Player 1's payoffs in the game of Exercise 9.B.5(e) with a mixed equilibrium:
`[[1, -1], [-1, 1]]`. -/
def maskinMix₁ : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![-1, 1]]

/-- Player 2's payoffs `[[-1, 1], [2, -2]]` (no ties). -/
def maskinMix₂ : Fin 2 → Fin 2 → ℝ := ![![-1, 1], ![2, -2]]

theorem maskinMix_spne_iff (m₁ : Fin 2) (s₂ : Fin 2 → Fin 2) :
    IsMaskinSPNE maskinMix₁ maskinMix₂ m₁ s₂ ↔ s₂ 0 = 1 ∧ s₂ 1 = 0 := by
  constructor
  · intro h
    have h0 := h.1 0 1
    have h1 := h.1 1 0
    refine ⟨?_, ?_⟩
    · rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) (s₂ 0) with he | he
      · rw [he] at h0
        norm_num [maskinMix₂] at h0
      · exact he
    · rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) (s₂ 1) with he | he
      · exact he
      · rw [he] at h1
        norm_num [maskinMix₂] at h1
  · rintro ⟨h0, h1⟩
    refine ⟨fun m₁' m₂' => ?_, fun m₁' => ?_⟩
    · fin_cases m₁' <;> fin_cases m₂' <;> simp [h0, h1, maskinMix₂]
    · fin_cases m₁' <;> fin_cases m₁ <;> simp [h0, h1, maskinMix₁]

/-- **Exercise 9.B.5(c), an instance** (MWG, p. 302). The game `maskinMix₁`, `maskinMix₂` has
two distinct SPNE, `(0, s₂)` and `(1, s₂)` with `s₂ = (0 ↦ 1, 1 ↦ 0)`; player 1 is indifferent
between the distinct pairs `(0, 1)` and `(1, 0)`. -/
theorem exercise_9_B_5c_instance :
    IsMaskinSPNE maskinMix₁ maskinMix₂ 0 ![1, 0] ∧ IsMaskinSPNE maskinMix₁ maskinMix₂ 1 ![1, 0] ∧
      maskinMix₁ 0 1 = maskinMix₁ 1 0 :=
  ⟨(maskinMix_spne_iff 0 _).2 ⟨rfl, rfl⟩, (maskinMix_spne_iff 1 _).2 ⟨rfl, rfl⟩,
    by simp [maskinMix₁]⟩

/-- **Exercise 9.B.5(e), mixed equilibria** (MWG, p. 302). The conclusion of (d) fails if the
pure strategy Nash equilibrium of (a) is replaced by a mixed one: in the game `maskinMix₁`,
`maskinMix₂` player 2 has no ties, player 1 playing `0` with probability `2/3` and player 2
playing `0` with probability `1/2` is a mixed Nash equilibrium of (a) giving player 1 the payoff
`0`, but every SPNE of (b) gives player 1 the payoff `−1`. -/
theorem exercise_9_B_5e_mixed :
    (∀ m₁ m₂ m₁' m₂' : Fin 2, (m₁ ≠ m₁' ∨ m₂ ≠ m₂') → maskinMix₂ m₁ m₂ ≠ maskinMix₂ m₁' m₂') ∧
    IsMixedNash (bimatrix maskinMix₁ maskinMix₂) (mp ![2 / 3, 1 / 3] ![1 / 2, 1 / 2]) ∧
    (bimatrix maskinMix₁ maskinMix₂).mixedPayoff (mp ![2 / 3, 1 / 3] ![1 / 2, 1 / 2]) 0 = 0 ∧
    ∀ m₁ s₂, IsMaskinSPNE maskinMix₁ maskinMix₂ m₁ s₂ → maskinMix₁ m₁ (s₂ m₁) = -1 := by
  have hx : IsMixedStrategy (![2 / 3, 1 / 3] : Fin 2 → ℝ) := by
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a <;> norm_num
    · simp [Fin.sum_univ_two]
      norm_num
  have hy : IsMixedStrategy (![1 / 2, 1 / 2] : Fin 2 → ℝ) := by
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a <;> norm_num
    · simp [Fin.sum_univ_two]
      norm_num
  refine ⟨?_, ?_, ?_, fun m₁ s₂ h => ?_⟩
  · intro m₁ m₂ m₁' m₂' hne
    fin_cases m₁ <;> fin_cases m₂ <;> fin_cases m₁' <;> fin_cases m₂' <;>
      simp_all [maskinMix₂] <;> norm_num
  · refine (bimatrix_isMixedNash_iff _ _ hx hy).2 ⟨fun a' => ?_, fun b' => ?_⟩
    · fin_cases a' <;> simp [Fin.sum_univ_two, maskinMix₁]
    · fin_cases b' <;> simp [Fin.sum_univ_two, maskinMix₂] <;> norm_num
  · rw [(bimatrix_mixedPayoff _ _ _).1]
    simp [Fin.sum_univ_two, maskinMix₁]
  · obtain ⟨h0, h1⟩ := (maskinMix_spne_iff m₁ s₂).1 h
    fin_cases m₁ <;> simp [h0, h1, maskinMix₁]

end MWG.DynamicGames
