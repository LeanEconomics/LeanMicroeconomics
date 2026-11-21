/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.Mixed
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Basic

/-!
# Dominant and dominated strategies; pure Nash equilibrium

MWG, Sections 8.A-8.B (pp. 235-240) and Definition 8.D.1 (p. 246).

Games are the Chapter 7 normal forms `Γ_N = [I, {S_i}, {u_i(·)}]`
(`MWG.NoncooperativeGames.NormalForm`). A profile of the rivals' strategies `s_{-i}` is
represented by a full profile `r` whose `i`-th coordinate is ignored: `(s_i, s_{-i})` is
`Function.update r i s_i`.

* Definitions 8.B.1-8.B.3: `StrictlyDominant`, `StrictlyDominates`, `StrictlyDominated`,
  `WeaklyDominates`, `WeaklyDominated`, `WeaklyDominant`, and the restatement of 8.B.1 on
  p. 237 (`strictlyDominant_iff_dominates`).
* Definition 8.D.1 (`IsNashEquilibrium`) and the best-response correspondence `b_i(s_{-i})`
  of p. 247 (`bestResponse`, `isNashEquilibrium_iff_mem_bestResponse`).
* Iterated deletion of strictly dominated strategies (pp. 238-240): a deletion step removes
  some strategies that are strictly dominated, within the remaining game, by a remaining
  strategy (`SDStep`); a process is a finite chain of steps from the full game
  (`Relation.ReflTransGen SDStep`), and it is complete when nothing remaining is dominated
  (`SDTerminal`).
* **Exercise 8.B.4** (`exercise_8_B_4`): in a game with finitely many strategies, the order of
  deletion does not matter: every complete process ends at the same sets. The finiteness is
  needed: `exercise_8_B_4_infinite_counterexample` is a one-player game with strategies `ℕ`
  where two complete processes end at `{0}` and `{1}` (correction 1).
* **Exercise 8.D.2** (`exercise_8_D_2`): if iterated deletion leaves a single profile, it is a
  Nash equilibrium.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

variable {I : Type*} {S : I → Type*} [DecidableEq I]

/-- **Definition 8.B.1** (MWG, p. 237). `s_i` is a strictly dominant strategy for player `i`:
`u_i(s_i, s_{-i}) > u_i(s_i', s_{-i})` for every `s_i' ≠ s_i` and every `s_{-i}`. -/
def StrictlyDominant (N : NormalForm I S) (i : I) (s : S i) : Prop :=
  ∀ s' : S i, s' ≠ s → ∀ r : (j : I) → S j, N.payoff i (update r i s') < N.payoff i (update r i s)

/-- **Definition 8.B.2** (MWG, p. 237). `s_i'` strictly dominates `s_i`:
`u_i(s_i', s_{-i}) > u_i(s_i, s_{-i})` for all `s_{-i}`. -/
def StrictlyDominates (N : NormalForm I S) (i : I) (s' s : S i) : Prop :=
  ∀ r : (j : I) → S j, N.payoff i (update r i s) < N.payoff i (update r i s')

/-- **Definition 8.B.2** (MWG, p. 237). `s_i` is strictly dominated. -/
def StrictlyDominated (N : NormalForm I S) (i : I) (s : S i) : Prop :=
  ∃ s', StrictlyDominates N i s' s

/-- **Section 8.B** (MWG, p. 237). Restatement of Definition 8.B.1: a strictly dominant strategy
strictly dominates every other strategy. -/
theorem strictlyDominant_iff_dominates (N : NormalForm I S) (i : I) (s : S i) :
    StrictlyDominant N i s ↔ ∀ s', s' ≠ s → StrictlyDominates N i s s' :=
  Iff.rfl

/-- **Definition 8.B.3** (MWG, p. 238). `s_i'` weakly dominates `s_i`: at least as good against
every `s_{-i}` and strictly better against some. -/
def WeaklyDominates (N : NormalForm I S) (i : I) (s' s : S i) : Prop :=
  (∀ r : (j : I) → S j, N.payoff i (update r i s) ≤ N.payoff i (update r i s')) ∧
    ∃ r : (j : I) → S j, N.payoff i (update r i s) < N.payoff i (update r i s')

/-- **Definition 8.B.3** (MWG, p. 238). `s_i` is weakly dominated. -/
def WeaklyDominated (N : NormalForm I S) (i : I) (s : S i) : Prop :=
  ∃ s', WeaklyDominates N i s' s

/-- **Definition 8.B.3** (MWG, p. 238). `s_i` is a weakly dominant strategy: it weakly dominates
every other strategy. -/
def WeaklyDominant (N : NormalForm I S) (i : I) (s : S i) : Prop :=
  ∀ s', s' ≠ s → WeaklyDominates N i s s'

/-- A strictly dominated strategy is weakly dominated (as long as some rival profile exists). -/
theorem StrictlyDominates.weaklyDominates {N : NormalForm I S} {i : I} {s' s : S i}
    (h : StrictlyDominates N i s' s) (r : (j : I) → S j) : WeaklyDominates N i s' s :=
  ⟨fun r => (h r).le, r, h r⟩

/-- Strict domination is transitive. -/
theorem StrictlyDominates.trans {N : NormalForm I S} {i : I} {a b c : S i}
    (hab : StrictlyDominates N i a b) (hbc : StrictlyDominates N i b c) :
    StrictlyDominates N i a c :=
  fun r => (hbc r).trans (hab r)

/-- **Definition 8.D.1** (MWG, p. 246). A pure strategy profile `s` is a Nash equilibrium:
`u_i(s_i, s_{-i}) ≥ u_i(s_i', s_{-i})` for every `i` and every `s_i' ∈ S_i`. -/
def IsNashEquilibrium (N : NormalForm I S) (s : (i : I) → S i) : Prop :=
  ∀ i (t : S i), N.payoff i (update s i t) ≤ N.payoff i s

/-- **Section 8.D** (MWG, p. 247). Player `i`'s best-response correspondence
`b_i(s_{-i}) = {s_i ∈ S_i : u_i(s_i, s_{-i}) ≥ u_i(s_i', s_{-i}) for all s_i' ∈ S_i}`; the `i`-th
coordinate of `r` is ignored. -/
def bestResponse (N : NormalForm I S) (i : I) (r : (j : I) → S j) : Set (S i) :=
  {t | ∀ t' : S i, N.payoff i (update r i t') ≤ N.payoff i (update r i t)}

/-- The best-response correspondence depends only on the rivals' strategies `s_{-i}`. -/
theorem bestResponse_update (N : NormalForm I S) (i : I) (r : (j : I) → S j) (x : S i) :
    bestResponse N i (update r i x) = bestResponse N i r := by
  ext t
  simp only [bestResponse, Set.mem_ofPred_eq, update_idem]

/-- **Section 8.D** (MWG, p. 247). `s` is a Nash equilibrium iff `s_i ∈ b_i(s_{-i})` for all
`i`. -/
theorem isNashEquilibrium_iff_mem_bestResponse (N : NormalForm I S) (s : (i : I) → S i) :
    IsNashEquilibrium N s ↔ ∀ i, s i ∈ bestResponse N i s := by
  simp only [IsNashEquilibrium, bestResponse, Set.mem_ofPred_eq, update_eq_self]

/-- A strictly dominated strategy is never played in a pure Nash equilibrium. -/
theorem IsNashEquilibrium.not_strictlyDominated {N : NormalForm I S} {s : (i : I) → S i}
    (h : IsNashEquilibrium N s) (i : I) : ¬ StrictlyDominated N i (s i) := by
  rintro ⟨s', hs'⟩
  have h1 := hs' s
  rw [update_eq_self] at h1
  exact absurd (h i s') (not_le.2 h1)

/-! ### Iterated deletion of strictly dominated strategies -/

/-- Within the remaining strategy sets `T`, `s_i` is strictly dominated by a remaining strategy
of player `i` against every remaining profile of the rivals. -/
def SDominatedIn (N : NormalForm I S) (T : (i : I) → Set (S i)) (i : I) (s : S i) : Prop :=
  ∃ s' ∈ T i, ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ T j) →
    N.payoff i (update r i s) < N.payoff i (update r i s')

/-- **Section 8.B** (MWG, pp. 238-240). One step of iterated deletion of strictly dominated
strategies: `T'` keeps a subset of each `T_i`, and everything removed is strictly dominated in
the game restricted to `T`. Several strategies of several players may be removed at once. -/
def SDStep (N : NormalForm I S) (T T' : (i : I) → Set (S i)) : Prop :=
  (∀ i, T' i ⊆ T i) ∧ ∀ i, ∀ s ∈ T i, s ∉ T' i → SDominatedIn N T i s

/-- **Section 8.B** (MWG, p. 239). A deletion process is complete when no remaining strategy
is strictly dominated in the remaining game. -/
def SDTerminal (N : NormalForm I S) (T : (i : I) → Set (S i)) : Prop :=
  ∀ i, ∀ s ∈ T i, ¬ SDominatedIn N T i s

/-- The full game: every strategy remains. -/
def fullSets (S : I → Type*) : (i : I) → Set (S i) := fun _ => Set.univ

/-- Deletion only removes strategies. -/
theorem sdChain_subset {N : NormalForm I S} {P Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (SDStep N) P Q) (i : I) : Q i ⊆ P i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (hstep.1 i).trans ih

/-- In a finite game where every remaining set is nonempty, a deletion step leaves every set
nonempty: a maximizer of `u_i(·, r)` for a remaining rival profile `r` is never dominated. -/
theorem sdStep_nonempty [∀ i, Finite (S i)] {N : NormalForm I S}
    {T T' : (i : I) → Set (S i)} (h : SDStep N T T') (hT : ∀ i, (T i).Nonempty) (i : I) :
    (T' i).Nonempty := by
  choose r hr using hT
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image (T i) (fun x => N.payoff i (update r i x))
    (Set.toFinite _) ⟨r i, hr i⟩
  by_contra hne
  have htT' : t ∉ T' i := fun h' => hne ⟨t, h'⟩
  obtain ⟨s', hs', hdom⟩ := h.2 i t ht htT'
  exact absurd (hmax s' hs') (not_le.2 (hdom r fun j _ => hr j))

/-- Every set stays nonempty along a deletion process in a finite game. -/
theorem sdChain_nonempty [∀ i, Finite (S i)] {N : NormalForm I S}
    {P Q : (i : I) → Set (S i)} (h : Relation.ReflTransGen (SDStep N) P Q)
    (hP : ∀ i, (P i).Nonempty) (i : I) : (Q i).Nonempty := by
  induction h generalizing i with
  | refl => exact hP i
  | tail _ hstep ih => exact sdStep_nonempty hstep ih i

/-- The key lemma for Exercise 8.B.4. Along a deletion process from `P` to `Q` in a finite
game, every strategy of `P_i` that is deleted is strictly dominated, against every profile of
the rivals in `Q`, by a strategy that survives in `Q_i`. -/
theorem sdChain_dominated_by_survivor [∀ i, Finite (S i)] {N : NormalForm I S}
    {P Q : (i : I) → Set (S i)} (h : Relation.ReflTransGen (SDStep N) P Q)
    (hP : ∀ i, (P i).Nonempty) (i : I) (s : S i) (hs : s ∈ P i) (hsQ : s ∉ Q i) :
    ∃ t ∈ Q i, ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ Q j) →
      N.payoff i (update r i s) < N.payoff i (update r i t) := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing s with
  | refl => exact absurd hs hsQ
  | @head P P' hstep hrest ih =>
    have hP' : ∀ i, (P' i).Nonempty := fun j => sdStep_nonempty hstep hP j
    have hQP : ∀ j, Q j ⊆ P j := fun j => (sdChain_subset hrest j).trans (hstep.1 j)
    by_cases hsP' : s ∈ P' i
    · exact ih hP' s hsP' hsQ
    · -- `s` was deleted in the first step; pick an undominated dominator in `P_i`
      obtain ⟨s₁, hs₁, hdom₁⟩ := hstep.2 i s hs hsP'
      choose r₀ hr₀ using hP
      set D : Set (S i) := {t | t ∈ P i ∧ ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ P j) →
        N.payoff i (update r i s) < N.payoff i (update r i t)} with hD
      obtain ⟨t, ⟨htP, htdom⟩, hmax⟩ := Set.exists_max_image D
        (fun x => N.payoff i (update r₀ i x)) (Set.toFinite _) ⟨s₁, hs₁, hdom₁⟩
      have htP' : t ∈ P' i := by
        by_contra htP'
        obtain ⟨t₂, ht₂, hdom₂⟩ := hstep.2 i t htP htP'
        have h₂D : t₂ ∈ D := ⟨ht₂, fun r hr => (htdom r hr).trans (hdom₂ r hr)⟩
        exact absurd (hmax t₂ h₂D) (not_le.2 (hdom₂ r₀ fun j _ => hr₀ j))
      by_cases htQ : t ∈ Q i
      · exact ⟨t, htQ, fun r hr => htdom r fun j hj => hQP j (hr j hj)⟩
      · obtain ⟨u, huQ, hdomu⟩ := ih hP' t htP' htQ
        exact ⟨u, huQ, fun r hr => (htdom r fun j hj => hQP j (hr j hj)).trans (hdomu r hr)⟩

/-- A complete deletion process from the full game ends inside every stage of any other
deletion process from the full game. -/
theorem sdTerminal_subset_chain [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    {N : NormalForm I S} {T Q : (i : I) → Set (S i)}
    (hT : Relation.ReflTransGen (SDStep N) (fullSets S) T) (hTt : SDTerminal N T)
    (hQ : Relation.ReflTransGen (SDStep N) (fullSets S) Q) (i : I) : T i ⊆ Q i := by
  have hfull : ∀ j, (fullSets S j).Nonempty := fun j => Set.univ_nonempty
  induction hQ generalizing i with
  | refl => exact Set.subset_univ _
  | @tail P Q _ hstep ih =>
    intro s hsT
    by_contra hsQ
    obtain ⟨s', hs'P, hdom⟩ := hstep.2 i s (ih i hsT) hsQ
    have hTP : ∀ j, T j ⊆ P j := ih
    by_cases hs'T : s' ∈ T i
    · exact hTt i s hsT ⟨s', hs'T, fun r hr => hdom r fun j hj => hTP j (hr j hj)⟩
    · obtain ⟨t, htT, hdomt⟩ :=
        sdChain_dominated_by_survivor hT hfull i s' (Set.mem_univ _) hs'T
      exact hTt i s hsT ⟨t, htT, fun r hr =>
        (hdom r fun j hj => hTP j (hr j hj)).trans (hdomt r hr)⟩

/-- **Exercise 8.B.4** (MWG, p. 262). In a game with finitely many (nonempty) strategy sets,
the order of deletion does not matter: any two complete processes of iterated deletion of
strictly dominated strategies end at the same strategy sets. -/
theorem exercise_8_B_4 [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] {N : NormalForm I S}
    {T₁ T₂ : (i : I) → Set (S i)}
    (h₁ : Relation.ReflTransGen (SDStep N) (fullSets S) T₁) (ht₁ : SDTerminal N T₁)
    (h₂ : Relation.ReflTransGen (SDStep N) (fullSets S) T₂) (ht₂ : SDTerminal N T₂) :
    T₁ = T₂ :=
  funext fun i => (sdTerminal_subset_chain h₁ ht₁ h₂ i).antisymm
    (sdTerminal_subset_chain h₂ ht₂ h₁ i)

/-- A one-player game with strategy set `ℕ` and payoff `u(n) = n` (used to show that
Exercise 8.B.4 needs finitely many strategies). -/
def countingGame : NormalForm Unit (fun _ => ℕ) where
  payoff _ s := (s () : ℝ)

/-- In the counting game, deleting every strategy except `k` is a deletion step from the full
game: every `n` is strictly dominated by `n + 1`. -/
theorem countingGame_step (k : ℕ) :
    SDStep countingGame (fullSets _) (fun _ => {k}) := by
  refine ⟨fun _ => Set.subset_univ _, fun i n _ _ => ⟨n + 1, Set.mem_univ _, fun r _ => ?_⟩⟩
  simp only [countingGame, update_self]
  push_cast
  linarith

/-- In the counting game, `{k}` is a complete result: nothing remaining is dominated. -/
theorem countingGame_terminal (k : ℕ) : SDTerminal countingGame (fun _ => {k}) := by
  rintro i n hn ⟨m, hm, hdom⟩
  have h := hdom (fun _ => k) fun j hj => absurd rfl hj
  rw [Set.mem_singleton_iff] at hn hm
  simp only [countingGame, update_self] at h
  rw [hn, hm] at h
  exact lt_irrefl _ h

/-- **Exercise 8.B.4: finiteness is needed** (correction 1). In the one-player game with
strategies `ℕ` and `u(n) = n`, the complete deletion processes "delete all but `0`" and
"delete all but `1`" end at different sets. -/
theorem exercise_8_B_4_infinite_counterexample :
    ∃ T₁ T₂ : (i : Unit) → Set ℕ,
      Relation.ReflTransGen (SDStep countingGame) (fullSets _) T₁ ∧
      SDTerminal countingGame T₁ ∧
      Relation.ReflTransGen (SDStep countingGame) (fullSets _) T₂ ∧
      SDTerminal countingGame T₂ ∧ T₁ ≠ T₂ := by
  refine ⟨fun _ => {0}, fun _ => {1}, Relation.ReflTransGen.single (countingGame_step 0),
    countingGame_terminal 0, Relation.ReflTransGen.single (countingGame_step 1),
    countingGame_terminal 1, fun h => ?_⟩
  have h01 : ({0} : Set ℕ) = {1} := congrFun h ()
  have h0 : (0 : ℕ) ∈ ({1} : Set ℕ) := h01 ▸ Set.mem_singleton 0
  simp at h0

/-- **Exercise 8.D.2** (MWG, p. 263). If iterated deletion of strictly dominated strategies (in a
game with finitely many strategies) leaves a unique profile `s`, then `s` is a Nash
equilibrium. -/
theorem exercise_8_D_2 [∀ i, Finite (S i)] [∀ i, Nonempty (S i)] {N : NormalForm I S}
    {T : (i : I) → Set (S i)} (hT : Relation.ReflTransGen (SDStep N) (fullSets S) T)
    {s : (i : I) → S i} (hs : ∀ i, T i = {s i}) : IsNashEquilibrium N s := by
  intro i t
  by_cases ht : t = s i
  · rw [ht, update_eq_self]
  · have htT : t ∉ T i := by rw [hs i]; exact ht
    obtain ⟨u, huT, hdom⟩ := sdChain_dominated_by_survivor hT (fun _ => Set.univ_nonempty) i t
      (Set.mem_univ _) htT
    rw [hs i, Set.mem_singleton_iff] at huT
    have := hdom s fun j _ => by rw [hs j]; rfl
    rw [huT, update_eq_self] at this
    exact this.le

end MWG.SimultaneousMoveGames
