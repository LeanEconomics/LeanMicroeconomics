import MWGNoncooperativeGames.Mixed
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import MWGClassicalDemand.AppendixMH
import LeanEconomics.FixedPoint.Brouwer
import LeanEconomics.FixedPoint.Kakutani
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import MWGNoncooperativeGames.MatchingPennies
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Jensen
import MWGProduction.AppendixMM
import Mathlib.Basic.NNReal.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.NormNum
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The algebra of mixed payoffs

MWG, Sections 7.E and 8.B, pp. 232 and 240.

The mixed payoff `u_i(σ) = ∑_s σ₁(s₁) ⋯ σ_I(s_I) u_i(s)` is Chapter 7's
`NormalForm.mixedPayoff`. This module proves the identities that the chapter uses throughout:

* `mixedPayoff_update`: `u_k(τ, σ_{-i}) = ∑_s τ(s_i) [∏_{j ≠ i} σ_j(s_j)] u_k(s)`.
* `mixedPayoff_update_eq_sum_pure`: `u_k(τ, σ_{-i}) = ∑_{s_i} τ(s_i) u_k(s_i, σ_{-i})`, so a
  player's payoff is linear in his own mixed strategy (`mixedPayoff_update_add_smul`).
* `mixedPayoff_update_eq_expect`: the formula of p. 240,
  `u_k(τ, σ_{-i}) = ∑_{s_{-i}} [∏_{k ≠ i} σ_k(s_k)] u_k(τ, s_{-i})`, written as a sum over full
  pure profiles drawn from the mixed profile `σ` (whose `i`-th coordinate sums to one).
* `mixedPayoff_compound`: a mixed profile drawn from independent beliefs over mixed strategies
  has the payoff of the compound profile (used for footnote 1, p. 243).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]

/-- A profile `σ = (σ₁, …, σ_I)` of mixed strategies. -/
def IsMixedProfile (σ : (i : I) → S i → ℝ) : Prop := ∀ i, IsMixedStrategy (σ i)

/-- The degenerate mixed profile that plays the pure profile `s` with probability one. -/
def pureProfile [∀ i, DecidableEq (S i)] (s : (i : I) → S i) : (i : I) → S i → ℝ :=
  fun i => pureMixed (s i)

omit [Fintype I] [DecidableEq I] in
theorem isMixedProfile_pureProfile [∀ i, DecidableEq (S i)] (s : (i : I) → S i) :
    IsMixedProfile (pureProfile s) := fun i => isMixedStrategy_pureMixed (s i)

omit [Fintype I] [∀ i, Fintype (S i)] in
/-- Replacing one coordinate of a pure profile commutes with taking the degenerate profile. -/
theorem pureProfile_update [∀ i, DecidableEq (S i)] (s : (i : I) → S i) (i : I) (a : S i) :
    update (pureProfile s) i (pureMixed a) = pureProfile (update s i a) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [pureProfile]
  · simp [pureProfile, update_of_ne h]

omit [∀ i, Fintype (S i)] in
/-- The weight of a pure profile when coordinate `i` is replaced. -/
theorem prod_update_eq (σ : (i : I) → S i → ℝ) (i : I) (τ : S i → ℝ) (s : (i : I) → S i) :
    ∏ j, update σ i τ j (s j) = τ (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Section 8.B** (MWG, p. 240). `u_k(τ, σ_{-i}) = ∑_s τ(s_i) [∏_{j ≠ i} σ_j(s_j)] u_k(s)`. -/
theorem mixedPayoff_update (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i τ) k =
      ∑ s : (i : I) → S i, τ (s i) * ((∏ j ∈ univ.erase i, σ j (s j)) * N.payoff k s) := by
  unfold NormalForm.mixedPayoff
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [prod_update_eq, mul_assoc]

/-- The payoff of player `k` does not depend on the `i`-th coordinate of `σ` once that
coordinate is replaced. -/
theorem mixedPayoff_update_update (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ τ' : S i → ℝ) (k : I) :
    N.mixedPayoff (update (update σ i τ') i τ) k = N.mixedPayoff (update σ i τ) k := by
  rw [update_idem]

/-- Linearity of `u_k(·, σ_{-i})` in player `i`'s own mixed strategy:
`u_k(τ + c • τ', σ_{-i}) = u_k(τ, σ_{-i}) + c u_k(τ', σ_{-i})`. -/
theorem mixedPayoff_update_add_smul (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ τ' : S i → ℝ) (c : ℝ) (k : I) :
    N.mixedPayoff (update σ i (τ + c • τ')) k =
      N.mixedPayoff (update σ i τ) k + c * N.mixedPayoff (update σ i τ') k := by
  simp only [mixedPayoff_update, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- Linearity: `u_k(∑_x c_x τ_x, σ_{-i}) = ∑_x c_x u_k(τ_x, σ_{-i})`. -/
theorem mixedPayoff_update_sum_smul (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    {K : Type*} [Fintype K] (c : K → ℝ) (τ : K → S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i (∑ x, c x • τ x)) k =
      ∑ x, c x * N.mixedPayoff (update σ i (τ x)) k := by
  simp only [mixedPayoff_update, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
  ring

variable [∀ i, DecidableEq (S i)]

/-- **Section 8.D** (MWG, p. 251). A player's payoff is the average, under his own mixed
strategy, of the payoffs of his pure strategies: `u_k(τ, σ_{-i}) = ∑_a τ(a) u_k(a, σ_{-i})`. -/
theorem mixedPayoff_update_eq_sum_pure (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i τ) k =
      ∑ a, τ a * N.mixedPayoff (update σ i (pureMixed a)) k := by
  have hτ : τ = ∑ a, τ a • pureMixed a := by
    funext b
    simp [Finset.sum_apply, pureMixed]
  conv_lhs => rw [hτ]
  exact mixedPayoff_update_sum_smul N σ i τ (fun a => pureMixed a) k

/-- The payoff against a pure profile with player `i` replaced by the pure strategy `a`. -/
theorem mixedPayoff_pureProfile_update (N : NormalForm I S) (s : (i : I) → S i) (i : I)
    (a : S i) (k : I) :
    N.mixedPayoff (update (pureProfile s) i (pureMixed a)) k = N.payoff k (update s i a) := by
  rw [pureProfile_update]
  exact N.mixedPayoff_pure _ k

/-- The payoff of a degenerate profile is the pure payoff. -/
theorem mixedPayoff_pureProfile (N : NormalForm I S) (s : (i : I) → S i) (k : I) :
    N.mixedPayoff (pureProfile s) k = N.payoff k s :=
  N.mixedPayoff_pure s k

/-- Against a pure rival profile, `u_k(τ, s_{-i}) = ∑_a τ(a) u_k(a, s_{-i})`. -/
theorem mixedPayoff_pureProfile_update_mixed (N : NormalForm I S) (s : (i : I) → S i) (i : I)
    (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update (pureProfile s) i τ) k = ∑ a, τ a * N.payoff k (update s i a) := by
  rw [mixedPayoff_update_eq_sum_pure]
  simp only [mixedPayoff_pureProfile_update]

omit [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The probability that the mixed profile `σ` plays the pure profile `s` is nonnegative. -/
theorem prod_mixed_nonneg {σ : (i : I) → S i → ℝ} (hσ : ∀ i a, 0 ≤ σ i a)
    (s : (i : I) → S i) : 0 ≤ ∏ j, σ j (s j) :=
  Finset.prod_nonneg fun j _ => hσ j _

omit [∀ i, DecidableEq (S i)] in
/-- The weights `∏_{j} σ_j(s_j)` of a mixed profile sum to one. -/
theorem sum_prod_mixed_eq_one {σ : (i : I) → S i → ℝ} (hσ : ∀ i, ∑ a, σ i a = 1) :
    ∑ s : (i : I) → S i, ∏ j, σ j (s j) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => hσ j

/-- **Section 8.B** (MWG, p. 240). The payoff against a mixed profile is the expectation of
the payoffs against the pure rival profiles drawn from it:
`u_k(τ, σ_{-i}) = ∑_{s} [∏_j σ_j(s_j)] u_k(τ, s_{-i})`, where the `i`-th coordinate of `σ` only
needs to sum to one (it integrates out). -/
theorem mixedPayoff_update_eq_expect (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (hσi : ∑ a, σ i a = 1) (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i τ) k =
      ∑ s : (i : I) → S i, (∏ j, σ j (s j)) * N.mixedPayoff (update (pureProfile s) i τ) k := by
  simp only [mixedPayoff_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  -- the weight of `t` among the pure rival profiles drawn from `σ`
  have key : ∑ s : (i : I) → S i,
      (∏ j, σ j (s j)) * ∏ j ∈ univ.erase i, pureProfile s j (t j) =
        ∏ j ∈ univ.erase i, σ j (t j) := by
    have hG : ∀ s : (i : I) → S i, (∏ j, σ j (s j)) * ∏ j ∈ univ.erase i, pureProfile s j (t j)
        = ∏ j, (σ j (s j) * if j = i then 1 else pureMixed (s j) (t j)) := by
      intro s
      rw [Finset.prod_mul_distrib, ← Finset.mul_prod_erase univ
        (fun j => if j = i then (1 : ℝ) else pureMixed (s j) (t j)) (mem_univ i)]
      simp only [ite_true, one_mul]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [ne_of_mem_erase hj, ↓reduceIte]
      rfl
    simp_rw [hG]
    rw [← Fintype.prod_sum (fun j x => σ j x * if j = i then 1 else pureMixed x (t j)),
      ← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [ite_true, mul_one, hσi, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [ne_of_mem_erase hj, ↓reduceIte, pureMixed, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  calc τ (t i) * ((∏ j ∈ univ.erase i, σ j (t j)) * N.payoff k t)
      = (∑ s : (i : I) → S i,
          (∏ j, σ j (s j)) * ∏ j ∈ univ.erase i, pureProfile s j (t j)) *
          (τ (t i) * N.payoff k t) := by rw [key]; ring
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring

/-- **Section 8.B** (MWG, p. 240). If `u_i(τ, s_{-i}) ≤ u_i(τ', s_{-i})` against every pure rival
profile, the same holds against every mixed profile. -/
theorem mixedPayoff_le_of_pure (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) (i : I) {τ τ' : S i → ℝ} (k : I)
    (h : ∀ s, N.mixedPayoff (update (pureProfile s) i τ) k ≤
      N.mixedPayoff (update (pureProfile s) i τ') k) :
    N.mixedPayoff (update σ i τ) k ≤ N.mixedPayoff (update σ i τ') k := by
  rw [mixedPayoff_update_eq_expect N σ i (hσ i).2, mixedPayoff_update_eq_expect N σ i (hσ i).2]
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (h s) (prod_mixed_nonneg (fun j a => (hσ j).1 a) s)

/-- **Section 8.B** (MWG, p. 240). Strict version: if `u_i(τ, s_{-i}) < u_i(τ', s_{-i})` against
every pure rival profile, the same holds against every mixed profile. -/
theorem mixedPayoff_lt_of_pure (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) (i : I) {τ τ' : S i → ℝ} (k : I)
    (h : ∀ s, N.mixedPayoff (update (pureProfile s) i τ) k <
      N.mixedPayoff (update (pureProfile s) i τ') k) :
    N.mixedPayoff (update σ i τ) k < N.mixedPayoff (update σ i τ') k := by
  rw [mixedPayoff_update_eq_expect N σ i (hσ i).2, mixedPayoff_update_eq_expect N σ i (hσ i).2]
  have hsum := sum_prod_mixed_eq_one (fun j => (hσ j).2)
  obtain ⟨s₀, -, hs₀⟩ : ∃ s ∈ (univ : Finset ((i : I) → S i)), 0 < ∏ j, σ j (s j) := by
    by_contra hno
    push Not at hno
    have : ∑ s : (i : I) → S i, ∏ j, σ j (s j) ≤ 0 := Finset.sum_nonpos hno
    linarith
  exact Finset.sum_lt_sum
    (fun s _ => mul_le_mul_of_nonneg_left (h s).le
      (prod_mixed_nonneg (fun j a => (hσ j).1 a) s))
    ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left (h s₀) hs₀⟩

omit [∀ i, DecidableEq (S i)] in
/-- The mixed payoff of player `k` against a mixed profile is bounded by `∑_s |u_k(s)|`. -/
theorem abs_mixedPayoff_le (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) (k : I) :
    |N.mixedPayoff σ k| ≤ ∑ s, |N.payoff k s| := by
  unfold NormalForm.mixedPayoff
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_mul, abs_of_nonneg (prod_mixed_nonneg (fun j a => (hσ j).1 a) s)]
  have h1 : ∏ j, σ j (s j) ≤ 1 := by
    rw [← sum_prod_mixed_eq_one (fun j => (hσ j).2)]
    exact Finset.single_le_sum (fun t _ => prod_mixed_nonneg (fun j a => (hσ j).1 a) t)
      (mem_univ s)
  exact (mul_le_of_le_one_left (abs_nonneg _) h1)

omit [∀ i, DecidableEq (S i)] in
/-- **Footnote 1** (MWG, p. 243), the computation behind it. If each player `j`'s strategy is
drawn independently from finitely many mixed strategies `τ_j(x)` with probabilities `π_j(x)`,
the expected payoff is the payoff of the compound profile `ρ_j = ∑_x π_j(x) τ_j(x)`. -/
theorem mixedPayoff_compound (N : NormalForm I S) {K : I → Type*} [∀ j, Fintype (K j)]
    (π : (j : I) → K j → ℝ) (τ : (j : I) → K j → S j → ℝ) (k : I) :
    ∑ x : (j : I) → K j, (∏ j, π j (x j)) * N.mixedPayoff (fun j => τ j (x j)) k =
      N.mixedPayoff (fun j => ∑ y, π j y • τ j y) k := by
  unfold NormalForm.mixedPayoff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Mixed strategies: domination, best responses and mixed Nash equilibrium

MWG, Section 8.B (pp. 240-242), Definition 8.C.1 and footnote 1 (pp. 242-243) and Section 8.D
(pp. 250-251).

Throughout, `N : NormalForm I S` has finitely many players and finite pure strategy sets, and
the game `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` is its mixed extension; mixed strategies are probability
vectors `σ_i : S_i → ℝ` and `u_i(σ)` is `N.mixedPayoff σ i`.

* **Definition 8.B.4**: `MixedStrictlyDominates`, `MixedStrictlyDominated`,
  `MixedStrictlyDominant`; the pure test of p. 240 (`mixedStrictlyDominates_iff_pure`).
* **Proposition 8.B.1** (`proposition_8_B_1`) and **Exercise 8.B.6** (`exercise_8_B_6`).
* **Exercise 8.B.7** (`exercise_8_B_7`): a strictly dominant strategy is pure.
* **Definition 8.C.1**: `IsBestResponse`, `NeverBestResponse`; a strictly dominated strategy is
  never a best response (`neverBestResponse_of_mixedStrictlyDominated`, p. 243).
* **Footnote 1** (p. 243): a strategy that is optimal against an independent probabilistic
  conjecture is a best response to the compound profile (`footnote_8_1`).
* **Definition 8.D.2** (`IsMixedNash`) and its identity with Definition 8.D.1 applied to the
  mixed extension (`isMixedNash_iff_mixedExtensionGame`).
* **Proposition 8.D.1** (`proposition_8_D_1`), the pure-deviation test that follows from it
  (`isMixedNash_iff_pure_deviations`) and **Corollary 8.D.1** (`corollary_8_D_1`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- **Definition 8.B.4** (MWG, p. 240). `τ'` strictly dominates `τ` for player `i` in
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`: `u_i(τ', σ_{-i}) > u_i(τ, σ_{-i})` for every profile `σ_{-i}`
of the rivals' mixed strategies (the `i`-th coordinate of `σ` is ignored). -/
def MixedStrictlyDominates (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) : Prop :=
  ∀ σ : (j : I) → S j → ℝ, IsMixedProfile σ →
    N.mixedPayoff (update σ i τ) i < N.mixedPayoff (update σ i τ') i

/-- **Definition 8.B.4** (MWG, p. 240). The mixed strategy `τ` is strictly dominated. -/
def MixedStrictlyDominated (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∃ τ', IsMixedStrategy τ' ∧ MixedStrictlyDominates N i τ' τ

/-- **Definition 8.B.4** (MWG, p. 240). `τ` is a strictly dominant strategy: it strictly dominates
every other mixed strategy. -/
def MixedStrictlyDominant (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  IsMixedStrategy τ ∧ ∀ τ', IsMixedStrategy τ' → τ' ≠ τ → MixedStrictlyDominates N i τ τ'

/-- **Section 8.B** (MWG, p. 240). To test whether `τ'` strictly dominates `τ` it suffices to
compare them against the pure strategies of the rivals:
`u_i(τ', σ_{-i}) > u_i(τ, σ_{-i})` for all `σ_{-i}` iff `u_i(τ', s_{-i}) > u_i(τ, s_{-i})` for all
`s_{-i}`. -/
theorem mixedStrictlyDominates_iff_pure (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) :
    MixedStrictlyDominates N i τ' τ ↔ ∀ s : (j : I) → S j,
      N.mixedPayoff (update (pureProfile s) i τ) i <
        N.mixedPayoff (update (pureProfile s) i τ') i :=
  ⟨fun h s => h _ (isMixedProfile_pureProfile s),
    fun h _ hσ => mixedPayoff_lt_of_pure N hσ i i h⟩

/-- **Proposition 8.B.1** (MWG, p. 241). Player `i`'s pure strategy `s_i` is strictly dominated
in `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` iff some mixed strategy `σ_i'` has
`u_i(σ_i', s_{-i}) > u_i(s_i, s_{-i})` for all `s_{-i}`. -/
theorem proposition_8_B_1 (N : NormalForm I S) (i : I) (a : S i) :
    MixedStrictlyDominated N i (pureMixed a) ↔ ∃ τ', IsMixedStrategy τ' ∧
      ∀ s : (j : I) → S j, N.payoff i (update s i a) <
        N.mixedPayoff (update (pureProfile s) i τ') i := by
  simp only [MixedStrictlyDominated, mixedStrictlyDominates_iff_pure,
    mixedPayoff_pureProfile_update]

/-- Moving the probability `c` of player `i`'s mixed strategy `τ` from the pure strategy `a`
to the mixed strategy `τ'` changes his payoff by `c (u_i(τ', σ_{-i}) - u_i(a, σ_{-i}))`. -/
theorem mixedPayoff_shift (N : NormalForm I S) (σ : (j : I) → S j → ℝ) (i : I)
    (τ τ' : S i → ℝ) (a : S i) (c : ℝ) (k : I) :
    N.mixedPayoff (update σ i (τ + c • (τ' - pureMixed a))) k =
      N.mixedPayoff (update σ i τ) k + c * (N.mixedPayoff (update σ i τ') k -
        N.mixedPayoff (update σ i (pureMixed a)) k) := by
  have h : τ' - pureMixed a = τ' + (-1 : ℝ) • pureMixed a := by
    funext b; simp [sub_eq_add_neg]
  rw [mixedPayoff_update_add_smul, h, mixedPayoff_update_add_smul]
  ring

omit [Fintype I] [DecidableEq I] in
/-- Moving the probability `c ≤ τ(a)` from the pure strategy `a` to a mixed strategy `τ'`
keeps `τ` a mixed strategy. -/
theorem isMixedStrategy_shift {i : I} {τ τ' : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hτ' : IsMixedStrategy τ') {a : S i} {c : ℝ} (hc0 : 0 ≤ c) (hca : c ≤ τ a) :
    IsMixedStrategy (τ + c • (τ' - pureMixed a)) := by
  refine ⟨fun b => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, pureMixed]
    split_ifs with hb
    · subst hb
      nlinarith [hτ'.1 b]
    · nlinarith [hτ.1 b, hτ'.1 b]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hτ.2, hτ'.2, (isMixedStrategy_pureMixed a).2]
    ring

/-- **Exercise 8.B.6** (MWG, p. 241). If the pure strategy `s_i` is strictly dominated in
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`, so is every mixed strategy that plays `s_i` with positive
probability. -/
theorem exercise_8_B_6 (N : NormalForm I S) (i : I) (a : S i)
    (ha : MixedStrictlyDominated N i (pureMixed a)) {τ : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hpos : 0 < τ a) : MixedStrictlyDominated N i τ := by
  obtain ⟨τ', hτ', hdom⟩ := ha
  refine ⟨τ + τ a • (τ' - pureMixed a), isMixedStrategy_shift hτ hτ' hpos.le le_rfl,
    fun σ hσ => ?_⟩
  rw [mixedPayoff_shift]
  have := hdom σ hσ
  nlinarith

/-- A mixed strategy is the average of its pure strategies: if all of them do at most `M`,
so does the mixed strategy. -/
theorem mixedPayoff_le_of_pure_le (N : NormalForm I S) (σ : (j : I) → S j → ℝ) (i : I)
    {τ : S i → ℝ} (hτ : IsMixedStrategy τ) {M : ℝ} (k : I)
    (h : ∀ a, N.mixedPayoff (update σ i (pureMixed a)) k ≤ M) :
    N.mixedPayoff (update σ i τ) k ≤ M := by
  rw [mixedPayoff_update_eq_sum_pure]
  calc ∑ a, τ a * N.mixedPayoff (update σ i (pureMixed a)) k ≤ ∑ a, τ a * M :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hτ.1 a)
    _ = M := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- The uniform mixed strategy. -/
noncomputable def uniformMixed (T : Type*) [Fintype T] : T → ℝ :=
  fun _ => 1 / (Fintype.card T : ℝ)

theorem isMixedStrategy_uniformMixed (T : Type*) [Fintype T] [Nonempty T] :
    IsMixedStrategy (uniformMixed T) := by
  refine ⟨fun _ => by unfold uniformMixed; positivity, ?_⟩
  simp only [uniformMixed, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_one_div_cancel this]

theorem uniformMixed_pos (T : Type*) [Fintype T] [Nonempty T] (t : T) :
    0 < uniformMixed T t := by
  unfold uniformMixed
  have : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  positivity

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- A mixed profile exists when every pure strategy set is nonempty. -/
theorem isMixedProfile_uniform [∀ i, Nonempty (S i)] :
    IsMixedProfile (fun i => uniformMixed (S i)) :=
  fun i => isMixedStrategy_uniformMixed (S i)

/-- **Exercise 8.B.7** (MWG, p. 262). A strictly dominant strategy in
`[I, {Δ(S_i)}, {u_i(·)}]` is a pure strategy (when every `S_j` is nonempty). -/
theorem exercise_8_B_7 [∀ i, Nonempty (S i)] (N : NormalForm I S) (i : I) {τ : S i → ℝ}
    (h : MixedStrictlyDominant N i τ) : ∃ a, τ = pureMixed a := by
  set σ : (j : I) → S j → ℝ := fun j => uniformMixed (S j)
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ
    (fun b => N.mixedPayoff (update σ i (pureMixed b)) i) univ_nonempty
  refine ⟨a, by_contra fun hne => ?_⟩
  have h1 := h.2 (pureMixed a) (isMixedStrategy_pureMixed a) (Ne.symm hne) σ
    isMixedProfile_uniform
  have h2 := mixedPayoff_le_of_pure_le N σ i h.1 i (fun b => hmax b (mem_univ b))
  linarith

/-- **Definition 8.C.1** (MWG, p. 242). `τ` is a best response for player `i` to the rivals'
strategies `σ_{-i}` (the `i`-th coordinate of `σ` is ignored): `u_i(τ, σ_{-i}) ≥ u_i(τ', σ_{-i})`
for all `τ' ∈ Δ(S_i)`. -/
def IsBestResponse (N : NormalForm I S) (i : I) (τ : S i → ℝ) (σ : (j : I) → S j → ℝ) :
    Prop :=
  IsMixedStrategy τ ∧ ∀ τ', IsMixedStrategy τ' →
    N.mixedPayoff (update σ i τ') i ≤ N.mixedPayoff (update σ i τ) i

/-- **Definition 8.C.1** (MWG, p. 242). `τ` is never a best response: there is no profile
`σ_{-i}` of mixed strategies of the rivals to which it is a best response. -/
def NeverBestResponse (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∀ σ : (j : I) → S j → ℝ, IsMixedProfile σ → ¬ IsBestResponse N i τ σ

omit [∀ i, DecidableEq (S i)] in
/-- Best responses depend only on the rivals' strategies. -/
theorem isBestResponse_update (N : NormalForm I S) (i : I) (τ : S i → ℝ)
    (σ : (j : I) → S j → ℝ) (x : S i → ℝ) :
    IsBestResponse N i τ (update σ i x) ↔ IsBestResponse N i τ σ := by
  simp only [IsBestResponse, update_idem]

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.C** (MWG, p. 243). A strictly dominated strategy is never a best response. -/
theorem neverBestResponse_of_mixedStrictlyDominated (N : NormalForm I S) (i : I)
    {τ : S i → ℝ} (h : MixedStrictlyDominated N i τ) : NeverBestResponse N i τ := by
  rintro σ hσ ⟨-, hbr⟩
  obtain ⟨τ', hτ', hdom⟩ := h
  exact absurd (hbr τ' hτ') (not_le.2 (hdom σ hσ))

/-- **Section 8.D** (MWG, pp. 250-251). A mixed strategy is a best response iff every pure
strategy it plays with positive probability is a best response among the pure strategies. -/
theorem isBestResponse_iff_support (N : NormalForm I S) (i : I) {τ : S i → ℝ}
    (hτ : IsMixedStrategy τ) (σ : (j : I) → S j → ℝ) :
    IsBestResponse N i τ σ ↔ ∀ a, 0 < τ a → ∀ b,
      N.mixedPayoff (update σ i (pureMixed b)) i ≤
        N.mixedPayoff (update σ i (pureMixed a)) i := by
  constructor
  · rintro ⟨-, hbr⟩ a ha b
    by_contra hlt
    push Not at hlt
    have := hbr _ (isMixedStrategy_shift hτ (isMixedStrategy_pureMixed b) ha.le le_rfl)
    rw [mixedPayoff_shift] at this
    nlinarith
  · intro h
    refine ⟨hτ, fun τ' hτ' => ?_⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < τ a := by
      by_contra hno
      push Not at hno
      have : ∑ a, τ a ≤ 0 := Finset.sum_nonpos fun a _ => hno a
      linarith [hτ.2]
    have hM := h a₀ ha₀
    refine (mixedPayoff_le_of_pure_le N σ i hτ' i hM).trans (le_of_eq ?_)
    rw [mixedPayoff_update_eq_sum_pure N σ i τ i]
    calc N.mixedPayoff (update σ i (pureMixed a₀)) i
        = ∑ a, τ a * N.mixedPayoff (update σ i (pureMixed a₀)) i := by
          rw [← Finset.sum_mul, hτ.2, one_mul]
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rcases (hτ.1 a).eq_or_lt with h0 | hpos
          · rw [← h0, zero_mul, zero_mul]
          · rw [le_antisymm (h a hpos a₀) (hM a)]

/-- A pure strategy maximizing the payoff against `σ_{-i}` is a best response. -/
theorem isBestResponse_pureMixed_of_max (N : NormalForm I S) (i : I) (σ : (j : I) → S j → ℝ)
    {a : S i} (ha : ∀ b, N.mixedPayoff (update σ i (pureMixed b)) i ≤
      N.mixedPayoff (update σ i (pureMixed a)) i) :
    IsBestResponse N i (pureMixed a) σ :=
  ⟨isMixedStrategy_pureMixed a, fun _ hτ' => mixedPayoff_le_of_pure_le N σ i hτ' i ha⟩

/-- Every player has a pure best response to any `σ_{-i}` (when `S_i` is nonempty). -/
theorem exists_pure_bestResponse [∀ i, Nonempty (S i)] (N : NormalForm I S) (i : I)
    (σ : (j : I) → S j → ℝ) : ∃ a, IsBestResponse N i (pureMixed a) σ := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ
    (fun b => N.mixedPayoff (update σ i (pureMixed b)) i) univ_nonempty
  exact ⟨a, isBestResponse_pureMixed_of_max N i σ fun b => hmax b (mem_univ b)⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Footnote 1** (MWG, p. 243). Suppose player `i` believes that each rival `j` plays the mixed
strategy `τ_j(x)` with probability `π_j(x)`, independently across rivals (player `i`'s own
coordinate of the conjecture is irrelevant). If `τ` is optimal against this probabilistic
conjecture, it is a best response to the compound profile `ρ_j = ∑_x π_j(x) τ_j(x)`, because the
expected payoffs coincide. -/
theorem footnote_8_1 (N : NormalForm I S) (i : I) {K : I → Type*} [∀ j, Fintype (K j)]
    (π : (j : I) → K j → ℝ) (hπ : ∑ x, π i x = 1) (τfam : (j : I) → K j → S j → ℝ)
    (τ : S i → ℝ) :
    ∑ x : (j : I) → K j, (∏ j, π j (x j)) *
        N.mixedPayoff (update (fun j => τfam j (x j)) i τ) i =
      N.mixedPayoff (update (fun j => ∑ y, π j y • τfam j y) i τ) i := by
  have h1 : ∀ x : (j : I) → K j, update (fun j => τfam j (x j)) i τ =
      fun j => update τfam i (fun _ => τ) j (x j) := by
    intro x
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  have h2 : update (fun j => ∑ y, π j y • τfam j y) i τ =
      fun j => ∑ y, π j y • update τfam i (fun _ => τ) j y := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      rw [← Finset.sum_smul (s := univ) (f := π j) (x := τ), hπ, one_smul]
    · simp [update_of_ne hj]
  simp_rw [h1, h2]
  exact mixedPayoff_compound N π (update τfam i (fun _ => τ)) i

/-- **Definition 8.D.2** (MWG, p. 250). A mixed strategy profile `σ` is a Nash equilibrium of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`: `u_i(σ_i, σ_{-i}) ≥ u_i(σ_i', σ_{-i})` for all `σ_i' ∈ Δ(S_i)`
and every `i`. -/
def IsMixedNash (N : NormalForm I S) (σ : (i : I) → S i → ℝ) : Prop :=
  IsMixedProfile σ ∧ ∀ i τ, IsMixedStrategy τ → N.mixedPayoff (update σ i τ) i ≤ N.mixedPayoff σ i

omit [∀ i, DecidableEq (S i)] in
/-- In a mixed Nash equilibrium every player's strategy is a best response to the others'. -/
theorem isMixedNash_iff_bestResponse (N : NormalForm I S) (σ : (i : I) → S i → ℝ) :
    IsMixedNash N σ ↔ IsMixedProfile σ ∧ ∀ i, IsBestResponse N i (σ i) σ := by
  simp only [IsMixedNash, IsBestResponse, update_eq_self]
  exact ⟨fun h => ⟨h.1, fun i => ⟨h.1 i, h.2 i⟩⟩, fun h => ⟨h.1, fun i => (h.2 i).2⟩⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Definition 8.D.2 = Definition 8.D.1 for the mixed extension** (MWG, p. 250). A mixed
profile is a Nash equilibrium in the sense of Definition 8.D.2 iff it is a Nash equilibrium
(Definition 8.D.1) of Chapter 7's mixed-extension game `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`. -/
theorem isMixedNash_iff_mixedExtensionGame (N : NormalForm I S) (σ : (i : I) → S i → ℝ)
    (hσ : IsMixedProfile σ) :
    IsMixedNash N σ ↔ IsNashEquilibrium N.mixedExtensionGame (fun i => ⟨σ i, hσ i⟩) := by
  have hval : ∀ i (τ : {τ : S i → ℝ // IsMixedStrategy τ}),
      (fun j => (update (fun j => (⟨σ j, hσ j⟩ : {τ : S j → ℝ // IsMixedStrategy τ})) i τ j).1)
        = update σ i τ.1 := by
    intro i τ
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  constructor
  · intro h i τ
    simp only [NormalForm.mixedExtensionGame]
    rw [hval]
    exact h.2 i τ.1 τ.2
  · intro h
    refine ⟨hσ, fun i τ hτ => ?_⟩
    have := h i ⟨τ, hτ⟩
    simp only [NormalForm.mixedExtensionGame] at this
    rwa [hval] at this

/-- **Proposition 8.D.1** (MWG, p. 250). Let `S_i⁺` be the pure strategies that player `i` plays
with positive probability under `σ`. Then `σ` is a Nash equilibrium of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` iff for every `i`:
(i) `u_i(s_i, σ_{-i}) = u_i(s_i', σ_{-i})` for all `s_i, s_i' ∈ S_i⁺`, and
(ii) `u_i(s_i, σ_{-i}) ≥ u_i(s_i', σ_{-i})` for all `s_i ∈ S_i⁺` and `s_i' ∉ S_i⁺`. -/
theorem proposition_8_D_1 (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) :
    IsMixedNash N σ ↔ ∀ i,
      (∀ a b, 0 < σ i a → 0 < σ i b → N.mixedPayoff (update σ i (pureMixed a)) i =
        N.mixedPayoff (update σ i (pureMixed b)) i) ∧
      (∀ a b, 0 < σ i a → ¬ 0 < σ i b → N.mixedPayoff (update σ i (pureMixed b)) i ≤
        N.mixedPayoff (update σ i (pureMixed a)) i) := by
  rw [isMixedNash_iff_bestResponse]
  simp only [hσ, true_and]
  refine forall_congr' fun i => ?_
  rw [isBestResponse_iff_support N i (hσ i)]
  constructor
  · intro h
    exact ⟨fun a b ha hb => le_antisymm (h b hb a) (h a ha b), fun a b ha _ => h a ha b⟩
  · rintro ⟨h1, h2⟩ a ha b
    by_cases hb : 0 < σ i b
    · exact (h1 a b ha hb).ge
    · exact h2 a b ha hb

/-- **Section 8.D** (MWG, p. 251). To test whether `σ` is a Nash equilibrium it suffices to
consider pure strategy deviations. -/
theorem isMixedNash_iff_pure_deviations (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) :
    IsMixedNash N σ ↔ ∀ i b, N.mixedPayoff (update σ i (pureMixed b)) i ≤ N.mixedPayoff σ i := by
  constructor
  · exact fun h i b => h.2 i _ (isMixedStrategy_pureMixed b)
  · intro h
    exact ⟨hσ, fun i τ hτ => mixedPayoff_le_of_pure_le N σ i hτ i (h i)⟩

/-- **Corollary 8.D.1** (MWG, p. 251). The pure profile `s` is a Nash equilibrium of
`Γ_N = [I, {S_i}, {u_i(·)}]` iff it is a (degenerate) mixed strategy Nash equilibrium of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`. -/
theorem corollary_8_D_1 (N : NormalForm I S) (s : (i : I) → S i) :
    IsNashEquilibrium N s ↔ IsMixedNash N (pureProfile s) := by
  rw [isMixedNash_iff_pure_deviations N (isMixedProfile_pureProfile s)]
  simp only [mixedPayoff_pureProfile_update, mixedPayoff_pureProfile]
  rfl

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Fixed point theorems

MWG, Mathematical Appendix, Section M.I, pp. 952-953.

* **Theorem M.I.1** (Brouwer, `theorem_M_I_1`): from LeanEconomics' `brouwer` (any
  finite-dimensional real normed space), stated for `A ⊆ ℝ^N`. The case `N = 1`, `A = [0, 1]`,
  by the intermediate value theorem as in the text (`brouwer_unitInterval_ivt`); continuity is
  indispensable (`figure_M_I_1b`); convexity is indispensable: a 90-degree clockwise rotation of
  the circle `‖x‖ = 1` in `ℝ²` is continuous with no fixed point (`circle_rotation_no_fixedPoint`,
  `circle_not_convex`).
* **Theorem M.I.2** (Kakutani, `theorem_M_I_2`): with MWG's upper hemicontinuity
  (Definition M.H.3, `UpperHemicontinuousMWG` from Chapter 3), derived from LeanEconomics'
  `kakutani` (closed-graph form, any real normed space; `kakutani_mwg`). Convex values are
  indispensable (`figure_M_I_2b`).
* **Theorem M.I.3** (Tarski, `theorem_M_I_3`): a nondecreasing self-map of `[0, 1]^N` has a fixed
  point; proved by the Knaster-Tarski theorem on the complete lattice `[0, 1]^N`. Continuity is
  not needed (`figure_M_I_3`).

Each theorem has a concrete instance of its hypotheses (`theorem_M_I_1_instance`,
`theorem_M_I_2_instance`, and `figure_M_I_3` for Theorem M.I.3).
-/

namespace MWG.SimultaneousMoveGames

open MWG.ClassicalDemand Filter Topology

/-- **Theorem M.I.1** (Brouwer's fixed point theorem; MWG, p. 952). If `A ⊆ ℝ^N` is nonempty,
compact and convex and `f : A → A` is continuous, then `f` has a fixed point `x = f(x)`. -/
theorem theorem_M_I_1 {N : ℕ} {A : Set (Fin N → ℝ)} (hne : A.Nonempty) (hA : IsCompact A)
    (hconv : Convex ℝ A) {f : (Fin N → ℝ) → (Fin N → ℝ)} (hf : ContinuousOn f A)
    (hmaps : Set.MapsTo f A A) : ∃ x ∈ A, x = f x := by
  obtain ⟨x, hx, hfx⟩ := LeanEconomics.FixedPoint.brouwer hA hconv hne hf hmaps
  exact ⟨x, hx, hfx.symm⟩

/-- The hypotheses of Theorem M.I.1 are satisfiable: halving maps the cube `[0, 1]^N` into
itself. -/
theorem theorem_M_I_1_instance (N : ℕ) :
    let A : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
    A.Nonempty ∧ IsCompact A ∧ Convex ℝ A ∧ ContinuousOn (fun x => (1 / 2 : ℝ) • x) A ∧
      Set.MapsTo (fun x : Fin N → ℝ => (1 / 2 : ℝ) • x) A A := by
  intro A
  refine ⟨⟨0, fun k _ => by simp⟩, isCompact_univ_pi fun _ => isCompact_Icc,
    convex_pi fun _ _ => convex_Icc 0 1, (continuous_const_smul _).continuousOn,
    fun x hx k _ => ?_⟩
  have := hx k (Set.mem_univ k)
  simp only [Pi.smul_apply, smul_eq_mul, Set.mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- **Section M.I** (MWG, pp. 952-953). For `N = 1` and `A = [0, 1]` Brouwer's theorem is a
consequence of the intermediate value theorem applied to `φ(x) = f(x) - x`, which has
`φ(0) ≥ 0` and `φ(1) ≤ 0`. -/
theorem brouwer_unitInterval_ivt {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hmaps : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) : ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = x := by
  have hφ : ContinuousOn (fun x => f x - x) (Set.Icc 0 1) := hf.sub continuousOn_id
  have h0 := hmaps (Set.left_mem_Icc.2 zero_le_one)
  have h1 := hmaps (Set.right_mem_Icc.2 zero_le_one)
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1 - 1) (f 0 - 0) := ⟨by linarith [h1.2], by linarith [h0.1]⟩
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' zero_le_one hφ hmem
  exact ⟨x, hx, by linarith [hx0]⟩

/-- **Figure M.I.1(b)** (MWG, p. 952). Continuity is indispensable: the function equal to `1`
on `[0, 1/2]` and to `0` on `(1/2, 1]` maps `[0, 1]` into itself and has no fixed point. -/
theorem figure_M_I_1b :
    let f : ℝ → ℝ := fun x => if x ≤ 1 / 2 then 1 else 0
    Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1) ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ x := by
  intro f
  refine ⟨fun x _ => ?_, fun x _ => ?_⟩
  · simp only [f]
    split_ifs <;> norm_num
  · simp only [f]
    split_ifs with h
    · intro h1; linarith
    · intro h0; rw [← h0] at h; norm_num at h

/-- The unit circle `S = {x ∈ ℝ² : ‖x‖ = 1}` (Euclidean norm, written out). -/
def unitCircle : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 = 1}

/-- The 90-degree clockwise rotation `(x₁, x₂) ↦ (x₂, -x₁)`. -/
def rotateClockwise (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 1, -x 0]

/-- **Section M.I** (MWG, p. 953). The 90-degree clockwise rotation is continuous, maps the
circle `S` into itself and has no fixed point on it. -/
theorem circle_rotation_no_fixedPoint :
    Continuous rotateClockwise ∧ Set.MapsTo rotateClockwise unitCircle unitCircle ∧
      ∀ x ∈ unitCircle, rotateClockwise x ≠ x := by
  refine ⟨?_, fun x hx => ?_, fun x hx hfx => ?_⟩
  · refine continuous_pi fun k => ?_
    fin_cases k
    · exact continuous_apply 1
    · exact (continuous_apply 0).neg
  · simp only [unitCircle, Set.mem_ofPred_eq, rotateClockwise, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx ⊢
    nlinarith [hx]
  · have h0 := congrFun hfx 0
    have h1 := congrFun hfx 1
    simp only [rotateClockwise, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1
    simp only [unitCircle, Set.mem_ofPred_eq] at hx
    have : x 0 = 0 := by linarith
    have : x 1 = 0 := by linarith
    simp_all

/-- **Section M.I** (MWG, p. 953). The circle is not convex (the midpoint of `(1, 0)` and
`(-1, 0)` is not on it), which is why the rotation escapes Brouwer's theorem. -/
theorem circle_not_convex : ¬ Convex ℝ unitCircle := by
  intro h
  have hp : (![1, 0] : Fin 2 → ℝ) ∈ unitCircle := by simp [unitCircle]
  have hq : (![-1, 0] : Fin 2 → ℝ) ∈ unitCircle := by simp [unitCircle]
  have hm := h hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp [unitCircle] at hm

/-- **Theorem M.I.2 in a real normed space**: MWG's Kakutani theorem, with upper
hemicontinuity in the sense of Definition M.H.3, derived from LeanEconomics' closed-graph
`kakutani`. -/
theorem kakutani_mwg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}
    (hne : A.Nonempty) (hA : IsCompact A) (hconv : Convex ℝ A) {f : E → Set E}
    (huhc : UpperHemicontinuousMWG A f) (hfA : CorrMapsInto A A f)
    (hfne : ∀ x ∈ A, (f x).Nonempty) (hfconv : ∀ x ∈ A, Convex ℝ (f x)) :
    ∃ x ∈ A, x ∈ f x := by
  refine LeanEconomics.FixedPoint.kakutani hA hconv hne hfne hfconv hfA ?_
  refine IsSeqClosed.isClosed fun p q hp hq => ?_
  have hx : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hq
  have hy : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hq
  have hqA : q.1 ∈ A := hA.isClosed.mem_of_tendsto hx (Eventually.of_forall fun n => (hp n).1)
  exact ⟨hqA, huhc.1 (fun n => (p n).1) (fun n => (p n).2) q.1 q.2 (fun n => (hp n).1) hqA
    (fun n => (hp n).2) hx hy⟩

/-- **Theorem M.I.2** (Kakutani's fixed point theorem; MWG, p. 953). If `A ⊆ ℝ^N` is nonempty,
compact and convex and `f : A → A` is an upper hemicontinuous correspondence with `f(x) ⊆ A`
nonempty and convex for every `x ∈ A`, then `f` has a fixed point `x ∈ f(x)`. -/
theorem theorem_M_I_2 {N : ℕ} {A : Set (Fin N → ℝ)} (hne : A.Nonempty) (hA : IsCompact A)
    (hconv : Convex ℝ A) {f : (Fin N → ℝ) → Set (Fin N → ℝ)}
    (huhc : UpperHemicontinuousMWG A f) (hfA : CorrMapsInto A A f)
    (hfne : ∀ x ∈ A, (f x).Nonempty) (hfconv : ∀ x ∈ A, Convex ℝ (f x)) :
    ∃ x ∈ A, x ∈ f x :=
  kakutani_mwg hne hA hconv huhc hfA hfne hfconv

/-- The hypotheses of Theorem M.I.2 are satisfiable: the constant correspondence `f(x) = A` on the
cube `A = [0, 1]^N`. -/
theorem theorem_M_I_2_instance (N : ℕ) :
    let A : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
    A.Nonempty ∧ IsCompact A ∧ Convex ℝ A ∧ UpperHemicontinuousMWG A (fun _ => A) ∧
      CorrMapsInto A A (fun _ => A) ∧ (∀ x ∈ A, ((fun _ => A) x).Nonempty) ∧
      ∀ x ∈ A, Convex ℝ ((fun _ => A) x) := by
  intro A
  have hAc : IsCompact A := isCompact_univ_pi fun _ => isCompact_Icc
  have hne : A.Nonempty := ⟨0, fun k _ => by simp⟩
  have hconv : Convex ℝ A := convex_pi fun _ _ => convex_Icc 0 1
  refine ⟨hne, hAc, hconv, ?_, fun _ _ => le_rfl, fun _ _ => hne, fun _ _ => hconv⟩
  refine (uhc_iff_hasClosedGraph_of_isCompact hAc (fun _ _ => le_rfl)).2 ?_
  intro xs ys x y _ _ hys _ hy
  exact hAc.isClosed.mem_of_tendsto hy (Eventually.of_forall hys)

/-- The correspondence of Figure M.I.2(b): `{1}` on `[0, 1/2)`, `{0, 1}` at `1/2`, `{0}` on
`(1/2, 1]`. -/
noncomputable def figM12b (x : ℝ) : Set ℝ :=
  if x < 1 / 2 then {1} else if x = 1 / 2 then {0, 1} else {0}

/-- **Figure M.I.2(b)** (MWG, p. 953). Convex values are indispensable: the correspondence
`figM12b` on `[0, 1]` is upper hemicontinuous with nonempty values in `[0, 1]`, its value at
`1/2` is not convex, and it has no fixed point. -/
theorem figure_M_I_2b :
    UpperHemicontinuousMWG (Set.Icc (0 : ℝ) 1) figM12b ∧
      CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) figM12b ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, (figM12b x).Nonempty) ∧ ¬ Convex ℝ (figM12b (1 / 2)) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, x ∉ figM12b x := by
  have hY : CorrMapsInto (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) figM12b := by
    intro x _ y hy
    unfold figM12b at hy
    split_ifs at hy
    · simp only [Set.mem_singleton_iff] at hy; subst hy; norm_num
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> norm_num
    · simp only [Set.mem_singleton_iff] at hy; subst hy; norm_num
  refine ⟨(uhc_iff_hasClosedGraph_of_isCompact isCompact_Icc hY).2 ?_, hY, ?_, ?_, ?_⟩
  · refine hasClosedGraph_of_isClosed (C := (Set.Iic (1 / 2) ×ˢ {1}) ∪ (Set.Ici (1 / 2) ×ˢ {0}))
      ((isClosed_Iic.prod isClosed_singleton).union (isClosed_Ici.prod isClosed_singleton))
      fun x _ y => ?_
    unfold figM12b
    split_ifs with h1 h2
    · simp only [Set.mem_singleton_iff, Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
      constructor
      · intro hy; exact Or.inl ⟨h1.le, hy⟩
      · rintro (⟨_, hy⟩ | ⟨hx, _⟩)
        · exact hy
        · linarith
    · subst h2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_prod,
        Set.mem_Iic, Set.mem_Ici, le_refl, true_and]
      tauto
    · simp only [Set.mem_singleton_iff, Set.mem_union, Set.mem_prod, Set.mem_Iic, Set.mem_Ici]
      constructor
      · intro hy; exact Or.inr ⟨by push Not at h1; exact h1, hy⟩
      · rintro (⟨hx, _⟩ | ⟨_, hy⟩)
        · exact absurd (le_antisymm hx (not_lt.1 h1)) h2
        · exact hy
  · intro x _
    unfold figM12b
    split_ifs <;> simp
  · intro h
    have h0 : (0 : ℝ) ∈ figM12b (1 / 2) := by simp [figM12b]
    have h1 : (1 : ℝ) ∈ figM12b (1 / 2) := by simp [figM12b]
    have := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp [figM12b] at this
  · intro x hx hfx
    unfold figM12b at hfx
    split_ifs at hfx with h1 h2
    · simp only [Set.mem_singleton_iff] at hfx; linarith
    · subst h2; norm_num at hfx
    · simp only [Set.mem_singleton_iff] at hfx; subst hfx; norm_num at h1

/-- **Theorem M.I.3** (Tarski's fixed point theorem; MWG, p. 953). If `f : [0, 1]^N → [0, 1]^N`
is nondecreasing (`f(x') ≥ f(x)` whenever `x' ≥ x`), then `f` has a fixed point. Continuity is
not assumed. -/
theorem theorem_M_I_3 {N : ℕ} {f : (Fin N → ℝ) → (Fin N → ℝ)}
    (hmaps : Set.MapsTo f (Set.pi Set.univ fun _ => Set.Icc 0 1)
      (Set.pi Set.univ fun _ => Set.Icc 0 1))
    (hmono : MonotoneOn f (Set.pi Set.univ fun _ => Set.Icc 0 1)) :
    ∃ x ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), x = f x := by
  have hfact : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  set C : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1 with hC
  have hval : ∀ y : Fin N → Set.Icc (0 : ℝ) 1, (fun k => (y k : ℝ)) ∈ C :=
    fun y k _ => (y k).2
  let g : (Fin N → Set.Icc (0 : ℝ) 1) →o (Fin N → Set.Icc (0 : ℝ) 1) :=
    { toFun := fun y k => ⟨f (fun k => (y k : ℝ)) k, hmaps (hval y) k (Set.mem_univ k)⟩
      monotone' := fun y y' hyy' k => by
        have : (fun k => (y k : ℝ)) ≤ fun k => (y' k : ℝ) := fun k => hyy' k
        exact hmono (hval y) (hval y') this k }
  refine ⟨fun k => (OrderHom.lfp g k : ℝ), hval _, ?_⟩
  funext k
  have h := congrFun (OrderHom.map_lfp g) k
  exact (congrArg Subtype.val h).symm

/-- **Figure M.I.3** (MWG, p. 953). A nondecreasing, discontinuous self-map of `[0, 1]` (`1/4`
below `1/2`, `3/4` from `1/2` on) satisfies the hypotheses of Theorem M.I.3 and has fixed
points, although it is not continuous. -/
theorem figure_M_I_3 :
    let f : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x _ => if x 0 < 1 / 2 then 1 / 4 else 3 / 4
    Set.MapsTo f (Set.pi Set.univ fun _ => Set.Icc 0 1) (Set.pi Set.univ fun _ => Set.Icc 0 1) ∧
      MonotoneOn f (Set.pi Set.univ fun _ => Set.Icc 0 1) ∧ ¬ Continuous f ∧
      f (fun _ => 1 / 4) = (fun _ => 1 / 4) := by
  intro f
  refine ⟨fun x _ k _ => ?_, fun x _ y _ hxy k => ?_, fun hc => ?_, ?_⟩
  · simp only [f]
    split_ifs <;> norm_num
  · simp only [f]
    have := hxy 0
    split_ifs with h1 h2 <;> norm_num
    linarith
  · have hc0 : Continuous fun t : ℝ => f (fun _ => t) 0 :=
      (continuous_apply 0).comp (hc.comp (continuous_pi fun _ => continuous_id))
    have hlim : Tendsto (fun t : ℝ => f (fun _ => t) 0) (𝓝[<] (1 / 2)) (𝓝 (1 / 4)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [f]
      rw [Set.mem_Iio] at ht
      simp only [ht, ↓reduceIte]
    have hval := hc0.continuousAt (x := 1 / 2)
    have h2 := tendsto_nhds_unique (hval.tendsto.mono_left nhdsWithin_le_nhds) hlim
    simp only [f, lt_irrefl, ↓reduceIte] at h2
    norm_num at h2
  · funext k
    simp only [f]
    norm_num

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Existence of Nash equilibrium

MWG, Section 8.D (pp. 252-253) and Appendix A of Chapter 8 (pp. 260-261).

The strategy sets are subsets `S_i` of real normed spaces `E_i` (MWG: Euclidean spaces
`ℝ^{M_i}`, which are instances; `proposition_8_D_3` is the Euclidean statement) and the
payoffs are functions `u_i` on profiles in `∏_i E_i`. The best-response correspondence
`b_i(s_{-i})` is `bestResp u S i s` (the `i`-th coordinate of `s` is ignored).

* **Lemma 8.AA.1** (`lemma_8_AA_1`): nonempty compact convex `S_i` and `u_i` continuous and
  quasiconcave in `s_i` make `b_i` nonempty, convex-valued and upper hemicontinuous
  (Definition M.H.3, `UpperHemicontinuousMWG`).
* **Proposition 8.D.3** (`nash_exists_of_quasiconcave`, `proposition_8_D_3`): the proof of
  p. 261, applying Kakutani's theorem (`kakutani_mwg`, Theorem M.I.2) to
  `b(s) = b_1(s_{-1}) × ⋯ × b_I(s_{-I})`. The equilibrium is a Nash equilibrium of the normal
  form `[I, {S_i}, {u_i}]` (`restrictGame`, `isNashEquilibrium_restrictGame`).
* **Proposition 8.D.2** (`proposition_8_D_2`): with finitely many pure strategies, a mixed
  strategy Nash equilibrium exists; as on p. 261 it is Proposition 8.D.3 for the game with
  strategy sets `Δ(S_i)` and the multilinear payoffs `u_i(σ)`. The strategy sets must be
  nonempty (`no_mixedProfile_of_isEmpty`, correction 2).
* **Footnote 5** (p. 253): a finite strategy set is convex only if it has at most one element
  (`footnote_8_5`), so a singleton is the exception to the printed claim (correction 3).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames MWG.ClassicalDemand Function Filter Topology

variable {I : Type*} [Fintype I] [DecidableEq I] {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- **Section 8.D** (MWG, p. 247), for strategy sets `S_i ⊆ E_i`: player `i`'s best responses
`b_i(s_{-i}) = {t ∈ S_i : u_i(t, s_{-i}) ≥ u_i(t', s_{-i}) for all t' ∈ S_i}`. -/
def bestResp (u : I → ((i : I) → E i) → ℝ) (S : (i : I) → Set (E i)) (i : I)
    (s : (i : I) → E i) : Set (E i) :=
  {t | t ∈ S i ∧ ∀ t' ∈ S i, u i (update s i t') ≤ u i (update s i t)}

omit [Fintype I] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] in
/-- Replacing a coordinate of a profile in `∏ S_j` by a point of `S_i` stays in `∏ S_j`. -/
theorem update_mem_pi {S : (i : I) → Set (E i)} {s : (i : I) → E i}
    (hs : s ∈ Set.pi Set.univ S) (i : I) {t : E i} (ht : t ∈ S i) :
    update s i t ∈ Set.pi Set.univ S := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using ht
  · simpa [update_of_ne hj] using hs j (Set.mem_univ j)

/-- **Lemma 8.AA.1** (MWG, p. 260). If the sets `S_j` are nonempty, `S_i` is compact and
convex, and `u_i` is continuous on `S = S_1 × ⋯ × S_I` and quasiconcave in `s_i`, then player
`i`'s best-response correspondence is nonempty, convex-valued and upper hemicontinuous. -/
theorem lemma_8_AA_1 {u : I → ((i : I) → E i) → ℝ} {S : (i : I) → Set (E i)} (i : I)
    (hSne : ∀ j, (S j).Nonempty) (hcpt : IsCompact (S i)) (_hconv : Convex ℝ (S i))
    (hcont : ContinuousOn (u i) (Set.pi Set.univ S))
    (hqc : ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t)) :
    (∀ s ∈ Set.pi Set.univ S, (bestResp u S i s).Nonempty) ∧
      (∀ s ∈ Set.pi Set.univ S, Convex ℝ (bestResp u S i s)) ∧
      UpperHemicontinuousMWG (Set.pi Set.univ S) (bestResp u S i) := by
  have hcomp : ∀ s ∈ Set.pi Set.univ S, ContinuousOn (fun t => u i (update s i t)) (S i) :=
    fun s hs => hcont.comp (continuous_const.update i continuous_id).continuousOn
      fun t ht => update_mem_pi hs i ht
  refine ⟨fun s hs => ?_, fun s hs => ?_, ?_, ?_⟩
  · -- the set of maximizers of a continuous function on a compact set is nonempty
    obtain ⟨t, ht, hmax⟩ := hcpt.exists_isMaxOn (hSne i) (hcomp s hs)
    exact ⟨t, ht, fun t' ht' => hmax ht'⟩
  · -- the maximizers of a quasiconcave function on a convex set form an upper level set
    obtain ⟨t₀, ht₀, hmax⟩ := hcpt.exists_isMaxOn (hSne i) (hcomp s hs)
    have heq : bestResp u S i s = {t | t ∈ S i ∧ u i (update s i t₀) ≤ u i (update s i t)} := by
      ext t
      constructor
      · rintro ⟨ht, hbr⟩; exact ⟨ht, hbr t₀ ht₀⟩
      · rintro ⟨ht, hge⟩; exact ⟨ht, fun t' ht' => (hmax ht').trans hge⟩
    rw [heq]
    exact hqc s hs _
  · -- closed graph: pass to the limit in `u_i(sⁿ_i, sⁿ_{-i}) ≥ u_i(s'_i, sⁿ_{-i})`
    intro xs ys x y hxs hx hys hxl hyl
    have hyS : y ∈ S i :=
      hcpt.isClosed.mem_of_tendsto hyl (Eventually.of_forall fun n => (hys n).1)
    refine ⟨hyS, fun t' ht' => ?_⟩
    have h1 : Tendsto (fun n => update (xs n) i t') atTop (𝓝 (update x i t')) :=
      ((continuous_id.update i continuous_const).tendsto x).comp hxl
    have h2 : Tendsto (fun n => update (xs n) i (ys n)) atTop (𝓝 (update x i y)) :=
      ((continuous_fst.update i continuous_snd).tendsto (x, y)).comp (hxl.prodMk_nhds hyl)
    have hc1 := ((hcont _ (update_mem_pi hx i ht')).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n => update_mem_pi (hxs n) i ht'⟩))
    have hc2 := ((hcont _ (update_mem_pi hx i hyS)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall fun n =>
        update_mem_pi (hxs n) i (hys n).1⟩))
    exact le_of_tendsto_of_tendsto' hc1 hc2 fun n => (hys n).2 t' ht'
  · -- images lie in the compact, hence bounded, set `S_i`
    intro B _ _
    exact hcpt.isBounded.subset (Set.iUnion₂_subset fun x _ t ht => ht.1)

omit [Fintype I] in
/-- **Proposition 8.D.3 in real normed spaces** (MWG, pp. 253 and 261). If every `S_i` is a
nonempty, convex and compact subset of a real normed space and every `u_i` is continuous on
`S_1 × ⋯ × S_I` and quasiconcave in `s_i`, there is a profile `s ∈ S` with
`u_i(s_i, s_{-i}) ≥ u_i(s_i', s_{-i})` for all `s_i' ∈ S_i` and all `i`. -/
theorem nash_exists_of_quasiconcave [Finite I] {u : I → ((i : I) → E i) → ℝ}
    {S : (i : I) → Set (E i)}
    (hSne : ∀ i, (S i).Nonempty) (hcpt : ∀ i, IsCompact (S i)) (hconv : ∀ i, Convex ℝ (S i))
    (hcont : ∀ i, ContinuousOn (u i) (Set.pi Set.univ S))
    (hqc : ∀ i, ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t)) :
    ∃ s ∈ Set.pi Set.univ S, ∀ i, ∀ t ∈ S i, u i (update s i t) ≤ u i s := by
  have := Fintype.ofFinite I
  have hL := fun i => lemma_8_AA_1 i hSne (hcpt i) (hconv i) (hcont i) (hqc i)
  set K : Set ((i : I) → E i) := Set.pi Set.univ S
  set F : ((i : I) → E i) → Set ((i : I) → E i) :=
    fun s => Set.pi Set.univ fun i => bestResp u S i s
  have hKc : IsCompact K := isCompact_univ_pi hcpt
  have hFK : CorrMapsInto K K F := fun s _ t ht i _ => (ht i (Set.mem_univ i)).1
  have huhc : UpperHemicontinuousMWG K F := by
    refine ⟨fun xs ys x y hxs hx hys hxl hyl i _ => ?_, fun B hBK _ => ?_⟩
    · exact (hL i).2.2.1 xs (fun n => ys n i) x (y i) hxs hx (fun n => hys n i (Set.mem_univ i))
        hxl ((continuous_apply i).tendsto y |>.comp hyl)
    · exact hKc.isBounded.subset (Set.iUnion₂_subset fun x hx => hFK x (hBK hx))
  obtain ⟨s, hs, hsF⟩ := kakutani_mwg (Set.univ_pi_nonempty_iff.2 hSne) hKc
    (convex_pi fun i _ => hconv i) huhc hFK
    (fun s hs => Set.univ_pi_nonempty_iff.2 fun i => (hL i).1 s hs)
    (fun s hs => convex_pi fun i _ => (hL i).2.1 s hs)
  refine ⟨s, hs, fun i t ht => ?_⟩
  have := (hsF i (Set.mem_univ i)).2 t ht
  rwa [update_eq_self] at this

omit [Fintype I] in
/-- **Proposition 8.D.3** (MWG, p. 253). A Nash equilibrium exists in `Γ_N = [I, {S_i}, {u_i}]`
if for every `i`, (i) `S_i` is a nonempty, convex and compact subset of a Euclidean space
`ℝ^{M_i}`, and (ii) `u_i(s_1, …, s_I)` is continuous in `(s_1, …, s_I)` and quasiconcave in
`s_i`. -/
theorem proposition_8_D_3 [Finite I] {M : I → ℕ} {u : I → ((i : I) → Fin (M i) → ℝ) → ℝ}
    {S : (i : I) → Set (Fin (M i) → ℝ)} (hSne : ∀ i, (S i).Nonempty)
    (hconv : ∀ i, Convex ℝ (S i)) (hcpt : ∀ i, IsCompact (S i))
    (hcont : ∀ i, ContinuousOn (u i) (Set.pi Set.univ S))
    (hqc : ∀ i, ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t)) :
    ∃ s ∈ Set.pi Set.univ S, ∀ i, ∀ t ∈ S i, u i (update s i t) ≤ u i s :=
  nash_exists_of_quasiconcave hSne hcpt hconv hcont hqc

/-- The normal form `[I, {S_i}, {u_i(·)}]` whose strategy sets are the subsets `S_i ⊆ E_i`. -/
def restrictGame (u : I → ((i : I) → E i) → ℝ) (S : (i : I) → Set (E i)) :
    NormalForm I (fun i => S i) where
  payoff i s := u i fun j => (s j : E j)

omit [Fintype I] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] in
/-- A profile as in Proposition 8.D.3 is a Nash equilibrium (Definition 8.D.1) of the normal form
`[I, {S_i}, {u_i(·)}]`. -/
theorem isNashEquilibrium_restrictGame {u : I → ((i : I) → E i) → ℝ}
    {S : (i : I) → Set (E i)} {s : (i : I) → E i} (hs : s ∈ Set.pi Set.univ S)
    (hne : ∀ i, ∀ t ∈ S i, u i (update s i t) ≤ u i s) :
    IsNashEquilibrium (restrictGame u S) (fun i => ⟨s i, hs i (Set.mem_univ i)⟩) := by
  intro i t
  have hval : (fun j => ((update (fun i => (⟨s i, hs i (Set.mem_univ i)⟩ : S i)) i t j : S j) :
      E j)) = update s i (t : E i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  simp only [restrictGame]
  rw [hval]
  exact hne i t t.2

/-- The hypotheses of Proposition 8.D.3 are satisfiable: one player choosing `x ∈ [0, 1]` with
payoff `x`. -/
theorem proposition_8_D_3_instance :
    let S : (i : Unit) → Set (Fin 1 → ℝ) := fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
    let u : Unit → ((i : Unit) → Fin 1 → ℝ) → ℝ := fun _ s => s () 0
    (∀ i, (S i).Nonempty) ∧ (∀ i, Convex ℝ (S i)) ∧ (∀ i, IsCompact (S i)) ∧
      (∀ i, ContinuousOn (u i) (Set.pi Set.univ S)) ∧
      ∀ i, ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t) := by
  intro S u
  refine ⟨fun _ => ⟨0, fun k _ => by simp⟩, fun _ => convex_pi fun _ _ => convex_Icc 0 1,
    fun _ => isCompact_univ_pi fun _ => isCompact_Icc,
    fun _ => ((continuous_apply 0).comp (continuous_apply ())).continuousOn,
    fun i s _ => ?_⟩
  have h : (fun t : Fin 1 → ℝ => u i (update s i t)) = fun t => t 0 := by
    funext t
    simp [u]
  rw [h]
  exact (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).concaveOn
    (convex_pi fun _ _ => convex_Icc 0 1) |>.quasiconcaveOn

/-! ### Proposition 8.D.2 -/

variable {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

omit [∀ i, DecidableEq (S i)] in
/-- The mixed payoff is continuous in the mixed profile. -/
theorem continuous_mixedPayoff (N : NormalForm I S) (k : I) :
    Continuous fun σ : (i : I) → S i → ℝ => N.mixedPayoff σ k := by
  unfold NormalForm.mixedPayoff
  refine continuous_finsetSum _ fun s _ => ?_
  refine Continuous.mul (continuous_finsetProd _ fun j _ => ?_) continuous_const
  exact (continuous_apply (s j)).comp (continuous_apply j)

omit [∀ i, DecidableEq (S i)] in
/-- A player's mixed payoff is affine, hence concave, in his own mixed strategy. -/
theorem concaveOn_mixedPayoff_update (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    {K : Set (S i → ℝ)} (hK : Convex ℝ K) :
    ConcaveOn ℝ K fun τ => N.mixedPayoff (update σ i τ) i := by
  refine ⟨hK, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [mixedPayoff_update, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The set `Δ(T)` of mixed strategies is convex. -/
theorem convex_mixedExtension (T : Type*) [Fintype T] : Convex ℝ (mixedExtension T) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun t => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.1 t, hy.1 t]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The set `Δ(T)` of mixed strategies is compact. -/
theorem isCompact_mixedExtension (T : Type*) [Fintype T] : IsCompact (mixedExtension T) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : T => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hcube.of_isClosed_subset ?_ fun σ hσ t _ => ⟨hσ.1 t, ?_⟩
  · have h1 : IsClosed {σ : T → ℝ | ∀ t, 0 ≤ σ t} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t)
    have h2 : IsClosed {σ : T → ℝ | ∑ t, σ t = 1} :=
      isClosed_eq (continuous_finsetSum _ fun t _ => continuous_apply t) continuous_const
    exact h1.inter h2
  · rw [← hσ.2]
    exact Finset.single_le_sum (fun t _ => hσ.1 t) (Finset.mem_univ t)

omit [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.D.2** (MWG, pp. 252 and 261). Every game `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` in
which the sets `S_1, …, S_I` are finite (and nonempty) has a mixed strategy Nash equilibrium.
As in the text, this is Proposition 8.D.3 for strategy sets `Δ(S_i)` and the payoffs
`u_i(σ) = ∑_s [∏_k σ_k(s_k)] u_i(s)`. -/
theorem proposition_8_D_2 [∀ i, Nonempty (S i)] (N : NormalForm I S) :
    ∃ σ, IsMixedNash N σ := by
  obtain ⟨σ, hσ, hne⟩ := nash_exists_of_quasiconcave (E := fun i => S i → ℝ)
    (u := fun i σ => N.mixedPayoff σ i) (S := fun i => mixedExtension (S i))
    (fun i => ⟨_, isMixedStrategy_uniformMixed (S i)⟩)
    (fun i => isCompact_mixedExtension (S i)) (fun i => convex_mixedExtension (S i))
    (fun i => (continuous_mixedPayoff N i).continuousOn)
    (fun i σ _ => (concaveOn_mixedPayoff_update N σ i (convex_mixedExtension (S i))).quasiconcaveOn)
  exact ⟨σ, fun i => hσ i (Set.mem_univ i), fun i τ hτ => hne i τ hτ⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.D.2 needs nonempty strategy sets** (correction 2). If some `S_i` is empty there
is no mixed strategy for player `i`, so no mixed profile and no mixed Nash equilibrium. -/
theorem no_mixedProfile_of_isEmpty [∀ i, Fintype (S i)] (i : I) [IsEmpty (S i)]
    (σ : (i : I) → S i → ℝ) : ¬ IsMixedProfile σ := by
  intro h
  have := (h i).2
  simp at this

/-- **Footnote 5** (MWG, p. 253). A finite convex subset of a real vector space has at most one
element. -/
theorem footnote_8_5 {V : Type*} [AddCommGroup V] [Module ℝ V] {T : Set V} (hfin : T.Finite)
    (hconv : Convex ℝ T) : T.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hsub : segment ℝ x y ⊆ T := hconv.segment_subset hx hy
  rw [segment_eq_image_lineMap] at hsub
  have hinf : (AffineMap.lineMap x y '' Set.Icc (0 : ℝ) 1).Infinite :=
    (Set.Icc_infinite zero_lt_one).image (AffineMap.lineMap_injective ℝ hxy).injOn
  exact hinf (hfin.subset hsub)

/-- **Footnote 5 as printed is false for one-point sets** (correction 3): a singleton strategy set
is finite and convex. -/
theorem footnote_8_5_singleton {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    ({v} : Set V).Finite ∧ Convex ℝ ({v} : Set V) :=
  ⟨Set.finite_singleton v, convex_singleton v⟩

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Rationalizable strategies

MWG, Section 8.C, pp. 242-245, and the remarks on rationalizability in Section 8.D (p. 247).

Strategy sets are sets `T_i ⊆ Δ(S_i)` of mixed strategies. A strategy survives one round if it
is a best response (Definition 8.C.1, over all of `Δ(S_i)`) to some profile of the rivals'
remaining strategies.

* `ratStep`, `ratIter`: removing every strategy that is never a best response, once and `n`
  times; **Definition 8.C.2**: `Rationalizable N i τ` holds when `τ` survives every round.
* `NBRStep`: one step of a deletion process that removes *some* strategies that are never a
  best response to the remaining strategies; `NBRTerminal`: nothing remaining can be removed.
* **Exercise 8.C.2** (`exercise_8_C_2`): every complete deletion process ends at the set of
  rationalizable strategies (`nbrTerminal_eq_rationalizable`), so the order of removal does not
  matter (no finiteness is needed).
* **Section 8.C** (p. 243): the rationalizable strategies are no more than the strategies that
  survive iterated strict dominance: they put no weight on a pure strategy deleted by any
  process of iterated deletion of (pure) strategies that are strictly dominated by mixed
  strategies of the remaining ones (`rationalizable_support_subset`; `MSDStep` generalizes the
  pure process `SDStep` of Section 8.B, `sdStep_msdStep`).
* **Section 8.D** (p. 247): every strategy in a Nash equilibrium is rationalizable
  (`rationalizable_of_isMixedNash`); with Proposition 8.D.2, every player has a rationalizable
  strategy (footnote 3, `footnote_8_3`).
* **Exercise 8.C.1** (`exercise_8_C_1`): if iterated strict dominance leaves a unique profile,
  that profile (played with certainty) is exactly what survives the removal of strategies that
  are never a best response.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- `τ` is a best response to some profile of the rivals' strategies remaining in `T`. -/
def BRToSome (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) (i : I) (τ : S i → ℝ) :
    Prop :=
  ∃ σ : (j : I) → S j → ℝ, IsMixedProfile σ ∧ (∀ j, j ≠ i → σ j ∈ T j) ∧ IsBestResponse N i τ σ

/-- One round of removal of the strategies that are never a best response to the remaining
strategies. -/
def ratStep (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) : (i : I) → Set (S i → ℝ) :=
  fun i => {τ | τ ∈ T i ∧ BRToSome N T i τ}

/-- The strategies surviving `n` rounds, starting from `Δ(S_i)`. -/
def ratIter (N : NormalForm I S) : ℕ → (i : I) → Set (S i → ℝ)
  | 0 => fun i => mixedExtension (S i)
  | n + 1 => ratStep N (ratIter N n)

/-- **Definition 8.C.2** (MWG, p. 243). The rationalizable strategies of player `i` are the
strategies in `Δ(S_i)` that survive the iterated removal of strategies that are never a best
response. -/
def Rationalizable (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∀ n, τ ∈ ratIter N n i

omit [∀ i, DecidableEq (S i)] in
theorem BRToSome.mono {N : NormalForm I S} {T T' : (i : I) → Set (S i → ℝ)}
    (hTT' : ∀ j, T j ⊆ T' j) {i : I} {τ : S i → ℝ} (h : BRToSome N T i τ) :
    BRToSome N T' i τ := by
  obtain ⟨σ, hσ, hT, hbr⟩ := h
  exact ⟨σ, hσ, fun j hj => hTT' j (hT j hj), hbr⟩

omit [∀ i, DecidableEq (S i)] in
/-- A set of strategies each of which is a best response to the remaining strategies is never
reduced: it lies in every round, hence consists of rationalizable strategies. -/
theorem subset_ratIter_of_bestResponseSet {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (hTΔ : ∀ i, T i ⊆ mixedExtension (S i)) (hT : ∀ i, ∀ τ ∈ T i, BRToSome N T i τ) :
    ∀ n i, T i ⊆ ratIter N n i := by
  intro n
  induction n with
  | zero => exact hTΔ
  | succ n ih => exact fun i τ hτ => ⟨ih i hτ, (hT i τ hτ).mono ih⟩

omit [∀ i, DecidableEq (S i)] in
/-- Strategies in a best-response set are rationalizable. -/
theorem rationalizable_of_bestResponseSet {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (hTΔ : ∀ i, T i ⊆ mixedExtension (S i)) (hT : ∀ i, ∀ τ ∈ T i, BRToSome N T i τ) {i : I}
    {τ : S i → ℝ} (hτ : τ ∈ T i) : Rationalizable N i τ :=
  fun n => subset_ratIter_of_bestResponseSet hTΔ hT n i hτ

omit [∀ i, DecidableEq (S i)] in
/-- Rationalizable strategies are mixed strategies. -/
theorem Rationalizable.isMixedStrategy {N : NormalForm I S} {i : I} {τ : S i → ℝ}
    (h : Rationalizable N i τ) : IsMixedStrategy τ :=
  h 0

/-- A deletion step: `T'` keeps part of each `T_i`, and every removed strategy is never a best
response to the strategies remaining in `T`. -/
def NBRStep (N : NormalForm I S) (T T' : (i : I) → Set (S i → ℝ)) : Prop :=
  (∀ i, T' i ⊆ T i) ∧ ∀ i, ∀ τ ∈ T i, τ ∉ T' i → ¬ BRToSome N T i τ

/-- A deletion process is complete when every remaining strategy is a best response to some
remaining strategies. -/
def NBRTerminal (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) : Prop :=
  ∀ i, ∀ τ ∈ T i, BRToSome N T i τ

omit [∀ i, DecidableEq (S i)] in
/-- Along any deletion process from `Δ`, some round of the maximal process lies inside the
current sets. -/
theorem exists_ratIter_subset_of_chain {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (h : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T) :
    ∃ n, ∀ i, ratIter N n i ⊆ T i := by
  induction h with
  | refl => exact ⟨0, fun _ => le_rfl⟩
  | @tail P Q _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun i τ hτ => ?_⟩
    by_contra hτQ
    exact hstep.2 i τ (hn i hτ.1) hτQ (hτ.2.mono hn)

omit [∀ i, DecidableEq (S i)] in
/-- Deletion processes stay inside `Δ`. -/
theorem nbrChain_subset {N : NormalForm I S} {P T : (i : I) → Set (S i → ℝ)}
    (h : Relation.ReflTransGen (NBRStep N) P T) (i : I) : T i ⊆ P i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (hstep.1 i).trans ih

omit [∀ i, DecidableEq (S i)] in
/-- Every complete deletion process of strategies that are never a best response ends at the set
of rationalizable strategies. -/
theorem nbrTerminal_eq_rationalizable {N : NormalForm I S} {T : (i : I) → Set (S i → ℝ)}
    (h : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T)
    (ht : NBRTerminal N T) (i : I) : T i = {τ | Rationalizable N i τ} := by
  ext τ
  constructor
  · exact fun hτ => rationalizable_of_bestResponseSet (nbrChain_subset h) ht hτ
  · intro hτ
    obtain ⟨n, hn⟩ := exists_ratIter_subset_of_chain h
    exact hn i (hτ n)

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.C.2** (MWG, p. 262). The order of removal does not matter for the set of
strategies that survives a process of iterated deletion of strategies that are never a best
response. -/
theorem exercise_8_C_2 {N : NormalForm I S} {T₁ T₂ : (i : I) → Set (S i → ℝ)}
    (h₁ : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T₁)
    (ht₁ : NBRTerminal N T₁)
    (h₂ : Relation.ReflTransGen (NBRStep N) (fun i => mixedExtension (S i)) T₂)
    (ht₂ : NBRTerminal N T₂) : T₁ = T₂ :=
  funext fun i => (nbrTerminal_eq_rationalizable h₁ ht₁ i).trans
    (nbrTerminal_eq_rationalizable h₂ ht₂ i).symm

omit [∀ i, DecidableEq (S i)] in
/-- The maximal process (removing every strategy that is never a best response at each round)
is a deletion process. -/
theorem nbrStep_ratStep (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) :
    NBRStep N T (ratStep N T) :=
  ⟨fun _ _ hτ => hτ.1, fun _ _ hτ hτ' hbr => hτ' ⟨hτ, hbr⟩⟩

/-! ### Rationalizability and iterated strict dominance -/

/-- One step of iterated deletion of strictly dominated pure strategies when randomization is
allowed (Section 8.B, p. 242: the test of Proposition 8.B.1 "applied at each stage using the
remaining set of pure strategies"): every removed pure strategy `a ∈ P_i` is strictly worse,
against every remaining rival profile, than some mixed strategy over `P_i`. -/
def MSDStep (N : NormalForm I S) (P Q : (i : I) → Set (S i)) : Prop :=
  (∀ i, Q i ⊆ P i) ∧ ∀ i, ∀ a ∈ P i, a ∉ Q i → ∃ τ' : S i → ℝ, IsMixedStrategy τ' ∧
    (∀ b, 0 < τ' b → b ∈ P i) ∧ ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ P j) →
      N.payoff i (update r i a) < N.mixedPayoff (update (pureProfile r) i τ') i

/-- A step of the pure process of Section 8.B is a step of the mixed one. -/
theorem sdStep_msdStep {N : NormalForm I S} {P Q : (i : I) → Set (S i)}
    (h : SDStep N P Q) : MSDStep N P Q := by
  refine ⟨h.1, fun i a ha haQ => ?_⟩
  obtain ⟨a', ha', hdom⟩ := h.2 i a ha haQ
  refine ⟨pureMixed a', isMixedStrategy_pureMixed a', fun b hb => ?_, fun r hr => ?_⟩
  · have : b = a' := by
      by_contra hne
      simp [pureMixed, hne] at hb
    rwa [this]
  · rw [mixedPayoff_pureProfile_update]
    exact hdom r hr

/-- Against a mixed profile whose rivals only play remaining pure strategies, a pure strategy
deleted in an `MSDStep` does strictly worse than its dominator. -/
theorem msd_dominated_lt {N : NormalForm I S} {P : (i : I) → Set (S i)} {i : I} {a : S i}
    {τ' : S i → ℝ}
    (hdom : ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ P j) →
      N.payoff i (update r i a) < N.mixedPayoff (update (pureProfile r) i τ') i)
    {σ : (j : I) → S j → ℝ} (hσ : IsMixedProfile σ)
    (hsupp : ∀ j, j ≠ i → ∀ b, 0 < σ j b → b ∈ P j) :
    N.mixedPayoff (update σ i (pureMixed a)) i < N.mixedPayoff (update σ i τ') i := by
  rw [mixedPayoff_update_eq_expect N σ i (hσ i).2, mixedPayoff_update_eq_expect N σ i (hσ i).2]
  have hw : ∀ s : (i : I) → S i, 0 ≤ ∏ j, σ j (s j) :=
    prod_mixed_nonneg fun j a => (hσ j).1 a
  have hsum := sum_prod_mixed_eq_one (fun j => (hσ j).2)
  obtain ⟨s₀, -, hs₀⟩ : ∃ s ∈ (univ : Finset ((i : I) → S i)), 0 < ∏ j, σ j (s j) := by
    by_contra hno
    push Not at hno
    have : ∑ s : (i : I) → S i, ∏ j, σ j (s j) ≤ 0 := Finset.sum_nonpos hno
    linarith
  have hlt : ∀ s, 0 < ∏ j, σ j (s j) →
      N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i <
        N.mixedPayoff (update (pureProfile s) i τ') i := by
    intro s hs
    rw [mixedPayoff_pureProfile_update]
    refine hdom s fun j hj => hsupp j hj (s j) ?_
    have hne : ∏ j, σ j (s j) ≠ 0 := hs.ne'
    rw [Finset.prod_ne_zero_iff] at hne
    exact ((hσ j).1 _).lt_of_ne (hne j (mem_univ j)).symm
  refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left
    (hlt s₀ hs₀) hs₀⟩
  rcases (hw s).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hlt s hpos).le (hw s)

/-- **Section 8.C** (MWG, p. 243). The set of rationalizable strategies is no larger than the set
surviving iterated removal of strictly dominated strategies: along any deletion process of
strictly dominated pure strategies (dominated by mixtures of remaining ones), some round of the
removal of never-best responses only keeps strategies supported on the remaining pure
strategies. -/
theorem exists_ratIter_support_subset {N : NormalForm I S} {Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) :
    ∃ n, ∀ i, ∀ τ ∈ ratIter N n i, ∀ a, 0 < τ a → a ∈ Q i := by
  induction h with
  | refl => exact ⟨0, fun _ _ _ _ _ => Set.mem_univ _⟩
  | @tail P Q _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun i τ hτ a ha => ?_⟩
    have haP : a ∈ P i := hn i τ hτ.1 a ha
    by_contra haQ
    obtain ⟨τ', hτ', -, hdom⟩ := hstep.2 i a haP haQ
    obtain ⟨σ, hσ, hσT, hbr⟩ := hτ.2
    have hlt := msd_dominated_lt hdom hσ fun j hj b hb => hn j (σ j) (hσT j hj) b hb
    have hsupp := (isBestResponse_iff_support N i hbr.1 σ).1 hbr a ha
    have h1 := mixedPayoff_le_of_pure_le N σ i hτ' i hsupp
    linarith

/-- **Section 8.C** (MWG, p. 243). A rationalizable strategy puts no weight on any pure strategy
removed by iterated strict dominance. -/
theorem rationalizable_support_subset {N : NormalForm I S} {Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) {i : I} {τ : S i → ℝ}
    (hτ : Rationalizable N i τ) {a : S i} (ha : 0 < τ a) : a ∈ Q i := by
  obtain ⟨n, hn⟩ := exists_ratIter_support_subset h
  exact hn i τ (hτ n) a ha

/-- A process of the pure deletion of Section 8.B is a process of the mixed one. -/
theorem msdChain_of_sdChain {N : NormalForm I S} {P Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (SDStep N) P Q) : Relation.ReflTransGen (MSDStep N) P Q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (sdStep_msdStep hs)

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.D** (MWG, p. 247). Every strategy that is part of a Nash equilibrium profile is
rationalizable. -/
theorem rationalizable_of_isMixedNash {N : NormalForm I S} {σ : (i : I) → S i → ℝ}
    (h : IsMixedNash N σ) (i : I) : Rationalizable N i (σ i) := by
  have hbr := (isMixedNash_iff_bestResponse N σ).1 h
  refine rationalizable_of_bestResponseSet (T := fun j => {σ j})
    (fun j τ hτ => by rw [Set.mem_singleton_iff.1 hτ]; exact h.1 j)
    (fun j τ hτ => ?_) (Set.mem_singleton _)
  rw [Set.mem_singleton_iff.1 hτ]
  exact ⟨σ, h.1, fun k _ => Set.mem_singleton _, hbr.2 j⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Footnote 3** (MWG, p. 245). A player always has a rationalizable strategy when a Nash
equilibrium exists, in particular in every finite game (Proposition 8.D.2). -/
theorem footnote_8_3 [∀ i, Nonempty (S i)] (N : NormalForm I S) (i : I) :
    ∃ τ, Rationalizable N i τ := by
  obtain ⟨σ, hσ⟩ := proposition_8_D_2 N
  exact ⟨σ i, rationalizable_of_isMixedNash hσ i⟩

/-- **Exercise 8.C.1** (MWG, p. 262). If iterated elimination of strictly dominated strategies
yields a unique prediction `s`, the same prediction results from eliminating strategies that are
never a best response: the rationalizable strategies of player `i` are exactly `s_i` played with
certainty. -/
theorem exercise_8_C_1 [∀ i, Nonempty (S i)] {N : NormalForm I S}
    {T : (i : I) → Set (S i)} (hT : Relation.ReflTransGen (SDStep N) (fullSets S) T)
    {s : (i : I) → S i} (hs : ∀ i, T i = {s i}) (i : I) (τ : S i → ℝ) :
    Rationalizable N i τ ↔ τ = pureMixed (s i) := by
  constructor
  · intro hτ
    have hsupp : ∀ a, 0 < τ a → a = s i := fun a ha => by
      have := rationalizable_support_subset (msdChain_of_sdChain hT) hτ ha
      rwa [hs i, Set.mem_singleton_iff] at this
    have hmix := hτ.isMixedStrategy
    have hzero : ∀ a, a ≠ s i → τ a = 0 := fun a ha =>
      le_antisymm (not_lt.1 fun h => ha (hsupp a h)) (hmix.1 a)
    have hone : τ (s i) = 1 := by
      rw [← hmix.2, Finset.sum_eq_single (s i) (fun b _ hb => hzero b hb)
        (fun h => absurd (mem_univ _) h)]
    funext a
    by_cases ha : a = s i
    · subst ha; simp [pureMixed, hone]
    · simp [pureMixed, ha, hzero a ha]
  · rintro rfl
    have hne : IsNashEquilibrium N s := exercise_8_D_2 hT hs
    exact rationalizable_of_isMixedNash ((corollary_8_D_1 N s).1 hne) i

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Never a best response versus strictly dominated: the separating-hyperplane argument

MWG, Section 8.C, pp. 243-245, and Exercise 8.C.3 (p. 262).

* `bestResponse_correlated_of_not_dominated`: in any finite game, a pure strategy `s_i` that is
  not strictly dominated by a mixed strategy is a best response to some *correlated* belief
  `μ` over the rivals' pure strategy profiles. The proof separates the convex set
  `{(u_i(σ_i', s_{-i}) - u_i(s_i, s_{-i}))_{s_{-i}} : σ_i' ∈ Δ(S_i)}` from the open positive
  orthant by a hyperplane (Mathlib's Hahn-Banach `geometric_hahn_banach_open`); the normal of
  the hyperplane, normalized, is `μ`. This is the remark on p. 245 that the equivalence
  reemerges when the rivals' randomizations may be correlated (`correlated_iff_not_dominated`).
* `expect_eq_mixedPayoff_marginals`: a payoff that depends only on the strategy of one rival
  has the same expectation under `μ` and under the product of the marginals of `μ`.
* **Exercise 8.C.3** (`exercise_8_C_3`): in a two-player game with finite strategy sets, a pure
  strategy that is never a best response to a mixed strategy of the opponent is strictly
  dominated by some mixed strategy (Figure 8.C.2 is the picture).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- A (correlated) belief over pure strategy profiles: a probability vector on `S`. -/
def IsBelief (μ : ((i : I) → S i) → ℝ) : Prop := (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1

/-- The expected payoff to player `i` from the mixed strategy `τ` when the rivals' pure strategy
profile `s_{-i}` is drawn from the belief `μ` (the `i`-th coordinate of `s` is ignored). -/
def beliefPayoff (N : NormalForm I S) (i : I) (μ : ((i : I) → S i) → ℝ) (τ : S i → ℝ) : ℝ :=
  ∑ s, μ s * N.mixedPayoff (update (pureProfile s) i τ) i

/-- **Section 8.C** (MWG, p. 245, small type). In a finite game, a pure strategy `a` of player `i`
that is not strictly dominated by any mixed strategy is a best response to some correlated belief
over the rivals' pure strategy profiles. -/
theorem bestResponse_correlated_of_not_dominated (N : NormalForm I S) (i : I) (a : S i)
    (hnd : ¬ MixedStrictlyDominated N i (pureMixed a)) :
    ∃ μ, IsBelief μ ∧ ∀ τ', IsMixedStrategy τ' →
      beliefPayoff N i μ τ' ≤ beliefPayoff N i μ (pureMixed a) := by
  classical
  -- the gains `d(τ')(s) = u_i(τ', s_{-i}) - u_i(a, s_{-i})`
  set d : (S i → ℝ) → ((i : I) → S i) → ℝ := fun τ' s =>
    N.mixedPayoff (update (pureProfile s) i τ') i -
      N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i with hd
  set C : Set (((i : I) → S i) → ℝ) := d '' mixedExtension (S i) with hC
  set P : Set (((i : I) → S i) → ℝ) := {x | ∀ s, 0 < x s} with hP
  have hPopen : IsOpen P := by
    rw [hP, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  have hPconv : Convex ℝ P := by
    intro x hx y hy p q hp hq hpq s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hp.eq_or_lt with rfl | hp'
    · simp only [zero_add] at hpq; subst hpq; simpa using hy s
    · nlinarith [hx s, hy s]
  have hdaff : ∀ τ₁ τ₂ (p q : ℝ), p + q = 1 → d (p • τ₁ + q • τ₂) = p • d τ₁ + q • d τ₂ := by
    intro τ₁ τ₂ p q hpq
    funext s
    simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mixedPayoff_update_add_smul N (pureProfile s) i (p • τ₁) τ₂ q i
    have h2 : N.mixedPayoff (update (pureProfile s) i (p • τ₁)) i =
        p * N.mixedPayoff (update (pureProfile s) i τ₁) i := by
      have := mixedPayoff_update_add_smul N (pureProfile s) i 0 τ₁ p i
      simp only [zero_add] at this
      rw [this]
      simp [mixedPayoff_update]
    rw [h1, h2]
    have : p * N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i +
        q * N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i =
        N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i := by rw [← add_mul, hpq, one_mul]
    linarith
  have hCconv : Convex ℝ C := by
    rintro _ ⟨τ₁, h₁, rfl⟩ _ ⟨τ₂, h₂, rfl⟩ p q hp hq hpq
    exact ⟨p • τ₁ + q • τ₂, convex_mixedExtension (S i) h₁ h₂ hp hq hpq, hdaff τ₁ τ₂ p q hpq⟩
  have hdisj : Disjoint P C := by
    rw [Set.disjoint_left]
    rintro x hx ⟨τ', hτ', rfl⟩
    refine hnd ⟨τ', hτ', (mixedStrictlyDominates_iff_pure N i τ' _).2 fun s => ?_⟩
    have := hx s
    simp only [hd] at this
    linarith
  obtain ⟨f, u₀, hfP, hfC⟩ := geometric_hahn_banach_open hPconv hPopen hCconv hdisj
  -- coordinates of the separating functional
  set p : ((i : I) → S i) → ℝ := fun s => f (Pi.single s 1) with hpdef
  have hf : ∀ x, f x = ∑ s, x s * p s := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (((i : I) → S i) → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul, hpdef]
    congr 2
    funext t
    simp only [Pi.single_apply, eq_comm]
  have h0C : (0 : ((i : I) → S i) → ℝ) ∈ C :=
    ⟨pureMixed a, isMixedStrategy_pureMixed a, by funext s; simp [hd]⟩
  have hu₀ : u₀ ≤ 0 := by simpa using hfC 0 h0C
  have hone : (fun _ => (1 : ℝ)) ∈ P := fun _ => one_pos
  have hgap : ∑ s, p s < u₀ := by
    have := hfP _ hone
    rw [hf] at this
    simpa only [one_mul] using this
  have hsump : ∑ s, p s < 0 := by linarith
  -- the separating normal points into the negative orthant
  have hpneg : ∀ s₀, p s₀ ≤ 0 := by
    intro s₀
    by_contra hpos
    push Not at hpos
    set t : ℝ := (u₀ - ∑ s, p s) / p s₀ + 1 with ht
    have htpos : 0 < t := by
      have : 0 ≤ (u₀ - ∑ s, p s) / p s₀ := div_nonneg (by linarith) hpos.le
      linarith
    have hx : (fun s => (1 : ℝ) + if s = s₀ then t else 0) ∈ P := by
      intro s
      change 0 < 1 + (if s = s₀ then t else 0)
      split_ifs <;> linarith
    have := hfP _ hx
    rw [hf] at this
    simp only [add_mul, one_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    have h2 : t * p s₀ = u₀ - ∑ s, p s + p s₀ := by
      rw [ht, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith
  -- the belief: the normalized negative of the normal
  set Z : ℝ := -∑ s, p s with hZ
  have hZpos : 0 < Z := by linarith
  refine ⟨fun s => -p s / Z, ⟨fun s => div_nonneg (by linarith [hpneg s]) hZpos.le, ?_⟩,
    fun τ' hτ' => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_neg_distrib, ← hZ, div_self hZpos.ne']
  · -- `f(d(τ')) ≥ 0`
    have hfd : 0 ≤ f (d τ') := by
      by_contra hneg
      push Not at hneg
      have hε : 0 < f (d τ') / ∑ s, p s := div_pos_of_neg_of_neg hneg hsump
      have hx : (fun _ => f (d τ') / ∑ s, p s) ∈ P := fun _ => hε
      have h1 := hfP _ hx
      have h2 := hfC _ ⟨τ', hτ', rfl⟩
      rw [hf (fun _ => _)] at h1
      rw [← Finset.mul_sum, div_mul_cancel₀ _ hsump.ne] at h1
      linarith
    rw [hf] at hfd
    unfold beliefPayoff
    have key : ∑ s, -p s / Z * N.mixedPayoff (update (pureProfile s) i τ') i -
        ∑ s, -p s / Z * N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i =
        -(∑ s, d τ' s * p s) / Z := by
      rw [← Finset.sum_sub_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [hd]
      ring
    have : -(∑ s, d τ' s * p s) / Z ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hZpos.le
    linarith

/-- **Section 8.C** (MWG, p. 245, small type). With correlated beliefs the equivalence holds for
any number of players: a pure strategy is a best response to some correlated belief iff it is
not strictly dominated. -/
theorem correlated_iff_not_dominated (N : NormalForm I S) (i : I) (a : S i) :
    (∃ μ, IsBelief μ ∧ ∀ τ', IsMixedStrategy τ' →
      beliefPayoff N i μ τ' ≤ beliefPayoff N i μ (pureMixed a)) ↔
      ¬ MixedStrictlyDominated N i (pureMixed a) := by
  refine ⟨?_, bestResponse_correlated_of_not_dominated N i a⟩
  rintro ⟨μ, hμ, hbr⟩ ⟨τ', hτ', hdom⟩
  have hlt := (mixedStrictlyDominates_iff_pure N i τ' _).1 hdom
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < μ s := by
    by_contra hno
    push Not at hno
    have : ∑ s, μ s ≤ 0 := Finset.sum_nonpos fun s _ => hno s
    linarith [hμ.2]
  have : beliefPayoff N i μ (pureMixed a) < beliefPayoff N i μ τ' := by
    refine Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hlt s).le (hμ.1 s))
      ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left (hlt s₀) hs₀⟩
  linarith [hbr τ' hτ']

/-- The marginal of a belief `μ` on player `k`'s pure strategies. -/
def marginal (μ : ((i : I) → S i) → ℝ) (k : I) : S k → ℝ :=
  fun b => ∑ s ∈ univ.filter (fun s : (i : I) → S i => s k = b), μ s

/-- The marginals of a belief are mixed strategies. -/
theorem isMixedProfile_marginal {μ : ((i : I) → S i) → ℝ} (hμ : IsBelief μ) :
    IsMixedProfile (marginal μ) := by
  intro k
  refine ⟨fun b => Finset.sum_nonneg fun s _ => hμ.1 s, ?_⟩
  unfold marginal
  rw [Finset.sum_fiberwise univ (fun s : (i : I) → S i => s k) μ]
  exact hμ.2

/-- A function of the profile that depends only on player `j`'s strategy has the same expectation
under a belief `μ` and under the independent product of its marginals. -/
theorem expect_eq_mixedPayoff_marginals {μ : ((i : I) → S i) → ℝ} (hμ : IsBelief μ) (j : I)
    (g : ((i : I) → S i) → ℝ) (hg : ∀ s s' : (i : I) → S i, s j = s' j → g s = g s') :
    ∑ s, μ s * g s = ∑ s, (∏ k, marginal μ k (s k)) * g s := by
  obtain ⟨s₀⟩ : Nonempty ((i : I) → S i) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hμ.2
    simp at this
  set h : S j → ℝ := fun b => g (update s₀ j b) with hh
  have hgh : ∀ s, g s = h (s j) := fun s => hg _ _ (by simp)
  -- the left side, fiber by fiber
  have hL : ∑ s, μ s * g s = ∑ b, marginal μ j b * h b := by
    rw [← Finset.sum_fiberwise univ (fun s : (i : I) → S i => s j)]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold marginal
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hgh s, (Finset.mem_filter.1 hs).2]
  -- the right side, via the auxiliary game whose payoff is `h(s_j)`
  set G : NormalForm I S := ⟨fun _ s => h (s j)⟩ with hG
  have hR : ∑ s, (∏ k, marginal μ k (s k)) * g s = G.mixedPayoff (marginal μ) j := by
    unfold NormalForm.mixedPayoff
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hgh s]
  have hpure : ∀ b, G.mixedPayoff (update (marginal μ) j (pureMixed b)) j = h b := by
    intro b
    unfold NormalForm.mixedPayoff
    have hterm : ∀ s : (i : I) → S i,
        (∏ k, update (marginal μ) j (pureMixed b) k (s k)) * G.payoff j s =
          (∏ k, update (marginal μ) j (pureMixed b) k (s k)) * h b := by
      intro s
      by_cases hsb : s j = b
      · simp [hG, hsb]
      · rw [prod_update_eq]
        simp [pureMixed, hsb]
    simp_rw [hterm]
    rw [← Finset.sum_mul, sum_prod_mixed_eq_one, one_mul]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using (isMixedStrategy_pureMixed b).2
    · rw [update_of_ne hk]; exact (isMixedProfile_marginal hμ k).2
  rw [hL, hR]
  conv_rhs => rw [← update_eq_self j (marginal μ), mixedPayoff_update_eq_sum_pure]
  simp only [hpure]

/-- **Exercise 8.C.3** (MWG, p. 262). In a two-player game with finite strategy sets, if the pure
strategy `s_i` is never a best response to any mixed strategy of `i`'s opponent, then `s_i` is
strictly dominated by some mixed strategy `σ_i ∈ Δ(S_i)`. -/
theorem exercise_8_C_3 (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (a : S i) (hnbr : NeverBestResponse N i (pureMixed a)) :
    MixedStrictlyDominated N i (pureMixed a) := by
  by_contra hnd
  obtain ⟨μ, hμ, hbr⟩ := bestResponse_correlated_of_not_dominated N i a hnd
  -- the payoff against `s_{-i}` depends only on the opponent's strategy `s_j`
  have hdep : ∀ τ : S i → ℝ, ∀ s s' : (k : I) → S k, s j = s' j →
      N.mixedPayoff (update (pureProfile s) i τ) i =
        N.mixedPayoff (update (pureProfile s') i τ) i := by
    intro τ s s' hss'
    congr 1
    funext k
    rcases htwo k with rfl | rfl
    · simp
    · simp [update_of_ne (Ne.symm hij), pureProfile, hss']
  have hσ := isMixedProfile_marginal hμ
  refine hnbr (marginal μ) hσ ⟨isMixedStrategy_pureMixed a, fun τ' hτ' => ?_⟩
  have hconv : ∀ τ : S i → ℝ, beliefPayoff N i μ τ = N.mixedPayoff (update (marginal μ) i τ) i := by
    intro τ
    unfold beliefPayoff
    rw [expect_eq_mixedPayoff_marginals hμ j _ (hdep τ),
      mixedPayoff_update_eq_expect N (marginal μ) i (hσ i).2]
  rw [← hconv, ← hconv]
  exact hbr τ' hτ'

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Trembling-hand perfection

MWG, Section 8.F, pp. 258-260, and Exercises 8.F.1 and 8.F.3 (pp. 265-266).

* Perturbed games (p. 258): `IsPerturbation ε` (`ε_i(s_i) ∈ (0, 1)`, `∑_{s_i} ε_i(s_i) < 1`),
  `perturbedSet ε i = Δ_ε(S_i)` and `IsPerturbedNash` (Nash equilibrium of `Γ_ε`).
* **Definition 8.F.1** (`IsTHP`): a Nash equilibrium that is the limit of Nash equilibria of
  a sequence of perturbed games whose trembles go to zero.
* **Proposition 8.F.1** (`proposition_8_F_1`, which is **Exercise 8.F.1**): a Nash equilibrium
  is trembling-hand perfect iff it is a best response to every element of some sequence of
  totally mixed profiles converging to it.
* Weak domination in `[I, {Δ(S_i)}, {u_i(·)}]` (Definition 8.B.3 for the mixed extension,
  `MixedWeaklyDominates`) and its pure test (`mixedWeaklyDominates_iff_pure`).
* **Proposition 8.F.2** (`proposition_8_F_2`, `proposition_8_F_2_pure`): no player's strategy in
  a trembling-hand perfect equilibrium is weakly dominated, and no weakly dominated pure
  strategy is played with positive probability.
* **Exercise 8.F.3** (`exercise_8_F_3`, Selten's theorem): every game with finite (nonempty)
  strategy sets has a trembling-hand perfect equilibrium: every perturbed game has an
  equilibrium (`exists_perturbedNash`, Proposition 8.D.3 on `Δ_ε(S_i)`) and a subsequence of the
  equilibria of the uniformly perturbed games converges to an equilibrium of `Γ_N`. Hence a Nash
  equilibrium in which no weakly dominated strategy is played exists
  (`exists_nash_no_weakly_dominated`, p. 259).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset Filter Topology

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- **Section 8.F** (MWG, p. 258). A perturbation: for each player `i` and pure strategy `s_i`
a number `ε_i(s_i) ∈ (0, 1)`, with `∑_{s_i ∈ S_i} ε_i(s_i) < 1`. -/
def IsPerturbation (ε : (i : I) → S i → ℝ) : Prop :=
  (∀ i s, 0 < ε i s ∧ ε i s < 1) ∧ ∀ i, ∑ s, ε i s < 1

/-- **Section 8.F** (MWG, p. 258). The perturbed strategy set
`Δ_ε(S_i) = {σ_i : σ_i(s_i) ≥ ε_i(s_i) for all s_i ∈ S_i and ∑_{s_i} σ_i(s_i) = 1}`. -/
def perturbedSet (ε : (i : I) → S i → ℝ) (i : I) : Set (S i → ℝ) :=
  {τ | (∀ s, ε i s ≤ τ s) ∧ ∑ s, τ s = 1}

/-- A Nash equilibrium of the perturbed game `Γ_ε = [I, {Δ_ε(S_i)}, {u_i(·)}]`. -/
def IsPerturbedNash (N : NormalForm I S) (ε : (i : I) → S i → ℝ) (σ : (i : I) → S i → ℝ) :
    Prop :=
  (∀ i, σ i ∈ perturbedSet ε i) ∧
    ∀ i, ∀ τ ∈ perturbedSet ε i, N.mixedPayoff (update σ i τ) i ≤ N.mixedPayoff σ i

/-- **Definition 8.F.1** (MWG, p. 258). A Nash equilibrium `σ` of `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`
is (normal form) trembling-hand perfect if there is a sequence of perturbed games `Γ_{εᵏ}` with
`εᵏ_i(s_i) → 0` for all `i` and `s_i`, and Nash equilibria `σᵏ` of `Γ_{εᵏ}` with `σᵏ → σ`. -/
def IsTHP (N : NormalForm I S) (σ : (i : I) → S i → ℝ) : Prop :=
  IsMixedNash N σ ∧ ∃ (ε : ℕ → (i : I) → S i → ℝ) (σs : ℕ → (i : I) → S i → ℝ),
    (∀ k, IsPerturbation (ε k)) ∧ (∀ i s, Tendsto (fun k => ε k i s) atTop (𝓝 0)) ∧
    (∀ k, IsPerturbedNash N (ε k) (σs k)) ∧ Tendsto σs atTop (𝓝 σ)

/-- **Section 8.F** (MWG, p. 259). A totally mixed strategy gives every pure strategy positive
probability. -/
def IsTotallyMixed {T : Type*} [Fintype T] (τ : T → ℝ) : Prop :=
  IsMixedStrategy τ ∧ ∀ s, 0 < τ s

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- Perturbed strategies are mixed strategies. -/
theorem isMixedStrategy_of_mem_perturbedSet {ε : (i : I) → S i → ℝ} (hε : IsPerturbation ε)
    {i : I} {τ : S i → ℝ} (hτ : τ ∈ perturbedSet ε i) : IsMixedStrategy τ :=
  ⟨fun s => (hε.1 i s).1.le.trans (hτ.1 s), hτ.2⟩

/-- In a Nash equilibrium of a perturbed game, a pure strategy that is not a best response is
played with its minimal probability `ε_i(s_i)`. -/
theorem perturbedNash_eq_of_not_best {N : NormalForm I S} {ε : (i : I) → S i → ℝ}
    {σ : (i : I) → S i → ℝ} (h : IsPerturbedNash N ε σ) (i : I) {a b : S i}
    (hab : N.mixedPayoff (update σ i (pureMixed a)) i <
      N.mixedPayoff (update σ i (pureMixed b)) i) : σ i a = ε i a := by
  refine le_antisymm ?_ ((h.1 i).1 a)
  by_contra hgt
  push Not at hgt
  have hba : b ≠ a := by rintro rfl; exact lt_irrefl _ hab
  set c := σ i a - ε i a with hc
  have hcpos : 0 < c := by linarith
  have hmem : σ i + c • (pureMixed b - pureMixed a) ∈ perturbedSet ε i := by
    refine ⟨fun t => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, pureMixed]
      rcases eq_or_ne t a with rfl | hta
      · simp [hba.symm]; linarith
      · by_cases htb : t = b
        · subst htb; simp [hta]; linarith [(h.1 i).1 t]
        · simp only [hta, htb, ↓reduceIte, sub_self, mul_zero, add_zero]; exact (h.1 i).1 t
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_sub_distrib, (h.1 i).2, (isMixedStrategy_pureMixed b).2,
        (isMixedStrategy_pureMixed a).2, sub_self, mul_zero, add_zero]
  have hle := h.2 i _ hmem
  rw [mixedPayoff_shift] at hle
  rw [update_eq_self] at hle
  nlinarith

omit [∀ i, DecidableEq (S i)] in
/-- A perturbed equilibrium is a profile of totally mixed strategies. -/
theorem isTotallyMixed_of_perturbedNash {N : NormalForm I S} {ε : (i : I) → S i → ℝ}
    (hε : IsPerturbation ε) {σ : (i : I) → S i → ℝ} (h : IsPerturbedNash N ε σ) (i : I) :
    IsTotallyMixed (σ i) :=
  ⟨isMixedStrategy_of_mem_perturbedSet hε (h.1 i),
    fun s => (hε.1 i s).1.trans_le ((h.1 i).1 s)⟩

omit [∀ i, DecidableEq (S i)] in
/-- A mixed strategy gives at most probability one to each pure strategy. -/
theorem mixed_le_one {T : Type*} [Fintype T] {τ : T → ℝ} (h : IsMixedStrategy τ)
    (s : T) : τ s ≤ 1 := by
  rw [← h.2]
  exact Finset.single_le_sum (fun t _ => h.1 t) (mem_univ s)

omit [∀ i, DecidableEq (S i)] in
/-- A mixed strategy plays some pure strategy with positive probability. -/
theorem mixed_exists_pos {T : Type*} [Fintype T] {τ : T → ℝ} (h : IsMixedStrategy τ) :
    ∃ s, 0 < τ s := by
  by_contra hno
  push Not at hno
  have : ∑ s, τ s ≤ 0 := Finset.sum_nonpos fun s _ => hno s
  linarith [h.2]

omit [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.F.1** (MWG, p. 259; **Exercise 8.F.1**, p. 265). A Nash equilibrium `σ` of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` is (normal form) trembling-hand perfect iff there is a sequence
of totally mixed profiles `σᵏ → σ` such that `σ_i` is a best response to every `σᵏ_{-i}`, for all
`i`. -/
theorem proposition_8_F_1 (N : NormalForm I S) {σ : (i : I) → S i → ℝ} (hσ : IsMixedNash N σ) :
    IsTHP N σ ↔ ∃ ρ : ℕ → (i : I) → S i → ℝ, (∀ k i, IsTotallyMixed (ρ k i)) ∧
      Tendsto ρ atTop (𝓝 σ) ∧ ∀ k i, IsBestResponse N i (σ i) (ρ k) := by
  classical
  constructor
  · rintro ⟨-, ε, σs, hε, hε0, hNE, hlim⟩
    -- eventually every strategy played by `σ_i` is played with more than its minimum
    have hev : ∀ᶠ k in atTop, ∀ i a, 0 < σ i a → ε k i a < σs k i a := by
      rw [eventually_all]
      intro i
      rw [eventually_all]
      intro a
      by_cases ha : 0 < σ i a
      · have h1 : Tendsto (fun k => σs k i a - ε k i a) atTop (𝓝 (σ i a - 0)) :=
          (((continuous_apply a).comp (continuous_apply i)).tendsto σ |>.comp hlim).sub (hε0 i a)
        rw [sub_zero] at h1
        filter_upwards [h1.eventually (lt_mem_nhds ha)] with k hk _
        linarith
      · exact Eventually.of_forall fun k h => absurd h ha
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    refine ⟨fun k => σs (k + K), fun k i => isTotallyMixed_of_perturbedNash (hε _) (hNE _) i,
      hlim.comp (tendsto_add_atTop_nat K), fun k i => ?_⟩
    rw [isBestResponse_iff_support N i (hσ.1 i)]
    intro a ha b
    by_contra hlt
    push Not at hlt
    have := perturbedNash_eq_of_not_best (hNE (k + K)) i hlt
    have := hK (k + K) (Nat.le_add_left K k) i a ha
    linarith
  · rintro ⟨ρ, hρ, hlim, hbr⟩
    refine ⟨hσ, fun k i s => if 0 < σ i s then min (ρ k i s / 2) (1 / ((k : ℝ) + 2))
      else ρ k i s, ρ, fun k => ?_, fun i s => ?_, fun k => ?_, hlim⟩
    · -- the trembles form a perturbation
      have hρle : ∀ i s, ρ k i s ≤ 1 := fun i s => mixed_le_one (hρ k i).1 s
      have hεle : ∀ i s, (if 0 < σ i s then min (ρ k i s / 2) (1 / ((k : ℝ) + 2))
          else ρ k i s) ≤ ρ k i s := by
        intro i s
        split_ifs
        · exact (min_le_left _ _).trans (by linarith [(hρ k i).2 s])
        · exact le_rfl
      refine ⟨fun i s => ⟨?_, ?_⟩, fun i => ?_⟩
      · dsimp only
        split_ifs
        · exact lt_min (by linarith [(hρ k i).2 s]) (by positivity)
        · exact (hρ k i).2 s
      · dsimp only
        split_ifs with hs
        · exact (min_le_left _ _).trans_lt (by linarith [hρle i s])
        · -- some other strategy has positive probability under `ρᵏ_i`
          obtain ⟨a, ha⟩ := mixed_exists_pos (hσ.1 i)
          have hne : s ≠ a := fun h => hs (h ▸ ha)
          have h1 : ρ k i s + ρ k i a ≤ 1 := by
            rw [← (hρ k i).1.2]
            have := Finset.sum_le_sum_of_subset_of_nonneg (s := {s, a}) (t := univ)
              (f := ρ k i) (subset_univ _) (fun x _ _ => (hρ k i).1.1 x)
            rwa [Finset.sum_pair hne] at this
          linarith [(hρ k i).2 a]
      · obtain ⟨a, ha⟩ := mixed_exists_pos (hσ.1 i)
        have hlt : (if 0 < σ i a then min (ρ k i a / 2) (1 / ((k : ℝ) + 2)) else ρ k i a) <
            ρ k i a := by
          simp only [ha, ↓reduceIte]
          exact (min_le_left _ _).trans_lt (by linarith [(hρ k i).2 a])
        calc ∑ s, (if 0 < σ i s then min (ρ k i s / 2) (1 / ((k : ℝ) + 2)) else ρ k i s)
            < ∑ s, ρ k i s := Finset.sum_lt_sum (fun s _ => hεle i s) ⟨a, mem_univ _, hlt⟩
          _ = 1 := (hρ k i).1.2
    · -- the trembles vanish
      by_cases hs : 0 < σ i s
      · simp only [hs, ↓reduceIte]
        have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          refine squeeze_zero (fun k => by positivity) (fun k => ?_) this
          gcongr
          linarith
        refine squeeze_zero (fun k => le_min (by linarith [(hρ k i).2 s]) (by positivity))
          (fun k => min_le_right _ _) h1
      · simp only [hs, ↓reduceIte]
        have h1 : Tendsto (fun k => ρ k i s) atTop (𝓝 (σ i s)) :=
          tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim i) s
        rwa [le_antisymm (not_lt.1 hs) ((hσ.1 i).1 s)] at h1
    · -- `ρᵏ` is an equilibrium of the perturbed game
      refine ⟨fun i => ⟨fun s => ?_, (hρ k i).1.2⟩, fun i τ hτ => ?_⟩
      · dsimp only
        split_ifs
        · exact (min_le_left _ _).trans (by linarith [(hρ k i).2 s])
        · exact le_rfl
      · have hsupp := (isBestResponse_iff_support N i (hσ.1 i) (ρ k)).1 (hbr k i)
        obtain ⟨a₀, ha₀⟩ := mixed_exists_pos (hσ.1 i)
        set v : S i → ℝ := fun s => N.mixedPayoff (update (ρ k) i (pureMixed s)) i with hv
        set M := v a₀
        have hvM : ∀ s, v s ≤ M := fun s => hsupp a₀ ha₀ s
        have hvsupp : ∀ s, 0 < σ i s → v s = M := fun s hs => le_antisymm (hvM s) (hsupp s hs a₀)
        conv_rhs => rw [← update_eq_self i (ρ k)]
        rw [mixedPayoff_update_eq_sum_pure N (ρ k) i τ i,
          mixedPayoff_update_eq_sum_pure N (ρ k) i (ρ k i) i]
        have hterm : ∀ s, (τ s - ρ k i s) * v s ≤ (τ s - ρ k i s) * M := by
          intro s
          by_cases hs : 0 < σ i s
          · rw [hvsupp s hs]
          · have : ρ k i s ≤ τ s := by
              have := hτ.1 s
              simp only [hs, ↓reduceIte] at this
              exact this
            exact mul_le_mul_of_nonneg_left (hvM s) (by linarith)
        have hsum := Finset.sum_le_sum fun s (_ : s ∈ univ) => hterm s
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, hτ.2, (hρ k i).1.2, sub_self,
          zero_mul] at hsum
        simp only [sub_mul, Finset.sum_sub_distrib] at hsum
        linarith

/-- **Definition 8.B.3 for `[I, {Δ(S_i)}, {u_i(·)}]`** (MWG, pp. 238 and 259). `τ'` weakly
dominates `τ`: at least as good against every profile of the rivals' mixed strategies and
strictly better against some. -/
def MixedWeaklyDominates (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) : Prop :=
  (∀ ρ : (j : I) → S j → ℝ, IsMixedProfile ρ →
      N.mixedPayoff (update ρ i τ) i ≤ N.mixedPayoff (update ρ i τ') i) ∧
    ∃ ρ : (j : I) → S j → ℝ, IsMixedProfile ρ ∧
      N.mixedPayoff (update ρ i τ) i < N.mixedPayoff (update ρ i τ') i

/-- The mixed strategy `τ` of player `i` is weakly dominated. -/
def MixedWeaklyDominated (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∃ τ', IsMixedStrategy τ' ∧ MixedWeaklyDominates N i τ' τ

/-- Weak domination can be tested against the rivals' pure strategy profiles. -/
theorem mixedWeaklyDominates_iff_pure (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) :
    MixedWeaklyDominates N i τ' τ ↔
      (∀ s, N.mixedPayoff (update (pureProfile s) i τ) i ≤
        N.mixedPayoff (update (pureProfile s) i τ') i) ∧
      ∃ s, N.mixedPayoff (update (pureProfile s) i τ) i <
        N.mixedPayoff (update (pureProfile s) i τ') i := by
  constructor
  · rintro ⟨hle, ρ, hρ, hlt⟩
    refine ⟨fun s => hle _ (isMixedProfile_pureProfile s), ?_⟩
    by_contra hno
    push Not at hno
    have := mixedPayoff_le_of_pure N hρ i i (τ := τ') (τ' := τ) hno
    linarith
  · rintro ⟨hle, s, hs⟩
    exact ⟨fun ρ hρ => mixedPayoff_le_of_pure N hρ i i hle, _, isMixedProfile_pureProfile s, hs⟩

omit [∀ i, DecidableEq (S i)] in
/-- Against a totally mixed profile, a weakly dominating strategy does strictly better. -/
theorem MixedWeaklyDominates.lt_of_totallyMixed {N : NormalForm I S} {i : I} {τ' τ : S i → ℝ}
    (h : MixedWeaklyDominates N i τ' τ) {ρ : (j : I) → S j → ℝ}
    (hρ : ∀ j, IsTotallyMixed (ρ j)) :
    N.mixedPayoff (update ρ i τ) i < N.mixedPayoff (update ρ i τ') i := by
  classical
  obtain ⟨hle, s₀, hs₀⟩ := (mixedWeaklyDominates_iff_pure N i τ' τ).1 h
  rw [mixedPayoff_update_eq_expect N ρ i (hρ i).1.2, mixedPayoff_update_eq_expect N ρ i (hρ i).1.2]
  have hw : ∀ s : (j : I) → S j, 0 ≤ ∏ j, ρ j (s j) :=
    prod_mixed_nonneg fun j a => (hρ j).1.1 a
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle s) (hw s))
    ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left hs₀ (Finset.prod_pos fun j _ => (hρ j).2 _)⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.F.2** (MWG, p. 259). In a (normal form) trembling-hand perfect Nash
equilibrium `σ`, no `σ_i` is a weakly dominated strategy. -/
theorem proposition_8_F_2 (N : NormalForm I S) {σ : (i : I) → S i → ℝ} (h : IsTHP N σ)
    (i : I) : ¬ MixedWeaklyDominated N i (σ i) := by
  classical
  obtain ⟨ρ, hρ, -, hbr⟩ := (proposition_8_F_1 N h.1).1 h
  rintro ⟨τ', hτ', hdom⟩
  have := hdom.lt_of_totallyMixed (hρ 0)
  linarith [(hbr 0 i).2 τ' hτ']

/-- If the pure strategy `a` is weakly dominated, so is every mixed strategy that plays it with
positive probability. -/
theorem mixedWeaklyDominated_of_pure (N : NormalForm I S) (i : I) {a : S i}
    (ha : MixedWeaklyDominated N i (pureMixed a)) {τ : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hpos : 0 < τ a) : MixedWeaklyDominated N i τ := by
  obtain ⟨τ', hτ', hle, ρ₀, hρ₀, hlt⟩ := ha
  refine ⟨τ + τ a • (τ' - pureMixed a), isMixedStrategy_shift hτ hτ' hpos.le le_rfl,
    fun ρ hρ => ?_, ρ₀, hρ₀, ?_⟩
  · rw [mixedPayoff_shift]
    nlinarith [hle ρ hρ]
  · rw [mixedPayoff_shift]
    nlinarith

/-- **Proposition 8.F.2** (MWG, p. 259), second statement. In a trembling-hand perfect Nash
equilibrium no weakly dominated pure strategy is played with positive probability. -/
theorem proposition_8_F_2_pure (N : NormalForm I S) {σ : (i : I) → S i → ℝ} (h : IsTHP N σ)
    (i : I) (a : S i) (ha : MixedWeaklyDominated N i (pureMixed a)) : σ i a = 0 := by
  by_contra hne
  have hpos : 0 < σ i a := lt_of_le_of_ne ((h.1.1 i).1 a) (Ne.symm hne)
  exact proposition_8_F_2 N h i (mixedWeaklyDominated_of_pure N i ha (h.1.1 i) hpos)

/-! ### Existence (Exercise 8.F.3) -/

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- `Δ_ε(S_i)` is convex. -/
theorem convex_perturbedSet (ε : (i : I) → S i → ℝ) (i : I) : Convex ℝ (perturbedSet ε i) := by
  intro x hx y hy p q hp hq hpq
  refine ⟨fun t => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx.1 t) hp
    have h2 := mul_le_mul_of_nonneg_left (hy.1 t) hq
    have h3 : ε i t = p * ε i t + q * ε i t := by rw [← add_mul, hpq, one_mul]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hpq]

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- `Δ_ε(S_i)` is compact. -/
theorem isCompact_perturbedSet {ε : (i : I) → S i → ℝ} (hε : IsPerturbation ε) (i : I) :
    IsCompact (perturbedSet ε i) := by
  refine (isCompact_mixedExtension (S i)).of_isClosed_subset ?_
    fun τ hτ => isMixedStrategy_of_mem_perturbedSet hε hτ
  have h1 : IsClosed {τ : S i → ℝ | ∀ s, ε i s ≤ τ s} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have h2 : IsClosed {τ : S i → ℝ | ∑ s, τ s = 1} :=
    isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const
  exact h1.inter h2

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- `Δ_ε(S_i)` is nonempty: spread the slack `1 - ∑ ε_i` uniformly. -/
theorem perturbedSet_nonempty [∀ i, Nonempty (S i)] {ε : (i : I) → S i → ℝ}
    (hε : IsPerturbation ε) (i : I) : (perturbedSet ε i).Nonempty := by
  refine ⟨fun s => ε i s + (1 - ∑ t, ε i t) * uniformMixed (S i) s, fun s => ?_, ?_⟩
  · have := hε.2 i
    have := uniformMixed_pos (S i) s
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, (isMixedStrategy_uniformMixed (S i)).2]
    ring

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.F.3**, first step (MWG, p. 266). Every perturbed game has a Nash equilibrium. -/
theorem exists_perturbedNash [∀ i, Nonempty (S i)] (N : NormalForm I S)
    {ε : (i : I) → S i → ℝ} (hε : IsPerturbation ε) : ∃ σ, IsPerturbedNash N ε σ := by
  obtain ⟨σ, hσ, hne⟩ := nash_exists_of_quasiconcave (E := fun i => S i → ℝ)
    (u := fun i σ => N.mixedPayoff σ i) (S := perturbedSet ε)
    (fun i => perturbedSet_nonempty hε i) (fun i => isCompact_perturbedSet hε i)
    (fun i => convex_perturbedSet ε i) (fun i => (continuous_mixedPayoff N i).continuousOn)
    (fun i σ _ => (concaveOn_mixedPayoff_update N σ i (convex_perturbedSet ε i)).quasiconcaveOn)
  exact ⟨σ, fun i => hσ i (Set.mem_univ i), hne⟩

omit [∀ i, DecidableEq (S i)] in
/-- Payoffs are jointly continuous in the profile and the replacing strategy. -/
theorem tendsto_mixedPayoff_update (N : NormalForm I S) (i : I) {σs : ℕ → (j : I) → S j → ℝ}
    {τs : ℕ → S i → ℝ} {σ : (j : I) → S j → ℝ} {τ : S i → ℝ} (h1 : Tendsto σs atTop (𝓝 σ))
    (h2 : Tendsto τs atTop (𝓝 τ)) :
    Tendsto (fun n => N.mixedPayoff (update (σs n) i (τs n)) i) atTop
      (𝓝 (N.mixedPayoff (update σ i τ) i)) := by
  have hupd : Continuous fun p : ((j : I) → S j → ℝ) × (S i → ℝ) => update p.1 i p.2 :=
    continuous_fst.update i continuous_snd
  have hc : Continuous fun p : ((j : I) → S j → ℝ) × (S i → ℝ) =>
      N.mixedPayoff (update p.1 i p.2) i := (continuous_mixedPayoff N i).comp hupd
  have h3 : Tendsto (fun n => (σs n, τs n)) atTop (𝓝 (σ, τ)) := h1.prodMk_nhds h2
  have h4 := (hc.tendsto (σ, τ)).comp h3
  exact h4

/-- The uniform trembles `εⁿ_i(s_i) = 1 / ((n + 2) |S_i|)`. -/
noncomputable def uniformTremble (S : I → Type*) [∀ i, Fintype (S i)] (n : ℕ) :
    (i : I) → S i → ℝ :=
  fun i _ => 1 / (((n : ℝ) + 2) * Fintype.card (S i))

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem isPerturbation_uniformTremble [∀ i, Nonempty (S i)] (n : ℕ) :
    IsPerturbation (uniformTremble S n) := by
  have hc : ∀ i, (1 : ℝ) ≤ Fintype.card (S i) := fun i => by
    exact_mod_cast Fintype.card_pos
  refine ⟨fun i s => ⟨by unfold uniformTremble; have := hc i; positivity, ?_⟩, fun i => ?_⟩
  · unfold uniformTremble
    rw [div_lt_one (by have := hc i; positivity)]
    nlinarith [hc i]
  · simp only [uniformTremble, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have := hc i
    rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem tendsto_uniformTremble [∀ i, Nonempty (S i)] (i : I) (s : S i) :
    Tendsto (fun n => uniformTremble S n i s) atTop (𝓝 0) := by
  have hc : (1 : ℝ) ≤ Fintype.card (S i) := by exact_mod_cast Fintype.card_pos
  refine squeeze_zero (fun n => by unfold uniformTremble; positivity) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold uniformTremble
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.F.3** (MWG, p. 266; Selten 1975, p. 259). Every game
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` in which the `S_i` are finite (nonempty) sets has a (normal form)
trembling-hand perfect Nash equilibrium. -/
theorem exercise_8_F_3 [∀ i, Nonempty (S i)] (N : NormalForm I S) : ∃ σ, IsTHP N σ := by
  choose σs hσs using fun n => exists_perturbedNash N (isPerturbation_uniformTremble (S := S) n)
  set K : Set ((i : I) → S i → ℝ) := Set.pi Set.univ fun i => mixedExtension (S i)
  have hK : IsCompact K := isCompact_univ_pi fun i => isCompact_mixedExtension (S i)
  have hmem : ∀ n, σs n ∈ K := fun n i _ =>
    isMixedStrategy_of_mem_perturbedSet (isPerturbation_uniformTremble n) ((hσs n).1 i)
  obtain ⟨σ, hσK, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hσ : IsMixedProfile σ := fun i => hσK i (Set.mem_univ i)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- the limit is a Nash equilibrium of `Γ_N`
  have hNE : IsMixedNash N σ := by
    refine ⟨hσ, fun i τ hτ => ?_⟩
    -- approximate `τ` by perturbed strategies
    set c : ℕ → ℝ := fun n => 1 / ((φ n : ℝ) + 2) with hcdef
    set τs : ℕ → S i → ℝ := fun n => (1 - c n) • τ + uniformTremble S (φ n) i with hτs
    have hc0 : Tendsto c atTop (𝓝 0) :=
      squeeze_zero (fun n => by positivity) (fun n => by
        change 1 / ((φ n : ℝ) + 2) ≤ 1 / ((φ n : ℝ) + 1)
        gcongr
        linarith) ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφtop)
    have hτlim : Tendsto τs atTop (𝓝 τ) := by
      have h1 : Tendsto (fun n => (1 - c n) • τ) atTop (𝓝 ((1 - 0 : ℝ) • τ)) :=
        (tendsto_const_nhds.sub hc0).smul_const τ
      have h2 : Tendsto (fun n => uniformTremble S (φ n) i) atTop (𝓝 0) :=
        tendsto_pi_nhds.2 fun s => (tendsto_uniformTremble i s).comp hφtop
      simpa using h1.add h2
    have hτmem : ∀ n, τs n ∈ perturbedSet (uniformTremble S (φ n)) i := by
      intro n
      have hc1 : c n ≤ 1 := by
        simp only [hcdef]
        rw [div_le_one (by positivity)]
        linarith [(φ n).cast_nonneg (α := ℝ)]
      refine ⟨fun s => ?_, ?_⟩
      · simp only [hτs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [hτ.1 s]
      · simp only [hτs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hτ.2, mul_one, uniformTremble, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcdef]
        have : (Fintype.card (S i) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp
        ring
    have hineq : ∀ n, N.mixedPayoff (update (σs (φ n)) i (τs n)) i ≤
        N.mixedPayoff (σs (φ n)) i := fun n => (hσs (φ n)).2 i _ (hτmem n)
    have hl1 := tendsto_mixedPayoff_update N i hlim hτlim
    have hl2 : Tendsto (fun n => N.mixedPayoff ((σs ∘ φ) n) i) atTop
        (𝓝 (N.mixedPayoff σ i)) := ((continuous_mixedPayoff N i).tendsto σ).comp hlim
    exact le_of_tendsto_of_tendsto' hl1 hl2 hineq
  refine ⟨σ, hNE, fun n => uniformTremble S (φ n), fun n => σs (φ n),
    fun n => isPerturbation_uniformTremble _, fun i s => (tendsto_uniformTremble i s).comp hφtop,
    fun n => hσs (φ n), hlim⟩

/-- **Section 8.F** (MWG, pp. 259-260). Every finite game has a Nash equilibrium in which no player
plays a weakly dominated strategy, and no weakly dominated pure strategy is played with positive
probability. -/
theorem exists_nash_no_weakly_dominated [∀ i, Nonempty (S i)] (N : NormalForm I S) :
    ∃ σ, IsMixedNash N σ ∧ (∀ i, ¬ MixedWeaklyDominated N i (σ i)) ∧
      ∀ i a, MixedWeaklyDominated N i (pureMixed a) → σ i a = 0 := by
  obtain ⟨σ, hσ⟩ := exercise_8_F_3 N
  exact ⟨σ, hσ.1, proposition_8_F_2 N hσ, proposition_8_F_2_pure N hσ⟩

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Two-player games given by payoff tables

MWG's two-player examples are payoff tables: player 1 (`i = 0`) chooses a row among `m`, player 2
(`i = 1`) a column among `n`. `bimatrix u₁ u₂` is the Chapter 7 normal form with strategy sets
`Fin m` and `Fin n` (`S2 m n`), and `pp a b` is the pure profile (row `a`, column `b`).

This module translates the chapter's notions for such games into statements about the table:
pure payoffs after a deviation (`bimatrix_update_zero`, `bimatrix_update_one`), Nash
equilibrium (`bimatrix_isNash_iff`), domination (`bimatrix_strictlyDominates_zero_iff`, …), and
mixed payoffs (`mixedPayoff_fin_two`, `bimatrix_mixedPayoff_zero`, …).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- The strategy sets `S_1 = Fin m` (rows) and `S_2 = Fin n` (columns). -/
abbrev S2 (m n : ℕ) : Fin 2 → Type := fun i => Fin (![m, n] i)

/-- The two-player game with payoff tables `u₁` (player 1, rows) and `u₂` (player 2). -/
def bimatrix {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : NormalForm (Fin 2) (S2 m n) where
  payoff i s := if i = 0 then u₁ (s 0) (s 1) else u₂ (s 0) (s 1)

/-- The pure profile (row `a`, column `b`). -/
def pp {m n : ℕ} (a : Fin m) (b : Fin n) : (i : Fin 2) → S2 m n i :=
  Fin.cons a (Fin.cons b finZeroElim)

@[simp] theorem pp_zero {m n : ℕ} (a : Fin m) (b : Fin n) : pp a b 0 = a := rfl

@[simp] theorem pp_one {m n : ℕ} (a : Fin m) (b : Fin n) : pp a b 1 = b := rfl

theorem eq_pp {m n : ℕ} (s : (i : Fin 2) → S2 m n i) : s = pp (s 0) (s 1) := by
  funext i
  fin_cases i <;> rfl

variable {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)

@[simp] theorem bimatrix_payoff_zero (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).payoff 0 s = u₁ (s 0) (s 1) := rfl

@[simp] theorem bimatrix_payoff_one (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).payoff 1 s = u₂ (s 0) (s 1) := rfl

/-- Player 1 deviates to row `a`. -/
@[simp] theorem bimatrix_update_zero (s : (i : Fin 2) → S2 m n i) (a : Fin m) (k : Fin 2) :
    (bimatrix u₁ u₂).payoff k (update s 0 a) = if k = 0 then u₁ a (s 1) else u₂ a (s 1) := by
  simp [bimatrix, Function.update]

/-- Player 2 deviates to column `b`. -/
@[simp] theorem bimatrix_update_one (s : (i : Fin 2) → S2 m n i) (b : Fin n) (k : Fin 2) :
    (bimatrix u₁ u₂).payoff k (update s 1 b) = if k = 0 then u₁ (s 0) b else u₂ (s 0) b := by
  simp [bimatrix, Function.update]

/-- Nash equilibrium (Definition 8.D.1) in a two-player table. -/
theorem bimatrix_isNash_iff (a : Fin m) (b : Fin n) :
    IsNashEquilibrium (bimatrix u₁ u₂) (pp a b) ↔
      (∀ a', u₁ a' b ≤ u₁ a b) ∧ ∀ b', u₂ a b' ≤ u₂ a b := by
  constructor
  · intro h
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · simpa using h 0 a'
    · simpa using h 1 b'
  · rintro ⟨h1, h2⟩ i t
    fin_cases i
    · simpa using h1 t
    · simpa using h2 t

/-- Strict domination (Definition 8.B.2) for player 1. -/
theorem bimatrix_strictlyDominates_zero_iff (a' a : Fin m) :
    StrictlyDominates (bimatrix u₁ u₂) 0 a' a ↔ ∀ b, u₁ a b < u₁ a' b := by
  constructor
  · intro h b
    simpa using h (pp a b)
  · intro h r
    simpa using h (r 1)

/-- Strict domination (Definition 8.B.2) for player 2. -/
theorem bimatrix_strictlyDominates_one_iff (b' b : Fin n) :
    StrictlyDominates (bimatrix u₁ u₂) 1 b' b ↔ ∀ a, u₂ a b < u₂ a b' := by
  constructor
  · intro h a
    simpa using h (pp a b)
  · intro h r
    simpa using h (r 0)

/-- Weak domination (Definition 8.B.3) for player 1. -/
theorem bimatrix_weaklyDominates_zero_iff (a' a : Fin m) :
    WeaklyDominates (bimatrix u₁ u₂) 0 a' a ↔
      (∀ b, u₁ a b ≤ u₁ a' b) ∧ ∃ b, u₁ a b < u₁ a' b := by
  constructor
  · rintro ⟨h1, r, hr⟩
    exact ⟨fun b => by simpa using h1 (pp a b), r 1, by simpa using hr⟩
  · rintro ⟨h1, b, hb⟩
    exact ⟨fun r => by simpa using h1 (r 1), pp a b, by simpa using hb⟩

/-- Weak domination (Definition 8.B.3) for player 2. -/
theorem bimatrix_weaklyDominates_one_iff (b' b : Fin n) :
    WeaklyDominates (bimatrix u₁ u₂) 1 b' b ↔
      (∀ a, u₂ a b ≤ u₂ a b') ∧ ∃ a, u₂ a b < u₂ a b' := by
  constructor
  · rintro ⟨h1, r, hr⟩
    exact ⟨fun a => by simpa using h1 (pp a b), r 0, by simpa using hr⟩
  · rintro ⟨h1, a, ha⟩
    exact ⟨fun r => by simpa using h1 (r 0), pp a b, by simpa using ha⟩

/-- A strictly dominant strategy (Definition 8.B.1) for player 1. -/
theorem bimatrix_strictlyDominant_zero_iff (a : Fin m) :
    StrictlyDominant (bimatrix u₁ u₂) 0 a ↔ ∀ a', a' ≠ a → ∀ b, u₁ a' b < u₁ a b := by
  exact (strictlyDominant_iff_dominates (bimatrix u₁ u₂) 0 a).trans
    (forall_congr' fun a' => imp_congr_right fun _ =>
      bimatrix_strictlyDominates_zero_iff u₁ u₂ a a')

/-- A strictly dominant strategy (Definition 8.B.1) for player 2. -/
theorem bimatrix_strictlyDominant_one_iff (b : Fin n) :
    StrictlyDominant (bimatrix u₁ u₂) 1 b ↔ ∀ b', b' ≠ b → ∀ a, u₂ a b' < u₂ a b := by
  exact (strictlyDominant_iff_dominates (bimatrix u₁ u₂) 1 b).trans
    (forall_congr' fun b' => imp_congr_right fun _ =>
      bimatrix_strictlyDominates_one_iff u₁ u₂ b b')

/-- Remaining strategy sets `A` (rows) and `B` (columns). -/
def ps {m n : ℕ} (A : Set (Fin m)) (B : Set (Fin n)) : (i : Fin 2) → Set (S2 m n i) :=
  Fin.cons A (Fin.cons B finZeroElim)

@[simp] theorem ps_zero {m n : ℕ} (A : Set (Fin m)) (B : Set (Fin n)) : ps A B 0 = A := rfl

@[simp] theorem ps_one {m n : ℕ} (A : Set (Fin m)) (B : Set (Fin n)) : ps A B 1 = B := rfl

/-- Strict domination within remaining sets, for player 1. -/
theorem bimatrix_sdominatedIn_zero_iff (A : Set (Fin m)) (B : Set (Fin n)) (a : Fin m) :
    SDominatedIn (bimatrix u₁ u₂) (ps A B) 0 a ↔ ∃ a' ∈ A, ∀ b ∈ B, u₁ a b < u₁ a' b := by
  constructor
  · rintro ⟨a', ha', h⟩
    refine ⟨a', ha', fun b hb => ?_⟩
    have := h (pp a b) fun j hj => by
      fin_cases j
      · exact absurd rfl hj
      · exact hb
    simpa using this
  · rintro ⟨a', ha', h⟩
    refine ⟨a', ha', fun r hr => ?_⟩
    simpa using h (r 1) (hr 1 (by decide))

/-- Strict domination within remaining sets, for player 2. -/
theorem bimatrix_sdominatedIn_one_iff (A : Set (Fin m)) (B : Set (Fin n)) (b : Fin n) :
    SDominatedIn (bimatrix u₁ u₂) (ps A B) 1 b ↔ ∃ b' ∈ B, ∀ a ∈ A, u₂ a b < u₂ a b' := by
  constructor
  · rintro ⟨b', hb', h⟩
    refine ⟨b', hb', fun a ha => ?_⟩
    have := h (pp a b) fun j hj => by
      fin_cases j
      · exact ha
      · exact absurd rfl hj
    simpa using this
  · rintro ⟨b', hb', h⟩
    refine ⟨b', hb', fun r hr => ?_⟩
    simpa using h (r 0) (hr 0 (by decide))

/-- A deletion step in a two-player table. -/
theorem bimatrix_sdStep_iff (A A' : Set (Fin m)) (B B' : Set (Fin n)) :
    SDStep (bimatrix u₁ u₂) (ps A B) (ps A' B') ↔
      (A' ⊆ A ∧ B' ⊆ B) ∧ (∀ a ∈ A, a ∉ A' → ∃ a' ∈ A, ∀ b ∈ B, u₁ a b < u₁ a' b) ∧
        ∀ b ∈ B, b ∉ B' → ∃ b' ∈ B, ∀ a ∈ A, u₂ a b < u₂ a b' := by
  unfold SDStep
  rw [Fin.forall_fin_two, Fin.forall_fin_two]
  exact and_congr Iff.rfl (and_congr
    (forall₂_congr fun a _ => imp_congr_right fun _ => bimatrix_sdominatedIn_zero_iff u₁ u₂ A B a)
    (forall₂_congr fun b _ => imp_congr_right fun _ => bimatrix_sdominatedIn_one_iff u₁ u₂ A B b))

/-- Completeness of a deletion process in a two-player table. -/
theorem bimatrix_sdTerminal_iff (A : Set (Fin m)) (B : Set (Fin n)) :
    SDTerminal (bimatrix u₁ u₂) (ps A B) ↔
      (∀ a ∈ A, ¬ ∃ a' ∈ A, ∀ b ∈ B, u₁ a b < u₁ a' b) ∧
        ∀ b ∈ B, ¬ ∃ b' ∈ B, ∀ a ∈ A, u₂ a b < u₂ a b' := by
  unfold SDTerminal
  rw [Fin.forall_fin_two]
  exact and_congr
    (forall₂_congr fun a _ => not_congr (bimatrix_sdominatedIn_zero_iff u₁ u₂ A B a))
    (forall₂_congr fun b _ => not_congr (bimatrix_sdominatedIn_one_iff u₁ u₂ A B b))

theorem fullSets_eq_ps : fullSets (S2 m n) = ps Set.univ Set.univ := by
  funext i
  fin_cases i <;> rfl

omit u₁ u₂ in
/-- **Section 7.E/8.D** for two players: `u_k(σ) = ∑_{a,b} σ₁(a) σ₂(b) u_k(a, b)`. -/
theorem mixedPayoff_fin_two {S : Fin 2 → Type*} [∀ i, Fintype (S i)] (N : NormalForm (Fin 2) S)
    (σ : (i : Fin 2) → S i → ℝ) (k : Fin 2) :
    N.mixedPayoff σ k = ∑ a : S 0, ∑ b : S 1, σ 0 a * σ 1 b *
      N.payoff k (Fin.cons a (Fin.cons b finZeroElim)) := by
  unfold NormalForm.mixedPayoff
  rw [← (piFinTwoEquiv S).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.prod_univ_two, piFinTwoEquiv]

/-- Mixed payoffs in a two-player table. -/
theorem bimatrix_mixedPayoff (σ : (i : Fin 2) → S2 m n i → ℝ) :
    (bimatrix u₁ u₂).mixedPayoff σ 0 = ∑ a : Fin m, ∑ b : Fin n, σ 0 a * σ 1 b * u₁ a b ∧
      (bimatrix u₁ u₂).mixedPayoff σ 1 = ∑ a : Fin m, ∑ b : Fin n, σ 0 a * σ 1 b * u₂ a b := by
  rw [mixedPayoff_fin_two, mixedPayoff_fin_two]
  exact ⟨rfl, rfl⟩

/-- Player 1's payoff from row `a` against player 2's mixed strategy. -/
theorem bimatrix_mixedPayoff_row (σ : (i : Fin 2) → S2 m n i → ℝ) (a : Fin m) :
    (bimatrix u₁ u₂).mixedPayoff (update σ 0 (pureMixed a)) 0 = ∑ b : Fin n, σ 1 b * u₁ a b := by
  rw [(bimatrix_mixedPayoff u₁ u₂ _).1]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hrow : (update σ 0 (pureMixed a) : (i : Fin 2) → S2 m n i → ℝ) 0 =
      fun a' : Fin m => if a' = a then (1 : ℝ) else 0 := by
    rw [update_self]; rfl
  rw [hrow, update_of_ne h10]
  simp [ite_mul]

/-- Player 2's payoff from column `b` against player 1's mixed strategy. -/
theorem bimatrix_mixedPayoff_col (σ : (i : Fin 2) → S2 m n i → ℝ) (b : Fin n) :
    (bimatrix u₁ u₂).mixedPayoff (update σ 1 (pureMixed b)) 1 = ∑ a : Fin m, σ 0 a * u₂ a b := by
  rw [(bimatrix_mixedPayoff u₁ u₂ _).2]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hcol : (update σ 1 (pureMixed b) : (i : Fin 2) → S2 m n i → ℝ) 1 =
      fun b' : Fin n => if b' = b then (1 : ℝ) else 0 := by
    rw [update_self]; rfl
  rw [hcol, update_of_ne h01]
  simp [ite_mul, mul_ite]

/-- A profile of mixed strategies in a two-player table from the two players' vectors. -/
def mp {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : (i : Fin 2) → S2 m n i → ℝ :=
  Fin.cons x (Fin.cons y finZeroElim)

@[simp] theorem mp_zero {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : mp x y 0 = x := rfl

@[simp] theorem mp_one {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : mp x y 1 = y := rfl

theorem isMixedProfile_mp {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) : IsMixedProfile (mp x y) := by
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- Mixed Nash equilibrium (Definition 8.D.2) in a two-player table: no profitable pure
deviation. -/
theorem bimatrix_isMixedNash_iff {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    IsMixedNash (bimatrix u₁ u₂) (mp x y) ↔
      (∀ a', ∑ b, y b * u₁ a' b ≤ ∑ a, ∑ b, x a * y b * u₁ a b) ∧
      ∀ b', ∑ a, x a * u₂ a b' ≤ ∑ a, ∑ b, x a * y b * u₂ a b := by
  rw [isMixedNash_iff_pure_deviations _ (isMixedProfile_mp hx hy)]
  constructor
  · intro h
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · have := h 0 a'
      rwa [bimatrix_mixedPayoff_row, (bimatrix_mixedPayoff u₁ u₂ _).1] at this
    · have := h 1 b'
      rwa [bimatrix_mixedPayoff_col, (bimatrix_mixedPayoff u₁ u₂ _).2] at this
  · rintro ⟨h1, h2⟩
    rw [Fin.forall_fin_two]
    refine ⟨fun a => ?_, fun b => ?_⟩
    · exact (bimatrix_mixedPayoff_row u₁ u₂ (mp x y) a).trans_le
        ((h1 a).trans_eq (bimatrix_mixedPayoff u₁ u₂ (mp x y)).1.symm)
    · exact (bimatrix_mixedPayoff_col u₁ u₂ (mp x y) b).trans_le
        ((h2 b).trans_eq (bimatrix_mixedPayoff u₁ u₂ (mp x y)).2.symm)

/-- Player 1's mixed strategy `τ` against player 2's pure strategy `b`. -/
theorem bimatrix_mixed_vs_pure_zero (τ : S2 m n 0 → ℝ) (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).mixedPayoff (update (pureProfile s) 0 τ) 0 =
      ∑ a : Fin m, τ a * u₁ a (s 1) := by
  rw [mixedPayoff_pureProfile_update_mixed]
  exact Finset.sum_congr rfl fun a _ => by simp [bimatrix, Function.update]

/-- Player 2's mixed strategy `τ` against player 1's pure strategy `a`. -/
theorem bimatrix_mixed_vs_pure_one (τ : S2 m n 1 → ℝ) (s : (i : Fin 2) → S2 m n i) :
    (bimatrix u₁ u₂).mixedPayoff (update (pureProfile s) 1 τ) 1 =
      ∑ b : Fin n, τ b * u₂ (s 0) b := by
  rw [mixedPayoff_pureProfile_update_mixed]
  exact Finset.sum_congr rfl fun b _ => by simp [bimatrix, Function.update]

/-- Strict domination of mixed strategies (Definition 8.B.4) for player 1, tested against the
columns. -/
theorem bimatrix_mixedStrictlyDominates_zero_iff [NeZero m] (τ' τ : Fin m → ℝ) :
    MixedStrictlyDominates (bimatrix u₁ u₂) 0 τ' τ ↔
      ∀ b, ∑ a, τ a * u₁ a b < ∑ a, τ' a * u₁ a b := by
  refine (mixedStrictlyDominates_iff_pure _ _ _ _).trans ⟨fun h b => ?_, fun h s => ?_⟩
  · have h1 := h (pp (0 : Fin m) b)
    have e1 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ (pp (0 : Fin m) b)
    have e2 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ' (pp (0 : Fin m) b)
    simp only [pp_one] at e1 e2
    linarith
  · have e1 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ s
    have e2 := bimatrix_mixed_vs_pure_zero u₁ u₂ τ' s
    have := h (s 1)
    linarith

/-- Strict domination of mixed strategies (Definition 8.B.4) for player 2, tested against the
rows. -/
theorem bimatrix_mixedStrictlyDominates_one_iff [NeZero n] (τ' τ : Fin n → ℝ) :
    MixedStrictlyDominates (bimatrix u₁ u₂) 1 τ' τ ↔
      ∀ a, ∑ b, τ b * u₂ a b < ∑ b, τ' b * u₂ a b := by
  refine (mixedStrictlyDominates_iff_pure _ _ _ _).trans ⟨fun h a => ?_, fun h s => ?_⟩
  · have h1 := h (pp a (0 : Fin n))
    have e1 := bimatrix_mixed_vs_pure_one u₁ u₂ τ (pp a (0 : Fin n))
    have e2 := bimatrix_mixed_vs_pure_one u₁ u₂ τ' (pp a (0 : Fin n))
    simp only [pp_zero] at e1 e2
    linarith
  · have e1 := bimatrix_mixed_vs_pure_one u₁ u₂ τ s
    have e2 := bimatrix_mixed_vs_pure_one u₁ u₂ τ' s
    have := h (s 0)
    linarith

/-- A row is a best response (Definition 8.C.1) to player 2's mixed strategy if no row does
better against it. -/
theorem bimatrix_isBestResponse_row (σ : (i : Fin 2) → S2 m n i → ℝ) (a : Fin m)
    (h : ∀ a', ∑ b : Fin n, σ 1 b * u₁ a' b ≤ ∑ b : Fin n, σ 1 b * u₁ a b) :
    IsBestResponse (bimatrix u₁ u₂) 0 (pureMixed a) σ := by
  refine isBestResponse_pureMixed_of_max _ 0 σ fun a' => ?_
  have e1 := bimatrix_mixedPayoff_row u₁ u₂ σ a
  have e2 := bimatrix_mixedPayoff_row u₁ u₂ σ a'
  have := h a'
  linarith

/-- A column is a best response (Definition 8.C.1) to player 1's mixed strategy if no column does
better against it. -/
theorem bimatrix_isBestResponse_col (σ : (i : Fin 2) → S2 m n i → ℝ) (b : Fin n)
    (h : ∀ b', ∑ a : Fin m, σ 0 a * u₂ a b' ≤ ∑ a : Fin m, σ 0 a * u₂ a b) :
    IsBestResponse (bimatrix u₁ u₂) 1 (pureMixed b) σ := by
  refine isBestResponse_pureMixed_of_max _ 1 σ fun b' => ?_
  have e1 := bimatrix_mixedPayoff_col u₁ u₂ σ b
  have e2 := bimatrix_mixedPayoff_col u₁ u₂ σ b'
  have := h b'
  linarith

/-- A mixed Nash equilibrium of a two-player table (Proposition 8.D.1): every row played with
positive probability is a best row against `y`, and every column played with positive probability
is a best column against `x`. -/
theorem bimatrix_isMixedNash_support {x : Fin m → ℝ} {y : Fin n → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    IsMixedNash (bimatrix u₁ u₂) (mp x y) ↔
      (∀ a, 0 < x a → ∀ a', ∑ b, y b * u₁ a' b ≤ ∑ b, y b * u₁ a b) ∧
      ∀ b, 0 < y b → ∀ b', ∑ a, x a * u₂ a b' ≤ ∑ a, x a * u₂ a b := by
  rw [isMixedNash_iff_bestResponse]
  simp only [isMixedProfile_mp hx hy, true_and]
  rw [Fin.forall_fin_two]
  refine and_congr ?_ ?_
  · refine (isBestResponse_iff_support _ 0 hx (mp x y)).trans (forall_congr' fun a =>
      imp_congr_right fun _ => forall_congr' fun a' => ?_)
    have e1 := bimatrix_mixedPayoff_row u₁ u₂ (mp x y) a
    have e2 := bimatrix_mixedPayoff_row u₁ u₂ (mp x y) a'
    constructor <;> intro h <;> simp only [mp_one] at e1 e2 <;> linarith
  · refine (isBestResponse_iff_support _ 1 hy (mp x y)).trans (forall_congr' fun b =>
      imp_congr_right fun _ => forall_congr' fun b' => ?_)
    have e1 := bimatrix_mixedPayoff_col u₁ u₂ (mp x y) b
    have e2 := bimatrix_mixedPayoff_col u₁ u₂ (mp x y) b'
    constructor <;> intro h <;> simp only [mp_zero] at e1 e2 <;> linarith

omit u₁ u₂ in
/-- Payoff of a row against a pure column, as a sum. -/
theorem sum_pureMixed_mul {k : ℕ} (b₀ : Fin k) (f : Fin k → ℝ) :
    ∑ b, pureMixed b₀ b * f b = f b₀ := by
  simp [pureMixed]

/-- Every mixed profile of a two-player table is `mp (σ 0) (σ 1)`. -/
theorem eq_mp (σ : (i : Fin 2) → S2 m n i → ℝ) : σ = mp (σ 0) (σ 1) := by
  funext i
  fin_cases i <;> rfl

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The examples of Section 8.B

MWG, Section 8.B, pp. 236-242. Rows and columns are numbered from `0` in the order printed.

* Figure 8.B.1, the Prisoner's Dilemma: "confess" is strictly dominant for both prisoners,
  `(confess, confess)` is a Nash equilibrium, and both prisoners prefer `(don't, don't)`.
* **Example 8.B.1** (Figure 8.B.2): no strictly dominant strategy; `D` is strictly dominated by
  `M` and by `U`.
* **Example 8.B.2** (Figure 8.B.3): `U` and `M` are weakly dominated by `D`. The small type of
  p. 240: iterated deletion of *weakly* dominated strategies depends on the order of deletion
  (`figure_8_B_3_order_dependence`).
* **Example 8.B.3** (Figure 8.B.4, the DA's Brother): neither of prisoner 1's strategies is
  dominated, but iterated strict dominance leaves only `(confess, confess)`.
* Figure 8.B.5 (pp. 241-242): no pure strategy dominates `M`, but `½U + ½D` does; with `M`
  paying `6` against both columns, neither `U` nor `D` is strictly dominated while `½U + ½D` is
  strictly dominated by `M`.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

/-! ### Figure 8.B.1: the Prisoner's Dilemma (row/column `0` = don't confess, `1` = confess) -/

/-- Prisoner 1's payoffs in Figure 8.B.1. -/
def pdU₁ : Fin 2 → Fin 2 → ℝ := ![![-2, -10], ![-1, -5]]

/-- Prisoner 2's payoffs in Figure 8.B.1. -/
def pdU₂ : Fin 2 → Fin 2 → ℝ := ![![-2, -1], ![-10, -5]]

/-- **Figure 8.B.1** (MWG, pp. 236-237). In the Prisoner's Dilemma "confess" is a strictly dominant
strategy for each prisoner. -/
theorem figure_8_B_1_confess_dominant :
    StrictlyDominant (bimatrix pdU₁ pdU₂) 0 (1 : Fin 2) ∧
      StrictlyDominant (bimatrix pdU₁ pdU₂) 1 (1 : Fin 2) := by
  refine ⟨(bimatrix_strictlyDominant_zero_iff _ _ _).2 ?_,
    (bimatrix_strictlyDominant_one_iff _ _ _).2 ?_⟩
  · intro a ha b
    fin_cases a
    · fin_cases b <;> norm_num [pdU₁]
    · exact absurd rfl ha
  · intro b hb a
    fin_cases b
    · fin_cases a <;> norm_num [pdU₂]
    · exact absurd rfl hb

/-- **Figure 8.B.1** (MWG, p. 237). `(confess, confess)` is a Nash equilibrium, yet both prisoners
prefer `(don't confess, don't confess)`; moving away from it, a prisoner gains one year and costs
his partner eight. -/
theorem figure_8_B_1_dilemma :
    IsNashEquilibrium (bimatrix pdU₁ pdU₂) (pp (1 : Fin 2) (1 : Fin 2)) ∧
      pdU₁ 1 1 < pdU₁ 0 0 ∧ pdU₂ 1 1 < pdU₂ 0 0 ∧
      pdU₁ 1 0 - pdU₁ 0 0 = 1 ∧ pdU₂ 1 0 - pdU₂ 0 0 = -8 := by
  refine ⟨(bimatrix_isNash_iff _ _ _ _).2 ⟨fun a => ?_, fun b => ?_⟩, ?_⟩
  · fin_cases a <;> norm_num [pdU₁]
  · fin_cases b <;> norm_num [pdU₂]
  · norm_num [pdU₁, pdU₂]

/-! ### Example 8.B.1 (Figure 8.B.2) -/

/-- Player 1's payoffs in Figure 8.B.2 (rows `U, M, D`, columns `L, R`). -/
def fig8B2U₁ : Fin 3 → Fin 2 → ℝ := ![![1, -1], ![-1, 1], ![-2, -3]]

/-- Player 2's payoffs in Figure 8.B.2. -/
def fig8B2U₂ : Fin 3 → Fin 2 → ℝ := ![![-1, 1], ![1, -1], ![5, 2]]

/-- **Example 8.B.1** (MWG, p. 237). In the game of Figure 8.B.2 there is no strictly dominant
strategy, and `D` is strictly dominated by `M` (and also by `U`). -/
theorem example_8_B_1 :
    (¬ ∃ a : Fin 3, StrictlyDominant (bimatrix fig8B2U₁ fig8B2U₂) 0 a) ∧
      (¬ ∃ b : Fin 2, StrictlyDominant (bimatrix fig8B2U₁ fig8B2U₂) 1 b) ∧
      StrictlyDominates (bimatrix fig8B2U₁ fig8B2U₂) 0 (1 : Fin 3) (2 : Fin 3) ∧
      StrictlyDominates (bimatrix fig8B2U₁ fig8B2U₂) 0 (0 : Fin 3) (2 : Fin 3) := by
  refine ⟨?_, ?_, (bimatrix_strictlyDominates_zero_iff _ _ _ _).2 fun b => ?_,
    (bimatrix_strictlyDominates_zero_iff _ _ _ _).2 fun b => ?_⟩
  · rintro ⟨a, ha⟩
    have h := (bimatrix_strictlyDominant_zero_iff _ _ a).1 ha
    fin_cases a
    · have := h 1 (by decide) 1; norm_num [fig8B2U₁] at this
    · have := h 0 (by decide) 0; norm_num [fig8B2U₁] at this
    · have := h 0 (by decide) 0; norm_num [fig8B2U₁] at this
  · rintro ⟨b, hb⟩
    have h := (bimatrix_strictlyDominant_one_iff _ _ b).1 hb
    fin_cases b
    · have := h 1 (by decide) 0; norm_num [fig8B2U₂] at this
    · have := h 0 (by decide) 1; norm_num [fig8B2U₂] at this
  · fin_cases b <;> norm_num [fig8B2U₁]
  · fin_cases b <;> norm_num [fig8B2U₁]

/-! ### Example 8.B.2 (Figure 8.B.3) and order dependence of weak deletion -/

/-- Player 1's payoffs in Figure 8.B.3 (rows `U, M, D`, columns `L, R`). -/
def fig8B3U₁ : Fin 3 → Fin 2 → ℝ := ![![5, 4], ![6, 3], ![6, 4]]

/-- Player 2's payoffs in Figure 8.B.3. -/
def fig8B3U₂ : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![4, 4]]

/-- **Example 8.B.2** (MWG, p. 238). In Figure 8.B.3 player 1's strategies `U` and `M` are both
weakly dominated by `D`. -/
theorem example_8_B_2 :
    WeaklyDominates (bimatrix fig8B3U₁ fig8B3U₂) 0 (2 : Fin 3) (0 : Fin 3) ∧
      WeaklyDominates (bimatrix fig8B3U₁ fig8B3U₂) 0 (2 : Fin 3) (1 : Fin 3) := by
  refine ⟨(bimatrix_weaklyDominates_zero_iff _ _ _ _).2 ⟨fun b => ?_, 0, by norm_num [fig8B3U₁]⟩,
    (bimatrix_weaklyDominates_zero_iff _ _ _ _).2 ⟨fun b => ?_, 1, by norm_num [fig8B3U₁]⟩⟩
  · fin_cases b <;> norm_num [fig8B3U₁]
  · fin_cases b <;> norm_num [fig8B3U₁]

/-- Within remaining sets `A` (rows) and `B` (columns), `a` is weakly dominated by a remaining
row. -/
def RowWeaklyDominatedIn {m n : ℕ} (u : Fin m → Fin n → ℝ) (A : Set (Fin m)) (B : Set (Fin n))
    (a : Fin m) : Prop :=
  ∃ a' ∈ A, (∀ b ∈ B, u a b ≤ u a' b) ∧ ∃ b ∈ B, u a b < u a' b

/-- Within remaining sets, the column `b` is weakly dominated by a remaining column. -/
def ColWeaklyDominatedIn {m n : ℕ} (u : Fin m → Fin n → ℝ) (A : Set (Fin m)) (B : Set (Fin n))
    (b : Fin n) : Prop :=
  ∃ b' ∈ B, (∀ a ∈ A, u a b ≤ u a b') ∧ ∃ a ∈ A, u a b < u a b'

/-- **Section 8.B** (MWG, p. 240, small type). One step of iterated deletion of weakly dominated
strategies in a two-player table: everything removed is weakly dominated in the remaining
game. -/
def WDStep2 {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (P Q : Set (Fin m) × Set (Fin n)) : Prop :=
  Q.1 ⊆ P.1 ∧ Q.2 ⊆ P.2 ∧ (∀ a ∈ P.1, a ∉ Q.1 → RowWeaklyDominatedIn u₁ P.1 P.2 a) ∧
    ∀ b ∈ P.2, b ∉ Q.2 → ColWeaklyDominatedIn u₂ P.1 P.2 b

/-- No remaining strategy is weakly dominated in the remaining game. -/
def WDTerminal2 {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (P : Set (Fin m) × Set (Fin n)) : Prop :=
  (∀ a ∈ P.1, ¬ RowWeaklyDominatedIn u₁ P.1 P.2 a) ∧
    ∀ b ∈ P.2, ¬ ColWeaklyDominatedIn u₂ P.1 P.2 b

/-- A singleton game has no weakly dominated strategies. -/
theorem wdTerminal2_singleton {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (a : Fin m) (b : Fin n) :
    WDTerminal2 u₁ u₂ ({a}, {b}) := by
  constructor
  · rintro x hx ⟨a', ha', -, b', -, hlt⟩
    simp only [Set.mem_singleton_iff] at hx ha'
    subst hx ha'
    exact lt_irrefl _ hlt
  · rintro y hy ⟨b', hb', -, a', -, hlt⟩
    simp only [Set.mem_singleton_iff] at hy hb'
    subst hy hb'
    exact lt_irrefl _ hlt

/-- **Section 8.B** (MWG, p. 240, small type). In Figure 8.B.3 iterated deletion of weakly dominated
strategies depends on the order of deletion: deleting `U`, then `L`, then `M` leaves `(D, R)`;
deleting `M`, then `R`, then `U` leaves `(D, L)`. Both are complete deletion processes. -/
theorem figure_8_B_3_order_dependence :
    let u₁ := fig8B3U₁
    let u₂ := fig8B3U₂
    Relation.ReflTransGen (WDStep2 u₁ u₂) (Set.univ, Set.univ) ({2}, {1}) ∧
      WDTerminal2 u₁ u₂ ({2}, {1}) ∧
      Relation.ReflTransGen (WDStep2 u₁ u₂) (Set.univ, Set.univ) ({2}, {0}) ∧
      WDTerminal2 u₁ u₂ ({2}, {0}) ∧ (({2}, {1}) : Set (Fin 3) × Set (Fin 2)) ≠ ({2}, {0}) := by
  intro u₁ u₂
  refine ⟨?_, wdTerminal2_singleton _ _ _ _, ?_, wdTerminal2_singleton _ _ _ _, ?_⟩
  · -- delete `U`, then `L`, then `M`
    refine Relation.ReflTransGen.head (b := ({1, 2}, Set.univ)) ?_ ?_
    · refine ⟨Set.subset_univ _, le_rfl, fun a _ ha => ⟨2, Set.mem_univ _, ?_⟩,
        fun b _ hb => absurd (Set.mem_univ b) hb⟩
      have : a = 0 := by fin_cases a <;> simp_all
      subst this
      exact ⟨fun b _ => by fin_cases b <;> norm_num [u₁, fig8B3U₁],
        0, Set.mem_univ _, by norm_num [u₁, fig8B3U₁]⟩
    refine Relation.ReflTransGen.head (b := ({1, 2}, {1})) ?_ ?_
    · refine ⟨le_rfl, Set.subset_univ _, fun a ha ha' => absurd ha ha', fun b _ hb => ?_⟩
      have : b = 0 := by fin_cases b <;> simp_all
      subst this
      refine ⟨1, Set.mem_univ _, fun a ha => ?_, 1, by simp, by norm_num [u₂, fig8B3U₂]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> norm_num [u₂, fig8B3U₂]
    refine Relation.ReflTransGen.single ⟨by simp, le_rfl, fun a ha ha' => ?_,
      fun b hb hb' => absurd hb hb'⟩
    have : a = 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ha'
      tauto
    subst this
    refine ⟨2, by simp, fun b hb => ?_, 1, rfl, by norm_num [u₁, fig8B3U₁]⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    norm_num [u₁, fig8B3U₁]
  · -- delete `M`, then `R`, then `U`
    refine Relation.ReflTransGen.head (b := ({0, 2}, Set.univ)) ?_ ?_
    · refine ⟨Set.subset_univ _, le_rfl, fun a _ ha => ⟨2, Set.mem_univ _, ?_⟩,
        fun b _ hb => absurd (Set.mem_univ b) hb⟩
      have : a = 1 := by fin_cases a <;> simp_all
      subst this
      exact ⟨fun b _ => by fin_cases b <;> norm_num [u₁, fig8B3U₁],
        1, Set.mem_univ _, by norm_num [u₁, fig8B3U₁]⟩
    refine Relation.ReflTransGen.head (b := ({0, 2}, {0})) ?_ ?_
    · refine ⟨le_rfl, Set.subset_univ _, fun a ha ha' => absurd ha ha', fun b _ hb => ?_⟩
      have : b = 1 := by fin_cases b <;> simp_all
      subst this
      refine ⟨0, Set.mem_univ _, fun a ha => ?_, 0, by simp, by norm_num [u₂, fig8B3U₂]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> norm_num [u₂, fig8B3U₂]
    refine Relation.ReflTransGen.single ⟨by simp, le_rfl, fun a ha ha' => ?_,
      fun b hb hb' => absurd hb hb'⟩
    have : a = 0 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ha'
      tauto
    subst this
    refine ⟨2, by simp, fun b hb => ?_, 0, rfl, by norm_num [u₁, fig8B3U₁]⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    norm_num [u₁, fig8B3U₁]
  · intro h
    have := congrArg Prod.snd h
    simp only [Set.singleton_eq_singleton_iff] at this
    exact absurd this (by decide)

/-! ### Example 8.B.3 (Figure 8.B.4): the DA's Brother -/

/-- Prisoner 1's payoffs in the DA's Brother (Figure 8.B.4). -/
def daU₁ : Fin 2 → Fin 2 → ℝ := ![![0, -10], ![-1, -5]]

/-- Prisoner 2's payoffs in the DA's Brother. -/
def daU₂ : Fin 2 → Fin 2 → ℝ := ![![-2, -1], ![-10, -5]]

/-- **Example 8.B.3** (MWG, pp. 238-239). In the DA's Brother neither of prisoner 1's strategies is
weakly (let alone strictly) dominated, while "don't confess" is strictly dominated for
prisoner 2. -/
theorem example_8_B_3_dominance :
    (∀ a : Fin 2, ¬ WeaklyDominated (bimatrix daU₁ daU₂) 0 a) ∧
      (∀ a : Fin 2, ¬ StrictlyDominated (bimatrix daU₁ daU₂) 0 a) ∧
      StrictlyDominates (bimatrix daU₁ daU₂) 1 (1 : Fin 2) (0 : Fin 2) := by
  have hw : ∀ a : Fin 2, ¬ WeaklyDominated (bimatrix daU₁ daU₂) 0 a := by
    rintro a ⟨a', ha'⟩
    have h := (bimatrix_weaklyDominates_zero_iff _ _ a' a).1 ha'
    fin_cases a <;> fin_cases a'
    · obtain ⟨b, hb⟩ := h.2; exact lt_irrefl _ hb
    · have := h.1 0
      simp [daU₁] at this
      linarith
    · have := h.1 1
      simp [daU₁] at this
      linarith
    · obtain ⟨b, hb⟩ := h.2; exact lt_irrefl _ hb
  refine ⟨hw, fun a ⟨a', ha'⟩ => hw a ⟨a', ha'.weaklyDominates (pp 0 0)⟩,
    (bimatrix_strictlyDominates_one_iff _ _ _ _).2 fun a => ?_⟩
  fin_cases a <;> norm_num [daU₂]

/-- **Example 8.B.3** (MWG, p. 239). Iterated deletion of strictly dominated strategies in the DA's
Brother: delete prisoner 2's "don't confess", then prisoner 1's "don't confess"; the unique
prediction `(confess, confess)` is the end of every complete process (Exercise 8.B.4) and a
Nash equilibrium. -/
theorem example_8_B_3 :
    Relation.ReflTransGen (SDStep (bimatrix daU₁ daU₂)) (fullSets _) (ps {1} {1}) ∧
      SDTerminal (bimatrix daU₁ daU₂) (ps {1} {1}) ∧
      (∀ T, Relation.ReflTransGen (SDStep (bimatrix daU₁ daU₂)) (fullSets _) T →
        SDTerminal (bimatrix daU₁ daU₂) T → T = ps {1} {1}) ∧
      IsNashEquilibrium (bimatrix daU₁ daU₂) (pp (1 : Fin 2) (1 : Fin 2)) := by
  have hchain : Relation.ReflTransGen (SDStep (bimatrix daU₁ daU₂)) (fullSets _)
      (ps {1} {1}) := by
    rw [fullSets_eq_ps]
    refine Relation.ReflTransGen.head (b := ps Set.univ {1}) ?_ ?_
    · refine (bimatrix_sdStep_iff _ _ _ _ _ _).2 ⟨⟨le_rfl, Set.subset_univ _⟩,
        fun a _ ha => absurd (Set.mem_univ a) ha, fun b _ hb => ⟨1, Set.mem_univ _, ?_⟩⟩
      have : b = 0 := by fin_cases b <;> simp_all
      subst this
      intro a _
      fin_cases a <;> norm_num [daU₂]
    · refine Relation.ReflTransGen.single ((bimatrix_sdStep_iff _ _ _ _ _ _).2
        ⟨⟨Set.subset_univ _, le_rfl⟩, fun a _ ha => ⟨1, Set.mem_univ _, ?_⟩,
          fun b hb hb' => absurd hb hb'⟩)
      have : a = 0 := by fin_cases a <;> simp_all
      subst this
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      norm_num [daU₁]
  have hterm : SDTerminal (bimatrix daU₁ daU₂) (ps {1} {1}) := by
    refine (bimatrix_sdTerminal_iff _ _ _ _).2 ⟨fun a ha ⟨a', ha', h⟩ => ?_,
      fun b hb ⟨b', hb', h⟩ => ?_⟩
    · rw [Set.mem_singleton_iff] at ha ha'
      subst ha ha'
      exact lt_irrefl _ (h 1 rfl)
    · rw [Set.mem_singleton_iff] at hb hb'
      subst hb hb'
      exact lt_irrefl _ (h 1 rfl)
  have hne : ∀ i, Nonempty (S2 2 2 i) := fun i => by fin_cases i <;> exact ⟨(0 : Fin 2)⟩
  refine ⟨hchain, hterm, fun T hT hTt => exercise_8_B_4 hT hTt hchain hterm, ?_⟩
  refine exercise_8_D_2 hchain fun i => ?_
  fin_cases i <;> rfl

/-! ### Figure 8.B.5: domination by a randomized strategy -/

/-- Player 1's payoffs in Figure 8.B.5(a) (rows `U, M, D`, columns `L, R`). -/
def fig8B5U₁ : Fin 3 → Fin 2 → ℝ := ![![10, 0], ![4, 4], ![0, 10]]

/-- Player 2's payoffs in Figure 8.B.5(a). -/
def fig8B5U₂ : Fin 3 → Fin 2 → ℝ := ![![1, 4], ![2, 3], ![5, 2]]

/-- The randomized strategy `½U + ½D`. -/
noncomputable def halfUD : Fin 3 → ℝ := ![1 / 2, 0, 1 / 2]

theorem isMixedStrategy_halfUD : IsMixedStrategy halfUD := by
  refine ⟨fun a => by fin_cases a <;> norm_num [halfUD], ?_⟩
  simp [halfUD, Fin.sum_univ_three]
  norm_num

/-- **Figure 8.B.5** (MWG, p. 241). None of `U`, `M`, `D` is strictly dominated by another pure
strategy, but `½U + ½D` (expected payoff `5` against both columns) strictly dominates `M`, so `M`
is strictly dominated in `[I, {Δ(S_i)}, {u_i(·)}]` (Proposition 8.B.1). -/
theorem figure_8_B_5 :
    (∀ a a' : Fin 3, ¬ StrictlyDominates (bimatrix fig8B5U₁ fig8B5U₂) 0 a' a) ∧
      MixedStrictlyDominates (bimatrix fig8B5U₁ fig8B5U₂) 0 halfUD (pureMixed (1 : Fin 3)) ∧
      MixedStrictlyDominated (bimatrix fig8B5U₁ fig8B5U₂) 0 (pureMixed (1 : Fin 3)) := by
  have hdom : MixedStrictlyDominates (bimatrix fig8B5U₁ fig8B5U₂) 0 halfUD
      (pureMixed (1 : Fin 3)) := by
    refine (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁ fig8B5U₂ halfUD
      (pureMixed (1 : Fin 3))).2 fun b => ?_
    fin_cases b <;> simp [Fin.sum_univ_three, halfUD, pureMixed, fig8B5U₁] <;> norm_num
  refine ⟨fun a a' h => ?_, hdom, ⟨halfUD, isMixedStrategy_halfUD, hdom⟩⟩
  have h' := (bimatrix_strictlyDominates_zero_iff _ _ a' a).1 h
  have h0 := h' 0
  have h1 := h' 1
  fin_cases a <;> fin_cases a' <;> simp [fig8B5U₁] at h0 h1 <;> linarith

/-- Player 1's payoffs when `M` pays `6` against both columns (p. 242). -/
def fig8B5U₁' : Fin 3 → Fin 2 → ℝ := ![![10, 0], ![6, 6], ![0, 10]]

/-- **Section 8.B** (MWG, p. 242). If `M` pays `6` against either column, neither `U` nor `D` is
strictly dominated (even by a mixed strategy), but `½U + ½D` is strictly dominated by `M`. -/
theorem figure_8_B_5_variant :
    ¬ MixedStrictlyDominated (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (0 : Fin 3)) ∧
      ¬ MixedStrictlyDominated (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (2 : Fin 3)) ∧
      MixedStrictlyDominates (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (1 : Fin 3)) halfUD := by
  refine ⟨fun ⟨(τ : Fin 3 → ℝ), hτ, h⟩ => ?_, fun ⟨(τ : Fin 3 → ℝ), hτ, h⟩ => ?_,
    (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁' fig8B5U₂ (pureMixed (1 : Fin 3))
      halfUD).2 fun b => ?_⟩
  · have h0 := (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁' fig8B5U₂ τ
      (pureMixed (0 : Fin 3))).1 h 0
    have hs : ∑ a : Fin 3, τ a = 1 := hτ.2
    simp only [Fin.sum_univ_three] at h0 hs
    simp [pureMixed, fig8B5U₁'] at h0
    nlinarith [hτ.1 (0 : Fin 3), hτ.1 (1 : Fin 3), hτ.1 (2 : Fin 3)]
  · have h1 := (bimatrix_mixedStrictlyDominates_zero_iff fig8B5U₁' fig8B5U₂ τ
      (pureMixed (2 : Fin 3))).1 h 1
    have hs : ∑ a : Fin 3, τ a = 1 := hτ.2
    simp only [Fin.sum_univ_three] at h1 hs
    simp [pureMixed, fig8B5U₁'] at h1
    nlinarith [hτ.1 (0 : Fin 3), hτ.1 (1 : Fin 3), hτ.1 (2 : Fin 3)]
  · fin_cases b <;> simp [Fin.sum_univ_three, halfUD, pureMixed, fig8B5U₁'] <;> norm_num

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The examples of Sections 8.C and 8.D

MWG, pp. 244-252, and Exercise 8.D.1 (p. 263). Rows and columns are numbered from `0`.

* **Example 8.C.1** (Figure 8.C.1, Bernheim's game): `a₁, a₂, a₃` and `b₁, b₂, b₃` are
  rationalizable (each is a best response to one of the others), `b₄` is strictly dominated by
  `½b₁ + ½b₃`, `a₄` is strictly dominated by `a₂` once `b₄` is deleted, and neither `a₄` nor `b₄`
  is rationalizable.
* Figure 8.C.2 (p. 245): when `M` in Figure 8.B.5 pays `6` against both columns it is a best
  response to `σ₂(R) = ½`.
* **Example 8.D.1** (Figure 8.D.1): `(M, m)` is the only pure Nash equilibrium.
* **Example 8.D.2**: `(a₂, b₂)` is the only pure Nash equilibrium of Figure 8.C.1, and
  **Exercise 8.D.1**: it is the only mixed one.
* **Example 8.D.3** (Meeting in New York): two pure equilibria; with Grand Central paying
  `1000` (the focal-point discussion, p. 248) both remain equilibria. **Example 8.D.5**: going to
  Grand Central with probability `1/11` is a mixed equilibrium, and `1/11` is the only
  probability that makes a player indifferent.
* The correlated-equilibrium remark (p. 252): following a public signal to `(Empire State, Empire
  State)` or `(Grand Central, Grand Central)` is self-enforcing.
* **Example 8.D.4** (Figure 8.D.3, Chapter 7's `matchingPennies`): no pure equilibrium; each
  player mixing `½`-`½` is a mixed equilibrium.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

/-! ### Example 8.C.1 (Figure 8.C.1) -/

/-- Player 1's payoffs in Figure 8.C.1 (rows `a₁, …, a₄`, columns `b₁, …, b₄`). -/
def fig8C1U₁ : Fin 4 → Fin 4 → ℝ :=
  ![![0, 2, 7, 0], ![5, 3, 5, 0], ![7, 2, 0, 0], ![0, 0, 0, 10]]

/-- Player 2's payoffs in Figure 8.C.1. -/
def fig8C1U₂ : Fin 4 → Fin 4 → ℝ :=
  ![![7, 5, 0, 1], ![2, 3, 2, 1], ![0, 5, 7, 1], ![0, -2, 0, -1]]

/-- The game of Figure 8.C.1. -/
abbrev bernheim : NormalForm (Fin 2) (S2 4 4) := bimatrix fig8C1U₁ fig8C1U₂

/-- The randomized strategy `½b₁ + ½b₃`. -/
noncomputable def halfB13 : Fin 4 → ℝ := ![1 / 2, 0, 1 / 2, 0]

theorem isMixedStrategy_halfB13 : IsMixedStrategy halfB13 := by
  refine ⟨fun a => by fin_cases a <;> norm_num [halfB13], ?_⟩
  simp [halfB13, Fin.sum_univ_four]
  norm_num

/-- **Example 8.C.1** (MWG, p. 244). `b₄` is strictly dominated by `½b₁ + ½b₃`; once `b₄` is
deleted, `a₄` is strictly dominated by `a₂`. -/
theorem example_8_C_1_dominance :
    MixedStrictlyDominates bernheim 1 halfB13 (pureMixed (3 : Fin 4)) ∧
      ∀ b : Fin 4, b ≠ 3 → fig8C1U₁ 3 b < fig8C1U₁ 1 b := by
  refine ⟨(bimatrix_mixedStrictlyDominates_one_iff fig8C1U₁ fig8C1U₂ halfB13
    (pureMixed (3 : Fin 4))).2 fun a => ?_, fun b hb => ?_⟩
  · fin_cases a <;> simp [Fin.sum_univ_four, halfB13, pureMixed, fig8C1U₂] <;> norm_num
  · fin_cases b <;> simp_all [fig8C1U₁]

/-- The pure strategies of Figure 8.C.1 claimed rationalizable: `a₁, a₂, a₃` and `b₁, b₂, b₃`. -/
def bernheimSet : (i : Fin 2) → Set (S2 4 4 i → ℝ) :=
  Fin.cons {pureMixed (0 : Fin 4), pureMixed (1 : Fin 4), pureMixed (2 : Fin 4)}
    (Fin.cons {pureMixed (0 : Fin 4), pureMixed (1 : Fin 4), pureMixed (2 : Fin 4)} finZeroElim)

/-- **Example 8.C.1** (MWG, p. 244). `a₁, a₂, a₃` are rationalizable for player 1 and `b₁, b₂, b₃`
for player 2: `a₁` is a best response to `b₃`, `a₂` to `b₂`, `a₃` to `b₁`, and `b₁, b₂, b₃` are
best responses to `a₁, a₂, a₃`. -/
theorem example_8_C_1_rationalizable (k : Fin 3) :
    Rationalizable bernheim 0 (pureMixed (k.castSucc : Fin 4)) ∧
      Rationalizable bernheim 1 (pureMixed (k.castSucc : Fin 4)) := by
  have hΔ : ∀ i, bernheimSet i ⊆ mixedExtension (S2 4 4 i) := by
    intro i τ hτ
    fin_cases i <;>
    · simp only [bernheimSet] at hτ
      rcases hτ with rfl | rfl | rfl <;> exact isMixedStrategy_pureMixed _
  -- player 1's rows against a pure column, and player 2's columns against a pure row
  have hBR : ∀ i, ∀ τ ∈ bernheimSet i, BRToSome bernheim bernheimSet i τ := by
    intro i
    fin_cases i
    · intro τ hτ
      simp only [bernheimSet] at hτ
      -- `a₁` against `b₃`, `a₂` against `b₂`, `a₃` against `b₁`
      obtain ⟨a, b, rfl, hab⟩ : ∃ a b : Fin 4, τ = pureMixed a ∧ b ≠ 3 ∧
          ∀ a', fig8C1U₁ a' b ≤ fig8C1U₁ a b := by
        rcases hτ with rfl | rfl | rfl
        · exact ⟨0, 2, rfl, by decide, fun a' => by fin_cases a' <;> norm_num [fig8C1U₁]⟩
        · exact ⟨1, 1, rfl, by decide, fun a' => by fin_cases a' <;> norm_num [fig8C1U₁]⟩
        · exact ⟨2, 0, rfl, by decide, fun a' => by fin_cases a' <;> norm_num [fig8C1U₁]⟩
      refine ⟨mp (pureMixed a) (pureMixed b), isMixedProfile_mp (isMixedStrategy_pureMixed _)
        (isMixedStrategy_pureMixed _), fun j hj => ?_, ?_⟩
      · have : j = 1 := by fin_cases j <;> simp_all
        subst this
        simp only [bernheimSet, mp_one]
        change pureMixed b ∈ ({pureMixed 0, pureMixed 1, pureMixed 2} : Set (Fin 4 → ℝ))
        have hb := hab.1
        fin_cases b <;> simp_all
      · refine bimatrix_isBestResponse_row _ _ _ a fun a' => ?_
        simp only [mp_one, sum_pureMixed_mul]
        exact hab.2 a'
    · intro τ hτ
      simp only [bernheimSet] at hτ
      obtain ⟨b, a, rfl, hab⟩ : ∃ b a : Fin 4, τ = pureMixed b ∧ a ≠ 3 ∧
          ∀ b', fig8C1U₂ a b' ≤ fig8C1U₂ a b := by
        rcases hτ with rfl | rfl | rfl
        · exact ⟨0, 0, rfl, by decide, fun b' => by fin_cases b' <;> norm_num [fig8C1U₂]⟩
        · exact ⟨1, 1, rfl, by decide, fun b' => by fin_cases b' <;> norm_num [fig8C1U₂]⟩
        · exact ⟨2, 2, rfl, by decide, fun b' => by fin_cases b' <;> norm_num [fig8C1U₂]⟩
      refine ⟨mp (pureMixed a) (pureMixed b), isMixedProfile_mp (isMixedStrategy_pureMixed _)
        (isMixedStrategy_pureMixed _), fun j hj => ?_, ?_⟩
      · have : j = 0 := by fin_cases j <;> simp_all
        subst this
        simp only [bernheimSet, mp_zero]
        change pureMixed a ∈ ({pureMixed 0, pureMixed 1, pureMixed 2} : Set (Fin 4 → ℝ))
        have ha := hab.1
        fin_cases a <;> simp_all
      · refine bimatrix_isBestResponse_col _ _ _ b fun b' => ?_
        simp only [mp_zero, sum_pureMixed_mul]
        exact hab.2 b'
  have hmem : pureMixed (k.castSucc : Fin 4) ∈
      ({pureMixed 0, pureMixed 1, pureMixed 2} : Set (Fin 4 → ℝ)) := by
    fin_cases k <;> simp
  exact ⟨rationalizable_of_bestResponseSet (i := 0) hΔ hBR hmem,
    rationalizable_of_bestResponseSet (i := 1) hΔ hBR hmem⟩

/-- In Figure 8.C.1, every best response of player 2 puts zero weight on `b₄`. -/
theorem bernheim_bestResponse_b4 {σ : (i : Fin 2) → S2 4 4 i → ℝ} (hσ : IsMixedProfile σ)
    {τ : Fin 4 → ℝ} (hτ : IsBestResponse bernheim 1 τ σ) : τ 3 = 0 := by
  have hτm : IsMixedStrategy τ := hτ.1
  by_contra hne
  have hpos : 0 < τ 3 := lt_of_le_of_ne (hτm.1 3) (Ne.symm hne)
  have hsupp := (isBestResponse_iff_support bernheim 1 hτ.1 σ).1 hτ (3 : Fin 4) hpos
  -- `b₄` does strictly worse than `½b₁ + ½b₃` against `σ₁`
  have hlt := example_8_C_1_dominance.1 σ hσ
  have hle := mixedPayoff_le_of_pure_le bernheim σ 1 isMixedStrategy_halfB13 1 hsupp
  linarith

/-- **Example 8.C.1** (MWG, p. 244). `b₄` and `a₄` are not rationalizable: `b₄` is never a best
response, and `a₄` is not a best response to any of player 2's strategies that survive the first
round. -/
theorem example_8_C_1_not_rationalizable :
    ¬ Rationalizable bernheim 1 (pureMixed (3 : Fin 4)) ∧
      ¬ Rationalizable bernheim 0 (pureMixed (3 : Fin 4)) := by
  constructor
  · intro h
    obtain ⟨-, σ, hσ, -, hbr⟩ := h 1
    have : (pureMixed (3 : Fin 4) : Fin 4 → ℝ) 3 = 0 := bernheim_bestResponse_b4 hσ hbr
    simp [pureMixed] at this
  · intro h
    obtain ⟨-, σ, hσ, hσT, hbr⟩ := h 2
    obtain ⟨-, ρ, hρ, -, hbr₂⟩ := hσT 1 (by decide)
    have h3 := bernheim_bestResponse_b4 hρ hbr₂
    -- `a₂` does better than `a₄` against `σ₂`
    have hle := hbr.2 _ (isMixedStrategy_pureMixed (1 : Fin 4))
    have e1 := bimatrix_mixedPayoff_row fig8C1U₁ fig8C1U₂ σ (1 : Fin 4)
    have e2 := bimatrix_mixedPayoff_row fig8C1U₁ fig8C1U₂ σ (3 : Fin 4)
    have hm : IsMixedStrategy (σ 1 : Fin 4 → ℝ) := hσ 1
    set τ : Fin 4 → ℝ := σ 1 with hτdef
    have hs : ∑ b : Fin 4, τ b = 1 := hm.2
    have hm0 : ∀ b : Fin 4, 0 ≤ τ b := hm.1
    rw [Fin.sum_univ_four] at hs
    have E1 : ∑ b : Fin 4, τ b * fig8C1U₁ 1 b = 5 * τ 0 + 3 * τ 1 + 5 * τ 2 := by
      simp [Fin.sum_univ_four, fig8C1U₁]
      ring
    have E2 : ∑ b : Fin 4, τ b * fig8C1U₁ 3 b = 10 * τ 3 := by
      simp [Fin.sum_univ_four, fig8C1U₁, mul_comm]
    have key : ∑ b : Fin 4, τ b * fig8C1U₁ 1 b ≤ ∑ b : Fin 4, τ b * fig8C1U₁ 3 b :=
      e1.symm.trans_le (hle.trans_eq e2)
    linarith [hm0 0, hm0 1, hm0 2]

/-! ### Figure 8.C.2 -/

/-- **Figure 8.C.2** (MWG, p. 245). If `M` pays `6` against both columns in Figure 8.B.5, it is not
strictly dominated and is a best response to `σ₂(R) = ½`. -/
theorem figure_8_C_2 :
    IsBestResponse (bimatrix fig8B5U₁' fig8B5U₂) 0 (pureMixed (1 : Fin 3))
      (mp halfUD ![1 / 2, 1 / 2]) := by
  refine bimatrix_isBestResponse_row _ _ _ 1 fun a' => ?_
  simp only [mp_one]
  fin_cases a' <;> simp [Fin.sum_univ_two, fig8B5U₁'] <;> norm_num

/-! ### Example 8.D.1 (Figure 8.D.1) -/

/-- Player 1's payoffs in Figure 8.D.1 (rows `U, M, D`, columns `ℓ, m, r`). -/
def fig8D1U₁ : Fin 3 → Fin 3 → ℝ := ![![5, 0, 3], ![4, 5, 4], ![3, 0, 5]]

/-- Player 2's payoffs in Figure 8.D.1. -/
def fig8D1U₂ : Fin 3 → Fin 3 → ℝ := ![![3, 4, 5], ![0, 5, 0], ![5, 4, 3]]

/-- **Example 8.D.1** (MWG, p. 246). `(M, m)` is the only pure strategy Nash equilibrium of the
game in Figure 8.D.1. -/
theorem example_8_D_1 (a b : Fin 3) :
    IsNashEquilibrium (bimatrix fig8D1U₁ fig8D1U₂) (pp a b) ↔ a = 1 ∧ b = 1 := by
  rw [bimatrix_isNash_iff]
  fin_cases a <;> fin_cases b <;> simp [Fin.forall_fin_succ, fig8D1U₁, fig8D1U₂] <;> norm_num

/-- **Example 8.D.2** (MWG, p. 246). `(a₂, b₂)` is the only pure strategy Nash equilibrium of the
game in Figure 8.C.1. -/
theorem example_8_D_2 (a b : Fin 4) :
    IsNashEquilibrium bernheim (pp a b) ↔ a = 1 ∧ b = 1 := by
  rw [bimatrix_isNash_iff]
  fin_cases a <;> fin_cases b <;> simp [Fin.forall_fin_succ, fig8C1U₁, fig8C1U₂] <;> norm_num

/-- **Exercise 8.D.1** (MWG, p. 263). `(a₂, b₂)` played with certainty is the unique mixed strategy
Nash equilibrium of the game in Figure 8.C.1. -/
theorem exercise_8_D_1 {x y : Fin 4 → ℝ} (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    IsMixedNash bernheim (mp x y) ↔ x = pureMixed 1 ∧ y = pureMixed 1 := by
  rw [bimatrix_isMixedNash_support _ _ hx hy]
  have hx0 := hx.1
  have hy0 := hy.1
  have hxs : x 0 + x 1 + x 2 + x 3 = 1 := by simpa [Fin.sum_univ_four] using hx.2
  have hys : y 0 + y 1 + y 2 + y 3 = 1 := by simpa [Fin.sum_univ_four] using hy.2
  -- the payoffs of the rows against `y` and of the columns against `x`
  have hrow : ∀ a', ∑ b, y b * fig8C1U₁ a' b =
      ![2 * y 1 + 7 * y 2, 5 * y 0 + 3 * y 1 + 5 * y 2, 7 * y 0 + 2 * y 1, 10 * y 3] a' := by
    intro a'
    fin_cases a' <;> simp [Fin.sum_univ_four, fig8C1U₁] <;> ring
  have hcol : ∀ b', ∑ a, x a * fig8C1U₂ a b' =
      ![7 * x 0 + 2 * x 1, 5 * x 0 + 3 * x 1 + 5 * x 2 - 2 * x 3, 2 * x 1 + 7 * x 2,
        x 0 + x 1 + x 2 - x 3] b' := by
    intro b'
    fin_cases b' <;> simp [Fin.sum_univ_four, fig8C1U₂] <;> ring
  simp only [hrow, hcol]
  constructor
  · rintro ⟨h1, h2⟩
    have nx : ∀ a, x a ≤ 0 ∨ 0 < x a := fun a => le_or_gt _ _
    have ny : ∀ b, y b ≤ 0 ∨ 0 < y b := fun b => le_or_gt _ _
    -- `b₄` is never used, then `a₄` is never used
    have y3 : y 3 = 0 := by
      rcases ny 3 with h | h
      · exact le_antisymm h (hy0 3)
      · have c0 := h2 3 h 0
        have c2 := h2 3 h 2
        simp at c0 c2
        linarith [hx0 0, hx0 1, hx0 2, hx0 3]
    have x3 : x 3 = 0 := by
      rcases nx 3 with h | h
      · exact le_antisymm h (hx0 3)
      · have r1 := h1 3 h 1
        simp at r1
        linarith [hy0 0, hy0 1, hy0 2, hy0 3]
    -- `a₁` is never used
    have x0 : x 0 = 0 := by
      rcases nx 0 with h | h
      · exact le_antisymm h (hx0 0)
      · have r1 := h1 0 h 1
        have r2 := h1 0 h 2
        simp at r1 r2
        have hy2 : 0 < y 2 := by
          by_contra hle
          push Not at hle
          linarith [hy0 0, hy0 1]
        have c1 := h2 2 hy2 1
        simp at c1
        have hx2 : 0 < x 2 := by linarith [hx0 1]
        have r0 := h1 2 hx2 0
        simp at r0
        linarith [hy0 0, hy0 1, hy0 2]
    -- `a₃` is never used
    have x2 : x 2 = 0 := by
      rcases nx 2 with h | h
      · exact le_antisymm h (hx0 2)
      · have r1 := h1 2 h 1
        simp at r1
        have hy0' : 0 < y 0 := by linarith [hy0 1, hy0 2]
        have c1 := h2 0 hy0' 1
        simp at c1
        linarith [hx0 1]
    have x1 : x 1 = 1 := by linarith
    have hy' : ∀ b, b ≠ 1 → y b = 0 := by
      intro b hb
      rcases ny b with h | h
      · exact le_antisymm h (hy0 b)
      · have c := h2 b h 1
        fin_cases b
        · simp at c; linarith
        · exact absurd rfl hb
        · simp at c; linarith
        · exact y3
    have y0 := hy' 0 (by decide)
    have y2 := hy' 2 (by decide)
    have y1 : y 1 = 1 := by linarith
    refine ⟨funext fun a => ?_, funext fun b => ?_⟩
    · fin_cases a <;> simp [pureMixed, x0, x1, x2, x3]
    · fin_cases b <;> simp [pureMixed, y0, y1, y2, y3]
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
    · have : a = 1 := by by_contra h; simp [pureMixed, h] at ha
      subst this
      fin_cases a' <;> simp [pureMixed] <;> norm_num
    · have : b = 1 := by by_contra h; simp [pureMixed, h] at hb
      subst this
      fin_cases b' <;> simp [pureMixed] <;> norm_num

/-! ### Examples 8.D.3 and 8.D.5: Meeting in New York (`0` = Empire State, `1` = Grand Central) -/

/-- The Meeting in New York payoffs with values `v₀` at Empire State and `v₁` at Grand Central. -/
def meetNY (v₀ v₁ : ℝ) : Fin 2 → Fin 2 → ℝ := ![![v₀, 0], ![0, v₁]]

/-- **Example 8.D.3** (MWG, p. 247). In the Meeting in New York game (Figure 8.D.2, payoffs `100`)
the pure Nash equilibria are exactly (Empire State, Empire State) and (Grand Central, Grand
Central); with the focal payoff `1000` at Grand Central (p. 248) the same two profiles are the
pure equilibria. -/
theorem example_8_D_3 {v₀ v₁ : ℝ} (h₀ : 0 < v₀) (h₁ : 0 < v₁) (a b : Fin 2) :
    IsNashEquilibrium (bimatrix (meetNY v₀ v₁) (meetNY v₀ v₁)) (pp a b) ↔ a = b := by
  rw [bimatrix_isNash_iff]
  constructor
  · rintro ⟨h1, h2⟩
    fin_cases a <;> fin_cases b
    · rfl
    · have := h1 1; simp [meetNY] at this; linarith
    · have := h1 0; simp [meetNY] at this; linarith
    · rfl
  · rintro rfl
    refine ⟨fun a' => ?_, fun b' => ?_⟩ <;> fin_cases a <;>
      first | (fin_cases a' <;> simp [meetNY, h₀.le, h₁.le])
            | (fin_cases b' <;> simp [meetNY, h₀.le, h₁.le])

/-- **Example 8.D.3** (MWG, p. 247), the instance of Figure 8.D.2 (`100` at both places). -/
theorem example_8_D_3_figure (a b : Fin 2) :
    IsNashEquilibrium (bimatrix (meetNY 100 100) (meetNY 100 100)) (pp a b) ↔ a = b :=
  example_8_D_3 (by norm_num) (by norm_num) a b

/-- **Example 8.D.5** (MWG, p. 251). With payoffs `100` at Empire State and `1000` at Grand Central,
Mr. Thomas is indifferent between the two places exactly when Mr. Schelling goes to Grand Central
with probability `1/11`. -/
theorem example_8_D_5_indifference (σ : ℝ) :
    1000 * σ + 0 * (1 - σ) = 100 * (1 - σ) + 0 * σ ↔ σ = 1 / 11 := by
  constructor <;> intro h <;> linarith

/-- **Example 8.D.5** (MWG, p. 251). Each player going to Grand Central with probability `1/11` is a
mixed strategy Nash equilibrium of the Meeting in New York game with Grand Central paying
`1000`. -/
theorem example_8_D_5 :
    IsMixedNash (bimatrix (meetNY 100 1000) (meetNY 100 1000))
      (mp ![10 / 11, 1 / 11] ![10 / 11, 1 / 11]) := by
  have hm : IsMixedStrategy (![10 / 11, 1 / 11] : Fin 2 → ℝ) := by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]
    norm_num
  rw [bimatrix_isMixedNash_iff _ _ hm hm]
  refine ⟨fun a' => ?_, fun b' => ?_⟩ <;>
  · first | fin_cases a' | fin_cases b'
    all_goals simp [Fin.sum_univ_two, meetNY]; norm_num

/-- **Section 8.D** (MWG, p. 252, small type). With a public signal telling both players to go to
the same place (each place with probability `½`), following the signal is optimal for each player
whatever he is told: a correlated equilibrium in which the players always meet. -/
theorem meetNY_correlated (a a' : Fin 2) :
    meetNY 100 100 a' a ≤ meetNY 100 100 a a ∧
      (∑ b : Fin 2, (1 / 2 : ℝ) * meetNY 100 100 b b) = 100 := by
  constructor
  · fin_cases a <;> fin_cases a' <;> norm_num [meetNY]
  · simp [Fin.sum_univ_two, meetNY]
    norm_num

/-! ### Example 8.D.4: Matching Pennies (Chapter 7's `matchingPennies`, Figure 8.D.3) -/

/-- **Example 8.D.4** (MWG, p. 250). Matching Pennies has no pure strategy Nash equilibrium. -/
theorem example_8_D_4_no_pure (s : (i : Fin 2) → Fin 2) :
    ¬ IsNashEquilibrium matchingPennies s := by
  intro h
  have h0 := h 0
  have h1 := h 1
  have hs : s = ![s 0, s 1] := by funext i; fin_cases i <;> rfl
  rw [hs] at h0 h1
  generalize s 0 = a at h0 h1
  generalize s 1 = b at h0 h1
  fin_cases a <;> fin_cases b
  · have := h0 1; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this
  · have := h1 0; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this
  · have := h1 1; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this
  · have := h0 0; simp [matchingPennies, mpPay, Function.update] at this; norm_num at this

/-- **Example 8.D.4** (MWG, p. 250). Each player choosing heads and tails with equal probability is
a mixed strategy Nash equilibrium of Matching Pennies. -/
theorem example_8_D_4 : IsMixedNash matchingPennies (fun _ _ => 1 / 2) := by
  have hm : IsMixedProfile (fun (_ : Fin 2) (_ : Fin 2) => (1 / 2 : ℝ)) := fun _ =>
    ⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_two]⟩
  rw [isMixedNash_iff_pure_deviations _ hm]
  intro i b
  rw [mixedPayoff_fin_two, mixedPayoff_fin_two]
  fin_cases i <;> fin_cases b <;>
    norm_num [Fin.sum_univ_two, matchingPennies, mpPay, pureMixed, Function.update]

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Games of incomplete information: Bayesian Nash equilibrium

MWG, Section 8.E, pp. 253-257.

A Bayesian game `[I, {S_i}, {u_i(·)}, Θ, F(·)]` has finitely many types `Θ_i` for each player
(footnote 8 restricts Proposition 8.E.1 to this case), a prior `F` on `Θ = Θ_1 × ⋯ × Θ_I`, and
payoffs `u_i(s, θ)`. MWG write `u_i(s_i, s_{-i}, θ_i)`; the payoffs here may depend on the whole
type profile `θ` (needed in Exercise 8.E.1), which contains MWG's case (correction 4).

* `expectedPayoff`, (8.E.1): `ũ_i(s_1(·), …, s_I(·)) = E_θ[u_i(s_1(θ_1), …, s_I(θ_I), θ)]`;
  `toNormalForm` is the game `[I, {𝒮_i}, {ũ_i(·)}]` whose strategies are decision rules.
* **Definition 8.E.1** (`IsBNE`): a Nash equilibrium of that game.
* **Proposition 8.E.1** (`proposition_8_E_1`): with finitely many types, `s(·)` is a Bayesian
  Nash equilibrium iff every type of every player that occurs with positive probability plays a
  best response to the conditional distribution of the others' strategies (8.E.2).
* With finitely many strategies and types a mixed strategy Bayesian Nash equilibrium exists
  (`exists_mixed_BNE`, Proposition 8.D.2 applied to `toNormalForm`).
* **Example 8.E.1** (`example_8_E_1`): the DA's Brother with incomplete information: type I of
  prisoner 2 confesses, type II does not, and prisoner 1 does not confess if `μ < 1/6` and
  confesses if `μ > 1/6`.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- **Section 8.E** (MWG, p. 255). A Bayesian game: a prior `F` on type profiles `θ ∈ Θ` and
payoffs `u_i(s, θ)`. -/
structure BayesianGame (I : Type*) (S Θ : I → Type*) where
  /-- The joint distribution `F(θ_1, …, θ_I)` of the types (a probability vector). -/
  prior : ((i : I) → Θ i) → ℝ
  /-- Player `i`'s payoff `u_i(s, θ)` at the strategy profile `s` and type profile `θ`. -/
  payoff : I → ((i : I) → S i) → ((i : I) → Θ i) → ℝ

variable {I : Type*} {S Θ : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)]

namespace BayesianGame

/-- The prior is a probability distribution. -/
def IsPrior (G : BayesianGame I S Θ) : Prop :=
  (∀ θ, 0 ≤ G.prior θ) ∧ ∑ θ, G.prior θ = 1

/-- The strategies actually played at the type profile `θ` under the decision rules `s(·)`. -/
def play (s : (i : I) → Θ i → S i) (θ : (i : I) → Θ i) : (i : I) → S i := fun j => s j (θ j)

/-- **(8.E.1)** (MWG, p. 255). Player `i`'s expected payoff
`ũ_i(s_1(·), …, s_I(·)) = E_θ[u_i(s_1(θ_1), …, s_I(θ_I), θ)]`. -/
def expectedPayoff (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I) : ℝ :=
  ∑ θ, G.prior θ * G.payoff i (play s θ) θ

/-- **Section 8.E** (MWG, p. 255). The normal form `[I, {𝒮_i}, {ũ_i(·)}]` of a Bayesian game: pure
strategies are decision rules `s_i : Θ_i → S_i`. -/
def toNormalForm (G : BayesianGame I S Θ) : NormalForm I (fun i => Θ i → S i) where
  payoff i s := G.expectedPayoff s i

/-- **Definition 8.E.1** (MWG, p. 255). A (pure strategy) Bayesian Nash equilibrium: a profile of
decision rules that is a Nash equilibrium of `[I, {𝒮_i}, {ũ_i(·)}]`. -/
def IsBNE (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) : Prop :=
  IsNashEquilibrium G.toNormalForm s

omit [∀ i, DecidableEq (Θ i)] in
/-- **Definition 8.E.1** (MWG, p. 255), unfolded: `ũ_i(s_i(·), s_{-i}(·)) ≥ ũ_i(s_i'(·), s_{-i}(·))`
for all `s_i'(·)` and all `i`. -/
theorem isBNE_iff (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) :
    G.IsBNE s ↔ ∀ i (s' : Θ i → S i), G.expectedPayoff (update s i s') i ≤ G.expectedPayoff s i :=
  Iff.rfl

/-- The probability `Prob(θ_i = t)` that player `i` has type `t`. -/
def typeProb (G : BayesianGame I S Θ) (i : I) (t : Θ i) : ℝ :=
  ∑ θ ∈ univ.filter (fun θ : (i : I) → Θ i => θ i = t), G.prior θ

/-- The expected payoff of type `t` of player `i` from the strategy `a`, before dividing by the
probability of `t`: `∑_{θ : θ_i = t} F(θ) u_i(a, s_{-i}(θ_{-i}), θ)`. -/
def typeGain (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I) (t : Θ i) (a : S i) :
    ℝ :=
  ∑ θ ∈ univ.filter (fun θ : (i : I) → Θ i => θ i = t), G.prior θ * G.payoff i
    (update (play s θ) i a) θ

/-- **(8.E.2)** (MWG, p. 256). The conditional expected payoff of type `t` of player `i` from
playing `a`: `E_{θ_{-i}}[u_i(a, s_{-i}(θ_{-i}), θ) | θ_i = t]`. -/
noncomputable def condPayoff (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I)
    (t : Θ i) (a : S i) : ℝ :=
  G.typeGain s i t a / G.typeProb i t

omit [Fintype I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] in
theorem play_update (s : (i : I) → Θ i → S i) (i : I) (s' : Θ i → S i)
    (θ : (i : I) → Θ i) : play (update s i s') θ = update (play s θ) i (s' (θ i)) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [play]
  · simp [play, update_of_ne hj]

/-- The expected payoff of player `i` is the sum, over his types, of the types' gains. -/
theorem expectedPayoff_update_eq (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I)
    (s' : Θ i → S i) :
    G.expectedPayoff (update s i s') i = ∑ t, G.typeGain s i t (s' t) := by
  unfold expectedPayoff typeGain
  rw [← Finset.sum_fiberwise univ (fun θ : (i : I) → Θ i => θ i)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun θ hθ => ?_
  rw [play_update, (Finset.mem_filter.1 hθ).2]

/-- Playing the decision rule itself gives the types' gains at their own strategies. -/
theorem expectedPayoff_eq (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I) :
    G.expectedPayoff s i = ∑ t, G.typeGain s i t (s i t) := by
  rw [← expectedPayoff_update_eq, update_eq_self]

/-- A type with probability zero has zero gain from every strategy. -/
theorem typeGain_eq_zero (G : BayesianGame I S Θ) (hG : G.IsPrior) (s : (i : I) → Θ i → S i)
    (i : I) (t : Θ i) (ht : G.typeProb i t = 0) (a : S i) : G.typeGain s i t a = 0 := by
  have hz : ∀ θ ∈ univ.filter (fun θ : (i : I) → Θ i => θ i = t), G.prior θ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun θ _ => hG.1 θ).1 ht
  exact Finset.sum_eq_zero fun θ hθ => by rw [hz θ hθ, zero_mul]

/-- **Proposition 8.E.1** (MWG, pp. 255-256). With finitely many types, a profile of decision rules
is a Bayesian Nash equilibrium iff for every player `i` and every type `θ_i` that occurs with
positive probability, `s_i(θ_i)` maximizes the conditional expected payoff (8.E.2):
`E[u_i(s_i(θ_i), s_{-i}(θ_{-i}), θ) | θ_i] ≥ E[u_i(s_i', s_{-i}(θ_{-i}), θ) | θ_i]` for all
`s_i' ∈ S_i`. -/
theorem proposition_8_E_1 (G : BayesianGame I S Θ) (hG : G.IsPrior)
    (s : (i : I) → Θ i → S i) :
    G.IsBNE s ↔ ∀ i (t : Θ i), 0 < G.typeProb i t → ∀ a : S i,
      G.condPayoff s i t a ≤ G.condPayoff s i t (s i t) := by
  rw [isBNE_iff]
  constructor
  · intro h i t ht a
    -- deviate only at the type `t`
    have hdev := h i (update (s i) t a)
    rw [expectedPayoff_update_eq, expectedPayoff_eq,
      ← Finset.add_sum_erase _ _ (mem_univ t), ← Finset.add_sum_erase _ _ (mem_univ t)] at hdev
    have hrest : ∑ x ∈ univ.erase t, G.typeGain s i x (update (s i) t a x) =
        ∑ x ∈ univ.erase t, G.typeGain s i x (s i x) :=
      Finset.sum_congr rfl fun x hx => by rw [update_of_ne (ne_of_mem_erase hx)]
    rw [hrest, update_self] at hdev
    unfold condPayoff
    exact div_le_div_of_nonneg_right (by linarith) ht.le
  · intro h i s'
    rw [expectedPayoff_update_eq, expectedPayoff_eq]
    refine Finset.sum_le_sum fun t _ => ?_
    have hnn : 0 ≤ G.typeProb i t := Finset.sum_nonneg fun θ _ => hG.1 θ
    rcases hnn.eq_or_lt with h0 | hpos
    · rw [typeGain_eq_zero G hG s i t h0.symm, typeGain_eq_zero G hG s i t h0.symm]
    · have := h i t hpos (s' t)
      unfold condPayoff at this
      exact (div_le_div_iff_of_pos_right hpos).1 this

/-- With finitely many strategies and types, a Bayesian game has a mixed strategy Bayesian Nash
equilibrium: a mixed Nash equilibrium of `[I, {Δ(𝒮_i)}, {ũ_i(·)}]` (Proposition 8.D.2). -/
theorem exists_mixed_BNE [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (G : BayesianGame I S Θ) : ∃ σ, IsMixedNash G.toNormalForm σ := by
  classical
  exact proposition_8_D_2 G.toNormalForm

end BayesianGame

/-! ### Example 8.E.1: the DA's Brother with incomplete information -/

/-- The number of types of each prisoner in Example 8.E.1: one for prisoner 1 (`false`), two for
prisoner 2 (`true`). -/
abbrev daDims : Bool → ℕ
  | false => 1
  | true => 2

/-- The type sets of Example 8.E.1. -/
abbrev DAΘ (b : Bool) : Type := Fin (daDims b)

/-- **Example 8.E.1** (MWG, p. 254). Prisoner 1 (`false`) has a single type; prisoner 2 (`true`) has
type I (`0`, the preferences of Figure 8.B.4) with probability `μ` and type II (`1`, a psychic
penalty of six years for confessing) with probability `1 - μ`. Actions: `0` = don't confess,
`1` = confess. -/
noncomputable def daBayes (μ : ℝ) : BayesianGame Bool (fun _ => Fin 2) DAΘ where
  prior θ := if θ true = 0 then μ else 1 - μ
  payoff i s θ := if i = false then daU₁ (s false) (s true) else
    daU₂ (s false) (s true) - if θ true = 1 ∧ s true = 1 then 6 else 0

/-- The type profile in which prisoner 2 has type `t`. -/
def daθ (t : Fin 2) : (b : Bool) → DAΘ b
  | false => 0
  | true => t

/-- Type profiles of Example 8.E.1 as pairs. -/
def daΘEquiv : ((b : Bool) → DAΘ b) ≃ DAΘ false × DAΘ true where
  toFun θ := (θ false, θ true)
  invFun p b := match b with
    | false => p.1
    | true => p.2
  left_inv θ := by funext b; cases b <;> rfl
  right_inv p := rfl

/-- Sums over the type profiles of Example 8.E.1. -/
theorem sum_daΘ (f : ((b : Bool) → DAΘ b) → ℝ) : ∑ θ, f θ = f (daθ 0) + f (daθ 1) := by
  rw [← daΘEquiv.symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  rfl

theorem daBayes_isPrior {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : (daBayes μ).IsPrior := by
  refine ⟨fun θ => ?_, ?_⟩
  · simp only [daBayes]
    split_ifs <;> linarith
  · rw [sum_daΘ]
    simp [daBayes, daθ]

/-- **Example 8.E.1** (MWG, pp. 254-256). For `0 < μ < 1`, a profile of decision rules is a Bayesian
Nash equilibrium of the DA's Brother with incomplete information iff type I of prisoner 2
confesses, type II does not, and prisoner 1 does not confess when `μ < 1/6` and confesses when
`μ > 1/6` (either is optimal at `μ = 1/6`). -/
theorem example_8_E_1 {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) (s : (b : Bool) → DAΘ b → Fin 2) :
    (daBayes μ).IsBNE s ↔ s true 0 = 1 ∧ s true 1 = 0 ∧
      (μ < 1 / 6 → s false 0 = 0) ∧ (1 / 6 < μ → s false 0 = 1) := by
  rw [BayesianGame.proposition_8_E_1 _ (daBayes_isPrior h0.le h1.le), Bool.forall_bool]
  -- the type probabilities and the conditional payoffs
  have hp0 : (daBayes μ).typeProb false 0 = 1 := by
    unfold BayesianGame.typeProb
    rw [Finset.sum_filter, sum_daΘ]
    simp [daBayes, daθ]
  have hp1 : ∀ t : Fin 2, (daBayes μ).typeProb true t = if t = 0 then μ else 1 - μ := by
    intro t
    unfold BayesianGame.typeProb
    rw [Finset.sum_filter, sum_daΘ]
    fin_cases t <;> simp [daBayes, daθ]
  have hc0 : ∀ a : Fin 2, (daBayes μ).condPayoff s false 0 a =
      μ * daU₁ a (s true 0) + (1 - μ) * daU₁ a (s true 1) := by
    intro a
    unfold BayesianGame.condPayoff BayesianGame.typeGain
    rw [hp0, div_one, Finset.sum_filter, sum_daΘ]
    simp [daBayes, daθ, BayesianGame.play, Function.update]
  have hc1 : ∀ t a : Fin 2, (daBayes μ).condPayoff s true t a =
      daU₂ (s false 0) a - if t = 1 ∧ a = 1 then 6 else 0 := by
    intro t a
    unfold BayesianGame.condPayoff BayesianGame.typeGain
    rw [hp1, Finset.sum_filter, sum_daΘ]
    have hμ : μ ≠ 0 := h0.ne'
    have hμ' : 1 - μ ≠ 0 := by linarith
    fin_cases t <;> simp [daBayes, daθ, BayesianGame.play, Function.update] <;> field_simp
  have hpos1 : ∀ t : Fin 2, 0 < (daBayes μ).typeProb true t := by
    intro t
    rw [hp1]
    split_ifs <;> linarith
  have hall0 : ∀ P : DAΘ false → Prop, (∀ t, P t) ↔ P 0 := fun P =>
    ⟨fun h => h 0, fun h t => (Subsingleton.elim t 0) ▸ h⟩
  rw [hall0, Fin.forall_fin_two]
  simp only [hp0, hpos1, zero_lt_one, true_imp_iff, hc0, hc1, Fin.forall_fin_two]
  generalize s false 0 = x
  generalize s true 0 = y
  generalize s true 1 = z
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩
    have hy : y = 1 := by
      fin_cases y
      · fin_cases x
        all_goals simp [daU₂] at hy1
        all_goals linarith
      · rfl
    have hz : z = 0 := by
      fin_cases z
      · rfl
      · fin_cases x
        all_goals simp [daU₂] at hz0
        all_goals linarith
    subst hy hz
    refine ⟨rfl, rfl, fun hμ => ?_, fun hμ => ?_⟩
    · fin_cases x
      · rfl
      · simp [daU₁] at hx0; linarith
    · fin_cases x
      · simp [daU₁] at hx1; linarith
      · rfl
  · rintro ⟨rfl, rfl, hlo, hhi⟩
    have hcase : x = 0 ∧ μ ≤ 1 / 6 ∨ x = 1 ∧ 1 / 6 ≤ μ := by
      rcases lt_trichotomy μ (1 / 6) with h | h | h
      · exact Or.inl ⟨hlo h, h.le⟩
      · fin_cases x
        · exact Or.inl ⟨rfl, h.le⟩
        · exact Or.inr ⟨rfl, h.ge⟩
      · exact Or.inr ⟨hhi h, h.le⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
      rcases hcase with ⟨rfl, hμ⟩ | ⟨rfl, hμ⟩ <;> simp [daU₁, daU₂] <;> linarith

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Example 8.E.2: the Alphabeta research consortium

MWG, Example 8.E.2, pp. 256-257.

Each firm's type `θ_i` is uniform on `[0, 1]`, independently; developing costs `c ∈ (0, 1)` and
is worth `θ_i²` to firm `i`, and an invention is shared. A strategy is a decision rule
`s_i : [0, 1] → {develop, not}` (`true` = develop). With a continuum of types the book analyses
the equilibrium type by type, through condition (8.E.3) (see footnote 8: Proposition 8.E.1 holds
for almost every type); this is the formulation used here.

* `zProb s = Prob(s(θ) = develop)` is the Lebesgue measure of `{θ ∈ [0, 1] : s(θ) = true}`.
* `ZiggerBNE c s₁ s₂`: every type develops exactly when developing is at least as good as not
  developing, `θ_i² - c ≥ θ_i² Prob(s_j(θ_j) = 1)` (ties: develop).
* (8.E.3) and the cutoff rule (`zigger_cutoff`): firm `i` develops iff
  `θ_i ≥ [c / (1 - Prob(s_j(θ_j) = 1))]^{1/2}`, a cutoff at least `√c` (`zigger_cutoff_ge_sqrt`).
* `example_8_E_2`: in every equilibrium both firms use the cutoff `θ* = c^{1/3}`, and this is an
  equilibrium (`example_8_E_2_exists`); the cutoffs lie in `(0, 1)` and satisfy
  `(θ̂₁)² θ̂₂ = c = (θ̂₂)² θ̂₁`. The probabilities that neither, exactly one, or both firms develop
  are `(θ*)²`, `2θ*(1 - θ*)`, `(1 - θ*)²` (`example_8_E_2_outcomes`).
-/

namespace MWG.SimultaneousMoveGames

open MeasureTheory

/-- The probability `Prob(s(θ) = 1)` that a firm using the decision rule `s` develops, for `θ`
uniform on `[0, 1]`. -/
noncomputable def zProb (s : ℝ → Bool) : ℝ :=
  (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true})).toReal

/-- **Example 8.E.2** (MWG, p. 256). A Bayesian Nash equilibrium of the Zigger game, type by type:
type `θ` of firm `i` develops iff `θ² - c ≥ θ² Prob(s_j(θ_j) = 1)`. -/
def ZiggerBNE (c : ℝ) (s₁ s₂ : ℝ → Bool) : Prop :=
  (∀ θ ∈ Set.Icc (0 : ℝ) 1, s₁ θ = true ↔ θ ^ 2 * zProb s₂ ≤ θ ^ 2 - c) ∧
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, s₂ θ = true ↔ θ ^ 2 * zProb s₁ ≤ θ ^ 2 - c

/-- `√x < 1` for `x < 1`. -/
theorem zigger_sqrt_lt_one {x : ℝ} (hx : x < 1) : √x < 1 :=
  (Real.sqrt_lt' one_pos).2 (by simpa using hx)

/-- Probabilities lie in `[0, 1]`. -/
theorem zProb_mem (s : ℝ → Bool) : 0 ≤ zProb s ∧ zProb s ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold zProb
  have h : volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true}) ≤ 1 := by
    calc volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true}) ≤ volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono Set.inter_subset_left
      _ = 1 := by simp [Real.volume_Icc]
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

/-- The measure of `{θ ∈ [0, 1] : θ² ≥ k}` for `k ≤ 1` is `1 - √k`. -/
theorem volume_sq_ge {k : ℝ} (hk1 : k ≤ 1) :
    (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2})).toReal = 1 - √k := by
  have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2} = Set.Icc (√k) 1 := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, h1⟩, hk'⟩
      exact ⟨(Real.sqrt_le_left h0).2 hk', h1⟩
    · rintro ⟨h0, h1⟩
      have hθ : 0 ≤ θ := (Real.sqrt_nonneg k).trans h0
      exact ⟨⟨hθ, h1⟩, (Real.sqrt_le_left hθ).1 h0⟩
  have hs : √k ≤ 1 := Real.sqrt_le_one.mpr hk1
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- The set `{θ ∈ [0, 1] : θ² ≥ k}` is empty for `k > 1`. -/
theorem volume_sq_ge_of_one_lt {k : ℝ} (hk : 1 < k) :
    (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2})).toReal = 0 := by
  have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | k ≤ θ ^ 2} = ∅ := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro ⟨h0, h1⟩ hk'
    nlinarith
  simp [hset]

/-- **(8.E.3)** (MWG, p. 256): the best response of firm `i` is a cutoff rule. If
`Prob(s_j = 1) < 1`, type `θ ∈ [0, 1]` develops iff `θ ≥ [c / (1 - Prob(s_j(θ_j) = 1))]^{1/2}`; if
`Prob(s_j = 1) = 1` no type develops. -/
theorem zigger_cutoff {c q : ℝ} (hc : 0 < c) (hq : q ≤ 1) (θ : ℝ) (hθ : 0 ≤ θ) :
    (θ ^ 2 * q ≤ θ ^ 2 - c ↔ q < 1 ∧ √(c / (1 - q)) ≤ θ) := by
  constructor
  · intro h
    have hq1 : q < 1 := by
      by_contra hq1
      have : q = 1 := le_antisymm hq (not_lt.1 hq1)
      subst this
      linarith
    refine ⟨hq1, (Real.sqrt_le_left hθ).2 ?_⟩
    rw [div_le_iff₀ (by linarith)]
    linarith
  · rintro ⟨hq1, h⟩
    have := (Real.sqrt_le_left hθ).1 h
    rw [div_le_iff₀ (by linarith)] at this
    linarith

/-- **Section 8.E** (MWG, p. 257). The cutoff of a firm in the consortium is always (weakly) above
`√c`, the cutoff of a firm in isolation: firms free-ride on each other's development. -/
theorem zigger_cutoff_ge_sqrt {c q : ℝ} (hc : 0 < c) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    √c ≤ √(c / (1 - q)) :=
  Real.sqrt_le_sqrt (le_div_self hc.le (by linarith) (by linarith))

/-- The probability that a firm develops, when the other develops with probability `q`. -/
theorem zigger_prob_response {c : ℝ} (hc : 0 < c) {s q : ℝ → Bool} (hq : zProb q ≤ 1)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, s θ = true ↔ θ ^ 2 * zProb q ≤ θ ^ 2 - c) :
    zProb s = if zProb q < 1 ∧ c / (1 - zProb q) ≤ 1 then 1 - √(c / (1 - zProb q)) else 0 := by
  have hz : zProb s = (volume (Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true})).toReal := rfl
  have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | s θ = true} =
      Set.Icc (0 : ℝ) 1 ∩ {θ | zProb q < 1 ∧ c / (1 - zProb q) ≤ θ ^ 2} := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hθ, h⟩
      obtain ⟨h1, h2⟩ := (zigger_cutoff hc hq θ hθ.1).1 ((hs θ hθ).1 h)
      exact ⟨hθ, h1, (Real.sqrt_le_left hθ.1).1 h2⟩
    · rintro ⟨hθ, h1, h2⟩
      exact ⟨hθ, (hs θ hθ).2 ((zigger_cutoff hc hq θ hθ.1).2 ⟨h1, (Real.sqrt_le_left hθ.1).2 h2⟩)⟩
  rw [hz, hset]
  by_cases h1 : zProb q < 1
  · have hk : 0 < c / (1 - zProb q) := div_pos hc (by linarith)
    simp only [h1, true_and]
    split_ifs with hk1
    · exact volume_sq_ge hk1
    · exact volume_sq_ge_of_one_lt (not_le.1 hk1)
  · simp [h1]

/-- **Example 8.E.2** (MWG, p. 257). In any Bayesian Nash equilibrium both firms use the same cutoff
`θ* = c^{1/3}`: each firm develops exactly when its type is at least `c^{1/3}`, and each develops
with probability `1 - c^{1/3}`. Along the way the cutoffs `θ̂_i = 1 - Prob(s_i = 1)` lie in
`(0, 1)` and satisfy `(θ̂₁)² θ̂₂ = c = (θ̂₂)² θ̂₁`. -/
theorem example_8_E_2 {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {s₁ s₂ : ℝ → Bool}
    (h : ZiggerBNE c s₁ s₂) :
    let θ₁ := 1 - zProb s₁
    let θ₂ := 1 - zProb s₂
    (0 < θ₁ ∧ θ₁ < 1 ∧ 0 < θ₂ ∧ θ₂ < 1) ∧ θ₁ ^ 2 * θ₂ = c ∧ θ₂ ^ 2 * θ₁ = c ∧
      θ₁ = c ^ (1 / 3 : ℝ) ∧ θ₂ = c ^ (1 / 3 : ℝ) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, s₁ θ = true ↔ c ^ (1 / 3 : ℝ) ≤ θ) ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, s₂ θ = true ↔ c ^ (1 / 3 : ℝ) ≤ θ := by
  intro θ₁ θ₂
  obtain ⟨hq₁0, hq₁1⟩ := zProb_mem s₁
  obtain ⟨hq₂0, hq₂1⟩ := zProb_mem s₂
  have hr₁ := zigger_prob_response hc hq₂1 h.1
  have hr₂ := zigger_prob_response hc hq₁1 h.2
  have hsqc : √c < 1 := zigger_sqrt_lt_one hc1
  have hsqc0 : 0 < √c := Real.sqrt_pos.2 hc
  -- an interior response: if the other develops with probability below one and the resulting
  -- threshold is at most one, the cutoff is `√(c / (1 - q))`
  have key : ∀ q p : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ p → p ≤ 1 →
      p = (if q < 1 ∧ c / (1 - q) ≤ 1 then 1 - √(c / (1 - q)) else 0) →
      q = (if p < 1 ∧ c / (1 - p) ≤ 1 then 1 - √(c / (1 - p)) else 0) →
      q < 1 ∧ c / (1 - q) < 1 ∧ p = 1 - √(c / (1 - q)) := by
    intro q p hq0 hq1 hp0 hp1 hp hq
    -- `p = 0` is impossible: then `q = 1 - √c` and `p = 1 - c^{1/4} > 0`
    have hp_ne : p ≠ 0 := by
      intro hp00
      rw [hp00] at hq
      simp only [sub_zero, div_one, zero_lt_one, true_and, hc1.le, ↓reduceIte] at hq
      have h1 : q < 1 := by linarith
      have hk : c / (1 - q) = √c := by
        rw [hq, sub_sub_cancel, div_eq_iff hsqc0.ne', Real.mul_self_sqrt hc.le]
      simp only [h1, hk, hsqc.le, true_and, ↓reduceIte] at hp
      have : √(√c) < 1 := zigger_sqrt_lt_one hsqc
      linarith
    by_cases hcond : q < 1 ∧ c / (1 - q) ≤ 1
    · simp only [hcond, and_self, ↓reduceIte] at hp
      refine ⟨hcond.1, lt_of_le_of_ne hcond.2 fun h1 => hp_ne ?_, hp⟩
      rw [hp, h1, Real.sqrt_one, sub_self]
    · simp only [hcond, ↓reduceIte] at hp
      exact absurd hp hp_ne
  obtain ⟨hq₂lt, hk₁, hp₁⟩ := key (zProb s₂) (zProb s₁) hq₂0 hq₂1 hq₁0 hq₁1 hr₁ hr₂
  obtain ⟨hq₁lt, hk₂, hp₂⟩ := key (zProb s₁) (zProb s₂) hq₁0 hq₁1 hq₂0 hq₂1 hr₂ hr₁
  -- the cutoffs
  have hθ₁ : θ₁ = √(c / θ₂) := by simp only [θ₁, θ₂]; rw [hp₁]; ring
  have hθ₂ : θ₂ = √(c / θ₁) := by simp only [θ₁, θ₂]; rw [hp₂]; ring
  have hθ₁pos : 0 < θ₁ := by simp only [θ₁]; linarith
  have hθ₂pos : 0 < θ₂ := by simp only [θ₂]; linarith
  have hθ₁lt : θ₁ < 1 := by
    rw [hθ₁]; exact zigger_sqrt_lt_one (by simpa [θ₂] using hk₁)
  have hθ₂lt : θ₂ < 1 := by
    rw [hθ₂]; exact zigger_sqrt_lt_one (by simpa [θ₁] using hk₂)
  have e₁ : θ₁ ^ 2 * θ₂ = c := by
    rw [hθ₁, Real.sq_sqrt (div_nonneg hc.le hθ₂pos.le), div_mul_cancel₀ _ hθ₂pos.ne']
  have e₂ : θ₂ ^ 2 * θ₁ = c := by
    rw [hθ₂, Real.sq_sqrt (div_nonneg hc.le hθ₁pos.le), div_mul_cancel₀ _ hθ₁pos.ne']
  -- equal cutoffs, equal to `c^{1/3}`
  have heq : θ₁ = θ₂ := by
    have : θ₁ * θ₂ * (θ₁ - θ₂) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h0 | h0
    · nlinarith
    · linarith
  have hcube : θ₁ ^ 3 = c := by rw [← e₁, heq]; ring
  have hroot : θ₁ = c ^ (1 / 3 : ℝ) := by
    rw [← hcube, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast hθ₁pos.le (by norm_num)]
  -- the decision rules
  have hrule : ∀ (s : ℝ → Bool) (q : ℝ), q ≤ 1 → 1 - q = θ₁ →
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, s θ = true ↔ θ ^ 2 * q ≤ θ ^ 2 - c) →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, s θ = true ↔ c ^ (1 / 3 : ℝ) ≤ θ := by
    intro s q hq hqθ hs θ hθ
    rw [hs θ hθ, zigger_cutoff hc hq θ hθ.1]
    have hq1 : q < 1 := by linarith
    have hcut : √(c / (1 - q)) = c ^ (1 / 3 : ℝ) := by
      rw [hqθ, ← hroot, ← e₁, ← heq, show θ₁ ^ 2 * θ₁ / θ₁ = θ₁ ^ 2 by field_simp,
        Real.sqrt_sq hθ₁pos.le]
    rw [hcut]
    exact ⟨fun h => h.2, fun h => ⟨hq1, h⟩⟩
  refine ⟨⟨hθ₁pos, hθ₁lt, hθ₂pos, hθ₂lt⟩, e₁, e₂, hroot, heq ▸ hroot,
    hrule s₁ (zProb s₂) hq₂1 (by simp only [θ₂] at heq; linarith) h.1,
    hrule s₂ (zProb s₁) hq₁1 rfl h.2⟩

/-- **Example 8.E.2** (MWG, p. 257). Both firms using the cutoff `θ* = c^{1/3}` is a Bayesian Nash
equilibrium. -/
theorem example_8_E_2_exists {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ZiggerBNE c (fun θ => decide (c ^ (1 / 3 : ℝ) ≤ θ))
      (fun θ => decide (c ^ (1 / 3 : ℝ) ≤ θ)) := by
  set t := c ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc _
  have ht3 : t ^ 3 = c := by
    rw [ht, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow hc.le (by norm_num)]
  have ht1 : t < 1 := by
    by_contra h
    push Not at h
    nlinarith [pow_le_pow_left₀ zero_le_one h 3]
  have hq : zProb (fun θ => decide (t ≤ θ)) = 1 - t := by
    unfold zProb
    have hset : Set.Icc (0 : ℝ) 1 ∩ {θ | decide (t ≤ θ) = true} = Set.Icc t 1 := by
      ext θ
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨⟨ht0.le.trans h2, h1⟩, h2⟩
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have hside : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      decide (t ≤ θ) = true ↔ θ ^ 2 * zProb (fun θ => decide (t ≤ θ)) ≤ θ ^ 2 - c := by
    intro θ hθ
    rw [hq, decide_eq_true_eq, zigger_cutoff hc (by linarith) θ hθ.1]
    have hcut : √(c / (1 - (1 - t))) = t := by
      rw [sub_sub_cancel, ← ht3, show t ^ 3 / t = t ^ 2 by field_simp, Real.sqrt_sq ht0.le]
    rw [hcut]
    exact ⟨fun h => ⟨by linarith, h⟩, fun h => h.2⟩
  exact ⟨hside, hside⟩

/-- **Example 8.E.2** (MWG, p. 257). With independent types and both firms developing with
probability `1 - θ*`, the probability that neither develops is `(θ*)²`, that exactly one does is
`2θ*(1 - θ*)`, and that both do is `(1 - θ*)²`. -/
theorem example_8_E_2_outcomes (θ : ℝ) :
    (1 - (1 - θ)) * (1 - (1 - θ)) = θ ^ 2 ∧
      (1 - θ) * (1 - (1 - θ)) + (1 - (1 - θ)) * (1 - θ) = 2 * θ * (1 - θ) ∧
      (1 - θ) * (1 - θ) = (1 - θ) ^ 2 := by
  refine ⟨by ring, by ring, by ring⟩

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 8.B.1, 8.B.2, 8.D.6, 8.D.7 and 8.D.8

MWG, pp. 262-264.

* **Exercise 8.B.1** (lobbying): with payoff `α ∑ h_j + β ∏ h_j - w_i h_i²` and efforts `h_i ≥ 0`,
  each firm's strictly dominant strategy when `β = 0` is `h_i = max(α, 0) / (2 w_i)`
  (`exercise_8_B_1_dominant`); with `α > 0` and at least two firms, a strictly dominant strategy
  exists only if `β = 0` (`exercise_8_B_1_only_if`). The printed "only if" fails with one firm
  (`exercise_8_B_1_one_firm`) and when `α ≤ 0 > β` (`exercise_8_B_1_nonpositive`) (correction 5).
* **Exercise 8.B.2**: under Definition 8.B.3 a player has at most one weakly dominant strategy
  (`weaklyDominant_unique`), so (a) holds vacuously and (b) has no example; with the weaker
  notion "at least as good as every other strategy" (`AtLeastAsGoodAsAll`) two such strategies
  give equal payoffs (`exercise_8_B_2a`) and the opponent may prefer one of them
  (`exercise_8_B_2b`) (correction 6).
* **Exercise 8.D.6**: every `2 × 2` game has a mixed strategy Nash equilibrium.
* **Exercise 8.D.7** (the minimax theorem): `v_i ≥ w_i` in any game; in a zero-sum game every Nash
  equilibrium gives `u_i* = v_i = w_i`; equilibria are interchangeable.
* **Exercise 8.D.8**: as printed (strictly quasiconvex payoffs) the claim is false
  (`exercise_8_D_8_counterexample`); with payoffs strictly concave in the player's own strategy
  a best-response finite mixture is degenerate (`exercise_8_D_8`) (correction 7).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-! ### Exercise 8.B.1 -/

/-- Nonnegative effort levels `h ≥ 0`. -/
abbrev Effort := {h : ℝ // 0 ≤ h}

/-- **Exercise 8.B.1** (MWG, p. 262). The lobbying game: firm `i` chooses hours `h_i ≥ 0`, and its
payoff is the subsidy `α ∑_j h_j + β ∏_j h_j` minus its cost `w_i h_i²`. -/
def lobbyGame {I : Type*} [Fintype I] (α β : ℝ) (w : I → ℝ) : NormalForm I (fun _ => Effort) where
  payoff i h := α * ∑ j, (h j : ℝ) + β * ∏ j, (h j : ℝ) - w i * (h i : ℝ) ^ 2

/-- The maximizer of `A y - w y²` over `y ≥ 0`. -/
theorem quad_max {A w y : ℝ} (hw : 0 < w) (hy : 0 ≤ y) :
    A * y - w * y ^ 2 ≤ A * (max A 0 / (2 * w)) - w * (max A 0 / (2 * w)) ^ 2 ∧
      (y ≠ max A 0 / (2 * w) →
        A * y - w * y ^ 2 < A * (max A 0 / (2 * w)) - w * (max A 0 / (2 * w)) ^ 2) := by
  rcases le_total 0 A with hA | hA
  · rw [max_eq_left hA]
    have key : A * (A / (2 * w)) - w * (A / (2 * w)) ^ 2 - (A * y - w * y ^ 2) =
        w * (y - A / (2 * w)) ^ 2 := by field_simp; ring
    refine ⟨by nlinarith [sq_nonneg (y - A / (2 * w))], fun hne => ?_⟩
    have : 0 < (y - A / (2 * w)) ^ 2 := by positivity
    nlinarith
  · rw [max_eq_right hA]
    simp only [zero_div, mul_zero, ne_eq, sq, sub_zero]
    have h1 : y * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hA
    refine ⟨by nlinarith [mul_nonneg hw.le (mul_nonneg hy hy)], fun hne => ?_⟩
    have : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
    have h2 : 0 < w * (y * y) := by positivity
    linarith [mul_comm A y]

/-- The payoff of firm `i` after it changes its effort to `y`. -/
theorem lobbyGame_update {I : Type*} [Fintype I] [DecidableEq I] (α β : ℝ) (w : I → ℝ)
    (r : I → Effort) (i : I) (y : Effort) :
    (lobbyGame α β w).payoff i (update r i y) =
      (α + β * ∏ j ∈ univ.erase i, (r j : ℝ)) * y - w i * (y : ℝ) ^ 2 +
        α * ∑ j ∈ univ.erase i, (r j : ℝ) := by
  have hs : ∑ j, ((update r i y j : Effort) : ℝ) = y + ∑ j ∈ univ.erase i, (r j : ℝ) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  have hp : ∏ j, ((update r i y j : Effort) : ℝ) = y * ∏ j ∈ univ.erase i, (r j : ℝ) := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i), update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [lobbyGame, hs, hp, update_self]
  ring

/-- **Exercise 8.B.1** (MWG, p. 262). If `β = 0`, firm `i`'s strictly dominant strategy is
`h_i = max(α, 0) / (2 w_i)` (`α / (2 w_i)` when `α > 0`). -/
theorem exercise_8_B_1_dominant {I : Type*} [Fintype I] [DecidableEq I] (α : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (i : I) :
    StrictlyDominant (lobbyGame α 0 w) i
      ⟨max α 0 / (2 * w i), div_nonneg (le_max_right _ _) (by linarith [hw i])⟩ := by
  intro y hy r
  rw [lobbyGame_update, lobbyGame_update]
  simp only [zero_mul, add_zero]
  have hne : (y : ℝ) ≠ max α 0 / (2 * w i) := fun h => hy (Subtype.ext h)
  have := (quad_max (A := α) (hw i) y.2).2 hne
  linarith

/-- If `x` is strictly dominant for firm `i` and `y` maximizes firm `i`'s payoff against the
rivals' profile `r`, then `x = y`. -/
theorem eq_of_strictlyDominant_of_max {I : Type*} [DecidableEq I] {S : I → Type*}
    {N : NormalForm I S} {i : I} {x : S i} (hx : StrictlyDominant N i x) (r : (j : I) → S j)
    {y : S i} (hy : ∀ z, N.payoff i (update r i z) ≤ N.payoff i (update r i y)) : x = y := by
  by_contra hne
  exact absurd (hy x) (not_le.2 (hx y (Ne.symm hne) r))

/-- **Exercise 8.B.1** (MWG, p. 262). With `α > 0` and at least two firms, if firm `i` has a
strictly dominant strategy then `β = 0`. -/
theorem exercise_8_B_1_only_if {I : Type*} [Fintype I] [DecidableEq I] (α β : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (hα : 0 < α) (i j : I) (hij : j ≠ i) {x : Effort}
    (hx : StrictlyDominant (lobbyGame α β w) i x) : β = 0 := by
  by_contra hβ
  have hwi := hw i
  -- the best reply when the rivals choose `0`, and when they choose `1`
  have hbest : ∀ (r : I → Effort), ∀ z : Effort,
      (lobbyGame α β w).payoff i (update r i z) ≤ (lobbyGame α β w).payoff i (update r i
        ⟨max (α + β * ∏ j ∈ univ.erase i, (r j : ℝ)) 0 / (2 * w i),
          div_nonneg (le_max_right _ _) (by linarith)⟩) := by
    intro r z
    rw [lobbyGame_update, lobbyGame_update]
    have := (quad_max (A := α + β * ∏ j ∈ univ.erase i, (r j : ℝ)) hwi z.2).1
    linarith
  have h0 := congrArg Subtype.val (eq_of_strictlyDominant_of_max hx _ (hbest fun _ => ⟨0, le_rfl⟩))
  have h1 := congrArg Subtype.val
    (eq_of_strictlyDominant_of_max hx _ (hbest fun _ => ⟨1, zero_le_one⟩))
  have hz : ∏ j ∈ univ.erase i, ((⟨0, le_rfl⟩ : Effort) : ℝ) = 0 :=
    Finset.prod_eq_zero (mem_erase.2 ⟨hij, mem_univ j⟩) rfl
  have ho : ∏ j ∈ univ.erase i, ((⟨1, zero_le_one⟩ : Effort) : ℝ) = 1 := by simp
  simp only [hz, ho, mul_zero, add_zero, mul_one] at h0 h1
  rw [h0, max_eq_left hα.le] at h1
  have h2 : α = max (α + β) 0 := by
    field_simp at h1
    linarith
  rcases le_total (α + β) 0 with h | h
  · rw [max_eq_right h] at h2; linarith
  · rw [max_eq_left h] at h2; exact hβ (by linarith)

/-- **Exercise 8.B.1 needs two firms** (correction 5). With a single firm `β ≠ 0` does not prevent a
strictly dominant strategy: the payoff `(α + β) h - w h²` has the unique maximizer
`max(α + β, 0) / (2w)` whatever (the empty) rivals do. -/
theorem exercise_8_B_1_one_firm (α β w : ℝ) (hw : 0 < w) :
    StrictlyDominant (lobbyGame (I := Unit) α β fun _ => w) ()
      ⟨max (α + β) 0 / (2 * w), div_nonneg (le_max_right _ _) (by linarith)⟩ := by
  intro y hy r
  rw [lobbyGame_update, lobbyGame_update]
  simp only [Finset.univ_unique, Finset.erase_singleton, Finset.prod_empty, mul_one,
    Finset.sum_empty, mul_zero, add_zero]
  have hne : (y : ℝ) ≠ max (α + β) 0 / (2 * w) := fun h => hy (Subtype.ext h)
  have := (quad_max (A := α + β) hw y.2).2 hne
  linarith

/-- **Exercise 8.B.1 with `α ≤ 0` and `β < 0`** (correction 5). Then `h_i = 0` is strictly dominant
for every firm although `β ≠ 0`. -/
theorem exercise_8_B_1_nonpositive {I : Type*} [Fintype I] [DecidableEq I] (α β : ℝ)
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (hα : α ≤ 0) (hβ : β < 0) (i : I) :
    StrictlyDominant (lobbyGame α β w) i ⟨0, le_rfl⟩ := by
  intro y hy r
  rw [lobbyGame_update, lobbyGame_update]
  have hP : 0 ≤ ∏ j ∈ univ.erase i, (r j : ℝ) := Finset.prod_nonneg fun j _ => (r j).2
  have hy0 : 0 < (y : ℝ) := lt_of_le_of_ne y.2 fun h => hy (Subtype.ext h.symm)
  have hA : α + β * ∏ j ∈ univ.erase i, (r j : ℝ) ≤ 0 := by nlinarith
  have := hw i
  have h1 := mul_le_mul_of_nonneg_right hA hy0.le
  have h2 : 0 < w i * (y : ℝ) ^ 2 := by positivity
  simp only [zero_mul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero, zero_add] at h1 ⊢
  linarith

/-! ### Exercise 8.B.2 -/

/-- **Exercise 8.B.2 under Definition 8.B.3** (correction 6). A player has at most one weakly
dominant strategy: two would have to weakly dominate each other, which requires a strict
inequality in both directions. -/
theorem weaklyDominant_unique {I : Type*} {S : I → Type*} [DecidableEq I] {N : NormalForm I S}
    {i : I} {s s' : S i} (h : WeaklyDominant N i s) (h' : WeaklyDominant N i s') : s = s' := by
  by_contra hne
  obtain ⟨-, r, hr⟩ := h s' (Ne.symm hne)
  have := (h' s hne).1 r
  linarith

/-- The weaker notion: `s_i` does at least as well as every other strategy against every
`s_{-i}`. -/
def AtLeastAsGoodAsAll {I : Type*} {S : I → Type*} [DecidableEq I] (N : NormalForm I S) (i : I)
    (s : S i) : Prop :=
  ∀ s' (r : (j : I) → S j), N.payoff i (update r i s') ≤ N.payoff i (update r i s)

/-- **Exercise 8.B.2(a)** (MWG, p. 262), for the weaker notion: if two strategies are each at least
as good as every other, they yield equal payoffs against every strategy choice of the
opponents. -/
theorem exercise_8_B_2a {I : Type*} {S : I → Type*} [DecidableEq I] {N : NormalForm I S}
    {i : I} {s s' : S i} (h : AtLeastAsGoodAsAll N i s) (h' : AtLeastAsGoodAsAll N i s')
    (r : (j : I) → S j) : N.payoff i (update r i s) = N.payoff i (update r i s') :=
  le_antisymm (h' s r) (h s' r)

/-- **Exercise 8.B.2(b)** (MWG, p. 262), for the weaker notion: in the `2 × 2` game below both rows
are at least as good as every other row for player 1, but player 2 strictly prefers that player 1
play the first. -/
theorem exercise_8_B_2b :
    let u₁ : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
    let u₂ : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![0, 0]]
    AtLeastAsGoodAsAll (bimatrix u₁ u₂) 0 (0 : Fin 2) ∧
      AtLeastAsGoodAsAll (bimatrix u₁ u₂) 0 (1 : Fin 2) ∧ ∀ b : Fin 2, u₂ 1 b < u₂ 0 b := by
  intro u₁ u₂
  refine ⟨fun s' r => by simp [u₁], fun s' r => by simp [u₁], fun b => ?_⟩
  fin_cases b <;> simp [u₂]

/-! ### Exercise 8.D.6 -/

/-- **Exercise 8.D.6** (MWG, p. 264). Every two-player game with two strategies for each player has
a mixed strategy Nash equilibrium. -/
theorem exercise_8_D_6 (u₁ u₂ : Fin 2 → Fin 2 → ℝ) :
    ∃ x y : Fin 2 → ℝ, IsMixedStrategy x ∧ IsMixedStrategy y ∧
      IsMixedNash (bimatrix u₁ u₂) (mp x y) := by
  have hne : ∀ i, Nonempty (S2 2 2 i) := fun i => by fin_cases i <;> exact ⟨(0 : Fin 2)⟩
  obtain ⟨σ, hσ⟩ := proposition_8_D_2 (bimatrix u₁ u₂)
  exact ⟨σ 0, σ 1, hσ.1 0, hσ.1 1, Eq.mp (congrArg (IsMixedNash (bimatrix u₁ u₂)) (eq_mp σ)) hσ⟩

/-- **Exercise 8.D.6** (MWG, p. 264), the hint's parametrization: a mixed strategy over two pure
strategies is given by the probability `p ∈ [0, 1]` of the first. -/
theorem exercise_8_D_6_param (x : Fin 2 → ℝ) :
    IsMixedStrategy x ↔ ∃ p ∈ Set.Icc (0 : ℝ) 1, x = ![p, 1 - p] := by
  constructor
  · rintro ⟨h0, h1⟩
    rw [Fin.sum_univ_two] at h1
    refine ⟨x 0, ⟨h0 0, by linarith [h0 1]⟩, funext fun a => ?_⟩
    fin_cases a
    · rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
  · rintro ⟨p, ⟨h0, h1⟩, rfl⟩
    refine ⟨fun a => ?_, by simp [Fin.sum_univ_two]⟩
    fin_cases a <;> simp <;> linarith

/-! ### Exercise 8.D.7: the minimax theorem -/

/-- `⨆ x ⨅ y f(x, y) ≤ ⨅ y ⨆ x f(x, y)` for a bounded function on nonempty sets. -/
theorem iSup_iInf_le_iInf_iSup_of_bdd {X Y : Type*} [Nonempty X] [Nonempty Y] (f : X → Y → ℝ)
    {B : ℝ} (hB : ∀ x y, |f x y| ≤ B) : ⨆ x, ⨅ y, f x y ≤ ⨅ y, ⨆ x, f x y := by
  have hbb : ∀ x, BddBelow (Set.range fun y => f x y) :=
    fun x => ⟨-B, by rintro _ ⟨y, rfl⟩; linarith [(abs_le.1 (hB x y)).1]⟩
  have hba : ∀ y, BddAbove (Set.range fun x => f x y) :=
    fun y => ⟨B, by rintro _ ⟨x, rfl⟩; linarith [(abs_le.1 (hB x y)).2]⟩
  refine ciSup_le fun x => le_ciInf fun y => ?_
  exact (ciInf_le (hbb x) y).trans (le_ciSup (hba y) x)

variable {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A two-player mixed profile from the players' mixed strategies. -/
def mprof (x : S 0 → ℝ) (y : S 1 → ℝ) : (i : Fin 2) → S i → ℝ :=
  Fin.cons x (Fin.cons y finZeroElim)

/-- Player 1's mixed strategies. -/
abbrev Δ₁ (S : Fin 2 → Type*) [∀ i, Fintype (S i)] := {x : S 0 → ℝ // IsMixedStrategy x}

/-- Player 2's mixed strategies. -/
abbrev Δ₂ (S : Fin 2 → Type*) [∀ i, Fintype (S i)] := {y : S 1 → ℝ // IsMixedStrategy y}

/-- Player `k`'s payoff from the mixed profile `(x, y)`. -/
def pay2 (N : NormalForm (Fin 2) S) (k : Fin 2) (x : Δ₁ S) (y : Δ₂ S) : ℝ :=
  N.mixedPayoff (mprof x.1 y.1) k

omit [∀ i, DecidableEq (S i)] in
theorem isMixedProfile_mprof (x : Δ₁ S) (y : Δ₂ S) : IsMixedProfile (mprof x.1 y.1) := by
  intro i
  fin_cases i
  · exact x.2
  · exact y.2

omit [∀ i, DecidableEq (S i)] in
theorem abs_pay2_le (N : NormalForm (Fin 2) S) (k : Fin 2) (x : Δ₁ S) (y : Δ₂ S) :
    |pay2 N k x y| ≤ ∑ s, |N.payoff k s| :=
  abs_mixedPayoff_le N (isMixedProfile_mprof x y) k

/-- **Exercise 8.D.7** (MWG, p. 264). Player `i`'s maximin level `w_i = max_{σ_i} min_{σ_{-i}}
u_i(σ_i, σ_{-i})`, for player 1. -/
noncomputable def maximin₁ (N : NormalForm (Fin 2) S) : ℝ := ⨆ x : Δ₁ S, ⨅ y : Δ₂ S, pay2 N 0 x y

/-- Player 1's minimax level `v_1 = min_{σ_2} max_{σ_1} u_1(σ_1, σ_2)`. -/
noncomputable def minimax₁ (N : NormalForm (Fin 2) S) : ℝ := ⨅ y : Δ₂ S, ⨆ x : Δ₁ S, pay2 N 0 x y

/-- Player 2's maximin level `w_2 = max_{σ_2} min_{σ_1} u_2(σ_1, σ_2)`. -/
noncomputable def maximin₂ (N : NormalForm (Fin 2) S) : ℝ := ⨆ y : Δ₂ S, ⨅ x : Δ₁ S, pay2 N 1 x y

/-- Player 2's minimax level `v_2 = min_{σ_1} max_{σ_2} u_2(σ_1, σ_2)`. -/
noncomputable def minimax₂ (N : NormalForm (Fin 2) S) : ℝ := ⨅ x : Δ₁ S, ⨆ y : Δ₂ S, pay2 N 1 x y

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.D.7(a)** (MWG, p. 264). `v_i ≥ w_i` in any (finite, two-player) game. -/
theorem exercise_8_D_7a [∀ i, Nonempty (S i)] (N : NormalForm (Fin 2) S) :
    maximin₁ N ≤ minimax₁ N ∧ maximin₂ N ≤ minimax₂ N := by
  have h1 : Nonempty (Δ₁ S) := ⟨⟨_, isMixedStrategy_uniformMixed (S 0)⟩⟩
  have h2 : Nonempty (Δ₂ S) := ⟨⟨_, isMixedStrategy_uniformMixed (S 1)⟩⟩
  exact ⟨iSup_iInf_le_iInf_iSup_of_bdd (pay2 N 0) (abs_pay2_le N 0),
    iSup_iInf_le_iInf_iSup_of_bdd (fun y x => pay2 N 1 x y) (fun y x => abs_pay2_le N 1 x y)⟩

/-- A two-player game is zero-sum: `u_2(s) = -u_1(s)`. -/
def IsZeroSum2 (N : NormalForm (Fin 2) S) : Prop := ∀ s, N.payoff 1 s = -N.payoff 0 s

omit [∀ i, DecidableEq (S i)] in
theorem pay2_zeroSum {N : NormalForm (Fin 2) S} (hz : IsZeroSum2 N) (x : Δ₁ S) (y : Δ₂ S) :
    pay2 N 1 x y = -pay2 N 0 x y := by
  simp only [pay2, NormalForm.mixedPayoff]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [hz s]; ring

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem update_mprof_zero (x x' : S 0 → ℝ) (y : S 1 → ℝ) :
    update (mprof x y) 0 x' = mprof x' y := by
  funext i
  fin_cases i <;> rfl

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem update_mprof_one (x : S 0 → ℝ) (y y' : S 1 → ℝ) :
    update (mprof x y) 1 y' = mprof x y' := by
  funext i
  fin_cases i <;> rfl

omit [∀ i, DecidableEq (S i)] in
/-- A mixed Nash equilibrium `(x*, y*)` of a two-player game in terms of `pay2`. -/
theorem isMixedNash_mprof_iff (N : NormalForm (Fin 2) S) (x : Δ₁ S) (y : Δ₂ S) :
    IsMixedNash N (mprof x.1 y.1) ↔
      (∀ x' : Δ₁ S, pay2 N 0 x' y ≤ pay2 N 0 x y) ∧ ∀ y' : Δ₂ S, pay2 N 1 x y' ≤ pay2 N 1 x y := by
  classical
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun x' => ?_, fun y' => ?_⟩
    · have := h 0 x'.1 x'.2
      rwa [update_mprof_zero] at this
    · have := h 1 y'.1 y'.2
      rwa [update_mprof_one] at this
  · rintro ⟨h1, h2⟩
    refine ⟨isMixedProfile_mprof x y, fun i τ hτ => ?_⟩
    fin_cases i
    · have := h1 ⟨τ, hτ⟩
      simp only [pay2] at this
      rwa [← update_mprof_zero x.1 τ y.1] at this
    · have := h2 ⟨τ, hτ⟩
      simp only [pay2] at this
      rwa [← update_mprof_one x.1 y.1 τ] at this

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.D.7(b)** (MWG, p. 264). In any mixed strategy Nash equilibrium `(x*, y*)` of a
zero-sum game, each player's expected utility equals his minimax and his maximin levels:
`u_i* = v_i = w_i`. -/
theorem exercise_8_D_7b [∀ i, Nonempty (S i)] {N : NormalForm (Fin 2) S} (hz : IsZeroSum2 N)
    (x : Δ₁ S) (y : Δ₂ S) (h : IsMixedNash N (mprof x.1 y.1)) :
    pay2 N 0 x y = minimax₁ N ∧ pay2 N 0 x y = maximin₁ N ∧
      pay2 N 1 x y = minimax₂ N ∧ pay2 N 1 x y = maximin₂ N := by
  classical
  obtain ⟨h1, h2⟩ := (isMixedNash_mprof_iff N x y).1 h
  have hn1 : Nonempty (Δ₁ S) := ⟨x⟩
  have hn2 : Nonempty (Δ₂ S) := ⟨y⟩
  have hab := exercise_8_D_7a N
  set B0 := ∑ s, |N.payoff 0 s|
  set B1 := ∑ s, |N.payoff 1 s|
  have hbb : ∀ (k : Fin 2) (x' : Δ₁ S), BddBelow (Set.range fun y' : Δ₂ S => pay2 N k x' y') :=
    fun k x' => ⟨-∑ s, |N.payoff k s|, by
      rintro _ ⟨y', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).1]⟩
  have hba : ∀ (k : Fin 2) (y' : Δ₂ S), BddAbove (Set.range fun x' : Δ₁ S => pay2 N k x' y') :=
    fun k y' => ⟨∑ s, |N.payoff k s|, by
      rintro _ ⟨x', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).2]⟩
  have hbb' : ∀ (k : Fin 2) (y' : Δ₂ S), BddBelow (Set.range fun x' : Δ₁ S => pay2 N k x' y') :=
    fun k y' => ⟨-∑ s, |N.payoff k s|, by
      rintro _ ⟨x', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).1]⟩
  have hba' : ∀ (k : Fin 2) (x' : Δ₁ S), BddAbove (Set.range fun y' : Δ₂ S => pay2 N k x' y') :=
    fun k x' => ⟨∑ s, |N.payoff k s|, by
      rintro _ ⟨y', rfl⟩; linarith [(abs_le.1 (abs_pay2_le N k x' y')).2]⟩
  -- player 1: `v_1 ≤ u_1* ≤ w_1`
  have hv1 : minimax₁ N ≤ pay2 N 0 x y := by
    refine (ciInf_le (f := fun y' : Δ₂ S => ⨆ x' : Δ₁ S, pay2 N 0 x' y') ⟨-B0, ?_⟩ y).trans
      (ciSup_le h1)
    rintro _ ⟨y', rfl⟩
    exact (le_ciSup (hba 0 y') x).trans' (by linarith [(abs_le.1 (abs_pay2_le N 0 x y')).1])
  have hw1 : pay2 N 0 x y ≤ maximin₁ N := by
    refine (le_ciInf fun y' => ?_).trans
      (le_ciSup (f := fun x' : Δ₁ S => ⨅ y' : Δ₂ S, pay2 N 0 x' y') ⟨B0, ?_⟩ x)
    · have := h2 y'
      rw [pay2_zeroSum hz, pay2_zeroSum hz] at this
      linarith
    · rintro _ ⟨x', rfl⟩
      exact (ciInf_le (hbb 0 x') y).trans (by linarith [(abs_le.1 (abs_pay2_le N 0 x' y)).2])
  -- player 2: `v_2 ≤ u_2* ≤ w_2`
  have hv2 : minimax₂ N ≤ pay2 N 1 x y := by
    refine (ciInf_le (f := fun x' : Δ₁ S => ⨆ y' : Δ₂ S, pay2 N 1 x' y') ⟨-B1, ?_⟩ x).trans
      (ciSup_le h2)
    rintro _ ⟨x', rfl⟩
    exact (le_ciSup (hba' 1 x') y).trans' (by linarith [(abs_le.1 (abs_pay2_le N 1 x' y)).1])
  have hw2 : pay2 N 1 x y ≤ maximin₂ N := by
    refine (le_ciInf fun x' => ?_).trans
      (le_ciSup (f := fun y' : Δ₂ S => ⨅ x' : Δ₁ S, pay2 N 1 x' y') ⟨B1, ?_⟩ y)
    · have := h1 x'
      rw [pay2_zeroSum hz, pay2_zeroSum hz]
      linarith
    · rintro _ ⟨y', rfl⟩
      exact (ciInf_le (hbb' 1 y') x).trans (by linarith [(abs_le.1 (abs_pay2_le N 1 x y')).2])
  exact ⟨le_antisymm (by linarith [hab.1]) hv1, le_antisymm hw1 (by linarith [hab.1]),
    le_antisymm (by linarith [hab.2]) hv2, le_antisymm hw2 (by linarith [hab.2])⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.D.7(c)** (MWG, p. 264). In a zero-sum game, if `(x', y')` and `(x'', y'')` are
Nash equilibria, so are `(x', y'')` and `(x'', y')`. -/
theorem exercise_8_D_7c [∀ i, Nonempty (S i)] {N : NormalForm (Fin 2) S} (hz : IsZeroSum2 N)
    {x' x'' : Δ₁ S} {y' y'' : Δ₂ S} (h' : IsMixedNash N (mprof x'.1 y'.1))
    (h'' : IsMixedNash N (mprof x''.1 y''.1)) :
    IsMixedNash N (mprof x'.1 y''.1) ∧ IsMixedNash N (mprof x''.1 y'.1) := by
  classical
  obtain ⟨a1, a2⟩ := (isMixedNash_mprof_iff N x' y').1 h'
  obtain ⟨b1, b2⟩ := (isMixedNash_mprof_iff N x'' y'').1 h''
  obtain ⟨e1, -, -, -⟩ := exercise_8_D_7b hz x' y' h'
  obtain ⟨e2, -, -, -⟩ := exercise_8_D_7b hz x'' y'' h''
  -- `x'` guarantees the value against every `y`, and `y''` holds player 1 to it
  have gx : ∀ (x : Δ₁ S) (y : Δ₂ S) , IsMixedNash N (mprof x.1 y.1) → ∀ y₀ : Δ₂ S,
      pay2 N 0 x y ≤ pay2 N 0 x y₀ := by
    intro x y h y₀
    have := ((isMixedNash_mprof_iff N x y).1 h).2 y₀
    rw [pay2_zeroSum hz, pay2_zeroSum hz] at this
    linarith
  have c1 := gx x' y' h' y''
  have c2 := b1 x'
  have c3 := gx x'' y'' h'' y'
  have c4 := a1 x''
  have hval : pay2 N 0 x' y'' = pay2 N 0 x' y' := by linarith
  have hval' : pay2 N 0 x'' y' = pay2 N 0 x' y' := by linarith
  refine ⟨(isMixedNash_mprof_iff N x' y'').2 ⟨fun x₀ => ?_, fun y₀ => ?_⟩,
    (isMixedNash_mprof_iff N x'' y').2 ⟨fun x₀ => ?_, fun y₀ => ?_⟩⟩
  · linarith [b1 x₀]
  · rw [pay2_zeroSum hz, pay2_zeroSum hz]; linarith [gx x' y' h' y₀]
  · linarith [a1 x₀]
  · rw [pay2_zeroSum hz, pay2_zeroSum hz]; linarith [gx x'' y'' h'' y₀]

/-! ### Exercise 8.D.8 -/

/-- **Exercise 8.D.8 as printed is false** (correction 7). One player with the convex strategy set
`[-1, 1]` and the strictly convex (hence strictly quasiconvex) payoff `u(s) = s²`: the mixture of
`-1` and `1` with probability `½` each gives expected payoff `1`, at least as much as any finite
mixture, yet it is not degenerate. -/
theorem exercise_8_D_8_counterexample :
    StrictConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun s => s ^ 2) ∧
      (∀ x y : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → y ∈ Set.Icc (-1 : ℝ) 1 → x ≠ y →
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, (t * x + (1 - t) * y) ^ 2 < max (x ^ 2) (y ^ 2)) ∧
      ∀ (n : ℕ) (w x : Fin n → ℝ), (∀ k, 0 ≤ w k) → ∑ k, w k = 1 →
        (∀ k, x k ∈ Set.Icc (-1 : ℝ) 1) →
        ∑ k, w k * x k ^ 2 ≤ (1 / 2) * (-1 : ℝ) ^ 2 + (1 / 2) * (1 : ℝ) ^ 2 := by
  have hsc : StrictConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun s => s ^ 2) := by
    refine ⟨convex_Icc _ _, fun x _ y _ hxy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hd : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hxy
      positivity
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_pos ha hb]
  refine ⟨hsc, fun x y hx hy hxy t ht => ?_, fun n w x hw hs hx => ?_⟩
  · have := hsc.2 hx hy hxy ht.1 (by linarith [ht.2] : (0 : ℝ) < 1 - t) (by ring)
    simp only [smul_eq_mul] at this
    have h1 : t * x ^ 2 + (1 - t) * y ^ 2 ≤ max (x ^ 2) (y ^ 2) := by
      have := le_max_left (x ^ 2) (y ^ 2)
      have := le_max_right (x ^ 2) (y ^ 2)
      nlinarith [ht.1, ht.2]
    linarith
  · have hle : ∀ k, w k * x k ^ 2 ≤ w k := fun k => by
      have := hx k
      have : x k ^ 2 ≤ 1 := by nlinarith [this.1, this.2]
      nlinarith [hw k]
    calc ∑ k, w k * x k ^ 2 ≤ ∑ k, w k := Finset.sum_le_sum fun k _ => hle k
      _ = (1 / 2) * (-1 : ℝ) ^ 2 + (1 / 2) * (1 : ℝ) ^ 2 := by rw [hs]; norm_num

/-- **Exercise 8.D.8, corrected** (correction 7). If a player's expected payoff `U` (given the
others' play) is strictly concave on his convex strategy set, every finite mixture that is a best
response — at least as good as every pure strategy — is degenerate: all the points it plays with
positive probability coincide. -/
theorem exercise_8_D_8 {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {U : E → ℝ}
    (hU : StrictConcaveOn ℝ C U) {n : ℕ} {w : Fin n → ℝ} {x : Fin n → E}
    (hw : ∀ k, 0 < w k) (hs : ∑ k, w k = 1) (hx : ∀ k, x k ∈ C)
    (hbest : ∀ z ∈ C, U z ≤ ∑ k, w k * U (x k)) : ∀ j k, x j = x k := by
  by_contra hne
  push Not at hne
  obtain ⟨j, k, hjk⟩ := hne
  have hlt := hU.lt_map_sum (t := univ) (fun i _ => hw i) hs (fun i _ => hx i)
    ⟨j, mem_univ _, k, mem_univ _, hjk⟩
  have hmem : ∑ i, w i • x i ∈ C :=
    hU.1.sum_mem (fun i _ => (hw i).le) hs fun i _ => hx i
  have := hbest _ hmem
  simp only [smul_eq_mul] at hlt
  linarith

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Figure 8.F.1 and Exercises 8.C.4 and 8.F.2

MWG, pp. 258-259 and 263-265.

* Figure 8.F.1: `(D, R)` is a Nash equilibrium in which both players play weakly dominated
  strategies, so by Proposition 8.F.2 it is not trembling-hand perfect.
* **Exercise 8.F.2** (van Damme's three-player game): `(D, L, B₁)` and `(U, L, B₁)` are pure Nash
  equilibria, none of `D`, `L`, `B₁` is weakly dominated, yet `(D, L, B₁)` is not
  trembling-hand perfect: against any totally mixed profile near it, `U` does strictly better
  than `D`. So the converse of Proposition 8.F.2 fails with three players.
* **Exercise 8.C.4**: player 1's payoffs in a three-player game. As printed, the entry at
  `(D, ℓ)` for `L` is `η + 4ε`, and then `M` *is* a best response to the pure profile `(D, ℓ)`
  when `π ≥ η/2 + 4ε` (`exercise_8_C_4a_printed_false`); with the entry `π + 4ε` (the symmetric
  table) `M` is never a best response to independent randomizations (`exercise_8_C_4a`) (correction
  8). In both versions `M` is not strictly dominated (`exercise_8_C_4b`) and is a best response to
  a correlated belief (`exercise_8_C_4c`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset Filter Topology

/-- A pure strategy weakly dominated by another pure strategy (Definition 8.B.3) is weakly
dominated in the mixed extension. -/
theorem mixedWeaklyDominates_pureMixed {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {N : NormalForm I S} {i : I} {a' a : S i}
    (h : WeaklyDominates N i a' a) : MixedWeaklyDominates N i (pureMixed a') (pureMixed a) := by
  rw [mixedWeaklyDominates_iff_pure]
  simp only [mixedPayoff_pureProfile_update]
  obtain ⟨hle, r, hr⟩ := h
  exact ⟨fun s => hle s, r, hr⟩

/-! ### Figure 8.F.1 -/

/-- Player 1's payoffs in Figure 8.F.1 (rows `U, D`, columns `L, R`). -/
def fig8F1U₁ : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![-3, 0]]

/-- Player 2's payoffs in Figure 8.F.1. -/
def fig8F1U₂ : Fin 2 → Fin 2 → ℝ := ![![1, -3], ![0, 0]]

/-- **Figure 8.F.1** (MWG, pp. 258-259). `(D, R)` is a Nash equilibrium in which both players play
weakly dominated strategies (`D` by `U`, `R` by `L`); hence it is not trembling-hand perfect
(Proposition 8.F.2). -/
theorem figure_8_F_1 :
    IsNashEquilibrium (bimatrix fig8F1U₁ fig8F1U₂) (pp (1 : Fin 2) (1 : Fin 2)) ∧
      WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 0 (0 : Fin 2) (1 : Fin 2) ∧
      WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 1 (0 : Fin 2) (1 : Fin 2) ∧
      ¬ IsTHP (bimatrix fig8F1U₁ fig8F1U₂) (pureProfile (pp (1 : Fin 2) (1 : Fin 2))) := by
  have hw0 : WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 0 (0 : Fin 2) (1 : Fin 2) :=
    (bimatrix_weaklyDominates_zero_iff _ _ _ _).2
      ⟨fun b => by fin_cases b <;> norm_num [fig8F1U₁], 0, by norm_num [fig8F1U₁]⟩
  have hw1 : WeaklyDominates (bimatrix fig8F1U₁ fig8F1U₂) 1 (0 : Fin 2) (1 : Fin 2) :=
    (bimatrix_weaklyDominates_one_iff _ _ _ _).2
      ⟨fun a => by fin_cases a <;> norm_num [fig8F1U₂], 0, by norm_num [fig8F1U₂]⟩
  refine ⟨(bimatrix_isNash_iff _ _ _ _).2 ⟨fun a => ?_, fun b => ?_⟩, hw0, hw1, fun h => ?_⟩
  · fin_cases a <;> norm_num [fig8F1U₁]
  · fin_cases b <;> norm_num [fig8F1U₂]
  · exact proposition_8_F_2 _ h 0 ⟨_, isMixedStrategy_pureMixed _,
      mixedWeaklyDominates_pureMixed hw0⟩

/-! ### Exercise 8.F.2 -/

/-- Player 1's payoffs in Exercise 8.F.2, indexed (row, column, box): rows `U, D`, columns
`L, R`, boxes `B₁, B₂`. -/
def vdU₁ : Fin 2 → Fin 2 → Fin 2 → ℝ := ![![![1, 1], ![1, 0]], ![![1, 0], ![0, 1]]]

/-- **Exercise 8.F.2** (MWG, p. 265). Van Damme's three-player game: player 2 gets `1` from `L`,
player 3 gets `1` from `B₁`, and player 1's payoffs are `vdU₁`. -/
def vanDamme : NormalForm (Fin 3) (fun _ => Fin 2) where
  payoff i s := if i = 0 then vdU₁ (s 0) (s 1) (s 2) else if i = 1 then
    (if s 1 = 0 then 1 else 0) else (if s 2 = 0 then 1 else 0)

/-- The pure profile `(a, b, c)`. -/
def p3 (a b c : Fin 2) : Fin 3 → Fin 2 := ![a, b, c]

/-- In a three-player game with two strategies each, the payoff to the pure strategy `a` of
player 1 against the independent mixtures `ρ₂, ρ₃` of the others. -/
theorem mixedPayoff_three (N : NormalForm (Fin 3) (fun _ => Fin 2)) (ρ : (i : Fin 3) → Fin 2 → ℝ)
    (a : Fin 2) (k : Fin 3) :
    N.mixedPayoff (update ρ 0 (pureMixed a)) k =
      ∑ b, ∑ c, ρ 1 b * ρ 2 c * N.payoff k (p3 a b c) := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  conv_lhs => rw [← update_eq_self (1 : Fin 3) (update ρ 0 (pureMixed a)),
    mixedPayoff_update_eq_sum_pure]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [update_of_ne h10]
  set σ := update (update ρ 0 (pureMixed a)) 1 (pureMixed b) with hσ
  have hσ2 : σ 2 = ρ 2 := by rw [hσ, update_of_ne h21, update_of_ne h20]
  conv_lhs => rw [← update_eq_self (2 : Fin 3) σ, mixedPayoff_update_eq_sum_pure]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hpure : update σ 2 (pureMixed c) = pureProfile (p3 a b c) := by
    funext i
    fin_cases i <;> simp [hσ, pureProfile, p3, Function.update]
  rw [hpure, hσ2, mixedPayoff_pureProfile]
  ring

/-- The two pure Nash equilibria of Exercise 8.F.2. -/
theorem exercise_8_F_2_nash :
    IsNashEquilibrium vanDamme (p3 1 0 0) ∧ IsNashEquilibrium vanDamme (p3 0 0 0) := by
  constructor <;> intro i t <;> fin_cases i <;> fin_cases t <;>
    simp [vanDamme, p3, vdU₁, Function.update]

/-- **Exercise 8.F.2** (MWG, p. 265). None of `D` (player 1), `L` (player 2), `B₁` (player 3) is
weakly dominated in the mixed extension. -/
theorem exercise_8_F_2_undominated :
    ¬ MixedWeaklyDominated vanDamme 0 (pureMixed (1 : Fin 2)) ∧
      ¬ MixedWeaklyDominated vanDamme 1 (pureMixed (0 : Fin 2)) ∧
      ¬ MixedWeaklyDominated vanDamme 2 (pureMixed (0 : Fin 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨τ, hτ, hdom⟩ <;>
    obtain ⟨hle, s, hs⟩ := (mixedWeaklyDominates_iff_pure _ _ _ _).1 hdom <;>
    simp only [mixedPayoff_pureProfile_update_mixed, Fin.sum_univ_two] at hle hs <;>
    have h2 := hτ.2 <;> rw [Fin.sum_univ_two] at h2
  · -- against `(R, B₂)`, `D` earns `1` and `τ` earns `τ(D)`
    have h := hle (p3 0 1 1)
    simp [vanDamme, p3, vdU₁, pureMixed, Function.update] at h
    have hτD : τ 1 = 1 := by linarith [hτ.1 0]
    have hτU : τ 0 = 0 := by linarith
    have hs' : s = p3 (s 0) (s 1) (s 2) := by funext i; fin_cases i <;> rfl
    rw [hs'] at hs
    generalize s 0 = x at hs
    generalize s 1 = y at hs
    generalize s 2 = z at hs
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [vanDamme, p3, vdU₁, pureMixed, Function.update, hτD, hτU] at hs
  · simp [vanDamme, pureMixed, Function.update] at hs
    linarith [hτ.1 1]
  · simp [vanDamme, pureMixed, Function.update] at hs
    linarith [hτ.1 1]

/-- **Exercise 8.F.2** (MWG, p. 265). `(D, L, B₁)` is not (normal form) trembling-hand perfect,
although none of its strategies is weakly dominated: against totally mixed profiles near it,
`U` earns `1 - rβ` and `D` earns `(1 - r)(1 - β) + rβ`, where `r = ρ₂(R)`, `β = ρ₃(B₂)`, and
the difference `r + β - 3rβ` is positive once `r, β < 1/3`. -/
theorem exercise_8_F_2 : ¬ IsTHP vanDamme (pureProfile (p3 1 0 0)) := by
  intro h
  obtain ⟨ρ, hρ, hlim, hbr⟩ := (proposition_8_F_1 vanDamme h.1).1 h
  have hr : Tendsto (fun k => ρ k 1 1) atTop (𝓝 0) := by
    have := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim 1) 1
    simpa [pureProfile, p3, pureMixed] using this
  have hβ : Tendsto (fun k => ρ k 2 1) atTop (𝓝 0) := by
    have := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim 2) 1
    simpa [pureProfile, p3, pureMixed] using this
  obtain ⟨k, hk1, hk2⟩ := ((hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and
    (hβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)))).exists
  have hbrk := (hbr k 0).2 (pureMixed (0 : Fin 2)) (isMixedStrategy_pureMixed _)
  have hσ0 : (pureProfile (p3 1 0 0)) 0 = pureMixed (1 : Fin 2) := rfl
  rw [hσ0, mixedPayoff_three, mixedPayoff_three] at hbrk
  simp only [Fin.sum_univ_two, vanDamme, p3, vdU₁] at hbrk
  simp at hbrk
  have hs1 := (hρ k 1).1.2
  have hs2 := (hρ k 2).1.2
  rw [Fin.sum_univ_two] at hs1 hs2
  have hp1 := (hρ k 1).2 1
  have hp2 := (hρ k 2).2 1
  nlinarith [mul_pos hp1 hp2]

/-! ### Exercise 8.C.4 -/

/-- **Exercise 8.C.4** (MWG, p. 263). Player 1's payoffs `u(a, b, c)` for his strategy
`a ∈ {L, M, R}` (`0, 1, 2`), player 2's `b ∈ {U, D}` and player 3's `c ∈ {ℓ, r}`; the entry for
`L` at `(D, ℓ)` is the parameter `x` (printed `η + 4ε`; `π + 4ε` makes the table symmetric). -/
noncomputable def c4U (π ε η x : ℝ) : Fin 3 → Fin 2 → Fin 2 → ℝ :=
  ![![![π + 4 * ε, π - 4 * ε], ![x, π - 4 * ε]],
    ![![π - η, π + η / 2], ![π + η / 2, π - η]],
    ![![π - 4 * ε, π + 4 * ε], ![π - 4 * ε, π + 4 * ε]]]

/-- Player 1's expected payoff from `a` when player 2 plays `U` with probability `p` and player 3
plays `ℓ` with probability `r`, independently. -/
def c4E (u : Fin 3 → Fin 2 → Fin 2 → ℝ) (p r : ℝ) (a : Fin 3) : ℝ :=
  p * r * u a 0 0 + p * (1 - r) * u a 0 1 + (1 - p) * r * u a 1 0 + (1 - p) * (1 - r) * u a 1 1

/-- **Exercise 8.C.4(a)** (MWG, p. 263), with the symmetric entry `π + 4ε`. If `π, ε, η > 0` and
`η < 4ε`, then `M` is never a best response to independent randomizations of players 2 and 3:
against every pair of mixtures, `L` or `R` does strictly better. -/
theorem exercise_8_C_4a {π ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hηε : η < 4 * ε) {p r : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    c4E (c4U π ε η (π + 4 * ε)) p r 1 < c4E (c4U π ε η (π + 4 * ε)) p r 0 ∨
      c4E (c4U π ε η (π + 4 * ε)) p r 1 < c4E (c4U π ε η (π + 4 * ε)) p r 2 := by
  simp only [c4E, c4U, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hr0, hr1⟩ := hr
  -- `x = pr + (1 - p)(1 - r)` lies between `r` and `1 - r`
  have hx1 : r ≤ 1 / 2 → r ≤ p * r + (1 - p) * (1 - r) := fun h => by nlinarith
  have hx2 : 1 / 2 ≤ r → 1 - r ≤ p * r + (1 - p) * (1 - r) := fun h => by nlinarith
  rcases le_total r (1 / 2) with h | h
  · have := hx1 h
    nlinarith
  · have := hx2 h
    nlinarith

/-- **Exercise 8.C.4(a) as printed is false** (correction 8). With the printed entry `η + 4ε`, e.g.
`π = 10`, `ε = 1`, `η = 1`, the pure strategy `M` is a best response to `(D, ℓ)` (`p = 0`, `r = 1`),
a degenerate independent randomization. -/
theorem exercise_8_C_4a_printed_false :
    ∀ a : Fin 3, c4E (c4U 10 1 1 (1 + 4 * 1)) 0 1 a ≤ c4E (c4U 10 1 1 (1 + 4 * 1)) 0 1 1 := by
  intro a
  fin_cases a <;> simp [c4E, c4U] <;> norm_num

/-- **Exercise 8.C.4(b)** (MWG, p. 263). `M` is not strictly dominated (Proposition 8.B.1): for
every mixed strategy `τ` of player 1, `M` does at least as well as `τ` against `(U, r)` or against
`(D, ℓ)`. This holds for any entry `x ≤ π + 4ε + η`, so for the printed and the symmetric
table. -/
theorem exercise_8_C_4b {π ε η x : ℝ} (hη : 0 ≤ η) (hx : x ≤ π + 4 * ε + η) {τ : Fin 3 → ℝ}
    (hτ : IsMixedStrategy τ) :
    (∑ a, τ a * c4U π ε η x a 0 1 ≤ c4U π ε η x 1 0 1) ∨
      ∑ a, τ a * c4U π ε η x a 1 0 ≤ c4U π ε η x 1 1 0 := by
  have hs : τ 0 + τ 1 + τ 2 = 1 := by simpa [Fin.sum_univ_three] using hτ.2
  simp only [Fin.sum_univ_three, c4U, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have h3 := mul_le_mul_of_nonneg_left hx (hτ.1 0)
  have h4 := mul_nonneg (hτ.1 2) hη
  have h5 : τ 0 * (π - 4 * ε) + τ 0 * x ≤ τ 0 * (2 * π + η) := by nlinarith
  have h6 : (τ 0 + τ 1 + τ 2) * (2 * π + η) = 2 * π + η := by rw [hs]; ring
  linarith

/-- **Exercise 8.C.4(c)** (MWG, p. 263). `M` is a best response if players 2 and 3 correlate:
against the belief `½(U, r) + ½(D, ℓ)` it earns `π + η/2`, at least as much as `L` and `R`. -/
theorem exercise_8_C_4c {π ε η x : ℝ} (hη : 0 < η) (hx : x ≤ π + 4 * ε + η) (a : Fin 3) :
    (1 / 2) * c4U π ε η x a 0 1 + (1 / 2) * c4U π ε η x a 1 0 ≤
      (1 / 2) * c4U π ε η x 1 0 1 + (1 / 2) * c4U π ε η x 1 1 0 := by
  fin_cases a <;> simp [c4U] <;> linarith

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 8.D.4: simultaneous demands

MWG, Exercise 8.D.4, p. 263. Two individuals simultaneously demand amounts `d₁, d₂ ≥ 0` of 100
dollars; if `d₁ + d₂ ≤ 100` each gets his demand, otherwise both get nothing.

* (a) no strategy is strictly dominated (`exercise_8_D_4a`);
* (b) the weakly dominated strategies are exactly `d = 0` and `d > 100`
  (`exercise_8_D_4b`);
* (c) the pure Nash equilibria are the profiles with `d₁ + d₂ = 100` and those with both demands
  at least `100` (`exercise_8_D_4c`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

/-- **Exercise 8.D.4** (MWG, p. 263). The demand game. -/
noncomputable def demandGame : NormalForm (Fin 2) (fun _ => Effort) where
  payoff i d := if (d 0 : ℝ) + d 1 ≤ 100 then (d i : ℝ) else 0

theorem demand_update (r : Fin 2 → Effort) (i : Fin 2) (x : Effort) :
    demandGame.payoff i (update r i x) =
      if (x : ℝ) + r (1 - i) ≤ 100 then (x : ℝ) else 0 := by
  fin_cases i <;> simp [demandGame, Function.update, add_comm]

/-- An effort level from a nonnegative real. -/
def eff (x : ℝ) (hx : 0 ≤ x := by norm_num) : Effort := ⟨x, hx⟩

/-- **Exercise 8.D.4(a)** (MWG, p. 263). No strategy is strictly dominated: against a demand above
`100` every strategy earns nothing. -/
theorem exercise_8_D_4a (i : Fin 2) (d : Effort) : ¬ StrictlyDominated demandGame i d := by
  rintro ⟨d', h⟩
  have := h (fun _ => eff 200)
  rw [demand_update, demand_update] at this
  simp only [eff] at this
  have h1 : ¬ (d : ℝ) + 200 ≤ 100 := by linarith [d.2]
  have h2 : ¬ (d' : ℝ) + 200 ≤ 100 := by linarith [d'.2]
  simp only [h1, h2, ↓reduceIte, lt_irrefl] at this

/-- **Exercise 8.D.4(b)** (MWG, p. 263). A demand is weakly dominated iff it is `0` or above
`100`. -/
theorem exercise_8_D_4b (i : Fin 2) (d : Effort) :
    WeaklyDominated demandGame i d ↔ (d : ℝ) = 0 ∨ 100 < (d : ℝ) := by
  constructor
  · rintro ⟨d', hle, r, hr⟩
    by_contra hd
    push Not at hd
    have hpos : 0 < (d : ℝ) := lt_of_le_of_ne d.2 (Ne.symm hd.1)
    rcases lt_trichotomy (d' : ℝ) d with hlt | heq | hgt
    · -- against the demand `0`, `d` earns `d > d'`
      have := hle (fun _ => eff 0)
      rw [demand_update, demand_update] at this
      simp only [eff, add_zero] at this
      have h1 : (d : ℝ) ≤ 100 := hd.2
      have h2 : (d' : ℝ) ≤ 100 := by linarith
      simp only [h1, h2, ↓reduceIte] at this
      linarith
    · have : d' = d := Subtype.ext heq
      rw [this] at hr
      exact lt_irrefl _ hr
    · -- against the demand `100 - d`, `d` earns `d > 0` and `d'` nothing
      have := hle (fun _ => eff (100 - d) (by linarith))
      rw [demand_update, demand_update] at this
      simp only [eff] at this
      have h1 : (d : ℝ) + (100 - d) ≤ 100 := by linarith
      have h2 : ¬ (d' : ℝ) + (100 - d) ≤ 100 := by linarith
      simp only [h1, h2, ↓reduceIte] at this
      linarith
  · rintro (h0 | hbig)
    · refine ⟨eff 50, fun r => ?_, fun _ => eff 0, ?_⟩
      · rw [demand_update, demand_update]
        simp only [eff, h0]
        rw [ite_self]
        exact ite_nonneg (by norm_num) le_rfl
      · rw [demand_update, demand_update]
        simp only [eff, h0]
        norm_num
    · refine ⟨eff 100, fun r => ?_, fun _ => eff 0, ?_⟩
      · rw [demand_update, demand_update]
        simp only [eff]
        have h1 : ¬ (d : ℝ) + r (1 - i) ≤ 100 := by linarith [(r (1 - i)).2]
        simp only [h1, ↓reduceIte]
        exact ite_nonneg (by norm_num) le_rfl
      · rw [demand_update, demand_update]
        simp only [eff]
        have h1 : ¬ (d : ℝ) + 0 ≤ 100 := by linarith
        simp only [h1, ↓reduceIte]
        norm_num

/-- **Exercise 8.D.4(c)** (MWG, p. 263). The pure strategy Nash equilibria are the profiles whose
demands sum to `100` and those in which both demands are at least `100`. -/
theorem exercise_8_D_4c (d : Fin 2 → Effort) :
    IsNashEquilibrium demandGame d ↔
      (d 0 : ℝ) + d 1 = 100 ∨ (100 ≤ (d 0 : ℝ) ∧ 100 ≤ (d 1 : ℝ)) := by
  have hpay : ∀ i, demandGame.payoff i d = if (d 0 : ℝ) + d 1 ≤ 100 then (d i : ℝ) else 0 :=
    fun i => rfl
  have h0 := (d 0).2
  have h1 := (d 1).2
  constructor
  · intro h
    by_contra hno
    push Not at hno
    rcases lt_or_gt_of_ne hno.1 with hlt | hgt
    · -- demands leave money on the table: player 1 asks for the rest
      have := h 0 (eff (100 - d 1) (by linarith))
      rw [demand_update, hpay] at this
      simp only [eff, show (1 : Fin 2) - 0 = 1 from rfl] at this
      have hA : (100 - (d 1 : ℝ)) + d 1 ≤ 100 := by linarith
      simp only [hA, hlt.le, ↓reduceIte] at this
      linarith
    · -- the demands are incompatible: a player whose rival demands less than 100 deviates
      by_cases hd1 : (d 1 : ℝ) < 100
      · have := h 0 (eff (100 - d 1) (by linarith))
        rw [demand_update, hpay] at this
        simp only [eff, show (1 : Fin 2) - 0 = 1 from rfl] at this
        have hA : (100 - (d 1 : ℝ)) + d 1 ≤ 100 := by linarith
        have hB : ¬ (d 0 : ℝ) + d 1 ≤ 100 := by linarith
        simp only [hA, hB, ↓reduceIte] at this
        linarith
      · have hd0 : (d 0 : ℝ) < 100 := by
          by_contra h'
          exact hd1 (hno.2 (not_lt.1 h'))
        have := h 1 (eff (100 - d 0) (by linarith))
        rw [demand_update, hpay] at this
        simp only [eff, show (1 : Fin 2) - 1 = 0 from rfl] at this
        have hA : (100 - (d 0 : ℝ)) + d 0 ≤ 100 := by linarith
        have hB : ¬ (d 0 : ℝ) + d 1 ≤ 100 := by linarith
        simp only [hA, hB, ↓reduceIte] at this
        linarith
  · rintro (hsum | ⟨hb0, hb1⟩) i t
    · rw [demand_update, hpay]
      have hA : (d 0 : ℝ) + d 1 ≤ 100 := hsum.le
      simp only [hA, ↓reduceIte]
      have ht := t.2
      have hsum' : (d i : ℝ) + d (1 - i) = 100 := by
        fin_cases i
        · exact hsum
        · simpa [add_comm] using hsum
      have hdi := (d i).2
      split_ifs <;> linarith
    · rw [demand_update, hpay]
      have hB : ¬ (d 0 : ℝ) + d 1 ≤ 100 := by linarith
      have hother : 100 ≤ (d (1 - i) : ℝ) := by
        fin_cases i
        · exact hb1
        · exact hb0
      have ht := t.2
      simp only [hB, ↓reduceIte]
      split_ifs <;> linarith

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Two-player converses: rationalizability and trembling-hand perfection

MWG, Section 8.C, p. 245 (small type), and Section 8.F, p. 259 (small type).

Both converses rest on a theorem of the alternative, derived here from Farkas' lemma and its
strictly positive form (Stiemke) of Chapter 5's Appendix M.M (`MWG.Production.farkas`,
`MWG.Production.exists_pos_of_cone_inter_nonneg`, which use the closedness of finitely
generated cones, `MWG.Production.isClosed_coneOf`):

* `gordan_alternative`: either some nonnegative combination of the rows of a table is
  strictly positive on a set `R` of columns, or some nonzero probability vector supported on
  `R` makes every row nonpositive;
* `stiemke_alternative`: either some nonnegative combination of the rows is nonnegative and
  nonzero, or some strictly positive vector makes every row nonpositive.

**Trembling-hand perfection (p. 259).** In a two-player game, a strategy that is not weakly
dominated is a best response to a totally mixed strategy of the opponent
(`exists_totallyMixed_bestResponse`, by Stiemke). Hence a Nash equilibrium in which neither
player uses a weakly dominated strategy is trembling-hand perfect
(`isTHP_of_not_weaklyDominated_two`): the profiles `σ + t (y - σ)` with `t → 0` are totally
mixed, converge to `σ`, and each `σ_i` is a best response to them (Proposition 8.F.1).

**Rationalizability (p. 245).** The text says that with two players the rationalizable
strategies are exactly the survivors of iterated deletion of strictly dominated strategies.
With Definition 8.C.2 read literally (a conjecture is a profile of the rivals' *remaining*
mixed strategies) this is false (`Converses` module, correction 9): a mixture of two
surviving strategies can be deleted, and a strategy that is a best response only to that
mixture is then deleted too. It is true with the probabilistic conjectures of footnote 1
(p. 243), whose compound profiles are the convex combinations of remaining strategies
(`RationalizableConv`):

* `exists_ratIterConv_support_subset`: rationalizable strategies (in this sense, for any
  number of players) put no weight on strategies removed by iterated strict dominance;
* `exists_max_mem_of_msdChain`: along any process of iterated strict dominance, every
  conjecture supported on the remaining strategies has a best reply among the remaining
  strategies;
* `exists_belief_of_msdTerminal`: in a two-player game, a strategy that survives a complete
  process is a best response (among all of `Δ(S_i)`) to a mixed strategy of the opponent
  supported on the survivors (Gordan's alternative applied to the remaining game);
* `rationalizableConv_iff_two`: for two players, a pure strategy is rationalizable iff it
  survives a complete process of iterated deletion of strictly dominated strategies.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset Filter Topology

/-! ### Theorems of the alternative from Farkas' lemma -/

/-- **Gordan's alternative** (from Farkas' lemma, `MWG.Production.farkas`). If no nonnegative
combination of the rows `g a` is strictly positive on every column in `R`, then some nonnegative
`y`, zero off `R` and with positive sum, makes every row nonpositive: `∑_b y_b g(a, b) ≤ 0`. -/
theorem gordan_alternative {A B : Type*} [Fintype A] [Fintype B] (g : A → B → ℝ)
    (R : Set B) (hno : ¬ ∃ τ : A → ℝ, (∀ a, 0 ≤ τ a) ∧ ∀ b ∈ R, 0 < ∑ a, τ a * g a b) :
    ∃ y : B → ℝ, (∀ b, 0 ≤ y b) ∧ (∀ b ∉ R, y b = 0) ∧ 0 < ∑ b, y b ∧
      ∀ a, ∑ b, y b * g a b ≤ 0 := by
  classical
  set e := Fintype.equivFin B with he
  set gen : A ⊕ B ⊕ B → Fin (Fintype.card B) → ℝ :=
    Sum.elim (fun a k => g a (e.symm k))
      (Sum.elim (fun c => -Pi.single (e c) 1)
        (fun c => if c ∈ R then 0 else Pi.single (e c) 1)) with hgen
  set tgt : Fin (Fintype.card B) → ℝ := fun k => if e.symm k ∈ R then 1 else 0 with htgt
  have hsingle : ∀ (c b : B), (Pi.single (e c) (1 : ℝ) : Fin (Fintype.card B) → ℝ) (e b) =
      if b = c then 1 else 0 := by
    intro c b
    simp [Pi.single_apply, e.apply_eq_iff_eq]
  have hnotL : ¬ ∃ lam : A ⊕ B ⊕ B → ℝ, 0 ≤ lam ∧ tgt = ∑ x, lam x • gen x := by
    rintro ⟨lam, hlam, heq⟩
    apply hno
    refine ⟨fun a => lam (Sum.inl a), fun a => hlam _, fun b hb => ?_⟩
    have h1 := congrFun heq (e b)
    rw [Finset.sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type] at h1
    simp only [htgt, Equiv.symm_apply_apply, hb, ite_true, Pi.smul_apply, smul_eq_mul, hgen,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hsingle] at h1
    have h2 : ∑ x : B, lam (Sum.inr (Sum.inl x)) * -(if b = x then (1 : ℝ) else 0) =
        -lam (Sum.inr (Sum.inl b)) := by
      simp [mul_ite]
    have h3 : ∑ x : B, lam (Sum.inr (Sum.inr x)) *
        (if x ∈ R then (0 : Fin (Fintype.card B) → ℝ) else Pi.single (e x) 1) (e b) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x ∈ R
      · simp [hx]
      · have hxb : b ≠ x := fun h => hx (h ▸ hb)
        simp [hx, hxb]
    rw [h2, h3] at h1
    have := hlam (Sum.inr (Sum.inl b))
    simp only [Pi.zero_apply] at this
    linarith
  have hy : ∃ y : Fin (Fintype.card B) → ℝ, (∀ x, y ⬝ᵥ gen x ≤ 0) ∧ 0 < y ⬝ᵥ tgt := by
    by_contra hno'
    exact hnotL ((MWG.Production.farkas gen tgt).2 hno')
  obtain ⟨y, hyg, hyt⟩ := hy
  have hdot : ∀ v : Fin (Fintype.card B) → ℝ, y ⬝ᵥ v = ∑ b, y (e b) * v (e b) := by
    intro v
    rw [dotProduct]
    exact (e.sum_comp (fun k => y k * v k)).symm
  have hnn : ∀ b, 0 ≤ y (e b) := by
    intro b
    have := hyg (Sum.inr (Sum.inl b))
    rw [hdot] at this
    simp only [hgen, Sum.elim_inr, Sum.elim_inl, Pi.neg_apply, hsingle] at this
    simp [mul_ite] at this
    linarith
  have hzero : ∀ b ∉ R, y (e b) = 0 := by
    intro b hb
    have := hyg (Sum.inr (Sum.inr b))
    rw [hdot] at this
    simp only [hgen, Sum.elim_inr, hb, ite_false, hsingle] at this
    have h2 : y (e b) ≤ 0 := by simpa [mul_ite] using this
    exact le_antisymm h2 (hnn b)
  refine ⟨fun b => y (e b), hnn, hzero, ?_, fun a => ?_⟩
  · rw [hdot] at hyt
    refine hyt.trans_le (Finset.sum_le_sum fun b _ => ?_)
    simp only [htgt, Equiv.symm_apply_apply]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact hnn b
  · have := hyg (Sum.inl a)
    rw [hdot] at this
    simpa [hgen] using this

/-- **Stiemke's alternative** (from `MWG.Production.exists_pos_of_cone_inter_nonneg`). If every
nonnegative combination of the rows `g a` that is nonnegative in every column is zero, then some
strictly positive `y` makes every row nonpositive: `∑_b y_b g(a, b) ≤ 0`. -/
theorem stiemke_alternative {A B : Type*} [Fintype A] [Fintype B] (g : A → B → ℝ)
    (hno : ∀ τ : A → ℝ, (∀ a, 0 ≤ τ a) → (∀ b, 0 ≤ ∑ a, τ a * g a b) →
      ∀ b, ∑ a, τ a * g a b = 0) :
    ∃ y : B → ℝ, (∀ b, 0 < y b) ∧ ∀ a, ∑ b, y b * g a b ≤ 0 := by
  classical
  set e := Fintype.equivFin B with he
  set gen : A → Fin (Fintype.card B) → ℝ := fun a k => g a (e.symm k) with hgen
  have hcone : ∀ x ∈ MWG.Production.coneOf gen, 0 ≤ x → x = 0 := by
    rintro x ⟨lam, hlam, rfl⟩ hx
    have hx' : ∀ b, 0 ≤ ∑ a, lam a * g a b := by
      intro b
      have := hx (e b)
      simpa [Finset.sum_apply, hgen] using this
    have h0 := hno lam hlam hx'
    funext k
    have := h0 (e.symm k)
    simpa [Finset.sum_apply, hgen] using this
  obtain ⟨p, hp, hpa⟩ := MWG.Production.exists_pos_of_cone_inter_nonneg gen hcone
  refine ⟨fun b => p (e b), fun b => hp (e b), fun a => ?_⟩
  have := hpa a
  rw [dotProduct, ← e.sum_comp] at this
  simpa [hgen] using this

/-! ### Two-player games -/

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- In a two-player game a profile is determined by its two coordinates. -/
theorem two_profile_ext {T : I → Type*} {i j : I} (htwo : ∀ k, k = i ∨ k = j)
    {f g : (k : I) → T k} (hi : f i = g i) (hj : f j = g j) : f = g := by
  funext k
  rcases htwo k with rfl | rfl
  · exact hi
  · exact hj

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- In a two-player game the other player of `k` exists. -/
theorem two_other {i j : I} (hij : i ≠ j) (htwo : ∀ k, k = i ∨ k = j) (k : I) :
    ∃ o, k ≠ o ∧ ∀ l, l = k ∨ l = o := by
  rcases htwo k with rfl | rfl
  · exact ⟨j, hij, htwo⟩
  · exact ⟨i, hij.symm, fun l => (htwo l).symm⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- In a two-player game a pure profile exists as soon as both strategy sets are nonempty. -/
theorem two_nonempty {i j : I} (htwo : ∀ k, k = i ∨ k = j) (a : S i) (b : S j) :
    Nonempty ((k : I) → S k) := by
  have h : ∀ k, Nonempty (S k) := by
    intro k
    rcases htwo k with rfl | rfl
    · exact ⟨a⟩
    · exact ⟨b⟩
  exact ⟨fun k => Classical.choice (h k)⟩

/-- Two players: the payoff of the mixed strategy `τ` against the pure profile `s` is
`∑_a τ(a) u_i(a, s_j)`, where `u_i(a, b)` is computed at `(a, b)` on top of any fixed profile
`r`. -/
theorem two_mixedPayoff_pure (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (r s : (k : I) → S k) (τ : S i → ℝ) :
    N.mixedPayoff (update (pureProfile s) i τ) i =
      ∑ a, τ a * N.payoff i (update (update r j (s j)) i a) := by
  rw [mixedPayoff_pureProfile_update_mixed]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  exact two_profile_ext htwo (by simp) (by simp [update_of_ne hij.symm])

omit [∀ i, DecidableEq (S i)] in
/-- Two players: `u_i(τ, σ_j) = ∑_b σ_j(b) ∑_a τ(a) u_i(a, b)`. -/
theorem two_mixedPayoff_eq (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (r : (k : I) → S k) (σ : (k : I) → S k → ℝ)
    (τ : S i → ℝ) :
    N.mixedPayoff (update σ i τ) i =
      ∑ b, σ j b * ∑ a, τ a * N.payoff i (update (update r j b) i a) := by
  classical
  have h1 : update (update σ i τ) j (σ j) = update σ i τ := by
    have := update_eq_self j (update σ i τ)
    rwa [update_of_ne hij.symm] at this
  rw [← h1, mixedPayoff_update_eq_sum_pure]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 : update (update σ i τ) j (pureMixed b) = update (pureProfile (update r j b)) i τ :=
    two_profile_ext htwo (by simp [update_of_ne hij]) (by simp [update_of_ne hij.symm, pureProfile])
  rw [h2, two_mixedPayoff_pure N hij htwo r]
  simp

omit [∀ i, DecidableEq (S i)] in
/-- Two players: a best response to two profiles of the opponent is a best response to every
convex combination of them. -/
theorem isBestResponse_two_mix (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (r : (k : I) → S k) {τ : S i → ℝ}
    {σ y ρ : (k : I) → S k → ℝ} (h1 : IsBestResponse N i τ σ) (h2 : IsBestResponse N i τ y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hρ : ρ j = σ j + t • (y j - σ j)) :
    IsBestResponse N i τ ρ := by
  classical
  have key : ∀ τ'' : S i → ℝ, N.mixedPayoff (update ρ i τ'') i =
      N.mixedPayoff (update σ i τ'') i + t * (N.mixedPayoff (update y i τ'') i -
        N.mixedPayoff (update σ i τ'') i) := by
    intro τ''
    rw [two_mixedPayoff_eq N hij htwo r ρ, two_mixedPayoff_eq N hij htwo r σ,
      two_mixedPayoff_eq N hij htwo r y, hρ, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  refine ⟨h1.1, fun τ' hτ' => ?_⟩
  rw [key, key]
  have a1 := h1.2 τ' hτ'
  have a2 := h2.2 τ' hτ'
  nlinarith

/-! ### Trembling-hand perfection: the two-player converse of Proposition 8.F.2 -/

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.F** (MWG, p. 259, small type), the key step. In a two-player game, a mixed
strategy `τ` of player `i` that is not weakly dominated is a best response to some totally mixed
strategy `y` of the opponent `j` (Stiemke's alternative). -/
theorem exists_totallyMixed_bestResponse (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {τ : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hnd : ¬ MixedWeaklyDominated N i τ) (r : (k : I) → S k) :
    ∃ y : S j → ℝ, IsTotallyMixed y ∧
      ∀ σ : (k : I) → S k → ℝ, σ j = y → IsBestResponse N i τ σ := by
  classical
  set U : S i → S j → ℝ := fun a b => N.payoff i (update (update r j b) i a) with hU
  set V : S j → ℝ := fun b => ∑ a, τ a * U a b with hV
  have hpure : ∀ (τ' : S i → ℝ) (s : (k : I) → S k),
      N.mixedPayoff (update (pureProfile s) i τ') i = ∑ a, τ' a * U a (s j) :=
    fun τ' s => two_mixedPayoff_pure N hij htwo r s τ'
  have hno : ∀ τ' : S i → ℝ, (∀ a, 0 ≤ τ' a) → (∀ b, 0 ≤ ∑ a, τ' a * (U a b - V b)) →
      ∀ b, ∑ a, τ' a * (U a b - V b) = 0 := by
    intro τ' hτ'0 hge b₀
    by_contra hne
    have hpos : 0 < ∑ a, τ' a * (U a b₀ - V b₀) := (hge b₀).lt_of_ne (Ne.symm hne)
    set t := ∑ a, τ' a with ht
    have hexp : ∀ b, ∑ a, τ' a * (U a b - V b) = ∑ a, τ' a * U a b - t * V b := by
      intro b
      rw [ht, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have htpos : 0 < t := by
      rcases (Finset.sum_nonneg fun a (_ : a ∈ univ) => hτ'0 a).eq_or_lt with h0 | h0
      · have hz : ∀ a, τ' a = 0 := fun a =>
          (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hτ'0 a).1 h0.symm a (mem_univ a)
        simp [hz] at hpos
      · exact h0
    set τ'' : S i → ℝ := fun a => τ' a / t with hτ''
    have hτ''m : IsMixedStrategy τ'' := by
      refine ⟨fun a => div_nonneg (hτ'0 a) htpos.le, ?_⟩
      rw [hτ'', ← Finset.sum_div, ← ht, div_self htpos.ne']
    have hcmp : ∀ b, ∑ a, τ'' a * U a b - V b = (∑ a, τ' a * (U a b - V b)) / t := by
      intro b
      rw [hexp, sub_div, mul_div_cancel_left₀ _ htpos.ne', hτ'', Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun a _ => by ring
    apply hnd
    refine ⟨τ'', hτ''m, (mixedWeaklyDominates_iff_pure N i τ'' τ).2 ⟨fun s => ?_, ?_⟩⟩
    · rw [hpure, hpure]
      have := hcmp (s j)
      have h0 : 0 ≤ (∑ a, τ' a * (U a (s j) - V (s j))) / t := div_nonneg (hge _) htpos.le
      linarith
    · refine ⟨update r j b₀, ?_⟩
      rw [hpure, hpure, update_self]
      have := hcmp b₀
      have h0 : 0 < (∑ a, τ' a * (U a b₀ - V b₀)) / t := div_pos hpos htpos
      linarith
  obtain ⟨y, hypos, hya⟩ := stiemke_alternative (fun a b => U a b - V b) hno
  set Y := ∑ b, y b with hY
  have hYpos : 0 < Y := Finset.sum_pos (fun b _ => hypos b) ⟨r j, mem_univ _⟩
  refine ⟨fun b => y b / Y, ⟨⟨fun b => div_nonneg (hypos b).le hYpos.le, ?_⟩,
    fun b => div_pos (hypos b) hYpos⟩, fun σ hσ => ⟨hτ, fun τ' hτ' => ?_⟩⟩
  · rw [← Finset.sum_div, ← hY, div_self hYpos.ne']
  · rw [two_mixedPayoff_eq N hij htwo r σ, two_mixedPayoff_eq N hij htwo r σ, hσ]
    have hrow : ∀ a, ∑ b, y b / Y * U a b ≤ ∑ b, y b / Y * V b := by
      intro a
      have := hya a
      have h2 : ∑ b, y b / Y * U a b - ∑ b, y b / Y * V b =
          (∑ b, y b * (U a b - V b)) / Y := by
        rw [← Finset.sum_sub_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun b _ => by ring
      have h3 : (∑ b, y b * (U a b - V b)) / Y ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hYpos.le
      linarith
    have hswap : ∀ τ₀ : S i → ℝ, ∑ b, y b / Y * ∑ a, τ₀ a * U a b =
        ∑ a, τ₀ a * ∑ b, y b / Y * U a b := by
      intro τ₀
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hVeq : ∑ b, y b / Y * ∑ a, τ a * U a b = ∑ b, y b / Y * V b := rfl
    rw [hswap τ', hVeq]
    calc ∑ a, τ' a * ∑ b, y b / Y * U a b ≤ ∑ a, τ' a * ∑ b, y b / Y * V b :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrow a) (hτ'.1 a)
      _ = ∑ b, y b / Y * V b := by rw [← Finset.sum_mul, hτ'.2, one_mul]

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.F** (MWG, p. 259, small type). The converse of Proposition 8.F.2 for two players:
a Nash equilibrium `σ` of `[I, {Δ(S_i)}, {u_i(·)}]` with two players in which no `σ_i` is a weakly
dominated strategy is (normal form) trembling-hand perfect. (It fails with three players:
`exercise_8_F_2`.) -/
theorem isTHP_of_not_weaklyDominated_two (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {σ : (k : I) → S k → ℝ} (hσ : IsMixedNash N σ)
    (hnd : ∀ k, ¬ MixedWeaklyDominated N k (σ k)) : IsTHP N σ := by
  classical
  obtain ⟨ai, -⟩ := mixed_exists_pos (hσ.1 i)
  obtain ⟨bj, -⟩ := mixed_exists_pos (hσ.1 j)
  obtain ⟨r⟩ := two_nonempty htwo ai bj
  have htwo' : ∀ k, k = j ∨ k = i := fun k => (htwo k).symm
  obtain ⟨yj, hyj, hbri⟩ := exists_totallyMixed_bestResponse N hij htwo (hσ.1 i) (hnd i) r
  obtain ⟨yi, hyi, hbrj⟩ :=
    exists_totallyMixed_bestResponse N hij.symm htwo' (hσ.1 j) (hnd j) r
  set y : (k : I) → S k → ℝ := update (update σ i yi) j yj with hy
  have hyi' : y i = yi := by rw [hy, update_of_ne hij, update_self]
  have hyj' : y j = yj := by rw [hy, update_self]
  have hytm : ∀ k, IsTotallyMixed (y k) := by
    intro k
    rcases htwo k with rfl | rfl
    · rw [hyi']; exact hyi
    · rw [hyj']; exact hyj
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 / 2 := by
    intro n
    simp only [ht]
    gcongr
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have htlim : Tendsto t atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine squeeze_zero (fun n => (ht0 n).le) (fun n => ?_) this
    simp only [ht]
    gcongr
    linarith
  set ρ : ℕ → (k : I) → S k → ℝ := fun n => σ + t n • (y - σ) with hρ
  have hρk : ∀ n k, ρ n k = σ k + t n • (y k - σ k) := fun n k => rfl
  refine (proposition_8_F_1 N hσ).2 ⟨ρ, fun n k => ⟨⟨fun a => ?_, ?_⟩, fun a => ?_⟩, ?_,
    fun n k => ?_⟩
  · rw [hρk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (hσ.1 k).1 a
    have := (hytm k).2 a
    nlinarith [ht0 n, ht1 n]
  · rw [hρk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, (hσ.1 k).2, (hytm k).1.2]
    ring
  · rw [hρk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (hσ.1 k).1 a
    have := (hytm k).2 a
    nlinarith [ht0 n, ht1 n]
  · have : Tendsto (fun n => σ + t n • (y - σ)) atTop (𝓝 (σ + (0 : ℝ) • (y - σ))) :=
      (htlim.smul_const (y - σ)).const_add σ
    simpa using this
  · have hnash : ∀ l, IsBestResponse N l (σ l) σ := ((isMixedNash_iff_bestResponse N σ).1 hσ).2
    rcases htwo k with rfl | rfl
    · exact isBestResponse_two_mix N hij htwo r (hnash _) (hbri y hyj') (ht0 n).le
        ((ht1 n).trans (by norm_num)) (hρk n j)
    · exact isBestResponse_two_mix N hij.symm htwo' r (hnash _) (hbrj y hyi') (ht0 n).le
        ((ht1 n).trans (by norm_num)) (hρk n i)

/-! ### Rationalizability with probabilistic conjectures -/

/-- A process of iterated deletion of strictly dominated strategies (with mixed dominators,
`MSDStep`) is complete when no remaining pure strategy is strictly dominated, against the
remaining rival profiles, by a mixture of remaining strategies. -/
def MSDTerminal (N : NormalForm I S) (Q : (i : I) → Set (S i)) : Prop :=
  ∀ i, ∀ a ∈ Q i, ¬ ∃ τ' : S i → ℝ, IsMixedStrategy τ' ∧ (∀ b, 0 < τ' b → b ∈ Q i) ∧
    ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ Q j) →
      N.payoff i (update r i a) < N.mixedPayoff (update (pureProfile r) i τ') i

/-- **Footnote 1** (MWG, p. 243). `τ` is a best response to a probabilistic conjecture over the
rivals' remaining strategies `T`: its compound profile gives each rival `j` a convex combination
of strategies in `T_j`. -/
def BRToSomeConv (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) (i : I) (τ : S i → ℝ) :
    Prop :=
  ∃ σ : (j : I) → S j → ℝ, IsMixedProfile σ ∧ (∀ j, j ≠ i → σ j ∈ convexHull ℝ (T j)) ∧
    IsBestResponse N i τ σ

/-- One round of removal of the strategies that are never a best response to a probabilistic
conjecture over the remaining strategies. -/
def ratStepConv (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) :
    (i : I) → Set (S i → ℝ) :=
  fun i => {τ | τ ∈ T i ∧ BRToSomeConv N T i τ}

/-- The strategies surviving `n` rounds with probabilistic conjectures, from `Δ(S_i)`. -/
def ratIterConv (N : NormalForm I S) : ℕ → (i : I) → Set (S i → ℝ)
  | 0 => fun i => mixedExtension (S i)
  | n + 1 => ratStepConv N (ratIterConv N n)

/-- **Definition 8.C.2 with the probabilistic conjectures of footnote 1** (MWG, pp. 243-245).
The strategies in `Δ(S_i)` that survive iterated removal of strategies that are never a best
response to a probabilistic conjecture over the remaining strategies. -/
def RationalizableConv (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∀ n, τ ∈ ratIterConv N n i

omit [∀ i, DecidableEq (S i)] in
/-- Every round lies in `Δ(S_i)`. -/
theorem ratIterConv_subset (N : NormalForm I S) : ∀ n i, ratIterConv N n i ⊆ mixedExtension (S i)
  | 0 => fun _ => le_rfl
  | n + 1 => fun i _ hτ => ratIterConv_subset N n i hτ.1

omit [∀ i, DecidableEq (S i)] in
/-- A set of strategies each of which is a best response to a probabilistic conjecture over the
set is never reduced, so it consists of rationalizable strategies (in the sense of
`RationalizableConv`). -/
theorem rationalizableConv_of_bestResponseSet {N : NormalForm I S}
    {T : (i : I) → Set (S i → ℝ)} (hTΔ : ∀ i, T i ⊆ mixedExtension (S i))
    (hT : ∀ i, ∀ τ ∈ T i, BRToSomeConv N T i τ) {i : I} {τ : S i → ℝ} (hτ : τ ∈ T i) :
    RationalizableConv N i τ := by
  have key : ∀ n i, T i ⊆ ratIterConv N n i := by
    intro n
    induction n with
    | zero => exact hTΔ
    | succ n ih =>
      intro i τ hτ
      obtain ⟨σ, hσ, hσT, hbr⟩ := hT i τ hτ
      exact ⟨ih i hτ, σ, hσ, fun j hj => convexHull_mono (ih j) (hσT j hj), hbr⟩
  exact fun n => key n i hτ

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- A convex combination of vectors that vanish off `P` vanishes off `P`. -/
theorem eq_zero_of_mem_convexHull {T : Type*} {C : Set (T → ℝ)} {P : Set T}
    (hC : ∀ τ ∈ C, ∀ b ∉ P, τ b = 0) {ρ : T → ℝ} (hρ : ρ ∈ convexHull ℝ C) :
    ∀ b ∉ P, ρ b = 0 := by
  have hconv : Convex ℝ {f : T → ℝ | ∀ b ∉ P, f b = 0} := by
    intro x hx y hy a c _ _ _ b hb
    simp [hx b hb, hy b hb]
  exact convexHull_min hC hconv hρ

/-- **Section 8.C** (MWG, p. 243), with probabilistic conjectures. Along any process of iterated
deletion of strictly dominated strategies, some round of the removal of never-best responses
keeps only strategies supported on the remaining pure strategies. -/
theorem exists_ratIterConv_support_subset {N : NormalForm I S} {Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) :
    ∃ n, ∀ i, ∀ τ ∈ ratIterConv N n i, ∀ a, 0 < τ a → a ∈ Q i := by
  induction h with
  | refl => exact ⟨0, fun _ _ _ _ _ => Set.mem_univ _⟩
  | @tail P Q _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun i τ hτ a ha => ?_⟩
    have haP : a ∈ P i := hn i τ hτ.1 a ha
    by_contra haQ
    obtain ⟨τ', hτ', -, hdom⟩ := hstep.2 i a haP haQ
    obtain ⟨σ, hσ, hσT, hbr⟩ := hτ.2
    have hC : ∀ j, ∀ ρ ∈ ratIterConv N n j, ∀ c ∉ P j, ρ c = 0 := by
      intro j ρ hρ c hc
      rcases ((ratIterConv_subset N n j hρ).1 c).eq_or_lt with h0 | h0
      · exact h0.symm
      · exact absurd (hn j ρ hρ c h0) hc
    have hsuppσ : ∀ j, j ≠ i → ∀ b, 0 < σ j b → b ∈ P j := by
      intro j hj b hb
      by_contra hbP
      have := eq_zero_of_mem_convexHull (hC j) (hσT j hj) b hbP
      linarith
    have hlt := msd_dominated_lt hdom hσ hsuppσ
    have hsupp := (isBestResponse_iff_support N i hbr.1 σ).1 hbr a ha
    have h1 := mixedPayoff_le_of_pure_le N σ i hτ' i hsupp
    linarith

/-- Along any process of iterated strict dominance, a conjecture supported on the remaining
strategies of the rivals has a best reply (among all pure strategies) that remains: a best
reply is never strictly dominated against such a conjecture. -/
theorem exists_max_mem_of_msdChain {N : NormalForm I S} {P : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) P) (k : I) {σ : (j : I) → S j → ℝ}
    (hσ : IsMixedProfile σ) (hsupp : ∀ l, l ≠ k → ∀ b, 0 < σ l b → b ∈ P l) :
    ∃ a ∈ P k, ∀ c, N.mixedPayoff (update σ k (pureMixed c)) k ≤
      N.mixedPayoff (update σ k (pureMixed a)) k := by
  revert hsupp
  induction h with
  | refl =>
    intro _
    obtain ⟨a₀, -⟩ := mixed_exists_pos (hσ k)
    obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ
      (fun c => N.mixedPayoff (update σ k (pureMixed c)) k) ⟨a₀, mem_univ _⟩
    exact ⟨a, Set.mem_univ _, fun c => hmax c (mem_univ c)⟩
  | @tail P Q _ hstep ih =>
    intro hsupp
    have hsuppP : ∀ l, l ≠ k → ∀ b, 0 < σ l b → b ∈ P l :=
      fun l hl b hb => hstep.1 l (hsupp l hl b hb)
    obtain ⟨a, haP, hmax⟩ := ih hsuppP
    refine ⟨a, ?_, hmax⟩
    by_contra haQ
    obtain ⟨τ', hτ', -, hdom⟩ := hstep.2 k a haP haQ
    have hlt := msd_dominated_lt hdom hσ hsuppP
    have h1 := mixedPayoff_le_of_pure_le N σ k hτ' k hmax
    linarith

/-- **Section 8.C** (MWG, p. 245, small type), the key step. In a two-player game, a pure
strategy that survives a complete process of iterated strict dominance is a best response, among
all of `Δ(S_k)`, to a mixed strategy of the opponent supported on the opponent's survivors
(Gordan's alternative in the remaining game, then `exists_max_mem_of_msdChain`). -/
theorem exists_belief_of_msdTerminal (N : NormalForm I S) {k o : I} (hko : k ≠ o)
    (htwo : ∀ l, l = k ∨ l = o) {Q : (i : I) → Set (S i)}
    (hQ : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) (ht : MSDTerminal N Q)
    {b : S k} (hb : b ∈ Q k) :
    ∃ σ : (l : I) → S l → ℝ, IsMixedProfile σ ∧ (∀ d, 0 < σ o d → d ∈ Q o) ∧
      IsBestResponse N k (pureMixed b) σ := by
  classical
  -- the opponent has a surviving strategy
  obtain ⟨d₀, hd₀⟩ : (Q o).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    refine ht k b hb ⟨pureMixed b, isMixedStrategy_pureMixed b, fun c hc => ?_,
      fun r hr => absurd (hr o hko.symm) (by rw [hemp]; exact Set.notMem_empty _)⟩
    have : c = b := by
      by_contra hne
      simp [pureMixed, hne] at hc
    rwa [this]
  obtain ⟨r⟩ := two_nonempty htwo b d₀
  set U : S k → S o → ℝ := fun c d => N.payoff k (update (update r o d) k c) with hU
  have hpay : ∀ (τ : S k → ℝ) (s : (l : I) → S l),
      N.mixedPayoff (update (pureProfile s) k τ) k = ∑ c, τ c * U c (s o) :=
    fun τ s => two_mixedPayoff_pure N hko htwo r s τ
  have hpayb : ∀ s : (l : I) → S l, N.payoff k (update s k b) = U b (s o) := by
    intro s
    rw [← mixedPayoff_pureProfile_update, hpay]
    simp [pureMixed]
  set g : S k → S o → ℝ := fun c d => if c ∈ Q k then U c d - U b d else 0 with hg
  have hno : ¬ ∃ τ : S k → ℝ, (∀ c, 0 ≤ τ c) ∧ ∀ d ∈ Q o, 0 < ∑ c, τ c * g c d := by
    rintro ⟨τ, hτ0, hpos⟩
    set τ₀ : S k → ℝ := fun c => if c ∈ Q k then τ c else 0 with hτ₀
    have hτ₀0 : ∀ c, 0 ≤ τ₀ c := fun c => by
      simp only [hτ₀]; split_ifs
      · exact hτ0 c
      · exact le_rfl
    set t := ∑ c, τ₀ c with ht'
    have hsum : ∀ d, ∑ c, τ c * g c d = ∑ c, τ₀ c * U c d - t * U b d := by
      intro d
      rw [ht', Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hg, hτ₀]
      split_ifs <;> ring
    have htpos : 0 < t := by
      rcases (Finset.sum_nonneg fun c (_ : c ∈ univ) => hτ₀0 c).eq_or_lt with h0 | h0
      · have hz : ∀ c, τ₀ c = 0 := fun c =>
          (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hτ₀0 c).1 h0.symm c (mem_univ c)
        have := hpos d₀ hd₀
        rw [hsum] at this
        have ht0 : t = 0 := h0.symm
        simp [hz, ht0] at this
      · exact h0
    set τ' : S k → ℝ := fun c => τ₀ c / t with hτ'
    refine ht k b hb ⟨τ', ⟨fun c => div_nonneg (hτ₀0 c) htpos.le, ?_⟩, fun c hc => ?_,
      fun r' hr' => ?_⟩
    · rw [hτ', ← Finset.sum_div, ← ht', div_self htpos.ne']
    · by_contra hcQ
      simp [hτ', hτ₀, hcQ] at hc
    · rw [hpayb, hpay]
      have h1 := hpos (r' o) (hr' o hko.symm)
      rw [hsum] at h1
      have h2 : ∑ c, τ' c * U c (r' o) = (∑ c, τ₀ c * U c (r' o)) / t := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun c _ => by rw [hτ']; ring
      rw [h2, lt_div_iff₀ htpos]
      linarith
  obtain ⟨y, hy0, hyQ, hYpos, hya⟩ := gordan_alternative g (Q o) hno
  set Y := ∑ d, y d with hY
  set y' : S o → ℝ := fun d => y d / Y with hy'
  have hy'm : IsMixedStrategy y' := by
    refine ⟨fun d => div_nonneg (hy0 d) hYpos.le, ?_⟩
    rw [hy', ← Finset.sum_div, ← hY, div_self hYpos.ne']
  set σ : (l : I) → S l → ℝ := update (pureProfile r) o y' with hσdef
  have hσo : σ o = y' := by rw [hσdef, update_self]
  have hσm : IsMixedProfile σ := by
    intro l
    rcases htwo l with rfl | rfl
    · rw [hσdef, update_of_ne hko]; exact isMixedProfile_pureProfile r l
    · rw [hσo]; exact hy'm
  have hsuppo : ∀ d, 0 < σ o d → d ∈ Q o := by
    intro d hd
    by_contra hdQ
    rw [hσo, hy'] at hd
    simp [hyQ d hdQ] at hd
  have hpayσ : ∀ c, N.mixedPayoff (update σ k (pureMixed c)) k = ∑ d, y' d * U c d := by
    intro c
    rw [two_mixedPayoff_eq N hko htwo r σ, hσo]
    simp [pureMixed]
    rfl
  obtain ⟨a, haQ, hmax⟩ := exists_max_mem_of_msdChain hQ k hσm (fun l hl d hd => by
    rcases htwo l with rfl | rfl
    · exact absurd rfl hl
    · exact hsuppo d hd)
  refine ⟨σ, hσm, hsuppo, isBestResponse_pureMixed_of_max N k σ fun c => ?_⟩
  refine (hmax c).trans ?_
  rw [hpayσ, hpayσ]
  have h1 := hya a
  have h2 : ∑ d, y' d * U a d - ∑ d, y' d * U b d = (∑ d, y d * g a d) / Y := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg, haQ, ite_true, hy']
    ring
  have h3 : (∑ d, y d * g a d) / Y ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hYpos.le
  linarith

/-- **Section 8.C** (MWG, p. 245, small type), the reverse inclusion. In a two-player game, every
pure strategy that survives a complete process of iterated deletion of strictly dominated
strategies is rationalizable with probabilistic conjectures: the set of strategies that are best
responses to conjectures supported on the survivors is closed under best responses to mixtures of
its members. -/
theorem rationalizableConv_of_msdTerminal_two (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {Q : (i : I) → Set (S i)}
    (hQ : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) (ht : MSDTerminal N Q) (k : I)
    {a : S k} (ha : a ∈ Q k) : RationalizableConv N k (pureMixed a) := by
  classical
  set T : (l : I) → Set (S l → ℝ) := fun l => {τ | IsMixedStrategy τ ∧
    ∃ σ : (m : I) → S m → ℝ, IsMixedProfile σ ∧ (∀ m, m ≠ l → ∀ d, 0 < σ m d → d ∈ Q m) ∧
      IsBestResponse N l τ σ} with hT
  have hpure : ∀ l (b : S l), b ∈ Q l → pureMixed b ∈ T l := by
    intro l b hb
    obtain ⟨o, hlo, htwo'⟩ := two_other hij htwo l
    obtain ⟨σ, hσ, hsupp, hbr⟩ := exists_belief_of_msdTerminal N hlo htwo' hQ ht hb
    refine ⟨isMixedStrategy_pureMixed b, σ, hσ, fun m hm d hd => ?_, hbr⟩
    rcases htwo' m with rfl | rfl
    · exact absurd rfl hm
    · exact hsupp d hd
  refine rationalizableConv_of_bestResponseSet (T := T) (fun l τ hτ => hτ.1)
    (fun l τ hτ => ?_) (hpure k a ha)
  obtain ⟨-, σ, hσ, hsupp, hbr⟩ := hτ
  refine ⟨σ, hσ, fun m hm => ?_, hbr⟩
  have hdecomp : σ m = ∑ d ∈ univ.filter (fun d => 0 < σ m d), σ m d • pureMixed d := by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureMixed, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hc
    · rfl
    · exact le_antisymm (not_lt.1 hc) ((hσ m).1 c)
  rw [hdecomp]
  refine (convex_convexHull ℝ (T m)).sum_mem (fun d _ => (hσ m).1 d) ?_
    (fun d hd => subset_convexHull ℝ _ (hpure m d (hsupp m hm d (Finset.mem_filter.1 hd).2)))
  rw [Finset.sum_filter_of_ne fun d _ hd => ((hσ m).1 d).lt_of_ne (Ne.symm hd)]
  exact (hσ m).2

/-- **Section 8.C** (MWG, p. 245, small type), corrected. In a two-player game, a pure strategy
is rationalizable with probabilistic conjectures (footnote 1) iff it survives a complete process
of iterated deletion of strictly dominated strategies. -/
theorem rationalizableConv_iff_two (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {Q : (i : I) → Set (S i)}
    (hQ : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) (ht : MSDTerminal N Q) (k : I)
    (a : S k) : RationalizableConv N k (pureMixed a) ↔ a ∈ Q k := by
  refine ⟨fun h => ?_, rationalizableConv_of_msdTerminal_two N hij htwo hQ ht k⟩
  obtain ⟨n, hn⟩ := exists_ratIterConv_support_subset hQ
  exact hn k _ (h n) a (by simp [pureMixed])

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Instances of the two-player converses (pp. 245 and 259)

MWG, Section 8.C, p. 245, and Section 8.F, p. 259.

* **p. 245, Definition 8.C.2 read literally** (correction 9). In the two-player game
  `ratGap` (rows `a, b, c`, columns `L, R, M`) nothing is strictly dominated, so every strategy
  survives iterated strict dominance, yet row `a` is not rationalizable in the sense of
  Definition 8.C.2 (`Rationalizable`): `a` is a best response only to `½L + ½R`, which is
  strictly dominated by `M` and is removed in the first round. With the probabilistic
  conjectures of footnote 1 (`RationalizableConv`) `a` is rationalizable, as
  `rationalizableConv_iff_two` says (`rationalizable_two_counterexample`).
* **p. 259**: in Figure 8.F.1, `(U, L)` is a Nash equilibrium in which neither strategy is
  weakly dominated, so it is trembling-hand perfect (`figure_8_F_1_UL_isTHP`, an instance of
  `isTHP_of_not_weaklyDominated_two`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- If every pure strategy of every player is a best response to some mixed profile, no
strategy is strictly dominated: the full game is a complete deletion process. -/
theorem msdTerminal_full_of_bestResponse {I : Type*} {S : I → Type*} [Fintype I]
    [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {N : NormalForm I S}
    (h : ∀ i (a : S i), ∃ σ, IsMixedProfile σ ∧ IsBestResponse N i (pureMixed a) σ) :
    MSDTerminal N (fullSets S) := by
  rintro i a - ⟨τ', hτ', -, hdom⟩
  obtain ⟨σ, hσ, hbr⟩ := h i a
  have hd : MixedStrictlyDominated N i (pureMixed a) :=
    (proposition_8_B_1 N i a).2 ⟨τ', hτ', fun s => hdom s fun _ _ => Set.mem_univ _⟩
  exact neverBestResponse_of_mixedStrictlyDominated N i hd σ hσ hbr

/-! ### Rationalizability, p. 245 -/

/-- Player 1's payoffs in `ratGap`: rows `a, b, c`, columns `L, R, M`. -/
def ratGapU₁ : Fin 3 → Fin 3 → ℝ := ![![2, 2, -1], ![4, 0, 0], ![0, 4, 0]]

/-- Player 2's payoffs in `ratGap`. -/
def ratGapU₂ : Fin 3 → Fin 3 → ℝ := ![![0, 0, 1], ![3, 0, 2], ![0, 3, 2]]

/-- The two-player game separating Definition 8.C.2 from iterated strict dominance. -/
def ratGap : NormalForm (Fin 2) (S2 3 3) := bimatrix ratGapU₁ ratGapU₂

/-- The mixed strategy `½L + ½R` of player 2. -/
noncomputable def halfLR : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

theorem isMixedStrategy_halfLR : IsMixedStrategy halfLR :=
  ⟨fun b => by fin_cases b <;> norm_num [halfLR], by norm_num [halfLR, Fin.sum_univ_three]⟩

/-- In `ratGap` every pure strategy is a best response to some mixed strategy: `a` to
`½L + ½R`, `b` to `L`, `c` to `R`, `L` to `b`, `R` to `c`, `M` to `a`. -/
theorem ratGap_bestResponse (i : Fin 2) (a : S2 3 3 i) :
    ∃ σ, IsMixedProfile σ ∧ IsBestResponse ratGap i (pureMixed a) σ := by
  fin_cases i
  · change Fin 3 at a
    have key : ∀ y : Fin 3 → ℝ, IsMixedStrategy y →
        (∀ a', ∑ b, y b * ratGapU₁ a' b ≤ ∑ b, y b * ratGapU₁ a b) →
        ∃ σ, IsMixedProfile σ ∧ IsBestResponse ratGap 0 (pureMixed a) σ :=
      fun y hy h => ⟨mp (pureMixed 0) y, isMixedProfile_mp (isMixedStrategy_pureMixed _) hy,
        bimatrix_isBestResponse_row _ _ _ a h⟩
    fin_cases a
    · exact key halfLR isMixedStrategy_halfLR fun a' => by
        fin_cases a' <;> norm_num [Fin.sum_univ_three, halfLR, ratGapU₁]
    · exact key (pureMixed 0) (isMixedStrategy_pureMixed _) fun a' => by
        fin_cases a' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₁]
    · exact key (pureMixed 1) (isMixedStrategy_pureMixed _) fun a' => by
        fin_cases a' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₁]
  · change Fin 3 at a
    have key : ∀ x : Fin 3 → ℝ, IsMixedStrategy x →
        (∀ b', ∑ c, x c * ratGapU₂ c b' ≤ ∑ c, x c * ratGapU₂ c a) →
        ∃ σ, IsMixedProfile σ ∧ IsBestResponse ratGap 1 (pureMixed a) σ :=
      fun x hx h => ⟨mp x (pureMixed 0), isMixedProfile_mp hx (isMixedStrategy_pureMixed _),
        bimatrix_isBestResponse_col _ _ _ a h⟩
    fin_cases a
    · exact key (pureMixed 1) (isMixedStrategy_pureMixed _) fun b' => by
        fin_cases b' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₂]
    · exact key (pureMixed 2) (isMixedStrategy_pureMixed _) fun b' => by
        fin_cases b' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₂]
    · exact key (pureMixed 0) (isMixedStrategy_pureMixed _) fun b' => by
        fin_cases b' <;> norm_num [Fin.sum_univ_three, pureMixed, ratGapU₂]

/-- **Section 8.C, p. 245: Definition 8.C.2 read literally** (correction 9). In the two-player
game `ratGap` no strategy is strictly dominated (the full game is a complete process of iterated
strict dominance), but row `a` is not rationalizable under Definition 8.C.2; it is rationalizable
with the probabilistic conjectures of footnote 1. -/
theorem rationalizable_two_counterexample :
    MSDTerminal ratGap (fullSets (S2 3 3)) ∧ ¬ Rationalizable ratGap 0 (pureMixed (0 : Fin 3)) ∧
      RationalizableConv ratGap 0 (pureMixed (0 : Fin 3)) := by
  have hterm : MSDTerminal ratGap (fullSets (S2 3 3)) :=
    msdTerminal_full_of_bestResponse ratGap_bestResponse
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htwo : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k; fin_cases k <;> simp
  refine ⟨hterm, fun h => ?_, (rationalizableConv_iff_two ratGap h01 htwo
    Relation.ReflTransGen.refl hterm 0 (0 : Fin 3)).2 (Set.mem_univ _)⟩
  obtain ⟨-, σ, hσ, hσT, hbr⟩ := h 2
  obtain ⟨σ', hσ', -, hbr'⟩ := (hσT 1 h01.symm).2
  -- `a` is a best response only to `½L + ½R`
  set y : Fin 3 → ℝ := σ 1 with hy
  have hrow : ∀ a : Fin 3, ratGap.mixedPayoff (update σ 0 (pureMixed a)) 0 =
      ∑ b : Fin 3, y b * ratGapU₁ a b := fun a => bimatrix_mixedPayoff_row _ _ σ a
  have hb : ∑ b : Fin 3, y b * ratGapU₁ 1 b ≤ ∑ b : Fin 3, y b * ratGapU₁ 0 b := by
    rw [← hrow, ← hrow]; exact hbr.2 _ (isMixedStrategy_pureMixed _)
  have hc : ∑ b : Fin 3, y b * ratGapU₁ 2 b ≤ ∑ b : Fin 3, y b * ratGapU₁ 0 b := by
    rw [← hrow, ← hrow]; exact hbr.2 _ (isMixedStrategy_pureMixed _)
  simp only [Fin.sum_univ_three, ratGapU₁] at hb hc
  norm_num at hb hc
  have hy0 : ∀ b : Fin 3, 0 ≤ y b := (hσ 1).1
  have hy1 : ∑ b : Fin 3, y b = 1 := (hσ 1).2
  have hys : y 0 + y 1 + y 2 = 1 := by simpa [Fin.sum_univ_three] using hy1
  have hy2 : y 2 = 0 := by linarith [hy0 0, hy0 1, hy0 2]
  have hy01 : y 0 = 1 / 2 ∧ y 1 = 1 / 2 := by constructor <;> linarith
  -- `½L + ½R` is strictly dominated by `M`, so it is never a best response
  have hdom := (bimatrix_mixedStrictlyDominates_one_iff ratGapU₁ ratGapU₂
    (pureMixed (2 : Fin 3)) y).2 (fun a => by
      fin_cases a <;>
        simp [Fin.sum_univ_three, ratGapU₂, pureMixed, hy2, hy01.1, hy01.2] <;> norm_num)
  exact neverBestResponse_of_mixedStrictlyDominated ratGap 1
    ⟨_, isMixedStrategy_pureMixed (2 : Fin 3), hdom⟩ σ' hσ' hbr'

/-! ### Trembling-hand perfection, p. 259 -/

/-- **Section 8.F** (MWG, p. 259, small type), an instance of the two-player converse of
Proposition 8.F.2. In Figure 8.F.1, `(U, L)` is a Nash equilibrium in which neither `U` nor `L`
is weakly dominated (by any mixed strategy), so it is trembling-hand perfect. -/
theorem figure_8_F_1_UL_isTHP :
    IsTHP (bimatrix fig8F1U₁ fig8F1U₂) (pureProfile (pp (0 : Fin 2) (0 : Fin 2))) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have htwo : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k; fin_cases k <;> simp
  have hNE : IsNashEquilibrium (bimatrix fig8F1U₁ fig8F1U₂) (pp (0 : Fin 2) (0 : Fin 2)) :=
    (bimatrix_isNash_iff _ _ _ _).2 ⟨fun a => by fin_cases a <;> norm_num [fig8F1U₁],
      fun b => by fin_cases b <;> norm_num [fig8F1U₂]⟩
  refine isTHP_of_not_weaklyDominated_two _ h01 htwo ((corollary_8_D_1 _ _).1 hNE) fun k => ?_
  rintro ⟨τ', hτ', hdom⟩
  obtain ⟨hle, s, hlt⟩ := (mixedWeaklyDominates_iff_pure _ _ _ _).1 hdom
  have e1 := hle (pp (0 : Fin 2) (0 : Fin 2))
  rcases htwo k with rfl | rfl
  · set x : Fin 2 → ℝ := τ' with hx
    have h0 : ∀ a : Fin 2, 0 ≤ x a := hτ'.1
    have h2 : ∑ a : Fin 2, x a = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 2 2 i,
        (bimatrix fig8F1U₁ fig8F1U₂).mixedPayoff
          (update (pureProfile s') 0 (pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 0)) 0 =
        fig8F1U₁ 0 (s' 1) := fun s' => by
      rw [show pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 0 =
        pureMixed (pp (0 : Fin 2) (0 : Fin 2) 0) from rfl, mixedPayoff_pureProfile_update]
      simp
    rw [hL, bimatrix_mixed_vs_pure_zero] at e1 hlt
    simp only [Fin.sum_univ_two, pp_one] at e1 hlt h2
    norm_num [fig8F1U₁] at e1
    have hx1 : x 1 = 0 := by linarith [h0 0, h0 1]
    have hx0 : x 0 = 1 := by linarith
    rw [← hx, hx0, hx1] at hlt
    simp at hlt
  · set x : Fin 2 → ℝ := τ' with hx
    have h0 : ∀ a : Fin 2, 0 ≤ x a := hτ'.1
    have h2 : ∑ a : Fin 2, x a = 1 := hτ'.2
    have hL : ∀ s' : (i : Fin 2) → S2 2 2 i,
        (bimatrix fig8F1U₁ fig8F1U₂).mixedPayoff
          (update (pureProfile s') 1 (pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 1)) 1 =
        fig8F1U₂ (s' 0) 0 := fun s' => by
      rw [show pureProfile (pp (0 : Fin 2) (0 : Fin 2)) 1 =
        pureMixed (pp (0 : Fin 2) (0 : Fin 2) 1) from rfl, mixedPayoff_pureProfile_update]
      simp
    rw [hL, bimatrix_mixed_vs_pure_one] at e1 hlt
    simp only [Fin.sum_univ_two, pp_zero] at e1 hlt h2
    norm_num [fig8F1U₂] at e1
    have hx1 : x 1 = 0 := by linarith [h0 0, h0 1]
    have hx0 : x 0 = 1 := by linarith
    rw [← hx, hx0, hx1] at hlt
    simp at hlt

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 8.B.3 and 8.D.3: second-price and first-price auctions

MWG, Exercises 8.B.3 and 8.D.3, pp. 262-263.

**Exercise 8.B.3 (Vickrey auction).** `I` bidders bid nonnegative amounts (`ℝ≥0`); bidder `i`
values the object at `v_i ≥ 0`. If `b_i` is at least the highest rival bid `m_i = max_{j ≠ i} b_j`
then `i` is among the highest bidders, wins with probability `1 / (1 + #{j ≠ i : b_j = b_i})` and
pays the second-highest bid, which is `m_i` (with a tie at the top it equals the highest bid).
So `u_i(b) = (v_i - m_i) / (1 + #{j ≠ i : b_j = b_i})` if `m_i ≤ b_i` and `0` otherwise
(`vickrey`). Bidding `v_i` is a weakly dominant strategy and the only one
(`exercise_8_B_3`) as soon as there are two bidders; with a single bidder every bid pays `v_i`
and nothing is weakly dominant (`exercise_8_B_3_one_bidder`, correction 10).

**Exercise 8.D.3 (first-price auction with dollar bids).** Two bidders with integer values
`v_i ∈ ℕ` bid `b_i ∈ ℕ`; the higher bid wins and pays its bid, ties split the object.
* (a) No strategy is strictly dominated (`exercise_8_D_3a`): against a rival bid above both
  bids, both lose.
* (b) Bid `b` of bidder `i` is weakly dominated iff `b ≥ max(v_i, 1)` (dominated by
  `max(v_i - 1, 0)`), or `b = 0` and `v_i ≥ 2` (dominated by `1`) (`exercise_8_D_3b`).
* (c) The pure Nash equilibria are: a tie `b_1 = b_2 = b` with `b ≤ v_i ≤ b + 2` for both
  bidders, or the higher-value bidder winning with a bid one dollar above the loser's, at
  least the loser's value and at most his own value minus one (`exercise_8_D_3c`). An
  equilibrium always exists (`exercise_8_D_3c_exists`) and is not unique in general
  (`exercise_8_D_3c_not_unique`: with `v = (1, 1)` both `(0, 0)` and `(1, 1)` are equilibria).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset NNReal

/-! ### Exercise 8.B.3: the Vickrey auction -/

/-- **Exercise 8.B.3** (MWG, p. 262). The second-price sealed-bid auction with `I` bidders and
valuations `v_i ≥ 0`: bids are nonnegative; with `m_i = max_{j ≠ i} b_j`, bidder `i` gets
`(v_i - m_i) / (1 + #{j ≠ i : b_j = b_i})` if `m_i ≤ b_i` and `0` otherwise. -/
noncomputable def vickrey {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℝ≥0) :
    NormalForm I (fun _ => ℝ≥0) where
  payoff i b := if (univ.erase i).sup b ≤ b i then
    ((v i : ℝ) - ((univ.erase i).sup b : ℝ≥0)) /
      (1 + ((univ.erase i).filter fun j => b j = b i).card)
    else 0

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Bidder `i`'s payoff from the bid `x` depends on the rivals' bids only. -/
theorem vickrey_update (v : I → ℝ≥0) (i : I) (r : I → ℝ≥0) (x : ℝ≥0) :
    (vickrey v).payoff i (update r i x) = if (univ.erase i).sup r ≤ x then
      ((v i : ℝ) - ((univ.erase i).sup r : ℝ≥0)) /
        (1 + ((univ.erase i).filter fun j => r j = x).card) else 0 := by
  have hsup : (univ.erase i).sup (update r i x) = (univ.erase i).sup r :=
    Finset.sup_congr rfl fun j hj => update_of_ne (ne_of_mem_erase hj) _ _
  have hfil : ((univ.erase i).filter fun j => update r i x j = x) =
      (univ.erase i).filter fun j => r j = x :=
    Finset.filter_congr fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [vickrey, hsup, update_self, hfil]

/-- Truthful bidding gets `max(v_i - m_i, 0)`. -/
theorem vickrey_truthful (v : I → ℝ≥0) (i : I) (r : I → ℝ≥0) :
    (vickrey v).payoff i (update r i (v i)) = max ((v i : ℝ) - ((univ.erase i).sup r : ℝ≥0)) 0 := by
  rw [vickrey_update]
  set M := (univ.erase i).sup r with hM
  split_ifs with h
  · rcases h.lt_or_eq with hlt | heq
    · have hk : ((univ.erase i).filter fun j => r j = v i).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj hrj
        have := Finset.le_sup (f := r) hj
        rw [hrj, ← hM] at this
        exact absurd hlt (not_lt.2 this)
      rw [hk]
      have : (M : ℝ) < v i := by exact_mod_cast hlt
      simp [max_eq_left (by linarith : (0 : ℝ) ≤ (v i : ℝ) - M)]
    · rw [heq]; simp
  · have : (v i : ℝ) < M := by exact_mod_cast not_le.1 h
    rw [max_eq_right (by linarith)]

/-- Against any rival bids, truthful bidding is at least as good as any bid `x`. -/
theorem vickrey_le_truthful (v : I → ℝ≥0) (i : I) (r : I → ℝ≥0) (x : ℝ≥0) :
    (vickrey v).payoff i (update r i x) ≤ (vickrey v).payoff i (update r i (v i)) := by
  rw [vickrey_truthful, vickrey_update]
  split_ifs
  · set k := (((univ.erase i).filter fun j => r j = x).card : ℝ)
    have hk : (1 : ℝ) ≤ 1 + k := by simp [k]
    rcases le_or_gt 0 ((v i : ℝ) - ((univ.erase i).sup r : ℝ≥0)) with h0 | h0
    · exact (div_le_self h0 hk).trans (le_max_left _ _)
    · exact (div_neg_of_neg_of_pos h0 (by linarith)).le.trans (le_max_right _ _)
  · exact le_max_right _ _

/-- With all rivals bidding `z`, the highest rival bid is `z`. -/
theorem vickrey_sup_const (i j : I) (hj : j ≠ i) (z : ℝ≥0) :
    (univ.erase i).sup (fun _ => z) = z :=
  Finset.sup_const ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩⟩ z

/-- **Exercise 8.B.3** (MWG, p. 262). With at least two bidders, bidding one's valuation `v_i` is
a weakly dominant strategy in the Vickrey auction, and it is bidder `i`'s unique weakly dominant
strategy. -/
theorem exercise_8_B_3 (v : I → ℝ≥0) (i : I) (hI : ∃ j, j ≠ i) :
    WeaklyDominant (vickrey v) i (v i) ∧ ∀ x, WeaklyDominant (vickrey v) i x → x = v i := by
  obtain ⟨j, hj⟩ := hI
  have hdom : WeaklyDominant (vickrey v) i (v i) := by
    intro x hx
    refine ⟨fun r => vickrey_le_truthful v i r x, ?_⟩
    -- all rivals bid strictly between `x` and `v_i`
    set z : ℝ≥0 := ⟨((x : ℝ) + v i) / 2, by positivity⟩ with hz
    have hzr : (z : ℝ) = ((x : ℝ) + v i) / 2 := rfl
    refine ⟨fun _ => z, ?_⟩
    rw [vickrey_truthful, vickrey_update, vickrey_sup_const i j hj]
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hlt' : (x : ℝ) < v i := by exact_mod_cast hlt
      have hxz : ¬ z ≤ x := by
        rw [← NNReal.coe_le_coe, hzr]; linarith
      simp only [hxz, ↓reduceIte]
      rw [hzr, max_eq_left (by linarith)]
      linarith
    · have hgt' : (v i : ℝ) < x := by exact_mod_cast hgt
      have hxz : z ≤ x := by
        rw [← NNReal.coe_le_coe, hzr]; linarith
      simp only [hxz, ↓reduceIte]
      rw [hzr, max_eq_right (by linarith)]
      refine div_neg_of_neg_of_pos (by linarith) ?_
      positivity
  exact ⟨hdom, fun x hx =>
    @weaklyDominant_unique I (fun _ => ℝ≥0) _ (vickrey v) i x (v i) hx hdom⟩

/-- **Exercise 8.B.3 with one bidder** (correction 10). With a single bidder every bid pays
`v_1`, so truthful bidding is not weakly dominant (it does not weakly dominate the bid
`v_1 + 1`). -/
theorem exercise_8_B_3_one_bidder (v : Unit → ℝ≥0) :
    ¬ WeaklyDominant (vickrey v) () (v ()) := by
  intro h
  obtain ⟨-, r, hr⟩ := h (v () + 1) (by simp)
  rw [vickrey_update, vickrey_update] at hr
  simp at hr

/-- A concrete instance of Exercise 8.B.3: two bidders who value the object at `1`. -/
theorem exercise_8_B_3_instance : WeaklyDominant (vickrey (fun _ : Fin 2 => (1 : ℝ≥0))) 0 1 :=
  (exercise_8_B_3 _ 0 ⟨1, by decide⟩).1

/-! ### Exercise 8.D.3: the first-price auction with dollar bids -/

/-- Twice the payoff, an integer: bidding `x` against the rival bid `y` with value `v` gives
`2(v - x)` when winning, `v - x` when tying and `0` when losing. -/
def fpInt (v x y : ℕ) : ℤ :=
  if y < x then 2 * ((v : ℤ) - x) else if x = y then (v : ℤ) - x else 0

/-- **Exercise 8.D.3** (MWG, p. 263). The payoff of a bidder with value `v` who bids `x` against
the rival bid `y` in the first-price auction: `v - x` if `x > y`, `(v - x)/2` if `x = y`, `0`
otherwise. -/
noncomputable def fpPay (v x y : ℕ) : ℝ :=
  if y < x then (v : ℝ) - x else if x = y then ((v : ℝ) - x) / 2 else 0

theorem fpPay_eq (v x y : ℕ) : fpPay v x y = (fpInt v x y : ℝ) / 2 := by
  unfold fpPay fpInt
  split_ifs <;> push_cast <;> ring

theorem fpPay_le_iff (v x y v' x' y' : ℕ) :
    fpPay v x y ≤ fpPay v' x' y' ↔ fpInt v x y ≤ fpInt v' x' y' := by
  rw [fpPay_eq, fpPay_eq, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast Iff.rfl

theorem fpPay_lt_iff (v x y v' x' y' : ℕ) :
    fpPay v x y < fpPay v' x' y' ↔ fpInt v x y < fpInt v' x' y' := by
  rw [fpPay_eq, fpPay_eq, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast Iff.rfl

/-- **Exercise 8.D.3** (MWG, p. 263). The first-price sealed-bid auction with two bidders,
integer valuations `v_i` and bids in whole dollars. -/
noncomputable def firstPrice (v : Fin 2 → ℕ) : NormalForm (Fin 2) (fun _ => ℕ) where
  payoff i b := fpPay (v i) (b i) (b (1 - i))

theorem one_sub_ne (i : Fin 2) : 1 - i ≠ i := by
  fin_cases i <;> decide

theorem firstPrice_update (v : Fin 2 → ℕ) (i : Fin 2) (r : Fin 2 → ℕ) (x : ℕ) :
    (firstPrice v).payoff i (update r i x) = fpPay (v i) x (r (1 - i)) := by
  simp only [firstPrice, update_self, update_of_ne (one_sub_ne i)]

/-- Weak domination in the first-price auction, in terms of the rival's bid. -/
theorem firstPrice_weaklyDominates_iff (v : Fin 2 → ℕ) (i : Fin 2) (x' x : ℕ) :
    WeaklyDominates (firstPrice v) i x' x ↔
      (∀ y, fpInt (v i) x y ≤ fpInt (v i) x' y) ∧ ∃ y, fpInt (v i) x y < fpInt (v i) x' y := by
  constructor
  · rintro ⟨hle, r, hr⟩
    refine ⟨fun y => ?_, r (1 - i), ?_⟩
    · have := hle (fun _ => y)
      rwa [firstPrice_update, firstPrice_update, fpPay_le_iff] at this
    · rwa [firstPrice_update, firstPrice_update, fpPay_lt_iff] at hr
  · rintro ⟨hle, y, hy⟩
    refine ⟨fun r => ?_, fun _ => y, ?_⟩
    · rw [firstPrice_update, firstPrice_update, fpPay_le_iff]; exact hle _
    · rw [firstPrice_update, firstPrice_update, fpPay_lt_iff]; exact hy

/-- **Exercise 8.D.3(a)** (MWG, p. 263). No strategy is strictly dominated: against a rival bid
above both bids, both bids lose. -/
theorem exercise_8_D_3a (v : Fin 2 → ℕ) (i : Fin 2) (x : ℕ) :
    ¬ StrictlyDominated (firstPrice v) i x := by
  rintro ⟨x', hx'⟩
  have := hx' (fun _ => max x x' + 1)
  rw [firstPrice_update, firstPrice_update, fpPay_lt_iff] at this
  unfold fpInt at this
  split_ifs at this <;> omega

/-- **Exercise 8.D.3(b)** (MWG, p. 263). Bidder `i`'s bid `x` is weakly dominated iff
`x ≥ max(v_i, 1)` or (`x = 0` and `v_i ≥ 2`). -/
theorem exercise_8_D_3b (v : Fin 2 → ℕ) (i : Fin 2) (x : ℕ) :
    WeaklyDominated (firstPrice v) i x ↔ (v i ≤ x ∧ 1 ≤ x) ∨ (x = 0 ∧ 2 ≤ v i) := by
  set w := v i with hw
  constructor
  · rintro ⟨x', hdom⟩
    rw [firstPrice_weaklyDominates_iff] at hdom
    obtain ⟨hle, y, hy⟩ := hdom
    by_contra hcond
    have hxx' : x' ≠ x := by rintro rfl; exact lt_irrefl _ hy
    rw [← hw] at hle hy
    -- a rival bid against which `x` does strictly better than `x'`
    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
    · subst hx0
      have h1 := hle 0
      unfold fpInt at h1
      split_ifs at h1 <;> omega
    · rcases lt_or_gt_of_ne hxx' with hlt | hgt
      · have h1 := hle x
        unfold fpInt at h1
        split_ifs at h1 <;> omega
      · have h1 := hle (x - 1)
        unfold fpInt at h1
        split_ifs at h1 <;> omega
  · rintro (⟨hvx, hx1⟩ | ⟨rfl, hv2⟩)
    · refine ⟨w - 1, (firstPrice_weaklyDominates_iff v i _ _).2 ⟨fun y => ?_, ?_⟩⟩
      · rw [← hw]; unfold fpInt; split_ifs <;> omega
      · rcases Nat.eq_zero_or_pos w with hw0 | hwpos
        · refine ⟨0, ?_⟩
          rw [← hw]; unfold fpInt; split_ifs <;> omega
        · refine ⟨w - 1, ?_⟩
          rw [← hw]; unfold fpInt; split_ifs <;> omega
    · refine ⟨1, (firstPrice_weaklyDominates_iff v i _ _).2 ⟨fun y => ?_, 1, ?_⟩⟩
      · rw [← hw]; unfold fpInt; split_ifs <;> omega
      · rw [← hw]; unfold fpInt; simp; omega

/-- The best payoff against the rival bid `y`: `(∀ x, 2u(x, y) ≤ W)` iff `W` is at least the
payoff of losing (when possible), of tying and of winning by one dollar. -/
theorem fpInt_bound_iff (w y : ℕ) (W : ℤ) :
    (∀ x, fpInt w x y ≤ W) ↔
      ((1 ≤ y → 0 ≤ W) ∧ (w : ℤ) - y ≤ W ∧ 2 * ((w : ℤ) - (y + 1)) ≤ W) := by
  constructor
  · intro h
    refine ⟨fun hy => ?_, ?_, ?_⟩
    · have := h 0
      unfold fpInt at this
      split_ifs at this <;> omega
    · have := h y
      unfold fpInt at this
      split_ifs at this <;> omega
    · have := h (y + 1)
      unfold fpInt at this
      split_ifs at this <;> push_cast at this <;> omega
  · rintro ⟨h0, h1, h2⟩ x
    unfold fpInt
    split_ifs <;> omega

/-- Nash equilibrium in the first-price auction: each bid is a best reply to the other. -/
theorem firstPrice_isNash_iff (v : Fin 2 → ℕ) (b : Fin 2 → ℕ) :
    IsNashEquilibrium (firstPrice v) b ↔
      (∀ x, fpInt (v 0) x (b 1) ≤ fpInt (v 0) (b 0) (b 1)) ∧
        ∀ x, fpInt (v 1) x (b 0) ≤ fpInt (v 1) (b 1) (b 0) := by
  have h0 : ∀ x, (firstPrice v).payoff 0 (update b 0 x) = fpPay (v 0) x (b 1) :=
    fun x => firstPrice_update v 0 b x
  have h1 : ∀ x, (firstPrice v).payoff 1 (update b 1 x) = fpPay (v 1) x (b 0) :=
    fun x => firstPrice_update v 1 b x
  have e0 : (firstPrice v).payoff 0 b = fpPay (v 0) (b 0) (b 1) := by
    rw [← h0, update_eq_self]
  have e1 : (firstPrice v).payoff 1 b = fpPay (v 1) (b 1) (b 0) := by
    rw [← h1, update_eq_self]
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := h 0 x; rwa [h0, e0, fpPay_le_iff] at this
    · have := h 1 x; rwa [h1, e1, fpPay_le_iff] at this
  · rintro ⟨ha, hb⟩ i x
    fin_cases i
    · change (firstPrice v).payoff 0 (update b 0 x) ≤ (firstPrice v).payoff 0 b
      rw [h0, e0, fpPay_le_iff]; exact ha x
    · change (firstPrice v).payoff 1 (update b 1 x) ≤ (firstPrice v).payoff 1 b
      rw [h1, e1, fpPay_le_iff]; exact hb x

/-- **Exercise 8.D.3(c)** (MWG, p. 263). The pure strategy Nash equilibria of the first-price
auction with dollar bids: either both bid the same `b` with `b ≤ v_i ≤ b + 2` for both bidders, or
one bidder wins with a bid one dollar above the other's, at least the loser's value and at most
the winner's value minus one. -/
theorem exercise_8_D_3c (v : Fin 2 → ℕ) (b : Fin 2 → ℕ) :
    IsNashEquilibrium (firstPrice v) b ↔
      (b 0 = b 1 ∧ b 0 ≤ v 0 ∧ b 0 ≤ v 1 ∧ v 0 ≤ b 0 + 2 ∧ v 1 ≤ b 0 + 2) ∨
        (b 0 = b 1 + 1 ∧ v 1 ≤ b 0 ∧ b 0 + 1 ≤ v 0) ∨
          (b 1 = b 0 + 1 ∧ v 0 ≤ b 1 ∧ b 1 + 1 ≤ v 1) := by
  rw [firstPrice_isNash_iff, fpInt_bound_iff, fpInt_bound_iff]
  unfold fpInt
  split_ifs <;> omega

/-- **Exercise 8.D.3(c)** (MWG, p. 263). A pure strategy Nash equilibrium always exists: a tie at
the lower value when the values differ by at most two, and otherwise the higher-value bidder bids
one dollar above the other's value, which the other bids. -/
theorem exercise_8_D_3c_exists (v : Fin 2 → ℕ) : ∃ b, IsNashEquilibrium (firstPrice v) b := by
  by_cases h : v 0 ≤ v 1 + 2 ∧ v 1 ≤ v 0 + 2
  · rcases le_total (v 0) (v 1) with h01 | h10
    · exact ⟨fun _ => v 0, (exercise_8_D_3c v _).2 (Or.inl (by omega))⟩
    · exact ⟨fun _ => v 1, (exercise_8_D_3c v _).2 (Or.inl (by omega))⟩
  · rcases not_and_or.1 h with h1 | h1
    · refine ⟨fun k => if k = 0 then v 1 + 1 else v 1,
        (exercise_8_D_3c v _).2 (Or.inr (Or.inl ?_))⟩
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [h10, ↓reduceIte, true_and]
      omega
    · refine ⟨fun k => if k = 0 then v 0 else v 0 + 1,
        (exercise_8_D_3c v _).2 (Or.inr (Or.inr ?_))⟩
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [h10, ↓reduceIte, true_and]
      omega

/-- **Exercise 8.D.3(c)** (MWG, p. 263). The equilibrium need not be unique: with `v = (1, 1)`
both `(0, 0)` and `(1, 1)` are Nash equilibria. -/
theorem exercise_8_D_3c_not_unique :
    IsNashEquilibrium (firstPrice ![1, 1]) ![0, 0] ∧
      IsNashEquilibrium (firstPrice ![1, 1]) ![1, 1] := by
  refine ⟨(exercise_8_D_3c _ _).2 (Or.inl ?_), (exercise_8_D_3c _ _).2 (Or.inl ?_)⟩ <;>
    simp

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 8.B.5: iterated dominance in the Cournot model

MWG, Exercise 8.B.5, p. 262.

Firms `i ∈ I` choose quantities `q_i ≥ 0`; the price is `P = a - b ∑_j q_j` and unit cost is `c`,
so with `A = a - c` and rivals' total `X`, firm `i` earns `q_i (A - bX - b q_i)` (`cournot`).
Its best response to `X` is `r(X) = (A - bX)/(2b)` when `A ≥ bX`.

The deletion process needs infinitely many rounds, so it is formalized as the *maximal*
process: at each round every strategy that is strictly dominated (by a remaining strategy,
against the remaining rival strategies) is removed (`sdRound`, which is a deletion step of
Section 8.B, `sdStep_sdRound`); `sdIter N n` is what survives `n` rounds and the prediction is
the limit `⋂ₙ sdIter N n i`.

* `cournot_round`: if each firm's remaining set is `[L, U]` and the rivals' total ranges over
  `[kL, kU]` (`k` rivals), one round leaves `[r(kU), r(kL)]` (under the invariant that keeps the
  intervals nested); the first round leaves `[0, A/(2b)]` (`cournot_round_zero`).
* **Exercise 8.B.5(a)** (`exercise_8_B_5a`): with two firms the surviving sets are the intervals
  `[L_n, U_n]` of `cournotBounds`, whose width halves each round; every finite round leaves a
  continuum of strategies, and the limit is the single quantity `q* = (a - c)/(3b)`.
* **Exercise 8.B.5(b)** (`exercise_8_B_5b`): with three firms the process stops after one round
  at `[0, (a - c)/(2b)]` for every firm (nothing there is dominated: two rivals can total any
  amount in `[0, (a - c)/b]`), so there is no unique prediction.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset NNReal Filter Topology

/-! ### The maximal deletion process -/

variable {I : Type*} {S : I → Type*} [DecidableEq I]

/-- **Section 8.B** (MWG, pp. 238-240). One round of the maximal deletion process: remove every
remaining strategy that is strictly dominated in the remaining game. -/
def sdRound (N : NormalForm I S) (T : (i : I) → Set (S i)) : (i : I) → Set (S i) :=
  fun i => {s | s ∈ T i ∧ ¬ SDominatedIn N T i s}

/-- The strategies surviving `n` rounds of the maximal deletion process. -/
def sdIter (N : NormalForm I S) : ℕ → (i : I) → Set (S i)
  | 0 => fullSets S
  | n + 1 => sdRound N (sdIter N n)

/-- A round of the maximal process is a deletion step (Section 8.B). -/
theorem sdStep_sdRound (N : NormalForm I S) (T : (i : I) → Set (S i)) :
    SDStep N T (sdRound N T) :=
  ⟨fun _ _ hs => hs.1, fun i s hs hs' => by
    by_contra hnd
    exact hs' ⟨hs, hnd⟩⟩

/-- Every stage of the maximal process is reached by a deletion process from the full game. -/
theorem sdIter_chain (N : NormalForm I S) :
    ∀ n, Relation.ReflTransGen (SDStep N) (fullSets S) (sdIter N n)
  | 0 => Relation.ReflTransGen.refl
  | n + 1 => (sdIter_chain N n).tail (sdStep_sdRound N _)

/-! ### The Cournot game -/

/-- **Exercise 8.B.5** (MWG, p. 262). The Cournot game with firms `I`, inverse demand
`P = a - b ∑_j q_j` and unit cost `c`: `u_i(q) = (a - b ∑_j q_j) q_i - c q_i`. -/
def cournot (I : Type*) [Fintype I] (a b c : ℝ) : NormalForm I (fun _ => ℝ≥0) where
  payoff i q := (a - b * ∑ j, (q j : ℝ)) * q i - c * q i

/-- The rivals' total output `X = ∑_{j ≠ i} q_j`. -/
def rivalsTotal [Fintype I] (r : I → ℝ≥0) (i : I) : ℝ := ∑ j ∈ univ.erase i, (r j : ℝ)

/-- The interval `{q ≥ 0 : L ≤ q ≤ U}` of quantities. -/
def qIval (L U : ℝ) : Set ℝ≥0 := {q | L ≤ (q : ℝ) ∧ (q : ℝ) ≤ U}

/-- The best response `r(X) = (A - bX)/(2b)`. -/
noncomputable def cbr (A b X : ℝ) : ℝ := (A - b * X) / (2 * b)

variable [Fintype I]

/-- Firm `i`'s profit from `s` against the rivals' outputs: `s (A - bX - bs)`, `A = a - c`. -/
theorem cournot_update (a b c : ℝ) (i : I) (r : I → ℝ≥0) (s : ℝ≥0) :
    (cournot I a b c).payoff i (update r i s) =
      (s : ℝ) * ((a - c) - b * rivalsTotal r i - b * s) := by
  have hsum : ∑ j, ((update r i s j : ℝ≥0) : ℝ) = s + rivalsTotal r i := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  simp only [cournot, hsum, update_self]
  ring

/-- With every rival producing `x`, the rivals' total is `k x`, `k = |I| - 1`. -/
theorem rivalsTotal_const (i : I) (x : ℝ≥0) :
    rivalsTotal (fun _ => x) i = ((Fintype.card I - 1 : ℕ) : ℝ) * x := by
  simp [rivalsTotal, Finset.card_erase_of_mem]

/-- If every rival's output lies in `[L, U]`, the rivals' total lies in `[kL, kU]`. -/
theorem rivalsTotal_mem {L U : ℝ} (i : I) {r : I → ℝ≥0}
    (hr : ∀ j, j ≠ i → r j ∈ qIval L U) :
    ((Fintype.card I - 1 : ℕ) : ℝ) * L ≤ rivalsTotal r i ∧
      rivalsTotal r i ≤ ((Fintype.card I - 1 : ℕ) : ℝ) * U := by
  have hcard : (univ.erase i).card = Fintype.card I - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ]
  constructor
  · have := Finset.card_nsmul_le_sum (univ.erase i) (fun j => (r j : ℝ)) L
      fun j hj => (hr j (ne_of_mem_erase hj)).1
    rwa [hcard, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (univ.erase i) (fun j => (r j : ℝ)) U
      fun j hj => (hr j (ne_of_mem_erase hj)).2
    rwa [hcard, nsmul_eq_mul] at this

/-- The profit gap between `s'` and `s` against the rivals' total `X`. -/
theorem cournot_gap (A b X s s' : ℝ) :
    s' * (A - b * X - b * s') - s * (A - b * X - b * s) =
      (s' - s) * (A - b * X - b * (s + s')) := by
  ring

/-- A best response is never strictly dominated: if some admissible rivals' profile has
`bX = A - 2bs`, then `s` is not strictly dominated. -/
theorem cournot_not_dominated {a b c : ℝ} (hb : 0 < b) {T : I → Set ℝ≥0} {i : I} {s : ℝ≥0}
    {r : I → ℝ≥0} (hr : ∀ j, j ≠ i → r j ∈ T j)
    (hX : b * rivalsTotal r i = (a - c) - 2 * b * s) :
    ¬ SDominatedIn (cournot I a b c) T i s := by
  rintro ⟨s', -, hdom⟩
  have h := hdom r hr
  rw [cournot_update a b c i r s, cournot_update a b c i r, hX] at h
  nlinarith [sq_nonneg ((s : ℝ) - s')]

/-- **Exercise 8.B.5**, one round of deletion. Each firm's remaining quantities are `[L, U]` and
there are `k = |I| - 1 ≥ 1` rivals. Under the invariant `0 ≤ L ≤ U`, `L ≤ r(kU)`, `r(kL) ≤ U`,
`bkU ≤ A`, one round leaves `[r(kU), r(kL)]`. -/
theorem cournot_round {a b c : ℝ} (hb : 0 < b) (i : I) (hk : 1 ≤ Fintype.card I - 1)
    {L U : ℝ} (hL : 0 ≤ L) (hLU : L ≤ U)
    (h1 : L ≤ cbr (a - c) b ((Fintype.card I - 1 : ℕ) * U))
    (h2 : cbr (a - c) b ((Fintype.card I - 1 : ℕ) * L) ≤ U)
    (h3 : b * ((Fintype.card I - 1 : ℕ) * U) ≤ a - c) :
    sdRound (cournot I a b c) (fun _ => qIval L U) i =
      qIval (cbr (a - c) b ((Fintype.card I - 1 : ℕ) * U))
        (cbr (a - c) b ((Fintype.card I - 1 : ℕ) * L)) := by
  set k : ℝ := ((Fintype.card I - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hk
  set rU := cbr (a - c) b (k * U) with hrU
  set rL := cbr (a - c) b (k * L) with hrL
  have hrUrL : rU ≤ rL := by
    simp only [hrU, hrL, cbr]
    gcongr
  have hrU0 : 0 ≤ rU := by
    simp only [hrU, cbr]; exact div_nonneg (by linarith) (by linarith)
  have h2b : rU * (2 * b) = (a - c) - b * (k * U) := by
    simp only [hrU, cbr]; field_simp
  have h2b' : rL * (2 * b) = (a - c) - b * (k * L) := by
    simp only [hrL, cbr]; field_simp
  ext s
  constructor
  · rintro ⟨hsT, hnd⟩
    constructor
    · by_contra hlt
      push Not at hlt
      apply hnd
      set s' : ℝ≥0 := ⟨rU, hrU0⟩ with hs'
      have hs'v : (s' : ℝ) = rU := rfl
      refine ⟨s', ⟨h1, hrUrL.trans h2⟩, fun r hr => ?_⟩
      have hX := (rivalsTotal_mem i hr).2
      rw [← hkdef] at hX
      rw [cournot_update a b c i r s, cournot_update a b c i r s', hs'v]
      have hgap := cournot_gap (a - c) b (rivalsTotal r i) s rU
      have hpos : 0 < (rU - s) * ((a - c) - b * rivalsTotal r i - b * (s + rU)) := by
        apply mul_pos (by linarith)
        nlinarith
      linarith
    · by_contra hlt
      push Not at hlt
      apply hnd
      set s' : ℝ≥0 := ⟨rL, hrU0.trans hrUrL⟩ with hs'
      have hs'v : (s' : ℝ) = rL := rfl
      refine ⟨s', ⟨h1.trans hrUrL, h2⟩, fun r hr => ?_⟩
      have hX := (rivalsTotal_mem i hr).1
      rw [← hkdef] at hX
      rw [cournot_update a b c i r s, cournot_update a b c i r s', hs'v]
      have hgap := cournot_gap (a - c) b (rivalsTotal r i) s rL
      have hneg : (rL - s) * ((a - c) - b * rivalsTotal r i - b * (s + rL)) > 0 := by
        apply mul_pos_of_neg_of_neg (by linarith)
        nlinarith
      linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨h1.trans hlo, hhi.trans h2⟩, ?_⟩
    -- the rivals' total `X* = (A - 2bs)/b`, split equally
    set Xs : ℝ := ((a - c) - 2 * b * s) / b with hXs
    have hXs0 : 0 ≤ Xs / k := by
      apply div_nonneg _ (by linarith)
      rw [hXs]; apply div_nonneg _ hb.le
      nlinarith [mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 2 * b),
        mul_nonneg hb.le (mul_nonneg (by linarith : (0 : ℝ) ≤ k) hL)]
    set x : ℝ≥0 := ⟨Xs / k, hXs0⟩ with hx
    have hxv : (x : ℝ) = Xs / k := rfl
    refine cournot_not_dominated hb (r := fun _ => x) (fun j _ => ⟨?_, ?_⟩) ?_
    · show L ≤ (x : ℝ)
      rw [hxv, le_div_iff₀ (by linarith), hXs, le_div_iff₀ hb]
      nlinarith [mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 2 * b)]
    · show (x : ℝ) ≤ U
      rw [hxv, div_le_iff₀ (by linarith), hXs, div_le_iff₀ hb]
      nlinarith [mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ 2 * b)]
    · rw [rivalsTotal_const, ← hkdef, hxv, mul_div_cancel₀ _ (by linarith), hXs,
        mul_div_cancel₀ _ hb.ne']

/-- **Exercise 8.B.5**, the first round: from the full game, one round leaves `[0, A/(2b)]`
(quantities above the monopoly output are dominated by it). -/
theorem cournot_round_zero {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) (i : I)
    (hk : 1 ≤ Fintype.card I - 1) :
    sdRound (cournot I a b c) (fullSets _) i = qIval 0 ((a - c) / (2 * b)) := by
  set k : ℝ := ((Fintype.card I - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast hk
  set m := (a - c) / (2 * b) with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have h2m : m * (2 * b) = a - c := by rw [hm]; field_simp
  ext s
  constructor
  · rintro ⟨-, hnd⟩
    refine ⟨s.2, ?_⟩
    by_contra hlt
    push Not at hlt
    apply hnd
    set s' : ℝ≥0 := ⟨m, hm0⟩ with hs'
    have hs'v : (s' : ℝ) = m := rfl
    refine ⟨s', Set.mem_univ _, fun r _ => ?_⟩
    have hX : 0 ≤ rivalsTotal r i := Finset.sum_nonneg fun j _ => (r j).2
    rw [cournot_update a b c i r s, cournot_update a b c i r s', hs'v]
    have hgap := cournot_gap (a - c) b (rivalsTotal r i) s m
    have hneg : (m - s) * ((a - c) - b * rivalsTotal r i - b * (s + m)) > 0 := by
      apply mul_pos_of_neg_of_neg (by linarith)
      nlinarith
    linarith
  · rintro ⟨-, hhi⟩
    refine ⟨Set.mem_univ _, ?_⟩
    set Xs : ℝ := ((a - c) - 2 * b * s) / b with hXs
    have hXs0 : 0 ≤ Xs / k := by
      apply div_nonneg _ (by linarith)
      rw [hXs]; apply div_nonneg _ hb.le
      nlinarith [mul_le_mul_of_nonneg_left hhi (by linarith : (0 : ℝ) ≤ 2 * b)]
    set x : ℝ≥0 := ⟨Xs / k, hXs0⟩ with hx
    have hxv : (x : ℝ) = Xs / k := rfl
    refine cournot_not_dominated hb (r := fun _ => x) (fun j _ => Set.mem_univ _) ?_
    rw [rivalsTotal_const, ← hkdef, hxv, mul_div_cancel₀ _ (by linarith), hXs,
      mul_div_cancel₀ _ hb.ne']

/-! ### Exercise 8.B.5(a): two firms -/

/-- The bounds `(L_n, U_n)` of the quantities surviving `n + 1` rounds with two firms:
`(L_0, U_0) = (0, A/(2b))` and `(L_{n+1}, U_{n+1}) = (r(U_n), r(L_n))`. -/
noncomputable def cournotBounds (A b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, A / (2 * b))
  | n + 1 => (cbr A b (cournotBounds A b n).2, cbr A b (cournotBounds A b n).1)

/-- The invariant of the two-firm process, and the halving of the width. -/
theorem cournotBounds_inv {A b : ℝ} (hb : 0 < b) (hA : 0 < A) (n : ℕ) :
    0 ≤ (cournotBounds A b n).1 ∧ (cournotBounds A b n).1 ≤ (cournotBounds A b n).2 ∧
      (cournotBounds A b n).1 ≤ cbr A b (cournotBounds A b n).2 ∧
      cbr A b (cournotBounds A b n).1 ≤ (cournotBounds A b n).2 ∧
      b * (cournotBounds A b n).2 ≤ A ∧
      (cournotBounds A b n).1 ≤ A / (3 * b) ∧ A / (3 * b) ≤ (cournotBounds A b n).2 ∧
      (cournotBounds A b n).2 - (cournotBounds A b n).1 = A / (2 * b) / 2 ^ n := by
  induction n with
  | zero =>
    simp only [cournotBounds, cbr, pow_zero, div_one, sub_zero]
    refine ⟨le_rfl, by positivity, ?_, ?_, ?_, by positivity, ?_, trivial⟩
    · apply div_nonneg _ (by linarith)
      rw [mul_div_assoc', mul_comm b A, mul_div_mul_right _ _ hb.ne']
      linarith
    · simp
    · rw [mul_div_assoc', mul_comm b A, mul_div_mul_right _ _ hb.ne']
      linarith
    · gcongr; norm_num
  | succ n ih =>
    obtain ⟨hL, hLU, h1, h2, h3, hq1, hq2, hw⟩ := ih
    set L := (cournotBounds A b n).1
    set U := (cournotBounds A b n).2
    have e1 : (cournotBounds A b (n + 1)).1 = cbr A b U := rfl
    have e2 : (cournotBounds A b (n + 1)).2 = cbr A b L := rfl
    rw [e1, e2]
    have hcbr : ∀ x, cbr A b x * (2 * b) = A - b * x := fun x => by
      simp only [cbr]; field_simp
    have hmono : ∀ x y, x ≤ y → cbr A b y ≤ cbr A b x := fun x y hxy => by
      simp only [cbr]; gcongr
    have hq : cbr A b (A / (3 * b)) = A / (3 * b) := by
      simp only [cbr]; field_simp; ring
    refine ⟨?_, hmono _ _ hLU, hmono _ _ h2, hmono _ _ h1, ?_, ?_, ?_, ?_⟩
    · have := hcbr U
      nlinarith
    · have := hcbr L
      nlinarith
    · rw [← hq]; exact hmono _ _ hq2
    · rw [← hq]; exact hmono _ _ hq1
    · rw [pow_succ, show A / (2 * b) / (2 ^ n * 2) = (U - L) / 2 by rw [hw]; ring]
      simp only [cbr]
      field_simp
      ring

/-- With two firms, `n + 1` rounds leave `[L_n, U_n]` for each firm. -/
theorem cournot_two_sdIter {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) (n : ℕ) :
    sdIter (cournot (Fin 2) a b c) (n + 1) =
      fun _ => qIval (cournotBounds (a - c) b n).1 (cournotBounds (a - c) b n).2 := by
  have hk : 1 ≤ Fintype.card (Fin 2) - 1 := by simp
  have hk' : ((Fintype.card (Fin 2) - 1 : ℕ) : ℝ) = 1 := by simp
  induction n with
  | zero =>
    funext i
    exact cournot_round_zero hb hA i hk
  | succ n ih =>
    obtain ⟨hL, hLU, h1, h2, h3, -, -, -⟩ := cournotBounds_inv hb hA n
    funext i
    change sdRound _ (sdIter _ (n + 1)) i = _
    rw [ih]
    have := cournot_round (a := a) (c := c) hb i hk hL hLU (by rwa [hk', one_mul])
      (by rwa [hk', one_mul]) (by rwa [hk', one_mul])
    rw [this, hk', one_mul, one_mul]
    rfl

/-- The Cournot quantity `q* = (a - c)/(3b)`. -/
noncomputable def cournotStar (a b c : ℝ) (hb : 0 < b) (hA : 0 < a - c) : ℝ≥0 :=
  ⟨(a - c) / (3 * b), by positivity⟩

/-- **Exercise 8.B.5(a)** (MWG, p. 262). With two firms (`a > c`, `b > 0`), iterated deletion of
strictly dominated strategies yields a unique prediction, but only in the limit: every finite
round of the maximal process leaves at least two quantities for each firm, and the strategies
surviving all rounds are exactly `q* = (a - c)/(3b)`. -/
theorem exercise_8_B_5a {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ i, ⋂ n, sdIter (cournot (Fin 2) a b c) n i = {cournotStar a b c hb hA}) ∧
      ∀ n i, (sdIter (cournot (Fin 2) a b c) n i).Nontrivial := by
  have hw0 : 0 < (a - c) / (2 * b) := by positivity
  constructor
  · intro i
    ext s
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hs
      by_contra hne
      have hd : 0 < |(s : ℝ) - (a - c) / (3 * b)| := by
        rw [abs_pos, sub_ne_zero]
        intro h
        exact hne (NNReal.eq h)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hd hw0) (by norm_num : (1 / 2 : ℝ) < 1)
      have hsn := hs (n + 1)
      rw [cournot_two_sdIter hb hA] at hsn
      obtain ⟨-, -, -, -, -, hq1, hq2, hw⟩ := cournotBounds_inv hb hA n
      have hlt : (a - c) / (2 * b) / 2 ^ n < |(s : ℝ) - (a - c) / (3 * b)| := by
        have h := (lt_div_iff₀ hw0).1 hn
        rw [one_div_pow] at h
        calc (a - c) / (2 * b) / 2 ^ n = 1 / 2 ^ n * ((a - c) / (2 * b)) := by ring
          _ < _ := h
      rw [← hw] at hlt
      have := hsn.1
      have := hsn.2
      rcases lt_or_ge ((s : ℝ) - (a - c) / (3 * b)) 0 with hneg | hnn
      · rw [abs_of_neg hneg] at hlt; linarith
      · rw [abs_of_nonneg hnn] at hlt; linarith
    · rintro rfl n
      rcases n with _ | n
      · exact Set.mem_univ _
      · rw [cournot_two_sdIter hb hA]
        obtain ⟨-, -, -, -, -, hq1, hq2, -⟩ := cournotBounds_inv hb hA n
        exact ⟨hq1, hq2⟩
  · intro n i
    rcases n with _ | n
    · exact ⟨0, Set.mem_univ _, 1, Set.mem_univ _, zero_ne_one⟩
    · rw [cournot_two_sdIter hb hA]
      obtain ⟨hL, hLU, -, -, -, -, -, hw⟩ := cournotBounds_inv hb hA n
      have hpos : 0 < (cournotBounds (a - c) b n).2 - (cournotBounds (a - c) b n).1 := by
        rw [hw]; positivity
      refine ⟨⟨_, hL⟩, ⟨le_rfl, hLU⟩, ⟨_, hL.trans hLU⟩, ⟨hLU, le_rfl⟩, fun h => ?_⟩
      have := congrArg NNReal.toReal h
      change (cournotBounds (a - c) b n).1 = (cournotBounds (a - c) b n).2 at this
      linarith

/-! ### Exercise 8.B.5(b): three firms -/

/-- **Exercise 8.B.5(b)** (MWG, p. 262). With three firms the answer is no: after the first round
every firm keeps `[0, (a - c)/(2b)]`, nothing there is strictly dominated (two rivals can total
any amount in `[0, (a - c)/b]`), so the process stops at a continuum of quantities. -/
theorem exercise_8_B_5b {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ n i, sdIter (cournot (Fin 3) a b c) (n + 1) i = qIval 0 ((a - c) / (2 * b))) ∧
      SDTerminal (cournot (Fin 3) a b c) (fun _ => qIval 0 ((a - c) / (2 * b))) ∧
      ∀ i, (⋂ n, sdIter (cournot (Fin 3) a b c) n i).Nontrivial := by
  have hk : 1 ≤ Fintype.card (Fin 3) - 1 := by simp
  have hk' : ((Fintype.card (Fin 3) - 1 : ℕ) : ℝ) = 2 := by norm_num [Fintype.card_fin]
  set m := (a - c) / (2 * b) with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hcbr0 : cbr (a - c) b (2 * m) = 0 := by
    simp only [cbr, hm]; field_simp; ring
  have hcbrm : cbr (a - c) b (2 * 0) = m := by simp [cbr, hm]
  have hround : ∀ i, sdRound (cournot (Fin 3) a b c) (fun _ => qIval 0 m) i = qIval 0 m := by
    intro i
    have := cournot_round (a := a) (c := c) hb i hk le_rfl hm0
      (by rw [hk', hcbr0]) (by rw [hk', hcbrm]) (by rw [hk', hm]; field_simp; linarith)
    rw [this, hk', hcbr0, hcbrm]
  have hiter : ∀ n i, sdIter (cournot (Fin 3) a b c) (n + 1) i = qIval 0 m := by
    intro n
    induction n with
    | zero => exact fun i => cournot_round_zero hb hA i hk
    | succ n ih =>
      intro i
      change sdRound _ (sdIter _ (n + 1)) i = _
      have : sdIter (cournot (Fin 3) a b c) (n + 1) = fun _ => qIval 0 m := funext ih
      rw [this, hround]
  refine ⟨hiter, fun i s hs => ?_, fun i => ?_⟩
  · have : s ∈ sdRound (cournot (Fin 3) a b c) (fun _ => qIval 0 m) i := by rw [hround]; exact hs
    exact this.2
  · have hm0' : 0 < m := by rw [hm]; positivity
    refine ⟨0, ?_, ⟨m, hm0⟩, ?_, fun h => ?_⟩
    · refine Set.mem_iInter.2 fun n => ?_
      rcases n with _ | n
      · exact Set.mem_univ _
      · rw [hiter]; exact ⟨le_rfl, hm0⟩
    · refine Set.mem_iInter.2 fun n => ?_
      rcases n with _ | n
      · exact Set.mem_univ _
      · rw [hiter]; exact ⟨hm0, le_rfl⟩
    · have := congrArg NNReal.toReal h
      change (0 : ℝ) = m at this
      linarith

/-! ### Exercise 8.E.3: Cournot with privately known costs -/

/-- The probability of a firm's cost type: type `0` (cost `c_L`) has probability `μ`, type `1`
(cost `c_H`) probability `1 - μ`. -/
def typeP (μ : ℝ) (t : Fin 2) : ℝ := if t = 0 then μ else 1 - μ

/-- The unit cost of type `t`. -/
def tcost (cL cH : ℝ) (t : Fin 2) : ℝ := if t = 0 then cL else cH

/-- **Exercise 8.E.3** (MWG, p. 265). The linear Cournot duopoly of Exercise 8.B.5 in which each
firm's unit cost is `c_L` with probability `μ` and `c_H` with probability `1 - μ`, independently
across firms, and known only to the firm. -/
noncomputable def bayesCournot (a b μ cL cH : ℝ) :
    BayesianGame (Fin 2) (fun _ => ℝ≥0) (fun _ => Fin 2) where
  prior θ := typeP μ (θ 0) * typeP μ (θ 1)
  payoff i q θ := (a - b * ((q 0 : ℝ) + q 1) - tcost cL cH (θ i)) * q i

/-- The rival's expected output `μ s_j(c_L) + (1 - μ) s_j(c_H)`. -/
def expQ (μ : ℝ) (sj : Fin 2 → ℝ≥0) : ℝ := μ * sj 0 + (1 - μ) * sj 1

/-- A sum over the four type profiles. -/
theorem sum_fin2_fin2 (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ θ, f θ = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  have e : ∀ p q : Fin 2, (piFinTwoEquiv fun _ => Fin 2).symm (p, q) = ![p, q] := by
    intro p q
    funext k
    fin_cases k <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, e]
  ring

theorem bayesCournot_isPrior {a b μ cL cH : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (bayesCournot a b μ cL cH).IsPrior := by
  have hp : ∀ t, 0 ≤ typeP μ t := fun t => by
    unfold typeP; split_ifs <;> linarith
  refine ⟨fun θ => mul_nonneg (hp _) (hp _), ?_⟩
  simp only [bayesCournot]
  rw [sum_fin2_fin2]
  simp [typeP]
  ring

/-- The probability of each type. -/
theorem bayesCournot_typeProb (a b μ cL cH : ℝ) (i t : Fin 2) :
    (bayesCournot a b μ cL cH).typeProb i t = typeP μ t := by
  unfold BayesianGame.typeProb
  rw [Finset.sum_filter, sum_fin2_fin2]
  fin_cases i <;> fin_cases t <;> simp [bayesCournot, typeP] <;> ring

/-- The gain of type `t` of firm `i` from the output `x`: `Prob(t) x (a - c_t - bx - b E[q_j])`. -/
theorem bayesCournot_typeGain (a b μ cL cH : ℝ) (s : (i : Fin 2) → Fin 2 → ℝ≥0) (i t : Fin 2)
    (x : ℝ≥0) :
    (bayesCournot a b μ cL cH).typeGain s i t x =
      typeP μ t * ((x : ℝ) * (a - tcost cL cH t - b * x - b * expQ μ (s (1 - i)))) := by
  unfold BayesianGame.typeGain
  rw [Finset.sum_filter, sum_fin2_fin2]
  fin_cases i <;> fin_cases t <;>
    simp [bayesCournot, typeP, tcost, expQ, BayesianGame.play, Function.update] <;> ring

/-- Maximizing `x (K - bx)` over `x ≥ 0`: the maximizer is `max(K/(2b), 0)`. -/
theorem quad_argmax {b : ℝ} (hb : 0 < b) (K : ℝ) (y : ℝ≥0) :
    (∀ x : ℝ≥0, (x : ℝ) * (K - b * x) ≤ y * (K - b * y)) ↔ (y : ℝ) = max (K / (2 * b)) 0 := by
  have hy0 := NNReal.coe_nonneg y
  constructor
  · intro h
    rcases le_or_gt 0 K with hK | hK
    · have hK' : 0 ≤ K / (2 * b) := by positivity
      rw [max_eq_left hK']
      have := h ⟨K / (2 * b), hK'⟩
      change K / (2 * b) * (K - b * (K / (2 * b))) ≤ (y : ℝ) * (K - b * y) at this
      have h2 : (y - K / (2 * b)) ^ 2 * b ≤ 0 := by
        have e : (y - K / (2 * b)) ^ 2 * b =
            K / (2 * b) * (K - b * (K / (2 * b))) - y * (K - b * y) := by
          field_simp; ring
        linarith
      have h3 : (y - K / (2 * b)) ^ 2 = 0 := by
        have := mul_nonpos_iff.1 h2
        rcases this with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · exact le_antisymm h (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
      linarith
    · have hK' : K / (2 * b) < 0 := div_neg_of_neg_of_pos hK (by linarith)
      rw [max_eq_right hK'.le]
      have h0 := h 0
      simp only [NNReal.coe_zero, zero_mul] at h0
      by_contra hne
      have hy' : 0 < (y : ℝ) := lt_of_le_of_ne hy0 (fun h' => hne (by rw [← h']))
      have : (y : ℝ) * (K - b * y) < 0 := mul_neg_of_pos_of_neg hy' (by nlinarith)
      linarith
  · intro hy x
    have hx0 := NNReal.coe_nonneg x
    rcases le_or_gt 0 K with hK | hK
    · rw [max_eq_left (by positivity)] at hy
      rw [hy]
      have e : K / (2 * b) * (K - b * (K / (2 * b))) - x * (K - b * x) =
          ((x : ℝ) - K / (2 * b)) ^ 2 * b := by
        field_simp; ring
      nlinarith [sq_nonneg ((x : ℝ) - K / (2 * b))]
    · rw [max_eq_right (div_neg_of_neg_of_pos hK (by linarith)).le] at hy
      rw [hy]
      have e : (x : ℝ) * (K - b * x) = x * K - b * (x * x) := by ring
      have := mul_nonpos_of_nonneg_of_nonpos hx0 hK.le
      have := mul_nonneg hb.le (mul_nonneg hx0 hx0)
      rw [e]
      linarith

/-- Proposition 8.E.1 for the Bayesian Cournot game: a profile is a Bayesian Nash equilibrium iff
each type of each firm produces `max((a - c_t - b E[q_j])/(2b), 0)`. -/
theorem bayesCournot_isBNE_iff {a b μ cL cH : ℝ} (hb : 0 < b) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (s : (i : Fin 2) → Fin 2 → ℝ≥0) :
    (bayesCournot a b μ cL cH).IsBNE s ↔ ∀ i t,
      (s i t : ℝ) = max ((a - tcost cL cH t - b * expQ μ (s (1 - i))) / (2 * b)) 0 := by
  rw [BayesianGame.proposition_8_E_1 _ (bayesCournot_isPrior hμ0.le hμ1.le)]
  have hpos : ∀ t, 0 < typeP μ t := fun t => by
    unfold typeP; split_ifs <;> linarith
  refine forall_congr' fun i => forall_congr' fun t => ?_
  rw [bayesCournot_typeProb]
  simp only [hpos t, true_implies, BayesianGame.condPayoff, bayesCournot_typeProb,
    bayesCournot_typeGain, mul_div_cancel_left₀ _ (hpos t).ne']
  rw [← quad_argmax hb]
  refine forall_congr' fun x => ?_
  constructor <;> intro h <;> linarith

/-- The Bayesian Nash equilibrium outputs `q_t = (2a - 3c_t + c̄)/(6b)`, `c̄ = μ c_L + (1 - μ) c_H`.
-/
noncomputable def bcq (a b μ cL cH : ℝ) (t : Fin 2) : ℝ :=
  (2 * a - 3 * tcost cL cH t + (μ * cL + (1 - μ) * cH)) / (6 * b)

/-- **Exercise 8.E.3** (MWG, p. 265). In the Bayesian Cournot duopoly (`b > 0`, `0 < μ < 1`,
`c_L < c_H`, and `3c_H ≤ 2a + c̄` so that the high-cost output is nonnegative), the unique Bayesian
Nash equilibrium has each firm produce `q_L = (2a - 3c_L + c̄)/(6b)` when its cost is `c_L` and
`q_H = (2a - 3c_H + c̄)/(6b)` when its cost is `c_H`, where `c̄ = μ c_L + (1 - μ) c_H`. -/
theorem exercise_8_E_3 {a b μ cL cH : ℝ} (hb : 0 < b) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : cL < cH) (hint : 3 * cH ≤ 2 * a + (μ * cL + (1 - μ) * cH))
    (s : (i : Fin 2) → Fin 2 → ℝ≥0) :
    (bayesCournot a b μ cL cH).IsBNE s ↔ ∀ i t, (s i t : ℝ) = bcq a b μ cL cH t := by
  rw [bayesCournot_isBNE_iff hb hμ0 hμ1]
  set cbar := μ * cL + (1 - μ) * cH with hcbar
  set Qb := (a - cbar) / (3 * b) with hQb
  have hq0 : ∀ t, 0 ≤ bcq a b μ cL cH t := by
    intro t
    unfold bcq tcost
    split_ifs
    · apply div_nonneg _ (by linarith)
      nlinarith
    · exact div_nonneg (by linarith) (by linarith)
  -- `g(Q, t)`, the best reply of type `t` to the rival's expected output `Q`
  set g : ℝ → Fin 2 → ℝ := fun Q t => max ((a - tcost cL cH t - b * Q) / (2 * b)) 0 with hg
  have hgQb : ∀ t, g Qb t = bcq a b μ cL cH t := by
    intro t
    simp only [hg]
    have : (a - tcost cL cH t - b * Qb) / (2 * b) = bcq a b μ cL cH t := by
      simp only [hQb, bcq, hcbar]; field_simp; ring
    rw [this, max_eq_left (hq0 t)]
  have hexpQb : ∀ q : Fin 2 → ℝ≥0, (∀ t, (q t : ℝ) = bcq a b μ cL cH t) → expQ μ q = Qb := by
    intro q hq
    simp only [expQ, hq, bcq, tcost, hQb, hcbar]
    simp
    field_simp
    ring
  have hlip : ∀ Q Q' t, |g Q t - g Q' t| ≤ |Q - Q'| / 2 := by
    intro Q Q' t
    refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
    rw [show (a - tcost cL cH t - b * Q) / (2 * b) - (a - tcost cL cH t - b * Q') / (2 * b) =
      -(Q - Q') / 2 by field_simp; ring, abs_div, abs_neg]
    norm_num
  constructor
  · intro h
    -- the expected outputs are a fixed point of a contraction
    have hE : ∀ i, expQ μ (s i) = μ * g (expQ μ (s (1 - i))) 0 +
        (1 - μ) * g (expQ μ (s (1 - i))) 1 := by
      intro i
      simp only [expQ, h i 0, h i 1, hg]
    have hF : ∀ Q, |μ * g Q 0 + (1 - μ) * g Q 1 - Qb| ≤ |Q - Qb| / 2 := by
      intro Q
      have hQb' : Qb = μ * g Qb 0 + (1 - μ) * g Qb 1 := by
        rw [hgQb, hgQb]
        have := hexpQb (fun t => ⟨bcq a b μ cL cH t, hq0 t⟩) (fun t => rfl)
        rw [← this]
        rfl
      conv_lhs => rw [hQb']
      have e : μ * g Q 0 + (1 - μ) * g Q 1 - (μ * g Qb 0 + (1 - μ) * g Qb 1) =
          μ * (g Q 0 - g Qb 0) + (1 - μ) * (g Q 1 - g Qb 1) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hμ0, abs_of_pos (by linarith : 0 < 1 - μ)]
      have h0 := hlip Q Qb 0
      have h1 := hlip Q Qb 1
      nlinarith
    have h10 : (1 : Fin 2) - 1 = 0 := by decide
    have h01 : (1 : Fin 2) - 0 = 1 := by decide
    have e0 := hE 0
    have e1 := hE 1
    rw [h01] at e0
    rw [h10] at e1
    have a0 : |expQ μ (s 0) - Qb| ≤ |expQ μ (s 1) - Qb| / 2 := by rw [e0]; exact hF _
    have a1 : |expQ μ (s 1) - Qb| ≤ |expQ μ (s 0) - Qb| / 2 := by rw [e1]; exact hF _
    have z0 : expQ μ (s 0) = Qb := by
      have := abs_nonneg (expQ μ (s 0) - Qb)
      have := abs_nonneg (expQ μ (s 1) - Qb)
      have : |expQ μ (s 0) - Qb| = 0 := by linarith
      exact sub_eq_zero.1 (abs_eq_zero.1 this)
    have z1 : expQ μ (s 1) = Qb := by
      have := abs_nonneg (expQ μ (s 1) - Qb)
      have : |expQ μ (s 1) - Qb| = 0 := by rw [z0, sub_self, abs_zero] at a1; linarith
      exact sub_eq_zero.1 (abs_eq_zero.1 this)
    intro i t
    rw [h i t, ← hgQb]
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · simp only [hg, h01, z1]
    · simp only [hg, h10, z0]
  · intro h i t
    rw [h i t, hexpQb _ (h (1 - i)), ← hgQb]

/-- A concrete instance of Exercise 8.E.3 (`a = 10`, `b = 1`, `μ = 1/2`, `c_L = 1`, `c_H = 2`):
the profile `q_L = 37/12`, `q_H = 31/12` for both firms is a Bayesian Nash equilibrium. -/
theorem exercise_8_E_3_instance :
    (bayesCournot 10 1 (1 / 2) 1 2).IsBNE
      (fun _ t => if t = 0 then ⟨37 / 12, by norm_num⟩ else ⟨31 / 12, by norm_num⟩) := by
  refine (exercise_8_E_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _).2 fun i t => ?_
  fin_cases t <;> simp [bcq, tcost] <;> norm_num <;> rfl

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 8.D.5: ice-cream vendors on a boardwalk

MWG, Exercise 8.D.5, pp. 263-264.

Consumers are uniform on the boardwalk `[0, 1]` and buy from the nearest vendor; vendors at the
same location split their customers evenly. A vendor at `x` serves the points closer to `x`
than to any other occupied location: from the midpoint with the nearest occupied location to
its left (or `0`) to the midpoint with the nearest one to its right (or `1`), divided by the
number of vendors at `x`. With one rival at `y` this is `icShare2 x y`; with two rivals at `y`
and `z` it is `icShare3 x y z`. Locations are points of `unitInterval = [0, 1]`.

* **Exercise 8.D.5(a)** (`exercise_8_D_5a`): with two vendors the unique pure strategy Nash
  equilibrium is both vendors at the midpoint `½`.
* **Exercise 8.D.5(b)** (`exercise_8_D_5b`): with three vendors there is no pure strategy Nash
  equilibrium: a vendor who is alone at the far left (right) gains by moving towards his
  neighbour, and if all three share a location, one of them gains by moving away.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function unitInterval

/-- The market share of a vendor at `x` with one rival at `y`. -/
noncomputable def icShare2 (x y : ℝ) : ℝ :=
  ((if x < y then (x + y) / 2 else 1) - (if y < x then (x + y) / 2 else 0)) /
    (1 + if y = x then 1 else 0)

/-- The market share of a vendor at `x` with rivals at `y` and `z`. -/
noncomputable def icShare3 (x y z : ℝ) : ℝ :=
  (min (if x < y then (x + y) / 2 else 1) (if x < z then (x + z) / 2 else 1) -
      max (if y < x then (x + y) / 2 else 0) (if z < x then (x + z) / 2 else 0)) /
    (1 + (if y = x then 1 else 0) + (if z = x then 1 else 0))

/-- **Exercise 8.D.5(a)** (MWG, p. 264). Two ice-cream vendors choose locations in `[0, 1]`. -/
noncomputable def iceCream2 : NormalForm (Fin 2) (fun _ => unitInterval) where
  payoff i r := icShare2 (r i) (r (i + 1))

/-- **Exercise 8.D.5(b)** (MWG, p. 264). Three ice-cream vendors choose locations in `[0, 1]`. -/
noncomputable def iceCream3 : NormalForm (Fin 3) (fun _ => unitInterval) where
  payoff i r := icShare3 (r i) (r (i + 1)) (r (i + 2))

/-- The midpoint of two points of `[0, 1]`. -/
noncomputable def uiMid (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    unitInterval :=
  ⟨(x + y) / 2, ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩⟩

/-! ### Two vendors -/

theorem icShare2_lt {x y : ℝ} (h : x < y) : icShare2 x y = (x + y) / 2 := by
  simp [icShare2, h, not_lt.2 h.le, h.ne']

theorem icShare2_self (x : ℝ) : icShare2 x x = 1 / 2 := by
  simp [icShare2]; norm_num

theorem icShare2_gt {x y : ℝ} (h : y < x) : icShare2 x y = 1 - (x + y) / 2 := by
  simp [icShare2, h, not_lt.2 h.le, h.ne]

theorem iceCream2_update (i : Fin 2) (r : Fin 2 → unitInterval) (x : unitInterval) :
    iceCream2.payoff i (update r i x) = icShare2 x (r (i + 1)) := by
  have hne : i + 1 ≠ i := by fin_cases i <;> decide
  simp only [iceCream2, update_self, update_of_ne hne]

/-- With the rival at `½`, no location does better than `½`. -/
theorem icShare2_le_half (x : ℝ) : icShare2 x (1 / 2) ≤ 1 / 2 := by
  rcases lt_trichotomy x (1 / 2) with h | rfl | h
  · rw [icShare2_lt h]; linarith
  · rw [icShare2_self]
  · rw [icShare2_gt h]; linarith

/-- **Exercise 8.D.5(a)** (MWG, p. 264). With two vendors there is a unique pure strategy Nash
equilibrium, and both vendors locate at the midpoint of the boardwalk. -/
theorem exercise_8_D_5a (r : Fin 2 → unitInterval) :
    IsNashEquilibrium iceCream2 r ↔ (r 0 : ℝ) = 1 / 2 ∧ (r 1 : ℝ) = 1 / 2 := by
  have e0 : ∀ x, iceCream2.payoff 0 (update r 0 x) = icShare2 x (r 1) :=
    fun x => iceCream2_update 0 r x
  have e1 : ∀ x, iceCream2.payoff 1 (update r 1 x) = icShare2 x (r 0) :=
    fun x => iceCream2_update 1 r x
  have p0 : iceCream2.payoff 0 r = icShare2 (r 0) (r 1) := by rw [← e0, update_eq_self]
  have p1 : iceCream2.payoff 1 r = icShare2 (r 1) (r 0) := by rw [← e1, update_eq_self]
  have hu := (r 0).2
  have hw := (r 1).2
  constructor
  · intro h
    have d0 : ∀ x : unitInterval, icShare2 x (r 1) ≤ icShare2 (r 0) (r 1) := fun x => by
      have := h 0 x; rwa [e0, p0] at this
    have d1 : ∀ x : unitInterval, icShare2 x (r 0) ≤ icShare2 (r 1) (r 0) := fun x => by
      have := h 1 x; rwa [e1, p1] at this
    rcases lt_trichotomy (r 0 : ℝ) (r 1) with huw | huw | huw
    · exfalso
      have := d0 (uiMid _ _ hu hw)
      simp only [uiMid] at this
      rw [icShare2_lt huw, icShare2_lt (by linarith)] at this
      linarith
    · have hd := d0 ⟨1 / 2, by norm_num, by norm_num⟩
      simp only at hd
      rw [← huw, icShare2_self] at hd
      by_contra hne
      have hne' : (r 0 : ℝ) ≠ 1 / 2 := fun h' => hne ⟨h', huw ▸ h'⟩
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · rw [icShare2_gt hlt] at hd; linarith
      · rw [icShare2_lt hgt] at hd; linarith
    · exfalso
      have := d1 (uiMid _ _ hw hu)
      simp only [uiMid] at this
      rw [icShare2_lt huw, icShare2_lt (by linarith)] at this
      linarith
  · rintro ⟨h0, h1⟩ i x
    fin_cases i
    · change iceCream2.payoff 0 (update r 0 x) ≤ iceCream2.payoff 0 r
      rw [e0, p0, h0, h1, icShare2_self]
      exact icShare2_le_half _
    · change iceCream2.payoff 1 (update r 1 x) ≤ iceCream2.payoff 1 r
      rw [e1, p1, h0, h1, icShare2_self]
      exact icShare2_le_half _

/-! ### Three vendors -/

theorem icShare3_left {x y z : ℝ} (hxy : x < y) (hxz : x < z) :
    icShare3 x y z = (x + min y z) / 2 := by
  simp only [icShare3, hxy, hxz, not_lt.2 hxy.le, not_lt.2 hxz.le, hxy.ne', hxz.ne',
    ↓reduceIte, max_self, sub_zero, add_zero, div_one]
  rcases le_total y z with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]

theorem icShare3_right {x y z : ℝ} (hyx : y < x) (hzx : z < x) :
    icShare3 x y z = 1 - (x + max y z) / 2 := by
  simp only [icShare3, hyx, hzx, not_lt.2 hyx.le, not_lt.2 hzx.le, hyx.ne, hzx.ne,
    ↓reduceIte, min_self, add_zero, div_one]
  rcases le_total y z with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

theorem icShare3_self (a : ℝ) : icShare3 a a a = 1 / 3 := by
  simp only [icShare3, lt_irrefl, ↓reduceIte, min_self, max_self]
  norm_num

/-- A vendor alone at the far left gains by moving halfway towards the nearest rival. -/
theorem icShare3_leftmost {x y z : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hxy : x < y) (hxz : x < z)
    (h : ∀ x' : unitInterval, icShare3 x' y z ≤ icShare3 x y z) : False := by
  have hm : min y z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_min hy.1 hz.1, (min_le_left _ _).trans hy.2⟩
  have hxm : x < min y z := lt_min hxy hxz
  have := h (uiMid x (min y z) hx hm)
  simp only [uiMid] at this
  rw [icShare3_left hxy hxz, icShare3_left (by linarith [min_le_left y z])
    (by linarith [min_le_right y z])] at this
  linarith

/-- A vendor alone at the far right gains by moving halfway towards the nearest rival. -/
theorem icShare3_rightmost {x y z : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hyx : y < x) (hzx : z < x)
    (h : ∀ x' : unitInterval, icShare3 x' y z ≤ icShare3 x y z) : False := by
  have hm : max y z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hy.1.trans (le_max_left _ _), max_le hy.2 hz.2⟩
  have hxm : max y z < x := max_lt hyx hzx
  have := h (uiMid x (max y z) hx hm)
  simp only [uiMid] at this
  rw [icShare3_right hyx hzx, icShare3_right (by linarith [le_max_left y z])
    (by linarith [le_max_right y z])] at this
  linarith

/-- If all three vendors share a location, one of them gains by moving away. -/
theorem icShare3_together {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ x' : unitInterval, icShare3 x' a a ≤ icShare3 a a a) : False := by
  rw [icShare3_self] at h
  rcases lt_or_ge a (5 / 9) with hlt | hge
  · have := h (uiMid a 1 ha ⟨by norm_num, le_rfl⟩)
    simp only [uiMid] at this
    rw [icShare3_right (by linarith) (by linarith), max_self] at this
    linarith
  · have := h (uiMid a 0 ha ⟨le_rfl, by norm_num⟩)
    simp only [uiMid] at this
    rw [icShare3_left (by linarith) (by linarith), min_self] at this
    linarith

theorem iceCream3_update (i : Fin 3) (r : Fin 3 → unitInterval) (x : unitInterval) :
    iceCream3.payoff i (update r i x) = icShare3 x (r (i + 1)) (r (i + 2)) := by
  have h1 : i + 1 ≠ i := by fin_cases i <;> decide
  have h2 : i + 2 ≠ i := by fin_cases i <;> decide
  simp only [iceCream3, update_self, update_of_ne h1, update_of_ne h2]

/-- **Exercise 8.D.5(b)** (MWG, p. 264). With three vendors no pure strategy Nash equilibrium
exists. -/
theorem exercise_8_D_5b (r : Fin 3 → unitInterval) : ¬ IsNashEquilibrium iceCream3 r := by
  intro h
  have dev : ∀ i : Fin 3, ∀ x : unitInterval,
      icShare3 x (r (i + 1)) (r (i + 2)) ≤ icShare3 (r i) (r (i + 1)) (r (i + 2)) := by
    intro i x
    have := h i x
    rw [iceCream3_update] at this
    exact this
  have d0 := dev 0
  have d1 := dev 1
  have d2 := dev 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at d0 d1 d2
  have m0 := (r 0).2
  have m1 := (r 1).2
  have m2 := (r 2).2
  set x0 : ℝ := (r 0 : ℝ)
  set x1 : ℝ := (r 1 : ℝ)
  set x2 : ℝ := (r 2 : ℝ)
  rcases lt_trichotomy x0 x1 with h01 | h01 | h01 <;>
    rcases lt_trichotomy x0 x2 with h02 | h02 | h02 <;>
    rcases lt_trichotomy x1 x2 with h12 | h12 | h12 <;>
    first
    | exact icShare3_leftmost m0 m1 m2 (by linarith) (by linarith) d0
    | exact icShare3_leftmost m1 m2 m0 (by linarith) (by linarith) d1
    | exact icShare3_leftmost m2 m0 m1 (by linarith) (by linarith) d2
    | exact icShare3_rightmost m0 m1 m2 (by linarith) (by linarith) d0
    | exact icShare3_rightmost m1 m2 m0 (by linarith) (by linarith) d1
    | exact icShare3_rightmost m2 m0 m1 (by linarith) (by linarith) d2
    | (rw [← h01, ← h02] at d0; exact icShare3_together m0 d0)

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 8.D.9: Kreps's game

MWG, Exercise 8.D.9, pp. 264-265 (after Kreps 1990). Player 1 chooses `U` or `D`, player 2
chooses `LL`, `L`, `M` or `R` (rows and columns numbered from `0` in this order):

|     | `LL`      | `L`       | `M`  | `R`        |
|-----|-----------|-----------|------|------------|
| `U` | 100, 2    | -100, 1   | 0, 0 | -100, -100 |
| `D` | -100, -100| 100, -49  | 1, 0 | 100, 2     |

* (a) is a question about intuition. Its mathematical content: `M` is player 2's safe strategy.
  It guarantees `0`; every other pure strategy risks `-49` or worse; and `M` is the only mixed
  strategy that guarantees `0` (`exercise_8_D_9a`).
* (b) The Nash equilibria are `(U, LL)`, `(D, R)` and the mixed equilibrium in which player 1
  plays `U` with probability `51/52` and player 2 mixes `LL` and `L` equally
  (`exercise_8_D_9b`).
* (c) `M` is played in no Nash equilibrium (`exercise_8_D_9c_not_nash`). It is rationalizable
  (`exercise_8_D_9c_rationalizable`): it is a best response to `½U + ½D`, which is a best
  response to `½LL + ½L`, which is a best response to `(51/52)U + (1/52)D`, which is a best
  response to `½LL + ½L`.
* (d) is a question about preplay communication. Its mathematical content: in both pure
  equilibria the payoffs are `(100, 2)`, so both players strictly prefer either of them to any
  outcome in which player 2 plays `M` (player 2 gets `0` there) (`exercise_8_D_9d`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- Player 1's payoffs in Kreps's game. -/
def krepsU₁ : Fin 2 → Fin 4 → ℝ := ![![100, -100, 0, -100], ![-100, 100, 1, 100]]

/-- Player 2's payoffs in Kreps's game. -/
def krepsU₂ : Fin 2 → Fin 4 → ℝ := ![![2, 1, 0, -100], ![-100, -49, 0, 2]]

/-- **Exercise 8.D.9** (MWG, p. 264). Kreps's game. -/
def kreps : NormalForm (Fin 2) (S2 2 4) := bimatrix krepsU₁ krepsU₂

/-- Player 1's payoffs against player 2's mixed strategy `y`. -/
theorem kreps_rows (y : Fin 4 → ℝ) (a : Fin 2) :
    ∑ b, y b * krepsU₁ a b =
      ![100 * y 0 - 100 * y 1 - 100 * y 3, -100 * y 0 + 100 * y 1 + y 2 + 100 * y 3] a := by
  fin_cases a <;> simp [Fin.sum_univ_four, krepsU₁] <;> ring

/-- Player 2's payoffs against player 1's mixed strategy `x`. -/
theorem kreps_cols (x : Fin 2 → ℝ) (b : Fin 4) :
    ∑ a, x a * krepsU₂ a b =
      ![2 * x 0 - 100 * x 1, x 0 - 49 * x 1, 0, -100 * x 0 + 2 * x 1] b := by
  fin_cases b <;> simp [Fin.sum_univ_two, krepsU₂] <;> ring

/-- **Exercise 8.D.9(a)** (MWG, p. 265), its mathematical content. `M` guarantees player 2 the
payoff `0`, each other pure strategy risks at most `-49`, and `M` is the only mixed strategy of
player 2 that guarantees `0` against both of player 1's strategies. -/
theorem exercise_8_D_9a :
    (∀ a, krepsU₂ a 2 = 0) ∧ (∀ b, b ≠ 2 → ∃ a, krepsU₂ a b ≤ -49) ∧
      ∀ y : Fin 4 → ℝ, IsMixedStrategy y →
        ((∀ a, 0 ≤ ∑ b, y b * krepsU₂ a b) ↔ y = pureMixed 2) := by
  refine ⟨fun a => by fin_cases a <;> rfl, fun b hb => ?_, fun y hy => ?_⟩
  · fin_cases b
    · exact ⟨1, by norm_num [krepsU₂]⟩
    · exact ⟨1, by norm_num [krepsU₂]⟩
    · exact absurd rfl hb
    · exact ⟨0, by norm_num [krepsU₂]⟩
  · have h0 := hy.1
    have hs : y 0 + y 1 + y 2 + y 3 = 1 := by simpa [Fin.sum_univ_four] using hy.2
    constructor
    · intro h
      have hU := h 0
      have hD := h 1
      simp [Fin.sum_univ_four, krepsU₂] at hU hD
      have y0 : y 0 = 0 := by linarith [h0 0, h0 1, h0 3]
      have y1 : y 1 = 0 := by linarith [h0 0, h0 1, h0 3]
      have y3 : y 3 = 0 := by linarith [h0 0, h0 1, h0 3]
      have y2 : y 2 = 1 := by linarith
      funext b
      fin_cases b
      · simp [pureMixed, y0]
      · simp [pureMixed, y1]
      · simp [pureMixed, y2]
      · simp [pureMixed, y3]
    · rintro rfl a
      fin_cases a <;> simp [krepsU₂, pureMixed]

/-- The mixed equilibrium strategy of player 1. -/
noncomputable def krepsX : Fin 2 → ℝ := ![51 / 52, 1 / 52]

/-- The mixed equilibrium strategy of player 2: `½LL + ½L`. -/
noncomputable def krepsY : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

/-- **Exercise 8.D.9(b)** (MWG, p. 265). The Nash equilibria (pure and mixed) of Kreps's game are
`(U, LL)`, `(D, R)` and `((51/52) U + (1/52) D, ½ LL + ½ L)`. -/
theorem exercise_8_D_9b {x : Fin 2 → ℝ} {y : Fin 4 → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    IsMixedNash kreps (mp x y) ↔ (x = pureMixed 0 ∧ y = pureMixed 0) ∨
      (x = pureMixed 1 ∧ y = pureMixed 3) ∨ (x = krepsX ∧ y = krepsY) := by
  rw [kreps, bimatrix_isMixedNash_support _ _ hx hy]
  simp only [kreps_rows, kreps_cols]
  have hx0 := hx.1
  have hy0 := hy.1
  have hxs : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
  have hys : y 0 + y 1 + y 2 + y 3 = 1 := by simpa [Fin.sum_univ_four] using hy.2
  constructor
  · rintro ⟨hr, hc⟩
    -- the column conditions, one by one
    have c : ∀ b, 0 < y b → ∀ b', ![2 * x 0 - 100 * x 1, x 0 - 49 * x 1, 0,
        -100 * x 0 + 2 * x 1] b' ≤ ![2 * x 0 - 100 * x 1, x 0 - 49 * x 1, 0,
        -100 * x 0 + 2 * x 1] b := hc
    rcases (hx0 0).eq_or_lt with hx0z | hx0p
    · -- `x = D`: only `R` is a best reply
      have hx1 : x 1 = 1 := by linarith
      have hyz : ∀ b, b ≠ 3 → y b = 0 := by
        intro b hb
        rcases (hy0 b).eq_or_lt with h | h
        · exact h.symm
        · have := c b h 3
          fin_cases b <;> simp at this hb <;> linarith
      right; left
      refine ⟨?_, ?_⟩
      · funext a; fin_cases a <;> simp [pureMixed] <;> linarith
      · have y3 : y 3 = 1 := by linarith [hyz 0 (by decide), hyz 1 (by decide), hyz 2 (by decide)]
        funext b
        by_cases hb : b = 3
        · subst hb; simp [pureMixed, y3]
        · rw [hyz b hb]; simp [pureMixed, hb]
    rcases (hx0 1).eq_or_lt with hx1z | hx1p
    · -- `x = U`: only `LL` is a best reply
      have hx0' : x 0 = 1 := by linarith
      have hyz : ∀ b, b ≠ 0 → y b = 0 := by
        intro b hb
        rcases (hy0 b).eq_or_lt with h | h
        · exact h.symm
        · have := c b h 0
          fin_cases b <;> simp at this hb <;> linarith
      left
      refine ⟨?_, ?_⟩
      · funext a; fin_cases a <;> simp [pureMixed] <;> linarith
      · have y0 : y 0 = 1 := by linarith [hyz 1 (by decide), hyz 2 (by decide), hyz 3 (by decide)]
        funext b
        by_cases hb : b = 0
        · subst hb; simp [pureMixed, y0]
        · rw [hyz b hb]; simp [pureMixed, hb]
    -- both rows are played: player 1 is indifferent
    have hUD := hr 0 hx0p 1
    have hDU := hr 1 hx1p 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hUD hDU
    have hind : 200 * y 0 - 200 * y 1 - 200 * y 3 = y 2 := by linarith
    have y2 : y 2 = 0 := by
      rcases (hy0 2).eq_or_lt with h | h
      · exact h.symm
      · exfalso
        have hy0p : 0 < y 0 := by linarith [hy0 1, hy0 3]
        have m0 := c 2 h 0
        have m1 := c 2 h 1
        have l1 := c 0 hy0p 1
        simp at m0 m1 l1
        linarith
    have y3 : y 3 = 0 := by
      rcases (hy0 3).eq_or_lt with h | h
      · exact h.symm
      · exfalso
        have hy0p : 0 < y 0 := by linarith [hy0 1]
        have r0 := c 3 h 0
        have r2 := c 3 h 2
        have l3 := c 0 hy0p 3
        simp at r0 r2 l3
        linarith
    have y0 : y 0 = 1 / 2 := by linarith
    have y1 : y 1 = 1 / 2 := by linarith
    have l1 := c 0 (by linarith) 1
    have l0 := c 1 (by linarith) 0
    simp at l1 l0
    have x1 : x 1 = 1 / 52 := by linarith
    have x0 : x 0 = 51 / 52 := by linarith
    right; right
    refine ⟨?_, ?_⟩
    · funext a; fin_cases a <;> simp [krepsX, x0, x1]
    · funext b; fin_cases b <;> simp [krepsY, y0, y1, y2, y3]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
      · fin_cases a <;> fin_cases a' <;> simp [pureMixed] at ha ⊢
      · fin_cases b <;> fin_cases b' <;> simp [pureMixed] at hb ⊢
        norm_num
    · refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
      · fin_cases a <;> fin_cases a' <;> simp [pureMixed] at ha ⊢
      · fin_cases b <;> fin_cases b' <;> simp [pureMixed] at hb ⊢ <;> norm_num
    · refine ⟨fun a ha a' => ?_, fun b hb b' => ?_⟩
      · fin_cases a <;> fin_cases a' <;> simp [krepsY] at ha ⊢
      · fin_cases b <;> fin_cases b' <;> simp [krepsY, krepsX] at hb ⊢ <;> norm_num

/-- **Exercise 8.D.9(c)** (MWG, p. 265). `M` is not played in any Nash equilibrium. -/
theorem exercise_8_D_9c_not_nash {x : Fin 2 → ℝ} {y : Fin 4 → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) (h : IsMixedNash kreps (mp x y)) : y 2 = 0 := by
  rcases (exercise_8_D_9b hx hy).1 h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    simp [pureMixed, krepsY]

/-- **Exercise 8.D.9(c)** (MWG, p. 265). `M` is a rationalizable strategy (Definition 8.C.2): the
sets `{½U + ½D, (51/52)U + (1/52)D}` and `{M, ½LL + ½L}` are best responses to each other. -/
theorem exercise_8_D_9c_rationalizable : Rationalizable kreps 1 (pureMixed (2 : Fin 4)) := by
  set xh : Fin 2 → ℝ := ![1 / 2, 1 / 2] with hxh
  have hmx : IsMixedStrategy xh :=
    ⟨fun a => by fin_cases a <;> norm_num [xh], by norm_num [xh, Fin.sum_univ_two]⟩
  have hmX : IsMixedStrategy krepsX :=
    ⟨fun a => by fin_cases a <;> norm_num [krepsX], by norm_num [krepsX, Fin.sum_univ_two]⟩
  have hmY : IsMixedStrategy krepsY :=
    ⟨fun b => by fin_cases b <;> norm_num [krepsY], by norm_num [krepsY, Fin.sum_univ_four]⟩
  have hmM : IsMixedStrategy (pureMixed (2 : Fin 4)) := isMixedStrategy_pureMixed _
  set T : (i : Fin 2) → Set (S2 2 4 i → ℝ) :=
    Fin.cons ({xh, krepsX} : Set (Fin 2 → ℝ))
      (Fin.cons ({pureMixed 2, krepsY} : Set (Fin 4 → ℝ)) finZeroElim) with hT
  -- player 1's mixtures are best responses to `½LL + ½L` (both rows give `0`)
  have br1 : ∀ x : Fin 2 → ℝ, IsMixedStrategy x → IsBestResponse kreps 0 x (mp xh krepsY) := by
    intro x hx
    refine (isBestResponse_iff_support kreps 0 (τ := x) hx _).2 ?_
    intro a _ a'
    refine (bimatrix_mixedPayoff_row _ _ _ a').trans_le
      (le_of_le_of_eq ?_ (bimatrix_mixedPayoff_row _ _ _ a).symm)
    simp only [mp_one]
    fin_cases a <;> fin_cases a' <;> simp [Fin.sum_univ_four, krepsU₁, krepsY]
  -- player 2's best replies
  have br2M : IsBestResponse kreps 1 (pureMixed (2 : Fin 4)) (mp xh krepsY) := by
    refine bimatrix_isBestResponse_col _ _ _ (2 : Fin 4) fun b' => ?_
    simp only [mp_zero, kreps_cols]
    fin_cases b' <;> simp [xh] <;> norm_num
  have br2Y : IsBestResponse kreps 1 krepsY (mp krepsX krepsY) := by
    refine (isBestResponse_iff_support kreps 1 (τ := krepsY) hmY _).2 ?_
    intro b hb b'
    refine (bimatrix_mixedPayoff_col _ _ _ b').trans_le
      (le_of_le_of_eq ?_ (bimatrix_mixedPayoff_col _ _ _ b).symm)
    simp only [mp_zero]
    fin_cases b <;> fin_cases b' <;> simp [Fin.sum_univ_two, krepsU₂, krepsY, krepsX] at hb ⊢ <;>
      norm_num
  refine rationalizable_of_bestResponseSet (T := T) (fun i τ hτ => ?_) (fun i τ hτ => ?_) ?_
  · fin_cases i
    · rcases hτ with rfl | rfl
      · exact hmx
      · exact hmX
    · rcases hτ with rfl | rfl
      · exact hmM
      · exact hmY
  · fin_cases i
    · refine ⟨mp xh krepsY, isMixedProfile_mp hmx hmY, fun j hj => ?_, ?_⟩
      · fin_cases j
        · exact absurd rfl hj
        · exact Or.inr rfl
      · rcases hτ with rfl | rfl
        · exact br1 _ hmx
        · exact br1 _ hmX
    · rcases hτ with rfl | rfl
      · refine ⟨mp xh krepsY, isMixedProfile_mp hmx hmY, fun j hj => ?_, br2M⟩
        fin_cases j
        · exact Or.inl rfl
        · exact absurd rfl hj
      · refine ⟨mp krepsX krepsY, isMixedProfile_mp hmX hmY, fun j hj => ?_, br2Y⟩
        fin_cases j
        · exact Or.inr rfl
        · exact absurd rfl hj
  · exact Or.inl rfl

/-- **Exercise 8.D.9(d)** (MWG, p. 265), its mathematical content. Both pure strategy equilibria
give the payoffs `(100, 2)`, while player 2 gets `0` whenever he plays `M`: an agreement on either
pure equilibrium is strictly better for both players than any outcome with `M`. -/
theorem exercise_8_D_9d :
    krepsU₁ 0 0 = 100 ∧ krepsU₂ 0 0 = 2 ∧ krepsU₁ 1 3 = 100 ∧ krepsU₂ 1 3 = 2 ∧
      (∀ a, krepsU₁ a 2 < 100 ∧ krepsU₂ a 2 < 2) := by
  refine ⟨rfl, rfl, rfl, rfl, fun a => ?_⟩
  fin_cases a <;> norm_num [krepsU₁, krepsU₂]

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 8.E.1: two armies and an island

MWG, Exercise 8.E.1, p. 265.

Two armies choose to attack (`true`) or not (`false`). Each army is strong (`true`) or weak
(`false`) with probability `½`, independently, and knows only its own type. The island is worth
`M > 0`. An army that attacks captures the island if its rival does not attack, or if both attack
and it is strong while the rival is weak. When both attack they fight: an army pays its cost of
fighting, `s` if strong and `w` if weak (`0 < s < w`); there is no cost when the rival does not
attack. So an attacking army gets `M` if the rival does not attack; if both attack it gets `M - s`
(strong against weak), `-w` (weak against strong) or minus its own cost (equal strength); an army
that does not attack gets `0` (`armyPay`, `armies`).

A decision rule is a pair (action when strong, action when weak). **Exercise 8.E.1**
(`exercise_8_E_1`): the pure strategy Bayesian Nash equilibria are exactly
* one army always attacks and the other never does, when `M ≤ 2s`;
* one army always attacks and the other attacks only when strong, when `M ≥ 2s` and `M ≥ w`;
* both attack only when strong, when `s ≤ M ≤ w`.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- The payoff of an army that chooses `a` (attack = `true`) of type `t` (strong = `true`) when the
rival chooses `a'` and has type `t'`. -/
noncomputable def armyPay (M s w : ℝ) (a a' t t' : Bool) : ℝ :=
  if a then
    (if a' then (if t && !t' then M - s else if !t && t' then -w else -(if t then s else w))
      else M)
  else 0

/-- **Exercise 8.E.1** (MWG, p. 265). The armies game as a Bayesian game: types are independent
and each is strong with probability `½`. -/
noncomputable def armies (M s w : ℝ) : BayesianGame (Fin 2) (fun _ => Bool) (fun _ => Bool) where
  prior _ := 1 / 4
  payoff i a θ := armyPay M s w (a i) (a (1 - i)) (θ i) (θ (1 - i))

/-- A sum over the four type profiles. -/
theorem sum_fin2_bool (f : (Fin 2 → Bool) → ℝ) :
    ∑ θ, f θ = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  have e : ∀ p q : Bool, (piFinTwoEquiv fun _ => Bool).symm (p, q) = ![p, q] := by
    intro p q
    funext k
    fin_cases k <;> rfl
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, e]
  ring

theorem armies_isPrior (M s w : ℝ) : (armies M s w).IsPrior := by
  refine ⟨fun _ => by norm_num [armies], ?_⟩
  simp only [armies, sum_fin2_bool]
  norm_num

theorem armies_typeProb (M s w : ℝ) (i : Fin 2) (t : Bool) :
    (armies M s w).typeProb i t = 1 / 2 := by
  unfold BayesianGame.typeProb
  rw [Finset.sum_filter, sum_fin2_bool]
  fin_cases i <;> cases t <;> simp [armies] <;> norm_num

/-- The gain of type `t` of army `i` from the action `a`: a quarter of the payoffs against the
rival's two types. -/
theorem armies_typeGain (M s w : ℝ) (σ : (i : Fin 2) → Bool → Bool) (i : Fin 2) (t a : Bool) :
    (armies M s w).typeGain σ i t a = (armyPay M s w a (σ (1 - i) true) t true +
      armyPay M s w a (σ (1 - i) false) t false) / 4 := by
  unfold BayesianGame.typeGain
  rw [Finset.sum_filter, sum_fin2_bool]
  fin_cases i <;> cases t <;>
    simp [armies, BayesianGame.play, Function.update] <;> ring

/-- Proposition 8.E.1 for the armies game: each type's action is a best reply to the rival's
decision rule, in terms of `armyPay`. -/
theorem armies_isBNE_iff (M s w : ℝ) (σ : (i : Fin 2) → Bool → Bool) :
    (armies M s w).IsBNE σ ↔ ∀ i t a, armyPay M s w a (σ (1 - i) true) t true +
      armyPay M s w a (σ (1 - i) false) t false ≤ armyPay M s w (σ i t) (σ (1 - i) true) t true +
      armyPay M s w (σ i t) (σ (1 - i) false) t false := by
  rw [BayesianGame.proposition_8_E_1 _ (armies_isPrior M s w)]
  refine forall_congr' fun i => forall_congr' fun t => ?_
  simp only [armies_typeProb, BayesianGame.condPayoff, armies_typeGain]
  constructor
  · intro h a
    have := h (by norm_num) a
    linarith
  · intro h _ a
    have := h a
    linarith

/-- Always attack. -/
def stratAA : Bool → Bool := fun _ => true

/-- Never attack. -/
def stratNN : Bool → Bool := fun _ => false

/-- Attack only when strong. -/
def stratAN : Bool → Bool := fun t => t

/-- **Exercise 8.E.1** (MWG, p. 265). With `M > 0` and `0 < s < w`, the pure strategy Bayesian Nash
equilibria of the armies game are: one army always attacks and the other never does (iff
`M ≤ 2s`); one army always attacks and the other attacks only when strong (iff `M ≥ 2s` and
`M ≥ w`); both attack only when strong (iff `s ≤ M ≤ w`). -/
theorem exercise_8_E_1 {M s w : ℝ} (hM : 0 < M) (hs : 0 < s) (hsw : s < w)
    (σ : (i : Fin 2) → Bool → Bool) :
    (armies M s w).IsBNE σ ↔
      (M ≤ 2 * s ∧ ((σ 0 = stratAA ∧ σ 1 = stratNN) ∨ (σ 0 = stratNN ∧ σ 1 = stratAA))) ∨
      (2 * s ≤ M ∧ w ≤ M ∧ ((σ 0 = stratAN ∧ σ 1 = stratAA) ∨
        (σ 0 = stratAA ∧ σ 1 = stratAN))) ∨
      (s ≤ M ∧ M ≤ w ∧ σ 0 = stratAN ∧ σ 1 = stratAN) := by
  rw [armies_isBNE_iff]
  have e10 : (1 : Fin 2) - 0 = 1 := by decide
  have e11 : (1 : Fin 2) - 1 = 0 := by decide
  have hfun : ∀ (f : Bool → Bool) (p q : Bool),
      (f = fun t => if t then p else q) ↔ (f true = p ∧ f false = q) := by
    intro f p q
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩; funext t; cases t <;> simp [h1, h2]
  have hAA : ∀ i, σ i = stratAA ↔ σ i true = true ∧ σ i false = true := fun i => by
    rw [show stratAA = fun t => if t then true else true by funext t; cases t <;> rfl, hfun]
  have hNN : ∀ i, σ i = stratNN ↔ σ i true = false ∧ σ i false = false := fun i => by
    rw [show stratNN = fun t => if t then false else false by funext t; cases t <;> rfl, hfun]
  have hAN : ∀ i, σ i = stratAN ↔ σ i true = true ∧ σ i false = false := fun i => by
    rw [show stratAN = fun t => if t then true else false by funext t; cases t <;> rfl, hfun]
  simp only [hAA, hNN, hAN, Fin.forall_fin_two, Bool.forall_bool, e10, e11]
  generalize σ 0 true = p0
  generalize σ 0 false = q0
  generalize σ 1 true = p1
  generalize σ 1 false = q1
  cases p0 <;> cases q0 <;> cases p1 <;> cases q1 <;>
    simp only [armyPay, ↓reduceIte, add_neg_le_iff_le_add, add_self_nonpos_iff, add_zero,
      and_false, and_imp, and_self, and_true, Bool.and_false, Bool.and_self, Bool.and_true,
      Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.true_eq_false, false_or, gt_iff_lt,
      iff_false, le_add_neg_iff_add_le, Left.neg_nonpos_iff, le_neg_add_iff_add_le,
      le_neg_self_iff, neg_add_le_iff_le_add, nonneg_add_self_iff, not_and, not_le, or_false,
      or_self, or_true, le_refl, true_and, tsub_le_iff_right, zero_add] <;>
    first
    | linarith
    | (constructor <;> intro h <;> (try casesm* _ ∧ _) <;> (try constructorm* _ ∧ _) <;>
        linarith)
    | (intros; linarith)

/-- A concrete instance of Exercise 8.E.1 (`M = 1`, `s = 1`, `w = 2`): both armies attacking only
when strong is a Bayesian Nash equilibrium. -/
theorem exercise_8_E_1_instance : (armies 1 1 2).IsBNE (fun _ => stratAN) :=
  (exercise_8_E_1 one_pos one_pos one_lt_two _).2 (Or.inr (Or.inr ⟨le_rfl, one_le_two, rfl, rfl⟩))

end MWG.SimultaneousMoveGames

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 8.E.2: the first-price auction with uniform private values

MWG, Exercise 8.E.2, p. 265.

Each of `I = n + 1` bidders knows only his own valuation, drawn uniformly and independently from
`[0, v̄]`; bids are any real numbers, the highest bid wins and pays its bid. As in Example 8.E.2
(module `Zigger`) the continuum of types is handled type by type: when every rival bids
`s(x) = βx`, a single rival bids below `b` with probability `fpBelow v̄ β b`, the Lebesgue measure
of `{x ∈ [0, v̄] : βx < b}` divided by `v̄`; ties have probability zero (`fpTie_zero`); and a
bidder with value `v` who bids `b` against `n` independent rivals expects
`fpExp v̄ β n v b = (v - b) · fpBelow v̄ β b ^ n`.

* `fpBelow_eq`: `fpBelow v̄ β b = min(1, b/(βv̄))` for `b ≥ 0`, and `0` for `b ≤ 0`.
* `fp_core`: the inequality `(v - b) (b (n + 1)/n)^n ≤ v^{n+1}/(n + 1)` for `b ≥ 0`, from
  Bernoulli's inequality (an AM-GM step).
* **Exercise 8.E.2(b)** (`exercise_8_E_2b`): with `I = n + 1 ≥ 2` bidders, the linear rule
  `s(v) = ((I - 1)/I) v` is a symmetric Bayesian Nash equilibrium: against rivals using it, every
  type's bid `((I - 1)/I) v` maximizes `fpExp` over all real bids.
* **Exercise 8.E.2(a)** (`exercise_8_E_2a`): two bidders bid half their valuation.
* As `I → ∞` the equilibrium bid `((I - 1)/I) v` increases to `v` (`exercise_8_E_2b_limit`,
  `exercise_8_E_2b_mono`).
-/

namespace MWG.SimultaneousMoveGames

open MeasureTheory Filter Topology

/-- The probability that a rival with valuation uniform on `[0, v̄]` who bids `βx` bids below
`b`. -/
noncomputable def fpBelow (vbar β b : ℝ) : ℝ :=
  (volume (Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b})).toReal / vbar

/-- **Exercise 8.E.2** (MWG, p. 265). The expected payoff of a bidder with valuation `v` who bids
`b` when each of his `n` rivals bids `βx` at valuation `x`: he wins (paying `b`) iff all rivals bid
less, with probability `fpBelow v̄ β b ^ n` by independence. -/
noncomputable def fpExp (vbar β : ℝ) (n : ℕ) (v b : ℝ) : ℝ := (v - b) * fpBelow vbar β b ^ n

/-- Ties have probability zero: `{x : βx = b}` is a single point. -/
theorem fpTie_zero {β : ℝ} (hβ : 0 < β) (vbar b : ℝ) :
    volume (Set.Icc (0 : ℝ) vbar ∩ {x | β * x = b}) = 0 := by
  refine measure_mono_null (t := {b / β}) (fun x hx => ?_) (measure_singleton _)
  rw [Set.mem_singleton_iff, eq_div_iff hβ.ne', mul_comm]
  exact hx.2

/-- `fpBelow v̄ β b = min(1, b/(βv̄))` for `b ≥ 0`. -/
theorem fpBelow_eq {vbar β b : ℝ} (hv : 0 < vbar) (hβ : 0 < β) (hb : 0 ≤ b) :
    fpBelow vbar β b = min 1 (b / (β * vbar)) := by
  unfold fpBelow
  rcases le_or_gt b (β * vbar) with hle | hgt
  · have hset : Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b} = Set.Ico 0 (b / β) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_Ico]
      rw [lt_div_iff₀ hβ, mul_comm x β]
      constructor
      · rintro ⟨⟨h0, -⟩, h⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩
        refine ⟨⟨h0, ?_⟩, h⟩
        by_contra hx
        push Not at hx
        nlinarith
    rw [hset, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (div_nonneg hb hβ.le),
      min_eq_right ((div_le_one (by positivity)).2 hle), div_div]
  · have hset : Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b} = Set.Icc 0 vbar := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, by nlinarith [h.2]⟩
    rw [hset, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hv.le, div_self hv.ne',
      min_eq_left ((one_le_div (by positivity)).2 hgt.le)]

/-- Nobody bids below a nonpositive amount. -/
theorem fpBelow_nonpos {vbar β b : ℝ} (hβ : 0 < β) (hb : b ≤ 0) : fpBelow vbar β b = 0 := by
  unfold fpBelow
  have hset : Set.Icc (0 : ℝ) vbar ∩ {x | β * x < b} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]
    intro h0
    nlinarith [h0.1]
  rw [hset, measure_empty, ENNReal.toReal_zero, zero_div]

/-- Bernoulli's inequality in the form `(1 + n(1 - u)) uⁿ ≤ 1` for `u ≥ 0`. -/
theorem fp_bernoulli (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : (1 + n * (1 - u)) * u ^ n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt (1 + n * (1 - u)) 0 with hneg | hpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hneg (pow_nonneg hu n)).trans zero_le_one
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hu2 : u ≤ 2 := by
      by_contra h
      push Not at h
      nlinarith
    have hb := one_add_mul_le_pow (a := 1 - u) (by linarith) n
    calc (1 + n * (1 - u)) * u ^ n ≤ (1 + (1 - u)) ^ n * u ^ n :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg hu n)
      _ = ((2 - u) * u) ^ n := by rw [mul_pow]; ring
      _ ≤ 1 := pow_le_one₀ (mul_nonneg (by linarith) hu) (by nlinarith [sq_nonneg (u - 1)])

/-- The core inequality: with `n ≥ 1` rivals, `(v - b) (b (n + 1)/n)ⁿ ≤ (v/(n + 1)) vⁿ` for
`v, b ≥ 0`; equality at `b = (n/(n + 1)) v`. -/
theorem fp_core {n : ℕ} (hn : 1 ≤ n) {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) :
    (v - b) * (b * (n + 1) / n) ^ n ≤ v / (n + 1) * v ^ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases hv.eq_or_lt with rfl | hvp
  · have : 0 ≤ (b * (n + 1) / n) ^ n := pow_nonneg (by positivity) n
    simp only [zero_sub, zero_div, zero_mul]
    nlinarith
  · set u := b * (n + 1) / (n * v) with hu
    have hu0 : 0 ≤ u := by positivity
    have hbu : b * (n + 1) / n = v * u := by
      rw [hu]; field_simp
    have hvb : v - b = v / (n + 1) * (1 + n * (1 - u)) := by
      rw [hu]; field_simp; ring
    rw [hbu, hvb, mul_pow]
    have key := fp_bernoulli n hu0
    have hpos : 0 ≤ v / (n + 1) * v ^ n := by positivity
    calc v / (↑n + 1) * (1 + ↑n * (1 - u)) * (v ^ n * u ^ n)
        = v / (↑n + 1) * v ^ n * ((1 + ↑n * (1 - u)) * u ^ n) := by ring
      _ ≤ v / (↑n + 1) * v ^ n * 1 := mul_le_mul_of_nonneg_left key hpos
      _ = v / (↑n + 1) * v ^ n := mul_one _

/-- **Exercise 8.E.2(b)** (MWG, p. 265). With `I = n + 1 ≥ 2` bidders whose valuations are
uniform on `[0, v̄]`, the linear bid function `s(v) = (n/(n + 1)) v = ((I - 1)/I) v` is a symmetric
Bayesian Nash equilibrium: when every rival uses it, a bidder of any type `v ∈ [0, v̄]` maximizes
his expected payoff over all real bids `b` by bidding `s(v)`. -/
theorem exercise_8_E_2b {vbar : ℝ} (hvbar : 0 < vbar) {n : ℕ} (hn : 1 ≤ n) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ vbar) (b : ℝ) :
    fpExp vbar (n / (n + 1)) n v b ≤ fpExp vbar (n / (n + 1)) n v (n / (n + 1) * v) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := n / (n + 1) with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β < 1 := by rw [hβ, div_lt_one (by positivity)]; linarith
  -- the equilibrium payoff
  have hstar : fpExp vbar β n v (β * v) = v / (n + 1) * (v / vbar) ^ n := by
    unfold fpExp
    rw [fpBelow_eq hvbar hβ0 (by positivity)]
    rw [min_eq_right]
    · rw [mul_div_mul_left _ _ hβ0.ne', hβ]
      field_simp
      ring
    · rw [mul_div_mul_left _ _ hβ0.ne', div_le_one hvbar]; exact hv1
  have hRHS0 : 0 ≤ v / (n + 1) * (v / vbar) ^ n := by positivity
  rw [hstar]
  unfold fpExp
  rcases le_or_gt b 0 with hb | hb
  · rw [fpBelow_nonpos hβ0 hb, zero_pow (by omega), mul_zero]
    exact hRHS0
  -- the core inequality, divided by `v̄ⁿ`
  have hcore : ∀ b', 0 ≤ b' → (v - b') * (b' / (β * vbar)) ^ n ≤ v / (n + 1) * (v / vbar) ^ n := by
    intro b' hb'
    have := fp_core hn hv0 hb'
    have hvn : 0 < vbar ^ n := pow_pos hvbar n
    have e1 : (b' / (β * vbar)) ^ n = (b' * (n + 1) / n) ^ n / vbar ^ n := by
      rw [← div_pow]; congr 1; rw [hβ]; field_simp
    have e2 : (v / vbar) ^ n = v ^ n / vbar ^ n := div_pow _ _ _
    rw [e1, e2, ← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right this hvn.le
  rw [fpBelow_eq hvbar hβ0 hb.le]
  rcases le_or_gt b (β * vbar) with hle | hgt
  · rw [min_eq_right ((div_le_one (by positivity)).2 hle)]
    exact hcore b hb.le
  · rw [min_eq_left ((one_le_div (by positivity)).2 hgt.le), one_pow, mul_one]
    have := hcore (β * vbar) (by positivity)
    rw [div_self (by positivity), one_pow, mul_one] at this
    linarith

/-- **Exercise 8.E.2(a)** (MWG, p. 265). With two bidders, bidding half one's valuation,
`s(v) = v/2`, is a symmetric Bayesian Nash equilibrium. -/
theorem exercise_8_E_2a {vbar : ℝ} (hvbar : 0 < vbar) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ vbar)
    (b : ℝ) : fpExp vbar (1 / 2) 1 v b ≤ fpExp vbar (1 / 2) 1 v (v / 2) := by
  convert exercise_8_E_2b hvbar (n := 1) le_rfl hv0 hv1 b using 3 <;> norm_num
  ring

/-- **Exercise 8.E.2(b)** (MWG, p. 265). As the number of bidders `I` grows, each bidder's
equilibrium bid `((I - 1)/I) v` converges to his valuation `v`. -/
theorem exercise_8_E_2b_limit (v : ℝ) :
    Tendsto (fun I : ℕ => ((I : ℝ) - 1) / I * v) atTop (𝓝 v) := by
  have h : Tendsto (fun I : ℕ => (1 : ℝ) - 1 / I) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h
  have h2 := h.mul_const v
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with I hI
  have : (I : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Exercise 8.E.2(b)** (MWG, p. 265). The equilibrium bid `((I - 1)/I) v` is increasing in the
number of bidders `I`. -/
theorem exercise_8_E_2b_mono {v : ℝ} (hv : 0 ≤ v) {I J : ℕ} (hI : 1 ≤ I) (hIJ : I ≤ J) :
    ((I : ℝ) - 1) / I * v ≤ ((J : ℝ) - 1) / J * v := by
  have hI' : (1 : ℝ) ≤ I := by exact_mod_cast hI
  have hIJ' : (I : ℝ) ≤ J := by exact_mod_cast hIJ
  apply mul_le_mul_of_nonneg_right _ hv
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end MWG.SimultaneousMoveGames

set_option linter.style.longLine false
#print axioms MWG.SimultaneousMoveGames.StrictlyDominant
#print axioms MWG.SimultaneousMoveGames.StrictlyDominates
#print axioms MWG.SimultaneousMoveGames.StrictlyDominated
#print axioms MWG.SimultaneousMoveGames.strictlyDominant_iff_dominates
#print axioms MWG.SimultaneousMoveGames.WeaklyDominates
#print axioms MWG.SimultaneousMoveGames.WeaklyDominated
#print axioms MWG.SimultaneousMoveGames.WeaklyDominant
#print axioms MWG.SimultaneousMoveGames.StrictlyDominates.weaklyDominates
#print axioms MWG.SimultaneousMoveGames.StrictlyDominates.trans
#print axioms MWG.SimultaneousMoveGames.IsNashEquilibrium
#print axioms MWG.SimultaneousMoveGames.bestResponse
#print axioms MWG.SimultaneousMoveGames.bestResponse_update
#print axioms MWG.SimultaneousMoveGames.isNashEquilibrium_iff_mem_bestResponse
#print axioms MWG.SimultaneousMoveGames.IsNashEquilibrium.not_strictlyDominated
#print axioms MWG.SimultaneousMoveGames.SDominatedIn
#print axioms MWG.SimultaneousMoveGames.SDStep
#print axioms MWG.SimultaneousMoveGames.SDTerminal
#print axioms MWG.SimultaneousMoveGames.fullSets
#print axioms MWG.SimultaneousMoveGames.sdChain_subset
#print axioms MWG.SimultaneousMoveGames.sdStep_nonempty
#print axioms MWG.SimultaneousMoveGames.sdChain_nonempty
#print axioms MWG.SimultaneousMoveGames.sdChain_dominated_by_survivor
#print axioms MWG.SimultaneousMoveGames.sdTerminal_subset_chain
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_4
#print axioms MWG.SimultaneousMoveGames.countingGame
#print axioms MWG.SimultaneousMoveGames.countingGame_step
#print axioms MWG.SimultaneousMoveGames.countingGame_terminal
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_4_infinite_counterexample
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_2
#print axioms MWG.SimultaneousMoveGames.IsMixedProfile
#print axioms MWG.SimultaneousMoveGames.pureProfile
#print axioms MWG.SimultaneousMoveGames.isMixedProfile_pureProfile
#print axioms MWG.SimultaneousMoveGames.pureProfile_update
#print axioms MWG.SimultaneousMoveGames.prod_update_eq
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_update
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_update_update
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_update_add_smul
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_update_sum_smul
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_update_eq_sum_pure
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_pureProfile_update
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_pureProfile
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_pureProfile_update_mixed
#print axioms MWG.SimultaneousMoveGames.prod_mixed_nonneg
#print axioms MWG.SimultaneousMoveGames.sum_prod_mixed_eq_one
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_update_eq_expect
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_le_of_pure
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_lt_of_pure
#print axioms MWG.SimultaneousMoveGames.abs_mixedPayoff_le
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_compound
#print axioms MWG.SimultaneousMoveGames.MixedStrictlyDominates
#print axioms MWG.SimultaneousMoveGames.MixedStrictlyDominated
#print axioms MWG.SimultaneousMoveGames.MixedStrictlyDominant
#print axioms MWG.SimultaneousMoveGames.mixedStrictlyDominates_iff_pure
#print axioms MWG.SimultaneousMoveGames.proposition_8_B_1
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_shift
#print axioms MWG.SimultaneousMoveGames.isMixedStrategy_shift
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_6
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_le_of_pure_le
#print axioms MWG.SimultaneousMoveGames.uniformMixed
#print axioms MWG.SimultaneousMoveGames.isMixedStrategy_uniformMixed
#print axioms MWG.SimultaneousMoveGames.uniformMixed_pos
#print axioms MWG.SimultaneousMoveGames.isMixedProfile_uniform
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_7
#print axioms MWG.SimultaneousMoveGames.IsBestResponse
#print axioms MWG.SimultaneousMoveGames.NeverBestResponse
#print axioms MWG.SimultaneousMoveGames.isBestResponse_update
#print axioms MWG.SimultaneousMoveGames.neverBestResponse_of_mixedStrictlyDominated
#print axioms MWG.SimultaneousMoveGames.isBestResponse_iff_support
#print axioms MWG.SimultaneousMoveGames.isBestResponse_pureMixed_of_max
#print axioms MWG.SimultaneousMoveGames.exists_pure_bestResponse
#print axioms MWG.SimultaneousMoveGames.footnote_8_1
#print axioms MWG.SimultaneousMoveGames.IsMixedNash
#print axioms MWG.SimultaneousMoveGames.isMixedNash_iff_bestResponse
#print axioms MWG.SimultaneousMoveGames.isMixedNash_iff_mixedExtensionGame
#print axioms MWG.SimultaneousMoveGames.proposition_8_D_1
#print axioms MWG.SimultaneousMoveGames.isMixedNash_iff_pure_deviations
#print axioms MWG.SimultaneousMoveGames.corollary_8_D_1
#print axioms MWG.SimultaneousMoveGames.theorem_M_I_1
#print axioms MWG.SimultaneousMoveGames.theorem_M_I_1_instance
#print axioms MWG.SimultaneousMoveGames.brouwer_unitInterval_ivt
#print axioms MWG.SimultaneousMoveGames.figure_M_I_1b
#print axioms MWG.SimultaneousMoveGames.unitCircle
#print axioms MWG.SimultaneousMoveGames.rotateClockwise
#print axioms MWG.SimultaneousMoveGames.circle_rotation_no_fixedPoint
#print axioms MWG.SimultaneousMoveGames.circle_not_convex
#print axioms MWG.SimultaneousMoveGames.kakutani_mwg
#print axioms MWG.SimultaneousMoveGames.theorem_M_I_2
#print axioms MWG.SimultaneousMoveGames.theorem_M_I_2_instance
#print axioms MWG.SimultaneousMoveGames.figM12b
#print axioms MWG.SimultaneousMoveGames.figure_M_I_2b
#print axioms MWG.SimultaneousMoveGames.theorem_M_I_3
#print axioms MWG.SimultaneousMoveGames.figure_M_I_3
#print axioms MWG.SimultaneousMoveGames.bestResp
#print axioms MWG.SimultaneousMoveGames.update_mem_pi
#print axioms MWG.SimultaneousMoveGames.lemma_8_AA_1
#print axioms MWG.SimultaneousMoveGames.nash_exists_of_quasiconcave
#print axioms MWG.SimultaneousMoveGames.proposition_8_D_3
#print axioms MWG.SimultaneousMoveGames.restrictGame
#print axioms MWG.SimultaneousMoveGames.isNashEquilibrium_restrictGame
#print axioms MWG.SimultaneousMoveGames.proposition_8_D_3_instance
#print axioms MWG.SimultaneousMoveGames.continuous_mixedPayoff
#print axioms MWG.SimultaneousMoveGames.concaveOn_mixedPayoff_update
#print axioms MWG.SimultaneousMoveGames.convex_mixedExtension
#print axioms MWG.SimultaneousMoveGames.isCompact_mixedExtension
#print axioms MWG.SimultaneousMoveGames.proposition_8_D_2
#print axioms MWG.SimultaneousMoveGames.no_mixedProfile_of_isEmpty
#print axioms MWG.SimultaneousMoveGames.footnote_8_5
#print axioms MWG.SimultaneousMoveGames.footnote_8_5_singleton
#print axioms MWG.SimultaneousMoveGames.BRToSome
#print axioms MWG.SimultaneousMoveGames.ratStep
#print axioms MWG.SimultaneousMoveGames.ratIter
#print axioms MWG.SimultaneousMoveGames.Rationalizable
#print axioms MWG.SimultaneousMoveGames.BRToSome.mono
#print axioms MWG.SimultaneousMoveGames.subset_ratIter_of_bestResponseSet
#print axioms MWG.SimultaneousMoveGames.rationalizable_of_bestResponseSet
#print axioms MWG.SimultaneousMoveGames.Rationalizable.isMixedStrategy
#print axioms MWG.SimultaneousMoveGames.NBRStep
#print axioms MWG.SimultaneousMoveGames.NBRTerminal
#print axioms MWG.SimultaneousMoveGames.exists_ratIter_subset_of_chain
#print axioms MWG.SimultaneousMoveGames.nbrChain_subset
#print axioms MWG.SimultaneousMoveGames.nbrTerminal_eq_rationalizable
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_2
#print axioms MWG.SimultaneousMoveGames.nbrStep_ratStep
#print axioms MWG.SimultaneousMoveGames.MSDStep
#print axioms MWG.SimultaneousMoveGames.sdStep_msdStep
#print axioms MWG.SimultaneousMoveGames.msd_dominated_lt
#print axioms MWG.SimultaneousMoveGames.exists_ratIter_support_subset
#print axioms MWG.SimultaneousMoveGames.rationalizable_support_subset
#print axioms MWG.SimultaneousMoveGames.msdChain_of_sdChain
#print axioms MWG.SimultaneousMoveGames.rationalizable_of_isMixedNash
#print axioms MWG.SimultaneousMoveGames.footnote_8_3
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_1
#print axioms MWG.SimultaneousMoveGames.IsBelief
#print axioms MWG.SimultaneousMoveGames.beliefPayoff
#print axioms MWG.SimultaneousMoveGames.bestResponse_correlated_of_not_dominated
#print axioms MWG.SimultaneousMoveGames.correlated_iff_not_dominated
#print axioms MWG.SimultaneousMoveGames.marginal
#print axioms MWG.SimultaneousMoveGames.isMixedProfile_marginal
#print axioms MWG.SimultaneousMoveGames.expect_eq_mixedPayoff_marginals
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_3
#print axioms MWG.SimultaneousMoveGames.IsPerturbation
#print axioms MWG.SimultaneousMoveGames.perturbedSet
#print axioms MWG.SimultaneousMoveGames.IsPerturbedNash
#print axioms MWG.SimultaneousMoveGames.IsTHP
#print axioms MWG.SimultaneousMoveGames.IsTotallyMixed
#print axioms MWG.SimultaneousMoveGames.isMixedStrategy_of_mem_perturbedSet
#print axioms MWG.SimultaneousMoveGames.perturbedNash_eq_of_not_best
#print axioms MWG.SimultaneousMoveGames.isTotallyMixed_of_perturbedNash
#print axioms MWG.SimultaneousMoveGames.mixed_le_one
#print axioms MWG.SimultaneousMoveGames.mixed_exists_pos
#print axioms MWG.SimultaneousMoveGames.proposition_8_F_1
#print axioms MWG.SimultaneousMoveGames.MixedWeaklyDominates
#print axioms MWG.SimultaneousMoveGames.MixedWeaklyDominated
#print axioms MWG.SimultaneousMoveGames.mixedWeaklyDominates_iff_pure
#print axioms MWG.SimultaneousMoveGames.MixedWeaklyDominates.lt_of_totallyMixed
#print axioms MWG.SimultaneousMoveGames.proposition_8_F_2
#print axioms MWG.SimultaneousMoveGames.mixedWeaklyDominated_of_pure
#print axioms MWG.SimultaneousMoveGames.proposition_8_F_2_pure
#print axioms MWG.SimultaneousMoveGames.convex_perturbedSet
#print axioms MWG.SimultaneousMoveGames.isCompact_perturbedSet
#print axioms MWG.SimultaneousMoveGames.perturbedSet_nonempty
#print axioms MWG.SimultaneousMoveGames.exists_perturbedNash
#print axioms MWG.SimultaneousMoveGames.tendsto_mixedPayoff_update
#print axioms MWG.SimultaneousMoveGames.uniformTremble
#print axioms MWG.SimultaneousMoveGames.isPerturbation_uniformTremble
#print axioms MWG.SimultaneousMoveGames.tendsto_uniformTremble
#print axioms MWG.SimultaneousMoveGames.exercise_8_F_3
#print axioms MWG.SimultaneousMoveGames.exists_nash_no_weakly_dominated
#print axioms MWG.SimultaneousMoveGames.S2
#print axioms MWG.SimultaneousMoveGames.bimatrix
#print axioms MWG.SimultaneousMoveGames.pp
#print axioms MWG.SimultaneousMoveGames.pp_zero
#print axioms MWG.SimultaneousMoveGames.pp_one
#print axioms MWG.SimultaneousMoveGames.eq_pp
#print axioms MWG.SimultaneousMoveGames.bimatrix_payoff_zero
#print axioms MWG.SimultaneousMoveGames.bimatrix_payoff_one
#print axioms MWG.SimultaneousMoveGames.bimatrix_update_zero
#print axioms MWG.SimultaneousMoveGames.bimatrix_update_one
#print axioms MWG.SimultaneousMoveGames.bimatrix_isNash_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_strictlyDominates_zero_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_strictlyDominates_one_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_weaklyDominates_zero_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_weaklyDominates_one_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_strictlyDominant_zero_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_strictlyDominant_one_iff
#print axioms MWG.SimultaneousMoveGames.ps
#print axioms MWG.SimultaneousMoveGames.ps_zero
#print axioms MWG.SimultaneousMoveGames.ps_one
#print axioms MWG.SimultaneousMoveGames.bimatrix_sdominatedIn_zero_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_sdominatedIn_one_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_sdStep_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_sdTerminal_iff
#print axioms MWG.SimultaneousMoveGames.fullSets_eq_ps
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_fin_two
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixedPayoff
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixedPayoff_row
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixedPayoff_col
#print axioms MWG.SimultaneousMoveGames.mp
#print axioms MWG.SimultaneousMoveGames.mp_zero
#print axioms MWG.SimultaneousMoveGames.mp_one
#print axioms MWG.SimultaneousMoveGames.isMixedProfile_mp
#print axioms MWG.SimultaneousMoveGames.bimatrix_isMixedNash_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixed_vs_pure_zero
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixed_vs_pure_one
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixedStrictlyDominates_zero_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_mixedStrictlyDominates_one_iff
#print axioms MWG.SimultaneousMoveGames.bimatrix_isBestResponse_row
#print axioms MWG.SimultaneousMoveGames.bimatrix_isBestResponse_col
#print axioms MWG.SimultaneousMoveGames.bimatrix_isMixedNash_support
#print axioms MWG.SimultaneousMoveGames.sum_pureMixed_mul
#print axioms MWG.SimultaneousMoveGames.eq_mp
#print axioms MWG.SimultaneousMoveGames.pdU₁
#print axioms MWG.SimultaneousMoveGames.pdU₂
#print axioms MWG.SimultaneousMoveGames.figure_8_B_1_confess_dominant
#print axioms MWG.SimultaneousMoveGames.figure_8_B_1_dilemma
#print axioms MWG.SimultaneousMoveGames.fig8B2U₁
#print axioms MWG.SimultaneousMoveGames.fig8B2U₂
#print axioms MWG.SimultaneousMoveGames.example_8_B_1
#print axioms MWG.SimultaneousMoveGames.fig8B3U₁
#print axioms MWG.SimultaneousMoveGames.fig8B3U₂
#print axioms MWG.SimultaneousMoveGames.example_8_B_2
#print axioms MWG.SimultaneousMoveGames.RowWeaklyDominatedIn
#print axioms MWG.SimultaneousMoveGames.ColWeaklyDominatedIn
#print axioms MWG.SimultaneousMoveGames.WDStep2
#print axioms MWG.SimultaneousMoveGames.WDTerminal2
#print axioms MWG.SimultaneousMoveGames.wdTerminal2_singleton
#print axioms MWG.SimultaneousMoveGames.figure_8_B_3_order_dependence
#print axioms MWG.SimultaneousMoveGames.daU₁
#print axioms MWG.SimultaneousMoveGames.daU₂
#print axioms MWG.SimultaneousMoveGames.example_8_B_3_dominance
#print axioms MWG.SimultaneousMoveGames.example_8_B_3
#print axioms MWG.SimultaneousMoveGames.fig8B5U₁
#print axioms MWG.SimultaneousMoveGames.fig8B5U₂
#print axioms MWG.SimultaneousMoveGames.halfUD
#print axioms MWG.SimultaneousMoveGames.isMixedStrategy_halfUD
#print axioms MWG.SimultaneousMoveGames.figure_8_B_5
#print axioms MWG.SimultaneousMoveGames.fig8B5U₁'
#print axioms MWG.SimultaneousMoveGames.figure_8_B_5_variant
#print axioms MWG.SimultaneousMoveGames.fig8C1U₁
#print axioms MWG.SimultaneousMoveGames.fig8C1U₂
#print axioms MWG.SimultaneousMoveGames.bernheim
#print axioms MWG.SimultaneousMoveGames.halfB13
#print axioms MWG.SimultaneousMoveGames.isMixedStrategy_halfB13
#print axioms MWG.SimultaneousMoveGames.example_8_C_1_dominance
#print axioms MWG.SimultaneousMoveGames.bernheimSet
#print axioms MWG.SimultaneousMoveGames.example_8_C_1_rationalizable
#print axioms MWG.SimultaneousMoveGames.bernheim_bestResponse_b4
#print axioms MWG.SimultaneousMoveGames.example_8_C_1_not_rationalizable
#print axioms MWG.SimultaneousMoveGames.figure_8_C_2
#print axioms MWG.SimultaneousMoveGames.fig8D1U₁
#print axioms MWG.SimultaneousMoveGames.fig8D1U₂
#print axioms MWG.SimultaneousMoveGames.example_8_D_1
#print axioms MWG.SimultaneousMoveGames.example_8_D_2
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_1
#print axioms MWG.SimultaneousMoveGames.meetNY
#print axioms MWG.SimultaneousMoveGames.example_8_D_3
#print axioms MWG.SimultaneousMoveGames.example_8_D_3_figure
#print axioms MWG.SimultaneousMoveGames.example_8_D_5_indifference
#print axioms MWG.SimultaneousMoveGames.example_8_D_5
#print axioms MWG.SimultaneousMoveGames.meetNY_correlated
#print axioms MWG.SimultaneousMoveGames.example_8_D_4_no_pure
#print axioms MWG.SimultaneousMoveGames.example_8_D_4
#print axioms MWG.SimultaneousMoveGames.BayesianGame
#print axioms MWG.SimultaneousMoveGames.BayesianGame.mk
#print axioms MWG.SimultaneousMoveGames.BayesianGame.prior
#print axioms MWG.SimultaneousMoveGames.BayesianGame.payoff
#print axioms MWG.SimultaneousMoveGames.BayesianGame.IsPrior
#print axioms MWG.SimultaneousMoveGames.BayesianGame.play
#print axioms MWG.SimultaneousMoveGames.BayesianGame.expectedPayoff
#print axioms MWG.SimultaneousMoveGames.BayesianGame.toNormalForm
#print axioms MWG.SimultaneousMoveGames.BayesianGame.IsBNE
#print axioms MWG.SimultaneousMoveGames.BayesianGame.isBNE_iff
#print axioms MWG.SimultaneousMoveGames.BayesianGame.typeProb
#print axioms MWG.SimultaneousMoveGames.BayesianGame.typeGain
#print axioms MWG.SimultaneousMoveGames.BayesianGame.condPayoff
#print axioms MWG.SimultaneousMoveGames.BayesianGame.play_update
#print axioms MWG.SimultaneousMoveGames.BayesianGame.expectedPayoff_update_eq
#print axioms MWG.SimultaneousMoveGames.BayesianGame.expectedPayoff_eq
#print axioms MWG.SimultaneousMoveGames.BayesianGame.typeGain_eq_zero
#print axioms MWG.SimultaneousMoveGames.BayesianGame.proposition_8_E_1
#print axioms MWG.SimultaneousMoveGames.BayesianGame.exists_mixed_BNE
#print axioms MWG.SimultaneousMoveGames.daDims
#print axioms MWG.SimultaneousMoveGames.DAΘ
#print axioms MWG.SimultaneousMoveGames.daBayes
#print axioms MWG.SimultaneousMoveGames.daθ
#print axioms MWG.SimultaneousMoveGames.daΘEquiv
#print axioms MWG.SimultaneousMoveGames.sum_daΘ
#print axioms MWG.SimultaneousMoveGames.daBayes_isPrior
#print axioms MWG.SimultaneousMoveGames.example_8_E_1
#print axioms MWG.SimultaneousMoveGames.zProb
#print axioms MWG.SimultaneousMoveGames.ZiggerBNE
#print axioms MWG.SimultaneousMoveGames.zigger_sqrt_lt_one
#print axioms MWG.SimultaneousMoveGames.zProb_mem
#print axioms MWG.SimultaneousMoveGames.volume_sq_ge
#print axioms MWG.SimultaneousMoveGames.volume_sq_ge_of_one_lt
#print axioms MWG.SimultaneousMoveGames.zigger_cutoff
#print axioms MWG.SimultaneousMoveGames.zigger_cutoff_ge_sqrt
#print axioms MWG.SimultaneousMoveGames.zigger_prob_response
#print axioms MWG.SimultaneousMoveGames.example_8_E_2
#print axioms MWG.SimultaneousMoveGames.example_8_E_2_exists
#print axioms MWG.SimultaneousMoveGames.example_8_E_2_outcomes
#print axioms MWG.SimultaneousMoveGames.Effort
#print axioms MWG.SimultaneousMoveGames.lobbyGame
#print axioms MWG.SimultaneousMoveGames.quad_max
#print axioms MWG.SimultaneousMoveGames.lobbyGame_update
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_1_dominant
#print axioms MWG.SimultaneousMoveGames.eq_of_strictlyDominant_of_max
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_1_only_if
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_1_one_firm
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_1_nonpositive
#print axioms MWG.SimultaneousMoveGames.weaklyDominant_unique
#print axioms MWG.SimultaneousMoveGames.AtLeastAsGoodAsAll
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_2a
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_2b
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_6
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_6_param
#print axioms MWG.SimultaneousMoveGames.iSup_iInf_le_iInf_iSup_of_bdd
#print axioms MWG.SimultaneousMoveGames.mprof
#print axioms MWG.SimultaneousMoveGames.Δ₁
#print axioms MWG.SimultaneousMoveGames.Δ₂
#print axioms MWG.SimultaneousMoveGames.pay2
#print axioms MWG.SimultaneousMoveGames.isMixedProfile_mprof
#print axioms MWG.SimultaneousMoveGames.abs_pay2_le
#print axioms MWG.SimultaneousMoveGames.maximin₁
#print axioms MWG.SimultaneousMoveGames.minimax₁
#print axioms MWG.SimultaneousMoveGames.maximin₂
#print axioms MWG.SimultaneousMoveGames.minimax₂
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_7a
#print axioms MWG.SimultaneousMoveGames.IsZeroSum2
#print axioms MWG.SimultaneousMoveGames.pay2_zeroSum
#print axioms MWG.SimultaneousMoveGames.update_mprof_zero
#print axioms MWG.SimultaneousMoveGames.update_mprof_one
#print axioms MWG.SimultaneousMoveGames.isMixedNash_mprof_iff
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_7b
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_7c
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_8_counterexample
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_8
#print axioms MWG.SimultaneousMoveGames.mixedWeaklyDominates_pureMixed
#print axioms MWG.SimultaneousMoveGames.fig8F1U₁
#print axioms MWG.SimultaneousMoveGames.fig8F1U₂
#print axioms MWG.SimultaneousMoveGames.figure_8_F_1
#print axioms MWG.SimultaneousMoveGames.vdU₁
#print axioms MWG.SimultaneousMoveGames.vanDamme
#print axioms MWG.SimultaneousMoveGames.p3
#print axioms MWG.SimultaneousMoveGames.mixedPayoff_three
#print axioms MWG.SimultaneousMoveGames.exercise_8_F_2_nash
#print axioms MWG.SimultaneousMoveGames.exercise_8_F_2_undominated
#print axioms MWG.SimultaneousMoveGames.exercise_8_F_2
#print axioms MWG.SimultaneousMoveGames.c4U
#print axioms MWG.SimultaneousMoveGames.c4E
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_4a
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_4a_printed_false
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_4b
#print axioms MWG.SimultaneousMoveGames.exercise_8_C_4c
#print axioms MWG.SimultaneousMoveGames.demandGame
#print axioms MWG.SimultaneousMoveGames.demand_update
#print axioms MWG.SimultaneousMoveGames.eff
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_4a
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_4b
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_4c
#print axioms MWG.SimultaneousMoveGames.gordan_alternative
#print axioms MWG.SimultaneousMoveGames.stiemke_alternative
#print axioms MWG.SimultaneousMoveGames.two_profile_ext
#print axioms MWG.SimultaneousMoveGames.two_other
#print axioms MWG.SimultaneousMoveGames.two_nonempty
#print axioms MWG.SimultaneousMoveGames.two_mixedPayoff_pure
#print axioms MWG.SimultaneousMoveGames.two_mixedPayoff_eq
#print axioms MWG.SimultaneousMoveGames.isBestResponse_two_mix
#print axioms MWG.SimultaneousMoveGames.exists_totallyMixed_bestResponse
#print axioms MWG.SimultaneousMoveGames.isTHP_of_not_weaklyDominated_two
#print axioms MWG.SimultaneousMoveGames.MSDTerminal
#print axioms MWG.SimultaneousMoveGames.BRToSomeConv
#print axioms MWG.SimultaneousMoveGames.ratStepConv
#print axioms MWG.SimultaneousMoveGames.ratIterConv
#print axioms MWG.SimultaneousMoveGames.RationalizableConv
#print axioms MWG.SimultaneousMoveGames.ratIterConv_subset
#print axioms MWG.SimultaneousMoveGames.rationalizableConv_of_bestResponseSet
#print axioms MWG.SimultaneousMoveGames.eq_zero_of_mem_convexHull
#print axioms MWG.SimultaneousMoveGames.exists_ratIterConv_support_subset
#print axioms MWG.SimultaneousMoveGames.exists_max_mem_of_msdChain
#print axioms MWG.SimultaneousMoveGames.exists_belief_of_msdTerminal
#print axioms MWG.SimultaneousMoveGames.rationalizableConv_of_msdTerminal_two
#print axioms MWG.SimultaneousMoveGames.rationalizableConv_iff_two
#print axioms MWG.SimultaneousMoveGames.msdTerminal_full_of_bestResponse
#print axioms MWG.SimultaneousMoveGames.ratGapU₁
#print axioms MWG.SimultaneousMoveGames.ratGapU₂
#print axioms MWG.SimultaneousMoveGames.ratGap
#print axioms MWG.SimultaneousMoveGames.halfLR
#print axioms MWG.SimultaneousMoveGames.isMixedStrategy_halfLR
#print axioms MWG.SimultaneousMoveGames.ratGap_bestResponse
#print axioms MWG.SimultaneousMoveGames.rationalizable_two_counterexample
#print axioms MWG.SimultaneousMoveGames.figure_8_F_1_UL_isTHP
#print axioms MWG.SimultaneousMoveGames.vickrey
#print axioms MWG.SimultaneousMoveGames.vickrey_update
#print axioms MWG.SimultaneousMoveGames.vickrey_truthful
#print axioms MWG.SimultaneousMoveGames.vickrey_le_truthful
#print axioms MWG.SimultaneousMoveGames.vickrey_sup_const
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_3
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_3_one_bidder
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_3_instance
#print axioms MWG.SimultaneousMoveGames.fpInt
#print axioms MWG.SimultaneousMoveGames.fpPay
#print axioms MWG.SimultaneousMoveGames.fpPay_eq
#print axioms MWG.SimultaneousMoveGames.fpPay_le_iff
#print axioms MWG.SimultaneousMoveGames.fpPay_lt_iff
#print axioms MWG.SimultaneousMoveGames.firstPrice
#print axioms MWG.SimultaneousMoveGames.one_sub_ne
#print axioms MWG.SimultaneousMoveGames.firstPrice_update
#print axioms MWG.SimultaneousMoveGames.firstPrice_weaklyDominates_iff
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_3a
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_3b
#print axioms MWG.SimultaneousMoveGames.fpInt_bound_iff
#print axioms MWG.SimultaneousMoveGames.firstPrice_isNash_iff
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_3c
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_3c_exists
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_3c_not_unique
#print axioms MWG.SimultaneousMoveGames.sdRound
#print axioms MWG.SimultaneousMoveGames.sdIter
#print axioms MWG.SimultaneousMoveGames.sdStep_sdRound
#print axioms MWG.SimultaneousMoveGames.sdIter_chain
#print axioms MWG.SimultaneousMoveGames.cournot
#print axioms MWG.SimultaneousMoveGames.rivalsTotal
#print axioms MWG.SimultaneousMoveGames.qIval
#print axioms MWG.SimultaneousMoveGames.cbr
#print axioms MWG.SimultaneousMoveGames.cournot_update
#print axioms MWG.SimultaneousMoveGames.rivalsTotal_const
#print axioms MWG.SimultaneousMoveGames.rivalsTotal_mem
#print axioms MWG.SimultaneousMoveGames.cournot_gap
#print axioms MWG.SimultaneousMoveGames.cournot_not_dominated
#print axioms MWG.SimultaneousMoveGames.cournot_round
#print axioms MWG.SimultaneousMoveGames.cournot_round_zero
#print axioms MWG.SimultaneousMoveGames.cournotBounds
#print axioms MWG.SimultaneousMoveGames.cournotBounds_inv
#print axioms MWG.SimultaneousMoveGames.cournot_two_sdIter
#print axioms MWG.SimultaneousMoveGames.cournotStar
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_5a
#print axioms MWG.SimultaneousMoveGames.exercise_8_B_5b
#print axioms MWG.SimultaneousMoveGames.typeP
#print axioms MWG.SimultaneousMoveGames.tcost
#print axioms MWG.SimultaneousMoveGames.bayesCournot
#print axioms MWG.SimultaneousMoveGames.expQ
#print axioms MWG.SimultaneousMoveGames.sum_fin2_fin2
#print axioms MWG.SimultaneousMoveGames.bayesCournot_isPrior
#print axioms MWG.SimultaneousMoveGames.bayesCournot_typeProb
#print axioms MWG.SimultaneousMoveGames.bayesCournot_typeGain
#print axioms MWG.SimultaneousMoveGames.quad_argmax
#print axioms MWG.SimultaneousMoveGames.bayesCournot_isBNE_iff
#print axioms MWG.SimultaneousMoveGames.bcq
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_3
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_3_instance
#print axioms MWG.SimultaneousMoveGames.icShare2
#print axioms MWG.SimultaneousMoveGames.icShare3
#print axioms MWG.SimultaneousMoveGames.iceCream2
#print axioms MWG.SimultaneousMoveGames.iceCream3
#print axioms MWG.SimultaneousMoveGames.uiMid
#print axioms MWG.SimultaneousMoveGames.icShare2_lt
#print axioms MWG.SimultaneousMoveGames.icShare2_self
#print axioms MWG.SimultaneousMoveGames.icShare2_gt
#print axioms MWG.SimultaneousMoveGames.iceCream2_update
#print axioms MWG.SimultaneousMoveGames.icShare2_le_half
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_5a
#print axioms MWG.SimultaneousMoveGames.icShare3_left
#print axioms MWG.SimultaneousMoveGames.icShare3_right
#print axioms MWG.SimultaneousMoveGames.icShare3_self
#print axioms MWG.SimultaneousMoveGames.icShare3_leftmost
#print axioms MWG.SimultaneousMoveGames.icShare3_rightmost
#print axioms MWG.SimultaneousMoveGames.icShare3_together
#print axioms MWG.SimultaneousMoveGames.iceCream3_update
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_5b
#print axioms MWG.SimultaneousMoveGames.krepsU₁
#print axioms MWG.SimultaneousMoveGames.krepsU₂
#print axioms MWG.SimultaneousMoveGames.kreps
#print axioms MWG.SimultaneousMoveGames.kreps_rows
#print axioms MWG.SimultaneousMoveGames.kreps_cols
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_9a
#print axioms MWG.SimultaneousMoveGames.krepsX
#print axioms MWG.SimultaneousMoveGames.krepsY
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_9b
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_9c_not_nash
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_9c_rationalizable
#print axioms MWG.SimultaneousMoveGames.exercise_8_D_9d
#print axioms MWG.SimultaneousMoveGames.armyPay
#print axioms MWG.SimultaneousMoveGames.armies
#print axioms MWG.SimultaneousMoveGames.sum_fin2_bool
#print axioms MWG.SimultaneousMoveGames.armies_isPrior
#print axioms MWG.SimultaneousMoveGames.armies_typeProb
#print axioms MWG.SimultaneousMoveGames.armies_typeGain
#print axioms MWG.SimultaneousMoveGames.armies_isBNE_iff
#print axioms MWG.SimultaneousMoveGames.stratAA
#print axioms MWG.SimultaneousMoveGames.stratNN
#print axioms MWG.SimultaneousMoveGames.stratAN
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_1
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_1_instance
#print axioms MWG.SimultaneousMoveGames.fpBelow
#print axioms MWG.SimultaneousMoveGames.fpExp
#print axioms MWG.SimultaneousMoveGames.fpTie_zero
#print axioms MWG.SimultaneousMoveGames.fpBelow_eq
#print axioms MWG.SimultaneousMoveGames.fpBelow_nonpos
#print axioms MWG.SimultaneousMoveGames.fp_bernoulli
#print axioms MWG.SimultaneousMoveGames.fp_core
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_2b
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_2a
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_2b_limit
#print axioms MWG.SimultaneousMoveGames.exercise_8_E_2b_mono
