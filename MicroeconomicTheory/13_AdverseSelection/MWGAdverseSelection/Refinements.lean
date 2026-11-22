/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Reasonable-beliefs refinements in signaling games

MWG, Appendix A to Chapter 13, pp. 467-472.

A signaling game (`SignalingGame`): player 1 has a type `θ` in a finite set `Θ` with prior
`f(θ) > 0` and chooses `a ∈ A`; the other players `j ∈ J` see `a` and choose `s_j ∈ S_j`
simultaneously. After `a`, given a belief `μ` on `Θ`, the responders play the normal form game
`responseGame G a μ` of Chapter 8 (expected payoffs).

* `IsPBE` is the perfect Bayesian equilibrium of p. 468 (pure strategies, conditions (i)-(iii)).
* `DominatedFor` is (13.AA.1) (and, relative to a set of responses, (13.AA.2)); `typesUndominated`
  is `Θ(a)`; `eqResponses G T a` is `S*(Θ̂, a)`; `typesUndominatedStar` is `Θ*(a)`;
  `EqDominated` is (13.AA.3) and `typesNotEqDominated` is `Θ**(a)`; `ReasonableBeliefs`;
  `ViolatesIC` is the intuitive criterion (13.AA.4).
* `eqDominated_of_dominated` (p. 471): an action dominated in the sense of (13.AA.2) is
  equilibrium dominated.
* `passesIC_of_reasonable` (p. 471): a PBE with reasonable beliefs (relative to `Θ**`) passes
  the intuitive criterion.
* `two_types_singleton`, `two_types_reasonable` (p. 472): with two types, when equilibrium
  domination eliminates a type there is only one admissible belief, and a PBE passing the
  intuitive criterion stays a PBE when that belief is imposed.
* `example_13_AA_1` (p. 472): with three types a PBE can pass the intuitive criterion although no
  PBE with the same outcome has reasonable beliefs.

Departures. "`Min_{s'} u₁(a', s', θ) > Max_s u₁(a, s, θ)`" is read as "every payoff from `a'`
exceeds every payoff from `a`" (equivalent when the minimum and maximum exist, as the book
presupposes). In (13.AA.4), when `Θ**(a) = ∅` we use all beliefs (`S*(Θ, a)`), matching the
convention for reasonable beliefs ("for all `a` with `Θ**(a) ≠ ∅`").
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset

/-- **Appendix A** (MWG, p. 467). A signaling game: payoffs `u₁(a, s, θ)` of player 1 and
`u_j(a, s, θ)` of the responders `j ∈ J`. -/
structure SignalingGame (Θ A J : Type*) (S : J → Type*) where
  u1 : A → ((j : J) → S j) → Θ → ℝ
  u : J → A → ((j : J) → S j) → Θ → ℝ

namespace SignalingGame

variable {Θ A J : Type*} {S : J → Type*} [Fintype Θ] [DecidableEq J]

/-- A belief on `Θ` concentrated on `T`. -/
def IsBeliefOn (T : Set Θ) (μ : Θ → ℝ) : Prop :=
  (∀ θ, 0 ≤ μ θ) ∧ ∑ θ, μ θ = 1 ∧ ∀ θ, 0 < μ θ → θ ∈ T

/-- **Appendix A** (MWG, p. 468). The responders' simultaneous-move game after `a` when the
probability of type `θ` is `μ(θ)`. -/
def responseGame (G : SignalingGame Θ A J S) (a : A) (μ : Θ → ℝ) : NormalForm J S where
  payoff j s := ∑ θ, μ θ * G.u j a s θ

open Classical in
/-- **Appendix A** (MWG, p. 468). A pure strategy perfect Bayesian equilibrium: (i) each type's
action is optimal, (ii) beliefs are derived by Bayes' rule on the path, (iii) after every `a`
the responses are a Nash equilibrium of the response game given the belief `μ(·|a)`. -/
def IsPBE (G : SignalingGame Θ A J S) (f : Θ → ℝ) (aS : Θ → A) (sS : A → (j : J) → S j)
    (μ : A → Θ → ℝ) : Prop :=
  (∀ θ a, G.u1 a (sS a) θ ≤ G.u1 (aS θ) (sS (aS θ)) θ) ∧
    (∀ a θ, (∃ θ', aS θ' = a) →
      μ a θ * ∑ θ' ∈ univ.filter (fun θ' => aS θ' = a), f θ' = if aS θ = a then f θ else 0) ∧
    ∀ a, IsBeliefOn Set.univ (μ a) ∧ IsNashEquilibrium (G.responseGame a (μ a)) (sS a)

/-- **(13.AA.1)-(13.AA.2)** (MWG, pp. 468-469). Action `a` is strictly dominated for type `θ`
relative to response sets `R a`: some `a'` does better against every response in `R a'` than
`a` does against any response in `R a`. With `R = univ` this is (13.AA.1). -/
def DominatedFor (G : SignalingGame Θ A J S) (R : A → Set ((j : J) → S j)) (a : A) (θ : Θ) :
    Prop :=
  ∃ a', ∀ s ∈ R a, ∀ s' ∈ R a', G.u1 a s θ < G.u1 a' s' θ

/-- **Appendix A** (MWG, p. 468). `Θ(a)`: the types for which `a` is not strictly dominated in the
sense of (13.AA.1). -/
def typesUndominated (G : SignalingGame Θ A J S) (a : A) : Set Θ :=
  {θ | ¬ G.DominatedFor (fun _ => Set.univ) a θ}

/-- **Appendix A** (MWG, p. 469). `S*(Θ̂, a)`: the equilibrium responses to `a` for some belief
concentrated on `Θ̂`. -/
def eqResponses (G : SignalingGame Θ A J S) (T : Set Θ) (a : A) : Set ((j : J) → S j) :=
  {s | ∃ μ, IsBeliefOn T μ ∧ IsNashEquilibrium (G.responseGame a μ) s}

/-- **Appendix A** (MWG, p. 469). `Θ*(a)`: types for which `a` is not dominated in the sense of
(13.AA.2). -/
def typesUndominatedStar (G : SignalingGame Θ A J S) (a : A) : Set Θ :=
  {θ | ¬ G.DominatedFor (G.eqResponses Set.univ) a θ}

/-- **(13.AA.3)** (MWG, p. 471). Action `a` is equilibrium dominated for `θ` in a PBE with
equilibrium payoffs `uS`: every equilibrium response to `a` gives `θ` less than `uS θ`. -/
def EqDominated (G : SignalingGame Θ A J S) (uS : Θ → ℝ) (a : A) (θ : Θ) : Prop :=
  ∀ s ∈ G.eqResponses Set.univ a, G.u1 a s θ < uS θ

/-- **Appendix A** (MWG, p. 471). `Θ**(a)`. -/
def typesNotEqDominated (G : SignalingGame Θ A J S) (uS : Θ → ℝ) (a : A) : Set Θ :=
  {θ | ¬ G.EqDominated uS a θ}

/-- **Appendix A** (MWG, pp. 468-471). Beliefs are reasonable relative to `T`: whenever `T a` is
nonempty, `μ(θ | a) > 0` only for `θ ∈ T a`. -/
def ReasonableBeliefs (T : A → Set Θ) (μ : A → Θ → ℝ) : Prop :=
  ∀ a, (T a).Nonempty → ∀ θ, 0 < μ a θ → θ ∈ T a

/-- The equilibrium payoff `u₁*(θ)` of type `θ`. -/
def eqPayoff (G : SignalingGame Θ A J S) (aS : Θ → A) (sS : A → (j : J) → S j) (θ : Θ) : ℝ :=
  G.u1 (aS θ) (sS (aS θ)) θ

open Classical in
/-- The set of types used by the intuitive criterion at `a`: `Θ**(a)`, or all types if it is
empty. -/
noncomputable def icTypes (G : SignalingGame Θ A J S) (uS : Θ → ℝ) (a : A) : Set Θ :=
  if (G.typesNotEqDominated uS a).Nonempty then G.typesNotEqDominated uS a else Set.univ

/-- **(13.AA.4)** (MWG, p. 471). A PBE with equilibrium payoffs `uS` violates the intuitive
criterion if some type `θ` has a deviation `a` that gives her more than `uS θ` against every
equilibrium response to beliefs concentrated on `Θ**(a)`. -/
def ViolatesIC (G : SignalingGame Θ A J S) (uS : Θ → ℝ) : Prop :=
  ∃ θ a, ∀ s ∈ G.eqResponses (G.icTypes uS a) a, uS θ < G.u1 a s θ

/-- In a PBE the response to every action is an equilibrium response. -/
theorem IsPBE.mem_eqResponses {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ) (a : A) :
    sS a ∈ G.eqResponses Set.univ a :=
  ⟨μ a, (h.2.2 a).1, (h.2.2 a).2⟩

/-- **Appendix A** (MWG, p. 471). In a PBE, an action that is strictly dominated for `θ` in the
sense of (13.AA.2) is equilibrium dominated for `θ`: `Θ**(a) ⊆ Θ*(a)`. -/
theorem eqDominated_of_dominated {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ) {a : A} {θ : Θ}
    (hd : G.DominatedFor (G.eqResponses Set.univ) a θ) :
    G.EqDominated (G.eqPayoff aS sS) a θ := by
  obtain ⟨a', ha'⟩ := hd
  intro s hs
  exact (ha' s hs (sS a') (h.mem_eqResponses a')).trans_le (h.1 θ a')

/-- **Appendix A** (MWG, p. 471). `Θ**(a) ⊆ Θ*(a)`. -/
theorem typesNotEqDominated_subset {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ) (a : A) :
    G.typesNotEqDominated (G.eqPayoff aS sS) a ⊆ G.typesUndominatedStar a :=
  fun _ hθ hd => hθ (eqDominated_of_dominated h hd)

/-- **Appendix A** (MWG, p. 471). A PBE whose beliefs are reasonable relative to `Θ**` passes the
intuitive criterion. -/
theorem passesIC_of_reasonable {G : SignalingGame Θ A J S} {f : Θ → ℝ} {aS : Θ → A}
    {sS : A → (j : J) → S j} {μ : A → Θ → ℝ} (h : G.IsPBE f aS sS μ)
    (hr : ReasonableBeliefs (G.typesNotEqDominated (G.eqPayoff aS sS)) μ) :
    ¬ G.ViolatesIC (G.eqPayoff aS sS) := by
  rintro ⟨θ, a, hv⟩
  have hmem : sS a ∈ G.eqResponses (G.icTypes (G.eqPayoff aS sS) a) a := by
    refine ⟨μ a, ⟨(h.2.2 a).1.1, (h.2.2 a).1.2.1, fun θ' hθ' => ?_⟩, (h.2.2 a).2⟩
    unfold icTypes
    split_ifs with hne
    · exact hr a hne θ' hθ'
    · trivial
  exact absurd (h.1 θ a) (not_le.2 (hv _ hmem))

/-- **Appendix A** (MWG, p. 472). With two types, a belief concentrated on a single type is the
point mass on it: when equilibrium domination eliminates one type there is only one admissible
belief. -/
theorem two_types_singleton {μ : Bool → ℝ} {b : Bool} (h : IsBeliefOn {b} μ) :
    μ b = 1 ∧ μ (!b) = 0 := by
  obtain ⟨h0, h1, hs⟩ := h
  have hnb : μ (!b) = 0 := by
    by_contra hne
    have := hs (!b) (lt_of_le_of_ne (h0 _) (Ne.symm hne))
    cases b <;> simp at this
  refine ⟨?_, hnb⟩
  rw [Fintype.sum_bool] at h1
  cases b <;> simp_all

/-- **Appendix A** (MWG, p. 472). With two types, if a PBE passes the intuitive criterion and
equilibrium domination at an off-path action `a` eliminates all but type `b`
(`Θ**(a) = {b}`), then imposing the only admissible belief (`b` for sure) together with a
suitable equilibrium response keeps it a PBE with the same outcome: the intuitive criterion and
reasonable beliefs make the same predictions. -/
theorem two_types_reasonable {A J : Type*} {S : J → Type*} [DecidableEq J] [DecidableEq A]
    {G : SignalingGame Bool A J S} {f : Bool → ℝ} {aS : Bool → A} {sS : A → (j : J) → S j}
    {μ : A → Bool → ℝ} (h : G.IsPBE f aS sS μ) (hIC : ¬ G.ViolatesIC (G.eqPayoff aS sS))
    {a : A} (hoff : ∀ θ, aS θ ≠ a) {b : Bool}
    (hb : G.typesNotEqDominated (G.eqPayoff aS sS) a = {b}) :
    ∃ s ν, IsBeliefOn {b} ν ∧
      G.IsPBE f aS (Function.update sS a s) (Function.update μ a ν) := by
  have hic : G.icTypes (G.eqPayoff aS sS) a = {b} := by
    simp [icTypes, hb]
  unfold ViolatesIC at hIC
  push Not at hIC
  obtain ⟨s, hs, hsb⟩ := hIC b a
  rw [hic] at hs
  obtain ⟨ν, hν, hne⟩ := hs
  have hsame : ∀ θ, Function.update sS a s (aS θ) = sS (aS θ) := fun θ =>
    Function.update_of_ne (hoff θ) _ _
  refine ⟨s, ν, hν, ⟨fun θ a' => ?_, fun a' θ ha' => ?_, fun a' => ?_⟩⟩
  · rw [hsame]
    by_cases ha : a' = a
    · subst ha
      rw [Function.update_self]
      by_cases hθ : θ = b
      · subst hθ; exact hsb
      · have hθd : θ ∉ G.typesNotEqDominated (G.eqPayoff aS sS) a' := by
          rw [hb]; exact hθ
        simp only [typesNotEqDominated, Set.mem_ofPred_eq, not_not] at hθd
        refine (hθd s ⟨ν, ⟨hν.1, hν.2.1, fun _ _ => trivial⟩, hne⟩).le
    · rw [Function.update_of_ne ha]; exact h.1 θ a'
  · have ha : a' ≠ a := by
      rintro rfl; obtain ⟨θ', h'⟩ := ha'; exact hoff θ' h'
    rw [Function.update_of_ne ha]; exact h.2.1 a' θ ha'
  · by_cases ha : a' = a
    · subst ha
      rw [Function.update_self, Function.update_self]
      exact ⟨⟨hν.1, hν.2.1, fun _ _ => trivial⟩, hne⟩
    · rw [Function.update_of_ne ha, Function.update_of_ne ha]; exact h.2.2 a'

end SignalingGame

end MWG.AdverseSelection
