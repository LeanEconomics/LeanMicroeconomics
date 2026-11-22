/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.NashImplementation

/-!
# Subgame perfect implementation: Example 23.BB.1 (Moore and Repullo)

MWG, Appendix B of Chapter 23, pp. 915-916 (Example 23.BB.1, Figure 23.BB.1), and
Exercise 23.BB.1 (p. 925).

A pure exchange economy with two consumers and two goods; consumer `i`'s type is `θᵢᶜ`
(Cobb-Douglas) or `θᵢᴸ` (Leontief). The social choice function is `f(θ) = xᶜ` if `θ₁ = θ₁ᶜ` and
`f(θ) = xᴸ` if `θ₁ = θ₁ᴸ`. MWG give the allocations only in Figure 23.BB.1; we make the figure
concrete. The Edgeworth box has total endowment `(10, 10)`; an allocation is consumer 1's bundle
`(a, b)` (consumer 2 gets `(10 - a, 10 - b)`); the utilities are
`u₁ᶜ = ab`, `u₁ᴸ = min(a, b)`, `u₂ᶜ = (10 - a)(10 - b)`, `u₂ᴸ = min(10 - a, 10 - b)`
(both Leontief kinks lie on the diagonal, through `xᶜ`), and
`xᶜ = (5, 5)`, `xᴸ = (4, 4)`, `y = (3, 3)`, `z = (9, 2)`. These reproduce the orderings read from
Figure 23.BB.1 (`example_23_BB_1_figure`): consumer 1 always prefers `xᶜ` to `xᴸ` and consumer 2
the reverse; a Cobb-Douglas consumer 1 prefers `z` to `y`, a Leontief consumer 1 prefers `y` to
`z`; consumer 2 of either type ranks `y ≻ xᴸ ≻ xᶜ ≻ z`. (In the figure the two Cobb-Douglas
indifference curves through `xᶜ` are drawn crossing or tangent; our `xᶜ` is on the contract curve,
which plays no role.)

* `example_23_BB_1_lowerContour`, `example_23_BB_1_not_monotonic`,
  `example_23_BB_1_not_strongly`: `Lᵢ(xᶜ, θᶜ) ⊆ Lᵢ(xᶜ, θᴸ)` for `i = 1, 2`, so `f` is not
  monotonic and (Proposition 23.BB.1) no mechanism strongly implements it in Nash equilibrium.
* The three-stage mechanism and its subgame perfect equilibria, defined directly by optimality at
  every decision node (backward induction, which characterizes subgame perfection in this finite
  game of perfect information): `exercise_23_BB_1b`, `example_23_BB_1` (for every profile the
  subgame perfect equilibrium is unique and yields `f(θ)`).
* `exercise_23_BB_1a`: the normal form and all its (pure) Nash equilibria. For `θ₁ = θ₁ᶜ` the
  Nash equilibrium is unique; for `θ₁ = θ₁ᴸ` there are three, one of which yields `xᶜ ≠ f(θ)`.
-/

namespace MWG.MechanismDesign

open Function

/-- **Example 23.BB.1** (MWG, p. 915). Feasible allocations in the Edgeworth box with total
endowment `(10, 10)`, recorded by consumer 1's bundle. -/
abbrev MRBox : Type := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ 10 ∧ 0 ≤ p.2 ∧ p.2 ≤ 10}

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `xᶜ = (5, 5)`. -/
def mrXC : MRBox := ⟨(5, 5), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `xᴸ = (4, 4)`. -/
def mrXL : MRBox := ⟨(4, 4), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `y = (3, 3)`. -/
def mrY : MRBox := ⟨(3, 3), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 916, Figure 23.BB.1). The allocation `z = (9, 2)`. -/
def mrZ : MRBox := ⟨(9, 2), by norm_num⟩

/-- **Example 23.BB.1** (MWG, p. 915). Utilities: type `true` is Cobb-Douglas (`θᵢᶜ`), type
`false` Leontief (`θᵢᴸ`); consumer 0 is MWG's consumer 1, consumer 1 is MWG's consumer 2. -/
noncomputable def mrU : Fin 2 → MRBox → Bool → ℝ := fun i p b =>
  if i = 0 then (if b then p.1.1 * p.1.2 else min p.1.1 p.1.2)
  else (if b then (10 - p.1.1) * (10 - p.1.2) else min (10 - p.1.1) (10 - p.1.2))

/-- **Example 23.BB.1** (MWG, p. 915). `f(θ) = xᶜ` if `θ₁ = θ₁ᶜ`, `xᴸ` if `θ₁ = θ₁ᴸ`. -/
def mrF (θ : Fin 2 → Bool) : MRBox := if θ 0 then mrXC else mrXL

/-- **Example 23.BB.1** (MWG, p. 916). `xᶜ ≠ xᴸ`. -/
theorem mrXL_ne_mrXC : mrXL ≠ mrXC := by
  intro h
  have h1 := congrArg (fun p : MRBox => p.1.1) h
  norm_num [mrXL, mrXC] at h1

/-- **Example 23.BB.1** (MWG, pp. 915-916, Figure 23.BB.1). The orderings of the figure, for both
types `b` of each consumer: consumer 1 prefers `xᶜ` to `xᴸ`, consumer 2 the reverse; consumer 1
of type `θ₁ᶜ` prefers `z` to `y`, of type `θ₁ᴸ` prefers `xᴸ` to `y` and `y` to `z`; consumer 2
ranks `y ≻ xᴸ ≻ xᶜ ≻ z`. -/
theorem example_23_BB_1_figure :
    (∀ b, mrU 0 mrXL b < mrU 0 mrXC b) ∧ (∀ b, mrU 1 mrXC b < mrU 1 mrXL b) ∧
      mrU 0 mrY true < mrU 0 mrZ true ∧ mrU 0 mrZ true < mrU 0 mrXC true ∧
      mrU 0 mrZ false < mrU 0 mrY false ∧ mrU 0 mrY false < mrU 0 mrXL false ∧
      (∀ b, mrU 1 mrZ b < mrU 1 mrXC b ∧ mrU 1 mrXL b < mrU 1 mrY b) := by
  refine ⟨fun b => ?_, fun b => ?_, ?_, ?_, ?_, ?_, fun b => ?_⟩ <;>
    try cases b
  all_goals norm_num [mrU, mrXC, mrXL, mrY, mrZ, min_def]

/-- **Example 23.BB.1** (MWG, p. 916). `Lᵢ(xᶜ, θᵢᶜ) ⊆ Lᵢ(xᶜ, θᵢᴸ)` for `i = 1, 2`: the Leontief
indifference curve through `xᶜ` has its kink at `xᶜ`, so everything not strictly above `xᶜ` in
both goods is in its lower contour set. -/
theorem example_23_BB_1_lowerContour (i : Fin 2) :
    lowerContour (Θ := fun _ : Fin 2 => Bool) mrU i mrXC true ⊆
      lowerContour (Θ := fun _ : Fin 2 => Bool) mrU i mrXC false := by
  intro p hp
  have hp' : mrU i p true ≤ mrU i mrXC true := hp
  change mrU i p false ≤ mrU i mrXC false
  obtain ⟨⟨a, b⟩, ha0, ha1, hb0, hb1⟩ := p
  fin_cases i
  · simp only [mrU, mrXC, ite_true, Fin.zero_eta, Fin.isValue] at hp' ⊢
    rw [min_self]
    by_contra h
    have h1 : 5 < a := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
    have h2 : 5 < b := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
    nlinarith
  · simp only [mrU, mrXC, Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, ite_true] at hp' ⊢
    rw [show min ((10 : ℝ) - 5) (10 - 5) = 5 by norm_num]
    by_contra h
    have h1 : 5 < 10 - a := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
    have h2 : 5 < 10 - b := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
    nlinarith

/-- **Example 23.BB.1** (MWG, p. 916). `f` is not monotonic: the lower contour sets of
`xᶜ = f(θᶜ)` expand from `θᶜ = (θ₁ᶜ, θ₂ᶜ)` to `θᴸ = (θ₁ᴸ, θ₂ᴸ)`, but `f(θᴸ) = xᴸ ≠ xᶜ`. -/
theorem example_23_BB_1_not_monotonic :
    ¬MonotonicSCF (Θ := fun _ : Fin 2 => Bool) mrU mrF := by
  intro hM
  have h := hM (fun _ => true) (fun _ => false) fun i => example_23_BB_1_lowerContour i
  exact mrXL_ne_mrXC h

/-- **Example 23.BB.1** (MWG, p. 916). By Proposition 23.BB.1, no mechanism strongly implements
`f` in Nash equilibrium. -/
theorem example_23_BB_1_not_strongly {S : Fin 2 → Type*} (Γ : Mechanism S MRBox) :
    ¬StronglyImplementsInNash (Θ := fun _ : Fin 2 => Bool) mrU Γ mrF :=
  fun h => example_23_BB_1_not_monotonic (proposition_23_BB_1 h)

/-- **Example 23.BB.1** (MWG, p. 916). Stage 3: consumer 1 chooses `y` (`true`) or `z`
(`false`). -/
def mrStage3 (c3 : Bool) : MRBox := if c3 then mrY else mrZ

/-- **Example 23.BB.1** (MWG, p. 916). Stage 2: consumer 2 agrees (`true`, outcome `xᶜ`) or
challenges (`false`, go to stage 3, where consumer 1 plays `c3`). -/
def mrStage2 (ag c3 : Bool) : MRBox := if ag then mrXC else mrStage3 c3

/-- **Example 23.BB.1** (MWG, p. 916) and **Exercise 23.BB.1(a)** (MWG, p. 925). The outcome
function of the normal form: consumer 1's strategy is `(a₁, c₃)` (stage 1: announce "C"
(`true`) or "L" (`false`, outcome `xᴸ`); stage 3 choice), consumer 2's strategy is his stage-2
action. -/
def mrOutcome (s1 : Bool × Bool) (ag : Bool) : MRBox := if s1.1 then mrStage2 ag s1.2 else mrXL

/-- **Example 23.BB.1** (MWG, p. 916). Subgame perfect Nash equilibrium of the three-stage game of
perfect information at the profile `θ`: consumer 1's stage-3 choice is optimal, consumer 2's
stage-2 action is optimal given it, and consumer 1's stage-1 announcement is optimal given
both (optimality at every decision node, i.e. backward induction). -/
def IsMRSubgamePerfect (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) : Prop :=
  (∀ c, mrU 0 (mrStage3 c) (θ 0) ≤ mrU 0 (mrStage3 s1.2) (θ 0)) ∧
    (∀ g, mrU 1 (mrStage2 g s1.2) (θ 1) ≤ mrU 1 (mrStage2 ag s1.2) (θ 1)) ∧
    (∀ a, mrU 0 (mrOutcome (a, s1.2) ag) (θ 0) ≤ mrU 0 (mrOutcome s1 ag) (θ 0))

/-- **Exercise 23.BB.1(a)** (MWG, p. 925). Nash equilibrium of the normal form at `θ`. -/
def IsMRNash (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) : Prop :=
  (∀ s1', mrU 0 (mrOutcome s1' ag) (θ 0) ≤ mrU 0 (mrOutcome s1 ag) (θ 0)) ∧
    (∀ g, mrU 1 (mrOutcome s1 g) (θ 1) ≤ mrU 1 (mrOutcome s1 ag) (θ 1))

/-- **Exercise 23.BB.1(b)** (MWG, p. 925). For every profile the subgame perfect equilibrium is:
consumer 1 announces his type truthfully ("C" iff `θ₁ = θ₁ᶜ`) and at stage 3 picks `z` if
Cobb-Douglas, `y` if Leontief; consumer 2 agrees iff `θ₁ = θ₁ᶜ`. -/
theorem exercise_23_BB_1b (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) :
    IsMRSubgamePerfect θ s1 ag ↔ s1 = (θ 0, !θ 0) ∧ ag = θ 0 := by
  obtain ⟨a, c⟩ := s1
  cases h0 : θ 0 <;> cases h1 : θ 1 <;> cases a <;> cases c <;> cases ag <;>
    norm_num [IsMRSubgamePerfect, mrOutcome, mrStage2, mrStage3, Bool.forall_bool, h0, h1, mrU,
      mrXC, mrXL, mrY, mrZ, min_def]

/-- **Example 23.BB.1** (MWG, p. 916). For each profile `θ` the three-stage mechanism has a unique
subgame perfect Nash equilibrium, and it results in `f(θ)`: `f` is strongly implemented in
subgame perfect equilibrium. -/
theorem example_23_BB_1 (θ : Fin 2 → Bool) :
    (∃! s : (Bool × Bool) × Bool, IsMRSubgamePerfect θ s.1 s.2) ∧
      ∀ s1 ag, IsMRSubgamePerfect θ s1 ag → mrOutcome s1 ag = mrF θ := by
  refine ⟨⟨((θ 0, !θ 0), θ 0), (exercise_23_BB_1b θ _ _).2 ⟨rfl, rfl⟩, fun s hs => ?_⟩,
    fun s1 ag hs => ?_⟩
  · obtain ⟨h1, h2⟩ := (exercise_23_BB_1b θ s.1 s.2).1 hs
    exact Prod.ext h1 h2
  · obtain ⟨rfl, rfl⟩ := (exercise_23_BB_1b θ s1 ag).1 hs
    cases h0 : θ 0 <;> simp [mrOutcome, mrStage2, mrF, h0]

/-- **Exercise 23.BB.1(a)** (MWG, p. 925). The pure Nash equilibria of the normal form. If
`θ₁ = θ₁ᶜ` the only one is ((C, z), agree), with outcome `xᶜ`. If `θ₁ = θ₁ᴸ` they are
((L, y), challenge), ((L, z), challenge) (outcome `xᴸ`) and ((C, z), agree) (outcome `xᶜ`).
Consumer 2's type does not matter. -/
theorem exercise_23_BB_1a (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool) :
    IsMRNash θ s1 ag ↔
      (s1 = (true, false) ∧ ag = true) ∨ (θ 0 = false ∧ s1.1 = false ∧ ag = false) := by
  obtain ⟨a, c⟩ := s1
  cases h0 : θ 0 <;> cases h1 : θ 1 <;> cases a <;> cases c <;> cases ag <;>
    norm_num [IsMRNash, mrOutcome, mrStage2, mrStage3, Bool.forall_bool, Prod.forall, h0, h1,
      mrU, mrXC, mrXL, mrY, mrZ, min_def]

/-- **Exercise 23.BB.1(a)** (MWG, p. 925). With `θ₁ = θ₁ᴸ`, ((C, z), agree) is a Nash equilibrium
of the normal form with outcome `xᶜ ≠ f(θ)`: the mechanism does not strongly implement `f` in
Nash equilibrium (consumer 2's threat to challenge is not credible). -/
theorem exercise_23_BB_1a_not_strongly (θ : Fin 2 → Bool) (h0 : θ 0 = false) :
    IsMRNash θ (true, false) true ∧ mrOutcome (true, false) true ≠ mrF θ := by
  refine ⟨(exercise_23_BB_1a θ _ _).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
  simp only [mrOutcome, mrStage2, mrF, h0, ite_true]
  exact fun h => mrXL_ne_mrXC (by simpa using h.symm)

/-- **Exercise 23.BB.1** (MWG, p. 925). Every subgame perfect equilibrium is a Nash equilibrium of
the normal form. -/
theorem exercise_23_BB_1_spe_nash (θ : Fin 2 → Bool) (s1 : Bool × Bool) (ag : Bool)
    (h : IsMRSubgamePerfect θ s1 ag) : IsMRNash θ s1 ag := by
  obtain ⟨rfl, rfl⟩ := (exercise_23_BB_1b θ s1 ag).1 h
  rw [exercise_23_BB_1a]
  cases θ 0 <;> simp

end MWG.MechanismDesign
