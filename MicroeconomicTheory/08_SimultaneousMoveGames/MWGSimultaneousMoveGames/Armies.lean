/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Bayesian

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
