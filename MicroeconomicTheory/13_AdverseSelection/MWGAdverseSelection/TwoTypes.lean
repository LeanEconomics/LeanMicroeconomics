/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Refinements

/-!
# Two types: the intuitive criterion and reasonable beliefs, an instance

MWG, Appendix A, p. 472.

A concrete two-type signaling game satisfying the hypotheses of `two_types_reasonable`. Types
`false` (low) and `true` (high), equally likely; player 1 chooses `false` (the equilibrium
action) or `true` (the deviation); one responder chooses `s ∈ ℝ` with payoff `-(s - g(θ))²`,
`g(θ_L) = 0`, `g(θ_H) = 1`, so her unique best response to a belief `μ` is `s = μ(θ_H)`. Player 1
gets `0` from `false`; from `true` the low type gets `-1` and the high type `s - 1`.

* `twoTypes_instance`: pooling on `false` with the belief "low type" after `true` (response
  `0`) is a PBE; it passes the intuitive criterion; `Θ**(true) = {θ_H}`; its off-path belief is
  not reasonable; and `two_types_reasonable` turns it into a PBE with the reasonable belief and
  the same outcome.
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset SignalingGame

/-- The responder's target `g(θ)`. -/
def twoG (θ : Bool) : ℝ := if θ then 1 else 0

/-- **Appendix A** (MWG, p. 472). A two-type signaling game. -/
noncomputable def twoGame : SignalingGame Bool Bool Unit (fun _ => ℝ) where
  u1 a s θ := if a then (if θ then s () - 1 else -1) else 0
  u _ _ s θ := -(s () - twoG θ) ^ 2

/-- The responder's expected payoff is `-(s - μ(θ_H))²` plus a constant. -/
theorem twoGame_payoff (a : Bool) (μ : Bool → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    (twoGame.responseGame a μ).payoff () s = -(s () - μ true) ^ 2 + (μ true ^ 2 - μ true) := by
  simp only [SignalingGame.responseGame, twoGame, Fintype.sum_bool, twoG] at hμ ⊢
  simp only [Bool.false_eq_true, ↓reduceIte]
  have : μ false = 1 - μ true := by linarith
  rw [this]; ring

/-- The responder's unique equilibrium response to `μ` is `μ(θ_H)`. -/
theorem twoGame_nash_iff (a : Bool) (μ : Bool → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    IsNashEquilibrium (twoGame.responseGame a μ) s ↔ s () = μ true := by
  constructor
  · intro h
    have := h () (μ true)
    rw [twoGame_payoff a μ hμ, twoGame_payoff a μ hμ, Function.update_self, sub_self] at this
    nlinarith [sq_nonneg (s () - μ true)]
  · intro h i t
    rw [twoGame_payoff a μ hμ, twoGame_payoff a μ hμ, h]
    nlinarith [sq_nonneg (Function.update s i t () - μ true)]

/-- The point mass on `b`. -/
def boolPoint (b : Bool) : Bool → ℝ := fun θ => if θ = b then 1 else 0

theorem boolPoint_belief (b : Bool) (T : Set Bool) (hb : b ∈ T) : IsBeliefOn T (boolPoint b) := by
  refine ⟨fun θ => by unfold boolPoint; split_ifs <;> norm_num, ?_, fun θ h => ?_⟩
  · cases b <;> simp [boolPoint]
  · unfold boolPoint at h; split_ifs at h with he
    · rw [he]; exact hb
    · norm_num at h

/-- The response `s = 1` to the belief "high type" is an equilibrium response, for beliefs
concentrated on any `T ∋ θ_H`. -/
theorem twoGame_one_mem (T : Set Bool) (hT : true ∈ T) (a : Bool) :
    (fun _ => (1 : ℝ)) ∈ twoGame.eqResponses T a :=
  ⟨boolPoint true, boolPoint_belief true T hT,
    (twoGame_nash_iff a _ (boolPoint_belief true T hT).2.1 _).2 (by simp [boolPoint])⟩

/-- The responses of the PBE: `0` after `true` (belief: low type), `1/2` after `false`. -/
noncomputable def twoResp (a : Bool) : Unit → ℝ := if a then fun _ => 0 else fun _ => 1 / 2

/-- The beliefs of the PBE. -/
noncomputable def twoBelief (a : Bool) : Bool → ℝ := if a then boolPoint false else fun _ => 1 / 2

/-- **Appendix A** (MWG, p. 472). Two types: an instance of the hypotheses of
`two_types_reasonable`, and its conclusion. -/
theorem twoTypes_instance :
    twoGame.IsPBE (fun _ => 1 / 2) (fun _ => false) twoResp twoBelief ∧
      ¬ twoGame.ViolatesIC (twoGame.eqPayoff (fun _ => false) twoResp) ∧
      twoGame.typesNotEqDominated (twoGame.eqPayoff (fun _ => false) twoResp) true = {true} ∧
      ¬ ReasonableBeliefs (twoGame.typesNotEqDominated
        (twoGame.eqPayoff (fun _ => false) twoResp)) twoBelief ∧
      ∃ s ν, IsBeliefOn {true} ν ∧ twoGame.IsPBE (fun _ => 1 / 2) (fun _ => false)
        (Function.update twoResp true s) (Function.update twoBelief true ν) := by
  have hpay : twoGame.eqPayoff (fun _ => false) twoResp = fun _ => 0 := by
    funext θ; simp [SignalingGame.eqPayoff, twoGame]
  have hhalf : IsBeliefOn Set.univ (fun _ : Bool => (1 : ℝ) / 2) :=
    ⟨fun _ => by norm_num, by norm_num, fun _ _ => trivial⟩
  have hpbe : twoGame.IsPBE (fun _ => 1 / 2) (fun _ => false) twoResp twoBelief := by
    refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ?_⟩
    · cases a <;> cases θ <;> simp [twoGame, twoResp]
    · obtain ⟨θ', hθ'⟩ := ha
      subst hθ'
      simp [twoBelief]
    · cases a
      · refine ⟨hhalf, (twoGame_nash_iff false _ hhalf.2.1 _).2 ?_⟩
        simp [twoResp]
      · have hb := boolPoint_belief false Set.univ trivial
        refine ⟨hb, (twoGame_nash_iff true _ hb.2.1 _).2 ?_⟩
        simp [twoResp, boolPoint]
  have hnd : ∀ a, true ∈ twoGame.typesNotEqDominated (fun _ => 0) a := by
    intro a hdom
    have := hdom _ (twoGame_one_mem Set.univ trivial a)
    cases a <;> simp [twoGame] at this
  have heq : twoGame.typesNotEqDominated (twoGame.eqPayoff (fun _ => false) twoResp) true =
      {true} := by
    rw [hpay]
    ext θ
    cases θ
    · simp only [Set.mem_singleton_iff, Bool.false_eq_true, iff_false]
      intro hnot
      apply hnot
      intro s _
      simp [twoGame]
    · simp only [Set.mem_singleton_iff, iff_true]
      exact hnd true
  have hIC : ¬ twoGame.ViolatesIC (twoGame.eqPayoff (fun _ => false) twoResp) := by
    rw [hpay]
    rintro ⟨θ, a, hv⟩
    have hmem : true ∈ twoGame.icTypes (fun _ => 0) a := by
      unfold icTypes
      split_ifs
      · exact hnd a
      · trivial
    have := hv _ (twoGame_one_mem _ hmem a)
    cases a <;> cases θ <;> norm_num [twoGame] at this
  have hoff : ∀ θ : Bool, (fun _ : Bool => false) θ ≠ true := fun _ => Bool.false_ne_true
  refine ⟨hpbe, hIC, heq, fun hr => ?_, two_types_reasonable hpbe hIC hoff heq⟩
  have := hr true (by rw [heq]; exact ⟨true, rfl⟩) false (by simp [twoBelief, boolPoint])
  rw [heq] at this
  exact Bool.false_ne_true this

end MWG.AdverseSelection
