/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Refinements
import Mathlib.Tactic.FinCases

/-!
# Example 13.AA.1: the intuitive criterion versus reasonable beliefs with three types

MWG, Appendix A, pp. 471-472.

Three types `θ₁, θ₂, θ₃` (`Fin 3`), equally likely; player 1 chooses `false` (the equilibrium
action) or `true` (the deviation `â`); one responder chooses `s ∈ ℝ` with payoff
`-(s - g(θ))²`, `g = (-2, 1, 0)`, so after `â` her unique best response to a belief `μ` is
`s = μ(θ₂) - 2μ(θ₁)`. Player 1 gets `0` from `false`; from `â`, type `θ₁` gets `-1`, type `θ₂`
gets `1` if `s ≥ 1/4` (else `-1`) and type `θ₃` gets `1` if `0 ≤ s ≤ 3/4` (else `-1`). For
beliefs concentrated on `{θ₂, θ₃}`, `s = μ(θ₂|â)`: type `θ₂` strictly prefers to deviate iff
`μ(θ₂|â) ≥ 1/4` and type `θ₃` iff `μ(θ₂|â) ≤ 3/4`, as in the book.

* `example_13_AA_1_pbe`: everybody choosing `false`, with belief `θ₁` after `â`, is a PBE;
* `example_13_AA_1_eqdom`: `Θ**(â) = {θ₂, θ₃}`;
* `example_13_AA_1_ic`: this PBE passes the intuitive criterion;
* `example_13_AA_1_no_reasonable`: no PBE with this outcome has reasonable beliefs.
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset SignalingGame

/-- The responder's target `g(θ)`. -/
def exG : Fin 3 → ℝ := ![-2, 1, 0]

/-- **Example 13.AA.1** (MWG, p. 472). The signaling game. -/
noncomputable def exGame : SignalingGame (Fin 3) Bool Unit (fun _ => ℝ) where
  u1 a s θ := if a then
      (if θ = 0 then -1 else if θ = 1 then (if 1 / 4 ≤ s () then 1 else -1)
        else (if 0 ≤ s () ∧ s () ≤ 3 / 4 then 1 else -1))
    else 0
  u _ _ s θ := -(s () - exG θ) ^ 2

/-- The uniform prior. -/
noncomputable def exPrior : Fin 3 → ℝ := fun _ => 1 / 3

/-- The responder's expected payoff is `-(s - m)²` plus a constant, `m = Σ μ(θ) g(θ)`. -/
theorem exGame_payoff (a : Bool) (μ : Fin 3 → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    (exGame.responseGame a μ).payoff () s =
      -(s () - ∑ θ, μ θ * exG θ) ^ 2 + ((∑ θ, μ θ * exG θ) ^ 2 - ∑ θ, μ θ * exG θ ^ 2) := by
  simp only [SignalingGame.responseGame, exGame, Fin.sum_univ_three] at hμ ⊢
  have : μ 2 = 1 - μ 0 - μ 1 := by linarith
  rw [this]; ring

/-- After any action, the responder's unique equilibrium response to `μ` is `Σ μ(θ) g(θ)`. -/
theorem exGame_nash_iff (a : Bool) (μ : Fin 3 → ℝ) (hμ : ∑ θ, μ θ = 1) (s : Unit → ℝ) :
    IsNashEquilibrium (exGame.responseGame a μ) s ↔ s () = ∑ θ, μ θ * exG θ := by
  constructor
  · intro h
    have := h () (∑ θ, μ θ * exG θ)
    rw [exGame_payoff a μ hμ, exGame_payoff a μ hμ, Function.update_self, sub_self] at this
    nlinarith [sq_nonneg (s () - ∑ θ, μ θ * exG θ)]
  · intro h i t
    rw [exGame_payoff a μ hμ, exGame_payoff a μ hμ, h]
    nlinarith [sq_nonneg (Function.update s i t () - ∑ θ, μ θ * exG θ)]

/-- The point mass on `θ`. -/
def pointMass (θ : Fin 3) : Fin 3 → ℝ := fun θ' => if θ' = θ then 1 else 0

theorem pointMass_belief (θ : Fin 3) (T : Set (Fin 3)) (hθ : θ ∈ T) :
    IsBeliefOn T (pointMass θ) := by
  refine ⟨fun θ' => by unfold pointMass; split_ifs <;> norm_num, ?_, fun θ' h => ?_⟩
  · simp [pointMass]
  · unfold pointMass at h; split_ifs at h with he
    · rw [he]; exact hθ
    · norm_num at h

theorem pointMass_resp (θ : Fin 3) : ∑ θ', pointMass θ θ' * exG θ' = exG θ := by
  simp [pointMass]

/-- The equilibrium responses to `â` for beliefs concentrated on `T`. -/
theorem exGame_eqResponses (T : Set (Fin 3)) (a : Bool) (s : Unit → ℝ) :
    s ∈ exGame.eqResponses T a ↔ ∃ μ, IsBeliefOn T μ ∧ s () = ∑ θ, μ θ * exG θ := by
  constructor
  · rintro ⟨μ, hμ, hne⟩; exact ⟨μ, hμ, (exGame_nash_iff a μ hμ.2.1 s).1 hne⟩
  · rintro ⟨μ, hμ, hs⟩; exact ⟨μ, hμ, (exGame_nash_iff a μ hμ.2.1 s).2 hs⟩

/-- **Example 13.AA.1** (MWG, p. 472). With equilibrium payoffs `0`, `â` is equilibrium dominated
for `θ₁` only: `Θ**(â) = {θ₂, θ₃}`. -/
theorem example_13_AA_1_eqdom :
    exGame.typesNotEqDominated (fun _ => 0) true = {1, 2} := by
  ext θ
  simp only [SignalingGame.typesNotEqDominated, SignalingGame.EqDominated, Set.mem_ofPred_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases θ
  · simp only [exGame]; norm_num
  · simp only [exGame]
    norm_num
    refine ⟨fun _ => 1, (exGame_eqResponses _ _ _).2 ⟨pointMass 1, pointMass_belief 1 _ trivial,
      by rw [pointMass_resp]; simp [exG]⟩, by norm_num⟩
  · simp only [exGame]
    norm_num
    refine ⟨fun _ => 0, (exGame_eqResponses _ _ _).2 ⟨pointMass 2, pointMass_belief 2 _ trivial,
      by rw [pointMass_resp]; simp [exG]⟩, by norm_num⟩

/-- The responses of the PBE: `-2` after `â` (belief `θ₁`), `-1/3` after `false` (prior). -/
noncomputable def exResp (a : Bool) : Unit → ℝ := if a then fun _ => -2 else fun _ => -1 / 3

/-- The beliefs of the PBE. -/
noncomputable def exBelief (a : Bool) : Fin 3 → ℝ := if a then pointMass 0 else exPrior

theorem exPrior_belief : IsBeliefOn Set.univ exPrior :=
  ⟨fun _ => by norm_num [exPrior], by simp [exPrior],
    fun _ _ => trivial⟩

/-- The equilibrium payoffs are `0` whenever everybody plays `false`. -/
theorem exGame_eqPayoff (sS : Bool → Unit → ℝ) :
    exGame.eqPayoff (fun _ => false) sS = fun _ => 0 := by
  funext θ; simp [SignalingGame.eqPayoff, exGame]

/-- **Example 13.AA.1** (MWG, p. 472). All types choosing `false`, with belief `θ₁` after `â`, is
a PBE. -/
theorem example_13_AA_1_pbe : exGame.IsPBE exPrior (fun _ => false) exResp exBelief := by
  refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ?_⟩
  · cases a
    · exact le_rfl
    · fin_cases θ <;> simp [exGame, exResp] <;> norm_num
  · obtain ⟨_, h⟩ := ha
    subst h
    simp [exBelief, exPrior]
  · cases a
    · refine ⟨exPrior_belief, (exGame_nash_iff _ _ exPrior_belief.2.1 _).2 ?_⟩
      simp [exResp, exPrior, exG, Fin.sum_univ_three]; norm_num
    · refine ⟨pointMass_belief 0 _ trivial,
        (exGame_nash_iff _ _ (pointMass_belief 0 Set.univ trivial).2.1 _).2 ?_⟩
      simp only [exResp, ite_true]
      rw [pointMass_resp]; simp [exG]

/-- **Example 13.AA.1** (MWG, p. 472). This PBE does not violate the intuitive criterion: for
every type and deviation some equilibrium response to beliefs on `Θ**(â) = {θ₂, θ₃}` leaves the
type no better off. -/
theorem example_13_AA_1_ic :
    ¬ exGame.ViolatesIC (exGame.eqPayoff (fun _ => false) exResp) := by
  rw [exGame_eqPayoff]
  rintro ⟨θ, a, hv⟩
  have hict : exGame.icTypes (fun _ => 0) true = {1, 2} := by
    simp [icTypes, example_13_AA_1_eqdom]
  have hresp0 : (fun _ => -1 / 3 : Unit → ℝ) ∈ exGame.eqResponses Set.univ false :=
    (exGame_eqResponses _ _ _).2 ⟨exPrior, exPrior_belief, by
      simp [exPrior, exG, Fin.sum_univ_three]; norm_num⟩
  have hict0 : exGame.icTypes (fun _ => 0) false = Set.univ := by
    have : exGame.typesNotEqDominated (fun _ => 0) false = Set.univ := by
      ext θ
      simp only [typesNotEqDominated, EqDominated, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro hall
      have := hall _ hresp0
      simp [exGame] at this
    simp [icTypes, this]
  cases a
  · rw [hict0] at hv
    have := hv _ hresp0
    simp [exGame] at this
  · rw [hict] at hv
    fin_cases θ
    · have := hv (fun _ => 1) ((exGame_eqResponses _ _ _).2 ⟨pointMass 1,
        pointMass_belief 1 _ (by simp), by rw [pointMass_resp]; simp [exG]⟩)
      simp [exGame] at this; norm_num at this
    · have := hv (fun _ => 0) ((exGame_eqResponses _ _ _).2 ⟨pointMass 2,
        pointMass_belief 2 _ (by simp), by rw [pointMass_resp]; simp [exG]⟩)
      simp [exGame] at this; norm_num at this
    · have := hv (fun _ => 1) ((exGame_eqResponses _ _ _).2 ⟨pointMass 1,
        pointMass_belief 1 _ (by simp), by rw [pointMass_resp]; simp [exG]⟩)
      simp [exGame] at this; norm_num at this

/-- **Example 13.AA.1** (MWG, p. 472). No PBE in which every type chooses `false` has beliefs that
are reasonable relative to `Θ**`: after `â`, either `θ₂` or `θ₃` would deviate. -/
theorem example_13_AA_1_no_reasonable (sS : Bool → Unit → ℝ) (μ : Bool → Fin 3 → ℝ)
    (h : exGame.IsPBE exPrior (fun _ => false) sS μ)
    (hr : ReasonableBeliefs (exGame.typesNotEqDominated (exGame.eqPayoff (fun _ => false) sS))
      μ) : False := by
  rw [exGame_eqPayoff] at hr
  have hr' := hr true (by rw [example_13_AA_1_eqdom]; exact ⟨1, by simp⟩)
  rw [example_13_AA_1_eqdom] at hr'
  obtain ⟨⟨h0, h1, -⟩, hne⟩ := h.2.2 true
  have hμ0 : μ true 0 = 0 := by
    by_contra hne0
    have := hr' 0 (lt_of_le_of_ne (h0 0) (Ne.symm hne0))
    simp at this
  have hs := (exGame_nash_iff true _ h1 _).1 hne
  simp only [Fin.sum_univ_three, exG, hμ0] at hs h1
  norm_num at hs
  have hμ1 : μ true 1 ≤ 1 := by linarith [h0 2]
  have hdev1 := h.1 1 true
  have hdev2 := h.1 2 true
  have e1 : exGame.u1 true (sS true) 1 = if 1 / 4 ≤ μ true 1 then 1 else -1 := by
    simp [exGame, hs]
  have e2 : exGame.u1 true (sS true) 2 =
      if 0 ≤ μ true 1 ∧ μ true 1 ≤ 3 / 4 then 1 else -1 := by
    simp [exGame, hs]
  have z1 : exGame.u1 false (sS false) 1 = 0 := by simp [exGame]
  have z2 : exGame.u1 false (sS false) 2 = 0 := by simp [exGame]
  rw [e1, z1] at hdev1
  rw [e2, z2] at hdev2
  by_cases hq : 1 / 4 ≤ μ true 1
  · simp only [hq, ↓reduceIte] at hdev1; norm_num at hdev1
  · have : 0 ≤ μ true 1 ∧ μ true 1 ≤ 3 / 4 := ⟨h0 1, by linarith⟩
    simp only [this, and_self, ↓reduceIte] at hdev2; norm_num at hdev2

end MWG.AdverseSelection
