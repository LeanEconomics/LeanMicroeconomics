/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ExampleAA1
import MWGAdverseSelection.Signaling
import Mathlib.Tactic.LinearCombination

/-!
# Exercise 13.AA.1: three types, several PBE satisfying the intuitive criterion

MWG, Exercise 13.AA.1, p. 476 (Appendix A, pp. 467-472).

The education signaling model of Section 13.C with three equally likely types (`Fin 3`) of
productivity `θ = (1, 2, 10)`, `r(θ) = 0`, and education cost `c(e, θ) = k_θ e` with
`k = (1, 1/2, 1/4)` (single crossing). It is the `SignalingGame` `aaGame` of Appendix A: the
worker chooses `e ≥ 0` (`NNReal`); two firms observe `e` and bid wages; the worker accepts the
highest bid if it is nonnegative (ties split); a firm's payoff is its share of `θ - w`. The firms'
response game after `e` with belief `μ` is the wage game of Section 13.B with expected
productivity `E_μ[θ]` (`aa_payoff`), so its Nash equilibria are both firms bidding `E_μ[θ]`
(`aa_nash_iff`).

* `aa_pbe1`: the separating (Riley) PBE: education `(0, 1, 17)`, wages `(1, 2, 10)`, payoffs
  `(1, 3/2, 23/4)`;
* `aa_pbe2`: a partially pooling PBE: types 1 and 2 choose `e = 0` (wage `3/2`), type 3
  chooses `17`; payoffs `(3/2, 3/2, 23/4)`;
* `aa_passes_ic`: both satisfy the intuitive criterion (13.AA.4);
* `exercise_13_AA_1`: the two PBE have different outcomes, so more than one PBE satisfies the
  intuitive criterion.
-/

namespace MWG.AdverseSelection

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Finset SignalingGame

/-- Productivities `θ = (1, 2, 10)`. -/
def aaθ : Fin 3 → ℝ := ![1, 2, 10]

/-- Marginal education costs `k_θ = (1, 1/2, 1/4)`. -/
noncomputable def aaK : Fin 3 → ℝ := ![1, 1 / 2, 1 / 4]

/-- **Exercise 13.AA.1** (MWG, p. 476). The three-type education signaling game. -/
noncomputable def aaGame : SignalingGame (Fin 3) NNReal (Fin 2) (fun _ => ℝ) where
  u1 e w θ := max (max (w 0) (w 1)) 0 - aaK θ * e
  u j _ w θ := wageShare (w j) (w (1 - j)) (if 0 ≤ w j then aaθ θ - w j else 0)

/-- A two-type model used only for its home earnings `r = 0` in the Bertrand lemmas. -/
noncomputable def aaM0 : SigModel where
  θL := 1
  θH := 2
  lam := 1 / 2
  r := 0
  c := fun _ _ => 0

/-- Expected productivity under the belief `μ`. -/
noncomputable def aaMean (μ : Fin 3 → ℝ) : ℝ := ∑ θ, μ θ * aaθ θ

/-- The firms' response game after any education level is the wage game with expected
productivity `E_μ[θ]`. -/
theorem aa_payoff (a : NNReal) (μ : Fin 3 → ℝ) (hμ : ∑ θ, μ θ = 1) (j : Fin 2) (w : Fin 2 → ℝ) :
    (aaGame.responseGame a μ).payoff j w =
      (wageGame (aaM0.offerProfit (aaMean μ))).payoff j w := by
  simp only [SignalingGame.responseGame, aaGame, wageGame, SigModel.offerProfit, aaM0, aaMean,
    wageShare, Fin.sum_univ_three] at hμ ⊢
  split_ifs
  all_goals first
    | ring1
    | linear_combination (-(w j)) * hμ
    | linear_combination (-(w j) / 2) * hμ

theorem aaMean_ge (μ : Fin 3 → ℝ) (hμ : IsBeliefOn Set.univ μ) : 1 ≤ aaMean μ := by
  obtain ⟨h0, h1, -⟩ := hμ
  simp only [aaMean, aaθ, Fin.sum_univ_three] at h1 ⊢
  simp
  nlinarith [h0 0, h0 1, h0 2]

theorem aaMean_le (μ : Fin 3 → ℝ) (hμ : IsBeliefOn Set.univ μ) : aaMean μ ≤ 10 := by
  obtain ⟨h0, h1, -⟩ := hμ
  simp only [aaMean, aaθ, Fin.sum_univ_three] at h1 ⊢
  simp
  nlinarith [h0 0, h0 1, h0 2]

theorem aa_belief_univ {T : Set (Fin 3)} {μ : Fin 3 → ℝ} (h : IsBeliefOn T μ) :
    IsBeliefOn Set.univ μ := ⟨h.1, h.2.1, fun _ _ => trivial⟩

/-- **Exercise 13.AA.1**. After education `a` with belief `μ`, the firms' Nash equilibria are both
bidding `E_μ[θ]` (Section 13.C, p. 452). -/
theorem aa_nash_iff (a : NNReal) (μ : Fin 3 → ℝ) (hμ : IsBeliefOn Set.univ μ) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (aaGame.responseGame a μ) w ↔ w 0 = aaMean μ ∧ w 1 = aaMean μ := by
  have hp := aaMean_ge μ hμ
  have heq : IsNashEquilibrium (aaGame.responseGame a μ) w ↔
      IsNashEquilibrium (wageGame (aaM0.offerProfit (aaMean μ))) w := by
    unfold IsNashEquilibrium
    simp only [aa_payoff a μ hμ.2.1]
  rw [heq, aaM0.bertrand_iff (by linarith) w]
  have hr : aaM0.r = 0 := rfl
  constructor
  · rintro ⟨h1, -, -⟩; exact h1 (by rw [hr]; linarith)
  · rintro ⟨h1, h2⟩
    refine ⟨fun _ => ⟨h1, h2⟩, fun h => ?_, fun h => ?_⟩ <;> rw [hr] at h <;> linarith

theorem aa_eqResponses (T : Set (Fin 3)) (a : NNReal) (w : Fin 2 → ℝ) :
    w ∈ aaGame.eqResponses T a ↔ ∃ μ, IsBeliefOn T μ ∧ w 0 = aaMean μ ∧ w 1 = aaMean μ := by
  constructor
  · rintro ⟨μ, hμ, hne⟩; exact ⟨μ, hμ, (aa_nash_iff a μ (aa_belief_univ hμ) w).1 hne⟩
  · rintro ⟨μ, hμ, hw⟩; exact ⟨μ, hμ, (aa_nash_iff a μ (aa_belief_univ hμ) w).2 hw⟩

theorem aa_u1 (a : NNReal) (m : ℝ) (hm : 0 ≤ m) (θ : Fin 3) :
    aaGame.u1 a (fun _ => m) θ = m - aaK θ * a := by
  simp [aaGame, hm]

theorem aaMean_pointMass (τ : Fin 3) : aaMean (pointMass τ) = aaθ τ := by
  simp [aaMean, pointMass]

/-- The wage bid `θ_τ` is an equilibrium response for beliefs concentrated on `T ∋ τ`. -/
theorem aa_resp_mem {T : Set (Fin 3)} {τ : Fin 3} (hτ : τ ∈ T) (a : NNReal) :
    (fun _ => aaθ τ) ∈ aaGame.eqResponses T a :=
  (aa_eqResponses T a _).2 ⟨pointMass τ, pointMass_belief τ T hτ, by rw [aaMean_pointMass],
    by rw [aaMean_pointMass]⟩

/-- Every equilibrium response gives type `θ` at most `10 - k_θ a`. -/
theorem aa_u1_le {T : Set (Fin 3)} {a : NNReal} {w : Fin 2 → ℝ} (hw : w ∈ aaGame.eqResponses T a)
    (θ : Fin 3) : aaGame.u1 a w θ ≤ 10 - aaK θ * a := by
  obtain ⟨μ, hμ, h0, h1⟩ := (aa_eqResponses T a w).1 hw
  have hge := aaMean_ge μ (aa_belief_univ hμ)
  have hle := aaMean_le μ (aa_belief_univ hμ)
  have : w = fun _ => aaMean μ := funext fun j => by fin_cases j <;> simp [h0, h1]
  rw [this, aa_u1 a _ (by linarith)]
  linarith

/-- **(13.AA.4)** for this game: a PBE with equilibrium payoffs `u* = (u₁, 3/2, 23/4)`,
`1 ≤ u₁ ≤ 3/2`, does not violate the intuitive criterion. For a deviation `e`, the beliefs
concentrated on the lowest type in `Θ**(e)` (or on type 1 if `Θ**(e)` is empty) produce a wage
that gives no type more than its equilibrium payoff. -/
theorem aa_passes_ic (uS : Fin 3 → ℝ) (h0 : 1 ≤ uS 0) (h0' : uS 0 ≤ 3 / 2) (h1 : uS 1 = 3 / 2)
    (h2 : uS 2 = 23 / 4) : ¬ aaGame.ViolatesIC uS := by
  rintro ⟨θ, a, hv⟩
  have ha : (0 : ℝ) ≤ a := a.2
  have hK : ∀ θ', 0 ≤ aaK θ' * a := fun θ' => by
    fin_cases θ' <;> simp [aaK]
  have hus : ∀ θ', 1 ≤ uS θ' := fun θ' => by
    fin_cases θ'
    · exact h0
    · simp [h1]; norm_num
    · simp [h2]; norm_num
  -- membership in `icTypes`
  have hic : ∀ τ, τ ∈ aaGame.typesNotEqDominated uS a → τ ∈ aaGame.icTypes uS a := by
    intro τ hτ
    have hne : (aaGame.typesNotEqDominated uS a).Nonempty := ⟨τ, hτ⟩
    simp only [icTypes, hne, ↓reduceIte]
    exact hτ
  have hmem10 : ∀ τ, uS τ ≤ 10 - aaK τ * a → τ ∈ aaGame.typesNotEqDominated uS a := by
    intro τ hle hdom
    have := hdom _ (aa_resp_mem (τ := 2) (Set.mem_univ _) a)
    rw [aa_u1 a _ (by simp [aaθ])] at this
    simp only [aaθ] at this
    simp at this
    linarith
  -- the deviation fails against the response `θ_τ`
  have key : ∀ τ, τ ∈ aaGame.icTypes uS a → aaθ τ - aaK θ * a ≤ uS θ → False := by
    intro τ hτ hle
    have := hv _ (aa_resp_mem hτ a)
    rw [aa_u1 a _ (by fin_cases τ <;> simp [aaθ])] at this
    linarith
  by_cases hd0 : uS 0 ≤ 10 - aaK 0 * a
  · -- type 1 is not equilibrium dominated: respond with the wage `1`
    refine key 0 (hic 0 (hmem10 0 hd0)) ?_
    have := hus θ
    have := hK θ
    simp only [aaθ]; simp; linarith
  · rw [not_le] at hd0
    have hk0 : aaK 0 * a = a := by simp [aaK]
    rw [hk0] at hd0
    by_cases ha17 : (a : ℝ) ≤ 17
    · -- type 2 is not equilibrium dominated: respond with the wage `2`
      refine key 1 (hic 1 (hmem10 1 (by rw [h1]; simp [aaK]; linarith))) ?_
      fin_cases θ <;> simp [aaθ, aaK, h1, h2] <;> linarith
    · -- no type is undominated: all beliefs are allowed; respond with the wage `1`
      rw [not_le] at ha17
      have hempty : aaGame.typesNotEqDominated uS a = ∅ := by
        ext τ
        simp only [typesNotEqDominated, EqDominated, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_not]
        intro w hw
        have := aa_u1_le hw τ
        fin_cases τ <;> simp [aaK, h1, h2] at this ⊢ <;> linarith
      have huniv : aaGame.icTypes uS a = Set.univ := by
        simp [icTypes, hempty]
      refine key 0 (by rw [huniv]; trivial) ?_
      have := hus θ
      have := hK θ
      simp only [aaθ]; simp; linarith

/-- The uniform prior. -/
noncomputable def aaPrior : Fin 3 → ℝ := fun _ => 1 / 3

/-- The pooled belief `(1/2, 1/2, 0)` on types 1 and 2. -/
noncomputable def aaPool : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

theorem aaPool_belief : IsBeliefOn Set.univ aaPool :=
  ⟨fun θ => by fin_cases θ <;> simp [aaPool], by simp [aaPool, Fin.sum_univ_three]; norm_num,
    fun _ _ => trivial⟩

/-- Education levels of the separating PBE. -/
noncomputable def aaE1 : Fin 3 → NNReal := ![0, 1, 17]

/-- Education levels of the partially pooling PBE. -/
noncomputable def aaE2 : Fin 3 → NNReal := ![0, 0, 17]

open Classical in
/-- Beliefs of the separating PBE: Bayes on the path, type 1 off the path. -/
noncomputable def aaBel1 (a : NNReal) : Fin 3 → ℝ :=
  if a = 1 then pointMass 1 else if a = 17 then pointMass 2 else pointMass 0

open Classical in
/-- Beliefs of the partially pooling PBE. -/
noncomputable def aaBel2 (a : NNReal) : Fin 3 → ℝ :=
  if a = 0 then aaPool else if a = 17 then pointMass 2 else pointMass 0

/-- The firms bid the expected productivity. -/
noncomputable def aaResp (μ : NNReal → Fin 3 → ℝ) (a : NNReal) : Fin 2 → ℝ :=
  fun _ => aaMean (μ a)

theorem aaBel1_belief (a : NNReal) : IsBeliefOn Set.univ (aaBel1 a) := by
  unfold aaBel1
  split_ifs <;> exact pointMass_belief _ _ trivial

theorem aaBel2_belief (a : NNReal) : IsBeliefOn Set.univ (aaBel2 a) := by
  unfold aaBel2
  split_ifs
  · exact aaPool_belief
  · exact pointMass_belief _ _ trivial
  · exact pointMass_belief _ _ trivial

theorem aaResp1 (a : NNReal) :
    aaResp aaBel1 a = fun _ => if a = 1 then 2 else if a = 17 then 10 else 1 := by
  funext j
  simp only [aaResp, aaBel1]
  split_ifs <;> rw [aaMean_pointMass] <;> simp [aaθ]

theorem aaResp2 (a : NNReal) :
    aaResp aaBel2 a = fun _ => if a = 0 then 3 / 2 else if a = 17 then 10 else 1 := by
  funext j
  simp only [aaResp, aaBel2]
  split_ifs
  · simp [aaMean, aaPool, aaθ, Fin.sum_univ_three]; norm_num
  · rw [aaMean_pointMass]; simp [aaθ]
  · rw [aaMean_pointMass]; simp [aaθ]

theorem aa_payoff1 : aaGame.eqPayoff aaE1 (aaResp aaBel1) = ![1, 3 / 2, 23 / 4] := by
  funext θ
  simp only [eqPayoff, aaResp1, aaGame]
  fin_cases θ <;> simp [aaE1, aaK] <;> norm_num

theorem aa_payoff2 : aaGame.eqPayoff aaE2 (aaResp aaBel2) = ![3 / 2, 3 / 2, 23 / 4] := by
  funext θ
  simp only [eqPayoff, aaResp2, aaGame]
  fin_cases θ <;> simp [aaE2, aaK] <;> norm_num

/-- **Exercise 13.AA.1** (MWG, p. 476). The separating PBE: education `(0, 1, 17)`. -/
theorem aa_pbe1 : aaGame.IsPBE aaPrior aaE1 (aaResp aaBel1) aaBel1 := by
  refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ⟨aaBel1_belief a,
    (aa_nash_iff a _ (aaBel1_belief a) _).2 ⟨rfl, rfl⟩⟩⟩
  · change _ ≤ aaGame.eqPayoff aaE1 (aaResp aaBel1) θ
    have ha := NNReal.coe_nonneg a
    rw [aa_payoff1, aaResp1, aa_u1 a _ (by split_ifs <;> norm_num)]
    split_ifs with h1 h2
    · subst h1; fin_cases θ <;> norm_num [aaK]
    · subst h2; fin_cases θ <;> norm_num [aaK]
    · fin_cases θ <;> norm_num [aaK] <;> linarith
  · obtain ⟨θ', rfl⟩ := ha
    simp only [Finset.sum_filter, Fin.sum_univ_three]
    fin_cases θ' <;> fin_cases θ <;> simp [aaBel1, aaE1, aaPrior, pointMass]

/-- **Exercise 13.AA.1** (MWG, p. 476). The partially pooling PBE: types 1 and 2 choose
`e = 0`, type 3 chooses `17`. -/
theorem aa_pbe2 : aaGame.IsPBE aaPrior aaE2 (aaResp aaBel2) aaBel2 := by
  refine ⟨fun θ a => ?_, fun a θ ha => ?_, fun a => ⟨aaBel2_belief a,
    (aa_nash_iff a _ (aaBel2_belief a) _).2 ⟨rfl, rfl⟩⟩⟩
  · change _ ≤ aaGame.eqPayoff aaE2 (aaResp aaBel2) θ
    have ha := NNReal.coe_nonneg a
    rw [aa_payoff2, aaResp2, aa_u1 a _ (by split_ifs <;> norm_num)]
    split_ifs with h1 h2
    · subst h1; fin_cases θ <;> norm_num [aaK]
    · subst h2; fin_cases θ <;> norm_num [aaK]
    · fin_cases θ <;> norm_num [aaK] <;> linarith
  · obtain ⟨θ', rfl⟩ := ha
    simp only [Finset.sum_filter, Fin.sum_univ_three]
    fin_cases θ' <;> fin_cases θ <;> simp [aaBel2, aaE2, aaPrior, aaPool, pointMass] <;> norm_num

/-- **Exercise 13.AA.1** (MWG, p. 476). In the three-type education signaling model with
`r(θ) = 0`, two PBE with different outcomes, the separating PBE (education `(0, 1, 17)`) and a
partially pooling PBE (education `(0, 0, 17)`), both satisfy the intuitive criterion: the
lowest type gets `1` in the first and `3/2` in the second. -/
theorem exercise_13_AA_1 :
    aaGame.IsPBE aaPrior aaE1 (aaResp aaBel1) aaBel1 ∧
      aaGame.IsPBE aaPrior aaE2 (aaResp aaBel2) aaBel2 ∧
      ¬ aaGame.ViolatesIC (aaGame.eqPayoff aaE1 (aaResp aaBel1)) ∧
      ¬ aaGame.ViolatesIC (aaGame.eqPayoff aaE2 (aaResp aaBel2)) ∧
      aaE1 ≠ aaE2 ∧
      aaGame.eqPayoff aaE1 (aaResp aaBel1) 0 ≠ aaGame.eqPayoff aaE2 (aaResp aaBel2) 0 := by
  refine ⟨aa_pbe1, aa_pbe2, ?_, ?_, fun h => ?_, ?_⟩
  · rw [aa_payoff1]; exact aa_passes_ic _ (by simp) (by simp; norm_num) (by simp) (by simp)
  · rw [aa_payoff2]
    exact aa_passes_ic _ (by simp; norm_num) (by simp) (by simp) (by simp)
  · have := congrFun h 1
    simp [aaE1, aaE2] at this
  · rw [aa_payoff1, aa_payoff2]; simp; norm_num

end MWG.AdverseSelection
