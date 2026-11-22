/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.StickCarrot
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# Instances of Propositions 12.AA.1 and 12.AA.4; Example 12.AA.1

MWG, pp. 419-423.

* `locG`: a bounded two-player game on `ℝ²`, `π_i(q) = φ(q_j) − ψ(q_i)` with
  `φ(x) = x/(1 + x²)` and `ψ(x) = x²/(1 + x²)`, whose unique stage Nash equilibrium `q* = 0`
  satisfies all conditions of `LocalGameData` (`locG_data`); hence Propositions 12.AA.1 and
  12.AA.4 apply (`proposition_12_AA_1_instance`, `proposition_12_AA_4_instance`).
* `example_12_AA_1`: the Cournot stick-and-carrot SPNE with average payoff `0`, for quantities
  in a compact interval `[0, B]` (footnote 36).
* `example_12_AA_1_qbar`: as `δ → 1`, the stick `q̄` solving (12.AA.7) exists and exceeds the
  competitive quantity `q_c`.
* `example_12_AA_1_instance`: `p(x) = max(4 − x, 0)`, `c = 1`, `δ = 9/10`, `B = 11`,
  `q̄ = 81/8`, `qᵐ = 3/4`, `q* = (1, 1)`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

/-- `φ(x) = x/(1 + x²)`. -/
noncomputable def locPhi (x : ℝ) : ℝ := x / (1 + x ^ 2)

/-- `ψ(x) = x²/(1 + x²)`. -/
noncomputable def locPsi (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2)

/-- The game `π_i(q) = φ(q_j) − ψ(q_i)`. -/
noncomputable def locG (i : Fin 2) (q : Fin 2 → ℝ) : ℝ :=
  if i = 0 then locPhi (q 1) - locPsi (q 0) else locPhi (q 0) - locPsi (q 1)

theorem locPhi_abs (x : ℝ) : |locPhi x| ≤ 1 := by
  unfold locPhi
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2), div_le_one (by positivity)]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; nlinarith [sq_nonneg (x - 1)]
  · rw [abs_of_nonpos h]; nlinarith [sq_nonneg (x + 1)]

theorem locPsi_nonneg (x : ℝ) : 0 ≤ locPsi x := by unfold locPsi; positivity

theorem locPsi_le (x : ℝ) : locPsi x ≤ 1 := by
  unfold locPsi; rw [div_le_one (by positivity)]; linarith

theorem locG_bound : ∀ i x, |locG i x| ≤ 2 := by
  intro i x
  unfold locG
  split_ifs <;>
  · rw [abs_le]
    constructor <;> linarith [abs_le.1 (locPhi_abs (x 1)), abs_le.1 (locPhi_abs (x 0)),
      locPsi_nonneg (x 0), locPsi_nonneg (x 1), locPsi_le (x 0), locPsi_le (x 1)]

theorem locG_nash : IsStageNash locG 0 := by
  have h0 : ∀ j, locG j 0 = 0 := fun j => by
    unfold locG; split_ifs <;> simp [locPhi, locPsi]
  have hφ : locPhi 0 = 0 := by simp [locPhi]
  unfold IsStageNash
  rw [Fin.forall_fin_two]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have : locG 0 (update 0 0 a) = locPhi 0 - locPsi a := by simp [locG, update]
    rw [this, hφ, h0]; linarith [locPsi_nonneg a]
  · have : locG 1 (update 0 1 a) = locPhi 0 - locPsi a := by simp [locG, update]
    rw [this, hφ, h0]; linarith [locPsi_nonneg a]

theorem locPhi_hasDerivAt : HasDerivAt locPhi 1 0 := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * 0) 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_add 1
  have := (hasDerivAt_id' (0 : ℝ)).div h1 (by norm_num)
  exact this.congr_deriv (by norm_num)

theorem locPsi_hasDerivAt : HasDerivAt locPsi 0 0 := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * 0) 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * 0) 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have := h2.div h1 (by norm_num)
  exact this.congr_deriv (by norm_num)

theorem locG_bestReply (i : Fin 2) (y : ℝ) :
    bestReplyValue locG i (update 0 (1 - i) y) = locPhi y := by
  unfold bestReplyValue
  refine le_antisymm (ciSup_le fun a => ?_) ?_
  · fin_cases i <;> simp [locG, update] <;> linarith [locPsi_nonneg a]
  · refine le_trans ?_ (le_ciSup (f := fun a => locG i (update (update 0 (1 - i) y) i a))
      ⟨2, fun _ ⟨b, hb⟩ => hb ▸ (le_abs_self _).trans (locG_bound i _)⟩ 0)
    fin_cases i <;> simp [locG, update, locPsi]

/-- The game `locG` satisfies the hypotheses of Propositions 12.AA.1 and 12.AA.4 at `q* = 0`. -/
noncomputable def locG_data : LocalGameData locG 0 where
  L0 := (1 : ℝ) • ContinuousLinearMap.proj 1 - (0 : ℝ) • ContinuousLinearMap.proj 0
  L1 := (1 : ℝ) • ContinuousLinearMap.proj 0 - (0 : ℝ) • ContinuousLinearMap.proj 1
  deriv0 := by
    have hφ : HasDerivAt locPhi 1 ((0 : Fin 2 → ℝ) 1) := by simpa using locPhi_hasDerivAt
    have hψ : HasDerivAt locPsi 0 ((0 : Fin 2 → ℝ) 0) := by simpa using locPsi_hasDerivAt
    have h1 := hφ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ))
    have h2 := hψ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ))
    have := h1.sub h2
    convert this using 1
    funext q; simp [locG, Function.comp]
  deriv1 := by
    have hφ : HasDerivAt locPhi 1 ((0 : Fin 2 → ℝ) 0) := by simpa using locPhi_hasDerivAt
    have hψ : HasDerivAt locPsi 0 ((0 : Fin 2 → ℝ) 1) := by simpa using locPsi_hasDerivAt
    have h1 := hφ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ))
    have h2 := hψ.comp_hasFDerivAt (0 : Fin 2 → ℝ)
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ))
    have := h1.sub h2
    convert this using 1
    funext q; simp [locG, Function.comp]
  own0 := by simp
  own1 := by simp
  cross0 := by simp
  cross1 := by simp
  env0 := by
    have : (fun y => bestReplyValue locG 0 (update 0 1 y)) = locPhi := by
      funext y; simpa using locG_bestReply 0 y
    rw [this]
    simpa using locPhi_hasDerivAt
  env1 := by
    have : (fun y => bestReplyValue locG 1 (update 0 0 y)) = locPhi := by
      funext y; simpa using locG_bestReply 1 y
    rw [this]
    simpa using locPhi_hasDerivAt

/-- **Proposition 12.AA.1, an instance**: in `locG` with `δ = 1/2`, a Pareto improvement over
`q* = 0` is sustained by Nash reversion. -/
theorem proposition_12_AA_1_instance :
    ∃ q', (∀ i, locG i 0 < locG i q') ∧
      IsRepeatedSPNE locG (1 / 2) (nashReversion (fun _ => q') 0) :=
  proposition_12_AA_1 (by norm_num) (by norm_num) locG_bound locG_nash locG_data

/-- **Proposition 12.AA.4, an instance**: in `locG` with `δ = 1/2`, a stick-and-carrot SPNE
gives both players less than their stage Nash payoff. -/
theorem proposition_12_AA_4_instance :
    ∃ q', (∀ i, locG i q' < locG i 0) ∧ IsRepeatedSPNE locG (1 / 2) (scProfile q' 0 0 0) ∧
      ∀ i, (1 - 1 / 2) * osValue (stageU locG) (1 / 2) (scProfile q' 0 0 0) [] i < locG i 0 :=
  proposition_12_AA_4 (by norm_num) (by norm_num) locG_bound locG_nash locG_data

end MWG.MarketPower
