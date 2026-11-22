/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.StickCarrotInstances
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Propositions 12.AA.1 and 12.AA.4 as printed are false

MWG, Appendix A of Chapter 12, Propositions 12.AA.1 (p. 419) and 12.AA.4 (p. 421; Exercise
12.AA.2, p. 435).

MWG states both propositions for a two-player game with actions in `ℝ`, payoffs `π_i`
differentiable at the stage Nash equilibrium `q*`, and `∂π_i(q*)/∂q_j ≠ 0` (12.AA.4 adds
`π_i(q*) > π̲_i`). The proof of 12.AA.1 also uses the envelope property (12.AA.6), that the
best-response payoff `π̂_i` is differentiable at `q_j*` with derivative `∂π_i(q*)/∂q_j`; this does
not follow from the printed hypotheses, and without it both propositions fail.

* `sclG`: actions clamped to `S_i = [-1, 1]`; with `u = q_1`, `y = q_2` (after clamping),
  `π_1 = y − u² − min(u, 0)·|y|^{1/4}` and `π_2 = u − y²`. It has bounded payoffs, the unique
  stage Nash equilibrium `q* = 0`, best responses that exist, `π_i` differentiable at `q*` with
  cross partials `1`, and minimax payoffs below the Nash payoffs (`sclG_hypotheses`). But
  `π̂_1(y) = y + |y|^{1/2}/4`: a deviation gain of order `|y|^{1/2}`, not `o(|y|)`.
* `proposition_12_AA_1_false`: for every `δ ∈ (0, 1/5]` no `q'` with `π_i(q') > π_i(q*)` for
  both players is sustained by Nash reversion.
* `proposition_12_AA_4_false`: for every `δ ∈ (0, 1/2000]`, in every SPNE player 1's average
  payoff in every subgame is at least `π_1(q*)`, so no SPNE gives both players less.
* `counterexample_12_AA_1_4`: the two together, and `LocalGameData sclG 0` is empty.
* Corrected statements, `proposition_12_AA_1_upper` and `proposition_12_AA_4_upper`: MWG's
  hypotheses plus the one-sided bound
  `π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)`; the reverse bound already
  follows from `q*` being a Nash equilibrium and differentiability (`scl_env_of_upper`), as does
  `∂π_i(q*)/∂q_i = 0` (`scl_own_partial_zero`). Given those hypotheses the one-sided bound is
  equivalent to (12.AA.6) (`scl_upper_of_hasDerivAt`). Instances: `scl_upper_instance_1`,
  `scl_upper_instance_4`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

/-! ### The counterexample game -/

/-- Clamping to the action set `S_i = [-1, 1]`. -/
noncomputable def sclClamp (x : ℝ) : ℝ := max (-1) (min x 1)

/-- `|y|^{1/4}` of the clamped action `y`. -/
noncomputable def sclRoot (y : ℝ) : ℝ := Real.sqrt (Real.sqrt |sclClamp y|)

/-- The stage game: with `u = clamp(q_1)` and `y = clamp(q_2)`, player 1 (index `0`) gets
`y − u² − min(u, 0)·|y|^{1/4}` and player 2 (index `1`) gets `u − y²`. -/
noncomputable def sclG (i : Fin 2) (q : Fin 2 → ℝ) : ℝ :=
  if i = 0 then sclClamp (q 1) - sclClamp (q 0) ^ 2 - min (sclClamp (q 0)) 0 * sclRoot (q 1)
  else sclClamp (q 0) - sclClamp (q 1) ^ 2

theorem sclClamp_abs (x : ℝ) : |sclClamp x| ≤ 1 := by
  unfold sclClamp
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem sclClamp_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : sclClamp x = x := by
  unfold sclClamp
  rw [abs_le] at hx
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem sclClamp_eq_zero {x : ℝ} (hx : sclClamp x = 0) : x = 0 := by
  unfold sclClamp at hx
  rcases le_total x 1 with h | h
  · rw [min_eq_left h] at hx
    rcases le_total (-1) x with h' | h'
    · rwa [max_eq_right h'] at hx
    · rw [max_eq_left h'] at hx
      norm_num at hx
  · rw [min_eq_right h, max_eq_right (by norm_num)] at hx
    norm_num at hx

/-- The game depends on actions only through their clamped values: the action sets are
effectively the compact interval `[-1, 1]` (MWG, p. 417). -/
theorem sclG_clamp (i : Fin 2) (q : Fin 2 → ℝ) : sclG i (fun k => sclClamp (q k)) = sclG i q := by
  have e : ∀ x, sclClamp (sclClamp x) = sclClamp x := fun x => sclClamp_of_abs_le (sclClamp_abs x)
  simp only [sclG, sclRoot, e]

theorem sclClamp_zero : sclClamp 0 = 0 := sclClamp_of_abs_le (by simp)

theorem sclRoot_nonneg (y : ℝ) : 0 ≤ sclRoot y := Real.sqrt_nonneg _

theorem sclRoot_zero : sclRoot 0 = 0 := by simp [sclRoot, sclClamp_zero]

theorem sclRoot_sq (y : ℝ) : sclRoot y ^ 2 = Real.sqrt |sclClamp y| :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem sclRoot_le_one (y : ℝ) : sclRoot y ≤ 1 := by
  have h1 : Real.sqrt |sclClamp y| ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (sclClamp_abs y)
  simpa [sclRoot] using Real.sqrt_le_sqrt h1

/-- `|y| ≤ |y|^{1/2}` on `[-1, 1]`. -/
theorem sclRoot_sq_ge (y : ℝ) : |sclClamp y| ≤ sclRoot y ^ 2 := by
  rw [sclRoot_sq]
  have ht := sclClamp_abs y
  have hs := Real.sq_sqrt (abs_nonneg (sclClamp y))
  have hs0 := Real.sqrt_nonneg |sclClamp y|
  nlinarith

/-- `4|y| ≤ |y|^{1/2}` when `|y| ≤ 1/16`. -/
theorem sclRoot_sq_ge_four {y : ℝ} (hy : |sclClamp y| ≤ 1 / 16) :
    4 * |sclClamp y| ≤ sclRoot y ^ 2 := by
  rw [sclRoot_sq]
  have hs := Real.sq_sqrt (abs_nonneg (sclClamp y))
  have hs0 := Real.sqrt_nonneg |sclClamp y|
  have hs1 : Real.sqrt |sclClamp y| ≤ 1 / 4 := by nlinarith
  nlinarith

theorem sclG_bound : ∀ i x, |sclG i x| ≤ 3 := by
  intro i x
  have h0 := abs_le.1 (sclClamp_abs (x 0))
  have h1 := abs_le.1 (sclClamp_abs (x 1))
  have hr0 := sclRoot_nonneg (x 1)
  have hr1 := sclRoot_le_one (x 1)
  have hm1 : min (sclClamp (x 0)) 0 ≤ 0 := min_le_right _ _
  have hm2 : -1 ≤ min (sclClamp (x 0)) 0 := le_min h0.1 (by norm_num)
  have hp1 : min (sclClamp (x 0)) 0 * sclRoot (x 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm1 hr0
  have hp2 : -1 ≤ min (sclClamp (x 0)) 0 * sclRoot (x 1) := by nlinarith
  have hq0 : sclClamp (x 0) ^ 2 ≤ 1 := by nlinarith
  have hq1 : sclClamp (x 1) ^ 2 ≤ 1 := by nlinarith
  unfold sclG
  rw [abs_le]
  split_ifs
  · constructor <;> nlinarith [sq_nonneg (sclClamp (x 0))]
  · constructor <;> nlinarith [sq_nonneg (sclClamp (x 1))]

theorem sclG_zero_update (x : Fin 2 → ℝ) (a : ℝ) :
    sclG 0 (update x 0 a) =
      sclClamp (x 1) - sclClamp a ^ 2 - min (sclClamp a) 0 * sclRoot (x 1) := by
  simp [sclG]

theorem sclG_one_update (x : Fin 2 → ℝ) (a : ℝ) :
    sclG 1 (update x 1 a) = sclClamp (x 0) - sclClamp a ^ 2 := by
  simp [sclG]

theorem sclG_zero_val : ∀ i, sclG i 0 = 0 := by
  intro i
  fin_cases i <;> simp [sclG, sclClamp_zero, sclRoot_zero]

/-- Player 1's best-response payoff is `π̂_1(y) = y + |y|^{1/2}/4`, attained at
`u = −|y|^{1/4}/2`. -/
theorem sclG_br0 (x : Fin 2 → ℝ) :
    bestReplyValue sclG 0 x = sclClamp (x 1) + sclRoot (x 1) ^ 2 / 4 ∧
      sclG 0 (update x 0 (-sclRoot (x 1) / 2)) = bestReplyValue sclG 0 x := by
  have hr0 := sclRoot_nonneg (x 1)
  have hr1 := sclRoot_le_one (x 1)
  have hat : sclG 0 (update x 0 (-sclRoot (x 1) / 2)) =
      sclClamp (x 1) + sclRoot (x 1) ^ 2 / 4 := by
    rw [sclG_zero_update, sclClamp_of_abs_le (x := -sclRoot (x 1) / 2)
      (by rw [abs_le]; constructor <;> linarith), min_eq_left (by linarith)]
    ring
  have hbr : bestReplyValue sclG 0 x = sclClamp (x 1) + sclRoot (x 1) ^ 2 / 4 := by
    refine le_antisymm (ciSup_le fun a => ?_) ?_
    · rw [sclG_zero_update]
      rcases le_total 0 (sclClamp a) with h | h
      · rw [min_eq_right h]
        nlinarith [sq_nonneg (sclClamp a)]
      · rw [min_eq_left h]
        nlinarith [sq_nonneg (sclClamp a + sclRoot (x 1) / 2)]
    · rw [← hat]
      exact le_bestReplyValue sclG_bound 0 x _
  exact ⟨hbr, by rw [hat, hbr]⟩

/-- Player 2's best-response payoff is `π̂_2(u) = u`, attained at `y = 0`. -/
theorem sclG_br1 (x : Fin 2 → ℝ) :
    bestReplyValue sclG 1 x = sclClamp (x 0) ∧ sclG 1 (update x 1 0) = bestReplyValue sclG 1 x := by
  have hat : sclG 1 (update x 1 0) = sclClamp (x 0) := by
    rw [sclG_one_update, sclClamp_zero]
    ring
  have hbr : bestReplyValue sclG 1 x = sclClamp (x 0) := by
    refine le_antisymm (ciSup_le fun a => ?_) ?_
    · rw [sclG_one_update]
      nlinarith [sq_nonneg (sclClamp a)]
    · rw [← hat]
      exact le_bestReplyValue sclG_bound 1 x _
  exact ⟨hbr, by rw [hat, hbr]⟩

theorem sclG_nash : IsStageNash sclG 0 := by
  intro i a
  rw [sclG_zero_val]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [sclG_zero_update]
    simp only [Pi.zero_apply, sclClamp_zero, sclRoot_zero, mul_zero, sub_zero, zero_sub,
      Left.neg_nonpos_iff]
    exact sq_nonneg _
  · simp only [Fin.mk_one, Fin.isValue]
    rw [sclG_one_update]
    simp only [Pi.zero_apply, sclClamp_zero, zero_sub, Left.neg_nonpos_iff]
    exact sq_nonneg _

theorem sclG_nash_unique (x : Fin 2 → ℝ) (hx : IsStageNash sclG x) : x = 0 := by
  have h1 := hx 1 0
  rw [sclG_one_update, sclClamp_zero] at h1
  simp only [sclG, Fin.isValue, one_ne_zero, ↓reduceIte] at h1
  have hx1 : x 1 = 0 := sclClamp_eq_zero (by nlinarith [sq_nonneg (sclClamp (x 1))])
  have h0 := hx 0 0
  rw [sclG_zero_update, sclClamp_zero] at h0
  simp only [sclG, ↓reduceIte, hx1, sclClamp_zero, sclRoot_zero] at h0
  have hx0 : x 0 = 0 := sclClamp_eq_zero (by nlinarith [sq_nonneg (sclClamp (x 0))])
  funext k
  fin_cases k
  · exact hx0
  · exact hx1

/-- Player 1's payoff is differentiable at `q* = 0` with derivative `(0, 1)`. -/
theorem sclG_deriv0 :
    HasFDerivAt (sclG 0) (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hρ : 0 < min 1 (min (c / 2) ((c / 2) ^ 4)) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Fin 2 → ℝ) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hb1 : ‖h‖ < 1 := hh.trans_le (min_le_left _ _)
  have hb2 : ‖h‖ < c / 2 := hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hb3 : ‖h‖ < (c / 2) ^ 4 := hh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have h0 : |h 0| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 0
  have h1 : |h 1| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 1
  have e0 : sclClamp (h 0) = h 0 := sclClamp_of_abs_le (by linarith)
  have e1 : sclClamp (h 1) = h 1 := sclClamp_of_abs_le (by linarith)
  have hr : sclRoot (h 1) ≤ c / 2 := by
    unfold sclRoot
    rw [e1]
    have h4 : |h 1| ≤ ((c / 2) ^ 2) ^ 2 := by rw [← pow_mul]; linarith
    have s1 : Real.sqrt |h 1| ≤ (c / 2) ^ 2 :=
      (Real.sqrt_le_sqrt h4).trans_eq (Real.sqrt_sq (by positivity))
    exact (Real.sqrt_le_sqrt s1).trans_eq (Real.sqrt_sq (by positivity))
  have hr0 := sclRoot_nonneg (h 1)
  have hm : |min (h 0) 0| ≤ |h 0| := by
    rcases le_total (h 0) 0 with h' | h'
    · rw [min_eq_left h']
    · rw [min_eq_right h', abs_zero]
      exact abs_nonneg _
  have p1 : h 0 ^ 2 ≤ ‖h‖ * (c / 2) := by
    rw [← sq_abs]
    calc |h 0| ^ 2 = |h 0| * |h 0| := sq _
      _ ≤ ‖h‖ * (c / 2) := mul_le_mul h0 (by linarith) (abs_nonneg _) (norm_nonneg _)
  have p2 : |min (h 0) 0 * sclRoot (h 1)| ≤ ‖h‖ * (c / 2) := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul (hm.trans h0) hr hr0 (norm_nonneg _)
  have p2' := abs_le.1 p2
  rw [zero_add, sclG_zero_val, Real.norm_eq_abs, ContinuousLinearMap.proj_apply]
  simp only [sclG, ↓reduceIte, e0, e1]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (h 0)]

/-- Player 2's payoff is differentiable at `q* = 0` with derivative `(1, 0)`. -/
theorem sclG_deriv1 :
    HasFDerivAt (sclG 1) (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hρ : 0 < min 1 c := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Fin 2 → ℝ) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hb1 : ‖h‖ < 1 := hh.trans_le (min_le_left _ _)
  have hb2 : ‖h‖ < c := hh.trans_le (min_le_right _ _)
  have h0 : |h 0| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 0
  have h1 : |h 1| ≤ ‖h‖ := by simpa using norm_le_pi_norm h 1
  have e0 : sclClamp (h 0) = h 0 := sclClamp_of_abs_le (by linarith)
  have e1 : sclClamp (h 1) = h 1 := sclClamp_of_abs_le (by linarith)
  have p1 : h 1 ^ 2 ≤ c * ‖h‖ := by
    rw [← sq_abs]
    calc |h 1| ^ 2 = |h 1| * |h 1| := sq _
      _ ≤ c * ‖h‖ := mul_le_mul (by linarith) h1 (abs_nonneg _) hc.le
  rw [zero_add, sclG_zero_val, Real.norm_eq_abs, ContinuousLinearMap.proj_apply]
  simp only [sclG, Fin.isValue, one_ne_zero, ↓reduceIte, e0, e1]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (h 1)]

/-- **The counterexample satisfies MWG's hypotheses** (pp. 417, 419, 421): bounded payoffs
depending on actions only through `[-1, 1]` (`sclG_clamp`), the unique pure stage Nash
equilibrium `q* = 0`, best responses that exist (footnote 31), `π_i` differentiable at `q*` with
`∂π_1(q*)/∂q_2 = ∂π_2(q*)/∂q_1 = 1 ≠ 0`, and minimax payoffs `π̲_i < π_i(q*)`. -/
theorem sclG_hypotheses :
    (∀ i x, |sclG i x| ≤ 3) ∧ IsStageNash sclG 0 ∧ (∀ x, IsStageNash sclG x → x = 0) ∧
    (∀ i x, ∃ a, sclG i (update x i a) = bestReplyValue sclG i x) ∧
    HasFDerivAt (sclG 0) (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
    HasFDerivAt (sclG 1) (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 1 1) ≠ 0 ∧
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 0 1) ≠ 0 ∧
    ∀ i, minimaxValue sclG i < sclG i 0 := by
  refine ⟨sclG_bound, sclG_nash, sclG_nash_unique, ?_, sclG_deriv0, sclG_deriv1, by simp,
    by simp, ?_⟩
  · intro i x
    fin_cases i
    · exact ⟨_, (sclG_br0 x).2⟩
    · exact ⟨_, (sclG_br1 x).2⟩
  · intro i
    rw [sclG_zero_val]
    have hbdd : BddBelow (Set.range fun x : Fin 2 → ℝ => bestReplyValue sclG i x) :=
      ⟨-3, fun _ ⟨x, hx⟩ => hx ▸ bestReplyValue_ge sclG_bound i x⟩
    refine lt_of_le_of_lt (ciInf_le hbdd (fun _ => -1)) ?_
    have hc : sclClamp (-1) = -1 := sclClamp_of_abs_le (by norm_num)
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [(sclG_br0 _).1]
      have hr : sclRoot (-1) = 1 := by simp [sclRoot, hc]
      simp only [hc, hr]
      norm_num
    · simp only [Fin.mk_one, Fin.isValue]
      rw [(sclG_br1 _).1, hc]
      norm_num

/-! ### Proposition 12.AA.1 fails -/

/-- **Proposition 12.AA.1 is false as printed** (MWG, p. 419). In `sclG`, for every
`δ ∈ (0, 1/5]`, no `q'` with `π_i(q') > π_i(q*)` for both players is sustained by Nash reversion:
player 1's gain from deviating to `−|q_2'|^{1/4}/2` is `|q_2'|^{1/2}/4 + q_1'^2`, more than
`δ/(1 − δ)` times the gain `π_1(q') − π_1(q*) < q_2'`. -/
theorem proposition_12_AA_1_false {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 5) (q' : Fin 2 → ℝ)
    (hq' : ∀ i, sclG i 0 < sclG i q') :
    ¬ IsRepeatedSPNE sclG δ (nashReversion (fun _ => q') 0) := by
  intro hspne
  have hδ1 : δ < 1 := by linarith
  rw [nashReversion_spne_iff hδ0.le hδ1 sclG_bound _ sclG_nash] at hspne
  have hp0 := hq' 0
  have hp1 := hq' 1
  rw [sclG_zero_val] at hp0 hp1
  simp only [sclG, Fin.isValue, one_ne_zero, ↓reduceIte] at hp0 hp1
  have hr0 := sclRoot_nonneg (q' 1)
  have hr1 := sclRoot_le_one (q' 1)
  have hu : 0 < sclClamp (q' 0) := by nlinarith [sq_nonneg (sclClamp (q' 1))]
  rw [min_eq_right hu.le, zero_mul, sub_zero] at hp0
  have hy : 0 < sclClamp (q' 1) := by nlinarith [sq_nonneg (sclClamp (q' 0))]
  have hca : sclClamp (-sclRoot (q' 1) / 2) = -sclRoot (q' 1) / 2 :=
    sclClamp_of_abs_le (by rw [abs_le]; constructor <;> linarith)
  have ha : -sclRoot (q' 1) / 2 ≠ q' 0 := by
    intro h
    rw [h] at hca
    rw [hca] at hu
    linarith
  have key := hspne 0 0 _ ha
  rw [pathValue_const sclG hδ0.le hδ1, sclG_zero_update, sclG_zero_val, hca,
    min_eq_left (by linarith)] at key
  have hge := sclRoot_sq_ge (q' 1)
  rw [abs_of_pos hy] at hge
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  simp only [sclG, ↓reduceIte, min_eq_right hu.le, zero_mul, sub_zero, zero_div, mul_zero,
    add_zero] at key
  rw [le_div_iff₀ h1δ] at key
  nlinarith [sq_pos_of_pos hu, mul_le_mul_of_nonneg_left hge h1δ.le]

/-! ### Proposition 12.AA.4 fails -/

/-- In every SPNE of the repeated `sclG` game, player 2's action at every history satisfies
`clamp(q_2)² ≤ 6δ/(1 − δ)`: playing `0` instead gains `clamp(q_2)²` now and loses at most the
range `6/(1 − δ)` of continuation values. -/
theorem sclG_spne_action_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : OSProfile fun _ : Fin 2 => ℝ} (hσ : IsRepeatedSPNE sclG δ σ)
    (h : OSHist fun _ : Fin 2 => ℝ) :
    sclClamp (σ 1 h) ^ 2 ≤ 6 * δ / (1 - δ) := by
  have hos := (oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound sclG_bound) σ).1
    hσ 1 h 0
  rw [osValue_succ hδ0 hδ1 (stageU_bound sclG_bound) σ h 1] at hos
  have hV1 := abs_le.1 (osValue_abs_le hδ0 hδ1 (stageU_bound sclG_bound) σ
    (osPlay σ h :: h) 1)
  have hV2 := abs_le.1 (osValue_abs_le hδ0 hδ1 (stageU_bound sclG_bound) σ
    (update (osPlay σ h) 1 0 :: h) 1)
  simp only [stageU] at hos
  rw [sclG_one_update, sclClamp_zero] at hos
  have e : sclG 1 (osPlay σ h) = sclClamp (σ 0 h) - sclClamp (σ 1 h) ^ 2 := by
    simp [sclG, osPlay]
  have e2 : (osPlay σ h) 0 = σ 0 h := rfl
  rw [e, e2] at hos
  have hd : δ * (osValue (stageU sclG) δ σ (osPlay σ h :: h) 1 -
      osValue (stageU sclG) δ σ (update (osPlay σ h) 1 0 :: h) 1) ≤ δ * (6 / (1 - δ)) :=
    mul_le_mul_of_nonneg_left (by
      have : 6 / (1 - δ) = 3 / (1 - δ) + 3 / (1 - δ) := by ring
      linarith [hV1.2, hV2.1]) hδ0
  have e3 : 6 * δ / (1 - δ) = δ * (6 / (1 - δ)) := by ring
  rw [e3]
  nlinarith

/-- In every SPNE of the repeated `sclG` game with `δ ∈ [0, 1/2000]`, player 1's payoff in every
subgame is nonnegative: player 2's actions satisfy `|clamp(q_2)| ≤ 1/16`, where
`π̂_1(q_2) = clamp(q_2) + |clamp(q_2)|^{1/2}/4 ≥ 0`, so best-responding period by period secures
`0 = π_1(q*)`. -/
theorem sclG_spne_value_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2000)
    {σ : OSProfile fun _ : Fin 2 => ℝ} (hσ : IsRepeatedSPNE sclG δ σ)
    (h : OSHist fun _ : Fin 2 => ℝ) :
    0 ≤ osValue (stageU sclG) δ σ h 0 := by
  have hδ1 : δ < 1 := by linarith
  set τ : OSHist (fun _ : Fin 2 => ℝ) → ℝ := fun h' => -sclRoot (σ 1 h') / 2 with hτ
  have hterm : ∀ h', 0 ≤ stageU sclG 0 h' (osPlay (update σ 0 τ) h') := by
    intro h'
    rw [osPlay_update]
    simp only [stageU]
    have hsq := sclG_spne_action_sq hδ0 hδ1 hσ h'
    have hsmall : 6 * δ / (1 - δ) ≤ 1 / 256 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hc : |sclClamp (σ 1 h')| ≤ 1 / 16 := by
      have := sq_abs (sclClamp (σ 1 h'))
      nlinarith [abs_nonneg (sclClamp (σ 1 h'))]
    have h4 := sclRoot_sq_ge_four hc
    have hv := (sclG_br0 (osPlay σ h')).2
    rw [(sclG_br0 (osPlay σ h')).1] at hv
    have e : (osPlay σ h') 1 = σ 1 h' := rfl
    simp only [hτ, ← e]
    rw [hv]
    rw [e]
    nlinarith [neg_abs_le (sclClamp (σ 1 h'))]
  have hnn : 0 ≤ osValue (stageU sclG) δ (update σ 0 τ) h 0 :=
    tsum_nonneg fun n => mul_nonneg (pow_nonneg hδ0 n) (hterm _)
  exact hnn.trans (hσ 0 τ h)

/-- **Proposition 12.AA.4 (Exercise 12.AA.2) is false as printed** (MWG, pp. 421, 435). In
`sclG`, for every `δ ∈ (0, 1/2000]`, no SPNE gives both players average payoffs
`(1 − δ)v_i' < π_i(q*)`. -/
theorem proposition_12_AA_4_false {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2000) :
    ¬ ∃ σ : OSProfile (fun _ : Fin 2 => ℝ), IsRepeatedSPNE sclG δ σ ∧
      ∀ i, (1 - δ) * osValue (stageU sclG) δ σ [] i < sclG i 0 := by
  rintro ⟨σ, hσ, hlt⟩
  have h1 := hlt 0
  have h2 := sclG_spne_value_nonneg hδ0.le hδ hσ []
  rw [sclG_zero_val] at h1
  have : 0 ≤ (1 - δ) * osValue (stageU sclG) δ σ [] 0 := mul_nonneg (by linarith) h2
  linarith

/-- **Propositions 12.AA.1 and 12.AA.4 are false as printed** (MWG, pp. 419, 421). The game
`sclG` satisfies every printed hypothesis (`sclG_hypotheses`), yet at `δ = 1/5` no Pareto
improvement over `q*` is sustained by Nash reversion, and at `δ = 1/2000` no SPNE gives both
players less than `π_i(q*)`. Consequently the envelope property (12.AA.6) fails there:
`LocalGameData sclG 0` is empty. -/
theorem counterexample_12_AA_1_4 :
    (∀ q' : Fin 2 → ℝ, (∀ i, sclG i 0 < sclG i q') →
      ¬ IsRepeatedSPNE sclG (1 / 5) (nashReversion (fun _ => q') 0)) ∧
    (¬ ∃ σ : OSProfile (fun _ : Fin 2 => ℝ), IsRepeatedSPNE sclG (1 / 2000) σ ∧
      ∀ i, (1 - 1 / 2000) * osValue (stageU sclG) (1 / 2000) σ [] i < sclG i 0) ∧
    IsEmpty (LocalGameData sclG 0) := by
  refine ⟨fun q' hq' => proposition_12_AA_1_false (by norm_num) le_rfl q' hq',
    proposition_12_AA_4_false (by norm_num) le_rfl, ⟨fun D => ?_⟩⟩
  obtain ⟨q', hq', hs⟩ := proposition_12_AA_1 (δ := 1 / 5) (by norm_num) (by norm_num)
    sclG_bound sclG_nash D
  exact proposition_12_AA_1_false (by norm_num) le_rfl q' hq' hs

/-! ### The corrected statements -/

/-- At a stage Nash equilibrium where `π_i` is differentiable, `∂π_i(q*)/∂q_i = 0`
((12.AA.4), MWG, p. 419). -/
theorem scl_own_partial_zero {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ}
    {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (i : Fin 2) (hd : HasFDerivAt (g i) L qs)
    (hqs : IsStageNash g qs) : L (Pi.single i 1) = 0 := by
  have hc := hd.comp_hasDerivAt_of_eq (qs i) (hasDerivAt_update qs i (qs i))
    (update_eq_self i qs).symm
  have hmax : IsLocalMax (g i ∘ update qs i) (qs i) :=
    Eventually.of_forall fun s => by
      change g i (update qs i s) ≤ g i (update qs i (qs i))
      rw [update_eq_self]
      exact hqs i s
  exact hmax.hasDerivAt_eq_zero hc

/-- A function squeezed between a differentiable lower bound touching it at `y₀` and a one-sided
first-order upper bound is differentiable at `y₀`. -/
theorem scl_hasDerivAt_squeeze {f h : ℝ → ℝ} {a c y₀ : ℝ} (hh : HasDerivAt h a y₀)
    (hle : ∀ y, h y ≤ f y) (hf0 : f y₀ = c) (hh0 : h y₀ = c)
    (hup : ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, f y ≤ c + a * (y - y₀) + ε * |y - y₀|) :
    HasDerivAt f a y₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hh.isLittleO.bound hε, hup ε hε] with y h1 h2
  simp only [smul_eq_mul, Real.norm_eq_abs] at h1 ⊢
  rw [abs_le] at h1 ⊢
  have := hle y
  rw [hf0]
  rw [hh0] at h1
  constructor <;> nlinarith [h1.1, h1.2]

/-- The envelope property (12.AA.6) for player `i` from the one-sided bound
`π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)`: the reverse bound holds since
`π̂_i(q_j) ≥ π_i(q_i*, q_j)`. -/
theorem scl_env_of_upper {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs) {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (i j : Fin 2)
    (hij : j ≠ i) (hd : HasFDerivAt (g i) L qs)
    (hup : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs j),
      bestReplyValue g i (update qs j y) ≤ g i qs + L (Pi.single j 1) * (y - qs j) +
        ε * |y - qs j|) :
    HasDerivAt (fun y => bestReplyValue g i (update qs j y)) (L (Pi.single j 1)) (qs j) := by
  have hc := hd.comp_hasDerivAt_of_eq (qs j) (hasDerivAt_update qs j (qs j))
    (update_eq_self j qs).symm
  refine scl_hasDerivAt_squeeze hc (fun y => ?_) ?_ ?_ hup
  · have h1 := le_bestReplyValue hg i (update qs j y) (qs i)
    have e : update (update qs j y) i (qs i) = update qs j y := by
      rw [update_eq_self_iff, update_of_ne hij.symm]
    rw [e] at h1
    exact h1
  · simp only [update_eq_self]
    exact bestReplyValue_nash hg hqs i
  · simp only [comp_apply, update_eq_self]

/-- Conversely, the envelope property (12.AA.6) gives the one-sided bound. -/
theorem scl_upper_of_hasDerivAt {f : ℝ → ℝ} {a y₀ : ℝ} (hf : HasDerivAt f a y₀) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, f y ≤ f y₀ + a * (y - y₀) + ε * |y - y₀| := by
  intro ε hε
  filter_upwards [hf.isLittleO.bound hε] with y h1
  simp only [smul_eq_mul, Real.norm_eq_abs] at h1
  have := (abs_le.1 h1).2
  nlinarith

/-- `LocalGameData` from MWG's hypotheses plus the one-sided bounds on `π̂_1`, `π̂_2`. -/
noncomputable def sclLocalData {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs) {L0 L1 : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hd0 : HasFDerivAt (g 0) L0 qs) (hd1 : HasFDerivAt (g 1) L1 qs)
    (hc0 : L0 (Pi.single 1 1) ≠ 0) (hc1 : L1 (Pi.single 0 1) ≠ 0)
    (hup0 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 1),
      bestReplyValue g 0 (update qs 1 y) ≤ g 0 qs + L0 (Pi.single 1 1) * (y - qs 1) +
        ε * |y - qs 1|)
    (hup1 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 0),
      bestReplyValue g 1 (update qs 0 y) ≤ g 1 qs + L1 (Pi.single 0 1) * (y - qs 0) +
        ε * |y - qs 0|) :
    LocalGameData g qs where
  L0 := L0
  L1 := L1
  deriv0 := hd0
  deriv1 := hd1
  own0 := scl_own_partial_zero 0 hd0 hqs
  own1 := scl_own_partial_zero 1 hd1 hqs
  cross0 := hc0
  cross1 := hc1
  env0 := scl_env_of_upper hg hqs 0 1 (by decide) hd0 hup0
  env1 := scl_env_of_upper hg hqs 1 0 (by decide) hd1 hup1

/-- **Proposition 12.AA.1, corrected** (MWG, p. 419). Two players with actions in `ℝ`, bounded
payoffs, a stage Nash equilibrium `q*`, `π_i` differentiable at `q*` with
`∂π_i(q*)/∂q_j ≠ 0`, and the one-sided bound
`π̂_i(q_j) ≤ π_i(q*) + ∂π_i(q*)/∂q_j·(q_j − q_j*) + o(q_j − q_j*)` for `i = 1, 2`. Then for every
`δ ∈ (0, 1)` some `q'` with `π_i(q') > π_i(q*)` for both players is the stationary outcome path of
a Nash reversion SPNE. Without the one-sided bound the claim fails (`proposition_12_AA_1_false`).
-/
theorem proposition_12_AA_1_upper {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    {L0 L1 : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hd0 : HasFDerivAt (g 0) L0 qs) (hd1 : HasFDerivAt (g 1) L1 qs)
    (hc0 : L0 (Pi.single 1 1) ≠ 0) (hc1 : L1 (Pi.single 0 1) ≠ 0)
    (hup0 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 1),
      bestReplyValue g 0 (update qs 1 y) ≤ g 0 qs + L0 (Pi.single 1 1) * (y - qs 1) +
        ε * |y - qs 1|)
    (hup1 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 0),
      bestReplyValue g 1 (update qs 0 y) ≤ g 1 qs + L1 (Pi.single 0 1) * (y - qs 0) +
        ε * |y - qs 0|) :
    ∃ q', (∀ i, g i qs < g i q') ∧ IsRepeatedSPNE g δ (nashReversion (fun _ => q') qs) :=
  proposition_12_AA_1 hδ0 hδ1 hg hqs (sclLocalData hg hqs hd0 hd1 hc0 hc1 hup0 hup1)

/-- **Proposition 12.AA.4 and Exercise 12.AA.2, corrected** (MWG, pp. 421, 435). Under the
hypotheses of `proposition_12_AA_1_upper`, for every `δ ∈ (0, 1)` some stick-and-carrot SPNE gives
both players average payoffs `(1 − δ)v_i' < π_i(q*)`. (MWG's hypothesis `π_i(q*) > π̲_i` is not
needed.) Without the one-sided bound the claim fails (`proposition_12_AA_4_false`). -/
theorem proposition_12_AA_4_upper {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    {L0 L1 : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hd0 : HasFDerivAt (g 0) L0 qs) (hd1 : HasFDerivAt (g 1) L1 qs)
    (hc0 : L0 (Pi.single 1 1) ≠ 0) (hc1 : L1 (Pi.single 0 1) ≠ 0)
    (hup0 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 1),
      bestReplyValue g 0 (update qs 1 y) ≤ g 0 qs + L0 (Pi.single 1 1) * (y - qs 1) +
        ε * |y - qs 1|)
    (hup1 : ∀ ε > 0, ∀ᶠ y in 𝓝 (qs 0),
      bestReplyValue g 1 (update qs 0 y) ≤ g 1 qs + L1 (Pi.single 0 1) * (y - qs 0) +
        ε * |y - qs 0|) :
    ∃ q', (∀ i, g i q' < g i qs) ∧ IsRepeatedSPNE g δ (scProfile q' qs qs 0) ∧
      ∀ i, (1 - δ) * osValue (stageU g) δ (scProfile q' qs qs 0) [] i < g i qs :=
  proposition_12_AA_4 hδ0 hδ1 hg hqs (sclLocalData hg hqs hd0 hd1 hc0 hc1 hup0 hup1)

/-- The one-sided bounds hold in the game `locG` at `q* = 0`. -/
theorem scl_locG_upper :
    (∀ ε > 0, ∀ᶠ y in 𝓝 ((0 : Fin 2 → ℝ) 1),
      bestReplyValue locG 0 (update 0 1 y) ≤
        locG 0 0 + locG_data.L0 (Pi.single 1 1) * (y - (0 : Fin 2 → ℝ) 1) +
          ε * |y - (0 : Fin 2 → ℝ) 1|) ∧
    (∀ ε > 0, ∀ᶠ y in 𝓝 ((0 : Fin 2 → ℝ) 0),
      bestReplyValue locG 1 (update 0 0 y) ≤
        locG 1 0 + locG_data.L1 (Pi.single 0 1) * (y - (0 : Fin 2 → ℝ) 0) +
          ε * |y - (0 : Fin 2 → ℝ) 0|) := by
  have e : ∀ i j : Fin 2, bestReplyValue locG i (update 0 j ((0 : Fin 2 → ℝ) j)) = locG i 0 :=
    fun i j => by rw [update_eq_self]; exact bestReplyValue_nash locG_bound locG_nash i
  constructor
  · intro ε hε
    filter_upwards [scl_upper_of_hasDerivAt locG_data.env0 ε hε] with y hy
    rwa [e] at hy
  · intro ε hε
    filter_upwards [scl_upper_of_hasDerivAt locG_data.env1 ε hε] with y hy
    rwa [e] at hy

/-- **Proposition 12.AA.1, corrected, an instance**: `locG` with `δ = 1/2`. -/
theorem scl_upper_instance_1 :
    ∃ q', (∀ i, locG i 0 < locG i q') ∧
      IsRepeatedSPNE locG (1 / 2) (nashReversion (fun _ => q') 0) :=
  proposition_12_AA_1_upper (by norm_num) (by norm_num) locG_bound locG_nash locG_data.deriv0
    locG_data.deriv1 locG_data.cross0 locG_data.cross1 scl_locG_upper.1 scl_locG_upper.2

/-- **Proposition 12.AA.4, corrected, an instance**: `locG` with `δ = 1/2`. -/
theorem scl_upper_instance_4 :
    ∃ q', (∀ i, locG i q' < locG i 0) ∧ IsRepeatedSPNE locG (1 / 2) (scProfile q' 0 0 0) ∧
      ∀ i, (1 - 1 / 2) * osValue (stageU locG) (1 / 2) (scProfile q' 0 0 0) [] i < locG i 0 :=
  proposition_12_AA_4_upper (by norm_num) (by norm_num) locG_bound locG_nash locG_data.deriv0
    locG_data.deriv1 locG_data.cross0 locG_data.cross1 scl_locG_upper.1 scl_locG_upper.2

end MWG.MarketPower
