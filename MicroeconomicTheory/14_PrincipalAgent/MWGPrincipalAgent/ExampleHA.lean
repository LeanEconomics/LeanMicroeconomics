/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.RiskAverse
import MWGPrincipalAgent.Discrete
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential

/-!
# Concrete hidden-action models

MWG, Section 14.B, pp. 479-487: proved instances of the hypotheses of the results of
`HiddenAction` and `RiskAverse`, and the example behind Figure 14.B.1.

Three profit levels `0, 1, 2` (footnote 6), effort `true = e_H`, `false = e_L`, densities
`f(·|e_L) = (1/2, 1/4, 1/4)` and `f(·|e_H) = (1/4, 1/2, 1/4)`, and `v(w) = -exp(-w)`.

* `exA_standing`, `exA_fosd`: the standing assumptions and strict first-order stochastic
  dominance hold.
* `exA_not_mlrp`, `exA_optimal`, `exA_not_monotone`: **Figure 14.B.1** (p. 486): first-order
  stochastic dominance without the monotone likelihood ratio property, and the optimal incentive
  scheme for `e_H` (from footnote 7 with `γ = 2`, `μ = 1`) is not monotone in profits.
* `exA_lemma_14_B_1`, `exA_proposition_14_B_1`, `exA_welfare_loss`: instances of Lemma 14.B.1,
  Proposition 14.B.1 and the welfare loss of Proposition 14.B.3.
* `exA_tie`: with a tie under observability, `e_H` is an optimal observable effort and yet
  unobservability causes no loss (correction to the wording of Proposition 14.B.3).
* `exA_proposition_14_B_2`: an instance of Proposition 14.B.2 (risk-neutral manager).
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- The profit levels `0, 1, 2`. -/
def exPts : Fin 3 → ℝ := ![0, 1, 2]

/-- The densities: `f(·|e_L)` interpolates `(1/2, 1/4, 1/4)` and `f(·|e_H)` interpolates
`(1/4, 1/2, 1/4)` at the profit levels `0, 1, 2`, positively on all of `ℝ`. -/
noncomputable def exF (b : Bool) (x : ℝ) : ℝ :=
  if b then (1 + x ^ 2 * (2 - x) ^ 2) / 4 else (x ^ 2 - 3 * x + 4) / 8

/-- The family of example models: utility `v` with derivative `dv`, `g(e_L) = 0`, `g(e_H) = gH`
and reservation utility `u`. -/
noncomputable def exModel (v dv : ℝ → ℝ) (gH u : ℝ) : HAModel Bool where
  ν := dmeas exPts
  f := exF
  v := v
  dv := dv
  g := fun b => if b then gH else 0
  ubar := u

/-- Integrals in the example models are sums over the three profit levels. -/
theorem exA_integral (F : ℝ → ℝ) : ∫ x, F x ∂dmeas exPts = F 0 + F 1 + F 2 := by
  rw [dmeas_integral, Fin.sum_univ_three]; simp [exPts]

/-- The example models satisfy the standing assumptions whenever `v` does. -/
theorem exA_standing_of {v dv : ℝ → ℝ} (hv : ∀ w, HasDerivAt v (dv w) w) (hdv : ∀ w, 0 < dv w)
    (hc : ConcaveOn ℝ univ v) (gH u : ℝ) : (exModel v dv gH u).Standing where
  f_meas b := by
    cases b
    · change Measurable fun x => (x ^ 2 - 3 * x + 4) / 8
      fun_prop
    · change Measurable fun x : ℝ => (1 + x ^ 2 * (2 - x) ^ 2) / 4
      fun_prop
  f_pos b x := by
    cases b
    · change 0 < (x ^ 2 - 3 * x + 4) / 8
      nlinarith [sq_nonneg (x - 3 / 2)]
    · change 0 < (1 + x ^ 2 * (2 - x) ^ 2) / 4
      positivity
  f_int _ := dmeas_integrable _ _
  f_one b := by
    change ∫ x, exF b x ∂dmeas exPts = 1
    rw [exA_integral]; cases b <;> simp [exF] <;> norm_num
  x_int _ := dmeas_integrable _ _
  v_deriv := hv
  dv_pos := hdv
  v_conc := hc

/-- `v(w) = -exp(-w)` has derivative `exp(-w)`. -/
theorem exA_hasDeriv (w : ℝ) : HasDerivAt (fun w => -Real.exp (-w)) (Real.exp (-w)) w := by
  have := (hasDerivAt_neg w).exp.neg
  convert this using 1
  ring

/-- `v(w) = -exp(-w)` is strictly concave. -/
theorem exA_strictConcave : StrictConcaveOn ℝ univ fun w => -Real.exp (-w) := by
  have hd : deriv (fun w => -Real.exp (-w)) = fun w => Real.exp (-w) :=
    funext fun w => (exA_hasDeriv w).deriv
  refine StrictAnti.strictConcaveOn_univ_of_deriv (by fun_prop) ?_
  rw [hd]
  exact fun a b hab => Real.exp_lt_exp.2 (neg_lt_neg hab)

/-- The main example: `v(w) = -exp(-w)`, `g(e_H) = 3/20`, `ū = -29/40`. -/
noncomputable def exA : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) (3 / 20) (-29 / 40)

/-- The standing assumptions hold in `exA`. -/
theorem exA_standing : exA.Standing :=
  exA_standing_of exA_hasDeriv (fun _ => Real.exp_pos _) exA_strictConcave.concaveOn _ _

/-- In `exA` the manager is strictly risk averse: `v'(w) = exp(-w)` is strictly decreasing. -/
theorem exA_dv_anti : StrictAnti exA.dv := fun _ _ hab => Real.exp_lt_exp.2 (neg_lt_neg hab)

/-- The two effort levels. -/
theorem exA_two (b : Bool) : b = false ∨ b = true := by cases b <;> simp

/-- Strict first-order stochastic dominance holds in the example models. -/
theorem exA_fosd (v dv : ℝ → ℝ) (gH u : ℝ) : (exModel v dv gH u).FOSD true false := by
  have hF : ∀ b x, (exModel v dv gH u).F b x = ∑ i, (Iic x).indicator (exF b) (exPts i) :=
    fun b x => dmeas_setIntegral _ measurableSet_Iic _
  refine ⟨fun x => ?_, 0, ?_⟩
  · rw [hF, hF]
    simp only [Fin.sum_univ_three, indicator, mem_Iic]
    simp only [exPts, exF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    split_ifs <;> norm_num <;> linarith
  · rw [hF, hF]
    simp only [Fin.sum_univ_three, indicator, mem_Iic]
    simp only [exPts, exF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    norm_num

/-- **Figure 14.B.1(a)-(b)** (MWG, pp. 485-486). First-order stochastic dominance does not imply
the monotone likelihood ratio property: `f(π|e_L) / f(π|e_H)` is `2, 1/2, 1` at `π = 0, 1, 2`. -/
theorem exA_not_mlrp : ¬ Antitone fun x => exA.f false x / exA.f true x := by
  intro h
  have := h (show (1 : ℝ) ≤ 2 by norm_num)
  change exF false 2 / exF true 2 ≤ exF false 1 / exF true 1 at this
  simp only [exF] at this
  norm_num at this

/-- The optimal incentive scheme for `e_H` in `exA`: `w = 0, log (5/2), log 2` at `π = 0, 1, 2`. -/
noncomputable def exW (x : ℝ) : ℝ :=
  if x < 1 / 2 then 0 else if x < 3 / 2 then Real.log (5 / 2) else Real.log 2

/-- `exW` is admissible. -/
theorem exW_adm : exA.Adm exW := by
  refine ⟨?_, fun _ => ⟨dmeas_integrable _ _, dmeas_integrable _ _⟩⟩
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      measurable_const)

theorem exW_zero : exW 0 = 0 := by norm_num [exW]

theorem exW_one : exW 1 = Real.log (5 / 2) := by norm_num [exW]

theorem exW_two : exW 2 = Real.log 2 := by norm_num [exW]

/-- The manager's expected utilities under `exW`: both equal `ū = -29/40`. -/
theorem exA_EU : exA.EU true exW = -29 / 40 ∧ exA.EU false exW = -29 / 40 := by
  have h1 : Real.exp (-Real.log (5 / 2)) = 2 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hc : ∀ b : Bool, exA.EU b exW = ∫ x, -Real.exp (-exW x) * exF b x ∂dmeas exPts -
      (if b then 3 / 20 else 0) := fun _ => rfl
  rw [hc, hc, exA_integral, exA_integral, exW_zero, exW_one, exW_two, h1, h2]
  simp only [exF]
  norm_num

/-- (14.B.10) holds for `exW` with `γ = 2`, `μ = 1` at every profit level of `exA`. -/
theorem exA_foc : ∀ᵐ x ∂exA.ν, 1 / exA.dv (exW x) = 2 + 1 * (1 - exA.f false x / exA.f true x) := by
  refine dmeas_ae _ fun i => ?_
  change 1 / Real.exp (-exW (exPts i)) = 2 + 1 * (1 - exF false (exPts i) / exF true (exPts i))
  fin_cases i <;> simp only [exPts, exF] <;> norm_num [exW_zero, exW_one, exW_two, Real.exp_neg,
    Real.exp_log]

/-- **Figure 14.B.1(c)** (MWG, p. 486) and footnote 7. `exW` is the optimal incentive scheme for
implementing `e_H` in `exA`. -/
theorem exA_optimal : exA.IsHACostMin true exW := by
  obtain ⟨h1, h2⟩ := exA_EU
  refine HAModel.ha_kt_sufficient exA_standing exA_two exW_adm (by norm_num) (by norm_num)
    exA_foc ?_ ?_ ?_ ?_
  · rw [h1]; exact le_refl _
  · rw [h1, h2]
  · rw [h1]; change (2 : ℝ) * (-29 / 40 - -29 / 40) = 0; ring
  · rw [h1, h2]; ring

/-- **Figure 14.B.1(c)** (MWG, pp. 485-486). The optimal incentive scheme is not monotone in
profits: it pays more at `π = 1` than at `π = 2`. -/
theorem exA_not_monotone : ¬ Monotone exW := by
  intro h
  have := h (show (1 : ℝ) ≤ 2 by norm_num)
  rw [exW_one, exW_two] at this
  have := Real.log_lt_log (by norm_num) (show (2 : ℝ) < 5 / 2 by norm_num)
  linarith

/-- An instance of all the hypotheses of **Lemma 14.B.1** (MWG, p. 484). -/
theorem exA_lemma_14_B_1 : (0 : ℝ) < 2 ∧ (0 : ℝ) < 1 := by
  obtain ⟨h1, h2⟩ := exA_EU
  exact HAModel.lemma_14_B_1 exA_standing (exA_fosd _ _ _ _) (by norm_num [exA, exModel])
    exA_dv_anti (by rw [h1, h2]) (by norm_num) (by norm_num) exA_foc

/-- The fixed wages of (14.B.4) in `exA`: `w*_{e_L} = -log (29/40)`, `w*_{e_H} = -log (23/40)`. -/
noncomputable def exWstar (b : Bool) : ℝ := if b then -Real.log (23 / 40) else -Real.log (29 / 40)

theorem exA_wstar (b : Bool) : exA.v (exWstar b) = exA.ubar + exA.g b := by
  change -Real.exp (-exWstar b) = -29 / 40 + (if b then 3 / 20 else 0)
  cases b <;> simp only [exWstar] <;> norm_num [Real.exp_log]

/-- Expected gross profits in the example models: `3/4` under `e_L` and `1` under `e_H`. -/
theorem exA_GP (v dv : ℝ → ℝ) (gH u : ℝ) (b : Bool) :
    (exModel v dv gH u).GP b = if b then 1 else 3 / 4 := by
  change ∫ x, x * exF b x ∂dmeas exPts = _
  rw [exA_integral]; cases b <;> simp [exF] <;> norm_num

/-- With observable effort, `e_H` is strictly better than `e_L` in `exA`:
`1 + log (23/40) > 3/4 + log (29/40)`. -/
theorem exA_fb_strict : exA.GP false - exWstar false < exA.GP true - exWstar true := by
  rw [exA, exA_GP, exA_GP]
  simp only [exWstar, Bool.false_eq_true, ↓reduceIte]
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hlog : Real.log (29 / 23) < 1 / 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; linarith
  have : Real.log (29 / 40) - Real.log (23 / 40) = Real.log (29 / 23) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  linarith

/-- An instance of **Proposition 14.B.1** (MWG, p. 481): in `exA` the optimal contract with
observable effort specifies `e_H` and the fixed wage `-log (23/40)`. -/
theorem exA_proposition_14_B_1 : exA.IsObsOptimal true (fun _ => exWstar true) := by
  refine HAModel.proposition_14_B_1 exA_standing exA_wstar fun e => ?_
  rcases exA_two e with rfl | rfl
  · exact exA_fb_strict.le
  · exact le_rfl

/-- An instance of the **welfare loss in Proposition 14.B.3** (MWG, p. 487): in `exA` every
contract feasible under unobservable effort gives the owner strictly less than the observable
optimum. -/
theorem exA_welfare_loss {e : Bool} {w : ℝ → ℝ} (hw : exA.HAFeasible e w) :
    exA.OP e w < exA.GP true - exWstar true :=
  HAModel.ha_welfare_loss exA_standing exA_strictConcave exA_two (by norm_num [exA, exModel])
    (exA_wstar false) (exA_wstar true) exA_fb_strict hw

/-- The tie model: `g(e_H) = 1 - exp(-1/4)`, `ū = -1`, so `w*_{e_L} = 0` and `w*_{e_H} = 1/4`. -/
noncomputable def exTie : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) (1 - Real.exp (-(1 / 4))) (-1)

/-- **Correction to Proposition 14.B.3** (MWG, p. 487). In `exTie` the effort `e_H` is optimal
when effort is observable (it ties with `e_L`), and still unobservability causes no welfare loss:
a contract feasible under unobservable effort attains the observable-effort optimum. -/
theorem exA_tie :
    exTie.IsObsOptimal true (fun _ => 1 / 4) ∧ ∃ e w, exTie.HAFeasible e w ∧
      exTie.OP e w = exTie.OP true (fun _ => 1 / 4) := by
  have hst : exTie.Standing :=
    exA_standing_of exA_hasDeriv (fun _ => Real.exp_pos _) exA_strictConcave.concaveOn _ _
  have hws : ∀ b, exTie.v (if b then 1 / 4 else 0) = exTie.ubar + exTie.g b := by
    intro b
    change -Real.exp (-(if b then (1 / 4 : ℝ) else 0)) = -1 + (if b then 1 - Real.exp (-(1 / 4))
      else 0)
    cases b
    · simp
    · simp only [↓reduceIte]; ring
  have hGP : ∀ b, exTie.GP b = if b then 1 else 3 / 4 := exA_GP _ _ _ _
  have hopt : exTie.IsObsOptimal true (fun _ => 1 / 4) := by
    have := HAModel.proposition_14_B_1 hst hws (estar := true) fun e => by
      rcases exA_two e with rfl | rfl
      · simp only [hGP]; norm_num
      · exact le_rfl
    simpa using this
  obtain ⟨hfeas, hOP⟩ := HAModel.ha_no_loss_of_tie hst exA_two
    (show exTie.g false < exTie.g true by
      change (0 : ℝ) < 1 - Real.exp (-(1 / 4))
      have := Real.exp_lt_one_iff.2 (show -(1 / 4 : ℝ) < 0 by norm_num); linarith)
    (wH := 1 / 4) (hws false) (by simp [hGP]; norm_num)
  refine ⟨hopt, false, _, hfeas, ?_⟩
  rw [hOP, HAModel.ha_OP_eq hst (HAModel.ha_const_adm hst _), HAModel.ha_EW_const hst]

/-- The risk-neutral example: `v(w) = w`, `g(e_H) = 1/10`, `ū = 0`. -/
noncomputable def exRN : HAModel Bool := exModel id (fun _ => 1) (1 / 10) 0

/-- An instance of **Proposition 14.B.2** (MWG, p. 482): in `exRN`, selling the project for
`α* = 9/10` implements `e_H` optimally. -/
theorem exA_proposition_14_B_2 :
    exRN.IsHAOptimal true (fun x => x - (exRN.GP true - exRN.g true - exRN.ubar)) := by
  have hst : exRN.Standing :=
    exA_standing_of (fun w => hasDerivAt_id w) (fun _ => one_pos) (concaveOn_id convex_univ) _ _
  have hGP : ∀ b, exRN.GP b = if b then 1 else 3 / 4 := exA_GP _ _ _ _
  refine (HAModel.proposition_14_B_2 hst (fun _ => rfl) fun e => ?_).1
  rcases exA_two e with rfl | rfl
  · rw [hGP, hGP]; simp [exRN, exModel]; norm_num
  · exact le_rfl

end MWG.PrincipalAgent
