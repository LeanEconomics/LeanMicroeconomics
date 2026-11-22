/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.HiddenInfo
import MWGPrincipalAgent.ExampleHA
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A concrete hidden-information model

MWG, Section 14.C, pp. 489-499: a proved instance of the standing assumptions of `HiddenInfo`
in which the optimal contract of (14.C.8) exists and is computed.

`π(e) = log (1 + e)`, `g(e, θ) = e² exp(-θ) / 2`, `θ_L = log 2`, `θ_H = log 6`, `λ = 5/7`,
`v(w) = -exp(-w)`, `ū = -1` (so `v⁻¹(ū) = 0`). Then `e*_L = 1`, `e*_H = 2` (14.C.7), and the
optimal contract under hidden information has `e_H = 2`, `e_L = 1/2`, `w_L = 1/16`,
`w_H = 1/24 + 1/3 = 3/8` (Proposition 14.C.3).

* `exB_standing`: the standing assumptions hold.
* `exB_opt`: the optimal contract; `exB_proposition_14_C_3`, `exB_proposition_14_C_1`: instances.
-/

namespace MWG.PrincipalAgent

open Set

/-- `g(e, θ) = e² exp(-θ) / 2` is strictly convex in `e ≥ 0`. -/
theorem exB_g_conv (θ : ℝ) : StrictConvexOn ℝ (Ici 0) fun e : ℝ => e ^ 2 * Real.exp (-θ) / 2 := by
  refine ⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hk := Real.exp_pos (-θ)
  have hb' : b = 1 - a := by linarith
  subst hb'
  have hd : 0 < (x - y) ^ 2 := by positivity
  simp only [smul_eq_mul]
  have : (a * x + (1 - a) * y) ^ 2 < a * x ^ 2 + (1 - a) * y ^ 2 := by
    nlinarith [mul_pos (mul_pos ha hb) hd]
  have := mul_lt_mul_of_pos_right this hk
  nlinarith

/-- `log (1 + e)` has derivative `1 / (1 + e)` for `e > -1`. -/
theorem exB_log_deriv {e : ℝ} (he : 0 ≤ e) :
    HasDerivAt (fun e : ℝ => Real.log (1 + e)) (1 / (1 + e)) e := by
  have := ((hasDerivAt_id e).const_add 1).log (by simp; linarith)
  simpa using this

/-- `log (1 + e)` is strictly concave on `[0, ∞)`. -/
theorem exB_log_conc : StrictConcaveOn ℝ (Ici 0) fun e : ℝ => Real.log (1 + e) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) ?_ ?_
  · intro e he
    exact (exB_log_deriv (mem_Ici.1 he)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(exB_log_deriv (le_of_lt hx)).deriv, (exB_log_deriv (le_of_lt hy)).deriv]
    have hx' : (0:ℝ) < 1 + x := by linarith [mem_Ioi.1 hx]
    exact one_div_lt_one_div_of_lt hx' (by linarith)

/-- The concrete hidden-information model. -/
noncomputable def exB : HIModel where
  pH := fun e => Real.log (1 + e)
  pL := fun e => Real.log (1 + e)
  dpH := fun e => 1 / (1 + e)
  dpL := fun e => 1 / (1 + e)
  g := fun e θ => e ^ 2 * Real.exp (-θ) / 2
  ge := fun e θ => e * Real.exp (-θ)
  v := fun w => -Real.exp (-w)
  dv := fun w => Real.exp (-w)
  θL := Real.log 2
  θH := Real.log 6
  lam := 5 / 7
  ubar := -1
  c := 0

theorem exB_expL : Real.exp (-exB.θL) = 1 / 2 := by
  change Real.exp (-Real.log 2) = 1 / 2
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

theorem exB_expH : Real.exp (-exB.θH) = 1 / 6 := by
  change Real.exp (-Real.log 6) = 1 / 6
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- The standing assumptions of Section 14.C hold in `exB`. -/
theorem exB_standing : exB.Standing where
  pH_zero := by simp [exB]
  pL_zero := by simp [exB]
  pH_deriv e he := (exB_log_deriv he).hasDerivWithinAt
  pL_deriv e he := (exB_log_deriv he).hasDerivWithinAt
  dpL_pos e he := by change 0 < 1 / (1 + e); positivity
  dp_le _ _ := le_rfl
  pH_conc := exB_log_conc
  pL_conc := exB_log_conc
  g_zero θ := by simp [exB]
  g_deriv θ e _ := by
    have := ((hasDerivAt_pow 2 e).mul_const (Real.exp (-θ))).div_const 2
    refine HasDerivWithinAt.congr_deriv this.hasDerivWithinAt ?_
    change _ = e * Real.exp (-θ)
    push_cast; ring
  ge_zero θ := by simp [exB]
  g_conv θ := exB_g_conv θ
  θ_lt := Real.log_lt_log (by norm_num) (by norm_num)
  ge_cross e he := by
    change e * Real.exp (-exB.θH) < e * Real.exp (-exB.θL)
    rw [exB_expL, exB_expH]; linarith
  lam_pos := by norm_num [exB]
  lam_lt := by norm_num [exB]
  v_deriv := exA_hasDeriv
  dv_pos _ := Real.exp_pos _
  v_conc := exA_strictConcave
  v_c := by simp [exB]

theorem exB_focH : exB.dpH 2 = exB.ge 2 exB.θH := by
  change 1 / (1 + 2 : ℝ) = 2 * Real.exp (-exB.θH)
  rw [exB_expH]; norm_num

theorem exB_focL : exB.dpL 1 = exB.ge 1 exB.θL := by
  change 1 / (1 + 1 : ℝ) = 1 * Real.exp (-exB.θL)
  rw [exB_expL]; norm_num

/-- The virtual surplus of `exB`: `Q(e) = (2/7) log (1 + e) - 4 e² / 21`. -/
theorem exB_Q (e : ℝ) : exB.scr.Q e = 2 / 7 * Real.log (1 + e) - 4 * e ^ 2 / 21 := by
  change (1 - 5 / 7) * (Real.log (1 + e) - e ^ 2 * Real.exp (-exB.θL) / 2) -
    5 / 7 * (e ^ 2 * Real.exp (-exB.θL) / 2 - e ^ 2 * Real.exp (-exB.θH) / 2) = _
  rw [exB_expL, exB_expH]; ring

/-- `e = 1/2` maximizes the virtual surplus of `exB` on `[0, ∞)`. -/
theorem exB_Q_max (e : ℝ) (he : 0 ≤ e) : exB.scr.Q e ≤ exB.scr.Q (1 / 2) := by
  rw [exB_Q, exB_Q]
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (3 / 2) by positivity)
  rw [Real.log_div (by linarith) (by norm_num)] at h
  have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [this]
  nlinarith [sq_nonneg (2 * e - 1)]

/-- **The optimal contract of (14.C.8) in `exB`**: `e_H = e*_H = 2`, `e_L = 1/2`, with (i) and
(iii) binding. -/
theorem exB_opt : exB.scr.IsOpt (exB.scr.bind 2 (1 / 2)) := by
  have hH := (HIModel.hi_fbH_of_foc exB_standing (by norm_num) exB_focH).2
  have hL := (HIModel.hi_fbL_of_foc exB_standing (by norm_num) exB_focL).2
  refine (Screen.screen_opt_iff (HIModel.hi_hyp exB_standing) hH hL (by norm_num) _).2
    ⟨by change (0:ℝ) ≤ 1 / 2; norm_num, fun e he => exB_Q_max e he, rfl⟩

/-- An instance of **Proposition 14.C.3** (MWG, p. 499) in `exB`. -/
theorem exB_proposition_14_C_3 :
    (exB.scr.bind 2 (1 / 2)).eH = 2 ∧ 0 < (exB.scr.bind 2 (1 / 2)).eL ∧
      (exB.scr.bind 2 (1 / 2)).eL < 1 ∧
      exB.scr.Pi (exB.scr.bind 2 (1 / 2)) < exB.scr.FBval 2 1 := by
  obtain ⟨h1, h2, h3, -, -, h6⟩ := HIModel.proposition_14_C_3 exB_standing (by norm_num)
    exB_focH (by norm_num) exB_focL exB_opt
  exact ⟨h1, h2, h3, h6⟩

/-- An instance of **Proposition 14.C.1** (MWG, p. 492) in `exB`. -/
theorem exB_proposition_14_C_1 : exB.IsObsOpt (exB.fbK 2 1) :=
  (HIModel.proposition_14_C_1 exB_standing (by norm_num) exB_focH (by norm_num) exB_focL).1

end MWG.PrincipalAgent
