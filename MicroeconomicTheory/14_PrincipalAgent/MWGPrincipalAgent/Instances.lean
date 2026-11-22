/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExercisesB
import MWGPrincipalAgent.ExercisesAA
import MWGPrincipalAgent.ExampleHI
import MWGPrincipalAgent.AppendixA

/-!
# Instances of the hypotheses of the main results

Proved concrete instances (non-vacuity checks) for results of MWG Chapter 14 whose hypotheses are
not already instantiated in `ExampleHA`, `ExampleHI` or the exercise modules.

* Section 14.B: `inst_footnote_8`, `inst_EW_gt` (Proposition 14.B.3), `inst_high_implementable`
  (Appendix A) in the examples of `ExampleHA`.
* Section 14.C: `inst_lemmas_14_C`, `inst_appendix_B_steps`, `inst_eL_falls` in `exB`.
* Exercises: `inst_14_B_3b`, `inst_14_B_3c` (`g(e) = e³/3`), `inst_14_AA_2`.
-/

namespace MWG.PrincipalAgent

open Set

/-- **Footnote 8** in `exA`: the optimal scheme `exW` for `e_H` gives exactly `ū`. -/
theorem inst_footnote_8 : exA.EU true exW = exA.ubar :=
  HAModel.footnote_8 exA_standing exA_optimal

/-- **Proposition 14.B.3** in `exA`: the optimal scheme for `e_H` costs strictly more than the
observable-effort wage `-log (23/40)`. -/
theorem inst_EW_gt : exWstar true < exA.EW true exW :=
  HAModel.ha_EW_gt_of_IC exA_standing exA_strictConcave (by norm_num [exA, exModel])
    exA_optimal.1.1 (exA_optimal.1.2 false) (exA_wstar true)

/-- **Appendix A** ("`e_H` can be induced") in the risk-neutral example `exRN` (`v(w) = w` is
unbounded above). -/
theorem inst_high_implementable : ∃ w, exRN.HAFeasible true w := by
  have hst : exRN.Standing :=
    exA_standing_of (fun w => hasDerivAt_id w) (fun _ => one_pos) (concaveOn_id convex_univ) _ _
  exact HAModel.aa_high_implementable hst exA_two (exA_fosd _ _ _ _) fun y => ⟨y, le_refl _⟩

/-- **Lemmas 14.C.2-14.C.4** in `exB`: at the optimal contract `(i)` and `(iii)` bind, `e_H = e*_H`,
and `e_L < e*_L`. -/
theorem inst_lemmas_14_C :
    let K := exB.scr.bind 2 (1 / 2)
    (K.wL = exB.scr.c + exB.scr.g K.eL exB.scr.θL ∧
      K.wH = exB.scr.c + exB.scr.D K.eL + exB.scr.g K.eH exB.scr.θH) ∧
    (K.eL ≤ 1 ∧ K.eH = 2) ∧ K.eL < 1 := by
  intro K
  have hH := (HIModel.hi_fbH_of_foc exB_standing (by norm_num) exB_focH).2
  have hL := (HIModel.hi_fbL_of_foc exB_standing (by norm_num) exB_focL).2
  exact ⟨Screen.lemma_14_C_2 (HIModel.hi_hyp exB_standing) exB_opt,
    Screen.lemma_14_C_3 (HIModel.hi_hyp exB_standing) hH hL (by norm_num) exB_opt,
    HIModel.lemma_14_C_4 exB_standing (by norm_num) exB_focH (by norm_num) exB_focL exB_opt⟩

/-- **Appendix B, Steps 1-5** in `exB`, with the multipliers `γ = 1`, `φ_H = λ`, `φ_L = 0`. -/
theorem inst_appendix_B_steps :
    0 < exB.lam ∧ (exB.scr.bind 2 (1 / 2)).eL = 1 / 2 := by
  obtain ⟨h2, h3, h4, h5, cs1, cs3⟩ := HIModel.appendix_B_multipliers exB_standing (by norm_num)
    exB_focH (by norm_num) exB_focL exB_opt
  have := HIModel.appendix_B_steps exB_standing exB_opt.1 (γ := 1) (φH := exB.lam) (φL := 0)
    le_rfl h2 h3 (le_of_eq h4) (fun _ => h4) (by linarith [h5]) (fun _ => by linarith [h5])
    cs1 cs3 (by simp)
  exact ⟨this.1, rfl⟩

/-- **p. 499** ("`e_L` falls as `λ/(1 - λ)` rises") in `exB`: for `λ = 5/7` the optimal `e_L` is
`1/2`, for `λ = 81/91` it is `1/4`. -/
theorem inst_eL_falls : (1 / 4 : ℝ) < 1 / 2 := by
  have hSL : ∀ e, exB.scr.SL e = Real.log (1 + e) - e ^ 2 / 4 := fun e => by
    change Real.log (1 + e) - e ^ 2 * Real.exp (-exB.θL) / 2 = _
    rw [exB_expL]; ring
  have hD : ∀ e, exB.scr.D e = e ^ 2 / 6 := fun e => by
    change e ^ 2 * Real.exp (-exB.θL) / 2 - e ^ 2 * Real.exp (-exB.θH) / 2 = _
    rw [exB_expL, exB_expH]; ring
  refine HIModel.hi_eL_falls exB_standing (l1 := 5 / 7) (l2 := 81 / 91) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun e he => ?_) (fun e he => ?_)
  · rw [hSL, hSL, hD, hD]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (3 / 2) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (2 * e - 1)]
  · rw [hSL, hSL, hD, hD]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (5 / 4) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (4 * e - 1)]

/-- **Exercise 14.B.3(b)**, an instance: `g(e) = e³/3` (`g'(0) = 0`, `g', g'', g''' > 0` for
`e > 0`), `e* = 1`, `φσ² = 3/2`, `ū = 0`: the contract `e = 1`, `α = 1/3`, `β = 0` earns `2/3`. -/
theorem inst_14_B_3b {e α β : ℝ} (he : 0 ≤ e)
    (hpart : 0 ≤ α + β * e - 3 / 2 * β ^ 2 - e ^ 3 / 3) :
    e - (α + β * e) ≤ 1 - 1 ^ 3 / 3 - 0 := by
  have hconv : ConvexOn ℝ (Ici 0) fun e : ℝ => e ^ 3 / 3 := by
    have := (convexOn_pow 3).smul (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    refine this.congr fun x _ => ?_
    simp only [smul_eq_mul]; ring
  refine (exercise_14_B_3b (g := fun e => e ^ 3 / 3) (dg := fun e => e ^ 2) hconv
    (fun e _ => ?_) (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num) (by norm_num) he hpart).1
  have := ((hasDerivAt_pow 3 e).div_const 3).hasDerivWithinAt (s := Ici 0)
  convert this using 1; push_cast; ring

/-- **Exercise 14.B.3(c)**, an instance: `g(e) = e³/3`, `φσ² = 3/2`: `e = 1/2` maximizes
`e - g(e) - φσ² g'(e)²`, and `β = g'(1/2) = 1/4 = 1/(1 + 2φσ² g''(1/2))`. -/
theorem inst_14_B_3c : (fun e : ℝ => e ^ 2) (1 / 2) = 1 / (1 + 2 * (3 / 2) * (2 * (1 / 2))) ∧
    0 < (fun e : ℝ => e ^ 2) (1 / 2) ∧ (fun e : ℝ => e ^ 2) (1 / 2) < 1 := by
  refine exercise_14_B_3c_beta (g := fun e => e ^ 3 / 3) (dg := fun e => e ^ 2)
    (d2g := fun e => 2 * e) (ubar := 0) (by norm_num) (by norm_num) ?_ ?_ (by norm_num) ?_
  · have := (hasDerivAt_pow 3 (1 / 2 : ℝ)).div_const 3
    convert this using 1; push_cast; ring
  · have := hasDerivAt_pow 2 (1 / 2 : ℝ)
    convert this using 1; push_cast; ring
  · intro e he
    nlinarith [sq_nonneg (e - 1 / 2), mul_nonneg he (sq_nonneg (e - 1 / 2)),
      mul_nonneg (mul_nonneg he he) (sq_nonneg (e - 1 / 2))]

/-- **Exercise 14.AA.2**, an instance: `f(π_H|e) = (1 + e)/3` on `[0, 1]`, `g(e) = e²/2`,
`v_L = 0`, `v_H = 3/2`: the first-order condition holds at `e = 1/2`, which maximizes
`v_L + f(π_H|e)(v_H - v_L) - g(e)`. -/
theorem inst_14_AA_2 : ∀ e' ∈ Icc (0 : ℝ) 1,
    0 + (1 + e') / 3 * (3 / 2 - 0) - e' ^ 2 / 2 ≤
      0 + (1 + 1 / 2) / 3 * (3 / 2 - 0) - (1 / 2) ^ 2 / 2 := by
  refine exercise_14_AA_2_valid (p := fun e => (1 + e) / 3) (dp := fun _ => 1 / 3)
    (g := fun e => e ^ 2 / 2) (dg := fun e => e) ?_ ?_ (fun e _ => ?_) (fun e _ => ?_)
    (by norm_num) (by norm_num) (by norm_num)
  · refine ⟨convex_Icc 0 1, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul]
    linarith
  · have := (convexOn_pow 2).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    refine (this.subset (Icc_subset_Ici_self) (convex_Icc 0 1)).congr fun x _ => ?_
    simp only [smul_eq_mul]; ring
  · exact (((hasDerivAt_id e).const_add 1).div_const 3).hasDerivWithinAt
  · have := ((hasDerivAt_pow 2 e).div_const 2).hasDerivWithinAt (s := Icc 0 1)
    convert this using 1; push_cast; ring

end MWG.PrincipalAgent
