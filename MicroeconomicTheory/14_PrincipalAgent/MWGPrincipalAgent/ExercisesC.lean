/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExampleHI
import MWGAdverseSelection.ExercisesD1

/-!
# Exercises 14.C.2, 14.C.3, 14.C.5, 14.C.6

MWG, pp. 508-509.

* `exercise_14_C_2`: a risk-neutral manager; selling the project (`w(π) = π - α`) attains the
  observable-state payoff, and the revelation mechanism `(π(e*_i) - α, e*_i)` gives the same
  outcome.
* `exercise_14_C_3a`, `exercise_14_C_3a_suff`, `exercise_14_C_3b`: utility `v(w) - g(e, θ)`. Every
  optimal full-information contract pays the same wage in both states (so the manager's utility
  differs across states); the first-order conditions are sufficient; the full-information contract
  violates the truth-telling constraint of state `θ_H` when `e_L < e_H`.
* Exercise 14.C.5 is `HIModel` with `π_H ≠ π_L` (Section 14.C results hold when
  `π'_H ≥ π'_L > 0`); `exercise_14_C_5_reversal`: when `π'_H < π'_L` the first-best efforts can be
  reversed and the solution of the program without (iv) violates (iv).
* `exercise_14_C_6`, `exercise_14_C_6_instance`: the monopsony version of Exercise 13.D.1: the
  high type's task is efficient, the low type's is distorted down, below the competitive one.
-/

namespace MWG.PrincipalAgent

open Set

/-! ### Exercise 14.C.2 -/

/-- **Exercise 14.C.2** (MWG, p. 508). Hidden information with a risk-neutral manager
(`v(w) = w`). Let `e*_i` maximize `S_i(e) = π(e) - g(e, θ_i)` on `[0, ∞)` and
`α* = λ S_H(e*_H) + (1 - λ) S_L(e*_L) - ū`. Under `w(π) = π - α*` the manager in state `θ_i` chooses
`e*_i` (any optimal choice gives the full-information surplus), his expected utility is `ū`, and the
owner gets `α*`, which is the most he can get even when `θ` is observable. The revelation mechanism
`(π(e*_i) - α*, e*_i)` is truthful and gives the same outcome. -/
theorem exercise_14_C_2 (prof : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {θL θH lam ubar eHs eLs : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hH0 : 0 ≤ eHs) (hL0 : 0 ≤ eLs)
    (hH : ∀ e, 0 ≤ e → prof e - g e θH ≤ prof eHs - g eHs θH)
    (hL : ∀ e, 0 ≤ e → prof e - g e θL ≤ prof eLs - g eLs θL) :
    let α := lam * (prof eHs - g eHs θH) + (1 - lam) * (prof eLs - g eLs θL) - ubar
    -- the manager's choices under the sellout
    (∀ e, 0 ≤ e → prof e - α - g e θH ≤ prof eHs - α - g eHs θH) ∧
    (∀ e, 0 ≤ e → prof e - α - g e θL ≤ prof eLs - α - g eLs θL) ∧
    lam * (prof eHs - α - g eHs θH) + (1 - lam) * (prof eLs - α - g eLs θL) = ubar ∧
    -- the owner's payoff `α` is the observable-state optimum
    (∀ wH eH wL eL : ℝ, 0 ≤ eH → 0 ≤ eL →
      ubar ≤ lam * (wH - g eH θH) + (1 - lam) * (wL - g eL θL) →
      lam * (prof eH - wH) + (1 - lam) * (prof eL - wL) ≤ α) ∧
    -- the revelation mechanism
    (prof eHs - α - g eHs θH ≥ prof eLs - α - g eLs θH ∧
      prof eLs - α - g eLs θL ≥ prof eHs - α - g eHs θL) := by
  intro α
  refine ⟨fun e he => by linarith [hH e he], fun e he => by linarith [hL e he],
    by simp only [α]; ring, fun wH eH wL eL h1 h2 h3 => ?_, ?_, ?_⟩
  · have a := mul_le_mul_of_nonneg_left (hH eH h1) hl0
    have b := mul_le_mul_of_nonneg_left (hL eL h2) (by linarith : (0:ℝ) ≤ 1 - lam)
    simp only [α]; nlinarith
  · linarith [hH eLs hL0]
  · linarith [hL eHs hH0]

/-! ### Exercise 14.C.3 -/

/-- **Exercise 14.C.3(a)** (MWG, p. 509), full insurance. With utility `v(w) - g(e, θ)`, `v`
strictly concave and strictly increasing and continuous, every optimal full-information contract
pays the same wage in both states: otherwise paying the certainty equivalent `w̄` with
`v(w̄) = λ v(w_H) + (1 - λ) v(w_L)` in both states keeps the constraint and is cheaper. -/
theorem exercise_14_C_3a {v : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v) (hmono : StrictMono v)
    (hcont : Continuous v) (prof : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {θL θH lam ubar : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) {wH eH wL eL : ℝ}
    (hfeas : ubar ≤ lam * (v wH - g eH θH) + (1 - lam) * (v wL - g eL θL))
    (hopt : ∀ wH' wL', ubar ≤ lam * (v wH' - g eH θH) + (1 - lam) * (v wL' - g eL θL) →
      lam * (prof eH - wH') + (1 - lam) * (prof eL - wL') ≤
        lam * (prof eH - wH) + (1 - lam) * (prof eL - wL)) : wH = wL := by
  by_contra hne
  -- the certainty equivalent
  set t := lam * v wH + (1 - lam) * v wL
  have hJ := tpa_jensen_two_lt hv hl0 hl1 hne
  obtain ⟨wbar, hwbar⟩ : ∃ wbar, v wbar = t := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hlo : v wH ≤ t := by
        have := hmono h; simp only [t]; nlinarith
      have hhi : t ≤ v wL := by
        have := hmono h; simp only [t]; nlinarith
      obtain ⟨c, hc, hct⟩ := intermediate_value_Icc h.le hcont.continuousOn ⟨hlo, hhi⟩
      exact ⟨c, hct⟩
    · have hlo : v wL ≤ t := by
        have := hmono h; simp only [t]; nlinarith
      have hhi : t ≤ v wH := by
        have := hmono h; simp only [t]; nlinarith
      obtain ⟨c, hc, hct⟩ := intermediate_value_Icc h.le hcont.continuousOn ⟨hlo, hhi⟩
      exact ⟨c, hct⟩
  have hlt : wbar < lam * wH + (1 - lam) * wL := hmono.lt_iff_lt.1 (by rw [hwbar]; exact hJ)
  have := hopt wbar wbar (by rw [hwbar]; simp only [t] at *; nlinarith)
  nlinarith

/-- **Exercise 14.C.3(a)** (MWG, p. 509), sufficiency of the first-order conditions. With `π`
concave, `g(·, θ)` convex and `v` concave and increasing, a contract `(w̄, e_H, w̄, e_L)` with
binding constraint and `π'(e_i) v'(w̄) = g_e(e_i, θ_i)` is an optimal full-information contract. -/
theorem exercise_14_C_3a_suff {v dv prof dprof : ℝ → ℝ} {g ge : ℝ → ℝ → ℝ} {θL θH lam ubar : ℝ}
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hv : ConcaveOn ℝ univ v) (hdv : ∀ w, HasDerivAt v (dv w) w)
    (hdvpos : ∀ w, 0 < dv w) (hp : ConcaveOn ℝ (Ici 0) prof)
    (hdp : ∀ e, 0 ≤ e → HasDerivWithinAt prof (dprof e) (Ici 0) e)
    (hg : ∀ θ, ConvexOn ℝ (Ici 0) fun e => g e θ)
    (hdg : ∀ θ e, 0 ≤ e → HasDerivWithinAt (fun e => g e θ) (ge e θ) (Ici 0) e)
    {wbar eH eL : ℝ} (hH0 : 0 ≤ eH) (hL0 : 0 ≤ eL)
    (hbind : lam * (v wbar - g eH θH) + (1 - lam) * (v wbar - g eL θL) = ubar)
    (hfH : dprof eH * dv wbar = ge eH θH) (hfL : dprof eL * dv wbar = ge eL θL)
    {wH' eH' wL' eL' : ℝ} (hH0' : 0 ≤ eH') (hL0' : 0 ≤ eL')
    (hfeas : ubar ≤ lam * (v wH' - g eH' θH) + (1 - lam) * (v wL' - g eL' θL)) :
    lam * (prof eH' - wH') + (1 - lam) * (prof eL' - wL') ≤
      lam * (prof eH - wbar) + (1 - lam) * (prof eL - wbar) := by
  have hd := hdvpos wbar
  have tH := tpa_tangent_le hp (mem_Ici.2 hH0) (mem_Ici.2 hH0') (hdp eH hH0)
  have tL := tpa_tangent_le hp (mem_Ici.2 hL0) (mem_Ici.2 hL0') (hdp eL hL0)
  have gH := tpa_tangent_ge_convex (hg θH) (mem_Ici.2 hH0) (mem_Ici.2 hH0') (hdg θH eH hH0)
  have gL := tpa_tangent_ge_convex (hg θL) (mem_Ici.2 hL0) (mem_Ici.2 hL0') (hdg θL eL hL0)
  have vH := tpa_tangent_le hv (mem_univ wbar) (mem_univ wH') (hdv wbar).hasDerivWithinAt
  have vL := tpa_tangent_le hv (mem_univ wbar) (mem_univ wL') (hdv wbar).hasDerivWithinAt
  -- multiply the profit tangents by `v'(w̄) > 0`
  have key : dv wbar * (lam * (prof eH' - wH') + (1 - lam) * (prof eL' - wL')) ≤
      dv wbar * (lam * (prof eH - wbar) + (1 - lam) * (prof eL - wbar)) := by
    have a1 := mul_le_mul_of_nonneg_left tH (mul_nonneg hd.le hl0)
    have a2 := mul_le_mul_of_nonneg_left tL (mul_nonneg hd.le (by linarith : (0:ℝ) ≤ 1 - lam))
    have b1 := mul_le_mul_of_nonneg_left gH hl0
    have b2 := mul_le_mul_of_nonneg_left gL (by linarith : (0:ℝ) ≤ 1 - lam)
    have c1 := mul_le_mul_of_nonneg_left vH hl0
    have c2 := mul_le_mul_of_nonneg_left vL (by linarith : (0:ℝ) ≤ 1 - lam)
    have e1 : dv wbar * lam * (prof eH + dprof eH * (eH' - eH)) =
        dv wbar * lam * prof eH + lam * (ge eH θH * (eH' - eH)) := by rw [← hfH]; ring
    have e2 : dv wbar * (1 - lam) * (prof eL + dprof eL * (eL' - eL)) =
        dv wbar * (1 - lam) * prof eL + (1 - lam) * (ge eL θL * (eL' - eL)) := by rw [← hfL]; ring
    linarith
  exact le_of_mul_le_mul_left key hd

/-- **Exercise 14.C.3(b)** (MWG, p. 509). With `u = v(w) - g(e, θ)` and `g(·, θ_H)` strictly
increasing on `[0, ∞)`, a full-insurance contract `(w̄, e_H), (w̄, e_L)` with `0 ≤ e_L < e_H`
violates the truth-telling constraint of state `θ_H`: it is not feasible when `θ` is not
observable. -/
theorem exercise_14_C_3b {v : ℝ → ℝ} (g : ℝ → ℝ → ℝ) {θH wbar eH eL : ℝ}
    (hg : StrictMonoOn (fun e => g e θH) (Ici 0)) (hL0 : 0 ≤ eL) (hlt : eL < eH) :
    v wbar - g eH θH < v wbar - g eL θH := by
  have := hg (mem_Ici.2 hL0) (mem_Ici.2 (hL0.trans hlt.le)) hlt
  simp only at this; linarith

/-- **Exercise 14.C.3(b)**, the full-information efforts are ordered: if
`π'(e_i) v'(w̄) = g_e(e_i, θ_i)`, `π` is strictly concave, `g(·, θ_L)` convex, and
`g_e(e, θ_H) < g_e(e, θ_L)` for `e > 0`, then `e_L < e_H` whenever `e_H > 0`. -/
theorem exercise_14_C_3b_order {prof dprof : ℝ → ℝ} {g ge : ℝ → ℝ → ℝ} {θL θH a : ℝ}
    (hp : StrictConcaveOn ℝ (Ici 0) prof)
    (hdp : ∀ e, 0 ≤ e → HasDerivWithinAt prof (dprof e) (Ici 0) e)
    (hg : ConvexOn ℝ (Ici 0) fun e => g e θL)
    (hdg : ∀ e, 0 ≤ e → HasDerivWithinAt (fun e => g e θL) (ge e θL) (Ici 0) e)
    (hcross : ∀ e, 0 < e → ge e θH < ge e θL) (ha : 0 < a) {eH eL : ℝ} (hH0 : 0 < eH)
    (hL0 : 0 ≤ eL) (hfH : dprof eH * a = ge eH θH) (hfL : dprof eL * a = ge eL θL) :
    eL < eH := by
  by_contra hle
  rw [not_lt] at hle
  have h1 : dprof eL ≤ dprof eH := by
    rcases hle.lt_or_eq with h | h
    · exact (hi_deriv_anti hp (mem_Ici.2 hH0.le) (mem_Ici.2 hL0) h (hdp _ hH0.le)
        (hdp _ hL0)).le
    · rw [h]
  have h4 : ge eH θL ≤ ge eL θL := by
    rcases hle.lt_or_eq with h | h
    · have t1 := tpa_tangent_ge_convex hg (mem_Ici.2 hH0.le) (mem_Ici.2 hL0) (hdg eH hH0.le)
      have t2 := tpa_tangent_ge_convex hg (mem_Ici.2 hL0) (mem_Ici.2 hH0.le) (hdg eL hL0)
      nlinarith
    · rw [h]
  have := hcross eH hH0
  nlinarith [mul_le_mul_of_nonneg_right h1 ha.le]

/-! ### Exercise 14.C.5 -/

/-- The relaxed program without (iv) is solved by the binding contract at a maximizer of `S_H` and
a maximizer of the virtual surplus `Q`, whatever their order. -/
theorem screen_relax_opt {P : Screen} (h : P.Hyp) {eH eL : ℝ} (hH0 : 0 ≤ eH)
    (hH : ∀ e, 0 ≤ e → P.SH e ≤ P.SH eH) (hL0 : 0 ≤ eL) (hQ : ∀ e, 0 ≤ e → P.Q e ≤ P.Q eL) :
    P.IsOptRelax (P.bind eH eL) := by
  refine ⟨⟨hH0, hL0, ?_, ?_⟩, fun K hK => ?_⟩
  · unfold Screen.C1 Screen.bind; simp
  · unfold Screen.C3 Screen.bind Screen.D; simp only; linarith
  · have := Screen.screen_Pi_le h hK.2.2.1 hK.2.2.2
    rw [Screen.screen_Pi_bind]
    unfold Screen.R at this ⊢
    nlinarith [mul_le_mul_of_nonneg_left (hH _ hK.1) h.lam_pos.le, hQ _ hK.2.1]

/-- The model of `exercise_14_C_5_reversal`: `π_H(e) = log (1 + e) / 8`, `π_L(e) = log (1 + e)`,
`g(e, θ_L) = e²/4`, `g(e, θ_H) = e²/12`, `λ = 7/19`, `c = 0`. -/
noncomputable def exRev : Screen :=
  ⟨fun e => Real.log (1 + e) / 8, fun e => Real.log (1 + e),
    fun e θ => if θ = 0 then e ^ 2 / 4 else e ^ 2 / 12, 0, 1, 7 / 19, 0⟩

/-- **Exercise 14.C.5, "what happens if this condition is not satisfied?"** (MWG, p. 509). In
`exRev` (`π'_H < π'_L`) the first-best efforts are reversed (`e*_H = 1/2 < e*_L = 1`), and the
solution of the program without constraint (iv), `e_H = 1/2`, `e_L = 4/5`, violates (iv): the
truth-telling constraint of state `θ_L` can no longer be ignored. -/
theorem exercise_14_C_5_reversal :
    (∀ e, 0 ≤ e → exRev.SH e ≤ exRev.SH (1 / 2)) ∧ (∀ e, 0 ≤ e → exRev.SL e ≤ exRev.SL 1) ∧
      exRev.IsOptRelax (exRev.bind (1 / 2) (4 / 5)) ∧ ¬ exRev.C4 (exRev.bind (1 / 2) (4 / 5)) := by
  have gL : ∀ e, exRev.g e exRev.θL = e ^ 2 / 4 := fun e => by simp [exRev]
  have gH : ∀ e, exRev.g e exRev.θH = e ^ 2 / 12 := fun e => by simp [exRev]
  have hSH : ∀ e, exRev.SH e = Real.log (1 + e) / 8 - e ^ 2 / 12 := fun e => by
    simp only [Screen.SH, gH]; rfl
  have hSL : ∀ e, exRev.SL e = Real.log (1 + e) - e ^ 2 / 4 := fun e => by
    simp only [Screen.SL, gL]; rfl
  have hD : ∀ e, exRev.D e = e ^ 2 / 6 := fun e => by
    simp only [Screen.D, gL, gH]; ring
  have hQ : ∀ e, exRev.Q e = 12 / 19 * Real.log (1 + e) - 25 / 114 * e ^ 2 := fun e => by
    simp only [Screen.Q, hSL, hD]; simp only [exRev]; ring
  have hyp : exRev.Hyp := by
    refine ⟨by norm_num [exRev], by norm_num [exRev], by rw [hD]; norm_num, ?_⟩
    intro a ha b hb hab
    simp only [hD]
    have : (0:ℝ) ≤ a := ha
    nlinarith
  have hSHmax : ∀ e, 0 ≤ e → exRev.SH e ≤ exRev.SH (1 / 2) := fun e he => by
    rw [hSH, hSH]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (3 / 2) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (2 * e - 1)]
  have hSLmax : ∀ e, 0 ≤ e → exRev.SL e ≤ exRev.SL 1 := fun e he => by
    rw [hSL, hSL]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / 2 by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 1 = 2 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (e - 1)]
  have hQmax : ∀ e, 0 ≤ e → exRev.Q e ≤ exRev.Q (4 / 5) := fun e he => by
    rw [hQ, hQ]
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 + e) / (9 / 5) by positivity)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    have : (1 : ℝ) + 4 / 5 = 9 / 5 := by norm_num
    rw [this]
    nlinarith [sq_nonneg (5 * e - 4)]
  refine ⟨hSHmax, hSLmax, screen_relax_opt hyp (by norm_num) hSHmax (by norm_num) hQmax, ?_⟩
  intro h4
  unfold Screen.C4 Screen.bind at h4
  simp only at h4
  rw [gL, gL, hD, gH] at h4
  norm_num at h4
  linarith

/-! ### Exercise 14.C.6 -/

/-- The monopsony screening program of Exercise 14.C.6: Exercise 13.D.1's labor market (output
`θ(1 + μt)`, utility `w - c(t, θ)`, reservation utility `0`) with a single employer. -/
noncomputable def monopsony (M : AdverseSelection.SigModel) (μ : ℝ) : Screen :=
  ⟨fun t => M.θH * (1 + μ * t), fun t => M.θL * (1 + μ * t), M.c, M.θL, M.θH, M.lam, 0⟩

/-- The single-crossing assumption of Chapter 13 gives the hypotheses of the screening program. -/
theorem monopsony_hyp {M : AdverseSelection.SigModel} (hM : M.Valid) (μ : ℝ) :
    (monopsony M μ).Hyp := by
  refine ⟨hM.lam_pos, hM.lam_lt, ?_, ?_⟩
  · change M.c 0 M.θL - M.c 0 M.θH = 0
    rw [hM.c_zero, hM.c_zero, sub_self]
  · intro a ha b hb hab
    have := hM.sc a b ha hab
    change M.c a M.θL - M.c a M.θH < M.c b M.θL - M.c b M.θH
    linarith

/-- **Exercise 14.C.6** (MWG, p. 509). With a single employer, if `t*_H`, `t*_L` uniquely maximize
the types' surpluses `S_θ(t) = θ(1 + μt) - c(t, θ)` and `t*_L ≤ t*_H`, every optimal menu gives the
high type the efficient task `t*_H` and the low type a task `t_L ≤ t*_L` (with (i) and (iii)
binding). In every subgame perfect equilibrium of the competitive model of Exercise 13.D.1 the low
type's task is `t*_L`: the monopsonist's low task is no higher than the competitive one. -/
theorem exercise_14_C_6 {M : AdverseSelection.SigModel} (hM : M.Valid) {μ : ℝ} (hμ : 0 ≤ μ)
    {tHs tLs : ℝ} (hH : Screen.IsFB (monopsony M μ).SH tHs)
    (hL : Screen.IsFB (monopsony M μ).SL tLs) (hord : tLs ≤ tHs) {K : HIContract}
    (hK : (monopsony M μ).IsOpt K) :
    K.eH = tHs ∧ K.eL ≤ tLs ∧ K = (monopsony M μ).bind tHs K.eL ∧
      ∀ A₁ A₂, (M.prodGame μ).IsEq A₁ A₂ → ∃ kL, (M.prodGame μ).Chooses false (A₁ ∪ A₂) kL ∧
        kL.2 = tLs ∧ K.eL ≤ kL.2 := by
  have hyp := monopsony_hyp hM μ
  obtain ⟨hLle, hHe⟩ := Screen.lemma_14_C_3 hyp hH hL hord hK
  obtain ⟨-, -, hKb⟩ := (Screen.screen_opt_iff hyp hH hL hord K).1 hK
  refine ⟨hHe, hLle, hKb, fun A₁ A₂ hE => ?_⟩
  obtain ⟨kL, -, hkL, -, hkL0, -, -, -, hmax, -⟩ :=
    AdverseSelection.SigModel.exercise_13_D_1 hM hμ hE
  have hSL : ∀ t, (monopsony M μ).SL t = M.surplus μ false t := fun t => by
    simp only [Screen.SL, monopsony, AdverseSelection.SigModel.surplus,
      AdverseSelection.SigModel.θ_false]
  have heq : kL.2 = tLs := by
    by_contra hne
    have := hL.2 _ hkL0 hne
    rw [hSL, hSL] at this
    linarith [hmax tLs hL.1]
  exact ⟨kL, hkL, heq, heq ▸ hLle⟩

/-- **Exercise 14.C.6, an instance** (MWG, p. 509), with Chapter 13's `quadModel` (`θ_L = 1`,
`θ_H = 2`, `λ = 1/2`, `c(t, θ) = t²/θ`) and `μ = 4`: the optimal monopsony menu has tasks
`t_H = 8`, `t_L = 4/3`, while the competitive equilibrium tasks are `8` and `2`. -/
theorem exercise_14_C_6_instance :
    (monopsony AdverseSelection.SigModel.quadModel 4).IsOpt
      ((monopsony AdverseSelection.SigModel.quadModel 4).bind 8 (4 / 3)) := by
  set P := monopsony AdverseSelection.SigModel.quadModel 4
  have hyp := monopsony_hyp AdverseSelection.SigModel.quadModel_valid 4
  have hSH : ∀ t, P.SH t = 2 + 8 * t - t ^ 2 / 2 := fun t => by
    simp only [P, Screen.SH, monopsony, AdverseSelection.SigModel.quadModel]; ring
  have hSL : ∀ t, P.SL t = 1 + 4 * t - t ^ 2 := fun t => by
    simp only [P, Screen.SL, monopsony, AdverseSelection.SigModel.quadModel]; ring
  have hD : ∀ t, P.D t = t ^ 2 / 2 := fun t => by
    simp only [P, Screen.D, monopsony, AdverseSelection.SigModel.quadModel]; ring
  have hQ : ∀ t, P.Q t = (1 + 4 * t - t ^ 2) / 2 - t ^ 2 / 4 := fun t => by
    simp only [Screen.Q, hSL, hD]; simp only [P, monopsony, AdverseSelection.SigModel.quadModel]
    ring
  have hH : Screen.IsFB P.SH 8 := ⟨by norm_num, fun e _ hne => by
    rw [hSH, hSH]; have : 0 < (e - 8) ^ 2 := by positivity
    nlinarith⟩
  have hL : Screen.IsFB P.SL 2 := ⟨by norm_num, fun e _ hne => by
    rw [hSL, hSL]; have : 0 < (e - 2) ^ 2 := by positivity
    nlinarith⟩
  refine (Screen.screen_opt_iff hyp hH hL (by norm_num) _).2
    ⟨by change (0:ℝ) ≤ 4 / 3; norm_num, fun e _ => ?_, rfl⟩
  change P.Q e ≤ P.Q (4 / 3)
  rw [hQ, hQ]; nlinarith [sq_nonneg (e - 4 / 3)]

end MWG.PrincipalAgent
