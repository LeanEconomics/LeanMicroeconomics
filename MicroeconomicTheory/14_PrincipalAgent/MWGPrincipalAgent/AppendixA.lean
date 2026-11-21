/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExampleHA

/-!
# Appendix A: multiple effort levels in the hidden-action model

MWG, Appendix A, pp. 502-504.

Problem (14.AA.1) is `HAModel.IsHACostMin` for an arbitrary effort set `ε` (`HiddenAction`); with
`K` effort levels its incentive constraint is the `K - 1` inequalities `EU e' ≤ EU e`, `e' ≠ e`
(`aa_IC_iff`), and in the manager's utility levels it is linear (footnote 7, `ha_kt_sufficient`).

* `aa_not_implementable`: Figure 14.AA.1. If `f(·|e_M)` is a mixture `α f(·|e_L) + (1 - α) f(·|e_H)`
  and `g(e_M) > α g(e_L) + (1 - α) g(e_H)`, no scheme implements `e_M`.
* `aa_high_implementable`: with two effort levels, strict first-order stochastic dominance and a
  utility of income unbounded above, `e_H` can be implemented ("sufficiently high incentives").
* `aa_high_not_implementable`: correction: with a utility of income bounded above (`-exp(-w)`),
  `e_H` may be impossible to implement although the observable-effort contract for `e_H` exists.
* `foa_sufficient`: the first-order approach (14.AA.2)-(14.AA.3): a scheme satisfying (14.AA.3)
  with complementary slackness solves the relaxed program in which the incentive constraint is
  replaced by the manager's first-order condition.
* `foa_fails`: a solution of the relaxed program need not be incentive compatible: the manager's
  first-order condition holds at an effort level that is not optimal for him.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

namespace HAModel

variable {ε : Type*}

/-- **(14.AA.1)(ii)** (MWG, p. 503): the incentive constraint consists of the constraints
`EU e' ≤ EU e` for the other effort levels `e' ≠ e`. -/
theorem aa_IC_iff (M : HAModel ε) (e : ε) (w : ℝ → ℝ) :
    M.IC e w ↔ ∀ e', e' ≠ e → M.EU e' w ≤ M.EU e w := by
  refine ⟨fun h e' _ => h e', fun h e' => ?_⟩
  by_cases he : e' = e
  · rw [he]
  · exact h e' he

/-- **Figure 14.AA.1** (MWG, p. 503). If the profit density under `e_M` is the mixture
`α f(·|e_L) + (1 - α) f(·|e_H)` and `g(e_M) > α g(e_L) + (1 - α) g(e_H)`, then under every scheme
the manager strictly prefers `e_L` or `e_H` to `e_M`: `e_M` cannot be implemented. -/
theorem aa_not_implementable {M : HAModel ε} {eL eM eH : ε} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmix : ∀ x, M.f eM x = α * M.f eL x + (1 - α) * M.f eH x)
    (hg : α * M.g eL + (1 - α) * M.g eH < M.g eM) {w : ℝ → ℝ} (hw : M.Adm w) :
    M.EU eM w < M.EU eL w ∨ M.EU eM w < M.EU eH w := by
  have hEV : M.EV eM w = α * M.EV eL w + (1 - α) * M.EV eH w := by
    unfold EV
    have : (fun x => M.v (w x) * M.f eM x) =
        fun x => α * (M.v (w x) * M.f eL x) + (1 - α) * (M.v (w x) * M.f eH x) := by
      funext x; rw [hmix]; ring
    rw [this, integral_add ((hw.2 eL).2.const_mul _) ((hw.2 eH).2.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold EU
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  rw [hEV] at hc
  nlinarith [hc.1, hc.2]

/-- The two-valued scheme paying `w₁` where `f(π|e_L) < f(π|e_H)` and `w₀` elsewhere. -/
noncomputable def twoVal (M : HAModel ε) (eL eH : ε) (w₀ w₁ : ℝ) (x : ℝ) : ℝ :=
  if M.f eL x < M.f eH x then w₁ else w₀

/-- **"`e_H` could always be induced"** (MWG, p. 503), corrected. With two effort levels, strict
first-order stochastic dominance, `g(e_L) < g(e_H)`, and a utility of income that is unbounded
above, some admissible scheme satisfies the participation and incentive constraints for `e_H`. -/
theorem aa_high_implementable {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hfosd : M.FOSD eH eL) (hunb : ∀ y, ∃ w, y ≤ M.v w) :
    ∃ w, M.HAFeasible eH w := by
  set A := {x | M.f eL x < M.f eH x}
  have hA : MeasurableSet A := measurableSet_lt (hM.f_meas eL) (hM.f_meas eH)
  set P : ε → ℝ := fun e => ∫ x in A, M.f e x ∂M.ν
  -- the probability of A is larger under e_H
  have hdiff : 0 < P eH - P eL := by
    have hB := ha_fosd_set hM hfosd
    have hcompl : ∫ x in Aᶜ, (M.f eL x - M.f eH x) ∂M.ν = P eH - P eL := by
      have h1 : ∫ x in A, (M.f eL x - M.f eH x) ∂M.ν + ∫ x in Aᶜ, (M.f eL x - M.f eH x) ∂M.ν =
          ∫ x, (M.f eL x - M.f eH x) ∂M.ν := integral_add_compl hA ((hM.f_int eL).sub (hM.f_int eH))
      rw [integral_sub (hM.f_int eL) (hM.f_int eH), hM.f_one, hM.f_one, sub_self,
        integral_sub (hM.f_int eL).integrableOn (hM.f_int eH).integrableOn] at h1
      simp only [P]; linarith
    rw [← hcompl]
    have hsub : {x | M.f eH x < M.f eL x} ⊆ Aᶜ := fun x hx => by
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_lt]; exact (mem_ofPred_eq ▸ hx).le
    have hnn : ∀ x ∈ Aᶜ, 0 ≤ M.f eL x - M.f eH x := fun x hx => by
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_lt] at hx; linarith
    have hpos : 0 < ∫ x in {x | M.f eH x < M.f eL x}, (M.f eL x - M.f eH x) ∂M.ν := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · have : Function.support (fun x => M.f eL x - M.f eH x) ∩ {x | M.f eH x < M.f eL x} =
            {x | M.f eH x < M.f eL x} := by
          ext x; simp only [mem_inter_iff, Function.mem_support, mem_ofPred_eq]
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨by linarith, h⟩
        rw [this]; exact pos_iff_ne_zero.2 hB
      · filter_upwards [ae_restrict_mem (measurableSet_lt (hM.f_meas eH) (hM.f_meas eL))] with x hx
        simp only [Pi.zero_apply] at hx ⊢; linarith
      · exact ((hM.f_int eL).sub (hM.f_int eH)).integrableOn
    calc 0 < _ := hpos
      _ ≤ ∫ x in Aᶜ, (M.f eL x - M.f eH x) ∂M.ν :=
        setIntegral_mono_set ((hM.f_int eL).sub (hM.f_int eH)).integrableOn
          (ae_restrict_of_forall_mem hA.compl hnn) (Filter.Eventually.of_forall hsub)
  have hPH : 0 < P eH := by
    have : 0 ≤ P eL := setIntegral_nonneg hA fun x _ => (hM.f_pos eL x).le
    linarith
  -- choose the wages
  set u₀ := M.v 0
  set t := max (u₀ + (M.g eH - M.g eL) / (P eH - P eL)) (u₀ + (M.ubar + M.g eH - u₀) / P eH)
  obtain ⟨w₁, hw₁⟩ := hunb t
  set w := M.twoVal eL eH 0 w₁
  have hEV : ∀ e, M.EV e w = u₀ + (M.v w₁ - u₀) * P e := by
    intro e
    unfold EV
    have hsplit := integral_add_compl hA (show Integrable (fun x => M.v (w x) * M.f e x) M.ν from
      by
        have : (fun x => M.v (w x) * M.f e x) =
            A.indicator (fun x => M.v w₁ * M.f e x) + Aᶜ.indicator (fun x => u₀ * M.f e x) := by
          funext x
          by_cases hx : x ∈ A
          · simp [w, twoVal, indicator, hx, show M.f eL x < M.f eH x from hx]
          · simp only [w, twoVal, Pi.add_apply, indicator, hx, mem_compl_iff,
              not_false_eq_true, ↓reduceIte, zero_add]
            have hx' : ¬ M.f eL x < M.f eH x := hx
            simp only [hx', ↓reduceIte, u₀]
        rw [this]
        exact (((hM.f_int e).const_mul _).indicator hA).add
          (((hM.f_int e).const_mul _).indicator hA.compl))
    rw [← hsplit]
    have e1 : ∫ x in A, M.v (w x) * M.f e x ∂M.ν = M.v w₁ * P e := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hA fun x hx => ?_
      simp only [w, twoVal, show M.f eL x < M.f eH x from hx, ↓reduceIte]
    have e2 : ∫ x in Aᶜ, M.v (w x) * M.f e x ∂M.ν = u₀ * (1 - P e) := by
      have hc := integral_add_compl hA (hM.f_int e)
      rw [hM.f_one] at hc
      have : ∫ x in Aᶜ, M.f e x ∂M.ν = 1 - P e := by simp only [P]; linarith
      rw [← this, ← integral_const_mul]
      refine setIntegral_congr_fun hA.compl fun x hx => ?_
      have hx' : ¬ M.f eL x < M.f eH x := hx
      simp only [w, twoVal, hx', ↓reduceIte, u₀]
    rw [e1, e2]; ring
  have hadm : M.Adm w := by
    refine ⟨Measurable.ite hA measurable_const measurable_const, fun e => ⟨?_, ?_⟩⟩
    · have : (fun x => w x * M.f e x) =
          A.indicator (fun x => w₁ * M.f e x) + Aᶜ.indicator (fun x => 0 * M.f e x) := by
        funext x
        by_cases hx : x ∈ A
        · simp [w, twoVal, indicator, hx, show M.f eL x < M.f eH x from hx]
        · simp only [w, twoVal, Pi.add_apply, indicator, hx, mem_compl_iff,
            not_false_eq_true, ↓reduceIte, zero_add]
          have hx' : ¬ M.f eL x < M.f eH x := hx
          simp only [hx', ↓reduceIte]
      rw [this]
      exact (((hM.f_int e).const_mul _).indicator hA).add
        (((hM.f_int e).const_mul _).indicator hA.compl)
    · have : (fun x => M.v (w x) * M.f e x) =
          A.indicator (fun x => M.v w₁ * M.f e x) + Aᶜ.indicator (fun x => u₀ * M.f e x) := by
        funext x
        by_cases hx : x ∈ A
        · simp [w, twoVal, indicator, hx, show M.f eL x < M.f eH x from hx]
        · simp only [w, twoVal, Pi.add_apply, indicator, hx, mem_compl_iff,
            not_false_eq_true, ↓reduceIte, zero_add]
          have hx' : ¬ M.f eL x < M.f eH x := hx
          simp only [hx', ↓reduceIte, u₀]
      rw [this]
      exact (((hM.f_int e).const_mul _).indicator hA).add
        (((hM.f_int e).const_mul _).indicator hA.compl)
  have ht1 := le_max_left (u₀ + (M.g eH - M.g eL) / (P eH - P eL))
    (u₀ + (M.ubar + M.g eH - u₀) / P eH)
  have ht2 := le_max_right (u₀ + (M.g eH - M.g eL) / (P eH - P eL))
    (u₀ + (M.ubar + M.g eH - u₀) / P eH)
  refine ⟨w, ⟨hadm, ?_⟩, (ha_IC_two hE w).2 ?_⟩
  · unfold EU; rw [hEV]
    have : (M.ubar + M.g eH - u₀) / P eH ≤ M.v w₁ - u₀ := by linarith
    rw [div_le_iff₀ hPH] at this
    linarith
  · unfold EU; rw [hEV, hEV]
    have : (M.g eH - M.g eL) / (P eH - P eL) ≤ M.v w₁ - u₀ := by linarith
    rw [div_le_iff₀ hdiff] at this
    nlinarith

end HAModel

/-- The model of `aa_high_not_implementable`: `v(w) = -exp(-w)`, `g(e_H) = 1/2`, `ū = -1`. -/
noncomputable def exC : HAModel Bool :=
  exModel (fun w => -Real.exp (-w)) (fun w => Real.exp (-w)) (1 / 2) (-1)

/-- **Correction to p. 503** ("`e_H` could always be induced"). In `exC` (strict first-order
stochastic dominance, `v(w) = -exp(-w)` bounded above) the observable-effort contract for `e_H`
exists (`w = log 2`), but no scheme satisfies the participation and incentive constraints for
`e_H`. -/
theorem aa_high_not_implementable :
    exC.v (Real.log 2) = exC.ubar + exC.g true ∧ ¬ ∃ w, exC.HAFeasible true w := by
  refine ⟨?_, ?_⟩
  · change -Real.exp (-Real.log 2) = -1 + (if true then 1 / 2 else 0)
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  · rintro ⟨w, ⟨⟨hw, hpart⟩, hic⟩⟩
    have hEU : ∀ b : Bool, exC.EU b w = -Real.exp (-w 0) * exF b 0 + -Real.exp (-w 1) * exF b 1 +
        -Real.exp (-w 2) * exF b 2 - (if b then 1 / 2 else 0) := by
      intro b
      change (∫ x, -Real.exp (-w x) * exF b x ∂dmeas exPts) - _ = _
      rw [exA_integral]
      rfl
    have hic' := hic false
    rw [hEU, hEU] at hic'
    have hp := hpart
    change -1 ≤ exC.EU true w at hp
    rw [hEU] at hp
    simp only [exF, Bool.false_eq_true, ↓reduceIte] at hic' hp
    norm_num at hic' hp
    have h0 := Real.exp_pos (-w 0)
    have h1 := Real.exp_pos (-w 1)
    have h2 := Real.exp_pos (-w 2)
    nlinarith

/-- **The first-order approach** (MWG, p. 504, (14.AA.2)-(14.AA.3)). For one-dimensional effort the
incentive constraint is replaced by the manager's first-order condition
`∫ v(w(π)) f_e(π|e) dπ = g'(e)` (with `f_e` given by `fe`). If `w` satisfies this condition, and
`1 / v'(w(π)) = λ + μ f_e(π|e) / f(π|e)` at almost every `π`
with `λ ≥ 0` and complementary slackness (`μ` is unrestricted in sign since the constraint is an
equality), then `w` solves the relaxed program. -/
theorem foa_sufficient {ε : Type*} {M : HAModel ε} (hM : M.Standing) {e : ε} {fe : ℝ → ℝ} {dg : ℝ}
    (hfe : ∀ w', M.Adm w' → Integrable (fun x => M.v (w' x) * fe x) M.ν)
    {w : ℝ → ℝ} (hw : M.Adm w) {lam μ : ℝ} (hlam : 0 ≤ lam)
    (hfoc : ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = lam + μ * (fe x / M.f e x))
    (hcs : lam * (M.EU e w - M.ubar) = 0)
    (hfoa : ∫ x, M.v (w x) * fe x ∂M.ν = dg) {w' : ℝ → ℝ} (hw' : M.Adm w')
    (hpart' : M.ubar ≤ M.EU e w') (hfoa' : ∫ x, M.v (w' x) * fe x ∂M.ν = dg) :
    M.EW e w ≤ M.EW e w' := by
  have hpt : ∀ᵐ x ∂M.ν, lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) +
      μ * (M.v (w' x) * fe x - M.v (w x) * fe x) ≤ w' x * M.f e x - w x * M.f e x := by
    filter_upwards [hfoc] with x hx
    have htan := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
      (hM.v_deriv (w x)).hasDerivWithinAt
    have hd := hM.dv_pos (w x)
    have hf := hM.f_pos e x
    have key : (M.v (w' x) - M.v (w x)) * (1 / M.dv (w x)) ≤ w' x - w x := by
      rw [mul_one_div, div_le_iff₀ hd]; linarith
    rw [hx] at key
    have key2 := mul_le_mul_of_nonneg_right key hf.le
    have hr : fe x / M.f e x * M.f e x = fe x := div_mul_cancel₀ _ hf.ne'
    have : (M.v (w' x) - M.v (w x)) * (lam + μ * (fe x / M.f e x)) * M.f e x =
        lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) +
          μ * (M.v (w' x) * fe x - M.v (w x) * fe x) := by
      have : (M.v (w' x) - M.v (w x)) * (lam + μ * (fe x / M.f e x)) * M.f e x =
          (M.v (w' x) - M.v (w x)) * (lam * M.f e x + μ * (fe x / M.f e x * M.f e x)) := by ring
      rw [this, hr]; ring
    linarith
  have hi1 : Integrable (fun x => lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x)) M.ν :=
    ((hw'.2 e).2.sub (hw.2 e).2).const_mul lam
  have hi2 : Integrable (fun x => μ * (M.v (w' x) * fe x - M.v (w x) * fe x)) M.ν :=
    ((hfe w' hw').sub (hfe w hw)).const_mul μ
  have hint : ∫ x, (lam * (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) +
      μ * (M.v (w' x) * fe x - M.v (w x) * fe x)) ∂M.ν ≤
      ∫ x, (w' x * M.f e x - w x * M.f e x) ∂M.ν :=
    integral_mono_ae (hi1.add hi2) ((hw'.2 e).1.sub (hw.2 e).1) hpt
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_sub (hw'.2 e).2 (hw.2 e).2, integral_sub (hfe w' hw') (hfe w hw), hfoa, hfoa',
    integral_sub (hw'.2 e).1 (hw.2 e).1] at hint
  change lam * (M.EV e w' - M.EV e w) + μ * (dg - dg) ≤ M.EW e w' - M.EW e w at hint
  unfold HAModel.EU at hpart' hcs
  have : 0 ≤ lam * (M.EV e w' - M.g e - M.ubar) := mul_nonneg hlam (by linarith)
  nlinarith

/-- **The first-order approach can fail** (MWG, p. 504). Two outcomes, effort `e ∈ [0, 1]`,
`f(π_H | e) = (1 + e²)/3`, `g(e) = e/6`, a risk-neutral manager and `ū = 0`. For `e = 1/2` the
relaxed program (participation and the first-order condition `f'(π_H|e)(w_H - w_L) = g'(e)`) has the
unique solution `w_L = -1/8`, `w_H = 3/8`; but under it the manager strictly prefers `e = 1` to
`e = 1/2` (where his first-order condition holds at a minimum). -/
theorem foa_fails :
    let p : ℝ → ℝ := fun e => (1 + e ^ 2) / 3
    let U : ℝ → ℝ → ℝ → ℝ := fun wL wH e => wL + p e * (wH - wL) - e / 6
    (∀ wL wH, 0 ≤ U wL wH (1 / 2) → 2 * (1 / 2) / 3 * (wH - wL) = 1 / 6 →
      wL + p (1 / 2) * (wH - wL) ≥ -1 / 8 + p (1 / 2) * (3 / 8 - -1 / 8)) ∧
    U (-1 / 8) (3 / 8) (1 / 2) = 0 ∧ 2 * (1 / 2) / 3 * (3 / 8 - -1 / 8) = (1 / 6 : ℝ) ∧
    (∀ wL wH, 0 ≤ U wL wH (1 / 2) → 2 * (1 / 2) / 3 * (wH - wL) = 1 / 6 →
      wL + p (1 / 2) * (wH - wL) = -1 / 8 + p (1 / 2) * (3 / 8 - -1 / 8) →
      wL = -1 / 8 ∧ wH = 3 / 8) ∧
    U (-1 / 8) (3 / 8) (1 / 2) < U (-1 / 8) (3 / 8) 1 := by
  intro p U
  simp only [p, U]
  refine ⟨fun wL wH h1 h2 => by nlinarith, by norm_num, by norm_num,
    fun wL wH h1 h2 h3 => ⟨by nlinarith, by nlinarith⟩, by norm_num⟩

end MWG.PrincipalAgent
