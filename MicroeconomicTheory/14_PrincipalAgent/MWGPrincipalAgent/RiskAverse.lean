/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.HiddenAction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.IntermediateValue

/-!
# A risk-averse manager and two effort levels

MWG, Section 14.B, pp. 483-487.

* `ha_implement_low`: implementing the least costly effort (`e_L`) with the observable-effort
  fixed wage (pp. 483-484).
* `ha_kt_sufficient`: footnote 7, the Kuhn-Tucker condition (14.B.10) with complementary slackness
  is sufficient for (14.B.9) with `e = e_H` (the reformulated problem is convex in utilities).
* `lemma_14_B_1`: Lemma 14.B.1, both multipliers are positive.
* `ha_shift`, `footnote_8`: the utility-shift argument of footnote 8; the participation constraint
  binds in every solution of (14.B.9), for every effort level, and in every optimal contract.
* `ha_wage_vs_what`, `ha_monotone_iff_mlrp`: the likelihood-ratio form of the optimal scheme and
  the monotone likelihood ratio property (p. 485).
* `ha_EW_gt_of_IC`, `proposition_14_B_3`: Proposition 14.B.3; `ha_welfare_loss`,
  `ha_no_upward_distortion`, `footnote_9`.

Departures: the strict first-order stochastic dominance of p. 479 is used in the weaker form
"`F(π | e_H) ≤ F(π | e_L)` everywhere and strictly at some `π`" (`FOSD`). The necessity of the
Kuhn-Tucker conditions (footnote 7) is proved in `HANecessity` (`ha_kt_necessary`); here results
that MWG derives from (14.B.10) are proved for every scheme satisfying it, and those that do not
need multipliers (footnote 8, Proposition 14.B.3) are proved directly.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

namespace HAModel

variable {ε : Type*}

/-- The distribution function `F(π | e) = ∫_{π' ≤ π} f(π' | e) dπ'` (MWG, p. 479). -/
noncomputable def F (M : HAModel ε) (e : ε) (x : ℝ) : ℝ := ∫ y in Iic x, M.f e y ∂M.ν

/-- **Strict first-order stochastic dominance** (MWG, p. 479; Section 6.D): `F(π | e_H) ≤
F(π | e_L)` at every `π`, with strict inequality somewhere. -/
def FOSD (M : HAModel ε) (eH eL : ε) : Prop :=
  (∀ x, M.F eH x ≤ M.F eL x) ∧ ∃ x, M.F eH x < M.F eL x

/-- With exactly two effort levels, the incentive constraint (14.B.9)(ii) for `e_H` is
constraint (ii_H) of p. 484. -/
theorem ha_IC_two {M : HAModel ε} {eL eH : ε} (hE : ∀ e, e = eL ∨ e = eH) (w : ℝ → ℝ) :
    M.IC eH w ↔ M.EU eL w ≤ M.EU eH w := by
  refine ⟨fun h => h eL, fun h e => ?_⟩
  rcases hE e with rfl | rfl
  · exact h
  · exact le_rfl

/-- **Implementing `e_L`** (MWG, pp. 483-484). If `e` has the lowest disutility, the fixed wage
`w*_e` of the observable case solves (14.B.9). -/
theorem ha_implement_low {M : HAModel ε} (hM : M.Standing) {e : ε} (hlow : ∀ e', M.g e ≤ M.g e')
    {wbar : ℝ} (hwbar : M.v wbar = M.ubar + M.g e) : M.IsHACostMin e (fun _ => wbar) := by
  refine ⟨⟨(ha_fixed_wage_feasible hM hwbar).1, fun e' => ?_⟩, fun w' hw' => ?_⟩
  · unfold EU; rw [ha_EV_const hM, ha_EV_const hM]; linarith [hlow e']
  · exact (ha_fixed_wage_costMin hM hwbar).2 w' hw'.1

/-- The difference of expected utilities of income under two schemes. -/
theorem ha_EV_sub {M : HAModel ε} {w w' : ℝ → ℝ} (hw : M.Adm w) (hw' : M.Adm w') (e : ε) :
    ∫ x, (M.v (w' x) * M.f e x - M.v (w x) * M.f e x) ∂M.ν = M.EV e w' - M.EV e w :=
  integral_sub (hw'.2 e).2 (hw.2 e).2

/-- **Footnote 7 and (14.B.10)** (MWG, p. 484). Sufficiency of the Kuhn-Tucker conditions: if `w`
satisfies the participation constraint (i) and the incentive constraint (ii_H), and there are
multipliers `γ, μ ≥ 0` with complementary slackness such that
`1 / v'(w(π)) = γ + μ [1 - f(π | e_L) / f(π | e_H)]` at almost every `π`, then `w` solves (14.B.9)
for `e = e_H`. -/
theorem ha_kt_sufficient {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) {w : ℝ → ℝ} (hw : M.Adm w) {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hfoc : ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x))
    (hi : M.ubar ≤ M.EU eH w) (hii : M.EU eL w ≤ M.EU eH w)
    (hcs1 : γ * (M.EU eH w - M.ubar) = 0) (hcs2 : μ * (M.EU eH w - M.EU eL w) = 0) :
    M.IsHACostMin eH w := by
  refine ⟨⟨⟨hw, hi⟩, (ha_IC_two hE w).2 hii⟩, fun w' hw' => ?_⟩
  have hii' := (ha_IC_two hE w').1 hw'.2
  have hi' := hw'.1.2
  -- the pointwise inequality
  have hpt : ∀ᵐ x ∂M.ν, (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
      μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x) ≤
      w' x * M.f eH x - w x * M.f eH x := by
    filter_upwards [hfoc] with x hx
    have htan := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
      (hM.v_deriv (w x)).hasDerivWithinAt
    have hd := hM.dv_pos (w x)
    have hH := hM.f_pos eH x
    have hL := hM.f_pos eL x
    have key : (M.v (w' x) - M.v (w x)) * (1 / M.dv (w x)) ≤ w' x - w x := by
      rw [mul_one_div, div_le_iff₀ hd]; linarith
    rw [hx] at key
    have key2 := mul_le_mul_of_nonneg_right key hH.le
    have hr : M.f eL x / M.f eH x * M.f eH x = M.f eL x := div_mul_cancel₀ _ hH.ne'
    have : (M.v (w' x) - M.v (w x)) * (γ + μ * (1 - M.f eL x / M.f eH x)) * M.f eH x =
        (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
          μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x) := by
      have : (M.v (w' x) - M.v (w x)) * (γ + μ * (1 - M.f eL x / M.f eH x)) * M.f eH x =
          (M.v (w' x) - M.v (w x)) * (γ * M.f eH x + μ * M.f eH x -
            μ * (M.f eL x / M.f eH x * M.f eH x)) := by ring
      rw [this, hr]; ring
    linarith
  have hiH : Integrable (fun x => (γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x))
      M.ν := ((hw'.1.1.2 eH).2.sub (hw.2 eH).2).const_mul (γ + μ)
  have hiL : Integrable (fun x => μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) M.ν :=
    ((hw'.1.1.2 eL).2.sub (hw.2 eL).2).const_mul μ
  have hint : ∫ x, ((γ + μ) * (M.v (w' x) * M.f eH x - M.v (w x) * M.f eH x) -
      μ * (M.v (w' x) * M.f eL x - M.v (w x) * M.f eL x)) ∂M.ν ≤
      ∫ x, (w' x * M.f eH x - w x * M.f eH x) ∂M.ν :=
    integral_mono_ae (hiH.sub hiL) ((hw'.1.1.2 eH).1.sub (hw.2 eH).1) hpt
  rw [integral_sub hiH hiL, integral_const_mul, integral_const_mul, ha_EV_sub hw hw'.1.1,
    ha_EV_sub hw hw'.1.1, integral_sub (hw'.1.1.2 eH).1 (hw.2 eH).1] at hint
  change _ ≤ M.EW eH w' - M.EW eH w at hint
  unfold EU at hi hii hi' hii' hcs1 hcs2
  have h1 : 0 ≤ γ * (M.EV eH w' - M.g eH - M.ubar) := mul_nonneg hγ (by linarith)
  have h2 : 0 ≤ μ * (M.EV eH w' - M.g eH - (M.EV eL w' - M.g eL)) := mul_nonneg hμ (by linarith)
  nlinarith

/-- Strict first-order stochastic dominance makes `f(π | e_L) > f(π | e_H)` on a set of positive
measure (MWG, proof of Lemma 14.B.1, p. 484). -/
theorem ha_fosd_set {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hfosd : M.FOSD eH eL) :
    M.ν {x | M.f eH x < M.f eL x} ≠ 0 := by
  intro h0
  obtain ⟨x0, hx0⟩ := hfosd.2
  have hae : ∀ᵐ x ∂M.ν, M.f eL x ≤ M.f eH x := by
    rw [ae_iff]; simpa [not_le] using h0
  have := setIntegral_mono_ae (s := Iic x0) (hM.f_int eL).integrableOn (hM.f_int eH).integrableOn
    hae
  unfold F at hx0
  linarith

/-- The reference measure is not zero (each `f e` integrates to one). -/
theorem ha_nu_ne_zero {M : HAModel ε} (hM : M.Standing) (e : ε) : M.ν ≠ 0 := by
  intro h
  have := hM.f_one e
  rw [h, integral_zero_measure] at this
  exact zero_ne_one this

/-- **Lemma 14.B.1** (MWG, p. 484). Suppose `F(π | e_H)` strictly first-order stochastically
dominates `F(π | e_L)`, `g(e_H) > g(e_L)`, the manager is strictly risk averse (`v'` strictly
decreasing), and `w` satisfies the incentive constraint (ii_H). If multipliers `γ, μ ≥ 0` satisfy
(14.B.10) at almost every profit level, then `γ > 0` and `μ > 0`. -/
theorem lemma_14_B_1 {M : HAModel ε} (hM : M.Standing) {eL eH : ε} (hfosd : M.FOSD eH eL)
    (hg : M.g eL < M.g eH) (hda : StrictAnti M.dv) {w : ℝ → ℝ}
    (hii : M.EU eL w ≤ M.EU eH w) {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hfoc : ∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x)) :
    0 < γ ∧ 0 < μ := by
  constructor
  · by_contra hγ0
    have hγ' : γ = 0 := le_antisymm (not_lt.1 hγ0) hγ
    obtain ⟨x, hxS, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ha_fosd_set hM hfosd)
      (ae_restrict_of_ae hfoc)
    have hH := hM.f_pos eH x
    have hr : 1 < M.f eL x / M.f eH x := by rw [one_lt_div hH]; exact hxS
    have hpos : 0 < 1 / M.dv (w x) := one_div_pos.2 (hM.dv_pos _)
    rw [hx, hγ'] at hpos
    nlinarith
  · by_contra hμ0
    have hμ' : μ = 0 := le_antisymm (not_lt.1 hμ0) hμ
    have hne : (ae M.ν).NeBot := ae_neBot.2 (ha_nu_ne_zero hM eL)
    obtain ⟨x0, hx0⟩ := hfoc.exists
    have hconst : ∀ᵐ x ∂M.ν, w x = w x0 := by
      filter_upwards [hfoc] with x hx
      rw [hμ'] at hx hx0
      simp only [zero_mul, add_zero] at hx hx0
      have : M.dv (w x) = M.dv (w x0) := by
        have := hx.trans hx0.symm; simpa using this
      exact hda.injective this
    have hEV : ∀ e, M.EV e w = M.v (w x0) := by
      intro e
      have : M.EV e w = M.EV e (fun _ => w x0) := by
        unfold EV
        refine integral_congr_ae ?_
        filter_upwards [hconst] with x hx
        rw [hx]
      rw [this, ha_EV_const hM]
    unfold EU at hii
    rw [hEV, hEV] at hii
    linarith

/-- Concavity makes `v'` antitone. -/
theorem ha_dv_anti {M : HAModel ε} (hM : M.Standing) {x a : ℝ} (hxa : x ≤ a) :
    M.dv a ≤ M.dv x := by
  rcases hxa.lt_or_eq with hxa | rfl
  · have h1 := tpa_tangent_le hM.v_conc (mem_univ x) (mem_univ a) (hM.v_deriv x).hasDerivWithinAt
    have h2 := tpa_tangent_le hM.v_conc (mem_univ a) (mem_univ x) (hM.v_deriv a).hasDerivWithinAt
    nlinarith
  · exact le_rfl

/-- `v` is unbounded below and continuous, so every utility level below `v(a)` is attained at a
wage below `a` (used in footnote 8). -/
theorem ha_v_hits {M : HAModel ε} (hM : M.Standing) {a t : ℝ} (ht : t < M.v a) :
    ∃ y, y < a ∧ M.v y = t := by
  have hd := hM.dv_pos a
  set y0 := a - (M.v a - t) / M.dv a - 1
  have hy0 : M.v y0 < t := by
    have := tpa_tangent_le hM.v_conc (mem_univ a) (mem_univ y0) (hM.v_deriv a).hasDerivWithinAt
    have : M.dv a * (y0 - a) = -(M.v a - t) - M.dv a := by
      simp only [y0]; field_simp; ring
    linarith
  have hya : y0 ≤ a := by
    have : 0 ≤ (M.v a - t) / M.dv a := div_nonneg (by linarith) hd.le
    simp only [y0]; linarith
  have hcont : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  obtain ⟨y, hy, hyt⟩ := intermediate_value_Ioo hya hcont.continuousOn ⟨hy0, ht⟩
  exact ⟨y, hy.2, hyt⟩

/-- **Footnote 8** (MWG, p. 485). The scheme `ŵ` with `v(ŵ(π)) = v(w(π)) - Δ`. -/
noncomputable def shift (M : HAModel ε) (Δ : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  Classical.epsilon fun y => M.v y = M.v (w x) - Δ

/-- The defining property of the shifted scheme, for `Δ > 0`. -/
theorem ha_shift_spec {M : HAModel ε} (hM : M.Standing) {Δ : ℝ} (hΔ : 0 < Δ) (w : ℝ → ℝ)
    (x : ℝ) : M.v (M.shift Δ w x) = M.v (w x) - Δ := by
  obtain ⟨y, -, hy⟩ := ha_v_hits hM (by linarith : M.v (w x) - Δ < M.v (w x))
  exact Classical.epsilon_spec (p := fun y => M.v y = M.v (w x) - Δ) ⟨y, hy⟩

/-- **Footnote 8** (MWG, p. 485). Lowering the manager's utility by `Δ > 0` at every profit level:
the resulting scheme is admissible, lowers every expected utility by exactly `Δ`, and lowers the
expected wage strictly under every effort. -/
theorem ha_shift {M : HAModel ε} (hM : M.Standing) {Δ : ℝ} (hΔ : 0 < Δ) {w : ℝ → ℝ}
    (hw : M.Adm w) :
    M.Adm (M.shift Δ w) ∧ (∀ e, M.EU e (M.shift Δ w) = M.EU e w - Δ) ∧
      ∀ e, M.EW e (M.shift Δ w) < M.EW e w := by
  set w' := M.shift Δ w
  have hspec : ∀ x, M.v (w' x) = M.v (w x) - Δ := ha_shift_spec hM hΔ w
  have hmono := ha_v_strictMono hM
  have hcont : Continuous M.v :=
    continuous_iff_continuousAt.2 fun w => (hM.v_deriv w).continuousAt
  have hlt : ∀ x, w' x < w x := fun x => hmono.lt_iff_lt.1 (by rw [hspec]; linarith)
  have hmeas : Measurable w' := by
    refine measurable_of_Iio fun a => ?_
    have : w' ⁻¹' Iio a = {x | M.v (w x) - Δ < M.v a} := by
      ext x
      simp only [mem_preimage, mem_Iio]
      rw [← hmono.lt_iff_lt, hspec]
      rfl
    rw [this]
    exact measurableSet_lt ((hcont.measurable.comp hw.1).sub_const _) measurable_const
  obtain ⟨b, -, hb⟩ := ha_v_hits hM (by linarith : M.v 0 - Δ < M.v 0)
  set C := |b| + Δ / M.dv 0
  have hd0 := hM.dv_pos 0
  have hbound : ∀ x, |w' x| ≤ |w x| + C := by
    intro x
    have hlow : min b (w x - Δ / M.dv 0) ≤ w' x := by
      rcases le_or_gt 0 (w x) with h0 | h0
      · refine min_le_of_left_le (hmono.le_iff_le.1 ?_)
        rw [hb, hspec]; linarith [hmono.monotone h0]
      · refine min_le_of_right_le ?_
        have htan := tpa_tangent_le hM.v_conc (mem_univ (w x)) (mem_univ (w' x))
          (hM.v_deriv (w x)).hasDerivWithinAt
        rw [hspec] at htan
        have hdx := ha_dv_anti hM h0.le
        have hdpos := hM.dv_pos (w x)
        have h1 : M.dv (w x) * (w x - w' x) ≤ Δ := by linarith
        have h2 : w x - w' x ≤ Δ / M.dv 0 := by
          rw [le_div_iff₀ hd0]
          have : 0 ≤ w x - w' x := (sub_pos.2 (hlt x)).le
          nlinarith
        linarith
    have hC : 0 ≤ Δ / M.dv 0 := div_nonneg hΔ.le hd0.le
    rw [abs_le]
    constructor
    · refine le_trans (le_min ?_ ?_) hlow
      · have := neg_abs_le b; have := abs_nonneg (w x); simp only [C]; linarith
      · have := neg_abs_le (w x); have := abs_nonneg b; simp only [C]; linarith
    · have := le_abs_self (w x); have := abs_nonneg b; simp only [C]; linarith [hlt x]
  have hEV : ∀ e, M.EV e w' = M.EV e w - Δ := by
    intro e
    unfold EV
    simp only [hspec, sub_mul]
    rw [integral_sub (hw.2 e).2 ((hM.f_int e).const_mul Δ), integral_const_mul, hM.f_one,
      mul_one]
  have hint : ∀ e, Integrable (fun x => w' x * M.f e x) M.ν := by
    intro e
    refine Integrable.mono' (((hw.2 e).1.norm).add ((hM.f_int e).const_mul C))
      (hmeas.mul (hM.f_meas e)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hf := hM.f_pos e x
    change |w' x * M.f e x| ≤ ‖w x * M.f e x‖ + C * M.f e x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hf]
    nlinarith [hbound x]
  have hadm : M.Adm w' := by
    refine ⟨hmeas, fun e => ⟨hint e, ?_⟩⟩
    have : (fun x => M.v (w' x) * M.f e x) = fun x => M.v (w x) * M.f e x - Δ * M.f e x := by
      funext x; rw [hspec]; ring
    rw [this]; exact (hw.2 e).2.sub ((hM.f_int e).const_mul Δ)
  refine ⟨hadm, fun e => by unfold EU; rw [hEV]; ring, fun e => ?_⟩
  have hpos : 0 < ∫ x, (w x * M.f e x - w' x * M.f e x) ∂M.ν := by
    have hnn : 0 ≤ fun x => w x * M.f e x - w' x * M.f e x := fun x => by
      have := mul_lt_mul_of_pos_right (hlt x) (hM.f_pos e x)
      simp only [Pi.zero_apply]; linarith
    rw [integral_pos_iff_support_of_nonneg hnn ((hw.2 e).1.sub (hint e))]
    have hsupp : Function.support (fun x => w x * M.f e x - w' x * M.f e x) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      have := mul_lt_mul_of_pos_right (hlt x) (hM.f_pos e x)
      linarith
    rw [hsupp, pos_iff_ne_zero]
    intro h
    exact ha_nu_ne_zero hM e (Measure.measure_univ_eq_zero.1 h)
  rw [integral_sub (hw.2 e).1 (hint e)] at hpos
  unfold EW; linarith

/-- **Footnote 8** (MWG, p. 485). In any solution of (14.B.9) (for any effort level) the
participation constraint (i) binds. -/
theorem footnote_8 {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsHACostMin e w) : M.EU e w = M.ubar := by
  by_contra hne
  have hΔ : 0 < M.EU e w - M.ubar := sub_pos.2 (lt_of_le_of_ne hw.1.1.2 (Ne.symm hne))
  obtain ⟨hadm, hEU, hEW⟩ := ha_shift hM hΔ hw.1.1.1
  have hfeas : M.HAFeasible e (M.shift (M.EU e w - M.ubar) w) := by
    refine ⟨⟨hadm, by rw [hEU]; linarith⟩, fun e' => ?_⟩
    rw [hEU, hEU]; linarith [hw.1.2 e']
  linarith [hw.2 _ hfeas, hEW e]

/-- In every optimal contract under unobservable effort the participation constraint binds
(footnote 8, applied to the owner's whole problem). -/
theorem ha_optimal_binds {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsHAOptimal e w) : M.EU e w = M.ubar := by
  by_contra hne
  have hΔ : 0 < M.EU e w - M.ubar := sub_pos.2 (lt_of_le_of_ne hw.1.1.2 (Ne.symm hne))
  obtain ⟨hadm, hEU, hEW⟩ := ha_shift hM hΔ hw.1.1.1
  have hfeas : M.HAFeasible e (M.shift (M.EU e w - M.ubar) w) := by
    refine ⟨⟨hadm, by rw [hEU]; linarith⟩, fun e' => ?_⟩
    rw [hEU, hEU]; linarith [hw.1.2 e']
  have := hw.2 _ _ hfeas
  rw [ha_OP_eq hM hadm, ha_OP_eq hM hw.1.1.1] at this
  linarith [hEW e]

/-- **Footnote 9** (MWG, p. 487). The optimal contract under unobservable effort is a constrained
Pareto optimum: no contract satisfying the same incentive constraints makes the owner and the
manager both weakly better off and one of them strictly better off: any such contract gives
both parties exactly what they get under `w`. -/
theorem footnote_9 {M : HAModel ε} (hM : M.Standing) {e : ε} {w : ℝ → ℝ}
    (hw : M.IsHAOptimal e w) {e' : ε} {w' : ℝ → ℝ} (hw' : M.HAFeasible e' w')
    (hO : M.OP e w ≤ M.OP e' w') :
    M.OP e' w' = M.OP e w ∧ M.EU e' w' = M.EU e w := by
  have h1 := hw.2 e' w' hw'
  have hOeq : M.OP e' w' = M.OP e w := le_antisymm h1 hO
  have hopt' : M.IsHAOptimal e' w' := ⟨hw', fun e'' w'' h => hOeq ▸ hw.2 e'' w'' h⟩
  exact ⟨hOeq, by rw [ha_optimal_binds hM hopt', ha_optimal_binds hM hw]⟩

/-- **The likelihood-ratio form of (14.B.10)** (MWG, p. 485). Let `ŵ` be the fixed wage with
`1 / v'(ŵ) = γ`. If `w` satisfies (14.B.10) at `π` with `μ > 0` and `v'` is strictly decreasing,
then `w(π) > ŵ` if `f(π | e_L) / f(π | e_H) < 1`, and `w(π) < ŵ` if the ratio exceeds `1`. -/
theorem ha_wage_vs_what {M : HAModel ε} (hda : StrictAnti M.dv) (hdv : ∀ w, 0 < M.dv w)
    {eL eH : ε} {w : ℝ → ℝ} {γ μ x what : ℝ} (hμ : 0 < μ)
    (hfoc : 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x))
    (hwhat : 1 / M.dv what = γ) :
    (M.f eL x / M.f eH x < 1 → what < w x) ∧ (1 < M.f eL x / M.f eH x → w x < what) := by
  have key : ∀ a b, 1 / M.dv a < 1 / M.dv b → a < b := fun a b h => by
    have := (one_div_lt_one_div (hdv a) (hdv b)).1 h
    exact hda.lt_iff_gt.1 this
  constructor
  · intro hr
    exact key _ _ (by rw [hfoc, hwhat]; nlinarith)
  · intro hr
    exact key _ _ (by rw [hfoc, hwhat]; nlinarith)

/-- **The monotone likelihood ratio property** (MWG, p. 485). If `w` satisfies (14.B.10) at every
profit level with `μ > 0` and `v'` is strictly decreasing, then `w` is nondecreasing in `π` if and
only if the likelihood ratio `f(π | e_L) / f(π | e_H)` is nonincreasing in `π`. -/
theorem ha_monotone_iff_mlrp {M : HAModel ε} (hda : StrictAnti M.dv) (hdv : ∀ w, 0 < M.dv w)
    {eL eH : ε} {w : ℝ → ℝ} {γ μ : ℝ} (hμ : 0 < μ)
    (hfoc : ∀ x, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x)) :
    Monotone w ↔ Antitone fun x => M.f eL x / M.f eH x := by
  have key : ∀ x y, w x ≤ w y ↔ M.f eL y / M.f eH y ≤ M.f eL x / M.f eH x := by
    intro x y
    rw [← hda.le_iff_ge, ← one_div_le_one_div (hdv _) (hdv _), hfoc, hfoc]
    constructor <;> intro h <;> nlinarith
  exact ⟨fun h x y hxy => (key x y).1 (h hxy), fun h x y hxy => (key x y).2 (h hxy)⟩

/-- **p. 486; Proposition 14.B.3, "a larger expected wage payment"**. With a strictly concave `v`
and `g(e_H) > g(e_L)`, every scheme satisfying (i) and (ii_H) for `e_H` has expected wage strictly
above the observable-effort wage `w*_{e_H}` (Jensen's inequality). -/
theorem ha_EW_gt_of_IC {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {eL eH : ε} (hg : M.g eL < M.g eH) {w : ℝ → ℝ} (hw : M.ObsFeasible eH w)
    (hii : M.EU eL w ≤ M.EU eH w) {wH : ℝ} (hwH : M.v wH = M.ubar + M.g eH) :
    wH < M.EW eH w := by
  rcases (ha_cost_lower_bound hM hw hwH).lt_or_eq with h | h
  · exact h
  exfalso
  have h1 := ha_EV_le hM hw.1 eH
  have h2 := hw.2
  unfold EU at h2
  have heq : M.EV eH w = M.v (M.EW eH w) := by rw [← h, hwH] at h1 ⊢; linarith
  have hae := tpa_jensen_eq hsc hM.v_deriv (hM.f_pos eH) (hM.f_int eH) (hM.f_one eH)
    (hw.1.2 eH).1 (hw.1.2 eH).2 heq
  have hae' : ∀ᵐ x ∂M.ν, w x = M.EW eH w := hae
  have hEV : ∀ e, M.EV e w = M.v (M.EW eH w) := by
    intro e
    have : M.EV e w = M.EV e (fun _ => M.EW eH w) := by
      unfold EV
      refine integral_congr_ae ?_
      filter_upwards [hae'] with x hx
      rw [hx]
    rw [this, ha_EV_const hM]
  unfold EU at hii
  rw [hEV, hEV] at hii
  linarith

/-- **Proposition 14.B.3** (MWG, p. 487). Two effort levels, `g(e_L) < g(e_H)`, a strictly risk
averse manager (`v` strictly concave). (a) A scheme satisfying (14.B.10) with complementary
slackness implements `e_H` optimally; (b) every optimal scheme for `e_H` gives the manager exactly
`ū` and (c) has an expected wage strictly above the observable-effort wage `w*_{e_H}`; (d) the
optimal scheme for `e_L` is the observable-effort fixed wage. -/
theorem proposition_14_B_3 {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {eL eH : ε} (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (hwH : M.v wH = M.ubar + M.g eH) :
    (∀ w : ℝ → ℝ, M.Adm w → ∀ γ μ : ℝ, 0 ≤ γ → 0 ≤ μ →
      (∀ᵐ x ∂M.ν, 1 / M.dv (w x) = γ + μ * (1 - M.f eL x / M.f eH x)) →
      M.ubar ≤ M.EU eH w → M.EU eL w ≤ M.EU eH w → γ * (M.EU eH w - M.ubar) = 0 →
      μ * (M.EU eH w - M.EU eL w) = 0 → M.IsHACostMin eH w) ∧
    (∀ w, M.IsHACostMin eH w → M.EU eH w = M.ubar ∧ wH < M.EW eH w) ∧
    M.IsHACostMin eL (fun _ => wL) := by
  refine ⟨fun w hw γ μ hγ hμ hfoc hi hii h1 h2 => ha_kt_sufficient hM hE hw hγ hμ hfoc hi hii h1 h2,
    fun w hw => ⟨footnote_8 hM hw, ha_EW_gt_of_IC hM hsc hg hw.1.1 (hw.1.2 eL) hwH⟩,
    ha_implement_low hM (fun e => ?_) hwL⟩
  rcases hE e with rfl | rfl
  · exact le_rfl
  · exact hg.le

/-- **Proposition 14.B.3, welfare loss** (MWG, p. 487). If with observable effort `e_H` is
strictly better than `e_L` (`∫ π f(π|e_H) - w*_{e_H} > ∫ π f(π|e_L) - w*_{e_L}`), then every
contract feasible under unobservable effort gives the owner strictly less than his
observable-effort payoff. (With a tie the claim fails: see `ha_no_loss_of_tie`.) -/
theorem ha_welfare_loss {M : HAModel ε} (hM : M.Standing) (hsc : StrictConcaveOn ℝ univ M.v)
    {eL eH : ε} (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (hwH : M.v wH = M.ubar + M.g eH)
    (hstrict : M.GP eL - wL < M.GP eH - wH) {e : ε} {w : ℝ → ℝ} (hw : M.HAFeasible e w) :
    M.OP e w < M.GP eH - wH := by
  rw [ha_OP_eq hM hw.1.1]
  rcases hE e with rfl | rfl
  · have := ha_cost_lower_bound hM hw.1 hwL; linarith
  · have := ha_EW_gt_of_IC hM hsc hg hw.1 (hw.2 eL) hwH; linarith

/-- With a tie between `e_L` and `e_H` under observability there is no welfare loss: the
observable-effort fixed wage for `e_L` is feasible under unobservable effort and attains the
observable-effort payoff (refining the wording of Proposition 14.B.3, see corrections). -/
theorem ha_no_loss_of_tie {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (htie : M.GP eL - wL = M.GP eH - wH) :
    M.HAFeasible eL (fun _ => wL) ∧ M.OP eL (fun _ => wL) = M.GP eH - wH := by
  have hlow : ∀ e', M.g eL ≤ M.g e' := fun e' => by
    rcases hE e' with rfl | rfl
    · exact le_rfl
    · exact hg.le
  refine ⟨(ha_implement_low hM hlow hwL).1, ?_⟩
  rw [ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM, htie]

/-- **Downward distortion only** (MWG, p. 487). If `e_L` is strictly optimal under observable
effort, every optimal contract under unobservable effort implements `e_L`. -/
theorem ha_no_upward_distortion {M : HAModel ε} (hM : M.Standing) {eL eH : ε}
    (hE : ∀ e, e = eL ∨ e = eH) (hg : M.g eL < M.g eH) {wL wH : ℝ}
    (hwL : M.v wL = M.ubar + M.g eL) (hwH : M.v wH = M.ubar + M.g eH)
    (hstrict : M.GP eH - wH < M.GP eL - wL) {e : ε} {w : ℝ → ℝ} (hw : M.IsHAOptimal e w) :
    e = eL := by
  rcases hE e with rfl | rfl
  · rfl
  exfalso
  have hlow : ∀ e', M.g eL ≤ M.g e' := fun e' => by
    rcases hE e' with rfl | rfl
    · exact le_rfl
    · exact hg.le
  have h1 := hw.2 _ _ (ha_implement_low hM hlow hwL).1
  rw [ha_OP_eq hM (ha_const_adm hM _), ha_EW_const hM, ha_OP_eq hM hw.1.1.1] at h1
  have := ha_cost_lower_bound hM hw.1.1 hwH
  linarith

end HAModel

end MWG.PrincipalAgent
