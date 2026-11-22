/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.WelfareApprox
import MWGClassicalDemand.AppendixAContinuity

/-!
# Welfare approximations: footnote 28 (CV) and the comparisons on pp. 89-91

MWG, Section 3.I, pp. 89-91, footnote 28.

* Footnote 28, the compensating variation (`footnote_3_I_28_cv`): as a function of the price
  `s` of good `l` in `p¹`, `CV(p¹, p⁰, w) = w - e(p⁰, v(p¹, w))` has derivative `x_l(p⁰, w)`
  at `s = p⁰_l`. The proof needs no differentiability of `e` in `u` or of `v`: for every `s > 0`,
  `(s - p⁰_l) x_l(p¹, w) ≤ CV ≤ (s - p⁰_l) h_l(p⁰, v(p¹, w))` (revealed preference and
  concavity of `e` in `p`), and both bounds' coefficients tend to `x_l(p⁰, w)` (continuity of
  Walrasian demand, Proposition 3.AA.1, and of `v` and `e`).
* p. 89: "if `p¹_1 - p⁰_1` is small, the error involved in using the area variation measure
  becomes small as a fraction of the true welfare change" (`welfare_av_relative_error`,
  `welfare_ev_relative_error`), and the same holds for any measure with the same derivative
  (`econ_relative_error_of_deriv`).
* pp. 90-91, (3.I.9): the welfare change computed from the first-order Taylor approximation
  `h̃` of the Hicksian demand is a second-order expansion of the expenditure function:
  `e(p¹, u⁰) - e(p⁰, u⁰) - [h_l (s - p⁰_l) + ½ ∂h_l/∂p_l (s - p⁰_l)²] = o((s - p⁰_l)²)`
  (`equation_3_I_9_second_order`), from a general second-order Taylor lemma
  (`econ_second_order_taylor`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology Asymptotics

variable {L : ℕ}

/-- `priceLine (priceLine p l s) l t = priceLine p l t`. -/
theorem econ_priceLine_priceLine (p : Fin L → ℝ) (l : Fin L) (s t : ℝ) :
    priceLine (priceLine p l s) l t = priceLine p l t := by
  simp [priceLine]

/-- **Footnote 28** (MWG, p. 90), the compensating variation. With `u` continuous, strictly
quasiconcave, representing a locally nonsatiated `≿`, and `xs` the Walrasian demand function:
as a function of the price `s` of good `l` in `p¹`, `CV(p¹, p⁰, w)` has derivative `x_l(p⁰, w)`
at `s = p⁰_l`. -/
theorem footnote_3_I_28_cv {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (l : Fin L) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun s => compensatingVariation u (priceLine p₀ l s) p₀ w) (xs p₀ w l)
      (p₀ l) := by
  set a := p₀ l with hadef
  have ha : 0 < a := hp₀ l
  have hself : priceLine p₀ l a = p₀ := by simp [priceLine, hadef]
  set CV := fun s => compensatingVariation u (priceLine p₀ l s) p₀ w with hCV
  have hcv : ∀ s, CV s = w - expenditure u p₀ (indirectUtility u (priceLine p₀ l s) w) := by
    intro s
    simp only [hCV, compensatingVariation, equation_3_E_1_left hrep hu hlns hp₀ hw.le]
  have hcv0 : CV a = 0 := by
    rw [hcv, hself, equation_3_E_1_left hrep hu hlns hp₀ hw.le, sub_self]
  -- the two bounds
  set A := fun s => xs (priceLine p₀ l s) w l with hA
  set B := fun s => hicksianOf u xs p₀ (indirectUtility u (priceLine p₀ l s) w) l with hB
  have hlow : ∀ s, 0 < s → (s - a) * A s ≤ CV s := by
    intro s hs
    have hps := priceLine_pos hp₀ l hs
    have hx := hxs _ _ hps hw.le
    set x := xs (priceLine p₀ l s) w
    have hxK : x ∈ empConstraintSet u (indirectUtility u (priceLine p₀ l s) w) :=
      ⟨hx.1.1, (indirectUtility_eq_of_mem hx).le⟩
    have he := supportFn_le (exp_bddBelow hp₀ _) hxK
    have hwal := proposition_3_D_2_ii hrep hlns hx
    have hdot := priceLine_dot (priceLine p₀ l s) l (a - s) x
    have hps_l : priceLine p₀ l s l = s := by simp [priceLine]
    rw [hps_l, show s + (a - s) = a by ring, econ_priceLine_priceLine, hself, hwal] at hdot
    rw [hcv]
    change expenditure u p₀ _ ≤ p₀ ⬝ᵥ x at he
    simp only [hA]
    nlinarith
  have hup : ∀ s, 0 < s → CV s ≤ (s - a) * B s := by
    intro s hs
    have hps := priceLine_pos hp₀ l hs
    have hub := relations_indirectUtility_gt_zero hrep hu hlns hps hw
    have hne := welfare_v_attainable hu hps hw.le
    have hmem := hicksianOf_mem hrep hu hlns hxs hp₀ hub hne
    set h := hicksianOf u xs p₀ (indirectUtility u (priceLine p₀ l s) w)
    have hlin := expenditure_le_linear hmem hps
    rw [equation_3_E_1_left hrep hu hlns hps hw.le] at hlin
    have hdot := priceLine_dot p₀ l (s - a) h
    rw [← hadef, show a + (s - a) = s by ring] at hdot
    rw [hcv]
    simp only [hB]
    nlinarith [hlin.1, hlin.2]
  -- continuity of the bounds' coefficients
  have hsing : ∀ p w, PWDomain p w → walrasianDemand u p w = {xs p w} := by
    intro p w' hd
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hxs p w' hd.1 hd.2.le, fun y hy => ?_⟩
    exact proposition_3_D_2_iii_unique hq p w' hy (hxs p w' hd.1 hd.2.le)
  have hxc := proposition_3_AA_1_continuous hu hsing
  have hopen : IsOpen (pwDomainSet L) := by
    have : pwDomainSet L = {q : (Fin L → ℝ) × ℝ | StrictlyPositive q.1} ∩ {q | 0 < q.2} := by
      ext q; rfl
    rw [this]
    exact ((relations_isOpen_strictlyPositive L).preimage continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)
  have hxcat : ∀ q : (Fin L → ℝ) × ℝ, PWDomain q.1 q.2 →
      ContinuousAt (fun q : (Fin L → ℝ) × ℝ => xs q.1 q.2) q :=
    fun q hq' => hxc.continuousAt (hopen.mem_nhds hq')
  have hline : Tendsto (fun s => priceLine p₀ l s) (𝓝 a) (𝓝 p₀) := by
    have := (priceLine_hasDerivAt p₀ l a).continuousAt.tendsto
    rwa [hself] at this
  have hAt : Tendsto A (𝓝 a) (𝓝 (xs p₀ w l)) := by
    have h1 : Tendsto (fun s => (priceLine p₀ l s, w)) (𝓝 a) (𝓝 (p₀, w)) :=
      hline.prodMk_nhds tendsto_const_nhds
    have h2 := (hxcat (p₀, w) ⟨hp₀, hw⟩).tendsto.comp h1
    exact ((continuous_apply l).tendsto _).comp h2
  have hBt : Tendsto B (𝓝 a) (𝓝 (xs p₀ w l)) := by
    -- `v(p¹, w) → v(p⁰, w)` and `e(p⁰, ·)` is continuous there
    have hv : Tendsto (fun s => indirectUtility u (priceLine p₀ l s) w) (𝓝 a)
        (𝓝 (indirectUtility u p₀ w)) :=
      (exp_continuousAt_indirectUtility_prices hu hp₀ hw.le).tendsto.comp hline
    have hdom : ∀ᶠ s in 𝓝 a,
        (p₀, indirectUtility u (priceLine p₀ l s) w) ∈ expDomain u := by
      filter_upwards [lt_mem_nhds ha] with s hs
      exact ⟨hp₀, welfare_v_attainable hu (priceLine_pos hp₀ l hs) hw.le⟩
    have hpair : Tendsto (fun s => (p₀, indirectUtility u (priceLine p₀ l s) w)) (𝓝 a)
        (𝓝[expDomain u] (p₀, indirectUtility u p₀ w)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds hv, hdom⟩
    have hE := ((proposition_3_E_2_iv hrep hu hlns) (p₀, indirectUtility u p₀ w)
      ⟨hp₀, welfare_v_attainable hu hp₀ hw.le⟩).tendsto.comp hpair
    simp only [Function.comp_def, equation_3_E_1_left hrep hu hlns hp₀ hw.le] at hE
    have h2 := (hxcat (p₀, w) ⟨hp₀, hw⟩).tendsto.comp (tendsto_const_nhds.prodMk_nhds hE)
    exact ((continuous_apply l).tendsto _).comp h2
  -- squeeze the difference quotient
  rw [hasDerivAt_iff_tendsto_slope]
  have hmin : Tendsto (fun s => min (A s) (B s)) (𝓝[≠] a) (𝓝 (xs p₀ w l)) := by
    have := hAt.min hBt
    rw [min_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmax : Tendsto (fun s => max (A s) (B s)) (𝓝[≠] a) (𝓝 (xs p₀ w l)) := by
    have := hAt.max hBt
    rw [max_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] a, 0 < s ∧ s ≠ a :=
    (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds ha)).and self_mem_nhdsWithin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax ?_ ?_
  · filter_upwards [hev] with s ⟨hs, hsa⟩
    rw [slope_def_field, hcv0, sub_zero]
    rcases lt_or_gt_of_ne hsa with hlt | hgt
    · refine min_le_of_right_le ?_
      rw [le_div_iff_of_neg (by linarith)]
      linarith [hup s hs]
    · refine min_le_of_left_le ?_
      rw [le_div_iff₀ (by linarith)]
      linarith [hlow s hs]
  · filter_upwards [hev] with s ⟨hs, hsa⟩
    rw [slope_def_field, hcv0, sub_zero]
    rcases lt_or_gt_of_ne hsa with hlt | hgt
    · refine le_max_of_le_left ?_
      rw [div_le_iff_of_neg (by linarith)]
      linarith [hlow s hs]
    · refine le_max_of_le_right ?_
      rw [div_le_iff₀ (by linarith)]
      linarith [hup s hs]

/-- Two measures `F`, `G` vanishing at `a` with the same nonzero derivative `c` there have
relative error `(F - G)/G → 0` as `s → a`. -/
theorem econ_relative_error_of_deriv {F G : ℝ → ℝ} {a c : ℝ} (hF : HasDerivAt F c a)
    (hG : HasDerivAt G c a) (hF0 : F a = 0) (hG0 : G a = 0) (hc : c ≠ 0) :
    Tendsto (fun s => (F s - G s) / G s) (𝓝[≠] a) (𝓝 0) := by
  have h1 := hF.tendsto_slope
  have h2 := hG.tendsto_slope
  have h3 := (h1.sub h2).div h2 hc
  rw [sub_self, zero_div] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - a ≠ 0 := sub_ne_zero.mpr hs
  change (slope F a s - slope G a s) / slope G a s = _
  rw [slope_def_field, slope_def_field, hF0, hG0, sub_zero, sub_zero, ← sub_div,
    div_div_div_cancel_right₀ hs']

/-- **Section 3.I** (MWG, p. 89). For a small change in the price of good `l`, the error of the
area variation `AV(p¹, p⁰, w)` is small as a fraction of the true welfare change
`CV(p¹, p⁰, w)`, when `x_l(p⁰, w) ≠ 0`. -/
theorem welfare_av_relative_error {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (l : Fin L) {w : ℝ} (hw : 0 < w)
    (hc : ContinuousOn (fun t => xs (priceLine p₀ l t) w l) (Set.Ioi 0))
    (hx0 : xs p₀ w l ≠ 0) :
    Tendsto (fun s => (areaVariation xs p₀ l s (p₀ l) w -
        compensatingVariation u (priceLine p₀ l s) p₀ w) /
        compensatingVariation u (priceLine p₀ l s) p₀ w) (𝓝[≠] (p₀ l)) (𝓝 0) := by
  have hself : priceLine p₀ l (p₀ l) = p₀ := by simp [priceLine]
  refine econ_relative_error_of_deriv (footnote_3_I_28_av hp₀ l hc)
    (footnote_3_I_28_cv hrep hu hlns hq hxs hp₀ l hw) ?_ ?_ hx0
  · simp [areaVariation]
  · simp only [compensatingVariation, hself, sub_self]

/-- **Section 3.I** (MWG, p. 89, footnote 27). The same for the equivalent variation:
`(EV - CV)/CV → 0` for a small change in the price of good `l`, when `x_l(p⁰, w) ≠ 0`. -/
theorem welfare_ev_relative_error {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (l : Fin L) {w : ℝ} (hw : 0 < w)
    (hx0 : xs p₀ w l ≠ 0) :
    Tendsto (fun s => (equivalentVariation u (priceLine p₀ l s) p₀ w -
        compensatingVariation u (priceLine p₀ l s) p₀ w) /
        compensatingVariation u (priceLine p₀ l s) p₀ w) (𝓝[≠] (p₀ l)) (𝓝 0) := by
  have hself : priceLine p₀ l (p₀ l) = p₀ := by simp [priceLine]
  refine econ_relative_error_of_deriv (footnote_3_I_28_ev hrep hu hlns hq hxs hp₀ l hw)
    (footnote_3_I_28_cv hrep hu hlns hq hxs hp₀ l hw) ?_ ?_ hx0
  · simp only [equivalentVariation, hself, sub_self]
  · simp only [compensatingVariation, hself, sub_self]

/-- A second-order Taylor expansion with Peano remainder: if `F' = H` near `a` and `H` has
derivative `σ` at `a`, then `F(s) = F(a) + H(a)(s - a) + ½σ(s - a)² + o((s - a)²)`. -/
theorem econ_second_order_taylor {F H : ℝ → ℝ} {a σ : ℝ}
    (hF : ∀ᶠ t in 𝓝 a, HasDerivAt F (H t) t) (hH : HasDerivAt H σ a) :
    (fun s => F s - F a - H a * (s - a) - σ / 2 * (s - a) ^ 2) =o[𝓝 a]
      fun s => (s - a) ^ 2 := by
  rw [isLittleO_iff]
  intro c hc
  have ho := (hasDerivAt_iff_isLittleO.mp hH).def hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hF.and ho)
  filter_upwards [Metric.ball_mem_nhds a hδ] with s hs
  set g := fun t => F t - F a - H a * (t - a) - σ / 2 * (t - a) ^ 2 with hg
  have habs : ∀ t ∈ Set.uIcc a s, |t - a| ≤ |s - a| := by
    intro t ht
    rcases le_total a s with has | has
    · rw [Set.uIcc_of_le has] at ht
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]
      linarith [ht.2]
    · rw [Set.uIcc_of_ge has] at ht
      rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]
      linarith [ht.1]
  have hsub : Set.uIcc a s ⊆ Metric.ball a δ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact (habs t ht).trans_lt hs
  have hderiv : ∀ t ∈ Set.uIcc a s,
      HasDerivWithinAt g (H t - H a - σ * (t - a)) (Set.uIcc a s) t := by
    intro t ht
    have hFt := (hball t (hsub ht)).1
    have h1 : HasDerivAt (fun t => H a * (t - a)) (H a) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (H a)
    have h2 : HasDerivAt (fun t => σ / 2 * (t - a) ^ 2) (σ * (t - a)) t := by
      have hsq := (((hasDerivAt_id t).sub_const a).mul
        ((hasDerivAt_id t).sub_const a)).const_mul (σ / 2)
      convert hsq using 1
      · funext y
        simp only [id, Pi.mul_apply]
        ring
      · simp only [id]
        ring
    have := ((hFt.sub_const (F a)).sub h1).sub h2
    exact this.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc a s, ‖H t - H a - σ * (t - a)‖ ≤ c * ‖s - a‖ := by
    intro t ht
    have h := (hball t (hsub ht)).2
    have htl : ‖t - a‖ ≤ ‖s - a‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact habs t ht
    have : H t - H a - σ * (t - a) = H t - H a - (t - a) • σ := by
      rw [smul_eq_mul, mul_comm]
    rw [this]
    exact h.trans (mul_le_mul_of_nonneg_left htl hc.le)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc a s) Set.left_mem_uIcc Set.right_mem_uIcc
  have hga : g a = 0 := by simp [hg]
  rw [hga, sub_zero] at hmv
  calc ‖g s‖ ≤ c * ‖s - a‖ * ‖s - a‖ := hmv
    _ = c * ‖(s - a) ^ 2‖ := by rw [norm_pow]; ring

/-- **Equation (3.I.9)** (MWG, pp. 90-91), second-order accuracy. Let `u` be continuous,
strictly quasiconcave, representing a locally nonsatiated `≿`, `xs` the Walrasian demand,
`u⁰ > u(0)` attainable, and let the Hicksian demand `t ↦ h_l(p⁰ with p_l = t, u⁰)` have
derivative `σ = ∂h_l/∂p_l(p⁰, u⁰)` at `p⁰_l`. Then the welfare change computed from the
first-order approximation `h̃_l(t) = h_l(p⁰, u⁰) + σ(t - p⁰_l)`, namely
`∫_{p⁰_l}^{s} h̃_l = h_l(p⁰, u⁰)(s - p⁰_l) + ½σ(s - p⁰_l)²`, approximates
`e(p¹, u⁰) - e(p⁰, u⁰)` up to `o((s - p⁰_l)²)`: it is a second-order expansion of `e`. -/
theorem equation_3_I_9_second_order {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀) (l : Fin L) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {σ : ℝ}
    (hσ : HasDerivAt (fun t => hicksianOf u xs (priceLine p₀ l t) ub l) σ (p₀ l)) :
    (fun s => expenditure u (priceLine p₀ l s) ub - expenditure u p₀ ub -
        (hicksianOf u xs p₀ ub l * (s - p₀ l) + σ / 2 * (s - p₀ l) ^ 2)) =o[𝓝 (p₀ l)]
      fun s => (s - p₀ l) ^ 2 := by
  have hself : priceLine p₀ l (p₀ l) = p₀ := by simp [priceLine]
  obtain ⟨hd, -, -⟩ := expenditure_line_integral hrep hu hlns hq hxs hp₀ l hub hne
  have hF : ∀ᶠ t in 𝓝 (p₀ l), HasDerivAt (fun s => expenditure u (priceLine p₀ l s) ub)
      (hicksianOf u xs (priceLine p₀ l t) ub l) t := by
    filter_upwards [lt_mem_nhds (hp₀ l)] with t ht
    exact hd t ht
  have := econ_second_order_taylor hF hσ
  refine this.congr_left fun s => ?_
  simp only [hself]
  ring

end MWG.ClassicalDemand
