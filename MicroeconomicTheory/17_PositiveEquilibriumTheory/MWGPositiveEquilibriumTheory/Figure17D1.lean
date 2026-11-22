/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.TwoCountries
import MWGGeneralEquilibriumExamples.MultipleEquilibria

/-!
# Figure 17.D.1: the three equilibria of Example 15.B.2 are regular (MWG pp. 590-591)

The economy of Example 15.B.2 (Chapter 15's `ex15B2Economy`: utilities `x₁₁ - x₂₁⁻⁸/8`,
`-x₁₂⁻⁸/8 + x₂₂`, endowments `(2, r)`, `(r, 2)`, `r = 2^{8/9} - 2^{1/9}`) has the normalized
equilibria `p₁ ∈ {1/2, 1, 2}` (`example_15_B_2`). With `t = p₁^{1/9}` (Chapter 15's
`exercise_15_B_5_offerCurves`) the excess demand is
`z₁(p₁, 1) = G(t) = r/t⁹ - 1/t⁸ + 1/t - r` (`f17_excessDemand`), and
`G'(t) = -9r/t¹⁰ + 8/t⁹ - 1/t²` (`f17_hasDerivAt_G`). With `a = 2^{1/9}`:
`G'(1) = 7 - 9r > 0`, `G'(a) = a⁻¹⁰ a(17 - 10a⁷) < 0`, `G'(1/a) = 17a² - 20 < 0`.
So the three equilibria are regular, with indices `+1, -1, +1` (`figure_17_D_1`), as the figure
shows (p. 591: "every equilibrium regular").
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

/-- `G(t) = r/t⁹ - 1/t⁸ + 1/t - r`: `z₁(t⁹, 1)` in Example 15.B.2. -/
noncomputable def f17G (t : ℝ) : ℝ := ex15B2r * (t ^ 9)⁻¹ - (t ^ 8)⁻¹ + t⁻¹ - ex15B2r

/-- `G'(t) = -9r t⁻¹⁰ + 8t⁻⁹ - t⁻²`. -/
noncomputable def f17G' (t : ℝ) : ℝ := -9 * ex15B2r * t⁻¹ ^ 10 + 8 * t⁻¹ ^ 9 - t⁻¹ ^ 2

theorem f17_hasDerivAt_G {t : ℝ} (ht : t ≠ 0) : HasDerivAt f17G (f17G' t) t := by
  have h9 := ((hasDerivAt_pow 9 t).inv (pow_ne_zero 9 ht)).const_mul ex15B2r
  have h8 := (hasDerivAt_pow 8 t).inv (pow_ne_zero 8 ht)
  have h1 := hasDerivAt_inv ht
  have h := ((h9.sub h8).add h1).sub_const ex15B2r
  unfold f17G f17G'
  convert h using 1
  field_simp
  ring

/-- `(q^{1/9})⁹ = q` for `q ≥ 0`. -/
theorem f17_rpow_pow {q : ℝ} (hq : 0 ≤ q) : (q ^ ((1 : ℝ) / 9)) ^ 9 = q := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num

/-- At `p = (q, 1) ≫ 0`, with `t = q^{1/9}`, the excess demand of Example 15.B.2 is
`(G(t), t + r t⁹ - t⁸ - r)`. -/
theorem f17_excessDemand {q : ℝ} (hq : 0 < q) :
    excessDemand ex15B2Economy ![q, 1] =
      ![f17G (q ^ ((1 : ℝ) / 9)), q ^ ((1 : ℝ) / 9) + ex15B2r * (q ^ ((1 : ℝ) / 9)) ^ 9 -
        (q ^ ((1 : ℝ) / 9)) ^ 8 - ex15B2r] := by
  set t := q ^ ((1 : ℝ) / 9) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hq _
  have hp : StrictlyPositive (![q, 1] : Fin 2 → ℝ) := fun l => by fin_cases l <;> simp [hq]
  have ht9 : t ^ 9 = (![q, 1] : Fin 2 → ℝ) 0 / ![q, 1] 1 := by
    have : t ^ 9 = q := f17_rpow_pow hq.le
    rw [this]; simp
  obtain ⟨hd0, hd1, -, -⟩ := exercise_15_B_5_offerCurves hp ht ht9
  funext l
  rw [excessDemand_apply, Fin.sum_univ_two, demandFn_eq _ hd0, demandFn_eq _ hd1]
  have ht0 : t ≠ 0 := ht.ne'
  fin_cases l
  · simp [ex15B2OC1, ex15B2OC2, ex15B2Economy, f17G, div_eq_mul_inv]
    ring
  · simp [ex15B2OC1, ex15B2OC2, ex15B2Economy]
    ring

/-- At a normalized equilibrium `(q₀, 1)` of Example 15.B.2 with `G'(q₀^{1/9}) ≠ 0`, the
equilibrium is regular and its index is `-sign G'(q₀^{1/9})`. -/
theorem f17_regular {q0 : ℝ} (hq0 : 0 < q0) (heq : excessDemand ex15B2Economy ![q0, 1] = 0)
    (hG : f17G' (q0 ^ ((1 : ℝ) / 9)) ≠ 0) :
    IsRegularEqm (excessDemand ex15B2Economy) (vec1 q0) ∧
      eqmIndex (excessDemand ex15B2Economy) (vec1 q0) = -itgSgn (f17G' (q0 ^ ((1 : ℝ) / 9))) := by
  set z := excessDemand ex15B2Economy with hz
  set F : ℝ → ℝ := fun q => f17G (q ^ ((1 : ℝ) / 9)) with hF
  set d := f17G' (q0 ^ ((1 : ℝ) / 9)) * ((1 / 9) * q0 ^ ((1 : ℝ) / 9 - 1)) with hd
  have hfac : 0 < (1 / 9 : ℝ) * q0 ^ ((1 : ℝ) / 9 - 1) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hq0 _)
  have hFd : HasDerivAt F d q0 := by
    have hpow : HasDerivAt (fun q : ℝ => q ^ ((1 : ℝ) / 9)) ((1 / 9) * q0 ^ ((1 : ℝ) / 9 - 1))
        q0 := Real.hasDerivAt_rpow_const (Or.inl hq0.ne')
    exact (f17_hasDerivAt_G (Real.rpow_pos_of_pos hq0 ((1 : ℝ) / 9)).ne').comp q0 hpow
  have hpos : ∀ᶠ q in 𝓝 q0, 0 < q := lt_mem_nhds hq0
  have hnear : normED z =ᶠ[𝓝 (vec1 q0)] fun v _ => F (v 0) := by
    have : Tendsto (fun v : Fin 1 → ℝ => v 0) (𝓝 (vec1 q0)) (𝓝 q0) := by
      simpa [vec1] using (continuous_apply (0 : Fin 1)).tendsto (vec1 q0)
    filter_upwards [this.eventually hpos] with v hv
    funext l
    rw [Subsingleton.elim l 0]
    have hnp : normPrice v = ![v 0, 1] := by
      rw [← vec1_apply_zero v, normPrice_vec1]
      rfl
    simp only [normED, truncExcessDemand, hnp, hz, f17_excessDemand hv]
    rfl
  have hdiff : DifferentiableAt ℝ (normED z) (vec1 q0) := by
    have hg : DifferentiableAt ℝ (fun v : Fin 1 → ℝ => fun _ : Fin 1 => F (v 0)) (vec1 q0) := by
      have hc : DifferentiableAt ℝ (F ∘ fun v : Fin 1 → ℝ => v 0) (vec1 q0) :=
        hFd.differentiableAt.comp (vec1 q0) (by fun_prop)
      exact differentiableAt_pi.2 fun _ => hc
    exact hg.congr_of_eventuallyEq hnear
  have hslope : slope2 z q0 = d := by
    have h := two_goods_hasDerivAt hdiff
    have hloc : (fun s => z ![s, 1] 0) =ᶠ[𝓝 q0] F := by
      filter_upwards [hpos] with q hq
      rw [hz, f17_excessDemand hq]; rfl
    exact h.unique (hFd.congr_of_eventuallyEq hloc)
  have heqm : IsNormEqm z (vec1 q0) := by
    unfold IsNormEqm
    rw [normPrice_vec1]
    exact ⟨fun l => by fin_cases l <;> simp [hq0], heq⟩
  have hsgn : itgSgn d = itgSgn (f17G' (q0 ^ ((1 : ℝ) / 9))) := by
    rcases hG.lt_or_gt with h | h
    · rw [itgSgn_neg h, itgSgn_neg (mul_neg_of_neg_of_pos h hfac)]
    · rw [itgSgn_pos h, itgSgn_pos (mul_pos h hfac)]
  refine ⟨⟨heqm, hdiff, ?_⟩, ?_⟩
  · rw [det_eq_slope2, hslope]; exact mul_ne_zero hG hfac.ne'
  · rw [eqmIndex_two]
    change -itgSgn (slope2 z q0) = _
    rw [hslope, hsgn]

/-- Bounds on `r` and `a`: `a⁹ = 2`, `r = a⁸ - a`, `1.08 < a < 1.081`. -/
theorem f17_facts : ex15B2a ^ 9 = 2 ∧ ex15B2r * ex15B2a = 2 - ex15B2a ^ 2 ∧
    1.08 < ex15B2a ∧ ex15B2a < 1.081 := by
  refine ⟨ex15B2a_pow, ?_, ex15B2a_bounds⟩
  rw [ex15B2r_eq]
  linear_combination ex15B2a_pow

/-- **Figure 17.D.1** (MWG, pp. 590-591). The three normalized equilibria `p₁ = 1/2, 1, 2` of
Example 15.B.2 are regular, with indices `+1`, `-1`, `+1` (the slope of `z₁(·, 1)` is negative,
positive, negative). -/
theorem figure_17_D_1 :
    (IsRegularEqm (excessDemand ex15B2Economy) (vec1 (1 / 2)) ∧
      eqmIndex (excessDemand ex15B2Economy) (vec1 (1 / 2)) = 1) ∧
    (IsRegularEqm (excessDemand ex15B2Economy) (vec1 1) ∧
      eqmIndex (excessDemand ex15B2Economy) (vec1 1) = -1) ∧
    (IsRegularEqm (excessDemand ex15B2Economy) (vec1 2) ∧
      eqmIndex (excessDemand ex15B2Economy) (vec1 2) = 1) := by
  obtain ⟨h9, hra, ha1, ha2⟩ := f17_facts
  set a := ex15B2a with ha
  set r := ex15B2r with hr
  have ha0 : 0 < a := by linarith
  have hb : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0.ne'
  have hb0 : 0 < a⁻¹ := inv_pos.2 ha0
  -- the three values of `t = q^{1/9}`
  have t1 : (1 : ℝ) ^ ((1 : ℝ) / 9) = 1 := Real.one_rpow _
  have t2 : (2 : ℝ) ^ ((1 : ℝ) / 9) = a := rfl
  have t3 : (1 / 2 : ℝ) ^ ((1 : ℝ) / 9) = a⁻¹ := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
    rw [ha, ex15B2a]
  have hsq : a ^ 2 < 1.17 := by nlinarith
  have hr8 : r = a ^ 8 - a := ex15B2r_eq
  have hrb : r = 2 * a⁻¹ - a := by
    have : r * a * a⁻¹ = (2 - a ^ 2) * a⁻¹ := by rw [hra]
    rw [mul_assoc, mul_inv_cancel₀ ha0.ne', mul_one] at this
    rw [this]; field_simp
  have i9 : (a ^ 9)⁻¹ = 1 / 2 := by rw [h9]; norm_num
  have i8 : (a ^ 8)⁻¹ = a / 2 := inv_eq_of_mul_eq_one_right (by
    rw [show a ^ 8 * (a / 2) = a ^ 9 / 2 by ring, h9]; norm_num)
  have b9 : a⁻¹ ^ 9 = 1 / 2 := by rw [inv_pow, i9]
  have b8 : a⁻¹ ^ 8 = a / 2 := by rw [inv_pow, i8]
  have b10 : a⁻¹ ^ 10 = a⁻¹ / 2 := by rw [pow_succ, b9]; ring
  have hrlo : 0.769 < r := ex15B2r_bounds
  -- the three equilibria
  have e1 : excessDemand ex15B2Economy ![1, 1] = 0 := by
    rw [f17_excessDemand one_pos, t1]
    funext l; fin_cases l <;> simp [f17G]
  have e2 : excessDemand ex15B2Economy ![2, 1] = 0 := by
    rw [f17_excessDemand two_pos, t2]
    funext l
    fin_cases l
    · simp only [f17G, Matrix.cons_val_zero, Fin.zero_eta, Pi.zero_apply]
      rw [← hr, i9, i8, hrb]
      field_simp
      ring
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, Pi.zero_apply]
      rw [← hr, h9, hr8]
      ring
  have e3 : excessDemand ex15B2Economy ![1 / 2, 1] = 0 := by
    rw [f17_excessDemand (by norm_num), t3]
    funext l
    fin_cases l
    · simp only [f17G, Matrix.cons_val_zero, Fin.zero_eta, Pi.zero_apply]
      rw [← hr, b9, b8, hrb]
      field_simp
      ring
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, Pi.zero_apply]
      rw [← hr, b9, b8, hrb]
      field_simp
      ring
  -- the three slopes
  have d1 : 0 < f17G' 1 := by
    simp only [f17G', inv_one, one_pow, mul_one]
    rw [← hr]
    nlinarith
  have d2 : f17G' a < 0 := by
    have : f17G' a = 17 / 2 - 10 * a⁻¹ ^ 2 := by
      simp only [f17G']
      rw [← hr, b10, b9]
      have hrb' : r * a⁻¹ = 2 * a⁻¹ ^ 2 - 1 := by
        rw [hrb]; field_simp
      linear_combination (-9 / 2 : ℝ) * hrb'
    rw [this]
    have hinv2 : a⁻¹ ^ 2 * a ^ 2 = 1 := by rw [← mul_pow, hb, one_pow]
    nlinarith
  have d3 : f17G' a⁻¹ < 0 := by
    have : f17G' a⁻¹ = 17 * a ^ 2 - 20 := by
      simp only [f17G', inv_inv]
      rw [← hr, show a ^ 10 = a ^ 9 * a by ring, h9]
      linear_combination (-18 : ℝ) * hra
    rw [this]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h := f17_regular (by norm_num) e3 (by rw [t3]; exact d3.ne)
    rw [t3, itgSgn_neg d3] at h
    exact ⟨h.1, h.2⟩
  · have h := f17_regular one_pos e1 (by rw [t1]; exact d1.ne')
    rw [t1, itgSgn_pos d1] at h
    exact ⟨h.1, h.2⟩
  · have h := f17_regular two_pos e2 (by rw [t2]; exact d2.ne)
    rw [t2, itgSgn_neg d2] at h
    exact ⟨h.1, h.2⟩

end MWG.PositiveEquilibriumTheory
