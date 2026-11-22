/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Hildenbrand
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exercise 4.C.7: a nonincreasing wealth density

MWG, Exercise 4.C.7 (p. 124), first part. Proposition 4.C.4 still holds if the distribution of
wealth has a nonincreasing density `f` on `[0, w̄]`: with `x(p) = ∫₀^w̄ x̃(p, w) f(w) dw`,
`(p' - p)·[x(p') - x(p)] ≤ 0`.

Proof (layer cake): `f(w) = ∫₀^M 1[t < f(w)] dt`, and for each `t` the set `{w : t < f(w)}` is
an initial segment `(0, a]` of `(0, w̄]` up to a null set, because `f` is nonincreasing. On
each initial segment the integrand `g = 2w - p'·x̃(p, w) - p·x̃(p', w)` has nonpositive integral
by the uniform case (`young_square`), and Fubini adds these up. The unimodal counterexample of
the second part is `exercise_4_C_7_unimodal`.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand MeasureTheory

variable {L : ℕ}

/-- **Exercise 4.C.7** (MWG, p. 124), the analytic core. If `g` is integrable on `(0, w̄]` with
`∫₀^a g ≤ 0` for every `a ∈ [0, w̄]`, and `f` is measurable, nonincreasing and between `0` and
`M` on `(0, w̄]`, then `∫₀^w̄ g f ≤ 0`. -/
theorem antitone_weighted_integral_nonpos {g f : ℝ → ℝ} {wb M : ℝ}
    (hg : IntegrableOn g (Set.Ioc 0 wb)) (hgm : Measurable g) (hfm : Measurable f)
    (hf0 : ∀ w ∈ Set.Ioc 0 wb, 0 ≤ f w) (hfM : ∀ w ∈ Set.Ioc 0 wb, f w ≤ M)
    (hanti : AntitoneOn f (Set.Ioc 0 wb))
    (hG : ∀ a, a ≤ wb → ∫ w in Set.Ioc 0 a, g w ≤ 0) :
    ∫ w in Set.Ioc 0 wb, g w * f w ≤ 0 := by
  set M' := max M 0 with hM'
  set F : ℝ → ℝ → ℝ := fun w t => g w * (Set.Iio (f w)).indicator 1 t with hF
  -- the inner integral recovers `g w * f w`
  have hinner : ∀ w ∈ Set.Ioc 0 wb, ∫ t in Set.Ioc 0 M', F w t = g w * f w := by
    intro w hw
    simp only [F]
    rw [integral_const_mul]
    congr 1
    rw [integral_indicator_one measurableSet_Iio, Measure.real,
      Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio (f w) ∩ Set.Ioc 0 M' = Set.Ioo 0 (f w) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.le.trans ((hfM w hw).trans (le_max_left _ _))⟩
    rw [hset, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal (hf0 w hw)]
  have hmeasSet : MeasurableSet {q : ℝ × ℝ | q.2 < f q.1} :=
    measurableSet_lt measurable_snd (hfm.comp measurable_fst)
  have hFm : Measurable (Function.uncurry F) := by
    have : Function.uncurry F = fun q : ℝ × ℝ =>
        g q.1 * ({q : ℝ × ℝ | q.2 < f q.1}.indicator (fun _ => (1 : ℝ)) q) := by
      funext q
      simp [F, Set.indicator, Function.uncurry]
    rw [this]
    exact (hgm.comp measurable_fst).mul (measurable_const.indicator hmeasSet)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc 0 wb)).prod (volume.restrict (Set.Ioc 0 M'))) := by
    have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) M')) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    have hbound := hg.mul_prod (integrable_const (μ := volume.restrict (Set.Ioc (0 : ℝ) M'))
      (1 : ℝ))
    refine hbound.mono hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    simp only [F, Function.uncurry, mul_one, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    by_cases h : q.2 < f q.1 <;> simp [Set.indicator, h]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun w hw => (hinner w hw).symm),
    integral_integral_swap hint]
  apply integral_nonpos_of_ae
  filter_upwards with t
  -- the inner integral in `w` is an integral over an initial segment
  set E := Set.Ioc 0 wb ∩ {w | t < f w} with hE
  have hEm : MeasurableSet E := measurableSet_Ioc.inter (measurableSet_lt measurable_const hfm)
  have hrw : ∫ w in Set.Ioc 0 wb, F w t = ∫ w in E, g w := by
    have : ∀ w, F w t = {w | t < f w}.indicator g w := by
      intro w
      by_cases h : t < f w <;> simp [F, Set.indicator, h]
    simp_rw [this]
    rw [setIntegral_indicator (measurableSet_lt measurable_const hfm)]
  rw [hrw]
  rcases E.eq_empty_or_nonempty with hE0 | hEne
  · rw [hE0, Measure.restrict_empty, integral_zero_measure]
    simp
  have hEbdd : BddAbove E := ⟨wb, fun w hw => hw.1.2⟩
  set a := sSup E with ha
  have haw : a ≤ wb := csSup_le hEne fun w hw => hw.1.2
  have hsub1 : E ⊆ Set.Ioc 0 a := fun w hw => ⟨hw.1.1, le_csSup hEbdd hw⟩
  have hsub2 : Set.Ioo 0 a ⊆ E := by
    intro w hw
    obtain ⟨w', hw'E, hww'⟩ := exists_lt_of_lt_csSup hEne hw.2
    refine ⟨⟨hw.1, hww'.le.trans hw'E.1.2⟩, ?_⟩
    exact lt_of_lt_of_le hw'E.2 (hanti ⟨hw.1, hww'.le.trans hw'E.1.2⟩ hw'E.1 hww'.le)
  have hae : E =ᵐ[volume] Set.Ioc 0 a := by
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · rw [Set.sdiff_eq_empty.mpr hsub1, measure_empty]
    · apply measure_mono_null (Set.sdiff_subset_sdiff_right hsub2)
      apply measure_mono_null (t := ({a} : Set ℝ)) _ Real.volume_singleton
      intro w hw
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      have : ¬ w < a := fun h => h3 ⟨h1, h⟩
      exact le_antisymm h2 (not_lt.mp this)
  rw [setIntegral_congr_set hae]
  exact hG a haw

/-- **Exercise 4.C.7** (MWG, p. 124). Proposition 4.C.4 with a nonincreasing wealth density: if
`x̃` satisfies Walras' law, the weak axiom and takes values in `ℝ^L_+`, with `w ↦ x̃(p, w)`
measurable and integrable on `(0, w̄]`, and `f` is a measurable, nonnegative, bounded,
nonincreasing density on `(0, w̄]`, then `x(p) = ∫₀^w̄ x̃(p, w) f(w) dw` satisfies
`(p' - p)·[x(p') - x(p)] ≤ 0`. -/
theorem exercise_4_C_7 {x : DemandFunction L} (hWA : WeakAxiom x) (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) {wb : ℝ}
    (hmeas : ∀ p, StrictlyPositive p → ∀ l, Measurable fun w => x p w l)
    (hintx : ∀ p, StrictlyPositive p → ∀ l, IntegrableOn (fun w => x p w l) (Set.Ioc 0 wb))
    {f : ℝ → ℝ} {M : ℝ} (hfm : Measurable f) (hf0 : ∀ w ∈ Set.Ioc 0 wb, 0 ≤ f w)
    (hfM : ∀ w ∈ Set.Ioc 0 wb, f w ≤ M) (hanti : AntitoneOn f (Set.Ioc 0 wb))
    {p p' : Fin L → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') :
    (p' - p) ⬝ᵥ (densityDemand x f 0 wb p' - densityDemand x f 0 wb p) ≤ 0 := by
  have hm : ∀ q r, StrictlyPositive r → Measurable fun w => q ⬝ᵥ x r w := by
    intro q r hr
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ => (hmeas r hr l).const_mul (q l)
  have hi : ∀ q r, StrictlyPositive r → IntegrableOn (fun w => q ⬝ᵥ x r w) (Set.Ioc 0 wb) := by
    intro q r hr
    simp only [dotProduct]
    exact integrable_finsetSum _ fun l _ => (hintx r hr l).const_mul (q l)
  have hfb : ∀ᵐ w ∂(volume.restrict (Set.Ioc (0 : ℝ) wb)), ‖f w‖ ≤ max M 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun w hw => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w hw)]
    exact (hfM w hw).trans (le_max_left _ _)
  have hixf : ∀ r, StrictlyPositive r → ∀ l,
      IntegrableOn (fun w => x r w l * f w) (Set.Ioc 0 wb) := fun r hr l =>
    (hintx r hr l).mul_bdd hfm.aestronglyMeasurable hfb
  -- weighted dot products
  have hdot : ∀ q r, StrictlyPositive r →
      ∫ w in Set.Ioc 0 wb, (q ⬝ᵥ x r w) * f w = q ⬝ᵥ densityDemand x f 0 wb r := by
    intro q r hr
    simp only [dotProduct, densityDemand, Finset.sum_mul]
    rw [integral_finsetSum _ fun l _ => by
      simpa [mul_assoc] using (hixf r hr l).const_mul (q l)]
    exact Finset.sum_congr rfl fun l _ => by rw [← integral_const_mul]; simp only [mul_assoc]
  set g : ℝ → ℝ := fun w => 2 * w - p' ⬝ᵥ x p w - p ⬝ᵥ x p' w with hg
  have hgm : Measurable g :=
    ((measurable_const.mul measurable_id).sub (hm p' p hp)).sub (hm p p' hp')
  have hgi : IntegrableOn g (Set.Ioc 0 wb) :=
    (((integrable_const (2 : ℝ)).mul_bdd (c := wb) measurable_id.aestronglyMeasurable
      (by
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall fun w hw => ?_
        rw [Real.norm_eq_abs, id, abs_of_pos hw.1]
        exact hw.2)).sub (hi p' p hp)).sub (hi p p' hp')
  have hrp : ∀ w ∈ Set.Ioc 0 wb, ∀ w' ∈ Set.Ioc 0 wb,
      p' ⬝ᵥ x p w ≤ w' → w ≤ p ⬝ᵥ x p' w' := by
    intro w hw w' hw' hle
    by_cases heq : x p w = x p' w'
    · rw [← heq, hW p w ⟨hp, hw.1⟩]
    · exact (hWA p' w' p w ⟨hp', hw'.1⟩ ⟨hp, hw.1⟩ hle heq).le
  have hnn : ∀ q r, StrictlyPositive q → StrictlyPositive r → ∀ w ∈ Set.Ioc 0 wb,
      0 ≤ q ⬝ᵥ x r w := fun q r hq hr w hw =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hq l).le (hX r w ⟨hr, hw.1⟩ l)
  -- the uniform case on every initial segment
  have hG : ∀ a, a ≤ wb → ∫ w in Set.Ioc 0 a, g w ≤ 0 := by
    intro a ha
    rcases le_or_gt a 0 with ha0 | ha0
    · rw [Set.Ioc_eq_empty (not_lt.mpr ha0), Measure.restrict_empty, integral_zero_measure]
    have hsub : Set.Ioc 0 a ⊆ Set.Ioc 0 wb := Set.Ioc_subset_Ioc le_rfl ha
    have hy := young_square ha0.le (hm p' p hp) (hm p p' hp')
      (fun w hw => hnn p' p hp' hp w (hsub hw)) (fun w hw => hnn p p' hp hp' w (hsub hw))
      ((hi p' p hp).mono_set hsub) ((hi p p' hp').mono_set hsub)
      (fun w hw w' hw' => hrp w (hsub hw) w' (hsub hw'))
    have h2 : ∫ w in Set.Ioc 0 a, 2 * w = a ^ 2 := by
      rw [← intervalIntegral.integral_of_le ha0.le, intervalIntegral.integral_const_mul,
        integral_id]
      ring
    have hi2 : IntegrableOn (fun w : ℝ => 2 * w) (Set.Ioc 0 a) :=
      (continuous_const.mul continuous_id).integrableOn_Ioc
    simp only [g]
    rw [integral_sub (f := fun w => 2 * w - p' ⬝ᵥ x p w) (g := fun w => p ⬝ᵥ x p' w)
      (hi2.sub ((hi p' p hp).mono_set hsub)) ((hi p p' hp').mono_set hsub),
      integral_sub (f := fun w => 2 * w) (g := fun w => p' ⬝ᵥ x p w) hi2
        ((hi p' p hp).mono_set hsub), h2]
    linarith
  have hkey := antitone_weighted_integral_nonpos hgi hgm hfm hf0 hfM hanti hG
  -- expand the left side
  have hwal : ∀ r, StrictlyPositive r →
      ∫ w in Set.Ioc 0 wb, (r ⬝ᵥ x r w) * f w = ∫ w in Set.Ioc 0 wb, w * f w :=
    fun r hr => setIntegral_congr_fun measurableSet_Ioc fun w hw => by
      simp only [hW r w ⟨hr, hw.1⟩]
  have hexp : (p' - p) ⬝ᵥ (densityDemand x f 0 wb p' - densityDemand x f 0 wb p) =
      ∫ w in Set.Ioc 0 wb, g w * f w := by
    have e : ∀ w, g w * f w = 2 * (w * f w) - (p' ⬝ᵥ x p w) * f w - (p ⬝ᵥ x p' w) * f w := by
      intro w; simp only [g]; ring
    simp_rw [e]
    have hwf : IntegrableOn (fun w => w * f w) (Set.Ioc 0 wb) := by
      have := (hixf p hp)
      have h1 : IntegrableOn (fun w => (p ⬝ᵥ x p w) * f w) (Set.Ioc 0 wb) := by
        simp only [dotProduct, Finset.sum_mul]
        exact integrable_finsetSum _ fun l _ => by
          simpa [mul_assoc] using (hixf p hp l).const_mul (p l)
      exact h1.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun w hw => by simp only [hW p w ⟨hp, hw.1⟩]))
    have hdotI : ∀ q r, StrictlyPositive r →
        IntegrableOn (fun w => (q ⬝ᵥ x r w) * f w) (Set.Ioc 0 wb) := by
      intro q r hr
      simp only [dotProduct, Finset.sum_mul]
      exact integrable_finsetSum _ fun l _ => by
        simpa [mul_assoc] using (hixf r hr l).const_mul (q l)
    rw [integral_sub (f := fun w => 2 * (w * f w) - p' ⬝ᵥ x p w * f w)
      (g := fun w => p ⬝ᵥ x p' w * f w) ((hwf.const_mul 2).sub (hdotI p' p hp)) (hdotI p p' hp'),
      integral_sub (f := fun w => 2 * (w * f w)) (g := fun w => p' ⬝ᵥ x p w * f w)
        (hwf.const_mul 2) (hdotI p' p hp), integral_const_mul,
      hdot p' p hp, hdot p p' hp']
    have hI1 : ∫ w in Set.Ioc 0 wb, w * f w = p' ⬝ᵥ densityDemand x f 0 wb p' := by
      rw [← hwal p' hp', hdot p' p' hp']
    have hI2 : ∫ w in Set.Ioc 0 wb, w * f w = p ⬝ᵥ densityDemand x f 0 wb p := by
      rw [← hwal p hp, hdot p p hp]
    simp only [sub_dotProduct, dotProduct_sub]
    linear_combination (-1 : ℝ) * hI1 - hI2
  rw [hexp]
  exact hkey

end MWG.AggregateDemand
