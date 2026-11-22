/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.MoneyLotteries
import UtilityForMoney.GeneralQuantile
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# First-order stochastic dominance

MWG, Section 6.D, pp. 194-197: the standing restriction to distributions with `F(0) = 0` and
`F(x̄) = 1`, Definition 6.D.1, Proposition 6.D.1 in full generality for distribution
functions (both directions), Example 6.D.1 (an upward probabilistic shift produces a
first-order dominating distribution; Figure 6.D.2), and Exercise 6.D.2.

The "if" direction of Proposition 6.D.1 is proved without MWG's integration by parts (which
needs differentiable `u`): writing both laws as images of a uniform draw under their
generalized inverses (Kreps's `generalQuantile_uniform_law`), `F ≤ G` makes the quantile of
`F` pointwise larger, and a nondecreasing `u` preserves the order.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- **p. 195**. MWG's distributions in Section 6.D: probability measures with `F(0) = 0` and
`F(x̄) = 1` for some `x̄`. -/
def IsMWGDist (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ cdf μ 0 = 0 ∧ ∃ M, cdf μ M = 1

/-- Such a distribution is concentrated on some `(0, x̄]`. -/
theorem IsMWGDist.ae_mem {μ : Measure ℝ} (h : IsMWGDist μ) :
    ∃ M, 0 < M ∧ ∀ᵐ x ∂μ, x ∈ Ioc 0 M := by
  obtain ⟨hp, h0, M, hM⟩ := h
  have hle : μ (Iic 0) = 0 := by rw [← ofReal_cdf, h0, ENNReal.ofReal_zero]
  have hgt : μ (Ioi M) = 0 := by
    rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf, hM,
      ENNReal.ofReal_one]
  have hM0 : 0 < M := by
    by_contra hn
    have := monotone_cdf μ (not_lt.mp hn)
    rw [hM, h0] at this
    norm_num at this
  refine ⟨M, hM0, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hle, measure_eq_zero_iff_ae_notMem.mp hgt]
    with x h1 h2
  exact ⟨lt_of_not_ge h1, le_of_not_gt h2⟩

/-- An MWG distribution is a money lottery on `[0, ∞)`. -/
theorem IsMWGDist.isMoneyLottery {μ : Measure ℝ} (h : IsMWGDist μ) :
    IsMoneyLottery (Ici 0) μ := by
  obtain ⟨M, -, hae⟩ := h.ae_mem
  refine ⟨h.1, 0, M, Icc_subset_Ici_self, ?_⟩
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with x hx
  simpa using (⟨hx.1.le, hx.2⟩ : 0 ≤ x ∧ x ≤ M)

/-- A nondecreasing utility is integrable for an MWG distribution. -/
theorem IsMWGDist.integrable_monotone {μ : Measure ℝ} (h : IsMWGDist μ) {u : ℝ → ℝ}
    (hu : Monotone u) : Integrable u μ := by
  have := h.1
  obtain ⟨M, -, hae⟩ := h.ae_mem
  refine Integrable.of_bound hu.measurable.aestronglyMeasurable (|u 0| + |u M|) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_le]
  have h1 := hu hx.1.le
  have h2 := hu hx.2
  constructor
  · linarith [neg_abs_le (u 0), abs_nonneg (u M)]
  · linarith [le_abs_self (u M), abs_nonneg (u 0)]

/-- **Definition 6.D.1** (MWG, p. 195). `F` first-order stochastically dominates `G` if
`∫ u dF ≥ ∫ u dG` for every nondecreasing `u : ℝ → ℝ`. -/
def FOSD (μ ν : Measure ℝ) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ

/-- The step utility `1_{x > c}` is nondecreasing. -/
theorem monotone_step (c : ℝ) : Monotone fun x : ℝ => (Ioi c).indicator (1 : ℝ → ℝ) x := by
  intro x y hxy
  by_cases hx : c < x
  · have hy : c < y := hx.trans_le hxy
    simp [indicator, hx, hy]
  · by_cases hy : c < y <;> simp [indicator, hx, hy]

/-- The expected value of the step utility is `1 - F(c)`. -/
theorem integral_step {μ : Measure ℝ} [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ x, (Ioi c).indicator (1 : ℝ → ℝ) x ∂μ = 1 - cdf μ c := by
  rw [integral_indicator_one measurableSet_Ioi, cdf_eq_real, ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ]

/-- **Proposition 6.D.1** (MWG, p. 195). For MWG distributions, `F` first-order
stochastically dominates `G` iff `F(x) ≤ G(x)` for every `x`. -/
theorem proposition_6_D_1 {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν) :
    FOSD μ ν ↔ ∀ x, cdf μ x ≤ cdf ν x := by
  have := hμ.1
  have := hν.1
  constructor
  · intro h x
    have := h _ (monotone_step x)
    rw [integral_step, integral_step] at this
    linarith
  · intro hle u hu
    set lam : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
    have hlam : IsProbabilityMeasure lam := ⟨by simp [lam, Real.volume_Ioo]⟩
    have hQμ := Kreps.UtilityForMoney.generalQuantile_measurable μ
    have hQν := Kreps.UtilityForMoney.generalQuantile_measurable ν
    have eμ : ∫ x, u x ∂μ = ∫ t, u (Kreps.UtilityForMoney.GeneralQuantile μ t) ∂lam := by
      conv_lhs => rw [← Kreps.UtilityForMoney.generalQuantile_uniform_law μ]
      exact integral_map hQμ.aemeasurable hu.measurable.aestronglyMeasurable
    have eν : ∫ x, u x ∂ν = ∫ t, u (Kreps.UtilityForMoney.GeneralQuantile ν t) ∂lam := by
      conv_lhs => rw [← Kreps.UtilityForMoney.generalQuantile_uniform_law ν]
      exact integral_map hQν.aemeasurable hu.measurable.aestronglyMeasurable
    rw [eμ, eν]
    have hint (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : IsMWGDist ρ) :
        Integrable (fun t => u (Kreps.UtilityForMoney.GeneralQuantile ρ t)) lam := by
      have h1 := hρ.integrable_monotone hu
      rw [← Kreps.UtilityForMoney.generalQuantile_uniform_law ρ] at h1
      exact (integrable_map_measure hu.measurable.aestronglyMeasurable
        (Kreps.UtilityForMoney.generalQuantile_measurable ρ).aemeasurable).mp h1
    apply integral_mono_ae (hint ν hν) (hint μ hμ)
    have hae : ∀ᵐ t ∂lam, t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [hae] with t ht
    apply hu
    rw [Kreps.UtilityForMoney.generalQuantile_le_iff ν ht]
    exact ((Kreps.UtilityForMoney.generalQuantile_le_iff μ ht _).mp le_rfl).trans (hle _)

/-- **Exercise 6.D.2** (MWG, p. 213), first part. First-order dominance implies a weakly
higher mean. -/
theorem exercise_6_D_2_mean {μ ν : Measure ℝ} (h : FOSD μ ν) :
    ∫ x, x ∂ν ≤ ∫ x, x ∂μ :=
  h id monotone_id

/-- **Exercise 6.D.2** (MWG, p. 213), second part. `F = (1/2)δ₁ + (1/2)δ₅` has a higher mean
(`3`) than `G = δ₂` (`2`) but does not first-order dominate it. -/
theorem exercise_6_D_2_example :
    ∫ x, x ∂(Measure.dirac (2 : ℝ)) < ∫ x, x ∂(binLot (1 / 2) 1 5) ∧
      ¬FOSD (binLot (1 / 2) 1 5) (Measure.dirac 2) := by
  constructor
  · rw [integral_dirac, integral_binLot _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · intro h
    have := h _ (monotone_step 1)
    rw [integral_dirac, integral_binLot _ _ _ _ (by norm_num) (by norm_num)] at this
    simp [indicator] at this
    norm_num at this

/-- **Example 6.D.1** (MWG, p. 196). An upward probabilistic shift: if the second stage adds
`z ≥ 0` drawn from `H_x` (bounded), the reduced distribution `F` first-order stochastically
dominates `G`. -/
theorem example_6_D_1 {μ : Measure ℝ} (hμ : IsMWGDist μ) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    {B : ℝ} (hκ : ∀ x, ∀ᵐ z ∂(κ x), z ∈ Icc 0 B) :
    FOSD ((μ ⊗ₘ κ).map fun p => p.1 + p.2) μ := by
  have := hμ.1
  obtain ⟨M, -, hae⟩ := hμ.ae_mem
  intro u hu
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 + p.2 := by fun_prop
  rw [integral_map hmeas.aemeasurable hu.measurable.aestronglyMeasurable]
  have hjoint : ∀ᵐ p ∂(μ ⊗ₘ κ), p.1 ∈ Ioc 0 M ∧ p.2 ∈ Icc 0 B := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (measurable_fst measurableSet_Ioc).inter (measurable_snd measurableSet_Icc)
    · filter_upwards [hae] with x hx
      filter_upwards [hκ x] with z hz using ⟨hx, hz⟩
  have hint : Integrable (fun p : ℝ × ℝ => u (p.1 + p.2)) (μ ⊗ₘ κ) := by
    refine Integrable.of_bound (hu.measurable.comp hmeas).aestronglyMeasurable
      (|u 0| + |u (M + B)|) ?_
    filter_upwards [hjoint] with p hp
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hu (show 0 ≤ p.1 + p.2 by linarith [hp.1.1, hp.2.1])
    have h2 := hu (show p.1 + p.2 ≤ M + B by linarith [hp.1.2, hp.2.2])
    constructor
    · linarith [neg_abs_le (u 0), abs_nonneg (u (M + B))]
    · linarith [le_abs_self (u (M + B)), abs_nonneg (u 0)]
  rw [Measure.integral_compProd hint]
  apply integral_mono_ae (hμ.integrable_monotone hu) hint.integral_compProd
  filter_upwards [hint.ae_of_compProd] with x hx
  calc u x = ∫ _, u x ∂(κ x) := by simp
    _ ≤ ∫ z, u (x + z) ∂(κ x) := integral_mono_ae (integrable_const _) hx
        ((hκ x).mono fun z hz => hu (by linarith [hz.1]))

/-- Integrals against a weighted Dirac mass. -/
theorem integral_smul_dirac {a : ℝ} (ha : 0 ≤ a) (x : ℝ) (f : ℝ → ℝ) :
    ∫ z, f z ∂(ENNReal.ofReal a • Measure.dirac x) = a * f x := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ha, smul_eq_mul]

/-- A weighted Dirac mass integrates every function. -/
theorem integrable_smul_dirac (a x : ℝ) (f : ℝ → ℝ) :
    Integrable f (ENNReal.ofReal a • Measure.dirac x) :=
  (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The three-atom lottery `a δ_x + b δ_y + c δ_z`. -/
noncomputable def lot3M (a b c x y z : ℝ) : Measure ℝ :=
  ENNReal.ofReal a • Measure.dirac x + ENNReal.ofReal b • Measure.dirac y +
    ENNReal.ofReal c • Measure.dirac z

/-- Integrals against a three-atom lottery. -/
theorem integral_lot3M {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x y z : ℝ)
    (f : ℝ → ℝ) : ∫ t, f t ∂(lot3M a b c x y z) = a * f x + b * f y + c * f z := by
  unfold lot3M
  rw [integral_add_measure ((integrable_smul_dirac a x f).add_measure
    (integrable_smul_dirac b y f)) (integrable_smul_dirac c z f),
    integral_add_measure (integrable_smul_dirac a x f) (integrable_smul_dirac b y f),
    integral_smul_dirac ha, integral_smul_dirac hb, integral_smul_dirac hc]

/-- **Figure 6.D.2** (MWG, p. 196). `G` is the even randomization between `1` and `4`; the
outcome `1` is shifted to an even chance of `2` or `3` and `4` to `5`. The resulting
`F = (1/4)δ₂ + (1/4)δ₃ + (1/2)δ₅` first-order dominates `G`. -/
theorem figure_6_D_2 : FOSD (lot3M (1 / 4) (1 / 4) (1 / 2) 2 3 5) (binLot (1 / 2) 1 4) := by
  intro u hu
  rw [integral_binLot _ _ _ _ (by norm_num) (by norm_num),
    integral_lot3M (by norm_num) (by norm_num) (by norm_num)]
  have h1 := hu (show (1 : ℝ) ≤ 2 by norm_num)
  have h2 := hu (show (1 : ℝ) ≤ 3 by norm_num)
  have h3 := hu (show (4 : ℝ) ≤ 5 by norm_num)
  linarith

end MWG.ChoiceUnderUncertainty
