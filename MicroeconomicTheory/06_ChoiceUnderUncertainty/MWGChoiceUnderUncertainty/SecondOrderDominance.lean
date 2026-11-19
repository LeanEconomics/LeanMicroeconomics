/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.FirstOrderDominance
import MWGChoiceUnderUncertainty.AssetComparative
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Second-order stochastic dominance

MWG, Section 6.D, pp. 197-199: Definition 6.D.2, mean-preserving spreads (Example 6.D.2),
the integral condition (6.D.2), equality of the areas (6.D.1), and the implications of
Proposition 6.D.2 among (i) second-order dominance, (ii) mean-preserving spread and (iii)
condition (6.D.2).

A mean-preserving spread is MWG's compound lottery: a Markov kernel `H_x` with mean zero for
every `x`, and `G` the law of `x + z` when `x ~ F` and `z ~ H_x`. The utility functions of
Definition 6.D.2 are nondecreasing and concave on `ℝ₊`; such a function may jump at `0`, which
carries no mass under MWG's distributions (`F(0) = 0`). The key identity is
`∫ min(t, x) dF(t) = x - ∫₀ˣ F(s) ds` (layer-cake formula).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- **Definition 6.D.2** (MWG, p. 197). `F` second-order stochastically dominates `G` if
`∫ u dF ≥ ∫ u dG` for every nondecreasing concave `u : ℝ₊ → ℝ` (MWG compares distributions
with the same mean, which the theorems below assume). -/
def SOSD (μ ν : Measure ℝ) : Prop :=
  ∀ u : ℝ → ℝ, MonotoneOn u (Ici 0) → ConcaveOn ℝ (Ici 0) u → ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ

/-- A nondecreasing concave utility on `ℝ₊` is integrable for an MWG distribution. -/
theorem IsMWGDist.integrable_concave {μ : Measure ℝ} (h : IsMWGDist μ) {u : ℝ → ℝ}
    (hm : MonotoneOn u (Ici 0)) (hc : ConcaveOn ℝ (Ici 0) u) : Integrable u μ := by
  have := h.1
  obtain ⟨M, hM, hae⟩ := h.ae_mem
  have hcont : ContinuousOn u (Ioi 0) := by
    have := hc.continuousOn_interior
    rwa [interior_Ici] at this
  have hr : μ.restrict (Ioi 0) = μ := Measure.restrict_eq_self_of_ae_mem
    (hae.mono fun x hx => hx.1)
  have hmeas : AEStronglyMeasurable u μ := by
    have := hcont.aestronglyMeasurable (μ := μ) measurableSet_Ioi
    rwa [hr] at this
  refine Integrable.of_bound hmeas (|u 0| + |u M|) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_le]
  have h1 := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.1.le) hx.1.le
  have h2 := hm (mem_Ici.mpr hx.1.le) (mem_Ici.mpr hM.le) hx.2
  constructor
  · linarith [neg_abs_le (u 0), abs_nonneg (u M)]
  · linarith [le_abs_self (u M), abs_nonneg (u 0)]

/-- `t ↦ min(t, x)` is nondecreasing and concave on `ℝ₊`. -/
theorem min_utility_props (x : ℝ) :
    MonotoneOn (fun t : ℝ => min t x) (Ici 0) ∧ ConcaveOn ℝ (Ici 0) (fun t : ℝ => min t x) := by
  refine ⟨fun a _ b _ hab => min_le_min_right x hab, convex_Ici 0, ?_⟩
  intro a _ b _ s t hs ht hst
  simp only [smul_eq_mul]
  apply le_min
  · nlinarith [min_le_left a x, min_le_left b x]
  · have h1 := mul_le_mul_of_nonneg_left (min_le_right a x) hs
    have h2 := mul_le_mul_of_nonneg_left (min_le_right b x) ht
    have h3 : s * x + t * x = x := by rw [← add_mul, hst, one_mul]
    linarith

/-- **p. 198**. `∫ min(t, x) dF(t) = x - ∫₀ˣ F(s) ds` for an MWG distribution and `x ≥ 0`. -/
theorem integral_min_eq {μ : Measure ℝ} (h : IsMWGDist μ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t, min t x ∂μ = x - ∫ s in (0)..x, cdf μ s := by
  have := h.1
  obtain ⟨M, -, hae⟩ := h.ae_mem
  have hint : Integrable (fun t : ℝ => min t x) μ := by
    refine Integrable.of_bound (by fun_prop) x ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min ht.1.le hx)]
    exact min_le_right _ _
  rw [hint.integral_eq_integral_meas_lt (hae.mono fun t ht => le_min ht.1.le hx)]
  have key : ∀ s ∈ Ioi (0 : ℝ), μ.real {t | s < min t x} =
      (Iio x).indicator (fun s => 1 - cdf μ s) s := by
    intro s _
    by_cases hs : s < x
    · have : {t | s < min t x} = Ioi s := by
        ext t; simp only [mem_ofPred_eq, lt_min_iff, mem_Ioi, hs, and_true]
      rw [this, indicator_of_mem (mem_Iio.mpr hs), cdf_eq_real, ← compl_Iic,
        measureReal_compl measurableSet_Iic, probReal_univ]
    · have : {t | s < min t x} = ∅ := by
        ext t; simp only [mem_ofPred_eq, lt_min_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => hs
      rw [this, indicator_of_notMem (by simpa using hs)]; simp
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((monotone_cdf μ).intervalIntegrable)]
  simp

/-- **(6.D.2)** (MWG, p. 198). The integral condition: `∫₀ˣ G(t) dt ≥ ∫₀ˣ F(t) dt` for all
`x ≥ 0`. -/
def IntegralCondition (μ ν : Measure ℝ) : Prop :=
  ∀ x, 0 ≤ x → ∫ t in (0)..x, cdf μ t ≤ ∫ t in (0)..x, cdf ν t

/-- **(6.D.1)** (MWG, p. 198). With equal means, the areas below the two distribution
functions over `[0, x̄]` coincide: `∫₀^x̄ (F - G) = 0` (for `x̄` with `F(x̄) = G(x̄) = 1`). -/
theorem equal_areas {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν) {M : ℝ}
    (hM : 0 ≤ M) (hμM : cdf μ M = 1) (hνM : cdf ν M = 1)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) :
    ∫ t in (0)..M, (cdf μ t - cdf ν t) = 0 := by
  have := hμ.1
  have := hν.1
  have hmin (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : IsMWGDist ρ) (hρM : cdf ρ M = 1) :
      ∫ t, min t M ∂ρ = ∫ t, t ∂ρ := by
    apply integral_congr_ae
    have hgt : ρ (Ioi M) = 0 := by
      rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf, hρM,
        ENNReal.ofReal_one]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hgt] with t ht
    exact min_eq_left (le_of_not_gt ht)
  have e1 := integral_min_eq hμ hM
  have e2 := integral_min_eq hν hM
  rw [hmin μ hμ hμM] at e1
  rw [hmin ν hν hνM] at e2
  rw [intervalIntegral.integral_sub ((monotone_cdf μ).intervalIntegrable)
    ((monotone_cdf ν).intervalIntegrable)]
  linarith

/-- **Proposition 6.D.2**, (i) ⇒ (iii) (MWG, p. 199). Second-order dominance implies the
integral condition (6.D.2), using the utilities `min(t, x)`. -/
theorem sosd_integralCondition {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : SOSD μ ν) : IntegralCondition μ ν := by
  intro x hx
  obtain ⟨hm, hc⟩ := min_utility_props x
  have := h _ hm hc
  rw [integral_min_eq hμ hx, integral_min_eq hν hx] at this
  linarith

/-- **Example 6.D.2** (MWG, p. 197). A mean-preserving spread: a Markov kernel `H_x` with mean
zero for every `x`, and `G` the law of `x + z`. -/
def IsMeanPreservingSpread (μ ν : Measure ℝ) : Prop :=
  ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧ (∀ x, Integrable (fun z => z) (κ x) ∧
    ∫ z, z ∂(κ x) = 0) ∧ ν = (μ ⊗ₘ κ).map fun p => p.1 + p.2

/-- **Example 6.D.2** (MWG, pp. 197-198) and **Proposition 6.D.2**, (ii) ⇒ (i). If `G` is a
mean-preserving spread of `F` (both MWG distributions), `F` second-order stochastically
dominates `G` and the means agree. -/
theorem sosd_of_meanPreservingSpread {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : IsMeanPreservingSpread μ ν) : SOSD μ ν ∧ ∫ x, x ∂μ = ∫ x, x ∂ν := by
  obtain ⟨κ, hκ, hmean, rfl⟩ := h
  have := hμ.1
  obtain ⟨M, hM, hae⟩ := hμ.ae_mem
  obtain ⟨N, hN, haeν⟩ := hν.ae_mem
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 + p.2 := by fun_prop
  have hsum : ∀ᵐ p ∂(μ ⊗ₘ κ), p.1 + p.2 ∈ Ioc 0 N :=
    ae_of_ae_map hmeas.aemeasurable haeν
  have hfst : ∀ᵐ p ∂(μ ⊗ₘ κ), p.1 ∈ Ioc 0 M := by
    apply Measure.ae_compProd_of_ae_ae (measurable_fst measurableSet_Ioc)
    filter_upwards [hae] with x hx using Eventually.of_forall fun _ => hx
  have hboth := Measure.ae_ae_of_ae_compProd (hsum.and hfst)
  -- a general integrand bounded on the relevant region
  have key (u : ℝ → ℝ) (hu : Integrable u ((μ ⊗ₘ κ).map fun p => p.1 + p.2))
      (hstep : ∀ x ∈ Ioc 0 M, ∀ f : ℝ → ℝ, Integrable (fun z => u (x + z)) (κ x) →
        (∀ᵐ z ∂(κ x), x + z ∈ Ioc 0 N) → ∫ z, u (x + z) ∂(κ x) ≤ u x)
      (hu' : Integrable u μ) :
      ∫ x, u x ∂((μ ⊗ₘ κ).map fun p => p.1 + p.2) ≤ ∫ x, u x ∂μ := by
    rw [integral_map hmeas.aemeasurable hu.aestronglyMeasurable]
    have hint : Integrable (fun p : ℝ × ℝ => u (p.1 + p.2)) (μ ⊗ₘ κ) :=
      (integrable_map_measure hu.aestronglyMeasurable hmeas.aemeasurable).mp hu
    rw [Measure.integral_compProd hint]
    apply integral_mono_ae hint.integral_compProd hu'
    filter_upwards [hint.ae_of_compProd, hboth, hae] with x hx hb hxM
    exact hstep x hxM u hx (hb.mono fun z hz => hz.1)
  constructor
  · intro u hm hc
    have hiν := hν.integrable_concave hm hc
    refine key u hiν (fun x hx _ hxi hpos => ?_) (hμ.integrable_concave hm hc)
    obtain ⟨c, -, hstep⟩ := concave_supergradient hc hm
      (show x ∈ interior (Ici (0 : ℝ)) by rw [interior_Ici]; exact hx.1)
    have hbound : ∀ᵐ z ∂(κ x), u (x + z) ≤ u x + c * z := by
      filter_upwards [hpos] with z hz
      have hz' : x + z ∈ Ici (0 : ℝ) := mem_Ici.mpr hz.1.le
      have := hstep x (mem_Ici.mpr hx.1.le) (x + z) hz'
        (by rcases le_total 0 z with h0 | h0
            · exact Or.inl ⟨le_rfl, by linarith⟩
            · exact Or.inr ⟨by linarith, le_rfl⟩)
      linarith
    calc ∫ z, u (x + z) ∂(κ x) ≤ ∫ z, (u x + c * z) ∂(κ x) :=
          integral_mono_ae hxi ((integrable_const _).add ((hmean x).1.const_mul c)) hbound
      _ = u x := by
          rw [integral_add (integrable_const _) ((hmean x).1.const_mul c), integral_const_mul,
            (hmean x).2]
          simp
  · have hiν : Integrable (fun x : ℝ => x) ((μ ⊗ₘ κ).map fun p => p.1 + p.2) :=
      hν.isMoneyLottery.integrable_id
    rw [integral_map hmeas.aemeasurable hiν.aestronglyMeasurable]
    have hint : Integrable (fun p : ℝ × ℝ => p.1 + p.2) (μ ⊗ₘ κ) :=
      (integrable_map_measure hiν.aestronglyMeasurable hmeas.aemeasurable).mp hiν
    rw [Measure.integral_compProd hint]
    apply integral_congr_ae
    filter_upwards [hint.ae_of_compProd] with x hx
    rw [integral_add (integrable_const x) (hmean x).1, (hmean x).2]
    simp

end MWG.ChoiceUnderUncertainty
