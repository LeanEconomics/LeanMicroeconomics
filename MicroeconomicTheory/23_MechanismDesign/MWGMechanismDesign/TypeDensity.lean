/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Type distributions with a density

MWG, Section 23.D, pp. 887-891, and Section 23.E, pp. 894-896: agent `i`'s type `θᵢ` lies in
`[θ̲ᵢ, θ̄ᵢ]` and is distributed with distribution function `Φᵢ` and density `φᵢ(θᵢ) > 0` on
`[θ̲ᵢ, θ̄ᵢ]`.

* `TypeDensity`: a density `φ` that is measurable, strictly positive on `[θ̲, θ̄]` (`θ̲ < θ̄`),
  zero outside, with total mass one; its distribution `TypeDensity.measure` is
  `volume.withDensity φ`.
* The distribution is a probability measure concentrated on `[θ̲, θ̄]`
  (`TypeDensity.isProbabilityMeasure`, `TypeDensity.measure_compl_Icc`), has no atoms
  (`TypeDensity.measure_singleton`) and gives positive probability to every open subinterval
  (`TypeDensity.measure_Ioo_pos`); `∫ f dμ = ∫_{θ̲}^{θ̄} f φ` (`TypeDensity.integral_eq`);
  with `Φ(x) = ∫_{θ̲}^{x} φ` (`TypeDensity.cdf`), `μ([s, ∞)) = 1 - Φ(s)`
  (`TypeDensity.measureReal_Ici`).
* The Fubini identity behind MWG's integration by parts on p. 890:
  `E[∫_{θ̲}^{θ} w] = ∫_{θ̲}^{θ̄} w(s) μ([s, ∞)) ds = ∫_{θ̲}^{θ̄} w(s)(1 - Φ(s)) ds`
  (`td_integral_integral_eq`, `TypeDensity.integral_integral_eq`); MWG's integration by parts
  assumes more regularity, the Fubini form needs only `w` integrable on `[θ̲, θ̄]`.
* The uniform distribution on `[a, b]` (`uniformDensity`), in particular on `[0, 1]`.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- **Section 23.D** (MWG, p. 887). A type distribution on `[θ̲, θ̄]` with a strictly positive
density `φ`: `φ` is measurable, `φ > 0` on `[θ̲, θ̄]`, `φ = 0` outside, and `∫_{θ̲}^{θ̄} φ = 1`. -/
structure TypeDensity where
  /-- The lowest type `θ̲`. -/
  lo : ℝ
  /-- The highest type `θ̄`. -/
  hi : ℝ
  lo_lt_hi : lo < hi
  /-- The density `φ`. -/
  dens : ℝ → ℝ
  measurable_dens : Measurable dens
  dens_pos : ∀ x ∈ Set.Icc lo hi, 0 < dens x
  dens_eq_zero : ∀ x, x ∉ Set.Icc lo hi → dens x = 0
  integral_dens : ∫ x in lo..hi, dens x = 1

namespace TypeDensity

variable (D : TypeDensity)

/-- The distribution of types, `μ = φ · volume`. -/
noncomputable def measure : Measure ℝ :=
  volume.withDensity fun x => ((D.dens x).toNNReal : ENNReal)

/-- The distribution function `Φ(x) = ∫_{θ̲}^{x} φ`. -/
noncomputable def cdf (x : ℝ) : ℝ := ∫ s in D.lo..x, D.dens s

/-- The density is nonnegative. -/
theorem dens_nonneg (x : ℝ) : 0 ≤ D.dens x := by
  by_cases hx : x ∈ Set.Icc D.lo D.hi
  · exact (D.dens_pos x hx).le
  · rw [D.dens_eq_zero x hx]

/-- The density is integrable on `[θ̲, θ̄]` (its integral is `1 ≠ 0`). -/
theorem intervalIntegrable_dens : IntervalIntegrable D.dens volume D.lo D.hi := by
  by_contra h
  have := D.integral_dens
  rw [intervalIntegral.integral_undef h] at this
  exact zero_ne_one this

/-- A function vanishing outside `[θ̲, θ̄]` has `∫ g = ∫_{θ̲}^{θ̄} g`. -/
theorem integral_volume_eq {g : ℝ → ℝ} (hg : ∀ x, x ∉ Set.Icc D.lo D.hi → g x = 0) :
    ∫ x, g x = ∫ x in D.lo..D.hi, g x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le D.lo_lt_hi.le]

/-- The density is integrable on `ℝ`. -/
theorem integrable_dens : Integrable D.dens := by
  have h : D.dens = (Set.Icc D.lo D.hi).indicator D.dens := by
    funext x
    by_cases hx : x ∈ Set.Icc D.lo D.hi
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, D.dens_eq_zero x hx]
  rw [h, integrable_indicator_iff measurableSet_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le).1 D.intervalIntegrable_dens

/-- **Section 23.D** (MWG, p. 890). `∫ f dμ = ∫_{θ̲}^{θ̄} f(x) φ(x) dx`. -/
theorem integral_eq (f : ℝ → ℝ) : ∫ x, f x ∂D.measure = ∫ x in D.lo..D.hi, f x * D.dens x := by
  rw [measure, integral_withDensity_eq_integral_smul D.measurable_dens.real_toNNReal]
  have e : ∀ x, (D.dens x).toNNReal • f x = f x * D.dens x := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (D.dens_nonneg x), smul_eq_mul, mul_comm]
  simp only [e]
  exact D.integral_volume_eq fun x hx => by rw [D.dens_eq_zero x hx, mul_zero]

/-- The type distribution is a probability measure. -/
theorem isProbabilityMeasure : IsProbabilityMeasure D.measure := by
  refine ⟨?_⟩
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ x, ENNReal.ofReal (D.dens x) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal D.integrable_dens
    (Filter.Eventually.of_forall D.dens_nonneg), D.integral_volume_eq D.dens_eq_zero,
    D.integral_dens, ENNReal.ofReal_one]

/-- The type distribution is concentrated on `[θ̲, θ̄]`. -/
theorem measure_compl_Icc : D.measure (Set.Icc D.lo D.hi)ᶜ = 0 := by
  rw [measure, withDensity_apply _ measurableSet_Icc.compl]
  rw [setLIntegral_congr_fun measurableSet_Icc.compl (g := fun _ => 0)
    fun x hx => by simp [D.dens_eq_zero x hx]]
  simp

/-- **Section 23.D** (MWG, p. 887). The type distribution has no atoms. -/
theorem measure_singleton (x : ℝ) : D.measure {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- Probabilities of sets as integrals of the density. -/
theorem measure_eq_ofReal {s : Set ℝ} (hs : MeasurableSet s) :
    D.measure s = ENNReal.ofReal (∫ x in s, D.dens x) := by
  rw [measure, withDensity_apply _ hs]
  rw [ofReal_integral_eq_lintegral_ofReal D.integrable_dens.integrableOn
    (Filter.Eventually.of_forall D.dens_nonneg)]
  rfl

/-- **Section 23.D** (MWG, p. 887). With `φ > 0` on `[θ̲, θ̄]`, every open subinterval has
positive probability. -/
theorem measure_Ioo_pos {a b : ℝ} (ha : D.lo ≤ a) (hab : a < b) (hb : b ≤ D.hi) :
    0 < D.measure (Set.Ioo a b) := by
  rw [D.measure_eq_ofReal measurableSet_Ioo, ENNReal.ofReal_pos, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (D.integrable_dens.intervalIntegrable) (fun x hx => D.dens_pos x
      ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩) hab

/-- `x ↦ 1_A(x) φ(x)` is integrable. -/
theorem integrable_indicator_mul {A : Set ℝ} (hA : MeasurableSet A) :
    Integrable fun x => A.indicator 1 x * D.dens x := by
  refine (D.integrable_dens.indicator hA).congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ A <;> simp [hx]

/-- `μ((-∞, s]) = Φ(s)` for `s ∈ [θ̲, θ̄]`. -/
theorem measureReal_Iic {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) :
    D.measure.real (Set.Iic s) = D.cdf s := by
  rw [← integral_indicator_one measurableSet_Iic, D.integral_eq,
    ← intervalIntegral.integral_add_adjacent_intervals (b := s)]
  · have h1 : ∫ x in D.lo..s, (Set.Iic s).indicator 1 x * D.dens x = D.cdf s := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hs.1] at hx
      simp [Set.indicator_of_mem (Set.mem_Iic.2 hx.2)]
    have h2 : ∫ x in s..D.hi, (Set.Iic s).indicator 1 x * D.dens x = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [Set.uIoc_of_le hs.2] at hx
      simp [Set.indicator_of_notMem (show x ∉ Set.Iic s from fun h => absurd hx.1 (not_lt.2 h))]
    rw [h1, h2, add_zero]
  · exact (D.integrable_indicator_mul measurableSet_Iic).intervalIntegrable
  · exact (D.integrable_indicator_mul measurableSet_Iic).intervalIntegrable

/-- **Section 23.D** (MWG, p. 890). `μ([s, ∞)) = 1 - Φ(s)` for `s ∈ [θ̲, θ̄]`. -/
theorem measureReal_Ici {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) :
    D.measure.real (Set.Ici s) = 1 - D.cdf s := by
  have := D.isProbabilityMeasure
  rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr (Iio_ae_eq_Iic' (D.measure_singleton s)), D.measureReal_Iic hs]

end TypeDensity

/-- **Section 23.D** (MWG, p. 890), the step "integration by parts implies", in Fubini form and
for any type distribution `ν` concentrated on `[θ̲, θ̄]`: for `w` integrable on `[θ̲, θ̄]`,
`E_ν[∫_{θ̲}^{θ} w(s) ds] = ∫_{θ̲}^{θ̄} w(s) ν([s, ∞)) ds`. -/
theorem td_integral_integral_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] {lo hi : ℝ}
    (hle : lo ≤ hi) (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume lo hi) :
    ∫ θ, (∫ s in lo..θ, w s) ∂ν = ∫ s in lo..hi, w s * ν.real (Set.Ici s) := by
  have hwρ : Integrable w (volume.restrict (Set.Ioc lo hi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hw
  set F : ℝ → ℝ → ℝ := fun θ s => (Set.Ici s).indicator (fun _ => w s) θ with hF
  have hFm : Integrable (Function.uncurry F) (ν.prod (volume.restrict (Set.Ioc lo hi))) := by
    have hg : Integrable (fun p : ℝ × ℝ => w p.2) (ν.prod (volume.restrict (Set.Ioc lo hi))) :=
      hwρ.comp_snd ν
    have heq : Function.uncurry F = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => w p.2) := by
      funext p
      by_cases h : p.2 ≤ p.1 <;> simp [hF, Set.indicator, h, Function.uncurry]
    rw [heq]
    exact hg.indicator (measurableSet_le measurable_snd measurable_fst)
  have hL : ∀ᵐ θ ∂ν, ∫ s in lo..θ, w s = ∫ s in Set.Ioc lo hi, F θ s := by
    filter_upwards [mem_ae_iff.2 hsupp] with θ hθ
    rw [intervalIntegral.integral_of_le hθ.1]
    have e : ∀ s, F θ s = (Set.Iic θ).indicator w s := by
      intro s
      by_cases h : s ≤ θ <;> simp [hF, Set.indicator, h]
    simp only [e]
    rw [setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic, inf_eq_right.2 hθ.2]
  have hR : ∫ s in Set.Ioc lo hi, ∫ θ, F θ s ∂ν = ∫ s in lo..hi, w s * ν.real (Set.Ici s) := by
    rw [intervalIntegral.integral_of_le hle]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hF]
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]
  rw [integral_congr_ae hL, integral_integral_swap hFm, hR]

namespace TypeDensity

variable (D : TypeDensity)

/-- **Section 23.D** (MWG, p. 890), "integration by parts implies": for `w` integrable on
`[θ̲, θ̄]`, `∫_{θ̲}^{θ̄} (∫_{θ̲}^{θ} w(s) ds) φ(θ) dθ = ∫_{θ̲}^{θ̄} w(θ)(1 - Φ(θ)) dθ`. -/
theorem integral_integral_eq {w : ℝ → ℝ} (hw : IntervalIntegrable w volume D.lo D.hi) :
    ∫ x in D.lo..D.hi, (∫ s in D.lo..x, w s) * D.dens x =
      ∫ s in D.lo..D.hi, w s * (1 - D.cdf s) := by
  have := D.isProbabilityMeasure
  rw [← D.integral_eq, td_integral_integral_eq D.measure D.lo_lt_hi.le D.measure_compl_Icc hw]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le D.lo_lt_hi.le] at hs
  simp only [D.measureReal_Ici hs]

end TypeDensity

/-- The uniform distribution on `[a, b]`, density `1/(b - a)` on `[a, b]`. -/
noncomputable def uniformDensity (a b : ℝ) (h : a < b) : TypeDensity where
  lo := a
  hi := b
  lo_lt_hi := h
  dens := (Set.Icc a b).indicator fun _ => (b - a)⁻¹
  measurable_dens := measurable_const.indicator measurableSet_Icc
  dens_pos := fun x hx => by rw [Set.indicator_of_mem hx]; exact inv_pos.2 (sub_pos.2 h)
  dens_eq_zero := fun x hx => Set.indicator_of_notMem hx _
  integral_dens := by
    rw [intervalIntegral.integral_congr (g := fun _ => (b - a)⁻¹) fun x hx => by
      rw [Set.uIcc_of_le h.le] at hx; exact Set.indicator_of_mem hx _]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_inv_cancel₀ (sub_pos.2 h).ne']

/-- The uniform distribution on `[0, 1]`. -/
noncomputable def uniform01 : TypeDensity := uniformDensity 0 1 zero_lt_one

/-- Expectations under the uniform distribution on `[0, 1]`: `E[f] = ∫_0^1 f`. -/
theorem uniform01_integral (f : ℝ → ℝ) : ∫ x, f x ∂uniform01.measure = ∫ x in (0 : ℝ)..1, f x := by
  rw [uniform01.integral_eq]
  refine intervalIntegral.integral_congr fun x hx => ?_
  change x ∈ Set.uIcc (0 : ℝ) 1 at hx
  rw [Set.uIcc_of_le zero_le_one] at hx
  change f x * (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) x = f x
  rw [Set.indicator_of_mem hx]
  norm_num

/-- The uniform distribution on `[0, 1]` has `Φ(x) = x` on `[0, 1]`. -/
theorem uniform01_cdf {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : uniform01.cdf x = x := by
  change ∫ s in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) s = x
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun s hs => by
    rw [Set.uIcc_of_le hx.1] at hs
    rw [Set.indicator_of_mem (show s ∈ Set.Icc (0 : ℝ) 1 from ⟨hs.1, hs.2.trans hx.2⟩)]
    norm_num]
  simp

end MWG.MechanismDesign
