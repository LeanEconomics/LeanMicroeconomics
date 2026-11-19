/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.FirstOrderDominance
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# First-order dominance as an upward probabilistic shift

MWG, Example 6.D.1, p. 197: "whenever `F` first-order stochastically dominates `G`, it is
possible to generate `F` from `G`" by an upward probabilistic shift. The two distributions are
coupled through their quantile functions applied to one uniform draw (Kreps's
`generalQuantile_uniform_law`); the shift kernel `H_x` is the conditional law of the increment
given the first stage (Mathlib's disintegration `condKernel`), modified on a `G`-null set so
that `H_x` is concentrated on `[0, ∞)` for every `x`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- **Example 6.D.1** (MWG, p. 197), the reverse direction. If `F` first-order stochastically
dominates `G` (MWG distributions), there is a Markov kernel `H_x` with `H_x(z < 0) = 0` for
every `x` such that `F` is the law of `x + z` when `x ~ G` and `z ~ H_x`. -/
theorem example_6_D_1_converse {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : FOSD μ ν) : ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧ (∀ x, κ x (Iio 0) = 0) ∧
      μ = (ν ⊗ₘ κ).map fun p => p.1 + p.2 := by
  have := hμ.1
  have := hν.1
  have hle := (proposition_6_D_1 hμ hν).mp h
  set lam : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hlam : IsProbabilityMeasure lam := ⟨by simp [lam, Real.volume_Ioo]⟩
  set Qμ := Kreps.UtilityForMoney.GeneralQuantile μ
  set Qν := Kreps.UtilityForMoney.GeneralQuantile ν
  have mQμ : Measurable Qμ := Kreps.UtilityForMoney.generalQuantile_measurable μ
  have mQν : Measurable Qν := Kreps.UtilityForMoney.generalQuantile_measurable ν
  set f : ℝ → ℝ × ℝ := fun t => (Qν t, Qμ t - Qν t)
  have mf : Measurable f := mQν.prodMk (mQμ.sub mQν)
  set ρ : Measure (ℝ × ℝ) := lam.map f
  have hρ : IsProbabilityMeasure ρ := inferInstance
  have hfst : ρ.fst = ν := by
    rw [Measure.fst, Measure.map_map measurable_fst mf]
    exact Kreps.UtilityForMoney.generalQuantile_uniform_law ν
  have hsum : ρ.map (fun p => p.1 + p.2) = μ := by
    rw [Measure.map_map (by fun_prop) mf]
    convert Kreps.UtilityForMoney.generalQuantile_uniform_law μ using 2
    funext t; simp [f, Qμ]
  -- the increment is nonnegative almost surely
  have hpos : ∀ᵐ p ∂ρ, 0 ≤ p.2 := by
    rw [ae_map_iff mf.aemeasurable (measurableSet_le measurable_const measurable_snd)]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [f, sub_nonneg]
    rw [Kreps.UtilityForMoney.generalQuantile_le_iff ν ht]
    exact ((Kreps.UtilityForMoney.generalQuantile_le_iff μ ht _).mp le_rfl).trans (hle _)
  set κ₀ := ρ.condKernel
  have hdis : ρ.fst ⊗ₘ κ₀ = ρ := ρ.disintegrate κ₀
  have hκ₀ : ∀ᵐ x ∂ρ.fst, κ₀ x (Iio 0) = 0 := by
    have := Measure.ae_ae_of_ae_compProd (μ := ρ.fst) (κ := κ₀)
      (p := fun p : ℝ × ℝ => 0 ≤ p.2) (by rw [hdis]; exact hpos)
    filter_upwards [this] with x hx
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hx] with z hz
    simpa using hz
  have hs : MeasurableSet {x : ℝ | κ₀ x (Iio 0) = 0} :=
    (Kernel.measurable_coe κ₀ measurableSet_Iio) (measurableSet_singleton 0)
  set κ := Kernel.piecewise hs κ₀ (Kernel.const ℝ (Measure.dirac 0))
  refine ⟨κ, inferInstance, fun x => ?_, ?_⟩
  · rw [Kernel.piecewise_apply]
    split_ifs with hx
    · exact hx
    · simp [Kernel.const_apply]
  · have hae : κ =ᵐ[ν] κ₀ := by
      rw [← hfst]
      filter_upwards [hκ₀] with x hx
      rw [Kernel.piecewise_apply]
      exact ite_eq_left_iff.mpr fun hn => absurd (show x ∈ {x | κ₀ x (Iio 0) = 0} from hx) hn
    rw [Measure.compProd_congr hae, ← hfst, hdis, hsum]

end MWG.ChoiceUnderUncertainty
