/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.StrassenLimit
import MWGChoiceUnderUncertainty.DominanceExamples
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Second-order dominance implies a mean-preserving spread

MWG, Section 6.D, pp. 198-199: Proposition 6.D.2, (i) ⇒ (ii), stated in the book without
proof (the Rothschild-Stiglitz / Strassen theorem), the converse claim of Example 6.D.2, and
the remaining inclusion of Exercise 6.D.4(c). With these, Proposition 6.D.2 is proved in full:
for MWG distributions with the same mean, (i) second-order dominance, (ii) mean-preserving
spread and (iii) the integral condition (6.D.2) are equivalent.

Proof of (i) ⇒ (ii). `StrassenLimit` gives a probability measure `π` on `ℝ²` with marginals `F`
and `G`, concentrated on a compact square, with `∫ φ(x)(y - x) dπ = 0` for every bounded
continuous `φ`. Writing `π` in the coordinates `(x, z) = (x, y - x)` and disintegrating with
respect to `x` (Mathlib's conditional kernel on the standard Borel space `ℝ`) gives a Markov
kernel `H_x`; the identity with smooth compactly supported `φ` shows that `x ↦ ∫ z dH_x(z)`
vanishes `F`-almost everywhere (Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
Replacing `H_x` by `δ₀` on the null set where this fails gives MWG's compound lottery: `G` is the
law of `x + z` with `x ~ F` and `z ~ H_x`, `E[z | x] = 0` for every `x`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction ContDiff

/-- **Proposition 6.D.2**, (i) ⇒ (ii) (MWG, p. 199), and the converse claim of **Example
6.D.2** (p. 198). If `F` second-order stochastically dominates `G` and the means agree, then `G`
is a mean-preserving spread of `F`: there is a Markov kernel `H_x` with `∫ z dH_x(z) = 0` for
every `x` such that `G` is the law of `x + z` when `x ~ F` and `z ~ H_x`. -/
theorem proposition_6_D_2_i_ii {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) (h : SOSD μ ν) : IsMeanPreservingSpread μ ν := by
  have := hμ.1
  have := hν.1
  obtain ⟨M₁, hM₁, hae₁⟩ := hμ.ae_mem
  obtain ⟨M₂, -, hae₂⟩ := hν.ae_mem
  set M := max M₁ M₂
  have hM : 0 < M := lt_of_lt_of_le hM₁ (le_max_left _ _)
  have hμM : ∀ᵐ t ∂μ, t ∈ Ioc 0 M :=
    hae₁.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  have hνM : ∀ᵐ t ∂ν, t ∈ Ioc 0 M :=
    hae₂.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_right _ _)⟩
  have hdom : ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ univ U → ∫ t, U t ∂ν ≤ ∫ t, U t ∂μ :=
    fun U hm hc => h U (hm.monotoneOn _) (hc.subset (subset_univ _) (convex_Ici 0))
  obtain ⟨π, hπ, hπK, hπ1, hπ2, hπm⟩ := exists_martingale_coupling hM hμM hνM hdom hmean
  -- the coupling in the coordinates `(x, y - x)`
  set f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 - p.1) with hf
  have mf : Measurable f := by fun_prop
  set ρ : Measure (ℝ × ℝ) := π.map f
  have hρ : IsProbabilityMeasure ρ := inferInstance
  have hρfst : ρ.fst = μ := by
    rw [Measure.fst, Measure.map_map measurable_fst mf]
    exact hπ1
  have hρsum : ρ.map (fun p => p.1 + p.2) = ν := by
    rw [Measure.map_map (by fun_prop) mf, ← hπ2]
    congr 1
    funext p
    simp [f]
  have hρK : ∀ᵐ p ∂ρ, p.2 ∈ Icc (-(3 * M)) (3 * M) := by
    rw [ae_map_iff mf.aemeasurable (measurableSet_Icc.preimage measurable_snd)]
    filter_upwards [hπK] with p hp
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
    exact ⟨by simp only [f]; linarith, by simp only [f]; linarith⟩
  have hρm (φ : ℝ →ᵇ ℝ) : ∫ p, φ p.1 * p.2 ∂ρ = 0 := by
    rw [integral_map mf.aemeasurable (by fun_prop)]
    exact hπm φ
  set κ₀ := ρ.condKernel
  have hdis : ρ.fst ⊗ₘ κ₀ = ρ := ρ.disintegrate κ₀
  rw [hρfst] at hdis
  -- the conditional laws are concentrated on a bounded interval
  have hbd : ∀ᵐ x ∂μ, κ₀ x (Icc (-(3 * M)) (3 * M))ᶜ = 0 := by
    have := Measure.ae_ae_of_ae_compProd (μ := μ) (κ := κ₀)
      (p := fun p : ℝ × ℝ => p.2 ∈ Icc (-(3 * M)) (3 * M)) (by rw [hdis]; exact hρK)
    filter_upwards [this] with x hx
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hx] with z hz
    exact fun hn => hn hz
  have hint_of (x : ℝ) (hx : κ₀ x (Icc (-(3 * M)) (3 * M))ᶜ = 0) :
      Integrable (fun z : ℝ => z) (κ₀ x) := by
    refine Integrable.of_bound measurable_id.aestronglyMeasurable (3 * M) ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hx] with z hz
    rw [Real.norm_eq_abs, abs_le]
    exact not_not.mp hz
  -- the conditional mean
  set m : ℝ → ℝ := fun x => ∫ z, z ∂(κ₀ x) with hm
  have mm : Measurable m := (stronglyMeasurable_id.integral_kernel (κ := κ₀)).measurable
  have hmb : ∀ᵐ x ∂μ, |m x| ≤ 3 * M := by
    filter_upwards [hbd] with x hx
    have hb : ∀ᵐ z ∂(κ₀ x), ‖z‖ ≤ 3 * M := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hx] with z hz
      rw [Real.norm_eq_abs, abs_le]
      exact not_not.mp hz
    have := norm_integral_le_of_norm_le_const hb
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact this
  have hmi : Integrable m μ :=
    Integrable.of_bound mm.aestronglyMeasurable (3 * M) (hmb.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact hx)
  have hm0 : ∀ᵐ x ∂μ, m x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hmi.locallyIntegrable fun g hg hgs => ?_
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgs
    set φ : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hg.continuous C hC
    have hφ : ∀ x, φ x = g x := fun _ => rfl
    have hgi : Integrable (fun p : ℝ × ℝ => g p.1 * p.2) (μ ⊗ₘ κ₀) := by
      rw [hdis]
      refine Integrable.of_bound (by fun_prop) (C * (3 * M)) ?_
      filter_upwards [hρK] with p hp
      rw [norm_mul]
      exact mul_le_mul (hC _) (by rw [Real.norm_eq_abs, abs_le]; exact hp) (norm_nonneg _)
        ((norm_nonneg _).trans (hC 0))
    have := hρm φ
    simp only [hφ] at this
    rw [← hdis, Measure.integral_compProd hgi] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hbd] with x hx
    rw [smul_eq_mul, hm, ← integral_const_mul]
  -- the spread kernel
  set G := {x : ℝ | κ₀ x (Icc (-(3 * M)) (3 * M))ᶜ = 0} ∩ {x | m x = 0}
  have hG : MeasurableSet G :=
    ((Kernel.measurable_coe κ₀ measurableSet_Icc.compl) (measurableSet_singleton 0)).inter
      (mm (measurableSet_singleton 0))
  set κ := Kernel.piecewise hG κ₀ (Kernel.const ℝ (Measure.dirac 0))
  refine ⟨κ, inferInstance, fun x => ?_, ?_⟩
  · rw [Kernel.piecewise_apply]
    split_ifs with hx
    · exact ⟨hint_of x hx.1, hx.2⟩
    · simp only [Kernel.const_apply]
      exact ⟨integrable_dirac (by simp), by simp⟩
  · have hae : κ =ᵐ[μ] κ₀ := by
      filter_upwards [hbd, hm0] with x h1 h2
      rw [Kernel.piecewise_apply]
      exact ite_eq_left_iff.mpr fun hn => absurd (show x ∈ G from ⟨h1, h2⟩) hn
    rw [Measure.compProd_congr hae, hdis, hρsum]

/-- **Proposition 6.D.2** (MWG, p. 199), in full. For MWG distributions `F` and `G` with the
same mean, (i) `F` second-order stochastically dominates `G`, (ii) `G` is a mean-preserving
spread of `F`, and (iii) the integral condition (6.D.2) holds, are equivalent. -/
theorem proposition_6_D_2 {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) :
    (SOSD μ ν ↔ IsMeanPreservingSpread μ ν) ∧ (SOSD μ ν ↔ IntegralCondition μ ν) :=
  ⟨⟨proposition_6_D_2_i_ii hμ hν hmean, fun h => (sosd_of_meanPreservingSpread hμ hν h).1⟩,
    proposition_6_D_2_i_iii hμ hν⟩

/-- **Example 6.D.2** (MWG, p. 198), "saying that `G` is a mean-preserving spread of `F` is
equivalent to saying that `F` second-order stochastically dominates `G`" (distributions with the
same mean, as throughout Definition 6.D.2). -/
theorem example_6_D_2_equivalence {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) : IsMeanPreservingSpread μ ν ↔ SOSD μ ν :=
  (proposition_6_D_2 hμ hν hmean).1.symm

/-- **Exercise 6.D.4(c)** (MWG, p. 213), the other inclusion: every lottery `q` over `1`, `2`, `3`
dollars in the region of (b) (same mean as `p`, `q₁ ≥ p₁`) is a mean-preserving spread of `p`.
With `exercise_6_D_4c`, the mean-preserving spreads of `p` are exactly that region. -/
theorem exercise_6_D_4c_converse {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (hmean : q₃ - q₁ = p₃ - p₁) (h1 : p₁ ≤ q₁) :
    IsMeanPreservingSpread (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) := by
  have hF := lot3M_isMWGDist hp1 hp2 hp3 hp
  have hG := lot3M_isMWGDist hq1 hq2 hq3 hq
  have hm := (exercise_6_D_4a hp hq hp1 hp2 hp3 hq1 hq2 hq3).mpr hmean
  exact proposition_6_D_2_i_ii hF hG hm.symm
    ((exercise_6_D_4b hp hq hp1 hp2 hp3 hq1 hq2 hq3 hmean).mpr h1)

/-- **Exercise 6.D.4(c)** (MWG, p. 213), both inclusions: the mean-preserving spreads of `p` in
the simplex over `1`, `2`, `3` dollars are exactly the region of (b). -/
theorem exercise_6_D_4c_iff {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    IsMeanPreservingSpread (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) ↔
      q₃ - q₁ = p₃ - p₁ ∧ p₁ ≤ q₁ :=
  ⟨exercise_6_D_4c hp hq hp1 hp2 hp3 hq1 hq2 hq3, fun h =>
    exercise_6_D_4c_converse hp hq hp1 hp2 hp3 hq1 hq2 hq3 h.1 h.2⟩

/-- A concrete instance of Proposition 6.D.2, (i) ⇒ (ii), with a distribution that is not of
the explicit form of Example 6.D.2: `q = (1/2, 0, 1/2)` is a mean-preserving spread of the sure
`2` dollars `p = (0, 1, 0)`. -/
theorem exercise_6_D_4c_instance :
    IsMeanPreservingSpread (lot3M 0 1 0 1 2 3) (lot3M (1 / 2) 0 (1 / 2) 1 2 3) :=
  exercise_6_D_4c_converse (by norm_num) (by norm_num) le_rfl zero_le_one le_rfl
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)

end MWG.ChoiceUnderUncertainty
