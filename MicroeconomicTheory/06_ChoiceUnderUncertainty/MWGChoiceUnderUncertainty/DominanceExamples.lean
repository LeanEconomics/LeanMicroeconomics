/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.SOSDApprox

/-!
# Examples and exercises on stochastic dominance

MWG, Section 6.D, pp. 197-198 and Exercises 6.D.1, 6.D.3 and 6.D.4, p. 213: the
mean-preserving spread of Example 6.D.2 (Figure 6.D.3), the elementary increase in risk of
Example 6.D.3 (Exercise 6.D.3), and the regions of the three-outcome simplex (outcomes `1`, `2`,
`3` dollars) for first-order dominance, equal means, second-order dominance and condition
(6.D.2).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- A three-atom lottery integrates every function. -/
theorem integrable_lot3M (a b c x y z : ℝ) (f : ℝ → ℝ) : Integrable f (lot3M a b c x y z) :=
  ((integrable_smul_dirac a x f).add_measure (integrable_smul_dirac b y f)).add_measure
    (integrable_smul_dirac c z f)

/-- The measure of a set under a three-atom lottery. -/
theorem lot3M_apply (a b c x y z : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    lot3M a b c x y z s = ENNReal.ofReal a * s.indicator 1 x + ENNReal.ofReal b *
      s.indicator 1 y + ENNReal.ofReal c * s.indicator 1 z := by
  simp only [lot3M, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs]

/-- The three-outcome lottery `(p₁, p₂, p₃)` over `1`, `2`, `3` dollars is an MWG
distribution. -/
theorem lot3M_isMWGDist {p₁ p₂ p₃ : ℝ} (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h3 : 0 ≤ p₃)
    (hs : p₁ + p₂ + p₃ = 1) : IsMWGDist (lot3M p₁ p₂ p₃ 1 2 3) := by
  have hP : IsProbabilityMeasure (lot3M p₁ p₂ p₃ 1 2 3) := by
    constructor
    rw [lot3M_apply _ _ _ _ _ _ MeasurableSet.univ]
    simp only [indicator_univ, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3, hs,
      ENNReal.ofReal_one]
  refine ⟨hP, ?_, 3, ?_⟩
  · rw [cdf_eq_real, measureReal_def, lot3M_apply _ _ _ _ _ _ measurableSet_Iic]
    simp only [indicator, mem_Iic, Pi.one_apply]
    norm_num
  · rw [cdf_eq_real, measureReal_def, lot3M_apply _ _ _ _ _ _ measurableSet_Iic]
    simp only [indicator, mem_Iic, Pi.one_apply]
    norm_num
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3, hs]
    simp

/-- **Exercise 6.D.1(a)** (MWG, p. 213). In the simplex over `1`, `2`, `3` dollars, `L' = q`
first-order stochastically dominates `L = p` iff `q₁ ≤ p₁` and `q₃ ≥ p₃`. -/
theorem exercise_6_D_1a {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    FOSD (lot3M q₁ q₂ q₃ 1 2 3) (lot3M p₁ p₂ p₃ 1 2 3) ↔ q₁ ≤ p₁ ∧ p₃ ≤ q₃ := by
  constructor
  · intro h
    have s1 := h _ (monotone_step 1)
    have s2 := h _ (monotone_step 2)
    simp only [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3, indicator, mem_Ioi,
      Pi.one_apply] at s1 s2
    norm_num at s1 s2
    constructor <;> linarith
  · rintro ⟨h1, h3⟩ u hu
    rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3]
    have a1 := hu (show (1 : ℝ) ≤ 2 by norm_num)
    have a2 := hu (show (2 : ℝ) ≤ 3 by norm_num)
    have e : q₁ * u 1 + q₂ * u 2 + q₃ * u 3 - (p₁ * u 1 + p₂ * u 2 + p₃ * u 3) =
        (q₃ - p₃) * (u 3 - u 2) + (p₁ - q₁) * (u 2 - u 1) := by
      have : q₂ = 1 - q₁ - q₃ := by linarith
      have : p₂ = 1 - p₁ - p₃ := by linarith
      subst_vars; ring
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr a2),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr a1)]

/-- **Exercise 6.D.1(b)** (MWG, p. 213). The region where `F ≤ G` everywhere is the same:
`q₁ ≤ p₁` and `q₃ ≥ p₃`. -/
theorem exercise_6_D_1b {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    (∀ x, cdf (lot3M q₁ q₂ q₃ 1 2 3) x ≤ cdf (lot3M p₁ p₂ p₃ 1 2 3) x) ↔
      q₁ ≤ p₁ ∧ p₃ ≤ q₃ := by
  rw [← proposition_6_D_1 (lot3M_isMWGDist hq1 hq2 hq3 hq) (lot3M_isMWGDist hp1 hp2 hp3 hp)]
  exact exercise_6_D_1a hp hq hp1 hp2 hp3 hq1 hq2 hq3

/-- **Exercise 6.D.4(a)** (MWG, p. 213). Two lotteries over `1`, `2`, `3` dollars have the same
mean iff `q₃ - q₁ = p₃ - p₁`: they lie on a line of slope one in the simplex. -/
theorem exercise_6_D_4a {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    ∫ x, x ∂(lot3M q₁ q₂ q₃ 1 2 3) = ∫ x, x ∂(lot3M p₁ p₂ p₃ 1 2 3) ↔ q₃ - q₁ = p₃ - p₁ := by
  rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3]
  constructor <;> intro h <;> linarith

/-- **Exercise 6.D.4(b)** (MWG, p. 213). With equal means, `L = p` second-order stochastically
dominates `L' = q` iff `q₁ ≥ p₁`. -/
theorem exercise_6_D_4b {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (hmean : q₃ - q₁ = p₃ - p₁) :
    SOSD (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) ↔ p₁ ≤ q₁ := by
  constructor
  · intro h
    obtain ⟨hm, hc⟩ := min_utility_props 2
    have := h _ hm hc
    rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3] at this
    norm_num at this
    linarith
  · intro h u _ hc
    rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3]
    have hmid := hc.2 (show (1 : ℝ) ∈ Ici 0 by norm_num) (show (3 : ℝ) ∈ Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    norm_num at hmid
    have e : p₁ * u 1 + p₂ * u 2 + p₃ * u 3 - (q₁ * u 1 + q₂ * u 2 + q₃ * u 3) =
        (q₁ - p₁) * (2 * u 2 - u 1 - u 3) := by
      have : q₂ = 1 - q₁ - q₃ := by linarith
      have : p₂ = 1 - p₁ - p₃ := by linarith
      have : q₃ = p₃ - p₁ + q₁ := by linarith
      subst_vars; ring
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show (0 : ℝ) ≤ 2 * u 2 - u 1 - u 3 by linarith)]

/-- **Exercise 6.D.4(d)** (MWG, p. 213). With equal means, condition (6.D.2) between `p` and `q`
holds iff `q₁ ≥ p₁`: the same region as in (b). -/
theorem exercise_6_D_4d {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (hmean : q₃ - q₁ = p₃ - p₁) :
    IntegralCondition (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) ↔ p₁ ≤ q₁ := by
  rw [← proposition_6_D_2_i_iii (lot3M_isMWGDist hp1 hp2 hp3 hp)
    (lot3M_isMWGDist hq1 hq2 hq3 hq)]
  exact exercise_6_D_4b hp hq hp1 hp2 hp3 hq1 hq2 hq3 hmean

/-- **Example 6.D.2** (MWG, p. 197, Figure 6.D.3). `F` gives `2` or `3` dollars with even
probability; spreading `2` to an even chance of `1` or `3` and `3` to `2` or `4` gives the
uniform `G` on `{1, 2, 3, 4}` (represented as `(1/4, 1/4, 1/4)` on `1, 2, 3` plus `1/4` on
`4`). The means agree (`5/2`) and `F` second-order stochastically dominates `G`. -/
theorem example_6_D_2 :
    let G := lot3M (1 / 4) (1 / 4) (1 / 4) 1 2 3 + ENNReal.ofReal (1 / 4) • Measure.dirac 4
    ∫ x, x ∂(binLot (1 / 2) 2 3) = ∫ x, x ∂G ∧ SOSD (binLot (1 / 2) 2 3) G := by
  intro G
  have hG (f : ℝ → ℝ) : ∫ x, f x ∂G = (f 1 + f 2 + f 3 + f 4) / 4 := by
    simp only [G]
    rw [integral_add_measure (integrable_lot3M _ _ _ _ _ _ f) (integrable_smul_dirac _ _ f),
      integral_lot3M (by norm_num) (by norm_num) (by norm_num),
      integral_smul_dirac (by norm_num)]
    ring
  refine ⟨?_, fun u _ hc => ?_⟩
  · rw [hG, integral_binLot _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rw [hG, integral_binLot _ _ _ _ (by norm_num) (by norm_num)]
    have m1 := hc.2 (show (1 : ℝ) ∈ Ici 0 by norm_num) (show (3 : ℝ) ∈ Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    have m2 := hc.2 (show (2 : ℝ) ∈ Ici 0 by norm_num) (show (4 : ℝ) ∈ Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    norm_num at m1 m2
    linarith

/-- **Example 6.D.3** (MWG, p. 198). The elementary increase in risk: the mass that `F` assigns
to `[x', x'']` is moved to the endpoints, with weights `p' = ∫_{[x',x'']} (x'' - t)/(x'' - x')`
and `p'' = ∫_{[x',x'']} (t - x')/(x'' - x')` so that the mean is preserved. -/
noncomputable def elementaryIncrease (μ : Measure ℝ) (a b : ℝ) : Measure ℝ :=
  μ.restrict (Icc a b)ᶜ +
    ENNReal.ofReal (∫ t in Icc a b, (b - t) / (b - a) ∂μ) • Measure.dirac a +
    ENNReal.ofReal (∫ t in Icc a b, (t - a) / (b - a) ∂μ) • Measure.dirac b

/-- Integrals against an elementary increase in risk. -/
theorem integral_elementaryIncrease {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : Integrable f μ) :
    ∫ t, f t ∂(elementaryIncrease μ a b) = ∫ t in (Icc a b)ᶜ, f t ∂μ +
      (∫ t in Icc a b, (b - t) / (b - a) ∂μ) * f a +
      (∫ t in Icc a b, (t - a) / (b - a) ∂μ) * f b := by
  have hw1 : 0 ≤ ∫ t in Icc a b, (b - t) / (b - a) ∂μ :=
    setIntegral_nonneg measurableSet_Icc fun t ht => div_nonneg (by linarith [ht.2])
      (by linarith)
  have hw2 : 0 ≤ ∫ t in Icc a b, (t - a) / (b - a) ∂μ :=
    setIntegral_nonneg measurableSet_Icc fun t ht => div_nonneg (by linarith [ht.1])
      (by linarith)
  unfold elementaryIncrease
  rw [integral_add_measure (hf.restrict.add_measure (integrable_smul_dirac _ _ f))
    (integrable_smul_dirac _ _ f), integral_add_measure hf.restrict
    (integrable_smul_dirac _ _ f), integral_smul_dirac hw1, integral_smul_dirac hw2]

/-- **Exercise 6.D.3** (MWG, p. 213) and **Example 6.D.3** (p. 198). An elementary increase in
risk preserves the mean, and `F` second-order stochastically dominates it (for
`0 ≤ x' < x''`). -/
theorem exercise_6_D_3 {μ : Measure ℝ} (hμ : IsMWGDist μ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    ∫ t, t ∂(elementaryIncrease μ a b) = ∫ t, t ∂μ ∧ SOSD μ (elementaryIncrease μ a b) := by
  have := hμ.1
  have hba : 0 < b - a := by linarith
  have hlin : Integrable (fun t : ℝ => t) μ := hμ.isMoneyLottery.integrable_id
  have hchord_int (c d : ℝ) : Integrable (fun t : ℝ => c * ((b - t) / (b - a)) +
      d * ((t - a) / (b - a))) μ := by
    have h1 : Integrable (fun t : ℝ => (b - t) / (b - a)) μ :=
      ((integrable_const b).sub hlin).div_const _
    have h2 : Integrable (fun t : ℝ => (t - a) / (b - a)) μ :=
      (hlin.sub (integrable_const a)).div_const _
    exact (h1.const_mul c).add (h2.const_mul d)
  have hchord (c d : ℝ) : ∫ t in Icc a b, (c * ((b - t) / (b - a)) + d * ((t - a) / (b - a))) ∂μ
      = (∫ t in Icc a b, (b - t) / (b - a) ∂μ) * c +
        (∫ t in Icc a b, (t - a) / (b - a) ∂μ) * d := by
    rw [integral_add, integral_const_mul, integral_const_mul]
    · ring
    · exact (((integrable_const b).sub hlin).div_const _).restrict.const_mul c
    · exact ((hlin.sub (integrable_const a)).div_const _).restrict.const_mul d
  constructor
  · rw [integral_elementaryIncrease hab hlin,
      ← integral_add_compl (s := Icc a b) measurableSet_Icc hlin]
    have := hchord a b
    have e : ∫ t in Icc a b, (a * ((b - t) / (b - a)) + b * ((t - a) / (b - a))) ∂μ =
        ∫ t in Icc a b, t ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _; field_simp; ring
    linarith
  · intro u hm hc
    have hu := hμ.integrable_concave hm hc
    rw [integral_elementaryIncrease hab hu,
      ← integral_add_compl (s := Icc a b) measurableSet_Icc hu]
    have hch := hchord (u a) (u b)
    have : ∫ t in Icc a b, (u a * ((b - t) / (b - a)) + u b * ((t - a) / (b - a))) ∂μ ≤
        ∫ t in Icc a b, u t ∂μ := by
      apply setIntegral_mono_on (hchord_int _ _).restrict hu.restrict measurableSet_Icc
      intro t ht
      have hc' := hc.2 (show a ∈ Ici (0 : ℝ) from ha) (show b ∈ Ici (0 : ℝ) by
        exact mem_Ici.mpr (by linarith)) (show 0 ≤ (b - t) / (b - a) from
          div_nonneg (by linarith [ht.2]) hba.le)
        (show 0 ≤ (t - a) / (b - a) from div_nonneg (by linarith [ht.1]) hba.le)
        (by field_simp; ring)
      simp only [smul_eq_mul] at hc'
      have e : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by field_simp; ring
      rw [e] at hc'
      linarith
    linarith

/-- The second stage of a compound lottery started at a sure `x`: `(δ_x ⊗ H).map(+)` is `H_x`
shifted by `x`. -/
theorem dirac_compProd_map_add (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (x : ℝ) :
    ((Measure.dirac x) ⊗ₘ κ).map (fun p => p.1 + p.2) = (κ x).map (fun z => x + z) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply (by fun_prop) hs,
    Measure.dirac_compProd_apply ((by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2) hs)]
  rfl

/-- Real masses of the binary lottery. -/
theorem binLot_real {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (binLot p x y).real s = p * s.indicator 1 x + (1 - p) * s.indicator 1 y := by
  rw [measureReal_def]
  simp only [binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  rw [ENNReal.toReal_add (by simp [indicator]; split_ifs <;> simp)
    (by simp [indicator]; split_ifs <;> simp), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp only [indicator]
  split_ifs <;> simp

/-- **Example 6.D.2** (MWG, p. 197, Figure 6.D.3). `G` (uniform on `{1, 2, 3, 4}`) is a
mean-preserving spread of `F` (even chance of `2` or `3`): spreading each outcome by `±1` with
even probability (a mean-zero `H_x`). -/
theorem example_6_D_2_spread :
    IsMeanPreservingSpread (binLot (1 / 2) 2 3)
      (lot3M (1 / 4) (1 / 4) (1 / 4) 1 2 3 + ENNReal.ofReal (1 / 4) • Measure.dirac 4) := by
  have hP : IsProbabilityMeasure (binLot (1 / 2) (-1 : ℝ) 1) :=
    binLot_isProbabilityMeasure _ _ _ (by norm_num) (by norm_num)
  refine ⟨Kernel.const ℝ (binLot (1 / 2) (-1) 1), inferInstance, fun x => ⟨?_, ?_⟩, ?_⟩
  · simp only [Kernel.const_apply]
    exact (binLot_isMoneyLottery (S := univ) convex_univ (mem_univ _) (mem_univ _) (1 / 2)
      (by norm_num) (by norm_num)).integrable_id
  · simp only [Kernel.const_apply]
    rw [mean_binLot _ _ _ (by norm_num) (by norm_num)]; norm_num
  · have hF : binLot (1 / 2) (2 : ℝ) 3 = ENNReal.ofReal (1 / 2) • Measure.dirac 2 +
        ENNReal.ofReal (1 - 1 / 2) • Measure.dirac 3 := rfl
    rw [hF, Measure.compProd_add_left, Measure.compProd_smul_left, Measure.compProd_smul_left,
      Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
      dirac_compProd_map_add, dirac_compProd_map_add]
    all_goals try fun_prop
    simp only [Kernel.const_apply]
    ext s hs
    have h2 : MeasurableSet ((fun z : ℝ => 2 + z) ⁻¹' s) := (by fun_prop : Measurable _) hs
    have h3 : MeasurableSet ((fun z : ℝ => 3 + z) ⁻¹' s) := (by fun_prop : Measurable _) hs
    simp only [lot3M, binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Measure.map_apply (by fun_prop : Measurable fun z : ℝ => 2 + z) hs,
      Measure.map_apply (by fun_prop : Measurable fun z : ℝ => 3 + z) hs,
      Measure.dirac_apply' _ hs, Measure.dirac_apply' _ h2, Measure.dirac_apply' _ h3]
    have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have e2 : ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 4) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
    simp only [e1, indicator, mem_preimage, Pi.one_apply]
    norm_num
    have p1 : ((-1 : ℝ) ∈ (fun z : ℝ => 2 + z) ⁻¹' s) = ((1 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    have p2 : ((1 : ℝ) ∈ (fun z : ℝ => 2 + z) ⁻¹' s) = ((3 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    have p3 : ((-1 : ℝ) ∈ (fun z : ℝ => 3 + z) ⁻¹' s) = ((2 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    have p4 : ((1 : ℝ) ∈ (fun z : ℝ => 3 + z) ⁻¹' s) = ((4 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    simp only [p1, p2, p3, p4, mul_add]
    rw [← e2]
    split_ifs <;> first | (exfalso; simp_all; done) | ring

/-- **Exercise 6.D.4(c)** (MWG, p. 213). Every mean-preserving spread `q` of `p` (lotteries over
`1`, `2`, `3` dollars) lies in the region of (b): same mean and `q₁ ≥ p₁`. -/
theorem exercise_6_D_4c {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃)
    (h : IsMeanPreservingSpread (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3)) :
    q₃ - q₁ = p₃ - p₁ ∧ p₁ ≤ q₁ := by
  obtain ⟨hs, hm⟩ := sosd_of_meanPreservingSpread (lot3M_isMWGDist hp1 hp2 hp3 hp)
    (lot3M_isMWGDist hq1 hq2 hq3 hq) h
  have hmean := (exercise_6_D_4a hp hq hp1 hp2 hp3 hq1 hq2 hq3).mp hm.symm
  exact ⟨hmean, (exercise_6_D_4b hp hq hp1 hp2 hp3 hq1 hq2 hq3 hmean).mp hs⟩

end MWG.ChoiceUnderUncertainty
