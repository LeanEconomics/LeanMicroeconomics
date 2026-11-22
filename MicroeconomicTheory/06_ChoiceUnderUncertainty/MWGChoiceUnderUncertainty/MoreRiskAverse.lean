/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ArrowPratt
import UtilityForMoney.ArrowPrattTheorem
import UtilityForMoney.ComparativeRisk
import Mathlib.Analysis.Convex.Continuous

/-!
# Comparisons of risk aversion across individuals

MWG, Section 6.C, pp. 191-192: the five definitions (i)-(v) of "`u₂` is more risk averse than
`u₁`", Proposition 6.C.2 (their equivalence) with the differentiable proof of (i) ⇔ (ii), and
Exercises 6.C.6 and 6.C.7.

Conditions (iii) and (v) range over all money lotteries (compactly supported distributions,
see `MoneyLotteries`). The utilities are twice continuously differentiable with positive
marginal utility on an open interval `S`. The equivalence (i) ⇔ (ii) is Kreps's
Proposition 6.8 (Arrow-Pratt comparison iff the finite-lottery comparison) combined with
Kreps's Proposition 6.7 (the finite-lottery comparison iff concavity of `u₂ ∘ u₁⁻¹`); (ii) ⇒
(iii) is Jensen's inequality for `ψ` on arbitrary distributions; (iv) ⇒ (i) uses
`r_A = 4 lim π(ε)/ε`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A finite-support lottery over amounts in `S` (Kreps's `SimpleLottery S`) as a measure. -/
noncomputable def simpleMeasure {S : Set ℝ} (p : Kreps.UtilityForMoney.SimpleLottery S) :
    Measure ℝ :=
  ∑ x ∈ p.weights.support, ENNReal.ofReal (p.weights x) • Measure.dirac (x : ℝ)

/-- Expectations under `simpleMeasure p` are Kreps's expected utilities. -/
theorem integral_simpleMeasure {S : Set ℝ} (p : Kreps.UtilityForMoney.SimpleLottery S)
    (f : ℝ → ℝ) :
    ∫ z, f z ∂(simpleMeasure p) =
      Kreps.UtilityForMoney.ExpectedUtility (fun y : S => f y) p := by
  unfold simpleMeasure Kreps.UtilityForMoney.ExpectedUtility
  rw [integral_finsetSum_measure]
  · rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (p.weights_nonneg x),
      smul_eq_mul]
  · intro x _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A finite-support lottery over a convex `S` is a money lottery on `S`. -/
theorem simpleMeasure_isMoneyLottery {S : Set ℝ} (hS : Convex ℝ S)
    (p : Kreps.UtilityForMoney.SimpleLottery S) : IsMoneyLottery S (simpleMeasure p) := by
  classical
  have hne := p.support_weights_nonempty
  set T := p.weights.support.image (fun x : S => (x : ℝ))
  have hT : T.Nonempty := hne.image _
  refine ⟨⟨?_⟩, T.min' hT, T.max' hT, ?_, ?_⟩
  · simp only [simpleMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
      Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.weights_nonneg x)]
    have := p.total
    rw [Finsupp.sum] at this
    rw [this, ENNReal.ofReal_one]
  · obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp (T.min'_mem hT)
    obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp (T.max'_mem hT)
    rw [← ha', ← hb']
    exact hS.ordConnected.out a.property b.property
  · simp only [simpleMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl, indicator_of_notMem, mul_zero]
    simp only [mem_compl_iff, not_not]
    have hxT : (x : ℝ) ∈ T := Finset.mem_image_of_mem _ hx
    exact ⟨T.min'_le _ hxT, T.le_max' _ hxT⟩

/-- **Proposition 6.C.2(i)** (MWG, p. 191). `r_A(x, u₂) ≥ r_A(x, u₁)` for every `x`. -/
def MoreRiskAverseI (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ x ∈ S, arrowPratt u₁ x ≤ arrowPratt u₂ x

/-- **Proposition 6.C.2(ii)** (MWG, p. 191). `u₂ = ψ ∘ u₁` for an increasing concave `ψ`. -/
def MoreRiskAverseII (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (u₁ '' S) ∧ ConcaveOn ℝ (u₁ '' S) ψ ∧ ∀ x ∈ S, u₂ x = ψ (u₁ x)

/-- **Proposition 6.C.2(iii)** (MWG, p. 191). `c(F, u₂) ≤ c(F, u₁)` for every `F`. -/
def MoreRiskAverseIII (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ μ c₁ c₂, IsMoneyLottery S μ → IsCertaintyEquivalent S u₁ μ c₁ →
    IsCertaintyEquivalent S u₂ μ c₂ → c₂ ≤ c₁

/-- **Proposition 6.C.2(iv)** (MWG, p. 191). `π(x, ε, u₂) ≥ π(x, ε, u₁)` for all `x` and
`ε > 0`. -/
def MoreRiskAverseIV (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → probPremium u₁ x ε ≤ probPremium u₂ x ε

/-- **Proposition 6.C.2(v)** (MWG, p. 191). If `u₂` finds `F` at least as good as the riskless
`x̄`, so does `u₁`. -/
def MoreRiskAverseV (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ μ x, IsMoneyLottery S μ → x ∈ S → u₂ x ≤ ∫ z, u₂ z ∂μ → u₁ x ≤ ∫ z, u₁ z ∂μ

/-- Condition (v) restricted to finite-support lotteries is Kreps's `MoreRiskAverse`. -/
theorem kreps_of_moreRiskAverseV {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (h : MoreRiskAverseV S u₁ u₂) : Kreps.UtilityForMoney.MoreRiskAverse S u₂ u₁ := by
  intro p x hx
  have := h (simpleMeasure p) x (simpleMeasure_isMoneyLottery hS p) x.property
  simp only [integral_simpleMeasure] at this
  exact this hx

/-- Kreps's finite-lottery comparison gives the concave transformation (ii). -/
theorem moreRiskAverseII_of_kreps {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S) (c1 : ContinuousOn u₁ S)
    (c2 : ContinuousOn u₂ S) (h : Kreps.UtilityForMoney.MoreRiskAverse S u₂ u₁) :
    MoreRiskAverseII S u₁ u₂ :=
  ⟨Kreps.UtilityForMoney.UtilityTransform S u₂ u₁,
    Kreps.UtilityForMoney.utilityTransform_strictMonoOn h1 h2,
    (Kreps.UtilityForMoney.proposition_6_7 hS h2 h1 c2 c1).mp h,
    fun _ hx => (Kreps.UtilityForMoney.utilityTransform_apply u₂ h1 hx).symm⟩

/-- A concave transformation (ii) gives Kreps's finite-lottery comparison. -/
theorem kreps_of_moreRiskAverseII {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S) (c1 : ContinuousOn u₁ S)
    (c2 : ContinuousOn u₂ S) (h : MoreRiskAverseII S u₁ u₂) :
    Kreps.UtilityForMoney.MoreRiskAverse S u₂ u₁ := by
  obtain ⟨ψ, -, hψ, he⟩ := h
  apply (Kreps.UtilityForMoney.proposition_6_7 hS h2 h1 c2 c1).mpr
  refine ⟨hψ.1, fun a ha b hb s t hs ht hst => ?_⟩
  have heq : ∀ y ∈ u₁ '' S, Kreps.UtilityForMoney.UtilityTransform S u₂ u₁ y = ψ y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Kreps.UtilityForMoney.utilityTransform_apply u₂ h1 hx, he x hx]
  rw [heq a ha, heq b hb, heq _ (hψ.1 ha hb hs ht hst)]
  exact hψ.2 ha hb hs ht hst

/-- An open interval image: for `[a, b] ⊆ S` with `S` open, the values `u([a, b])` lie in the
interior of a closed interval contained in `u(S)`. -/
theorem exists_Icc_image_nhds {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u : ℝ → ℝ}
    (hc : ContinuousOn u S) (hi : StrictMonoOn u S) {a b : ℝ} (hab : Icc a b ⊆ S)
    (hle : a ≤ b) : ∃ a' b', a' < a ∧ b < b' ∧ Icc a' b' ⊆ S ∧
      Icc (u a') (u b') ⊆ u '' S ∧ u a' < u a ∧ u b < u b' := by
  have ha : a ∈ S := hab ⟨le_rfl, hle⟩
  have hb : b ∈ S := hab ⟨hle, le_rfl⟩
  obtain ⟨ε, hε, hεa⟩ := Metric.isOpen_iff.mp ho a ha
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.mp ho b hb
  have ha' : a - ε / 2 ∈ S := by
    apply hεa
    rw [Metric.mem_ball, Real.dist_eq, show a - ε / 2 - a = -(ε / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have hb' : b + δ / 2 ∈ S := by
    apply hδb
    rw [Metric.mem_ball, Real.dist_eq, show b + δ / 2 - b = δ / 2 by ring,
      abs_of_pos (by linarith)]
    linarith
  have hsub : Icc (a - ε / 2) (b + δ / 2) ⊆ S := hS.ordConnected.out ha' hb'
  refine ⟨a - ε / 2, b + δ / 2, by linarith, by linarith, hsub, ?_, hi ha' ha (by linarith),
    hi hb hb' (by linarith)⟩
  intro y hy
  obtain ⟨c, hc', hce⟩ := intermediate_value_Icc (by linarith) (hc.mono hsub) hy
  exact ⟨c, hsub hc', hce⟩

/-- **Proposition 6.C.2**, (ii) ⇒ (iii) (MWG, p. 191; Exercise 6.C.6(a), p. 210). By Jensen's
inequality for `ψ`, a concave transformation has smaller certainty equivalents. -/
theorem moreRiskAverse_ii_iii {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u₁ u₂ : ℝ → ℝ}
    (c1 : ContinuousOn u₁ S) (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S)
    (h2 : StrictMonoOn u₂ S) (h : MoreRiskAverseII S u₁ u₂) : MoreRiskAverseIII S u₁ u₂ := by
  obtain ⟨ψ, -, hψ, he⟩ := h
  intro μ k₁ k₂ hμ hk1 hk2
  have := hμ.1
  obtain ⟨a, b, hab, hae⟩ := hμ.ae_mem
  have hle : a ≤ b := by
    have : (ae μ).NeBot := ae_neBot.mpr (NeZero.ne μ)
    obtain ⟨z, hz⟩ := hae.exists
    exact hz.1.trans hz.2
  obtain ⟨a', b', -, -, hsub', himg, hlo, hhi⟩ := exists_Icc_image_nhds hS ho c1 h1 hab hle
  -- `ψ` is continuous on `[u₁ a, u₁ b]`, inside the interior of `[u₁ a', u₁ b']`
  have hψI : ConcaveOn ℝ (Icc (u₁ a') (u₁ b')) ψ := hψ.subset himg (convex_Icc _ _)
  have hψc : ContinuousOn ψ (Icc (u₁ a) (u₁ b)) := by
    have := hψI.continuousOn_interior
    rw [interior_Icc] at this
    exact this.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsubψ : Icc (u₁ a) (u₁ b) ⊆ Icc (u₁ a') (u₁ b') :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hval : ∀ᵐ z ∂μ, u₁ z ∈ Icc (u₁ a) (u₁ b) := hae.mono fun z hz =>
    ⟨h1.monotoneOn (hab ⟨le_rfl, hle⟩) (hab hz) hz.1,
      h1.monotoneOn (hab hz) (hab ⟨hle, le_rfl⟩) hz.2⟩
  have hint2 : ∫ z, u₂ z ∂μ = ∫ z, ψ (u₁ z) ∂μ :=
    integral_congr_ae (hae.mono fun z hz => he z (hab hz))
  have hInt : Integrable (fun z => ψ (u₁ z)) μ :=
    (hμ.integrable c2).congr (hae.mono fun z hz => he z (hab hz))
  have hj := (hψI.subset hsubψ (convex_Icc _ _)).le_map_integral hψc isClosed_Icc hval
    (hμ.integrable c1) hInt
  rw [← hint2, ← hk1.2, ← hk2.2, ← he k₁ hk1.1] at hj
  exact (h2.le_iff_le hk2.1 hk1.1).mp hj

/-- **Proposition 6.C.2**, (iii) ⇒ (v) (MWG, p. 191; Exercise 6.C.6(b), p. 210). -/
theorem moreRiskAverse_iii_v {S : Set ℝ} {u₁ u₂ : ℝ → ℝ} (c1 : ContinuousOn u₁ S)
    (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S)
    (h : MoreRiskAverseIII S u₁ u₂) : MoreRiskAverseV S u₁ u₂ := by
  intro μ x hμ hx hle
  obtain ⟨k₁, hk1⟩ := certaintyEquivalent_exists c1 hμ
  obtain ⟨k₂, hk2⟩ := certaintyEquivalent_exists c2 hμ
  have hk := h μ k₁ k₂ hμ hk1 hk2
  rw [← hk2.2] at hle
  have hxk : x ≤ k₂ := (h2.le_iff_le hx hk2.1).mp hle
  rw [← hk1.2]
  exact h1.monotoneOn hx hk1.1 (hxk.trans hk)

/-- **Proposition 6.C.2**, (v) ⇒ (iii) (MWG, p. 191; Exercise 6.C.6(b), p. 210). -/
theorem moreRiskAverse_v_iii {S : Set ℝ} {u₁ u₂ : ℝ → ℝ} (h1 : StrictMonoOn u₁ S)
    (h : MoreRiskAverseV S u₁ u₂) : MoreRiskAverseIII S u₁ u₂ := by
  intro μ k₁ k₂ hμ hk1 hk2
  have := h μ k₂ hμ hk2.1 hk2.2.le
  rw [← hk1.2] at this
  exact (h1.le_iff_le hk2.1 hk1.1).mp this

/-- **Proposition 6.C.2**, (iii) ⇒ (iv) (MWG, p. 191; Exercise 6.C.7, p. 210). -/
theorem moreRiskAverse_iii_iv {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S)
    (h : MoreRiskAverseIII S u₁ u₂) : MoreRiskAverseIV S u₁ u₂ := by
  intro x ε hε hm hp
  have hx : x ∈ S := hS.ordConnected.out hm hp ⟨by linarith, by linarith⟩
  have l1 : u₁ (x - ε) < u₁ x := h1 hm hx (by linarith)
  have l2 : u₁ x < u₁ (x + ε) := h1 hx hp (by linarith)
  have m2 : u₂ (x - ε) < u₂ (x + ε) := h2 hm hp (by linarith)
  set π₁ := probPremium u₁ x ε
  have hs1 := (probPremium_spec u₁ x ε (l1.trans l2)).1
  have hs2 := (probPremium_spec u₂ x ε m2).1
  -- `π₁ ∈ (-1/2, 1/2)`, so the premium gamble is a lottery
  have hb1 : -(1 / 2) < π₁ := by
    by_contra hn
    have : (1 / 2 + π₁) * u₁ (x + ε) + (1 / 2 - π₁) * u₁ (x - ε) ≤ u₁ (x - ε) := by nlinarith
    linarith
  have hb2 : π₁ < 1 / 2 := by
    by_contra hn
    have : u₁ (x + ε) ≤ (1 / 2 + π₁) * u₁ (x + ε) + (1 / 2 - π₁) * u₁ (x - ε) := by nlinarith
    linarith
  set p := 1 / 2 + π₁
  have hp0 : 0 ≤ p := by simp only [p]; linarith
  have hp1 : p ≤ 1 := by simp only [p]; linarith
  have hG := binLot_isMoneyLottery hS hp hm p hp0 hp1
  have hce1 : IsCertaintyEquivalent S u₁ (binLot p (x + ε) (x - ε)) x := by
    refine ⟨hx, ?_⟩
    rw [integral_binLot _ _ _ _ hp0 hp1, hs1]
    simp only [p]; ring
  obtain ⟨k₂, hk2⟩ := certaintyEquivalent_exists c2 hG
  have hk := h _ x k₂ hG hce1 hk2
  have hu2 : ∫ z, u₂ z ∂(binLot p (x + ε) (x - ε)) ≤ u₂ x := by
    rw [← hk2.2]; exact h2.monotoneOn hk2.1 hx hk
  rw [integral_binLot _ _ _ _ hp0 hp1] at hu2
  rw [hs2] at hu2
  simp only [p] at hu2
  nlinarith

/-- **Proposition 6.C.2**, (iv) ⇒ (i) (MWG, p. 191; Exercise 6.C.7, p. 210), via
`r_A(x) = 4 lim_{ε ↓ 0} π(x, ε)/ε`. -/
theorem moreRiskAverse_iv_i {S : Set ℝ} (ho : IsOpen S) {u₁ u₂ : ℝ → ℝ}
    (d1 : ∀ x ∈ S, ContDiffAt ℝ 2 u₁ x) (d2 : ∀ x ∈ S, ContDiffAt ℝ 2 u₂ x)
    (p1 : ∀ x ∈ S, 0 < deriv u₁ x) (p2 : ∀ x ∈ S, 0 < deriv u₂ x)
    (h : MoreRiskAverseIV S u₁ u₂) : MoreRiskAverseI S u₁ u₂ := by
  intro x hx
  have t1 := arrowPratt_eq_four_probPremium_slope (d1 x hx) (p1 x hx)
  have t2 := arrowPratt_eq_four_probPremium_slope (d2 x hx) (p2 x hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho x hx
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), probPremium u₁ x ε / ε ≤ probPremium u₂ x ε / ε := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hδ] with ε hε hεδ
    have hε0 : (0 : ℝ) < ε := hε
    apply div_le_div_of_nonneg_right _ hε0.le
    apply h x ε hε0
    · apply hball; rw [Metric.mem_ball, Real.dist_eq]
      rw [show x - ε - x = -ε by ring, abs_neg, abs_of_pos hε0]; exact hεδ.2
    · apply hball; rw [Metric.mem_ball, Real.dist_eq]
      rw [show x + ε - x = ε by ring, abs_of_pos hε0]; exact hεδ.2
  have := le_of_tendsto_of_tendsto t1 t2 hev
  linarith

/-- **Proposition 6.C.2** (MWG, p. 191). For utilities twice continuously differentiable with
positive marginal utility on an open interval, the five definitions of "`u₂` is more risk
averse than `u₁`" are equivalent. -/
theorem proposition_6_C_2 {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) (hne : S.Nonempty)
    {u₁ u₂ : ℝ → ℝ} (d1 : ∀ x ∈ S, ContDiffAt ℝ 2 u₁ x) (d2 : ∀ x ∈ S, ContDiffAt ℝ 2 u₂ x)
    (p1 : ∀ x ∈ S, 0 < deriv u₁ x) (p2 : ∀ x ∈ S, 0 < deriv u₂ x) :
    List.TFAE [MoreRiskAverseI S u₁ u₂, MoreRiskAverseII S u₁ u₂, MoreRiskAverseIII S u₁ u₂,
      MoreRiskAverseIV S u₁ u₂, MoreRiskAverseV S u₁ u₂] := by
  have c1 : ContinuousOn u₁ S := fun x hx => (d1 x hx).continuousAt.continuousWithinAt
  have c2 : ContinuousOn u₂ S := fun x hx => (d2 x hx).continuousAt.continuousWithinAt
  have hint : interior S = S := ho.interior_eq
  have h1 : StrictMonoOn u₁ S := strictMonoOn_of_deriv_pos hS c1 (by
    rw [hint]; exact p1)
  have h2 : StrictMonoOn u₂ S := strictMonoOn_of_deriv_pos hS c2 (by
    rw [hint]; exact p2)
  have hI : (interior S).Nonempty := by rw [hint]; exact hne
  tfae_have 1 → 2 := fun h => moreRiskAverseII_of_kreps hS h1 h2 c1 c2
    ((Kreps.UtilityForMoney.proposition_6_8 hS hI d2 d1 h1 p2 p1).mpr h)
  tfae_have 2 → 3 := moreRiskAverse_ii_iii hS ho c1 c2 h1 h2
  tfae_have 3 → 5 := moreRiskAverse_iii_v c1 c2 h1 h2
  tfae_have 5 → 3 := moreRiskAverse_v_iii h1
  tfae_have 3 → 4 := moreRiskAverse_iii_iv hS c2 h1 h2
  tfae_have 4 → 1 := moreRiskAverse_iv_i ho d1 d2 p1 p2
  tfae_finish

end MWG.ChoiceUnderUncertainty
