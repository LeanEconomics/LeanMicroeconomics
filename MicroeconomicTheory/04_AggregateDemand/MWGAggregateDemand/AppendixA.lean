/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.LeftRightLim

/-!
# Appendix A: regularizing effects of aggregation

MWG, Chapter 4, Appendix A, pp. 122-123, Example 4.AA.1.

Two goods, quasilinear in the numeraire; the first good is indivisible and wanted in at most one
unit, worth `v` units of numeraire.

* `example_4_AA_1_individual`: the individual demand correspondence is `1` for `p₁ < v`,
  `{0, 1}` for `p₁ = v` and `0` for `p₁ > v` (Figure 4.AA.1(a)), so it jumps at `p₁ = v`.
* `example_4_AA_1_continuum`: with a continuum of consumers whose values `v` have a
  distribution `μ` with no atoms (dispersed preferences), average demand
  `x₁(p₁) = μ{v > p₁} = 1 - G(p₁)` is continuous (Figure 4.AA.1(b)).
* `example_4_AA_1_finite`: with finitely many consumers, average demand jumps by at least
  `1/I` at every consumer's value, so it is not continuous (the distribution function of a
  finite population "cannot quite be continuous").
-/

namespace MWG.AggregateDemand

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Example 4.AA.1** (MWG, p. 122). A consumer who values one unit of the indivisible good at
`v` (in numeraire) chooses `n ∈ {0, 1}` to maximize the quasilinear `v n - p₁ n`. -/
def indivisibleDemand (v p : ℝ) : Set ℝ :=
  {n | (n = 0 ∨ n = 1) ∧ ∀ m : ℝ, (m = 0 ∨ m = 1) → v * m - p * m ≤ v * n - p * n}

/-- **Example 4.AA.1** (MWG, p. 122; Figure 4.AA.1(a)). The individual demand correspondence:
`x₁(p₁) = 1` if `p₁ < v`, `{0, 1}` if `p₁ = v`, and `0` if `p₁ > v`. -/
theorem example_4_AA_1_individual (v p : ℝ) :
    (p < v → indivisibleDemand v p = {1}) ∧ (p = v → indivisibleDemand v p = {0, 1}) ∧
      (v < p → indivisibleDemand v p = {0}) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext n
    simp only [indivisibleDemand, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn | hn, hmax⟩
      · have := hmax 1 (Or.inr rfl)
        rw [hn] at this
        linarith
      · exact hn
    · rintro rfl
      refine ⟨Or.inr rfl, fun m hm => ?_⟩
      rcases hm with rfl | rfl <;> linarith
  · subst h
    ext n
    simp only [indivisibleDemand, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro hn
      exact ⟨hn, fun m _ => by ring_nf; rfl⟩
  · ext n
    simp only [indivisibleDemand, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn | hn, hmax⟩
      · exact hn
      · have := hmax 0 (Or.inl rfl)
        rw [hn] at this
        linarith
    · rintro rfl
      refine ⟨Or.inl rfl, fun m hm => ?_⟩
      rcases hm with rfl | rfl <;> linarith

/-- **Example 4.AA.1** (MWG, pp. 122-123; Figure 4.AA.1(b)). With a continuum of consumers
whose values `v` are distributed according to a probability measure `μ` with no atoms
(dispersed preferences: the distribution function `G` is continuous), average demand for the
first good, the mass `μ{v > p₁}` of consumers who buy, equals `1 - G(p₁)` and is a continuous
function of `p₁`, although no individual demand is. -/
theorem example_4_AA_1_continuum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hna : ∀ a, μ {a} = 0) :
    (∀ p, μ.real (Set.Ioi p) = 1 - cdf μ p) ∧ Continuous fun p => μ.real (Set.Ioi p) := by
  have hcompl : ∀ p, μ.real (Set.Ioi p) = 1 - cdf μ p := by
    intro p
    rw [cdf_eq_real, ← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
  refine ⟨hcompl, ?_⟩
  have hcont : Continuous (cdf μ) := by
    rw [continuous_iff_continuousAt]
    intro a
    have hmono := (cdf μ).mono
    rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
    have hright : Function.rightLim (cdf μ) a = cdf μ a :=
      hmono.continuousWithinAt_Ioi_iff_rightLim_eq.mp
        (((cdf μ).right_continuous a).mono Set.Ioi_subset_Ici_self)
    have hsing := (cdf μ).measure_singleton a
    rw [measure_cdf, hna a] at hsing
    have h1 : cdf μ a - Function.leftLim (cdf μ) a ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing.symm
    have h2 : Function.leftLim (cdf μ) a ≤ cdf μ a := Monotone.leftLim_le hmono le_rfl
    rw [hright]
    linarith
  have : (fun p => μ.real (Set.Ioi p)) = fun p => 1 - cdf μ p := funext hcompl
  rw [this]
  exact continuous_const.sub hcont

/-- **Example 4.AA.1** (MWG, p. 123). With finitely many consumers with values `vᵢ`, average
demand `x₁(p₁) = #{i : vᵢ > p₁}/I` drops by at least `1/I` at every value `vⱼ`: it is at least
`x₁(vⱼ) + 1/I` for every `p₁ < vⱼ`, so it is not continuous at `vⱼ`. -/
theorem example_4_AA_1_finite {I : ℕ} (v : Fin I → ℝ) (j : Fin I) :
    (∀ p, p < v j → ((Finset.univ.filter fun i => v j < v i).card : ℝ) / I + 1 / I ≤
      ((Finset.univ.filter fun i => p < v i).card : ℝ) / I) ∧
      ¬ ContinuousAt (fun p : ℝ => ((Finset.univ.filter fun i => p < v i).card : ℝ) / I)
        (v j) := by
  have hI : (0 : ℝ) < I := by
    have : 0 < I := Fin.pos j
    exact_mod_cast this
  have hjump : ∀ p, p < v j → ((Finset.univ.filter fun i => v j < v i).card : ℝ) / I + 1 / I ≤
      ((Finset.univ.filter fun i => p < v i).card : ℝ) / I := by
    intro p hp
    have hsub : insert j (Finset.univ.filter fun i => v j < v i) ⊆
        Finset.univ.filter fun i => p < v i := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        linarith
    have hnot : j ∉ Finset.univ.filter fun i => v j < v i := by simp
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hcard
    have : ((Finset.univ.filter fun i => v j < v i).card : ℝ) + 1 ≤
        ((Finset.univ.filter fun i => p < v i).card : ℝ) := by exact_mod_cast hcard
    rw [← add_div]
    exact div_le_div_of_nonneg_right this hI.le
  refine ⟨hjump, fun hc => ?_⟩
  have hlim := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (v j)))
  have hle : ((Finset.univ.filter fun i => v j < v i).card : ℝ) / I + 1 / I ≤
      ((Finset.univ.filter fun i => v j < v i).card : ℝ) / I := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hjump p hp
  have : (0 : ℝ) < 1 / I := by positivity
  linarith

end MWG.AggregateDemand
