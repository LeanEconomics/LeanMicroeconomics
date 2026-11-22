/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.StrassenGrid
import UtilityForMoney.SupermartingaleCoupling

/-!
# Martingale couplings of the discretizations

Preparation for Proposition 6.D.2, (i) ⇒ (ii) (MWG, p. 199). If `F` dominates `G` for every
nondecreasing concave utility and the means agree, then on every grid the contraction of `F`
dominates the dilation of `G` in Kreps's finite sense (`SecondOrderDominates`), with equal
means. Kreps's finite theorem `supermartingaleCoupling_of_dominance` (Kreps I, Problem 6.6)
gives a joint table with nonpositive conditional drift; equal means force every row's drift to
vanish, so the table is a martingale coupling. We record it as a finite Borel probability
measure `π` on `ℝ²` with first marginal the contraction, second marginal the dilation and
`∫ φ(x)(y - x) dπ = 0` for every `φ`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The simple lottery `∑_{j<n} m_j δ_{c_j}` (Kreps's `SimpleLottery`). -/
noncomputable def atomLottery (n : ℕ) (c m : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hs : ∑ j ∈ Finset.range n, m j = 1) : Kreps.UtilityForMoney.SimpleLottery ℝ where
  weights := ∑ j ∈ Finset.range n, Finsupp.single (c j) (m j)
  nonneg := by
    intro x
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact hm j
    · exact le_rfl
  total := by
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index, hs]

/-- Expected utility of `∑_j m_j δ_{c_j}` is `∑_j m_j u(c_j)`. -/
theorem expectedUtility_atomLottery (n : ℕ) (c m : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hs : ∑ j ∈ Finset.range n, m j = 1) (U : ℝ → ℝ) :
    Kreps.UtilityForMoney.ExpectedUtility U (atomLottery n c m hm hs) =
      ∑ j ∈ Finset.range n, m j * U (c j) := by
  unfold Kreps.UtilityForMoney.ExpectedUtility atomLottery
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

/-- Every support point of `∑_j m_j δ_{c_j}` is one of the `c_j`. -/
theorem mem_support_atomLottery {n : ℕ} {c m : ℕ → ℝ} {hm : ∀ j, 0 ≤ m j}
    {hs : ∑ j ∈ Finset.range n, m j = 1} {x : ℝ}
    (hx : x ∈ (atomLottery n c m hm hs).weights.support) :
    ∃ j ∈ Finset.range n, c j = x := by
  classical
  have := Finsupp.support_finsetSum hx
  rw [Finset.mem_biUnion] at this
  obtain ⟨j, hj, hx'⟩ := this
  exact ⟨j, hj, (Finset.mem_singleton.mp (Finsupp.support_single_subset hx')).symm⟩

/-- Integration against a finite combination of point masses. -/
theorem integral_sum_dirac {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a : ι → ℝ × ℝ) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (a i)) = ∑ i ∈ s, w i * F (a i) := by
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- **Finite martingale coupling of the discretizations.** If `F` (`μ`) dominates `G` (`ν`) for
every nondecreasing concave utility on `ℝ`, with equal means, both concentrated on `(0, N h]`,
there is a finite probability measure on `ℝ²`, concentrated on `[-h, N h + h]²`, whose first
marginal is the contraction of `F`, whose second marginal is the dilation of `G`, and with
`∫ φ(x)(y - x) dπ = 0` for every `φ`. -/
theorem exists_grid_martingale_coupling {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hμ : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) (hν : ∀ᵐ t ∂ν, t ∈ Ioc 0 (N * h))
    (hdom : ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ univ U → ∫ t, U t ∂ν ≤ ∫ t, U t ∂μ)
    (hmean : ∫ t, t ∂μ = ∫ t, t ∂ν) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      (∀ᵐ p ∂π, p.1 ∈ Icc (-h) (N * h + h) ∧ p.2 ∈ Icc (-h) (N * h + h)) ∧
      (∀ g : ℝ → ℝ, ∫ p, g p.1 ∂π =
        ∑ j ∈ Finset.range (N + 1), gridMass μ h j * g (gridCtr μ h j)) ∧
      (∀ g : ℝ → ℝ, ∫ p, g p.2 ∂π =
        ∑ j ∈ Finset.range (N + 1), gridMass ν h j * g (gridPt h j)) ∧
      ∀ φ : ℝ → ℝ, ∫ p, φ p.1 * (p.2 - p.1) ∂π = 0 := by
  classical
  set p := atomLottery (N + 1) (gridCtr μ h) (gridMass μ h) (gridMass_nonneg μ h)
    (gridMass_sum hh hμ) with hp
  set q := atomLottery (N + 1) (gridPt h) (gridMass ν h) (gridMass_nonneg ν h)
    (gridMass_sum hh hν) with hq
  have hdomK : Kreps.UtilityForMoney.SecondOrderDominates p q := by
    intro U hm hc
    rw [hp, hq, expectedUtility_atomLottery, expectedUtility_atomLottery]
    calc _ ≤ ∫ t, U t ∂ν := dilation_le hh hν hc
      _ ≤ ∫ t, U t ∂μ := hdom U hm hc
      _ ≤ _ := le_contraction hh hμ hm hc
  obtain ⟨C, hC⟩ := Kreps.UtilityForMoney.supermartingaleCoupling_of_dominance hdomK
  -- row and column expectations
  have hrow (g : ℝ → ℝ) : ∑ i : p.weights.support, ∑ j : q.weights.support,
      C.mass i j * g i.val = ∑ j ∈ Finset.range (N + 1), gridMass μ h j * g (gridCtr μ h j) := by
    simp only [← Finset.sum_mul, C.row_sum]
    rw [Kreps.UtilityForMoney.sum_support_utility, hp, expectedUtility_atomLottery]
  have hcol (g : ℝ → ℝ) : ∑ i : p.weights.support, ∑ j : q.weights.support,
      C.mass i j * g j.val = ∑ j ∈ Finset.range (N + 1), gridMass ν h j * g (gridPt h j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, C.col_sum]
    rw [Kreps.UtilityForMoney.sum_support_utility, hq, expectedUtility_atomLottery]
  -- every row has zero drift
  have hzero : ∀ i : p.weights.support,
      ∑ j : q.weights.support, C.mass i j * (j.val - i.val) = 0 := by
    have htot : ∑ i : p.weights.support,
        ∑ j : q.weights.support, C.mass i j * (j.val - i.val) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hcol (fun x => x), hrow (fun x => x), dilation_mean hh hν, contraction_mean hh hμ,
        hmean, sub_self]
    exact fun i => (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hC i).mp htot i
      (Finset.mem_univ i)
  set π : Measure (ℝ × ℝ) := ∑ ij : p.weights.support × q.weights.support,
    ENNReal.ofReal (C.mass ij.1 ij.2) • Measure.dirac ((ij.1 : ℝ), (ij.2 : ℝ)) with hπ
  have hint (F : ℝ × ℝ → ℝ) : ∫ x, F x ∂π = ∑ i : p.weights.support, ∑ j : q.weights.support,
      C.mass i j * F (i.val, j.val) := by
    rw [hπ, integral_sum_dirac _ (fun ij : p.weights.support × q.weights.support =>
      C.mass ij.1 ij.2) (fun ij => C.nonneg ij.1 ij.2), Fintype.sum_prod_type]
  have hbox (N' : ℕ) (hN' : N' ≤ N) (y : ℝ) (hy : |y - gridPt h N'| ≤ h) :
      y ∈ Icc (-h) (N * h + h) := by
    have h0 : 0 ≤ gridPt h N' := by unfold gridPt; positivity
    have h1 : gridPt h N' ≤ N * h := by
      unfold gridPt
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN') hh.le
    rw [abs_le] at hy
    exact ⟨by linarith, by linarith⟩
  refine ⟨π, ⟨?_⟩, ?_, fun g => ?_, fun g => ?_, fun φ => ?_⟩
  · rw [hπ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun ij _ => C.nonneg ij.1 ij.2, Fintype.sum_prod_type]
    simp only [C.row_sum]
    rw [Kreps.UtilityForMoney.support_mass_sum, ENNReal.ofReal_one]
  · rw [ae_iff, hπ, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    convert mul_zero _
    rw [dirac_eq_zero_iff_not_mem (by measurability)]
    simp only [mem_ofPred_eq, not_not]
    obtain ⟨k, hk, hck⟩ := mem_support_atomLottery ij.1.property
    obtain ⟨l, hl, hcl⟩ := mem_support_atomLottery ij.2.property
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hl' : l ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    refine ⟨?_, ?_⟩
    · rw [← hck]; exact hbox k hk' _ (abs_gridCtr_sub_le hh hμ k)
    · rw [← hcl]; exact hbox l hl' _ (by simp [hh.le])
  · rw [hint (fun x => g x.1)]; exact hrow g
  · rw [hint (fun x => g x.2)]; exact hcol g
  · rw [hint (fun x => φ x.1 * (x.2 - x.1))]
    refine Finset.sum_eq_zero fun i _ => ?_
    have e : ∀ j : q.weights.support, C.mass i j * (φ i.val * (j.val - i.val)) =
        φ i.val * (C.mass i j * (j.val - i.val)) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, hzero i, mul_zero]

end MWG.ChoiceUnderUncertainty
