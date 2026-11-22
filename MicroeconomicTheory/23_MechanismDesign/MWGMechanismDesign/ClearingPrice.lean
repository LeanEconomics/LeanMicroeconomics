/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.TradeExercises
import MWGMechanismDesign.TypeDensity
import Mathlib.Topology.Order.IntermediateValue

/-!
# Exercise 23.E.5: existence of a market-clearing price

MWG, Exercise 23.E.5 (p. 922). A continuum of sellers, of total mass `m_S ≥ 0`, with valuations
distributed on `[θ̲₁, θ̄₁]` with density `φ₁ > 0`, and a continuum of buyers, of mass `m_B ≥ 0`,
with valuations distributed on `[θ̲₂, θ̄₂]` with density `φ₂ > 0`. Parts (a)-(b)
(`exercise_23_E_5a`, `exercise_23_E_5b`) take a market-clearing price as given; here it is
shown to exist.

* `cp_measureReal_Iic`: `μ((-∞, p]) = Φ(max(θ̲, min(p, θ̄)))` for every `p`, a continuous function
  of `p`.
* `exercise_23_E_5_clearing`: there is a price `p ∈ [min(θ̲₁, θ̲₂), max(θ̄₁, θ̄₂)]` at which the
  mass of sellers with valuation below `p`, `m_SΦ₁(p)`, equals the mass of buyers with valuation
  above `p`, `m_B(1 - Φ₂(p))` (intermediate value theorem: supply minus demand is continuous,
  `-m_B ≤ 0` at the bottom and `m_S ≥ 0` at the top).
* `exercise_23_E_5_competitive`: hence the competitive mechanism of part (b) exists: at that
  price it is dominant strategy incentive compatible, individually rational and balances the
  budget.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- `μ((-∞, p]) = Φ(max(θ̲, min(p, θ̄)))` for every `p ∈ ℝ`. -/
theorem cp_measureReal_Iic (D : TypeDensity) (p : ℝ) :
    D.measure.real (Set.Iic p) = D.cdf (max D.lo (min p D.hi)) := by
  have := D.isProbabilityMeasure
  have hle := D.lo_lt_hi.le
  rcases lt_or_ge p D.lo with hp | hp
  · rw [min_eq_left (by linarith), max_eq_left hp.le]
    have h0 : D.measure (Set.Iic p) = 0 := measure_mono_null (fun x hx => fun hx' =>
      absurd (lt_of_le_of_lt (Set.mem_Iic.1 hx) hp) (not_lt.2 hx'.1)) D.measure_compl_Icc
    simp [measureReal_def, h0, TypeDensity.cdf]
  · rcases le_or_gt p D.hi with hp' | hp'
    · rw [min_eq_left hp', max_eq_right hp]
      exact D.measureReal_Iic ⟨hp, hp'⟩
    · rw [min_eq_right hp'.le, max_eq_right hle]
      have h1 : D.measure (Set.Iic p)ᶜ = 0 := measure_mono_null (fun x hx => fun hx' =>
        hx (Set.mem_Iic.2 (hx'.2.trans hp'.le))) D.measure_compl_Icc
      rw [prob_compl_eq_zero_iff measurableSet_Iic] at h1
      simp [measureReal_def, h1, TypeDensity.cdf, D.integral_dens]

/-- `μ((-∞, p)) = Φ(max(θ̲, min(p, θ̄)))` (no atoms). -/
theorem cp_measureReal_Iio (D : TypeDensity) (p : ℝ) :
    D.measure.real (Set.Iio p) = D.cdf (max D.lo (min p D.hi)) := by
  rw [measureReal_congr (Iio_ae_eq_Iic' (D.measure_singleton p)), cp_measureReal_Iic]

/-- `μ((p, ∞)) = 1 - Φ(max(θ̲, min(p, θ̄)))`. -/
theorem cp_measureReal_Ioi (D : TypeDensity) (p : ℝ) :
    D.measure.real (Set.Ioi p) = 1 - D.cdf (max D.lo (min p D.hi)) := by
  have := D.isProbabilityMeasure
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, cp_measureReal_Iic]

/-- The measure of a set under `c • μ`, `c = ofReal m` with `m ≥ 0`, is `m μ(s)`. -/
theorem cp_smul_real {m : ℝ} (hm : 0 ≤ m) (μ : Measure ℝ) (s : Set ℝ) :
    ((ENNReal.ofReal m) • μ).real s = m * μ.real s := by
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hm, measureReal_def]

/-- `Φ(θ̲) = 0` and `Φ(θ̄) = 1`. -/
theorem cp_cdf_lo_hi (D : TypeDensity) : D.cdf D.lo = 0 ∧ D.cdf D.hi = 1 :=
  ⟨intervalIntegral.integral_same, D.integral_dens⟩

/-- **Exercise 23.E.5** (MWG, p. 922), existence of a market-clearing price. With sellers of
mass `m_S ≥ 0` whose valuations have density `φ₁ > 0` on `[θ̲₁, θ̄₁]` and buyers of mass
`m_B ≥ 0` whose valuations have density `φ₂ > 0` on `[θ̲₂, θ̄₂]`, there is a price
`p ∈ [min(θ̲₁, θ̲₂), max(θ̄₁, θ̄₂)]` at which the mass of sellers with valuation below `p` equals
the mass of buyers with valuation above `p`. -/
theorem exercise_23_E_5_clearing (D1 D2 : TypeDensity) {mS mB : ℝ} (hS : 0 ≤ mS)
    (hB : 0 ≤ mB) :
    ∃ p ∈ Set.Icc (min D1.lo D2.lo) (max D1.hi D2.hi),
      MarketClears ((ENNReal.ofReal mS) • D1.measure) ((ENNReal.ofReal mB) • D2.measure) p := by
  set F : ℝ → ℝ := fun p => mS * D1.cdf (max D1.lo (min p D1.hi)) -
    mB * (1 - D2.cdf (max D2.lo (min p D2.hi))) with hF
  have hc : Continuous F := by
    refine (continuous_const.mul (D1.continuous_cdf.comp ?_)).sub
      (continuous_const.mul (continuous_const.sub (D2.continuous_cdf.comp ?_)))
    · exact continuous_const.max (continuous_id.min continuous_const)
    · exact continuous_const.max (continuous_id.min continuous_const)
  set a := min D1.lo D2.lo
  set b := max D1.hi D2.hi
  have hab : a ≤ b := (min_le_left _ _).trans (D1.lo_lt_hi.le.trans (le_max_left _ _))
  have h1 := D1.lo_lt_hi.le
  have h2 := D2.lo_lt_hi.le
  have hFa : F a = -mB := by
    have e1 : max D1.lo (min a D1.hi) = D1.lo :=
      max_eq_left ((min_le_left _ _).trans (min_le_left _ _))
    have e2 : max D2.lo (min a D2.hi) = D2.lo :=
      max_eq_left ((min_le_left _ _).trans (min_le_right _ _))
    simp only [hF, e1, e2, (cp_cdf_lo_hi D1).1, (cp_cdf_lo_hi D2).1]
    ring
  have hFb : F b = mS := by
    have e1 : max D1.lo (min b D1.hi) = D1.hi := by
      rw [min_eq_right (le_max_left _ _), max_eq_right h1]
    have e2 : max D2.lo (min b D2.hi) = D2.hi := by
      rw [min_eq_right (le_max_right _ _), max_eq_right h2]
    simp only [hF, e1, e2, (cp_cdf_lo_hi D1).2, (cp_cdf_lo_hi D2).2]
    ring
  obtain ⟨p, hp, hp0⟩ := intermediate_value_Icc hab hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (F a) (F b) by rw [hFa, hFb]; exact ⟨by linarith, hS⟩)
  refine ⟨p, hp, ?_⟩
  rw [MarketClears, cp_smul_real hS, cp_smul_real hB, cp_measureReal_Iio, cp_measureReal_Ioi]
  simp only [hF] at hp0
  linarith

/-- **Exercise 23.E.5(b)** (MWG, p. 922) with the clearing price constructed: there is a price
`p` at which the competitive mechanism (sellers below `p` sell, buyers above `p` buy, all at `p`)
makes truth telling a dominant strategy, is individually rational and balances the budget. -/
theorem exercise_23_E_5_competitive (D1 D2 : TypeDensity) {mS mB : ℝ} (hS : 0 ≤ mS)
    (hB : 0 ≤ mB) :
    ∃ p, MarketClears ((ENNReal.ofReal mS) • D1.measure) ((ENNReal.ofReal mB) • D2.measure) p ∧
      (∀ θ r, compSellerU p θ r ≤ compSellerU p θ θ) ∧
      (∀ θ r, compBuyerU p θ r ≤ compBuyerU p θ θ) ∧
      (∀ θ, θ ≤ compSellerU p θ θ) ∧ (∀ θ, 0 ≤ compBuyerU p θ θ) ∧
      p * ((ENNReal.ofReal mB) • D2.measure).real (Set.Ioi p) -
        p * ((ENNReal.ofReal mS) • D1.measure).real (Set.Iio p) = 0 := by
  obtain ⟨p, -, hp⟩ := exercise_23_E_5_clearing D1 D2 hS hB
  obtain ⟨h1, h2, h3, h4, h5⟩ := exercise_23_E_5b p
  exact ⟨p, hp, h1, h2, h3, h4, h5 _ _ hp⟩

end MWG.MechanismDesign
