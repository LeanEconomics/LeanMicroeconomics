/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Regular
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniformly distributed types

MWG, Section 13.B, p. 442 (Example 13.B.1) and the concrete instances of this chapter.

`unifMeas a b` is the uniform distribution on `[a, b]`. We prove that it satisfies the standing
assumptions (`TypeDist`, `HasPosDensity`) and compute `F(c)` and `∫_{θ ≤ c} θ dF` for
`a ≤ c ≤ b`.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set

/-- The uniform distribution on `[a, b]`. -/
noncomputable def unifMeas (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

theorem unifMeas_apply {a b : ℝ} (hab : a < b) {S : Set ℝ} (hS : MeasurableSet S) :
    unifMeas a b S = ENNReal.ofReal ((volume (S ∩ Icc a b)).toReal / (b - a)) := by
  have hfin : volume (S ∩ Icc a b) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right (by simp [Real.volume_Icc])
  rw [unifMeas, Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul,
    ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_toReal hfin, div_eq_mul_inv, mul_comm]

theorem unifMeas_isProb {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (unifMeas a b) := by
  constructor
  rw [unifMeas_apply hab MeasurableSet.univ, univ_inter, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), div_self (by linarith), ENNReal.ofReal_one]

theorem unifMeas_compl {a b : ℝ} (hab : a < b) : unifMeas a b (Icc a b)ᶜ = 0 := by
  rw [unifMeas_apply hab measurableSet_Icc.compl, compl_inter_self, measure_empty,
    ENNReal.toReal_zero, zero_div, ENNReal.ofReal_zero]

theorem Iic_inter_Icc_of_le {a b c : ℝ} (hcb : c ≤ b) : Iic c ∩ Icc a b = Icc a c := by
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hcb⟩

/-- The uniform distribution on `[a, b]`, `0 ≤ a < b`, satisfies the standing assumptions. -/
theorem unifMeas_typeDist {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : TypeDist (unifMeas a b) a b where
  nonneg := ha
  lt := hab
  prob := unifMeas_isProb hab
  supp := unifMeas_compl hab

/-- The uniform distribution has a positive density. -/
theorem unifMeas_density {a b : ℝ} (hab : a < b) : HasPosDensity (unifMeas a b) a b where
  noAtom x := by
    rw [unifMeas_apply hab (measurableSet_singleton x)]
    have : volume ({x} ∩ Icc a b) = 0 := measure_mono_null inter_subset_left (by simp)
    rw [this]; simp
  pos c d hc hcd hd := by
    rw [unifMeas_apply hab measurableSet_Icc, Icc_inter_Icc, max_eq_left hc, min_eq_left hd,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    exact ENNReal.ofReal_pos.2 (div_pos (by linarith) (by linarith))

/-- `F(c) = (c - a)/(b - a)` for the uniform distribution. -/
theorem unifMeas_Iic {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    unifMeas a b (Iic c) = ENNReal.ofReal ((c - a) / (b - a)) := by
  rw [unifMeas_apply hab measurableSet_Iic, Iic_inter_Icc_of_le hcb, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

/-- `∫_{θ ≤ c} θ dF = (c² - a²) / (2 (b - a))` for the uniform distribution. -/
theorem unifMeas_setIntegral_Iic {a b c : ℝ} (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ θ in Iic c, θ ∂(unifMeas a b) = (c ^ 2 - a ^ 2) / (2 * (b - a)) := by
  rw [unifMeas, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict
    measurableSet_Iic, Iic_inter_Icc_of_le hcb, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hac, integral_id, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  field_simp

/-- `E[θ] = (a + b)/2` for the uniform distribution. -/
theorem unifMeas_mean {a b : ℝ} (hab : a < b) : meanType (unifMeas a b) = (a + b) / 2 := by
  have h := unifMeas_setIntegral_Iic hab hab.le le_rfl
  have hfull : ∫ θ in Iic b, θ ∂(unifMeas a b) = ∫ θ, θ ∂(unifMeas a b) := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    have hs : ∀ᵐ θ ∂(unifMeas a b), θ ∈ Icc a b :=
      measure_eq_zero_iff_ae_notMem.1 (unifMeas_compl hab) |>.mono fun _ hx => by simpa using hx
    filter_upwards [hs] with θ hθ hθc
    exact absurd hθ.2 hθc
  rw [meanType, ← hfull, h]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

end MWG.AdverseSelection
