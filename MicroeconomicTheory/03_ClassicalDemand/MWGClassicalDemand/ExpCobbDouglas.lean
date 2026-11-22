/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.ExpContinuity
import MWGClassicalDemand.UMPExamples

/-!
# Hicksian demand and the expenditure function for Cobb-Douglas utility

MWG, Example 3.E.1 (p. 63) and Exercises 3.E.2 (p. 63) and 3.E.8 (p. 98).

For `u(x₁, x₂) = x₁^α x₂^{1-α}` (`α ∈ (0, 1)`), `p ≫ 0` and `ū > 0 = u(0)`:
`e(p, ū) = α^{-α}(1-α)^{α-1} p₁^α p₂^{1-α} ū` and
`h(p, ū) = ([αp₂/((1-α)p₁)]^{1-α} ū, [(1-α)p₁/(αp₂)]^α ū)`, the unique solution of the EMP
(`example_3_E_1`). The proof uses the general theory: `v(p, w) = w C(p)` (Example 3.D.2),
so `e(p, ·)` is its inverse `ū / C(p)` (3.E.1, Exercise 3.E.8), and `h(p, ū) = x(p, e(p, ū))`
(3.E.4). Exercise 3.E.2 verifies Propositions 3.E.2 and 3.E.3 from the formulas.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

/-- The Cobb-Douglas utility `x₁^α x₂^{1-α}` is continuous on `ℝ²_+` for `α ∈ (0, 1)`. -/
theorem cobbDouglas_continuousOn {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ContinuousOn (cobbDouglasUtility 1 α) (nonnegOrthant 2) := by
  unfold cobbDouglasUtility
  apply Continuous.continuousOn
  have h1 : 0 < 1 - α := by linarith
  exact continuous_const.mul (((continuous_apply 0).rpow_const fun _ => Or.inr hα0.le).mul
    ((continuous_apply 1).rpow_const fun _ => Or.inr h1.le))

/-- The Cobb-Douglas preference is locally nonsatiated on `ℝ²_+`. -/
theorem cobbDouglas_lns {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    LocallyNonsatiated (nonnegOrthant 2) (utilityPref (cobbDouglasUtility 1 α)) := by
  have h1 : 0 < 1 - α := by linarith
  intro x hx ε hε
  set c := ε / 2
  have hc : 0 < c := by positivity
  refine ⟨x + fun _ => c, fun l => add_nonneg (hx l) hc.le, ?_, ?_⟩
  · rw [euclidDist_add_const, abs_of_pos hc]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have : Real.sqrt ((2 : ℕ) : ℝ) * c ≤ 2 * c := by
      push_cast; exact mul_le_mul_of_nonneg_right this hc.le
    simp only [c] at this ⊢
    linarith
  · have hlt : cobbDouglasUtility 1 α x < cobbDouglasUtility 1 α (x + fun _ => c) := by
      simp only [cobbDouglasUtility, one_mul, Pi.add_apply]
      have hx0 := hx 0
      have hx1 := hx 1
      have a1 : x 0 ^ α < (x 0 + c) ^ α := Real.rpow_lt_rpow hx0 (by linarith) hα0
      have a2 : x 1 ^ (1 - α) ≤ (x 1 + c) ^ (1 - α) :=
        Real.rpow_le_rpow hx1 (by linarith) h1.le
      have a3 : 0 < (x 1 + c) ^ (1 - α) := Real.rpow_pos_of_pos (by linarith) _
      have a4 : 0 ≤ x 0 ^ α := Real.rpow_nonneg hx0 _
      calc x 0 ^ α * x 1 ^ (1 - α) ≤ x 0 ^ α * (x 1 + c) ^ (1 - α) :=
            mul_le_mul_of_nonneg_left a2 a4
        _ < (x 0 + c) ^ α * (x 1 + c) ^ (1 - α) := mul_lt_mul_of_pos_right a1 a3
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- The constant `C(p) = (α/p₁)^α ((1-α)/p₂)^{1-α}` with `v(p, w) = w C(p)`. -/
noncomputable def cdConst (α : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  (α / p 0) ^ α * ((1 - α) / p 1) ^ (1 - α)

/-- `C(p) > 0`. -/
theorem cdConst_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) : 0 < cdConst α p := by
  have h1 : 0 < 1 - α := by linarith
  exact mul_pos (Real.rpow_pos_of_pos (div_pos hα0 (hp 0)) _)
    (Real.rpow_pos_of_pos (div_pos h1 (hp 1)) _)

/-- The Cobb-Douglas indirect utility is linear in wealth: `v(p, w) = w C(p)` for `w ≥ 0`. -/
theorem cobbDouglasIndirect_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    cobbDouglasIndirect α p w = w * cdConst α p := by
  have h1 : 0 < 1 - α := by linarith
  unfold cobbDouglasIndirect cdConst
  rw [show α * w / p 0 = w * (α / p 0) by ring, show (1 - α) * w / p 1 = w * ((1 - α) / p 1) by
    ring, Real.mul_rpow hw.le (div_pos hα0 (hp 0)).le,
    Real.mul_rpow hw.le (div_pos h1 (hp 1)).le]
  have : w ^ α * w ^ (1 - α) = w := by
    rw [← Real.rpow_add hw, add_sub_cancel, Real.rpow_one]
  calc w ^ α * (α / p 0) ^ α * (w ^ (1 - α) * ((1 - α) / p 1) ^ (1 - α))
      = (w ^ α * w ^ (1 - α)) * ((α / p 0) ^ α * ((1 - α) / p 1) ^ (1 - α)) := by ring
    _ = w * ((α / p 0) ^ α * ((1 - α) / p 1) ^ (1 - α)) := by rw [this]

/-- **Example 3.E.1** (MWG, p. 63). The Cobb-Douglas expenditure function `ū / C(p)`. -/
noncomputable def cdExpenditure (α : ℝ) (p : Fin 2 → ℝ) (ub : ℝ) : ℝ := ub / cdConst α p

/-- **Example 3.E.1** (MWG, p. 63). The Cobb-Douglas Hicksian demand `x(p, e(p, ū))`. -/
noncomputable def cdHicksian (α : ℝ) (p : Fin 2 → ℝ) (ub : ℝ) : Fin 2 → ℝ :=
  cobbDouglasDemand α p (cdExpenditure α p ub)

/-- **Example 3.E.1** (MWG, p. 63). The book's formula
`e(p, ū) = [α^{-α}(1-α)^{α-1}] p₁^α p₂^{1-α} ū`. -/
theorem cdExpenditure_eq_book {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (ub : ℝ) :
    cdExpenditure α p ub =
      α ^ (-α) * (1 - α) ^ (α - 1) * p 0 ^ α * p 1 ^ (1 - α) * ub := by
  have h1 : 0 < 1 - α := by linarith
  have hp0 := hp 0
  have hp1 := hp 1
  unfold cdExpenditure cdConst
  rw [Real.div_rpow hα0.le hp0.le, Real.div_rpow h1.le hp1.le,
    Real.rpow_neg hα0.le, show α - 1 = -(1 - α) by ring, Real.rpow_neg h1.le]
  have := Real.rpow_pos_of_pos hα0 α
  have := Real.rpow_pos_of_pos h1 (1 - α)
  have := Real.rpow_pos_of_pos hp0 α
  have := Real.rpow_pos_of_pos hp1 (1 - α)
  field_simp

/-- **Example 3.E.1** (MWG, p. 63). The book's formulas
`h₁(p, ū) = [αp₂/((1-α)p₁)]^{1-α} ū` and `h₂(p, ū) = [(1-α)p₁/(αp₂)]^α ū`. -/
theorem cdHicksian_eq_book {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (ub : ℝ) :
    cdHicksian α p ub 0 = (α * p 1 / ((1 - α) * p 0)) ^ (1 - α) * ub ∧
      cdHicksian α p ub 1 = ((1 - α) * p 0 / (α * p 1)) ^ α * ub := by
  have h1 : 0 < 1 - α := by linarith
  have hp0 := hp 0
  have hp1 := hp 1
  have ha := Real.rpow_pos_of_pos hα0 α
  have hb := Real.rpow_pos_of_pos h1 (1 - α)
  have hc := Real.rpow_pos_of_pos hp0 α
  have hd := Real.rpow_pos_of_pos hp1 (1 - α)
  have e1 : α ^ (1 - α) = α / α ^ α := by
    rw [eq_div_iff ha.ne', ← Real.rpow_add hα0, sub_add_cancel, Real.rpow_one]
  have e2 : p 0 ^ (1 - α) = p 0 / p 0 ^ α := by
    rw [eq_div_iff hc.ne', ← Real.rpow_add hp0, sub_add_cancel, Real.rpow_one]
  have e3 : (1 - α) ^ α = (1 - α) / (1 - α) ^ (1 - α) := by
    rw [eq_div_iff hb.ne', ← Real.rpow_add h1, add_sub_cancel, Real.rpow_one]
  have e4 : p 1 ^ α = p 1 / p 1 ^ (1 - α) := by
    rw [eq_div_iff hd.ne', ← Real.rpow_add hp1, add_sub_cancel, Real.rpow_one]
  unfold cdHicksian cobbDouglasDemand cdExpenditure cdConst
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.div_rpow hα0.le hp0.le, Real.div_rpow h1.le hp1.le,
    Real.div_rpow (mul_pos hα0 hp1).le (mul_pos h1 hp0).le,
    Real.div_rpow (mul_pos h1 hp0).le (mul_pos hα0 hp1).le,
    Real.mul_rpow hα0.le hp1.le, Real.mul_rpow h1.le hp0.le, Real.mul_rpow h1.le hp0.le,
    Real.mul_rpow hα0.le hp1.le]
  constructor
  · rw [e1, e2]
    field_simp
  · rw [e3, e4]
    field_simp

/-- **Example 3.E.1** (MWG, p. 63). For `α ∈ (0, 1)`, `p ≫ 0` and `ū > 0`, the EMP for the
Cobb-Douglas utility has the unique solution `h(p, ū) = cdHicksian α p ū`, and the expenditure
function is `e(p, ū) = cdExpenditure α p ū`. -/
theorem example_3_E_1 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 < ub) :
    expenditure (cobbDouglasUtility 1 α) p ub = cdExpenditure α p ub ∧
      hicksianDemand (cobbDouglasUtility 1 α) p ub = {cdHicksian α p ub} := by
  have hC := cdConst_pos hα0 hα1 hp
  set w := cdExpenditure α p ub with hw_def
  have hw : 0 < w := div_pos hub hC
  have hrep := representsOn_utilityPref (nonnegOrthant 2) (cobbDouglasUtility 1 α)
  have hcont := cobbDouglas_continuousOn hα0 hα1
  have hlns := cobbDouglas_lns hα0 hα1
  have hv : indirectUtility (cobbDouglasUtility 1 α) p w = ub := by
    rw [example_3_D_2 hα0 hα1 hp hw.le, cobbDouglasIndirect_eq hα0 hα1 hp hw, hw_def,
      cdExpenditure, div_mul_cancel₀ _ hC.ne']
  have he : expenditure (cobbDouglasUtility 1 α) p ub = w := by
    rw [← hv]
    exact equation_3_E_1_left hrep hcont hlns hp hw.le
  have hu0 : cobbDouglasUtility 1 α 0 < ub := by
    have : cobbDouglasUtility 1 α 0 = 0 := by
      simp [cobbDouglasUtility, Real.zero_rpow hα0.ne', Real.zero_rpow (by linarith : 1 - α ≠ 0)]
    rw [this]; exact hub
  have hne : ∃ x ∈ nonnegOrthant 2, ub ≤ cobbDouglasUtility 1 α x := by
    obtain ⟨x, hx⟩ := proposition_3_D_1 hcont hp hw.le
    exact ⟨x, hx.1.1, by rw [← hv, indirectUtility_eq_of_mem hx]⟩
  refine ⟨he, ?_⟩
  rw [equation_3_E_4_left hrep hcont hlns hp hu0 hne, he,
    example_3_D_1 one_pos hα0 hα1 hp hw.le]
  rfl

/-- **Exercise 3.E.8** (MWG, p. 98). For Cobb-Douglas utility the relations (3.E.1) hold:
`e(p, v(p, w)) = w` and `v(p, e(p, ū)) = ū`; the expenditure function is obtained by inverting
the indirect utility function `v(p, w) = w C(p)` and conversely. -/
theorem exercise_3_E_8_values {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w ub : ℝ} (hw : 0 < w) (hub : 0 < ub) :
    cdExpenditure α p (cobbDouglasIndirect α p w) = w ∧
      cobbDouglasIndirect α p (cdExpenditure α p ub) = ub := by
  have hC := cdConst_pos hα0 hα1 hp
  constructor
  · rw [cobbDouglasIndirect_eq hα0 hα1 hp hw, cdExpenditure, mul_div_cancel_right₀ _ hC.ne']
  · rw [cdExpenditure, cobbDouglasIndirect_eq hα0 hα1 hp (div_pos hub hC),
      div_mul_cancel₀ _ hC.ne']

/-- **Exercise 3.E.8** (MWG, p. 98). For Cobb-Douglas utility the relations (3.E.4) hold:
`h(p, ū) = x(p, e(p, ū))` and `x(p, w) = h(p, v(p, w))`. -/
theorem exercise_3_E_8_demands {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) {w ub : ℝ} (hw : 0 < w) (hub : 0 < ub) :
    cdHicksian α p ub = cobbDouglasDemand α p (cdExpenditure α p ub) ∧
      cobbDouglasDemand α p w = cdHicksian α p (cobbDouglasIndirect α p w) := by
  refine ⟨rfl, ?_⟩
  rw [cdHicksian, (exercise_3_E_8_values hα0 hα1 hp hw hub).1]

/-- **Exercise 3.E.2** (MWG, p. 63). The Cobb-Douglas expenditure function and Hicksian demand
have the properties of Propositions 3.E.2 and 3.E.3 on `p ≫ 0`, `ū > 0`: `e` is homogeneous of
degree one in `p`, strictly increasing in `ū`, nondecreasing in `p` and concave in `p`; `h` is
homogeneous of degree zero in `p`, has no excess utility, and is single-valued. -/
theorem exercise_3_E_2 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ p (t ub : ℝ), StrictlyPositive p → 0 < t →
        cdExpenditure α (t • p) ub = t * cdExpenditure α p ub) ∧
      (∀ p (ub ub' : ℝ), StrictlyPositive p → ub < ub' →
        cdExpenditure α p ub < cdExpenditure α p ub') ∧
      (∀ p p' (ub : ℝ), StrictlyPositive p → p ≤ p' → 0 < ub →
        cdExpenditure α p ub ≤ cdExpenditure α p' ub) ∧
      (∀ ub : ℝ, 0 < ub →
        ConcaveOn ℝ {p : Fin 2 → ℝ | StrictlyPositive p} (fun p => cdExpenditure α p ub)) ∧
      (∀ p (t ub : ℝ), StrictlyPositive p → 0 < t → 0 < ub →
        cdHicksian α (t • p) ub = cdHicksian α p ub) ∧
      (∀ p (ub : ℝ), StrictlyPositive p → 0 < ub →
        cobbDouglasUtility 1 α (cdHicksian α p ub) = ub) := by
  have hpos : ∀ (p : Fin 2 → ℝ) (t : ℝ), StrictlyPositive p → 0 < t → StrictlyPositive (t • p) :=
    fun p t hp ht l => mul_pos ht (hp l)
  have hcont := cobbDouglas_continuousOn hα0 hα1
  have hrep := representsOn_utilityPref (nonnegOrthant 2) (cobbDouglasUtility 1 α)
  have hlns := cobbDouglas_lns hα0 hα1
  have hneat : ∀ ub : ℝ, ∃ x ∈ nonnegOrthant 2, ub ≤ cobbDouglasUtility 1 α x := by
    intro ub
    refine ⟨fun _ => max ub 1, fun _ => le_trans zero_le_one (le_max_right _ _), ?_⟩
    simp only [cobbDouglasUtility, one_mul]
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one (le_max_right _ _)), add_sub_cancel,
      Real.rpow_one]
    exact le_max_left _ _
  refine ⟨fun p t ub hp ht => ?_, fun p ub ub' hp hlt => ?_, fun p p' ub hp hpp hub => ?_,
    fun ub hub => ?_, fun p t ub hp ht hub => ?_, fun p ub hp hub => ?_⟩
  · have hC : cdConst α (t • p) = t⁻¹ * cdConst α p := by
      have h1 : 0 < 1 - α := by linarith
      unfold cdConst
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show α / (t * p 0) = t⁻¹ * (α / p 0) by field_simp,
        show (1 - α) / (t * p 1) = t⁻¹ * ((1 - α) / p 1) by field_simp,
        Real.mul_rpow (inv_pos.mpr ht).le (div_pos hα0 (hp 0)).le,
        Real.mul_rpow (inv_pos.mpr ht).le (div_pos h1 (hp 1)).le]
      have : t⁻¹ ^ α * t⁻¹ ^ (1 - α) = t⁻¹ := by
        rw [← Real.rpow_add (inv_pos.mpr ht), add_sub_cancel, Real.rpow_one]
      calc t⁻¹ ^ α * (α / p 0) ^ α * (t⁻¹ ^ (1 - α) * ((1 - α) / p 1) ^ (1 - α))
          = (t⁻¹ ^ α * t⁻¹ ^ (1 - α)) * ((α / p 0) ^ α * ((1 - α) / p 1) ^ (1 - α)) := by ring
        _ = _ := by rw [this]
    rw [cdExpenditure, cdExpenditure, hC]
    have := cdConst_pos hα0 hα1 hp
    field_simp
  · exact div_lt_div_of_pos_right hlt (cdConst_pos hα0 hα1 hp)
  · have hp' : StrictlyPositive p' := fun l => (hp l).trans_le (hpp l)
    rw [← (example_3_E_1 hα0 hα1 hp hub).1, ← (example_3_E_1 hα0 hα1 hp' hub).1]
    exact proposition_3_E_2_ii_prices _ hp hpp ub
  · refine (proposition_3_E_2_iii (cobbDouglasUtility 1 α) ub).congr fun p hp => ?_
    exact (example_3_E_1 hα0 hα1 hp hub).1
  · have h1 := (example_3_E_1 hα0 hα1 (hpos p t hp ht) hub).2
    have h2 := (example_3_E_1 hα0 hα1 hp hub).2
    rw [proposition_3_E_3_i _ p ub ht, h2] at h1
    exact (Set.singleton_eq_singleton_iff.mp h1).symm
  · have hmem : cdHicksian α p ub ∈ hicksianDemand (cobbDouglasUtility 1 α) p ub := by
      rw [(example_3_E_1 hα0 hα1 hp hub).2]; exact Set.mem_singleton _
    have h0 : cobbDouglasUtility 1 α 0 = 0 := by
      simp [cobbDouglasUtility, Real.zero_rpow hα0.ne', Real.zero_rpow (by linarith : 1 - α ≠ 0)]
    exact proposition_3_E_3_ii hcont hp (by rw [h0]; exact hub.le) hmem

end MWG.ClassicalDemand
