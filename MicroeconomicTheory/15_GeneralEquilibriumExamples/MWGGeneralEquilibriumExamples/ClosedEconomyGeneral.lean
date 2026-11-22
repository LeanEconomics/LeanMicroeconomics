/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.ClosedEconomy
import MWGGeneralEquilibriumExamples.FactorParetoSet

/-!
# Exercise 15.D.4(b) for a general 2 × 2 model (MWG p. 543)

The closed economy of Exercise 15.D.4 (`IsClosedEqm`, `ClosedEconomy.lean`) with an arbitrary
2 × 2 technology satisfying the standing assumptions and the factor intensity condition (good 1
relatively intensive in factor 1), consumer 1 owning one unit of factor 1 and caring only for
good 2, consumer 2 owning one unit of factor 2 and caring only for good 1.

* **Exercise 15.D.4(b)** (`TwoByTwo.exercise_15_D_4b_general`): any two equilibria with strictly
  positive factor prices have proportional prices and the same outputs and consumptions: there is
  at most one equilibrium. With `w ≫ 0` both goods are produced, consumer 2's budget and the
  clearing of factor 2 give `w₁ z₁₁ = w₂ z₂₂` (the value of factor 1 used in good 1 equals the
  value of factor 2 used in good 2), and along the supported allocations of `z̄ = (1, 1)`
  `ω z₁₁ - z₂₂` is strictly increasing in `ω = w₁/w₂` (`TwoByTwo.ex15D4b_not_relPrice_lt`).
* Departure: equilibria with a zero factor price are not covered (the standing assumptions say
  nothing about `aⱼ(w)` unless `w ≫ 0`); for the Leontief technologies `exercise_15_D_4b` covers
  them as well.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

namespace TwoByTwo

variable {M : TwoByTwo}

/-- **Exercise 15.D.4(b)** (MWG, p. 543). The structure of an equilibrium with `w ≫ 0`: prices
equal unit costs, the outputs `q ≫ 0` employ `z̄ = (1, 1)` fully, consumer 1 spends `w₁` on good 2
and consumer 2 spends `w₂` on good 1, and `w₁ (q₁ a₁₁) = w₂ (q₂ a₂₂)`. -/
theorem ex15D4b_eqm_facts {p w q : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm M (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x)
    (hw : StrictlyPositive w) :
    (∀ j, p j = M.c j w) ∧ M.IsInteriorSupport ![1, 1] w q ∧
      w 0 * (q 0 * M.a 0 w 0) = w 1 * (q 1 * M.a 1 w 1) ∧
      x = ![Pi.single 1 (w 0 / p 1), Pi.single 0 (w 1 / p 0)] := by
  obtain ⟨hp, -, -, -, hqp, -, hb, hx, hg⟩ := h
  have hown : ∀ i, w ⬝ᵥ ex15D4own i = w i := fun i => by
    fin_cases i <;> simp [ex15D4own, Matrix.vecHead, Matrix.vecTail]
  have hx0 := hx 0
  have hx1 := hx 1
  simp only [hown] at hx0 hx1
  rw [onlyGood_demand hp (hw 0).le] at hx0
  rw [onlyGood_demand hp (hw 1).le] at hx1
  have hx0' : x 0 = Pi.single 1 (w 0 / p 1) := hx0
  have hx1' : x 1 = Pi.single 0 (w 1 / p 0) := hx1
  have hq0 : q 0 = w 1 / p 0 := by
    have := hg 0; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hq1 : q 1 = w 0 / p 1 := by
    have := hg 1; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hp0 := hp 0
  have hp1 := hp 1
  have hq0pos : 0 < q 0 := by rw [hq0]; exact div_pos (hw 1) hp0
  have hq1pos : 0 < q 1 := by rw [hq1]; exact div_pos (hw 0) hp1
  have hpc : ∀ j, p j = M.c j w := Fin.forall_fin_two.2 ⟨hqp 0 hq0pos, hqp 1 hq1pos⟩
  have hcl : ∀ l, q 0 * M.a 0 w l + q 1 * M.a 1 w l = 1 := by
    intro l
    have := hb l (hw l)
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at this
    rw [this]
    fin_cases l <;> simp [ex15D4own]
  refine ⟨hpc, ⟨hw, Fin.forall_fin_two.2 ⟨hq0pos, hq1pos⟩, ?_⟩, ?_, ?_⟩
  · funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcl l]
    fin_cases l <;> simp
  · have E1 : p 0 * q 0 = w 1 := by rw [hq0]; field_simp
    have E2 : p 0 = w 0 * M.a 0 w 0 + w 1 * M.a 0 w 1 := by rw [hpc 0, c, dot_two]
    linear_combination -q 0 * E2 + E1 - w 1 * hcl 1
  · funext i
    fin_cases i
    · exact hx0'
    · exact hx1'

/-- **Exercise 15.D.4(b)** (MWG, p. 543), the key step. Under factor intensity, two interior
supported allocations of `z̄ = (1, 1)` both satisfying `w₁ z₁₁ = w₂ z₂₂` cannot have different
relative factor prices: as `ω = w₁/w₂` rises the intensities fall, so `z₁₁ = r₁(1 - r₂)/(r₁ - r₂)`
does not fall and `z₂₂ = (r₁ - 1)/(r₁ - r₂)` does not rise, and `ω z₁₁ - z₂₂` is strictly
increasing. -/
theorem ex15D4b_not_relPrice_lt (hM : M.IsModel) (hFI : M.FactorIntensity)
    {w q w' q' : Fin 2 → ℝ} (hS : M.IsInteriorSupport ![1, 1] w q)
    (hS' : M.IsInteriorSupport ![1, 1] w' q')
    (hb : w 0 * (q 0 * M.a 0 w 0) = w 1 * (q 1 * M.a 1 w 1))
    (hb' : w' 0 * (q' 0 * M.a 0 w' 0) = w' 1 * (q' 1 * M.a 1 w' 1)) :
    ¬ w 0 / w 1 < w' 0 / w' 1 := by
  intro hlt
  have hw := hS.1
  have hw' := hS'.1
  have hint : M.factorRatio 1 w < M.factorRatio 0 w := hFI w hw
  have hint' : M.factorRatio 1 w' < M.factorRatio 0 w' := hFI w' hw'
  have hρ : (![1, 1] : Fin 2 → ℝ) 0 / (![1, 1] : Fin 2 → ℝ) 1 = 1 := by norm_num
  obtain ⟨hb1, hb2⟩ := interiorSupport_between hM hS hint
  obtain ⟨hb1', hb2'⟩ := interiorSupport_between hM hS' hint'
  rw [hρ] at hb1 hb2 hb1' hb2'
  have ha0 := factorRatio_antitone hM 0 hw hw' hlt.le
  have ha1 := factorRatio_antitone hM 1 hw hw' hlt.le
  obtain ⟨eS, eT⟩ := interiorSupport_identities hM hS
  obtain ⟨eS', eT'⟩ := interiorSupport_identities hM hS'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at eS eT eS' eT'
  have hbpos : 0 < M.factorRatio 1 w := div_pos (hM.a_pos 1 w 0 hw) (hM.a_pos 1 w 1 hw)
  have c0 : q 0 * M.a 0 w 0 = M.factorRatio 0 w * (q 0 * M.a 0 w 1) := by
    have := (hM.a_pos 0 w 1 hw).ne'
    unfold factorRatio
    field_simp
  have c0' : q' 0 * M.a 0 w' 0 = M.factorRatio 0 w' * (q' 0 * M.a 0 w' 1) := by
    have := (hM.a_pos 0 w' 1 hw').ne'
    unfold factorRatio
    field_simp
  have hZpos : 0 < q 0 * M.a 0 w 0 := mul_pos (hS.2.1 0) (hM.a_pos 0 w 0 hw)
  rw [c0] at hb
  rw [c0'] at hb'
  rw [c0] at hZpos
  set a := M.factorRatio 0 w
  set b := M.factorRatio 1 w
  set a' := M.factorRatio 0 w'
  set b' := M.factorRatio 1 w'
  set S := q 0 * M.a 0 w 1
  set S' := q' 0 * M.a 0 w' 1
  set T := q 1 * M.a 1 w 1
  set T' := q' 1 * M.a 1 w' 1
  have hP : 0 < (a - b) * (a' - b') * (a' - b) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  -- `z₁₁ = a S` does not fall
  have hZ : a * S ≤ a' * S' := by
    have key : (a' * S' - a * S) * ((a - b) * (a' - b') * (a' - b)) =
        a' * (b - b') * (a' - 1) * (a - b) + (1 - b) * b * (a - a') * (a' - b') := by
      linear_combination (a' * (a - b) * (a' - b)) * eS' - (a * (a' - b') * (a' - b)) * eS
    have hR : 0 ≤ a' * (b - b') * (a' - 1) * (a - b) + (1 - b) * b * (a - a') * (a' - b') := by
      have ha'pos : 0 < a' := by linarith
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg (mul_nonneg ha'pos.le (by linarith)) (by linarith))
          (by linarith)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hbpos.le) (by linarith))
          (by linarith)
    by_contra hc
    rw [not_le] at hc
    have : (a' * S' - a * S) * ((a - b) * (a' - b') * (a' - b)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hP
    linarith
  -- `z₂₂ = T` does not rise
  have hT : T' ≤ T := by
    have key : (T - T') * ((a - b) * (a' - b') * (a' - b)) =
        (a - a') * (1 - b) * (a' - b') + (a' - 1) * (b - b') * (a - b) := by
      linear_combination ((a' - b') * (a' - b)) * eT - ((a - b) * (a' - b)) * eT'
    have hR : 0 ≤ (a - a') * (1 - b) * (a' - b') + (a' - 1) * (b - b') * (a - b) :=
      add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
        (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
    by_contra hc
    rw [not_le] at hc
    have : (T - T') * ((a - b) * (a' - b') * (a' - b)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hP
    linarith
  have hw1 := hw 1
  have hw1' := hw' 1
  have hw0' := hw' 0
  rw [div_lt_div_iff₀ hw1 hw1'] at hlt
  have k1 : w 1 * (w' 0 * (a' * S')) = w 1 * (w' 1 * T') := by rw [hb']
  have k2 : w' 1 * (w 0 * (a * S)) = w' 1 * (w 1 * T) := by rw [hb]
  have k3 : w 1 * w' 1 * T' ≤ w 1 * w' 1 * T := mul_le_mul_of_nonneg_left hT (by positivity)
  have k4 : w 0 * w' 1 * (a * S) < w' 0 * w 1 * (a * S) := mul_lt_mul_of_pos_right hlt hZpos
  have k5 : w' 0 * w 1 * (a * S) ≤ w' 0 * w 1 * (a' * S') :=
    mul_le_mul_of_nonneg_left hZ (by positivity)
  nlinarith

/-- **Exercise 15.D.4(b)** (MWG, p. 543), general technologies. Under the standing assumptions and
the factor intensity condition, with consumer 1 (owner of factor 1) caring only for good 2 and
consumer 2 (owner of factor 2) only for good 1, any two equilibria with strictly positive factor
prices have proportional prices (`w' = t w`, `p' = t p`, `t > 0`), the same outputs and the same
consumptions: there is at most one equilibrium. -/
theorem exercise_15_D_4b_general (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w q p' w' q' : Fin 2 → ℝ} {x x' : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm M (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x)
    (h' : IsClosedEqm M (fun i => onlyGood (![1, 0] i)) ex15D4own p' w' q' x')
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') :
    ∃ t : ℝ, 0 < t ∧ w' = t • w ∧ p' = t • p ∧ q' = q ∧ x' = x := by
  obtain ⟨hpc, hS, hb, hx⟩ := ex15D4b_eqm_facts h hw
  obtain ⟨hpc', hS', hb', hx'⟩ := ex15D4b_eqm_facts h' hw'
  have hω : w 0 / w 1 = w' 0 / w' 1 := by
    rcases lt_trichotomy (w 0 / w 1) (w' 0 / w' 1) with hl | he | hg
    · exact absurd hl (ex15D4b_not_relPrice_lt hM hFI hS hS' hb hb')
    · exact he
    · exact absurd hg (ex15D4b_not_relPrice_lt hM hFI hS' hS hb' hb)
  have ha : ∀ k, M.a k w = M.a k w' := fun k => by
    rw [a_eq_rel hM k hw, a_eq_rel hM k hw', hω]
  have hD : M.a 0 w 0 * M.a 1 w 1 - M.a 1 w 0 * M.a 0 w 1 ≠ 0 :=
    (FactorIntensity.det_pos hM hFI hw).ne'
  have hs : ∑ k, q k • M.a k w = ![1, 1] := by rw [Fin.sum_univ_two]; exact hS.2.2
  have hs' : ∑ k, q' k • M.a k w = ![1, 1] := by
    rw [Fin.sum_univ_two, ha 0, ha 1]
    exact hS'.2.2
  have hc := outputs_cramer (a := fun k => M.a k w) hD hs
  have hc' := outputs_cramer (a := fun k => M.a k w) hD hs'
  have hq : q' = q := by
    funext k
    fin_cases k
    · exact hc'.1.trans hc.1.symm
    · exact hc'.2.trans hc.2.symm
  have hw1 := hw 1
  have hw1' := hw' 1
  set t := w' 1 / w 1 with htd
  have ht : 0 < t := div_pos hw1' hw1
  have hwt : w' = t • w := by
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, htd]
      rw [div_eq_div_iff hw1.ne' hw1'.ne'] at hω
      field_simp
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, htd]
      field_simp
  have hpt : p' = t • p := by
    funext j
    rw [hpc' j, hwt, c_smul hM j hw ht, Pi.smul_apply, smul_eq_mul, hpc j]
  refine ⟨t, ht, hwt, hpt, hq, ?_⟩
  rw [hx, hx', hwt, hpt]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ ht.ne', mul_div_mul_left _ _ ht.ne']

end TwoByTwo

/-- **Exercise 15.D.4(b)** (MWG, p. 543), instance: the general theorem applies to the Cobb-Douglas
technologies of Exercise 15.D.8 (`cdModel`, good 1 intensive in factor 1). -/
theorem exercise_15_D_4b_cdModel {p w q p' w' q' : Fin 2 → ℝ} {x x' : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm cdModel (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x)
    (h' : IsClosedEqm cdModel (fun i => onlyGood (![1, 0] i)) ex15D4own p' w' q' x')
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') :
    ∃ t : ℝ, 0 < t ∧ w' = t • w ∧ p' = t • p ∧ q' = q ∧ x' = x :=
  TwoByTwo.exercise_15_D_4b_general cdModel_isModel cdModel_factorIntensity h h' hw hw'

end MWG.GeneralEquilibriumExamples
