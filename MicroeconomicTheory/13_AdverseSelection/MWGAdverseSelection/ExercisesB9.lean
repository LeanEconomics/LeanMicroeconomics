/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ExercisesB7

/-!
# Exercise 13.B.9: positive selection with two types

MWG, Section 13.B, Exercise 13.B.9, p. 474. Two types `θ_H > θ_L ≥ 0`, `Prob(θ = θ_H) = λ`
(`twoPt λ θ_L θ_H`), `r` strictly decreasing. Interventions, budget, Pareto improvement and
constrained Pareto optimality are those of `Constrained.lean`. (`IsParetoImprovement` quantifies
over all of `[θ_L, θ_H]`; the intermediate types have probability zero, and with `r` decreasing
the results below do not depend on them.)

* `exercise_13_B_9_exact`: a full-employment equilibrium (`r(θ_L) ≤ E[θ]`, wage `E[θ]`) is a
  constrained Pareto optimum iff `r(θ_L) ≤ θ_L`. The proof of the hard direction goes through
  Exercise 13.B.7: a Pareto improvement must reduce employment, hence there is one of the form
  `(E[θ], ŵ_u)`, and the budget then gives `ŵ_u ≤ E[θ] - θ_L`. Under the exercise's assumption
  `r(θ_L) > θ_L` the full-employment equilibrium is therefore never constrained optimal.
* `exercise_13_B_9`: the hint's case `E[θ] = r(θ_L)` (types `1`, `3`, `λ = 1/2`,
  `r(θ) = (5 - θ)/2`): the highest-wage equilibrium `w* = 2` is not a constrained Pareto
  optimum; a small unemployment benefit (`ŵ_u = 1/2`) Pareto improves on it.
* `exercise_13_B_9_cpo_instance`: an instance of the other side (`r(θ_L) = θ_L`).
-/

namespace MWG.AdverseSelection

open MeasureTheory

/-- **Exercise 13.B.9** (MWG, p. 474). The two-type distribution: `θ_H` with probability `λ`,
`θ_L` with probability `1 - λ`. -/
noncomputable def twoPt (lam θL θH : ℝ) : Measure ℝ :=
  ENNReal.ofReal lam • Measure.dirac θH + ENNReal.ofReal (1 - lam) • Measure.dirac θL

/-- Integrals against the two-type distribution. -/
theorem integral_twoPt {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (f : ℝ → ℝ) :
    ∫ θ, f θ ∂twoPt lam θL θH = lam * f θH + (1 - lam) * f θL := by
  rw [twoPt, integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (sub_nonneg.2 h1), smul_eq_mul]

/-- The two-type distribution satisfies the standing assumptions. -/
theorem twoPt_typeDist {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hL : 0 ≤ θL)
    (hLH : θL < θH) : TypeDist (twoPt lam θL θH) θL θH where
  nonneg := hL
  lt := hLH
  prob := ⟨by
    simp only [twoPt, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]
    simp⟩
  supp := by
    simp only [twoPt, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
      Measure.dirac_apply' _ measurableSet_Icc.compl]
    simp [hLH.le]

/-- `E[θ] = λ θ_H + (1 - λ) θ_L`. -/
theorem meanType_twoPt {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    meanType (twoPt lam θL θH) = lam * θH + (1 - lam) * θL :=
  integral_twoPt h0 h1 _

/-- The profit of a firm paying `w` in the two-type model. -/
theorem firmProfit_twoPt {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (r : ℝ → ℝ) (w : ℝ) :
    firmProfit (twoPt lam θL θH) r w =
      lam * (acceptSet r w).indicator (fun θ => θ - w) θH +
        (1 - lam) * (acceptSet r w).indicator (fun θ => θ - w) θL :=
  integral_twoPt h0 h1 _

/-- **Exercise 13.B.9** (MWG, p. 474), the exact condition (via Exercise 13.B.7). In the
two-type positive selection model (`r` strictly decreasing), if `r(θ_L) ≤ E[θ]` then
`w* = E[θ]` is a competitive equilibrium wage with full employment, and it is a constrained
Pareto optimum iff `r(θ_L) ≤ θ_L`. -/
theorem exercise_13_B_9_exact {lam θL θH : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hL : 0 ≤ θL)
    (hLH : θL < θH) {r : ℝ → ℝ} (hr : Measurable r) (hanti : StrictAntiOn r (Set.Icc θL θH))
    (hfull : r θL ≤ meanType (twoPt lam θL θH)) :
    meanType (twoPt lam θL θH) ∈ eqWages (twoPt lam θL θH) θL θH r ∧
      (IsConstrainedPO (twoPt lam θL θH) θL θH r (meanType (twoPt lam θL θH)) ↔
        r θL ≤ θL) := by
  have hd := twoPt_typeDist hl0.le hl1.le hL hLH
  have hE := meanType_twoPt (θL := θL) (θH := θH) hl0.le hl1.le
  set E := meanType (twoPt lam θL θH)
  have hLi : θL ∈ Set.Icc θL θH := ⟨le_rfl, hLH.le⟩
  have hHi : θH ∈ Set.Icc θL θH := ⟨hLH.le, le_rfl⟩
  have hrHL : r θH < r θL := hanti hLi hHi hLH
  have hrle : ∀ θ ∈ Set.Icc θL θH, r θ ≤ r θL := fun θ hθ => hanti.antitoneOn hLi hθ hθ.1
  have hIccE : Set.Icc θL θH ⊆ acceptSet r E := fun θ hθ => (hrle θ hθ).trans hfull
  refine ⟨mean_mem_eqWages hd hIccE, ⟨fun hcpo => ?_, fun hLle => ?_⟩⟩
  · -- if `r(θ_L) > θ_L`, a small unemployment benefit Pareto improves
    by_contra hgt
    rw [not_le] at hgt
    set u := min (E - θL) (E - r θH) with hu
    have hu1 : E - r θL < u := lt_min (by linarith) (by linarith)
    have hu2 : u ≤ E - θL := min_le_left _ _
    have hu3 : u ≤ E - r θH := min_le_right _ _
    have hH : θH ∈ acceptSet r (E - u) := by change r θH ≤ E - u; linarith
    have hLn : θL ∉ acceptSet r (E - u) := fun h => by
      have : r θL ≤ E - u := h
      linarith
    refine hcpo E u ?_ ⟨fun θ _ => max_le_max le_rfl (by linarith), θL, hLi, ?_⟩
    · rw [budgetOK_iff hd hr, firmProfit_twoPt hl0.le hl1.le,
        Set.indicator_of_mem hH, Set.indicator_of_notMem hLn, mul_zero, add_zero]
      have h1 : 0 < 1 - lam := by linarith
      nlinarith
    · rw [max_eq_left hfull]
      exact lt_max_of_lt_right (by linarith)
  · intro we wu hb hpi
    by_cases hfI : Set.Icc θL θH ⊆ acceptSet r (we - wu)
    · -- everybody works: nobody can be paid more than `E[θ]`
      have hwu := (budgetOK_iff hd hr).1 hb
      rw [firmProfit_of_full hd hr hfI] at hwu
      obtain ⟨-, θ1, hθ1, hs⟩ := hpi
      rw [exB7_pay_emp (hfI hθ1)] at hs
      linarith [le_max_left E (r θ1)]
    · -- the intervention reduces employment: use Exercise 13.B.7
      rw [Set.not_subset] at hfI
      obtain ⟨θ0, hθ0, hθ0n⟩ := hfI
      have hred : ReducesEmployment θL θH r E we wu :=
        exB7_reduces_of hθ0 (not_le.1 hθ0n) ((hrle θ0 hθ0).trans hfull)
      obtain ⟨u, hu0, hb', ⟨-, θ1, hθ1, hs⟩, hred'⟩ :=
        (exercise_13_B_7_reduce hd hr E).1 ⟨we, wu, hb, hpi, hred⟩
      obtain ⟨θ2, hθ2, h21, -⟩ := exB7_reduces_exists hred'
      have hLn : θL ∉ acceptSet r (E - u) := fun h => by
        have : r θL ≤ E - u := h
        linarith [hrle θ2 hθ2]
      have hP := (budgetOK_iff hd hr).1 hb'
      rw [firmProfit_twoPt hl0.le hl1.le, Set.indicator_of_notMem hLn, mul_zero,
        add_zero] at hP
      have hu : u ≤ E - θL := by
        by_cases hH : θH ∈ acceptSet r (E - u)
        · rw [Set.indicator_of_mem hH] at hP
          have h1 : 0 < 1 - lam := by linarith
          nlinarith
        · rw [Set.indicator_of_notMem hH, mul_zero] at hP
          linarith
      have h1 : u + r θ1 ≤ E := by linarith [hrle θ1 hθ1]
      rw [max_eq_left h1] at hs
      exact absurd hs (not_lt.2 (le_max_left _ _))

/-- **Exercise 13.B.9** (MWG, p. 474). The highest-wage competitive equilibrium need not be a
constrained Pareto optimum. Types `θ_L = 1`, `θ_H = 3`, `λ = 1/2`, `r(θ) = (5 - θ)/2`
(strictly decreasing, `r(θ_H) = 1 < θ_H`, `r(θ_L) = 2 > θ_L`, and `E[θ] = 2 = r(θ_L)` as in the
hint): `w* = 2` is the highest equilibrium wage, and the intervention `(w*, ŵ_u) = (2, 1/2)`
(a small unemployment benefit, which sends `θ_L` home) is budget-feasible and Pareto
improving. -/
theorem exercise_13_B_9 :
    StrictAntiOn (fun θ : ℝ => (5 - θ) / 2) (Set.Icc 1 3) ∧
      (5 - 3) / 2 < (3 : ℝ) ∧ (1 : ℝ) < (5 - 1) / 2 ∧
      meanType (twoPt (1 / 2) 1 3) = (5 - 1) / 2 ∧
      IsGreatest (eqWages (twoPt (1 / 2) 1 3) 1 3 fun θ => (5 - θ) / 2) 2 ∧
      BudgetOK (twoPt (1 / 2) 1 3) (fun θ => (5 - θ) / 2) 2 (1 / 2) ∧
      IsParetoImprovement 1 3 (fun θ => (5 - θ) / 2) 2 2 (1 / 2) ∧
      ¬ IsConstrainedPO (twoPt (1 / 2) 1 3) 1 3 (fun θ => (5 - θ) / 2) 2 := by
  have hanti : StrictAntiOn (fun θ : ℝ => (5 - θ) / 2) (Set.Icc 1 3) :=
    fun a _ b _ hab => by simp only; linarith
  have hmeas : Measurable fun θ : ℝ => (5 - θ) / 2 :=
    (measurable_const.sub measurable_id).div_const 2
  have hd := twoPt_typeDist (lam := 1 / 2) (θL := 1) (θH := 3) (by norm_num) (by norm_num)
    zero_le_one (by norm_num)
  have hE : meanType (twoPt (1 / 2) 1 3) = 2 := by
    rw [meanType_twoPt (by norm_num) (by norm_num)]; norm_num
  have hex := exercise_13_B_9_exact (lam := 1 / 2) (θL := 1) (θH := 3) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) hmeas hanti (by rw [hE]; norm_num)
  rw [hE] at hex
  have hH : (3 : ℝ) ∈ acceptSet (fun θ : ℝ => (5 - θ) / 2) (2 - 1 / 2) := by
    change (5 - 3) / 2 ≤ (2 : ℝ) - 1 / 2; norm_num
  have hLn : (1 : ℝ) ∉ acceptSet (fun θ : ℝ => (5 - θ) / 2) (2 - 1 / 2) := fun h => by
    have : (5 - 1) / 2 ≤ (2 : ℝ) - 1 / 2 := h
    norm_num at this
  refine ⟨hanti, by norm_num, by norm_num, by rw [hE]; norm_num, ⟨hex.1, fun w hw => ?_⟩, ?_,
    ⟨fun θ _ => max_le_max le_rfl (by linarith), 1, ⟨le_rfl, by norm_num⟩, by norm_num⟩,
    fun h => absurd (hex.2.1 h) (by norm_num)⟩
  · by_contra hw2
    rw [not_le] at hw2
    have hsub : Set.Icc (1 : ℝ) 3 ⊆ acceptSet (fun θ : ℝ => (5 - θ) / 2) w := fun θ hθ => by
      change (5 - θ) / 2 ≤ w; linarith [hθ.1]
    rw [mem_eqWages_iff, condMean_of_superset hd hsub, hE] at hw
    linarith
  · rw [budgetOK_iff hd hmeas, firmProfit_twoPt (by norm_num) (by norm_num),
      Set.indicator_of_mem hH, Set.indicator_of_notMem hLn]
    norm_num

/-- **Exercise 13.B.9**, instance of the other side of the exact condition (MWG, p. 474). Types
`1`, `3` equally likely, `r(θ) = (3 - θ)/2` (`r(θ_L) = θ_L = 1`): the full-employment
equilibrium `w* = 2` is a constrained Pareto optimum. -/
theorem exercise_13_B_9_cpo_instance :
    IsConstrainedPO (twoPt (1 / 2) 1 3) 1 3 (fun θ => (3 - θ) / 2) 2 := by
  have hanti : StrictAntiOn (fun θ : ℝ => (3 - θ) / 2) (Set.Icc 1 3) :=
    fun a _ b _ hab => by simp only; linarith
  have hE : meanType (twoPt (1 / 2) 1 3) = 2 := by
    rw [meanType_twoPt (by norm_num) (by norm_num)]; norm_num
  have hex := exercise_13_B_9_exact (lam := 1 / 2) (θL := 1) (θH := 3) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) ((measurable_const.sub measurable_id).div_const 2)
    hanti (by rw [hE]; norm_num)
  rw [hE] at hex
  exact hex.2.2 (by norm_num)

end MWG.AdverseSelection
