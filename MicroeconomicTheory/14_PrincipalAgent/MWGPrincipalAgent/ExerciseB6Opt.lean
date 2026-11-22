/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExercisesB56
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Exercise 14.B.6(b): the optimal scheme when revenues can be reduced

MWG, Exercise 14.B.6(b), p. 508. Finitely many revenue levels `R_0 < ⋯ < R_n` and cost levels
`C_0, …, C_{m-1}` (corrections 7); revenue and cost are independent given effort, with
probabilities `r_e(R)` and `c_e(C)`; the owner implements `e_C`. Because the manager can reduce
revenues, he effectively faces a scheme nondecreasing in `R` (Exercise 14.B.5, `effw`).

* `exercise_14_B_6b_opt`: for every scheme `w(R, C)` nondecreasing in `R` that satisfies the
  participation and incentive constraints for `e_C`, the scheme `ŵ(C)` that pays, at each cost
  level, the certainty equivalent of `w(·, C)` under `r_{e_C}` (independent of `R`) also satisfies
  both constraints and costs no more (Jensen; the monotone likelihood ratio property makes the
  `e_R`-deviation weakly less attractive). With strict risk aversion it is strictly cheaper unless
  `w` already ignores `R` at every cost level of positive probability. So the optimal scheme
  depends on costs only, and solves the problem of part (a) with revenues ignored, with first-order
  condition `1 / v'(w(C)) = γ + μ [1 - f_C(C|e_R)/f_C(C|e_C)]` (`exercise_14_B_6a` with
  `ℓ_R ≡ 1`).
* `exercise_14_B_6b_instance`: a proved instance of the hypotheses.
-/

namespace MWG.PrincipalAgent

open Finset Set

/-- **Exercise 14.B.6(b)** (MWG, p. 508). Revenue-reduction-proof schemes (nondecreasing in `R`)
can be replaced by schemes depending on costs only, without violating the constraints for `e_C`
and without raising the expected wage; strictly so under strict risk aversion if `w` depends on
`R` at some cost level of positive probability. -/
theorem exercise_14_B_6b_opt {n m : ℕ} {v : ℝ → ℝ} (hv : ConcaveOn ℝ univ v)
    (hvc : Continuous v) (hvm : StrictMono v) {rC rR : Fin (n + 1) → ℝ} {cC cR : Fin m → ℝ}
    (hrC : ∀ i, 0 < rC i) (hrR : ∀ i, 0 < rR i) (hrC1 : ∑ i, rC i = 1) (hrR1 : ∑ i, rR i = 1)
    (hcC : ∀ j, 0 ≤ cC j) (hcR : ∀ j, 0 ≤ cR j) (hl : Monotone fun i => rR i / rC i)
    {gC gR ubar : ℝ} {w : Fin (n + 1) → Fin m → ℝ} (hw : ∀ j, Monotone fun i => w i j)
    (hIR : ubar ≤ ∑ i, ∑ j, rC i * cC j * v (w i j) - gC)
    (hIC : ∑ i, ∑ j, rR i * cR j * v (w i j) - gR ≤ ∑ i, ∑ j, rC i * cC j * v (w i j) - gC) :
    ∃ wh : Fin m → ℝ, (∀ j, v (wh j) = ∑ i, rC i * v (w i j)) ∧
      ubar ≤ ∑ j, cC j * v (wh j) - gC ∧
      ∑ j, cR j * v (wh j) - gR ≤ ∑ j, cC j * v (wh j) - gC ∧
      ∑ j, cC j * wh j ≤ ∑ i, ∑ j, rC i * cC j * w i j ∧
      (StrictConcaveOn ℝ univ v → (∃ j0, 0 < cC j0 ∧ ∃ i i', w i j0 ≠ w i' j0) →
        ∑ j, cC j * wh j < ∑ i, ∑ j, rC i * cC j * w i j) := by
  -- the certainty equivalents
  have hex : ∀ j, ∃ x, v x = ∑ i, rC i * v (w i j) := by
    intro j
    have hlo : v (w 0 j) ≤ ∑ i, rC i * v (w i j) := by
      calc v (w 0 j) = ∑ i, rC i * v (w 0 j) := by rw [← sum_mul, hrC1, one_mul]
        _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (hvm.monotone (hw j (Fin.zero_le i))) (hrC i).le
    have hhi : ∑ i, rC i * v (w i j) ≤ v (w (Fin.last n) j) := by
      calc ∑ i, rC i * v (w i j) ≤ ∑ i, rC i * v (w (Fin.last n) j) :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
              (hvm.monotone (hw j (Fin.le_last i))) (hrC i).le
        _ = _ := by rw [← sum_mul, hrC1, one_mul]
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc (hw j (Fin.zero_le (Fin.last n)))
      hvc.continuousOn ⟨hlo, hhi⟩
    exact ⟨x, hx⟩
  choose wh hwh using hex
  -- expected utilities
  have hUC : ∑ i, ∑ j, rC i * cC j * v (w i j) = ∑ j, cC j * v (wh j) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [hwh j, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  have hUR : ∑ j, cR j * v (wh j) ≤ ∑ i, ∑ j, rR i * cR j * v (w i j) := by
    rw [sum_comm]
    refine sum_le_sum fun j _ => ?_
    rw [hwh j]
    have hm := mlrp_expect_mono hrR hrC (by rw [hrR1, hrC1]) hl
      (hvm.monotone.comp (hw j))
    simp only [Function.comp] at hm
    have : ∑ i, rR i * cR j * v (w i j) = cR j * ∑ i, rR i * v (w i j) := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hm (hcR j)
  -- Jensen at each cost level
  have hJ : ∀ j, wh j ≤ ∑ i, rC i * w i j := by
    intro j
    have := hv.le_map_sum (t := univ) (w := rC) (p := fun i => w i j)
      (fun i _ => (hrC i).le) hrC1 (fun i _ => mem_univ _)
    simp only [smul_eq_mul] at this
    rw [← hwh j] at this
    exact hvm.le_iff_le.1 this
  have hcost : ∑ i, ∑ j, rC i * cC j * w i j = ∑ j, cC j * ∑ i, rC i * w i j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  refine ⟨wh, hwh, by linarith, by linarith, ?_, fun hsc ⟨j0, hj0, i, i', hii'⟩ => ?_⟩
  · rw [hcost]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hJ j) (hcC j)
  · rw [hcost]
    refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hJ j) (hcC j))
      ⟨j0, mem_univ _, mul_lt_mul_of_pos_left ?_ hj0⟩
    have := (hsc.lt_map_sum_iff_of_pos (t := univ) (w := rC) (p := fun i => w i j0)
      (fun i _ => hrC i) hrC1 (fun i _ => mem_univ _)).2 ⟨i, mem_univ _, i', mem_univ _, hii'⟩
    simp only [smul_eq_mul] at this
    rw [← hwh j0] at this
    exact hvm.lt_iff_lt.1 this

/-- **Exercise 14.B.6(b), an instance** (MWG, p. 508). Two revenue levels with
`r_{e_C} = (1/2, 1/2)` and `r_{e_R} = (1/4, 3/4)` (monotone likelihood ratio), two cost levels with
`c_{e_C} = (3/4, 1/4)` and `c_{e_R} = (1/4, 3/4)`, `v(w) = w`, `g(e_C) = 1`, `g(e_R) = 0`, `ū = 0`
and the scheme `w(R_i, C_0) = 2 + i/10`, `w(R_i, C_1) = 0`, nondecreasing in revenue: the
hypotheses of `exercise_14_B_6b_opt` hold. -/
theorem exercise_14_B_6b_instance :
    let rC : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    let rR : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let cC : Fin 2 → ℝ := ![3 / 4, 1 / 4]
    let cR : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let w : Fin 2 → Fin 2 → ℝ := fun i j => if j = 0 then 2 + (i : ℝ) / 10 else 0
    (∀ j, Monotone fun i => w i j) ∧ Monotone (fun i => rR i / rC i) ∧
      (0 : ℝ) ≤ ∑ i, ∑ j, rC i * cC j * w i j - 1 ∧
      ∑ i, ∑ j, rR i * cR j * w i j - 0 ≤ ∑ i, ∑ j, rC i * cC j * w i j - 1 := by
  intro rC rR cC cR w
  refine ⟨fun j i i' hii' => ?_, fun i i' hii' => ?_, ?_, ?_⟩
  · simp only [w]
    split_ifs
    · have : (i : ℝ) ≤ i' := by exact_mod_cast hii'
      linarith
    · exact le_rfl
  · fin_cases i <;> fin_cases i' <;> simp_all [rR, rC]
    norm_num
  · simp [Fin.sum_univ_two, rC, cC, w]
    norm_num
  · simp [Fin.sum_univ_two, rC, cC, rR, cR, w]
    norm_num

end MWG.PrincipalAgent
