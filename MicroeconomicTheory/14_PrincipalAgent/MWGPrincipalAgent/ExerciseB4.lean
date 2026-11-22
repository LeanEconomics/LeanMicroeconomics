/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Exercise 14.B.4

MWG, Exercise 14.B.4, p. 507; Appendix A, pp. 503-504.

Three efforts `e₁, e₂, e₃` (indices `0, 1, 2`), profits `π_H = 10` and `π_L = 0`,
`f(π_H|e) = 2/3, 1/2, 1/3`, `g(e) = 5/3, 8/5, 4/3`, `v(w) = √w`, `ū = 0`. A contract is described
by the manager's utility levels `v_H, v_L ≥ 0` (wages `v_H²`, `v_L²`), as the hint suggests.

* `exercise_14_B_4a`: with observable effort the optimal contract implements `e₁` with the fixed
  wage `25/9`.
* `exercise_14_B_4b`, `exercise_14_B_4b_threshold`: `e₂` cannot be implemented; it can be
  implemented iff `g(e₂) ≤ 3/2`.
* `exercise_14_B_4c`: with unobservable effort the optimal contract implements `e₁` with
  `v_H = 2`, `v_L = 1` (wages `4` and `1`), uniquely.
* `exercise_14_B_4d_obs`, `exercise_14_B_4d_unobs`: with `g(e₁) = √8` and `f(π_H|e₁) = x`, the
  observable optimum implements `e₂` for every `x ∈ (0, 1)`, while for `x ≥ 99/100` every optimal
  unobservable contract implements `e₁`: the effort implemented is higher when effort is not
  observable (the upward distortion of p. 487 and Appendix A, which also features inefficient risk
  bearing).
-/

namespace MWG.PrincipalAgent

/-- The manager's expected utility from effort `i` under utility levels `(v_H, v_L)`. -/
def b4EU (p g : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : ℝ := p i * vH + (1 - p i) * vL - g i

/-- The owner's expected profit when effort `i` is taken under `(v_H, v_L)` (wages `v²`). -/
def b4Profit (p : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : ℝ :=
  10 * p i - (p i * vH ^ 2 + (1 - p i) * vL ^ 2)

/-- A contract specifying effort `i` and acceptable to the manager (observable effort). -/
def b4Obs (p g : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : Prop :=
  0 ≤ vH ∧ 0 ≤ vL ∧ 0 ≤ b4EU p g i vH vL

/-- A contract implementing effort `i` when effort is unobservable. -/
def b4Impl (p g : Fin 3 → ℝ) (i : Fin 3) (vH vL : ℝ) : Prop :=
  b4Obs p g i vH vL ∧ ∀ j, b4EU p g j vH vL ≤ b4EU p g i vH vL

/-- The data of the exercise. -/
noncomputable def b4p : Fin 3 → ℝ := ![2 / 3, 1 / 2, 1 / 3]

noncomputable def b4g : Fin 3 → ℝ := ![5 / 3, 8 / 5, 4 / 3]

/-- Jensen for `v ↦ v²`: the expected wage is at least the square of the expected utility. -/
theorem b4_jensen {q a b : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (q * a + (1 - q) * b) ^ 2 ≤ q * a ^ 2 + (1 - q) * b ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - q)) (sq_nonneg (a - b))]

/-- The observable-effort bound: profit from effort `i` is at most `10 f(π_H|e_i) - g(e_i)²`. -/
theorem b4_obs_bound {p g : Fin 3 → ℝ} {i : Fin 3} (hp0 : 0 ≤ p i) (hp1 : p i ≤ 1)
    (hg : 0 ≤ g i) {vH vL : ℝ} (h : b4Obs p g i vH vL) :
    b4Profit p i vH vL ≤ 10 * p i - g i ^ 2 := by
  have hJ := b4_jensen (a := vH) (b := vL) hp0 hp1
  have hE : g i ≤ p i * vH + (1 - p i) * vL := by have := h.2.2; unfold b4EU at this; linarith
  unfold b4Profit
  nlinarith

/-- **Exercise 14.B.4(a)** (MWG, p. 507). With observable effort the optimal contract specifies
`e₁` and the fixed wage `25/9` (`v = 5/3`), with profit `35/9`. -/
theorem exercise_14_B_4a :
    b4Obs b4p b4g 0 (5 / 3) (5 / 3) ∧ b4Profit b4p 0 (5 / 3) (5 / 3) = 35 / 9 ∧
      ∀ i vH vL, b4Obs b4p b4g i vH vL → b4Profit b4p i vH vL ≤ 35 / 9 := by
  refine ⟨⟨by norm_num, by norm_num, by simp [b4EU, b4p, b4g]; norm_num⟩,
    by simp [b4Profit, b4p]; norm_num, fun i vH vL h => ?_⟩
  have := b4_obs_bound (p := b4p) (g := b4g) (i := i) (by fin_cases i <;> norm_num [b4p])
    (by fin_cases i <;> norm_num [b4p]) (by fin_cases i <;> norm_num [b4g]) h
  fin_cases i <;> simp [b4p, b4g] at this ⊢ <;> linarith

/-- **Exercise 14.B.4(b)** (MWG, p. 507). Whatever the utility levels, the manager strictly
prefers `e₁` or `e₃` to `e₂`: `e₂` cannot be implemented. -/
theorem exercise_14_B_4b (vH vL : ℝ) :
    b4EU b4p b4g 1 vH vL < b4EU b4p b4g 0 vH vL ∨ b4EU b4p b4g 1 vH vL < b4EU b4p b4g 2 vH vL := by
  simp only [b4EU, b4p, b4g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  by_contra h
  rw [not_or, not_lt, not_lt] at h
  linarith [h.1, h.2]

/-- **Exercise 14.B.4(b)**, "for what levels of `g(e₂)` would `e₂` be implementable?" (with
`g(e₂) ≥ 0`): exactly when `g(e₂) ≤ 3/2`. -/
theorem exercise_14_B_4b_threshold {g2 : ℝ} (hg2 : 0 ≤ g2) :
    (∃ vH vL, b4Impl b4p ![5 / 3, g2, 4 / 3] 1 vH vL) ↔ g2 ≤ 3 / 2 := by
  constructor
  · rintro ⟨vH, vL, -, hic⟩
    have h0 := hic 0
    have h2 := hic 2
    simp only [b4EU, b4p, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h2
    linarith
  · intro h
    refine ⟨g2 + 1, g2, ⟨by linarith, hg2, ?_⟩, fun j => ?_⟩
    · simp [b4EU, b4p]; linarith
    · fin_cases j <;> simp [b4EU, b4p] <;> linarith

/-- **Exercise 14.B.4(c)** (MWG, p. 507). With unobservable effort the optimal contract implements
`e₁` with `v_H = 2`, `v_L = 1` (wages `4` and `1`) and profit `11/3`; it is the unique contract
implementing `e₁` at least cost, implementing `e₃` yields at most `14/9`, and `e₂` cannot be
implemented. -/
theorem exercise_14_B_4c :
    b4Impl b4p b4g 0 2 1 ∧ b4Profit b4p 0 2 1 = 11 / 3 ∧
      (∀ vH vL, b4Impl b4p b4g 0 vH vL → b4Profit b4p 0 vH vL ≤ 11 / 3 ∧
        (b4Profit b4p 0 vH vL = 11 / 3 → vH = 2 ∧ vL = 1)) ∧
      (∀ vH vL, b4Impl b4p b4g 2 vH vL → b4Profit b4p 2 vH vL ≤ 14 / 9) ∧
      ∀ vH vL, ¬ b4Impl b4p b4g 1 vH vL := by
  refine ⟨⟨⟨by norm_num, by norm_num, by simp [b4EU, b4p, b4g]; norm_num⟩, fun j => ?_⟩,
    by simp [b4Profit, b4p]; norm_num, fun vH vL h => ?_, fun vH vL h => ?_, fun vH vL h => ?_⟩
  · fin_cases j <;> norm_num [b4EU, b4p, b4g]
  · obtain ⟨⟨-, -, hp⟩, hic⟩ := h
    have h2 := hic 2
    simp only [b4EU, b4p, b4g, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hp h2
    simp only [b4Profit, b4p, Matrix.cons_val_zero]
    constructor
    · nlinarith [sq_nonneg (vH - 2), sq_nonneg (vL - 1)]
    · intro heq
      constructor <;> nlinarith [sq_nonneg (vH - 2), sq_nonneg (vL - 1)]
  · have := b4_obs_bound (p := b4p) (g := b4g) (i := 2) (by norm_num [b4p])
      (by norm_num [b4p]) (by norm_num [b4g]) h.1
    simp [b4p, b4g] at this ⊢; linarith
  · rcases exercise_14_B_4b vH vL with h' | h'
    · linarith [h.2 0]
    · linarith [h.2 2]

/-- The data of part (d): `f(π_H|e₁) = x`, `g(e₁) = √8`. -/
noncomputable def b4pd (x : ℝ) : Fin 3 → ℝ := ![x, 1 / 2, 1 / 3]

noncomputable def b4gd : Fin 3 → ℝ := ![Real.sqrt 8, 8 / 5, 4 / 3]

theorem b4_sqrt8 : Real.sqrt 8 ^ 2 = 8 ∧ 2828 / 1000 < Real.sqrt 8 ∧ Real.sqrt 8 < 2829 / 1000 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num)
  have hp := Real.sqrt_nonneg 8
  refine ⟨h, ?_, ?_⟩ <;> nlinarith

/-- **Exercise 14.B.4(d)**, observable effort (MWG, p. 507). For every `x ∈ (0, 1)` the observable
optimum implements `e₂` with the fixed wage `64/25` (profit `61/25`); every contract specifying
`e₁` or `e₃` earns strictly less. -/
theorem exercise_14_B_4d_obs {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    b4Obs (b4pd x) b4gd 1 (8 / 5) (8 / 5) ∧ b4Profit (b4pd x) 1 (8 / 5) (8 / 5) = 61 / 25 ∧
      ∀ i vH vL, i ≠ 1 → b4Obs (b4pd x) b4gd i vH vL → b4Profit (b4pd x) i vH vL < 61 / 25 := by
  obtain ⟨h8, -, -⟩ := b4_sqrt8
  refine ⟨⟨by norm_num, by norm_num, by norm_num [b4EU, b4pd, b4gd]⟩, by
    simp [b4Profit, b4pd]; norm_num, fun i vH vL hi h => ?_⟩
  have := b4_obs_bound (p := b4pd x) (g := b4gd) (i := i)
    (by fin_cases i <;> norm_num [b4pd, hx0.le])
    (by fin_cases i <;> norm_num [b4pd, hx1.le]) (by fin_cases i <;> norm_num [b4gd]) h
  fin_cases i
  · simp [b4pd, b4gd, h8] at this ⊢; linarith
  · exact absurd rfl hi
  · simp [b4pd, b4gd] at this ⊢; linarith

/-- **Exercise 14.B.4(d)**, unobservable effort (MWG, p. 507). For `x ∈ [99/100, 1)` the contract
`v_H = 13/5 + v_L`, `v_L = √8 - 13x/5` implements `e₁` with profit above `9/5`, while every contract
implementing `e₂` earns at most `9/5` and every contract implementing `e₃` at most `14/9`: every
optimal contract implements `e₁`, a higher effort than the observable optimum `e₂`. -/
theorem exercise_14_B_4d_unobs {x : ℝ} (hx0 : 99 / 100 ≤ x) (hx1 : x < 1) :
    b4Impl (b4pd x) b4gd 0 (Real.sqrt 8 - 13 * x / 5 + 13 / 5) (Real.sqrt 8 - 13 * x / 5) ∧
      9 / 5 < b4Profit (b4pd x) 0 (Real.sqrt 8 - 13 * x / 5 + 13 / 5) (Real.sqrt 8 - 13 * x / 5) ∧
      (∀ vH vL, b4Impl (b4pd x) b4gd 1 vH vL → b4Profit (b4pd x) 1 vH vL ≤ 9 / 5) ∧
      (∀ vH vL, b4Impl (b4pd x) b4gd 2 vH vL → b4Profit (b4pd x) 2 vH vL ≤ 14 / 9) := by
  obtain ⟨h8, hlo, hhi⟩ := b4_sqrt8
  set s := Real.sqrt 8
  refine ⟨⟨⟨by nlinarith, by nlinarith, ?_⟩, fun j => ?_⟩, ?_, fun vH vL h => ?_,
    fun vH vL h => ?_⟩
  · simp only [b4EU, b4pd, b4gd, Matrix.cons_val_zero]; nlinarith
  · fin_cases j <;> simp [b4EU, b4pd, b4gd, s] <;> nlinarith
  · simp only [b4Profit, b4pd, Matrix.cons_val_zero]; nlinarith
  · obtain ⟨⟨-, -, hp⟩, hic⟩ := h
    have h2 := hic 2
    simp [b4EU, b4pd, b4gd] at hp h2
    simp only [b4Profit, b4pd]
    norm_num
    nlinarith [sq_nonneg (vH + vL - 16 / 5), sq_nonneg (vH - vL - 8 / 5)]
  · have := b4_obs_bound (p := b4pd x) (g := b4gd) (i := 2) (by norm_num [b4pd])
      (by norm_num [b4pd]) (by norm_num [b4gd]) h.1
    simp [b4pd, b4gd] at this ⊢; linarith

end MWG.PrincipalAgent
