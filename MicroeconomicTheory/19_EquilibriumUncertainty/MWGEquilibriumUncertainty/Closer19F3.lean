/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.ExercisesFH

/-!
# Exercise 19.F.3: more assets, everybody worse off (MWG p. 728)

* **(a)** A two-consumer, two-good economy with two equally likely states and linear Bernoulli
  utilities (`U19F3`, `omega19F3`). Its spot-market (no-asset, incomplete markets) Radner
  equilibrium (`exercise_19_F_3a_spot`) gives the utilities `(2, 1)`; its Arrow-Debreu (complete
  markets) equilibrium (`exercise_19_F_3a_AD`, also a Radner equilibrium with contingent trade,
  `exercise_19_F_3a_complete_radner`) gives `(3/2, 11/8)`. The sum of utilities is `23/8 < 3`
  (`exercise_19_F_3a`).
* **(b)** The four-state economy (`doubleU19F3`, `double19F3`): states 1, 2 as in (a), states 3, 4
  as in (a) with the roles of the consumers reversed, all equally likely (`exercise_19_F_3b`).
  For an allocation built from an allocation of (a) in the same way, each consumer's utility is
  half the sum of utilities in (a) (`doubleU19F3_double`).
* **(c)** With the single asset `r_A = (-1, -1, 2, 2)` (a transfer of wealth from states 1, 2
  to states 3, 4) the spot allocations of (a) form a Radner equilibrium; adding
  `r_B = (8, -9, 0, 0)` (a transfer between states 1 and 2) and `r_C = (0, 0, 8, -9)` (between
  states 3 and 4), the Arrow-Debreu allocations of (a) form a Radner equilibrium; every
  consumer's utility falls from `3/2` to `23/16` (`exercise_19_F_3c`).

The book speaks of "the" equilibrium; the theorems exhibit the equilibria and compare them
(uniqueness is not claimed). Utilities are linear, so each optimality claim is a linear
programming bound.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-! ## (a): the two-state economy -/

/-- A linear (expected) utility `∑_s ∑_l c_{sl} x_{sl}`; the probabilities are in `c`. -/
def linU {S L : ℕ} (c x : CVec S L) : ℝ := ∑ s, ∑ l, c s l * x s l

/-- Coefficients of Exercise 19.F.3(a), states equally likely: consumer 1 has Bernoulli utility
`x₁ + x₂/2` in both states; consumer 2 has `(3/4) x₁ + x₂` in state 1 and `(1/4) x₁ + x₂` in
state 2 (each multiplied by the probability `1/2`). -/
noncomputable def coef19F3 : Fin 2 → CVec 2 2 :=
  ![![![1 / 2, 1 / 4], ![1 / 2, 1 / 4]], ![![3 / 8, 1 / 2], ![1 / 8, 1 / 2]]]

/-- The utilities of Exercise 19.F.3(a). -/
noncomputable def U19F3 : Fin 2 → CVec 2 2 → ℝ := fun i => linU (coef19F3 i)

/-- Endowments of Exercise 19.F.3(a): consumer 1 owns one unit of good 2 in each state;
consumer 2 owns `1` unit of good 1 in state 1 and `3` units in state 2. -/
def omega19F3 : Fin 2 → CVec 2 2 := ![![![0, 1], ![0, 1]], ![![1, 0], ![3, 0]]]

/-- Spot prices of the no-asset equilibrium (good 1 is the numeraire in each state). -/
def pSpot19F3 : CVec 2 2 := ![![1, 1], ![1, 3]]

/-- The spot (incomplete markets) allocation: consumer 1 gets all of good 1. -/
def xSpot19F3 : Fin 2 → CVec 2 2 := ![![![1, 0], ![3, 0]], ![![0, 1], ![0, 1]]]

/-- Arrow-Debreu prices of Exercise 19.F.3(a). -/
noncomputable def pAD19F3 : CVec 2 2 := ![![9 / 8, 3 / 2], ![1, 3 / 2]]

/-- The Arrow-Debreu (complete markets) allocation: consumer 2 consumes good 1 in state 1. -/
def xAD19F3 : Fin 2 → CVec 2 2 := ![![![0, 0], ![3, 0]], ![![1, 1], ![0, 1]]]

/-- **Exercise 19.F.3(a)** (MWG, p. 728), incomplete markets: with no assets the spot prices
`(1, 1)` and `(1, 3)` and the allocation `xSpot19F3` form a Radner equilibrium. -/
theorem exercise_19_F_3a_spot :
    IsRadnerEqm (0 : Fin 2) (0 : Matrix (Fin 2) (Fin 0) ℝ) U19F3 omega19F3 Fin.elim0 pSpot19F3
      xSpot19F3 (fun _ => Fin.elim0) := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, by simp, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => k.elim0,
    fun s l => ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;> simp [xSpot19F3]
  · fin_cases i <;> fin_cases s <;> simp [xSpot19F3, omega19F3, pSpot19F3, dotProduct]
  · obtain ⟨hx, -, hb⟩ := hf
    have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    fin_cases i <;>
    · have h0 := hb 0
      have h1 := hb 1
      simp [pSpot19F3, omega19F3, dotProduct, Fin.sum_univ_two] at h0 h1
      simp [U19F3, linU, coef19F3, xSpot19F3, Fin.sum_univ_two]
      linarith
  · simp only [xSpot19F3, Finset.sum_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two,
      Fin.isValue, cons_val_zero, cons_val_one, omega19F3]
    fin_cases s <;> fin_cases l <;> simp

/-- **Exercise 19.F.3(a)** (MWG, p. 728), complete markets: the prices `pAD19F3` and the
allocation `xAD19F3` form an Arrow-Debreu equilibrium. -/
theorem exercise_19_F_3a_AD : IsADEqmU U19F3 omega19F3 xAD19F3 pAD19F3 := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, ?_⟩, fun x' hx hb => ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;> simp [xAD19F3]
  · fin_cases i <;> norm_num [cval, xAD19F3, omega19F3, pAD19F3, dotProduct]
  · have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    fin_cases i <;>
    · simp [cval, pAD19F3, omega19F3, dotProduct, Fin.sum_univ_two] at hb
      simp [U19F3, linU, coef19F3, xAD19F3, Fin.sum_univ_two]
      linarith
  · funext s l
    simp only [xAD19F3, Finset.sum_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two,
        Fin.isValue, cons_val_zero, cons_val_one, omega19F3]
    fin_cases s <;> fin_cases l <;> simp

/-- **Exercise 19.F.3(a)** (MWG, p. 728), complete markets as a Radner equilibrium: with trade in
the contingent commodities `(good 1, s)` at prices `q_s = p_{1s}` (Proposition 19.D.1(i)). -/
theorem exercise_19_F_3a_complete_radner :
    IsRadnerEqmD (0 : Fin 2) U19F3 omega19F3 (fun s => pAD19F3 s 0) pAD19F3 xAD19F3
      (fun i s => pAD19F3 s ⬝ᵥ (xAD19F3 i s - omega19F3 i s) / pAD19F3 s 0) :=
  proposition_19_D_1_i 0 (fun s => by fin_cases s <;> simp [pAD19F3]) exercise_19_F_3a_AD

/-- **Exercise 19.F.3(a)** (MWG, p. 728). The utilities are `(2, 1)` at the spot (incomplete
markets) equilibrium and `(3/2, 11/8)` at the Arrow-Debreu (complete markets) equilibrium: the sum
of utilities with complete markets, `23/8`, is smaller than with incomplete markets, `3`. -/
theorem exercise_19_F_3a :
    U19F3 0 (xSpot19F3 0) = 2 ∧ U19F3 1 (xSpot19F3 1) = 1 ∧
      U19F3 0 (xAD19F3 0) = 3 / 2 ∧ U19F3 1 (xAD19F3 1) = 11 / 8 ∧
      U19F3 0 (xAD19F3 0) + U19F3 1 (xAD19F3 1) <
        U19F3 0 (xSpot19F3 0) + U19F3 1 (xSpot19F3 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [U19F3, linU, coef19F3, xSpot19F3, xAD19F3, Fin.sum_univ_two] <;> norm_num

/-! ## (b): the four-state economy -/

/-- States 1, 2 of a four-state contingent vector. -/
def firstHalf19F3 {L : ℕ} (x : CVec 4 L) : CVec 2 L := fun s => x (Fin.castAdd 2 s)

/-- States 3, 4 of a four-state contingent vector. -/
def secondHalf19F3 {L : ℕ} (x : CVec 4 L) : CVec 2 L := fun s => x (Fin.natAdd 2 s)

/-- Exercise 19.F.3(b): from data `y` of the two-state economy (endowments, allocations), the
four-state data in which states 1, 2 are as in (a) and in states 3, 4 the roles of the two
consumers are reversed. -/
def double19F3 {L : ℕ} (y : Fin 2 → CVec 2 L) : Fin 2 → CVec 4 L :=
  ![Fin.append (y 0) (y 1), Fin.append (y 1) (y 0)]

/-- Exercise 19.F.3(b): the utilities of the four-state economy, four equally likely states.
Consumer 1 evaluates states 1, 2 as consumer 1 of (a) and states 3, 4 as consumer 2 of (a), and
vice versa; the factor `1/2` turns the probabilities `1/2` of (a) into `1/4`. -/
noncomputable def doubleU19F3 {L : ℕ} (U : Fin 2 → CVec 2 L → ℝ) : Fin 2 → CVec 4 L → ℝ :=
  ![fun x => (U 0 (firstHalf19F3 x) + U 1 (secondHalf19F3 x)) / 2,
    fun x => (U 1 (firstHalf19F3 x) + U 0 (secondHalf19F3 x)) / 2]

theorem append4_zero {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 0 = a 0 :=
  rfl

theorem append4_one {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 1 = a 1 :=
  rfl

theorem append4_two {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 2 = b 0 :=
  rfl

theorem append4_three {α : Type*} (a b : Fin 2 → α) : (Fin.append a b : Fin 4 → α) 3 = b 1 :=
  rfl

/-- **Exercise 19.F.3(b)** (MWG, p. 728). The four-state economy built from (a): in states 1, 2
each consumer has his own endowment of (a), in states 3, 4 the other consumer's; and each
consumer's utility is the expected utility, with probability `1/4` per state, of the Bernoulli
utilities of his own role of (a) in states 1, 2 and of the other role in states 3, 4. -/
theorem exercise_19_F_3b {L : ℕ} (U : Fin 2 → CVec 2 L → ℝ) (ω : Fin 2 → CVec 2 L) :
    (firstHalf19F3 (double19F3 ω 0) = ω 0 ∧ secondHalf19F3 (double19F3 ω 0) = ω 1 ∧
      firstHalf19F3 (double19F3 ω 1) = ω 1 ∧ secondHalf19F3 (double19F3 ω 1) = ω 0) ∧
    ∀ x, doubleU19F3 U 0 x = (U 0 (firstHalf19F3 x) + U 1 (secondHalf19F3 x)) / 2 ∧
      doubleU19F3 U 1 x = (U 1 (firstHalf19F3 x) + U 0 (secondHalf19F3 x)) / 2 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun x => ⟨rfl, rfl⟩⟩ <;>
    · funext s; fin_cases s <;> rfl

/-- Exercise 19.F.3(b): with the coefficients of (a), the four-state utilities are linear
expected utilities, `1/4` times the Bernoulli coefficients of the role in each state. -/
theorem doubleU19F3_linU (i : Fin 2) (x : CVec 4 2) :
    doubleU19F3 U19F3 i x = linU ((1 / 2 : ℝ) • double19F3 coef19F3 i) x := by
  fin_cases i <;>
  · simp [doubleU19F3, U19F3, linU, Fin.sum_univ_two, Fin.sum_univ_four, firstHalf19F3,
      secondHalf19F3, double19F3, coef19F3, append4_zero, append4_one, append4_two,
      append4_three]
    ring

/-- Exercise 19.F.3(b): for four-state allocations built from an allocation `y` of (a), every
consumer's utility is half the sum of the utilities of `y` in (a). -/
theorem doubleU19F3_double {L : ℕ} (U : Fin 2 → CVec 2 L → ℝ) (y : Fin 2 → CVec 2 L)
    (i : Fin 2) : doubleU19F3 U i (double19F3 y i) = (U 0 (y 0) + U 1 (y 1)) / 2 := by
  have h0 : firstHalf19F3 (double19F3 y 0) = y 0 := by
    funext s; fin_cases s <;> rfl
  have h1 : secondHalf19F3 (double19F3 y 0) = y 1 := by
    funext s; fin_cases s <;> rfl
  have h2 : firstHalf19F3 (double19F3 y 1) = y 1 := by
    funext s; fin_cases s <;> rfl
  have h3 : secondHalf19F3 (double19F3 y 1) = y 0 := by
    funext s; fin_cases s <;> rfl
  fin_cases i
  · change (U 0 (firstHalf19F3 (double19F3 y 0)) + U 1 (secondHalf19F3 (double19F3 y 0))) / 2 = _
    rw [h0, h1]
  · change (U 1 (firstHalf19F3 (double19F3 y 1)) + U 0 (secondHalf19F3 (double19F3 y 1))) / 2 = _
    rw [h2, h3, add_comm]

/-! ## (c): one asset versus three assets -/

/-- Exercise 19.F.3(c): the single asset `r_A = (-1, -1, 2, 2)`, which transfers wealth (in
good 1) from states 1, 2 to states 3, 4. -/
def R1_19F3 : Matrix (Fin 4) (Fin 1) ℝ := Matrix.of ![![-1], ![-1], ![2], ![2]]

/-- Exercise 19.F.3(c): `r_A` together with `r_B = (8, -9, 0, 0)` (a transfer between states 1
and 2) and `r_C = (0, 0, 8, -9)` (a transfer between states 3 and 4). -/
def R3_19F3 : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of ![![-1, 8, 0], ![-1, -9, 0], ![2, 0, 8], ![2, 0, -9]]

/-- Spot prices of the Arrow-Debreu equilibrium of (a), good 1 as numeraire in each state. -/
noncomputable def pADspot19F3 : CVec 2 2 := ![![1, 4 / 3], ![1, 3 / 2]]

/-- Asset trades in the three-asset equilibrium. -/
noncomputable def z3_19F3 : Fin 2 → Fin 3 → ℝ := ![![0, -1 / 6, 1 / 6], ![0, 1 / 6, -1 / 6]]

/-- **Exercise 19.F.3(c)** (MWG, p. 728), the single asset: at asset price `q_A = 1` and the spot
prices of (a) in each half, no asset trade and the spot allocations of (a) (consumer `i`'s role
in each half) form a Radner equilibrium of the four-state economy. -/
theorem exercise_19_F_3c_one :
    IsRadnerEqm (0 : Fin 2) R1_19F3 (doubleU19F3 U19F3) (double19F3 omega19F3) ![1]
      (Fin.append pSpot19F3 pSpot19F3) (double19F3 xSpot19F3) (fun _ _ => 0) := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, by simp, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => by simp,
    fun s l => ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;>
      simp [double19F3, xSpot19F3, append4_zero, append4_one, append4_two, append4_three]
  · fin_cases i <;> fin_cases s <;>
      norm_num [double19F3, xSpot19F3, omega19F3, pSpot19F3, dotProduct, append4_zero,
        append4_one, append4_two, append4_three, Matrix.mulVec]
  · obtain ⟨hx, hq, hb⟩ := hf
    have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    have n20 := hx 2 0; have n21 := hx 2 1; have n30 := hx 3 0; have n31 := hx 3 1
    simp [dotProduct] at hq
    rw [doubleU19F3_linU, doubleU19F3_linU]
    fin_cases i <;>
    · have h0 := hb 0
      have h1 := hb 1
      have h2 := hb 2
      have h3 := hb 3
      simp [pSpot19F3, omega19F3, double19F3, dotProduct, Fin.sum_univ_two, R1_19F3,
        Matrix.mulVec, append4_zero, append4_one, append4_two, append4_three] at h0 h1 h2 h3
      simp [linU, coef19F3, xSpot19F3, double19F3, Fin.sum_univ_two, Fin.sum_univ_four,
        append4_zero, append4_one, append4_two, append4_three]
      linarith
  · fin_cases s <;> fin_cases l <;>
      norm_num [double19F3, xSpot19F3, omega19F3, Fin.sum_univ_two, append4_zero, append4_one,
        append4_two, append4_three]

/-- **Exercise 19.F.3(c)** (MWG, p. 728), three assets: at asset prices `(1, 0, 0)` and the
spot-normalized Arrow-Debreu prices of (a) in each half, the trades `z3_19F3` (only in `r_B`,
`r_C`) and the Arrow-Debreu allocations of (a) form a Radner equilibrium of the four-state
economy. -/
theorem exercise_19_F_3c_three :
    IsRadnerEqm (0 : Fin 2) R3_19F3 (doubleU19F3 U19F3) (double19F3 omega19F3) ![1, 0, 0]
      (Fin.append pADspot19F3 pADspot19F3) (double19F3 xAD19F3) z3_19F3 := by
  refine ⟨fun i => ⟨⟨fun s l => ?_, ?_, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => ?_,
    fun s l => ?_⟩
  · fin_cases i <;> fin_cases s <;> fin_cases l <;>
      simp [double19F3, xAD19F3, append4_zero, append4_one, append4_two, append4_three]
  · fin_cases i <;> simp [z3_19F3, dotProduct, Fin.sum_univ_three]
  · fin_cases i <;> fin_cases s <;>
      norm_num [double19F3, xAD19F3, omega19F3, pADspot19F3, dotProduct, append4_zero,
        append4_one, append4_two, append4_three, R3_19F3, Matrix.mulVec, z3_19F3,
        Fin.sum_univ_three]
  · obtain ⟨hx, hq, hb⟩ := hf
    have n00 := hx 0 0; have n01 := hx 0 1; have n10 := hx 1 0; have n11 := hx 1 1
    have n20 := hx 2 0; have n21 := hx 2 1; have n30 := hx 3 0; have n31 := hx 3 1
    simp [dotProduct, Fin.sum_univ_three] at hq
    rw [doubleU19F3_linU, doubleU19F3_linU]
    fin_cases i <;>
    · have h0 := hb 0
      have h1 := hb 1
      have h2 := hb 2
      have h3 := hb 3
      simp [pADspot19F3, omega19F3, double19F3, dotProduct, Fin.sum_univ_two, R3_19F3,
        Matrix.mulVec, Fin.sum_univ_three, append4_zero, append4_one, append4_two,
        append4_three] at h0 h1 h2 h3
      simp [linU, coef19F3, xAD19F3, double19F3, Fin.sum_univ_two, Fin.sum_univ_four,
        append4_zero, append4_one, append4_two, append4_three]
      linarith
  · fin_cases k <;> norm_num [z3_19F3, Fin.sum_univ_two]
  · fin_cases s <;> fin_cases l <;>
      norm_num [double19F3, xAD19F3, omega19F3, Fin.sum_univ_two, append4_zero, append4_one,
        append4_two, append4_three]

/-- **Exercise 19.F.3(c)** (MWG, p. 728). The single-asset equilibrium is better for every
consumer than the equilibrium after the two new assets are added: each consumer's utility is
`3/2` with one asset and `23/16` with three (half the sums `3` and `23/8` of (a)). -/
theorem exercise_19_F_3c (i : Fin 2) :
    doubleU19F3 U19F3 i (double19F3 xSpot19F3 i) = 3 / 2 ∧
      doubleU19F3 U19F3 i (double19F3 xAD19F3 i) = 23 / 16 ∧
      doubleU19F3 U19F3 i (double19F3 xAD19F3 i) <
        doubleU19F3 U19F3 i (double19F3 xSpot19F3 i) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := exercise_19_F_3a
  rw [doubleU19F3_double, doubleU19F3_double, h1, h2, h3, h4]
  norm_num

end MWG.EquilibriumUncertainty
