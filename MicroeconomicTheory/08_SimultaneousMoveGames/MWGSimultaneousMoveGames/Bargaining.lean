/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.ExercisesCF

/-!
# Exercise 8.D.4: simultaneous demands

MWG, Exercise 8.D.4, p. 263. Two individuals simultaneously demand amounts `d₁, d₂ ≥ 0` of 100
dollars; if `d₁ + d₂ ≤ 100` each gets his demand, otherwise both get nothing.

* (a) no strategy is strictly dominated (`exercise_8_D_4a`);
* (b) the weakly dominated strategies are exactly `d = 0` and `d > 100`
  (`exercise_8_D_4b`);
* (c) the pure Nash equilibria are the profiles with `d₁ + d₂ = 100` and those with both demands
  at least `100` (`exercise_8_D_4c`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function

/-- **Exercise 8.D.4** (MWG, p. 263). The demand game. -/
noncomputable def demandGame : NormalForm (Fin 2) (fun _ => Effort) where
  payoff i d := if (d 0 : ℝ) + d 1 ≤ 100 then (d i : ℝ) else 0

theorem demand_update (r : Fin 2 → Effort) (i : Fin 2) (x : Effort) :
    demandGame.payoff i (update r i x) =
      if (x : ℝ) + r (1 - i) ≤ 100 then (x : ℝ) else 0 := by
  fin_cases i <;> simp [demandGame, Function.update, add_comm]

/-- An effort level from a nonnegative real. -/
def eff (x : ℝ) (hx : 0 ≤ x := by norm_num) : Effort := ⟨x, hx⟩

/-- **Exercise 8.D.4(a)** (MWG, p. 263). No strategy is strictly dominated: against a demand above
`100` every strategy earns nothing. -/
theorem exercise_8_D_4a (i : Fin 2) (d : Effort) : ¬ StrictlyDominated demandGame i d := by
  rintro ⟨d', h⟩
  have := h (fun _ => eff 200)
  rw [demand_update, demand_update] at this
  simp only [eff] at this
  have h1 : ¬ (d : ℝ) + 200 ≤ 100 := by linarith [d.2]
  have h2 : ¬ (d' : ℝ) + 200 ≤ 100 := by linarith [d'.2]
  simp only [h1, h2, ↓reduceIte, lt_irrefl] at this

/-- **Exercise 8.D.4(b)** (MWG, p. 263). A demand is weakly dominated iff it is `0` or above
`100`. -/
theorem exercise_8_D_4b (i : Fin 2) (d : Effort) :
    WeaklyDominated demandGame i d ↔ (d : ℝ) = 0 ∨ 100 < (d : ℝ) := by
  constructor
  · rintro ⟨d', hle, r, hr⟩
    by_contra hd
    push Not at hd
    have hpos : 0 < (d : ℝ) := lt_of_le_of_ne d.2 (Ne.symm hd.1)
    rcases lt_trichotomy (d' : ℝ) d with hlt | heq | hgt
    · -- against the demand `0`, `d` earns `d > d'`
      have := hle (fun _ => eff 0)
      rw [demand_update, demand_update] at this
      simp only [eff, add_zero] at this
      have h1 : (d : ℝ) ≤ 100 := hd.2
      have h2 : (d' : ℝ) ≤ 100 := by linarith
      simp only [h1, h2, ↓reduceIte] at this
      linarith
    · have : d' = d := Subtype.ext heq
      rw [this] at hr
      exact lt_irrefl _ hr
    · -- against the demand `100 - d`, `d` earns `d > 0` and `d'` nothing
      have := hle (fun _ => eff (100 - d) (by linarith))
      rw [demand_update, demand_update] at this
      simp only [eff] at this
      have h1 : (d : ℝ) + (100 - d) ≤ 100 := by linarith
      have h2 : ¬ (d' : ℝ) + (100 - d) ≤ 100 := by linarith
      simp only [h1, h2, ↓reduceIte] at this
      linarith
  · rintro (h0 | hbig)
    · refine ⟨eff 50, fun r => ?_, fun _ => eff 0, ?_⟩
      · rw [demand_update, demand_update]
        simp only [eff, h0]
        rw [ite_self]
        exact ite_nonneg (by norm_num) le_rfl
      · rw [demand_update, demand_update]
        simp only [eff, h0]
        norm_num
    · refine ⟨eff 100, fun r => ?_, fun _ => eff 0, ?_⟩
      · rw [demand_update, demand_update]
        simp only [eff]
        have h1 : ¬ (d : ℝ) + r (1 - i) ≤ 100 := by linarith [(r (1 - i)).2]
        simp only [h1, ↓reduceIte]
        exact ite_nonneg (by norm_num) le_rfl
      · rw [demand_update, demand_update]
        simp only [eff]
        have h1 : ¬ (d : ℝ) + 0 ≤ 100 := by linarith
        simp only [h1, ↓reduceIte]
        norm_num

/-- **Exercise 8.D.4(c)** (MWG, p. 263). The pure strategy Nash equilibria are the profiles whose
demands sum to `100` and those in which both demands are at least `100`. -/
theorem exercise_8_D_4c (d : Fin 2 → Effort) :
    IsNashEquilibrium demandGame d ↔
      (d 0 : ℝ) + d 1 = 100 ∨ (100 ≤ (d 0 : ℝ) ∧ 100 ≤ (d 1 : ℝ)) := by
  have hpay : ∀ i, demandGame.payoff i d = if (d 0 : ℝ) + d 1 ≤ 100 then (d i : ℝ) else 0 :=
    fun i => rfl
  have h0 := (d 0).2
  have h1 := (d 1).2
  constructor
  · intro h
    by_contra hno
    push Not at hno
    rcases lt_or_gt_of_ne hno.1 with hlt | hgt
    · -- demands leave money on the table: player 1 asks for the rest
      have := h 0 (eff (100 - d 1) (by linarith))
      rw [demand_update, hpay] at this
      simp only [eff, show (1 : Fin 2) - 0 = 1 from rfl] at this
      have hA : (100 - (d 1 : ℝ)) + d 1 ≤ 100 := by linarith
      simp only [hA, hlt.le, ↓reduceIte] at this
      linarith
    · -- the demands are incompatible: a player whose rival demands less than 100 deviates
      by_cases hd1 : (d 1 : ℝ) < 100
      · have := h 0 (eff (100 - d 1) (by linarith))
        rw [demand_update, hpay] at this
        simp only [eff, show (1 : Fin 2) - 0 = 1 from rfl] at this
        have hA : (100 - (d 1 : ℝ)) + d 1 ≤ 100 := by linarith
        have hB : ¬ (d 0 : ℝ) + d 1 ≤ 100 := by linarith
        simp only [hA, hB, ↓reduceIte] at this
        linarith
      · have hd0 : (d 0 : ℝ) < 100 := by
          by_contra h'
          exact hd1 (hno.2 (not_lt.1 h'))
        have := h 1 (eff (100 - d 0) (by linarith))
        rw [demand_update, hpay] at this
        simp only [eff, show (1 : Fin 2) - 1 = 0 from rfl] at this
        have hA : (100 - (d 0 : ℝ)) + d 0 ≤ 100 := by linarith
        have hB : ¬ (d 0 : ℝ) + d 1 ≤ 100 := by linarith
        simp only [hA, hB, ↓reduceIte] at this
        linarith
  · rintro (hsum | ⟨hb0, hb1⟩) i t
    · rw [demand_update, hpay]
      have hA : (d 0 : ℝ) + d 1 ≤ 100 := hsum.le
      simp only [hA, ↓reduceIte]
      have ht := t.2
      have hsum' : (d i : ℝ) + d (1 - i) = 100 := by
        fin_cases i
        · exact hsum
        · simpa [add_comm] using hsum
      have hdi := (d i).2
      split_ifs <;> linarith
    · rw [demand_update, hpay]
      have hB : ¬ (d 0 : ℝ) + d 1 ≤ 100 := by linarith
      have hother : 100 ≤ (d (1 - i) : ℝ) := by
        fin_cases i
        · exact hb1
        · exact hb0
      have ht := t.2
      simp only [hB, ↓reduceIte]
      split_ifs <;> linarith

end MWG.SimultaneousMoveGames
