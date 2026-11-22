/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exercise 8.D.5: ice-cream vendors on a boardwalk

MWG, Exercise 8.D.5, pp. 263-264.

Consumers are uniform on the boardwalk `[0, 1]` and buy from the nearest vendor; vendors at the
same location split their customers evenly. A vendor at `x` serves the points closer to `x`
than to any other occupied location: from the midpoint with the nearest occupied location to
its left (or `0`) to the midpoint with the nearest one to its right (or `1`), divided by the
number of vendors at `x`. With one rival at `y` this is `icShare2 x y`; with two rivals at `y`
and `z` it is `icShare3 x y z`. Locations are points of `unitInterval = [0, 1]`.

* **Exercise 8.D.5(a)** (`exercise_8_D_5a`): with two vendors the unique pure strategy Nash
  equilibrium is both vendors at the midpoint `½`.
* **Exercise 8.D.5(b)** (`exercise_8_D_5b`): with three vendors there is no pure strategy Nash
  equilibrium: a vendor who is alone at the far left (right) gains by moving towards his
  neighbour, and if all three share a location, one of them gains by moving away.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function unitInterval

/-- The market share of a vendor at `x` with one rival at `y`. -/
noncomputable def icShare2 (x y : ℝ) : ℝ :=
  ((if x < y then (x + y) / 2 else 1) - (if y < x then (x + y) / 2 else 0)) /
    (1 + if y = x then 1 else 0)

/-- The market share of a vendor at `x` with rivals at `y` and `z`. -/
noncomputable def icShare3 (x y z : ℝ) : ℝ :=
  (min (if x < y then (x + y) / 2 else 1) (if x < z then (x + z) / 2 else 1) -
      max (if y < x then (x + y) / 2 else 0) (if z < x then (x + z) / 2 else 0)) /
    (1 + (if y = x then 1 else 0) + (if z = x then 1 else 0))

/-- **Exercise 8.D.5(a)** (MWG, p. 264). Two ice-cream vendors choose locations in `[0, 1]`. -/
noncomputable def iceCream2 : NormalForm (Fin 2) (fun _ => unitInterval) where
  payoff i r := icShare2 (r i) (r (i + 1))

/-- **Exercise 8.D.5(b)** (MWG, p. 264). Three ice-cream vendors choose locations in `[0, 1]`. -/
noncomputable def iceCream3 : NormalForm (Fin 3) (fun _ => unitInterval) where
  payoff i r := icShare3 (r i) (r (i + 1)) (r (i + 2))

/-- The midpoint of two points of `[0, 1]`. -/
noncomputable def uiMid (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    unitInterval :=
  ⟨(x + y) / 2, ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩⟩

/-! ### Two vendors -/

theorem icShare2_lt {x y : ℝ} (h : x < y) : icShare2 x y = (x + y) / 2 := by
  simp [icShare2, h, not_lt.2 h.le, h.ne']

theorem icShare2_self (x : ℝ) : icShare2 x x = 1 / 2 := by
  simp [icShare2]; norm_num

theorem icShare2_gt {x y : ℝ} (h : y < x) : icShare2 x y = 1 - (x + y) / 2 := by
  simp [icShare2, h, not_lt.2 h.le, h.ne]

theorem iceCream2_update (i : Fin 2) (r : Fin 2 → unitInterval) (x : unitInterval) :
    iceCream2.payoff i (update r i x) = icShare2 x (r (i + 1)) := by
  have hne : i + 1 ≠ i := by fin_cases i <;> decide
  simp only [iceCream2, update_self, update_of_ne hne]

/-- With the rival at `½`, no location does better than `½`. -/
theorem icShare2_le_half (x : ℝ) : icShare2 x (1 / 2) ≤ 1 / 2 := by
  rcases lt_trichotomy x (1 / 2) with h | rfl | h
  · rw [icShare2_lt h]; linarith
  · rw [icShare2_self]
  · rw [icShare2_gt h]; linarith

/-- **Exercise 8.D.5(a)** (MWG, p. 264). With two vendors there is a unique pure strategy Nash
equilibrium, and both vendors locate at the midpoint of the boardwalk. -/
theorem exercise_8_D_5a (r : Fin 2 → unitInterval) :
    IsNashEquilibrium iceCream2 r ↔ (r 0 : ℝ) = 1 / 2 ∧ (r 1 : ℝ) = 1 / 2 := by
  have e0 : ∀ x, iceCream2.payoff 0 (update r 0 x) = icShare2 x (r 1) :=
    fun x => iceCream2_update 0 r x
  have e1 : ∀ x, iceCream2.payoff 1 (update r 1 x) = icShare2 x (r 0) :=
    fun x => iceCream2_update 1 r x
  have p0 : iceCream2.payoff 0 r = icShare2 (r 0) (r 1) := by rw [← e0, update_eq_self]
  have p1 : iceCream2.payoff 1 r = icShare2 (r 1) (r 0) := by rw [← e1, update_eq_self]
  have hu := (r 0).2
  have hw := (r 1).2
  constructor
  · intro h
    have d0 : ∀ x : unitInterval, icShare2 x (r 1) ≤ icShare2 (r 0) (r 1) := fun x => by
      have := h 0 x; rwa [e0, p0] at this
    have d1 : ∀ x : unitInterval, icShare2 x (r 0) ≤ icShare2 (r 1) (r 0) := fun x => by
      have := h 1 x; rwa [e1, p1] at this
    rcases lt_trichotomy (r 0 : ℝ) (r 1) with huw | huw | huw
    · exfalso
      have := d0 (uiMid _ _ hu hw)
      simp only [uiMid] at this
      rw [icShare2_lt huw, icShare2_lt (by linarith)] at this
      linarith
    · have hd := d0 ⟨1 / 2, by norm_num, by norm_num⟩
      simp only at hd
      rw [← huw, icShare2_self] at hd
      by_contra hne
      have hne' : (r 0 : ℝ) ≠ 1 / 2 := fun h' => hne ⟨h', huw ▸ h'⟩
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · rw [icShare2_gt hlt] at hd; linarith
      · rw [icShare2_lt hgt] at hd; linarith
    · exfalso
      have := d1 (uiMid _ _ hw hu)
      simp only [uiMid] at this
      rw [icShare2_lt huw, icShare2_lt (by linarith)] at this
      linarith
  · rintro ⟨h0, h1⟩ i x
    fin_cases i
    · change iceCream2.payoff 0 (update r 0 x) ≤ iceCream2.payoff 0 r
      rw [e0, p0, h0, h1, icShare2_self]
      exact icShare2_le_half _
    · change iceCream2.payoff 1 (update r 1 x) ≤ iceCream2.payoff 1 r
      rw [e1, p1, h0, h1, icShare2_self]
      exact icShare2_le_half _

/-! ### Three vendors -/

theorem icShare3_left {x y z : ℝ} (hxy : x < y) (hxz : x < z) :
    icShare3 x y z = (x + min y z) / 2 := by
  simp only [icShare3, hxy, hxz, not_lt.2 hxy.le, not_lt.2 hxz.le, hxy.ne', hxz.ne',
    ↓reduceIte, max_self, sub_zero, add_zero, div_one]
  rcases le_total y z with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]

theorem icShare3_right {x y z : ℝ} (hyx : y < x) (hzx : z < x) :
    icShare3 x y z = 1 - (x + max y z) / 2 := by
  simp only [icShare3, hyx, hzx, not_lt.2 hyx.le, not_lt.2 hzx.le, hyx.ne, hzx.ne,
    ↓reduceIte, min_self, add_zero, div_one]
  rcases le_total y z with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
  · rw [max_eq_left h, max_eq_left (by linarith)]

theorem icShare3_self (a : ℝ) : icShare3 a a a = 1 / 3 := by
  simp only [icShare3, lt_irrefl, ↓reduceIte, min_self, max_self]
  norm_num

/-- A vendor alone at the far left gains by moving halfway towards the nearest rival. -/
theorem icShare3_leftmost {x y z : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hxy : x < y) (hxz : x < z)
    (h : ∀ x' : unitInterval, icShare3 x' y z ≤ icShare3 x y z) : False := by
  have hm : min y z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_min hy.1 hz.1, (min_le_left _ _).trans hy.2⟩
  have hxm : x < min y z := lt_min hxy hxz
  have := h (uiMid x (min y z) hx hm)
  simp only [uiMid] at this
  rw [icShare3_left hxy hxz, icShare3_left (by linarith [min_le_left y z])
    (by linarith [min_le_right y z])] at this
  linarith

/-- A vendor alone at the far right gains by moving halfway towards the nearest rival. -/
theorem icShare3_rightmost {x y z : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1) (hyx : y < x) (hzx : z < x)
    (h : ∀ x' : unitInterval, icShare3 x' y z ≤ icShare3 x y z) : False := by
  have hm : max y z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hy.1.trans (le_max_left _ _), max_le hy.2 hz.2⟩
  have hxm : max y z < x := max_lt hyx hzx
  have := h (uiMid x (max y z) hx hm)
  simp only [uiMid] at this
  rw [icShare3_right hyx hzx, icShare3_right (by linarith [le_max_left y z])
    (by linarith [le_max_right y z])] at this
  linarith

/-- If all three vendors share a location, one of them gains by moving away. -/
theorem icShare3_together {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ x' : unitInterval, icShare3 x' a a ≤ icShare3 a a a) : False := by
  rw [icShare3_self] at h
  rcases lt_or_ge a (5 / 9) with hlt | hge
  · have := h (uiMid a 1 ha ⟨by norm_num, le_rfl⟩)
    simp only [uiMid] at this
    rw [icShare3_right (by linarith) (by linarith), max_self] at this
    linarith
  · have := h (uiMid a 0 ha ⟨le_rfl, by norm_num⟩)
    simp only [uiMid] at this
    rw [icShare3_left (by linarith) (by linarith), min_self] at this
    linarith

theorem iceCream3_update (i : Fin 3) (r : Fin 3 → unitInterval) (x : unitInterval) :
    iceCream3.payoff i (update r i x) = icShare3 x (r (i + 1)) (r (i + 2)) := by
  have h1 : i + 1 ≠ i := by fin_cases i <;> decide
  have h2 : i + 2 ≠ i := by fin_cases i <;> decide
  simp only [iceCream3, update_self, update_of_ne h1, update_of_ne h2]

/-- **Exercise 8.D.5(b)** (MWG, p. 264). With three vendors no pure strategy Nash equilibrium
exists. -/
theorem exercise_8_D_5b (r : Fin 3 → unitInterval) : ¬ IsNashEquilibrium iceCream3 r := by
  intro h
  have dev : ∀ i : Fin 3, ∀ x : unitInterval,
      icShare3 x (r (i + 1)) (r (i + 2)) ≤ icShare3 (r i) (r (i + 1)) (r (i + 2)) := by
    intro i x
    have := h i x
    rw [iceCream3_update] at this
    exact this
  have d0 := dev 0
  have d1 := dev 1
  have d2 := dev 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at d0 d1 d2
  have m0 := (r 0).2
  have m1 := (r 1).2
  have m2 := (r 2).2
  set x0 : ℝ := (r 0 : ℝ)
  set x1 : ℝ := (r 1 : ℝ)
  set x2 : ℝ := (r 2 : ℝ)
  rcases lt_trichotomy x0 x1 with h01 | h01 | h01 <;>
    rcases lt_trichotomy x0 x2 with h02 | h02 | h02 <;>
    rcases lt_trichotomy x1 x2 with h12 | h12 | h12 <;>
    first
    | exact icShare3_leftmost m0 m1 m2 (by linarith) (by linarith) d0
    | exact icShare3_leftmost m1 m2 m0 (by linarith) (by linarith) d1
    | exact icShare3_leftmost m2 m0 m1 (by linarith) (by linarith) d2
    | exact icShare3_rightmost m0 m1 m2 (by linarith) (by linarith) d0
    | exact icShare3_rightmost m1 m2 m0 (by linarith) (by linarith) d1
    | exact icShare3_rightmost m2 m0 m1 (by linarith) (by linarith) d2
    | (rw [← h01, ← h02] at d0; exact icShare3_together m0 d0)

end MWG.SimultaneousMoveGames
