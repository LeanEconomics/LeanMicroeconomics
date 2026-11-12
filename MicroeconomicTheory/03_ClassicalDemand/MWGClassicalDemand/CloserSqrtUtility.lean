/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.ExpBasic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Exercise 3.G.15: `u = 2x₁^{1/2} + 4x₂^{1/2}`

MWG, Exercise 3.G.15, p. 101. Write `k(p) = 1/p₁ + 4/p₂`.

* **(a)** `x₁(p, w) = w p₂/(p₁(p₂ + 4p₁))`, `x₂(p, w) = 4w p₁/(p₂(p₂ + 4p₁))` for `p ≫ 0`,
  `w > 0` (`exercise_3_G_15a`). The proof uses the tangent-line inequality for `√·`, with the
  exact remainder `(√b - √a)²/(2√a)`, which also gives uniqueness.
* **(d)** `v(p, w) = 2√(w k(p))` (`exercise_3_G_15d_indirect`), and Roy's identity
  `x_l = -(∂v/∂p_l)/(∂v/∂w)` (`exercise_3_G_15d_roy`).
* **(b)** `h₁(p, u) = u² p₂²/(4(p₂ + 4p₁)²)`, `h₂(p, u) = u² p₁²/(p₂ + 4p₁)²` for `u > 0`
  (`exercise_3_G_15b`).
* **(c)** `e(p, u) = u² p₁p₂/(4(p₂ + 4p₁))` and `∂e/∂p_l = h_l` (`exercise_3_G_15c`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

/-- **Exercise 3.G.15** (MWG, p. 101). The utility `u(x) = 2x₁^{1/2} + 4x₂^{1/2}`. -/
noncomputable def sqUtility (x : Fin 2 → ℝ) : ℝ := 2 * Real.sqrt (x 0) + 4 * Real.sqrt (x 1)

/-- `k(p) = 1/p₁ + 4/p₂`. -/
noncomputable def sqK (p : Fin 2 → ℝ) : ℝ := 1 / p 0 + 4 / p 1

/-- **Exercise 3.G.15(a)** (MWG, p. 101). The demand
`(w p₂/(p₁(p₂ + 4p₁)), 4w p₁/(p₂(p₂ + 4p₁)))`. -/
noncomputable def sqDemand (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  ![w * p 1 / (p 0 * (p 1 + 4 * p 0)), 4 * w * p 0 / (p 1 * (p 1 + 4 * p 0))]

/-- **Exercise 3.G.15(d)** (MWG, p. 101). The indirect utility `2√(w(1/p₁ + 4/p₂))`. -/
noncomputable def sqIndirect (p : Fin 2 → ℝ) (w : ℝ) : ℝ := 2 * Real.sqrt (w * sqK p)

/-- **Exercise 3.G.15(c)** (MWG, p. 101). The expenditure function `u² p₁p₂/(4(p₂ + 4p₁))`. -/
noncomputable def sqExpenditure (p : Fin 2 → ℝ) (u : ℝ) : ℝ :=
  u ^ 2 * p 0 * p 1 / (4 * (p 1 + 4 * p 0))

/-- **Exercise 3.G.15(b)** (MWG, p. 101). The Hicksian demand
`(u² p₂²/(4(p₂ + 4p₁)²), u² p₁²/(p₂ + 4p₁)²)`. -/
noncomputable def sqHicks (p : Fin 2 → ℝ) (u : ℝ) : Fin 2 → ℝ :=
  ![u ^ 2 * p 1 ^ 2 / (4 * (p 1 + 4 * p 0) ^ 2), u ^ 2 * p 0 ^ 2 / (p 1 + 4 * p 0) ^ 2]

/-- The tangent-line inequality for `√·`: for `b ≥ 0`, `2a√b ≤ a² + b`, with equality
only if `b = a²`. -/
theorem sq_tangent {a b : ℝ} (hb : 0 ≤ b) :
    2 * a * Real.sqrt b ≤ a ^ 2 + b ∧ (2 * a * Real.sqrt b = a ^ 2 + b → b = a ^ 2) := by
  have e2 := Real.sq_sqrt hb
  refine ⟨by nlinarith [sq_nonneg (Real.sqrt b - a)], fun h => ?_⟩
  have : (Real.sqrt b - a) ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this
  rw [← e2]
  congr 1
  linarith

/-- `k(p) > 0` for `p ≫ 0`. -/
theorem sqK_pos {p : Fin 2 → ℝ} (hp : StrictlyPositive p) : 0 < sqK p := by
  have h0 := hp 0
  have h1 := hp 1
  unfold sqK
  positivity

/-- The demanded quantities are squares: `x₁ = (s/p₁)²`, `x₂ = (2s/p₂)²` with `s = √(w/k(p))`. -/
theorem sqDemand_eq {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    sqDemand p w 0 = (Real.sqrt (w / sqK p) / p 0) ^ 2 ∧
      sqDemand p w 1 = (2 * Real.sqrt (w / sqK p) / p 1) ^ 2 := by
  have h0 := hp 0
  have h1 := hp 1
  have hk := sqK_pos hp
  have hs := Real.sq_sqrt (div_pos hw hk).le
  constructor
  · rw [div_pow, hs]
    simp only [sqDemand, sqK, Matrix.cons_val_zero]
    field_simp
  · rw [div_pow, mul_pow, hs]
    simp only [sqDemand, sqK, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring

/-- `s k(p) = √(w k(p))` for `s = √(w/k(p))`. -/
theorem sq_s_mul_k {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    Real.sqrt (w / sqK p) * sqK p = Real.sqrt (w * sqK p) := by
  have hk := sqK_pos hp
  have hs0 := Real.sqrt_nonneg (w / sqK p)
  rw [← Real.sqrt_sq (mul_nonneg hs0 hk.le), mul_pow, Real.sq_sqrt (div_pos hw hk).le]
  congr 1
  field_simp

/-- **Exercise 3.G.15(a)** (MWG, p. 101). For `p ≫ 0` and `w > 0` the UMP has the unique solution
`x(p, w) = (w p₂/(p₁(p₂ + 4p₁)), 4w p₁/(p₂(p₂ + 4p₁)))`, and `u(x(p, w)) = 2√(w k(p))`. -/
theorem exercise_3_G_15a {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    walrasianDemand sqUtility p w = {sqDemand p w} ∧ sqUtility (sqDemand p w) = sqIndirect p w := by
  have h0 := hp 0
  have h1 := hp 1
  have hk := sqK_pos hp
  set s := Real.sqrt (w / sqK p) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hw hk)
  obtain ⟨e0, e1⟩ := sqDemand_eq hp hw
  set a := s / p 0 with ha
  set c := 2 * s / p 1 with hc
  have ha0 : 0 < a := div_pos hs h0
  have hc0 : 0 < c := by positivity
  have hp0 : p 0 = s / a := by rw [ha]; field_simp
  have hp1 : p 1 = 2 * s / c := by rw [hc]; field_simp
  have r0 : Real.sqrt (sqDemand p w 0) = a := by rw [e0, Real.sqrt_sq ha0.le]
  have r1 : Real.sqrt (sqDemand p w 1) = c := by rw [e1, Real.sqrt_sq hc0.le]
  have hbud : p ⬝ᵥ sqDemand p w = w := by
    simp only [dotProduct, Fin.sum_univ_two, sqDemand, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
  have hw' : w = s * (a + 2 * c) := by
    rw [← hbud]
    simp only [dotProduct, Fin.sum_univ_two, e0, e1, hp0, hp1]
    field_simp
  have hval : sqUtility (sqDemand p w) = sqIndirect p w := by
    have hak : a + 2 * c = Real.sqrt (w / sqK p) * sqK p := by
      rw [ha, hc, ← hsdef]
      simp only [sqK]
      field_simp
      ring
    simp only [sqUtility, r0, r1, sqIndirect, ← sq_s_mul_k hp hw, ← hak]
    ring
  have key : ∀ y ∈ budgetSet p w, sqUtility y ≤ sqUtility (sqDemand p w) ∧
      (sqUtility y = sqUtility (sqDemand p w) → y = sqDemand p w) := by
    intro y hy
    have hy0 : 0 ≤ y 0 := hy.1 0
    have hy1 : 0 ≤ y 1 := hy.1 1
    have hpy : p 0 * y 0 + p 1 * y 1 ≤ w := by
      simpa [dotProduct, Fin.sum_univ_two] using hy.2
    obtain ⟨t0, q0⟩ := sq_tangent (a := a) hy0
    obtain ⟨t1, q1⟩ := sq_tangent (a := c) hy1
    -- `y₀/a + 2y₁/c ≤ a + 2c`
    have hB : y 0 / a + 2 * y 1 / c ≤ a + 2 * c := by
      have : s * (y 0 / a + 2 * y 1 / c) ≤ s * (a + 2 * c) := by
        rw [← hw']
        have : s * (y 0 / a + 2 * y 1 / c) = p 0 * y 0 + p 1 * y 1 := by
          rw [hp0, hp1]; field_simp
        linarith
      exact le_of_mul_le_mul_left this hs
    have i0 : 2 * Real.sqrt (y 0) ≤ a + y 0 / a := by
      rw [show a + y 0 / a = (a ^ 2 + y 0) / a by field_simp, le_div_iff₀ ha0]
      linarith
    have i1 : 4 * Real.sqrt (y 1) ≤ 2 * c + 2 * y 1 / c := by
      rw [show 2 * c + 2 * y 1 / c = 2 * (c ^ 2 + y 1) / c by field_simp,
        le_div_iff₀ hc0]
      linarith
    have hux : sqUtility (sqDemand p w) = 2 * a + 4 * c := by
      simp only [sqUtility, r0, r1]
    refine ⟨by rw [hux]; unfold sqUtility; linarith, fun heq => ?_⟩
    rw [hux] at heq
    unfold sqUtility at heq
    have j0 : 2 * Real.sqrt (y 0) = a + y 0 / a := by linarith
    have j1 : 4 * Real.sqrt (y 1) = 2 * c + 2 * y 1 / c := by linarith
    have k0 : y 0 = a ^ 2 := q0 (by
      have := congrArg (· * a) j0
      field_simp at this
      linarith)
    have k1 : y 1 = c ^ 2 := q1 (by
      have := congrArg (· * c) j1
      field_simp at this
      linarith)
    funext j
    fin_cases j
    · change y 0 = sqDemand p w 0
      rw [k0, ← r0, Real.sq_sqrt (by rw [e0]; positivity)]
    · change y 1 = sqDemand p w 1
      rw [k1, ← r1, Real.sq_sqrt (by rw [e1]; positivity)]
  have hxB : sqDemand p w ∈ budgetSet p w := by
    refine ⟨fun j => ?_, hbud.le⟩
    fin_cases j
    · change 0 ≤ sqDemand p w 0
      rw [e0]; positivity
    · change 0 ≤ sqDemand p w 1
      rw [e1]; positivity
  refine ⟨?_, hval⟩
  ext y
  rw [mem_walrasianDemand_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hmax⟩
    exact (key y hy).2 (le_antisymm (key y hy).1 (hmax _ hxB))
  · rintro rfl
    exact ⟨hxB, fun y hy => (key y hy).1⟩

/-- **Exercise 3.G.15(d)** (MWG, p. 101). The indirect utility is `v(p, w) = 2√(w(1/p₁ + 4/p₂))`
for `p ≫ 0`, `w > 0`. -/
theorem exercise_3_G_15d_indirect {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : 0 < w) : indirectUtility sqUtility p w = sqIndirect p w := by
  obtain ⟨hdem, hval⟩ := exercise_3_G_15a hp hw
  have hx : sqDemand p w ∈ walrasianDemand sqUtility p w := by rw [hdem]; rfl
  rw [indirectUtility_eq_of_mem hx, hval]

/-- **Exercise 3.G.15(d)** (MWG, p. 101), Roy's identity. With `k = 1/p₁ + 4/p₂`:
`∂v/∂w = k/√(wk)`, `∂v/∂p₁ = -(w/p₁²)/√(wk)`, `∂v/∂p₂ = -(4w/p₂²)/√(wk)`, and
`x_l(p, w) = -(∂v/∂p_l)/(∂v/∂w)` for `l = 1, 2`. -/
theorem exercise_3_G_15d_roy {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun w' => sqIndirect p w') (sqK p / Real.sqrt (w * sqK p)) w ∧
      HasDerivAt (fun t => sqIndirect ![t, p 1] w)
        (-(w / p 0 ^ 2) / Real.sqrt (w * sqK p)) (p 0) ∧
      HasDerivAt (fun t => sqIndirect ![p 0, t] w)
        (-(4 * w / p 1 ^ 2) / Real.sqrt (w * sqK p)) (p 1) ∧
      sqDemand p w 0 = -((-(w / p 0 ^ 2) / Real.sqrt (w * sqK p)) /
        (sqK p / Real.sqrt (w * sqK p))) ∧
      sqDemand p w 1 = -((-(4 * w / p 1 ^ 2) / Real.sqrt (w * sqK p)) /
        (sqK p / Real.sqrt (w * sqK p))) := by
  have h0 := hp 0
  have h1 := hp 1
  have hk := sqK_pos hp
  have hwk : 0 < w * sqK p := mul_pos hw hk
  have hsq : 0 < Real.sqrt (w * sqK p) := Real.sqrt_pos.2 hwk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (((hasDerivAt_id w).mul_const (sqK p)).sqrt hwk.ne').const_mul 2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  · have hf : HasDerivAt (fun t : ℝ => w * (1 / t + 4 / p 1)) (w * (-(1 / p 0 ^ 2))) (p 0) := by
      have := ((hasDerivAt_inv h0.ne').add_const (4 / p 1)).const_mul w
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with t
      simp [one_div]
    have hv : (w * (1 / p 0 + 4 / p 1)) ≠ 0 := by
      have : w * (1 / p 0 + 4 / p 1) = w * sqK p := rfl
      rw [this]; exact hwk.ne'
    have := (hf.sqrt hv).const_mul 2
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have : w * (1 / p 0 + 4 / p 1) = w * sqK p := rfl
      rw [this]
      field_simp
    · filter_upwards with t
      simp [sqIndirect, sqK]
  · have hf : HasDerivAt (fun t : ℝ => w * (1 / p 0 + 4 / t)) (w * (-(4 / p 1 ^ 2))) (p 1) := by
      have := (((hasDerivAt_inv h1.ne').const_mul 4).const_add (1 / p 0)).const_mul w
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with t
      simp [div_eq_mul_inv]
    have hv : (w * (1 / p 0 + 4 / p 1)) ≠ 0 := by
      have : w * (1 / p 0 + 4 / p 1) = w * sqK p := rfl
      rw [this]; exact hwk.ne'
    have := (hf.sqrt hv).const_mul 2
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have : w * (1 / p 0 + 4 / p 1) = w * sqK p := rfl
      rw [this]
      field_simp
    · filter_upwards with t
      simp [sqIndirect, sqK]
  · simp only [sqDemand, sqK, Matrix.cons_val_zero]
    field_simp
  · simp only [sqDemand, sqK, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp

/-- For `y ≥ 0`, `u(y) ≤ v(p, p·y)` (and `u(0) = 0`). -/
theorem sqUtility_le_indirect {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {y : Fin 2 → ℝ}
    (hy : y ∈ nonnegOrthant 2) : sqUtility y ≤ sqIndirect p (p ⬝ᵥ y) := by
  have hpy : 0 ≤ p ⬝ᵥ y := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hy l)
  rcases hpy.lt_or_eq with hpos | hzero
  · obtain ⟨hdem, hval⟩ := exercise_3_G_15a hp hpos
    have hx : sqDemand p (p ⬝ᵥ y) ∈ walrasianDemand sqUtility p (p ⬝ᵥ y) := by rw [hdem]; rfl
    rw [← hval]
    exact hx.2 y ⟨hy, le_rfl⟩
  · have hy0 : y = 0 := by
      have h := hzero.symm
      simp only [dotProduct, Fin.sum_univ_two] at h
      have a0 := mul_nonneg (hp 0).le (hy 0)
      have a1 := mul_nonneg (hp 1).le (hy 1)
      have b0 : p 0 * y 0 = 0 := by linarith
      have b1 : p 1 * y 1 = 0 := by linarith
      funext j
      fin_cases j
      · exact (mul_eq_zero.1 b0).resolve_left (hp 0).ne'
      · exact (mul_eq_zero.1 b1).resolve_left (hp 1).ne'
    rw [← hzero, hy0]
    simp [sqUtility, sqIndirect]

/-- `v(p, e(p, u)) = u` for `u ≥ 0`. -/
theorem sqIndirect_sqExpenditure {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {u : ℝ} (hu : 0 ≤ u) :
    sqIndirect p (sqExpenditure p u) = u := by
  have h0 := hp 0
  have h1 := hp 1
  have : sqExpenditure p u * sqK p = (u / 2) ^ 2 := by
    simp only [sqExpenditure, sqK]
    field_simp
    ring
  rw [sqIndirect, this, Real.sqrt_sq (by positivity)]
  ring

/-- **Exercise 3.G.15(b)** (MWG, p. 101). For `p ≫ 0` and `u > 0` the Hicksian demand is the single
bundle `(u² p₂²/(4(p₂ + 4p₁)²), u² p₁²/(p₂ + 4p₁)²)`. -/
theorem exercise_3_G_15b {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {u : ℝ} (hu : 0 < u) :
    hicksianDemand sqUtility p u = {sqHicks p u} := by
  have h0 := hp 0
  have h1 := hp 1
  have hk := sqK_pos hp
  set W := sqExpenditure p u with hW
  have hW0 : 0 < W := by rw [hW, sqExpenditure]; positivity
  obtain ⟨hdem, hval⟩ := exercise_3_G_15a hp hW0
  have hhx : sqHicks p u = sqDemand p W := by
    funext j
    fin_cases j
    · simp only [sqHicks, sqDemand, hW, sqExpenditure, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero]
      field_simp
    · simp only [sqHicks, sqDemand, hW, sqExpenditure, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
  have hxmem : sqHicks p u ∈ walrasianDemand sqUtility p W := by rw [hhx, hdem]; rfl
  have hxu : sqUtility (sqHicks p u) = u := by
    rw [hhx, hval, hW, sqIndirect_sqExpenditure hp hu.le]
  have hxp : p ⬝ᵥ sqHicks p u = W := by
    have hle := hxmem.1.2
    by_contra hne
    have hlt : p ⬝ᵥ sqHicks p u < W := lt_of_le_of_ne hle hne
    have h1 := sqUtility_le_indirect hp hxmem.1.1
    have hmono : sqIndirect p (p ⬝ᵥ sqHicks p u) < sqIndirect p W := by
      unfold sqIndirect
      have hpy : 0 ≤ p ⬝ᵥ sqHicks p u := Finset.sum_nonneg fun l _ =>
        mul_nonneg (hp l).le (hxmem.1.1 l)
      have := Real.sqrt_lt_sqrt (mul_nonneg hpy hk.le) (mul_lt_mul_of_pos_right hlt hk)
      linarith
    rw [hW, sqIndirect_sqExpenditure hp hu.le] at hmono
    linarith
  have hcheap : ∀ z ∈ nonnegOrthant 2, u ≤ sqUtility z → W ≤ p ⬝ᵥ z := by
    intro z hz hzu
    by_contra hlt
    push Not at hlt
    have h1 := sqUtility_le_indirect hp hz
    have hpz : 0 ≤ p ⬝ᵥ z := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hz l)
    have hmono : sqIndirect p (p ⬝ᵥ z) < sqIndirect p W := by
      unfold sqIndirect
      have := Real.sqrt_lt_sqrt (mul_nonneg hpz hk.le) (mul_lt_mul_of_pos_right hlt hk)
      linarith
    rw [hW, sqIndirect_sqExpenditure hp hu.le] at hmono
    linarith
  ext y
  rw [mem_hicksianDemand_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy0, hyu⟩, hmin⟩
    have hle : p ⬝ᵥ y ≤ W := hxp ▸ hmin _ hxmem.1.1 hxu.ge
    have hy : y ∈ walrasianDemand sqUtility p W :=
      ⟨⟨hy0, hle⟩, fun z hz => (hxmem.2 z hz).trans (by rw [hxu]; exact hyu)⟩
    rw [hdem] at hy
    rw [hhx]
    exact hy
  · rintro rfl
    exact ⟨⟨hxmem.1.1, hxu.ge⟩, fun z hz hzu => hxp ▸ hcheap z hz hzu⟩

/-- **Exercise 3.G.15(c)** (MWG, p. 101). For `u > 0`, `e(p, u) = u² p₁p₂/(4(p₂ + 4p₁))`, and its
price derivatives are the Hicksian demands: `∂e/∂p₁ = h₁(p, u)`, `∂e/∂p₂ = h₂(p, u)`. -/
theorem exercise_3_G_15c {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {u : ℝ} (hu : 0 < u) :
    expenditure sqUtility p u = sqExpenditure p u ∧
      HasDerivAt (fun t => sqExpenditure ![t, p 1] u) (sqHicks p u 0) (p 0) ∧
      HasDerivAt (fun t => sqExpenditure ![p 0, t] u) (sqHicks p u 1) (p 1) := by
  have h0 := hp 0
  have h1 := hp 1
  refine ⟨?_, ?_, ?_⟩
  · have hx : sqHicks p u ∈ hicksianDemand sqUtility p u := by
      rw [exercise_3_G_15b hp hu]; rfl
    rw [expenditure_eq_of_mem hx]
    simp only [dotProduct, Fin.sum_univ_two, sqHicks, sqExpenditure, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
  · have hD : p 1 + 4 * p 0 ≠ 0 := by positivity
    have hnum : HasDerivAt (fun t : ℝ => u ^ 2 * t * p 1) (u ^ 2 * p 1) (p 0) := by
      simpa using ((hasDerivAt_id (p 0)).const_mul (u ^ 2)).mul_const (p 1)
    have hden : HasDerivAt (fun t : ℝ => 4 * (p 1 + 4 * t)) 16 (p 0) := by
      have := (((hasDerivAt_id (p 0)).const_mul 4).const_add (p 1)).const_mul 4
      exact this.congr_deriv (by ring)
    have := hnum.div hden (by positivity)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [sqHicks, Matrix.cons_val_zero]
      field_simp
      ring
    · filter_upwards with t
      simp [sqExpenditure]
  · have hnum : HasDerivAt (fun t : ℝ => u ^ 2 * p 0 * t) (u ^ 2 * p 0) (p 1) := by
      simpa using (hasDerivAt_id (p 1)).const_mul (u ^ 2 * p 0)
    have hden : HasDerivAt (fun t : ℝ => 4 * (t + 4 * p 0)) 4 (p 1) := by
      have := ((hasDerivAt_id (p 1)).add_const (4 * p 0)).const_mul 4
      exact this.congr_deriv (by ring)
    have := hnum.div hden (by positivity)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [sqHicks, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
      ring
    · filter_upwards with t
      simp [sqExpenditure]

end MWG.ClassicalDemand
