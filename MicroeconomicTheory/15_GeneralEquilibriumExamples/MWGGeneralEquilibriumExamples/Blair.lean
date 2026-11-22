/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.MultipleEquilibria

/-!
# Blair's CES economy (MWG Exercise 15.B.6, p. 541)

The utilities are CES with exponent `-2`, `u(x) = (A x₁⁻² + B x₂⁻²)^{-1/2}`. We use the form
`x₁x₂ / √(A x₂² + B x₁²)` (`cesNeg2`), which equals it on `ℝ²₊₊` (`cesNeg2_eq`) and is its
continuous extension by `0` to the boundary of `ℝ²₊`.

* `cesNeg2_optimal`: the bundle `x ≫ 0` satisfying the first-order condition `A p₂ x₂³ = B p₁ x₁³`
  and `p·x = w` is the unique utility maximizer on the budget set (the proof is the convexity of
  `s ↦ s⁻²`).
* **Exercise 15.B.6**: with `u₁ = (x₁₁⁻² + (12/37)³ x₂₁⁻²)^{-1/2}`, `ω₁ = (1, 0)`,
  `u₂ = ((12/37)³ x₁₂⁻² + x₂₂⁻²)^{-1/2}`, `ω₂ = (0, 1)`, the Walrasian equilibrium price ratios are
  exactly `p₁/p₂ ∈ {27/64, 1, 64/27}` (`exercise_15_B_6`), with the equilibrium allocations
  given by `blairAlloc`.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- **Exercise 15.B.6** (MWG, p. 541). The CES utility with exponent `-2` and weights `A, B`,
written `x₁x₂/√(A x₂² + B x₁²)`. -/
noncomputable def cesNeg2 (A B : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  x 0 * x 1 / Real.sqrt (A * x 1 ^ 2 + B * x 0 ^ 2)

/-- On `ℝ²₊₊`, `cesNeg2 A B x = (A x₁⁻² + B x₂⁻²)^{-1/2}`. -/
theorem cesNeg2_eq {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : Fin 2 → ℝ} (h0 : 0 < x 0)
    (h1 : 0 < x 1) : cesNeg2 A B x = (A * (x 0 ^ 2)⁻¹ + B * (x 1 ^ 2)⁻¹) ^ (-(1 : ℝ) / 2) := by
  have hS : 0 < A * (x 0 ^ 2)⁻¹ + B * (x 1 ^ 2)⁻¹ := by positivity
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hS.le, ← Real.sqrt_eq_rpow,
    cesNeg2]
  have e : A * x 1 ^ 2 + B * x 0 ^ 2 = (x 0 * x 1) ^ 2 * (A * (x 0 ^ 2)⁻¹ + B * (x 1 ^ 2)⁻¹) := by
    field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- The value of `cesNeg2` on `ℝ²₊₊` through `S(x) = A/x₁² + B/x₂²`: `u = 1/√S`. -/
theorem cesNeg2_eq_inv_sqrt {A B : ℝ} {x : Fin 2 → ℝ} (h0 : 0 < x 0) (h1 : 0 < x 1) :
    cesNeg2 A B x = 1 / Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) := by
  have e : A * x 1 ^ 2 + B * x 0 ^ 2 = (x 0 * x 1) ^ 2 * (A / x 0 ^ 2 + B / x 1 ^ 2) := by
    field_simp
  rw [cesNeg2, e]
  by_cases hS : 0 ≤ A / x 0 ^ 2 + B / x 1 ^ 2
  · rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    by_cases hS0 : Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) = 0
    · rw [hS0]
      simp
    · field_simp
  · rw [not_le] at hS
    rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hS.le),
      Real.sqrt_eq_zero'.2 hS.le]
    simp

/-- The convexity inequality `1/y² ≥ 3/x² - 2y/x³` for `x, y > 0`, strict unless `y = x`. -/
theorem inv_sq_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    3 / x ^ 2 - 2 * y / x ^ 3 ≤ 1 / y ^ 2 ∧ (y ≠ x → 3 / x ^ 2 - 2 * y / x ^ 3 < 1 / y ^ 2) := by
  have key : 1 / y ^ 2 - (3 / x ^ 2 - 2 * y / x ^ 3) =
      (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by
    field_simp
    ring
  constructor
  · have : 0 ≤ (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by positivity
    linarith
  · intro hne
    have h2 : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      positivity
    have : 0 < (x - y) ^ 2 * (x + 2 * y) / (x ^ 3 * y ^ 2) := by positivity
    linarith

/-- **Exercise 15.B.6** (MWG, p. 541), the demand computation. Let `A, B > 0`, `p ≫ 0` and
`x ≫ 0` satisfy the first-order condition `A p₂ x₂³ = B p₁ x₁³`. Then every `y ≫ 0` with
`p·y ≤ p·x` has `A/y₁² + B/y₂² ≥ A/x₁² + B/x₂²`, strictly unless `y = x`. -/
theorem cesNeg2_optimal {A B p0 p1 x0 x1 y0 y1 : ℝ} (hA : 0 < A) (hB : 0 < B) (hp0 : 0 < p0)
    (hx0 : 0 < x0) (hx1 : 0 < x1) (hfoc : A * p1 * x1 ^ 3 = B * p0 * x0 ^ 3)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hb : p0 * y0 + p1 * y1 ≤ p0 * x0 + p1 * x1) :
    A / x0 ^ 2 + B / x1 ^ 2 ≤ A / y0 ^ 2 + B / y1 ^ 2 ∧
      ((y0 ≠ x0 ∨ y1 ≠ x1) → A / x0 ^ 2 + B / x1 ^ 2 < A / y0 ^ 2 + B / y1 ^ 2) := by
  -- the Lagrange multiplier `λ = A/(p₁ x₁³) = B/(p₂ x₂³)`
  set lam := A / (p0 * x0 ^ 3) with hlam
  have hlam1 : B / x1 ^ 3 = lam * p1 := by
    rw [hlam]
    field_simp
    linear_combination (-1 : ℝ) * hfoc
  have hlam0 : A / x0 ^ 3 = lam * p0 := by
    rw [hlam]
    field_simp
  have hlampos : 0 < lam := by positivity
  obtain ⟨t0, s0⟩ := inv_sq_tangent hx0 hy0
  obtain ⟨t1, s1⟩ := inv_sq_tangent hx1 hy1
  have e0 : A / y0 ^ 2 = A * (1 / y0 ^ 2) := by ring
  have e1 : B / y1 ^ 2 = B * (1 / y1 ^ 2) := by ring
  have lin : A * (3 / x0 ^ 2 - 2 * y0 / x0 ^ 3) + B * (3 / x1 ^ 2 - 2 * y1 / x1 ^ 3) =
      3 * (A / x0 ^ 2 + B / x1 ^ 2) - 2 * lam * (p0 * y0 + p1 * y1) := by
    have : A * (2 * y0 / x0 ^ 3) + B * (2 * y1 / x1 ^ 3) = 2 * lam * (p0 * y0 + p1 * y1) := by
      have h1 : A * (2 * y0 / x0 ^ 3) = 2 * y0 * (A / x0 ^ 3) := by ring
      have h2 : B * (2 * y1 / x1 ^ 3) = 2 * y1 * (B / x1 ^ 3) := by ring
      rw [h1, h2, hlam0, hlam1]
      ring
    linear_combination (-1 : ℝ) * this
  have linx : 2 * lam * (p0 * x0 + p1 * x1) = 2 * (A / x0 ^ 2 + B / x1 ^ 2) := by
    have h1 : lam * p0 * x0 = A / x0 ^ 2 := by
      rw [← hlam0]
      field_simp
    have h2 : lam * p1 * x1 = B / x1 ^ 2 := by
      rw [← hlam1]
      field_simp
    linear_combination 2 * h1 + 2 * h2
  have hcost : 2 * lam * (p0 * y0 + p1 * y1) ≤ 2 * lam * (p0 * x0 + p1 * x1) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left t0 hA.le, mul_le_mul_of_nonneg_left t1 hB.le]
  · rintro (h | h)
    · nlinarith [mul_lt_mul_of_pos_left (s0 h) hA, mul_le_mul_of_nonneg_left t1 hB.le]
    · nlinarith [mul_le_mul_of_nonneg_left t0 hA.le, mul_lt_mul_of_pos_left (s1 h) hB]

/-- The demand of a `cesNeg2 A B` consumer at `p ≫ 0` with wealth `p·x`, where `x ≫ 0` satisfies
the first-order condition: exactly `{x}`. -/
theorem cesNeg2_demand {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {p x : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (hx0 : 0 < x 0) (hx1 : 0 < x 1)
    (hfoc : A * p 1 * x 1 ^ 3 = B * p 0 * x 0 ^ 3) :
    walrasianDemand (cesNeg2 A B) p (p ⬝ᵥ x) = {x} := by
  have hux : 0 < cesNeg2 A B x := by
    rw [cesNeg2_eq_inv_sqrt hx0 hx1]
    have : 0 < A / x 0 ^ 2 + B / x 1 ^ 2 := by positivity
    positivity
  have hxb : x ∈ budgetSet p (p ⬝ᵥ x) := ⟨fun l => by fin_cases l; exacts [hx0.le, hx1.le],
    le_rfl⟩
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  -- utility comparison for affordable bundles
  have hcmp : ∀ y ∈ budgetSet p (p ⬝ᵥ x), cesNeg2 A B y ≤ cesNeg2 A B x ∧
      (cesNeg2 A B y = cesNeg2 A B x → y = x) := by
    intro y hy
    have hb : p 0 * y 0 + p 1 * y 1 ≤ p 0 * x 0 + p 1 * x 1 := by
      rw [← hdot, ← hdot]
      exact hy.2
    by_cases hpos : 0 < y 0 ∧ 0 < y 1
    · obtain ⟨h1, h2⟩ := cesNeg2_optimal hA hB (hp 0) hx0 hx1 hfoc hpos.1 hpos.2 hb
      have hSx : 0 < A / x 0 ^ 2 + B / x 1 ^ 2 := by positivity
      rw [cesNeg2_eq_inv_sqrt hx0 hx1, cesNeg2_eq_inv_sqrt hpos.1 hpos.2]
      have hsq : Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) ≤ Real.sqrt (A / y 0 ^ 2 + B / y 1 ^ 2) :=
        Real.sqrt_le_sqrt h1
      have hsx : 0 < Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) := Real.sqrt_pos.2 hSx
      refine ⟨one_div_le_one_div_of_le hsx hsq, fun heq => ?_⟩
      by_contra hne
      have hne' : y 0 ≠ x 0 ∨ y 1 ≠ x 1 := by
        by_contra hall
        simp only [not_or, not_not] at hall
        exact hne (funext fun l => by fin_cases l; exacts [hall.1, hall.2])
      have hlt := Real.sqrt_lt_sqrt hSx.le (h2 hne')
      have : 1 / Real.sqrt (A / y 0 ^ 2 + B / y 1 ^ 2) <
          1 / Real.sqrt (A / x 0 ^ 2 + B / x 1 ^ 2) := one_div_lt_one_div_of_lt hsx hlt
      linarith
    · have hzero : cesNeg2 A B y = 0 := by
        have hy0 := hy.1 0
        have hy1 := hy.1 1
        have : y 0 * y 1 = 0 := by
          by_contra hne
          apply hpos
          rcases mul_ne_zero_iff.1 hne with ⟨a, b⟩
          exact ⟨lt_of_le_of_ne hy0 (Ne.symm a), lt_of_le_of_ne hy1 (Ne.symm b)⟩
        simp [cesNeg2, this]
      rw [hzero]
      exact ⟨hux.le, fun h => absurd h hux.ne⟩
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact (hcmp y hy.1).2 (le_antisymm (hcmp y hy.1).1 (hy.2 x hxb))
  · rintro rfl
    exact ⟨hxb, fun y hy => (hcmp y hy).1⟩

/-- `cesNeg2` with `B > 0` is strictly increasing in `x₁` when `x₂ > 0`. -/
theorem cesNeg2_lt_add0 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : Fin 2 → ℝ} (hx0 : 0 ≤ x 0)
    (hx1 : 0 < x 1) : cesNeg2 A B x < cesNeg2 A B (x + Pi.single 0 1) := by
  have hy0 : 0 < (x + Pi.single 0 1 : Fin 2 → ℝ) 0 := by simp; linarith
  have hy1 : (x + Pi.single 0 1 : Fin 2 → ℝ) 1 = x 1 := by simp
  rw [cesNeg2_eq_inv_sqrt hy0 (by rw [hy1]; exact hx1)]
  rcases eq_or_lt_of_le hx0 with h | h
  · have : cesNeg2 A B x = 0 := by simp [cesNeg2, ← h]
    rw [this]
    have : 0 < A / (x + Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 +
        B / (x + Pi.single 0 1 : Fin 2 → ℝ) 1 ^ 2 := by
      rw [hy1]
      positivity
    positivity
  · rw [cesNeg2_eq_inv_sqrt h hx1, hy1]
    have hlt : A / (x + Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 < A / x 0 ^ 2 := by
      apply div_lt_div_of_pos_left hA (by positivity)
      simp only [Pi.add_apply, Pi.single_eq_same]
      nlinarith
    have hS : 0 < A / (x + Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 + B / x 1 ^ 2 := by positivity
    exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 hS) (Real.sqrt_lt_sqrt hS.le (by linarith))

/-- `cesNeg2` with the weights and goods swapped. -/
theorem cesNeg2_swap (A B : ℝ) (x : Fin 2 → ℝ) :
    cesNeg2 A B x = cesNeg2 B A ![x 1, x 0] := by
  simp [cesNeg2, mul_comm, add_comm]

/-- `cesNeg2` is strictly increasing in `x₂` when `x₁ > 0`. -/
theorem cesNeg2_lt_add1 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : Fin 2 → ℝ} (hx0 : 0 < x 0)
    (hx1 : 0 ≤ x 1) : cesNeg2 A B x < cesNeg2 A B (x + Pi.single 1 1) := by
  rw [cesNeg2_swap A B x, cesNeg2_swap A B (x + Pi.single 1 1)]
  have h := cesNeg2_lt_add0 hB hA (x := ![x 1, x 0]) (by simpa using hx1) (by simpa using hx0)
  convert h using 2
  funext l
  fin_cases l <;> simp

/-- The constant `c = 12/37` of Exercise 15.B.6. -/
noncomputable def blairC : ℝ := 12 / 37

/-- **Exercise 15.B.6** (MWG, p. 541). Blair's economy:
`u₁ = (x₁₁⁻² + c³x₂₁⁻²)^{-1/2}`, `u₂ = (c³x₁₂⁻² + x₂₂⁻²)^{-1/2}` (`c = 12/37`), `ω₁ = (1, 0)`,
`ω₂ = (0, 1)`. -/
noncomputable def blairEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant ![cesNeg2 1 (blairC ^ 3), cesNeg2 (blairC ^ 3) 1] ![![1, 0], ![0, 1]]

/-- The equilibrium allocation of Blair's economy at `p = (t³, 1)`:
consumer 1 gets `(t²/(t² + c), ct³/(t² + c))`, consumer 2 gets `(c/(ct³ + t), t/(ct³ + t)·t/c·c)`
in the form `(c/(t(ct² + 1)), 1/(ct² + 1))`. -/
noncomputable def blairAlloc (t : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![t ^ 2 / (t ^ 2 + blairC), blairC * t ^ 3 / (t ^ 2 + blairC)],
    ![blairC / (t * (blairC * t ^ 2 + 1)), 1 / (blairC * t ^ 2 + 1)]]

/-- Blair's economy: at `p ≫ 0` with `t³ = p₁/p₂`, the demands are the bundles of
`blairAlloc t`. -/
theorem blair_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {t : ℝ} (ht : 0 < t)
    (ht3 : t ^ 3 = p 0 / p 1) :
    blairEconomy.demand 0 p = {blairAlloc t 0} ∧ blairEconomy.demand 1 p = {blairAlloc t 1} := by
  have hc : (0 : ℝ) < blairC := by norm_num [blairC]
  have hp0 := hp 0
  have hp1 := hp 1
  have hq : p 0 = t ^ 3 * p 1 := by rw [ht3]; field_simp
  constructor
  · have hx0 : 0 < blairAlloc t 0 0 := by
      simp only [blairAlloc, Matrix.cons_val_zero]; positivity
    have hx1 : 0 < blairAlloc t 0 1 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]; positivity
    have hw : p ⬝ᵥ blairEconomy.ω 0 = p ⬝ᵥ blairAlloc t 0 := by
      simp only [blairEconomy, ExchangeEconomy.ofOrthant, blairAlloc, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
      ring
    have hfoc : 1 * p 1 * blairAlloc t 0 1 ^ 3 = blairC ^ 3 * p 0 * blairAlloc t 0 0 ^ 3 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
    have := cesNeg2_demand one_pos (pow_pos hc 3) hp hx0 hx1 hfoc
    unfold ExchangeEconomy.demand
    rw [hw]
    exact this
  · have hx0 : 0 < blairAlloc t 1 0 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]; positivity
    have hx1 : 0 < blairAlloc t 1 1 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]; positivity
    have hw : p ⬝ᵥ blairEconomy.ω 1 = p ⬝ᵥ blairAlloc t 1 := by
      simp only [blairEconomy, ExchangeEconomy.ofOrthant, blairAlloc, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
      ring
    have hfoc : blairC ^ 3 * p 1 * blairAlloc t 1 1 ^ 3 = 1 * p 0 * blairAlloc t 1 0 ^ 3 := by
      simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hq]
      field_simp
    have := cesNeg2_demand (pow_pos hc 3) one_pos hp hx0 hx1 hfoc
    unfold ExchangeEconomy.demand
    rw [hw]
    exact this

/-- In Blair's economy no consumer's demand exists unless `p ≫ 0`. -/
theorem blair_demand_empty {p : Fin 2 → ℝ} (hp : ¬ StrictlyPositive p) :
    blairEconomy.demand 0 p = ∅ ∨ blairEconomy.demand 1 p = ∅ := by
  have hc : (0 : ℝ) < blairC := by norm_num [blairC]
  simp only [StrictlyPositive, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  fin_cases l
  · -- consumer 2 can add good 1 for free
    right
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx, hb⟩, hmax⟩
    have hb' : p 0 * x 0 + p 1 * x 1 ≤ p 1 := by
      simpa [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] using hb
    simp at hl
    by_cases hx1 : 0 < x 1
    · have hmem : x + Pi.single 0 1 ∈ budgetSetOn (blairEconomy.X 1) p
          (p ⬝ᵥ blairEconomy.ω 1) := by
        refine ⟨fun j => ?_, ?_⟩
        · fin_cases j
          · simp; linarith [hx 0]
          · simpa using hx 1
        · simp only [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two,
            Pi.add_apply]
          simp
          linarith
      have h1 := hmax _ hmem
      have h2 := cesNeg2_lt_add0 (pow_pos hc 3) one_pos (hx 0) hx1
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith
    · have hx1' : x 1 = 0 := le_antisymm (not_lt.1 hx1) (hx 1)
      have hmem : (![1, 1] : Fin 2 → ℝ) ∈ budgetSetOn (blairEconomy.X 1) p
          (p ⬝ᵥ blairEconomy.ω 1) := by
        refine ⟨fun j => by fin_cases j <;> simp, ?_⟩
        simp [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
        linarith
      have h1 := hmax _ hmem
      have hz : cesNeg2 (blairC ^ 3) 1 x = 0 := by simp [cesNeg2, hx1']
      have hpos : 0 < cesNeg2 (blairC ^ 3) 1 ![1, 1] := by
        rw [cesNeg2_eq_inv_sqrt (by simp) (by simp)]
        have : 0 < blairC ^ 3 / (![1, 1] : Fin 2 → ℝ) 0 ^ 2 + 1 / (![1, 1] : Fin 2 → ℝ) 1 ^ 2 := by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          positivity
        positivity
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith
  · -- consumer 1 can add good 2 for free
    left
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx, hb⟩, hmax⟩
    have hb' : p 0 * x 0 + p 1 * x 1 ≤ p 0 := by
      simpa [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] using hb
    simp at hl
    by_cases hx0 : 0 < x 0
    · have hmem : x + Pi.single 1 1 ∈ budgetSetOn (blairEconomy.X 0) p
          (p ⬝ᵥ blairEconomy.ω 0) := by
        refine ⟨fun j => ?_, ?_⟩
        · fin_cases j
          · simpa using hx 0
          · simp; linarith [hx 1]
        · simp only [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two,
            Pi.add_apply]
          simp
          linarith
      have h1 := hmax _ hmem
      have h2 := cesNeg2_lt_add1 one_pos (pow_pos hc 3) hx0 (hx 1)
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith
    · have hx0' : x 0 = 0 := le_antisymm (not_lt.1 hx0) (hx 0)
      have hmem : (![1, 1] : Fin 2 → ℝ) ∈ budgetSetOn (blairEconomy.X 0) p
          (p ⬝ᵥ blairEconomy.ω 0) := by
        refine ⟨fun j => by fin_cases j <;> simp, ?_⟩
        simp [blairEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
        linarith
      have h1 := hmax _ hmem
      have hz : cesNeg2 1 (blairC ^ 3) x = 0 := by simp [cesNeg2, hx0']
      have hpos : 0 < cesNeg2 1 (blairC ^ 3) ![1, 1] := by
        rw [cesNeg2_eq_inv_sqrt (by simp) (by simp)]
        have : 0 < 1 / (![1, 1] : Fin 2 → ℝ) 0 ^ 2 + blairC ^ 3 / (![1, 1] : Fin 2 → ℝ) 1 ^ 2 := by
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          positivity
        positivity
      simp [blairEconomy, ExchangeEconomy.ofOrthant] at h1
      linarith

/-- The market-clearing equation of Blair's economy, `c t³ - t² + t - c = 0`, factors as
`(t - 1)(3t - 4)(4t - 3)/37 = 0` for `c = 12/37`. -/
theorem blair_factor (t : ℝ) :
    blairC * t ^ 3 - t ^ 2 + t - blairC = (t - 1) * (3 * t - 4) * (4 * t - 3) / 37 := by
  rw [blairC]
  ring

/-- **Exercise 15.B.6** (MWG, p. 541). The Walrasian equilibrium price vectors of Blair's economy
are exactly the `p ≫ 0` with `p₁/p₂ ∈ {1, 64/27, 27/64}`; at `p₁/p₂ = t³` the equilibrium
allocation is `blairAlloc t`. -/
theorem exercise_15_B_6 (p : Fin 2 → ℝ) :
    (∃ x, blairEconomy.IsDemandEqm p x) ↔
      StrictlyPositive p ∧ (p 0 = p 1 ∨ 27 * p 0 = 64 * p 1 ∨ 64 * p 0 = 27 * p 1) := by
  have hc : (0 : ℝ) < blairC := by norm_num [blairC]
  have htot : blairEconomy.totalEndowment = ![1, 1] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, blairEconomy,
      ExchangeEconomy.ofOrthant, Fin.sum_univ_two]
  -- market clearing for good 1 at `t`
  have hclear : ∀ t : ℝ, 0 < t → (blairAlloc t 0 0 + blairAlloc t 1 0 = 1 ↔
      blairC * t ^ 3 - t ^ 2 + t - blairC = 0) := by
    intro t ht
    simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : 0 < t ^ 2 + blairC := by positivity
    have h2 : 0 < t * (blairC * t ^ 2 + 1) := by positivity
    rw [div_add_div _ _ h1.ne' h2.ne', div_eq_one_iff_eq (by positivity)]
    constructor <;> intro h <;> nlinarith [h]
  have hclear2 : ∀ t : ℝ, 0 < t → blairAlloc t 0 0 + blairAlloc t 1 0 = 1 →
      blairAlloc t 0 1 + blairAlloc t 1 1 = 1 := by
    intro t ht h
    have hP := (hclear t ht).1 h
    simp only [blairAlloc, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
    have h1 : 0 < t ^ 2 + blairC := by positivity
    have h2 : 0 < blairC * t ^ 2 + 1 := by positivity
    rw [div_add_div _ _ h1.ne' h2.ne', div_eq_one_iff_eq (by positivity)]
    nlinarith [hP]
  constructor
  · rintro ⟨x, hbox, hd⟩
    have hp : StrictlyPositive p := by
      by_contra hp
      rcases blair_demand_empty hp with h | h
      · have := hd 0; rw [h] at this; exact this
      · have := hd 1; rw [h] at this; exact this
    refine ⟨hp, ?_⟩
    have hq : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    set t := (p 0 / p 1) ^ ((1 : ℝ) / 3) with htdef
    have ht : 0 < t := Real.rpow_pos_of_pos hq _
    have ht3 : t ^ 3 = p 0 / p 1 := by
      rw [htdef, ← Real.rpow_mul_natCast hq.le]
      norm_num
    obtain ⟨hd0, hd1⟩ := blair_demand hp ht ht3
    have hx0 := hd 0
    have hx1 := hd 1
    rw [hd0, Set.mem_singleton_iff] at hx0
    rw [hd1, Set.mem_singleton_iff] at hx1
    have hc1 := congrFun hbox.2 0
    rw [htot, Finset.sum_apply, Fin.sum_univ_two, hx0, hx1] at hc1
    have hP := (hclear t ht).1 hc1
    rw [blair_factor] at hP
    have : (t - 1) * (3 * t - 4) * (4 * t - 3) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · left
        have : t = 1 := by linarith
        rw [this, one_pow, eq_comm, div_eq_one_iff_eq (hp 1).ne'] at ht3
        exact ht3
      · right; left
        have : t = 4 / 3 := by linarith
        rw [this, eq_div_iff (hp 1).ne'] at ht3
        linarith
    · right; right
      have : t = 3 / 4 := by linarith
      rw [this, eq_div_iff (hp 1).ne'] at ht3
      linarith
  · rintro ⟨hp, hrel⟩
    obtain ⟨t, ht, ht3, hP⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 3 = p 0 / p 1 ∧
        blairC * t ^ 3 - t ^ 2 + t - blairC = 0 := by
      rcases hrel with h | h | h
      · refine ⟨1, one_pos, ?_, by rw [blair_factor]; ring⟩
        rw [h, div_self (hp 1).ne', one_pow]
      · refine ⟨4 / 3, by norm_num, ?_, by rw [blair_factor]; ring⟩
        rw [eq_div_iff (hp 1).ne']
        linarith
      · refine ⟨3 / 4, by norm_num, ?_, by rw [blair_factor]; ring⟩
        rw [eq_div_iff (hp 1).ne']
        linarith
    obtain ⟨hd0, hd1⟩ := blair_demand hp ht ht3
    have hc1 := (hclear t ht).2 hP
    have hc2 := hclear2 t ht hc1
    refine ⟨blairAlloc t, ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩⟩
    · fin_cases i
      · exact (hd0 ▸ Set.mem_singleton _ : blairAlloc t 0 ∈ blairEconomy.demand 0 p).1.1
      · exact (hd1 ▸ Set.mem_singleton _ : blairAlloc t 1 ∈ blairEconomy.demand 1 p).1.1
    · rw [htot]
      funext l
      fin_cases l
      · simpa [Fin.sum_univ_two] using hc1
      · simpa [Fin.sum_univ_two] using hc2
    · fin_cases i
      · exact (hd0 ▸ Set.mem_singleton _ : blairAlloc t 0 ∈ blairEconomy.demand 0 p)
      · exact (hd1 ▸ Set.mem_singleton _ : blairAlloc t 1 ∈ blairEconomy.demand 1 p)

end MWG.GeneralEquilibriumExamples
