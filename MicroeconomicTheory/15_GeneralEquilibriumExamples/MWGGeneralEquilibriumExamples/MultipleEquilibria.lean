/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Welfare
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Multiple Walrasian equilibria (MWG Example 15.B.2 and Exercise 15.B.5, pp. 521-522, 541)

The utilities are `u₁ = x₁₁ - x₂₁⁻⁸/8` and `u₂ = -x₁₂⁻⁸/8 + x₂₂`, quasilinear with respect to
different numeraires, and the endowments are `ω₁ = (2, r)`, `ω₂ = (r, 2)` with
`r = 2^{8/9} - 2^{1/9}`. Since `x⁻⁸ → ∞` as `x → 0`, utility is `-∞` on the face where the
non-numeraire good is zero; we model this by the consumption sets
`X₁ = {x : x₁ ≥ 0, x₂ > 0}` and `X₂ = {x : x₁ > 0, x₂ ≥ 0}` (the bundles of `ℝ²₊` with finite
utility).

* `ql8_optimal`: the demand of a consumer with utility `x_n - x_o⁻⁸/8` (prices `p_n, p_o > 0`): the
  unique optimum has `x_o = t` with `p_o t⁹ = p_n`.
* **Exercise 15.B.5**: the offer curves are as printed (`exercise_15_B_5_offerCurves`, with the
  book's `rpow` formulas in `exercise_15_B_5_printed`), they are strictly positive, and the
  equilibrium price ratios are exactly `p₁/p₂ ∈ {1/2, 1, 2}` (`example_15_B_2`): the market
  clearing equation `r t⁹ - t⁸ + t - r = 0` (`t⁹ = p₁/p₂`) has exactly the positive roots
  `1, 2^{1/9}, 2^{-1/9}` (`ex15B2_roots`).
* Consumer 1's demand for good 1 may increase with `p₁` (`example_15_B_2_increasing`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- The key inequality `t⁹ - 9 t s⁸ + 8 s⁹ = (s - t)² ∑_{k=0}^{7} (k+1) s^k t^{7-k} ≥ 0`. -/
theorem ql8_poly (s t : ℝ) : t ^ 9 - 9 * t * s ^ 8 + 8 * s ^ 9 = (s - t) ^ 2 *
    (t ^ 7 + 2 * s * t ^ 6 + 3 * s ^ 2 * t ^ 5 + 4 * s ^ 3 * t ^ 4 + 5 * s ^ 4 * t ^ 3 +
      6 * s ^ 5 * t ^ 2 + 7 * s ^ 6 * t + 8 * s ^ 7) := by
  ring

/-- **Exercise 15.B.5** (MWG, p. 541), the demand computation. A consumer with utility
`x_n - x_o⁻⁸/8` on `{x_n ≥ 0, x_o > 0}`, prices `p_n, p_o > 0` and wealth `w`: if `t > 0` solves the
first-order condition `p_o t⁹ = p_n`, every affordable bundle gives at most the utility of
`((w - p_o t)/p_n, t)`, with equality only at that bundle. -/
theorem ql8_optimal {pn po w t : ℝ} (hpn : 0 < pn) (hpo : 0 < po) (ht : 0 < t)
    (hfoc : po * t ^ 9 = pn) {xn xo : ℝ} (hxo : 0 < xo) (hb : pn * xn + po * xo ≤ w) :
    xn - 1 / (8 * xo ^ 8) ≤ (w - po * t) / pn - 1 / (8 * t ^ 8) ∧
      (xn - 1 / (8 * xo ^ 8) = (w - po * t) / pn - 1 / (8 * t ^ 8) →
        xo = t ∧ xn = (w - po * t) / pn) := by
  have hS : 0 < t ^ 7 + 2 * xo * t ^ 6 + 3 * xo ^ 2 * t ^ 5 + 4 * xo ^ 3 * t ^ 4 +
      5 * xo ^ 4 * t ^ 3 + 6 * xo ^ 5 * t ^ 2 + 7 * xo ^ 6 * t + 8 * xo ^ 7 := by positivity
  have hxn : xn ≤ (w - po * xo) / pn := by
    rw [le_div_iff₀ hpn]
    linarith
  -- the reduced inequality `po (t - xo)/pn ≤ 1/(8 xo⁸) - 1/(8 t⁸)`
  have key : po * (t - xo) / pn ≤ 1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8) := by
    rw [← hfoc]
    have h1 : 0 ≤ t ^ 9 - 9 * t * xo ^ 8 + 8 * xo ^ 9 := by
      rw [ql8_poly]
      positivity
    rw [div_le_iff₀ (by positivity)]
    have e : (1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8)) * (po * t ^ 9) =
        po * (t ^ 9 - t * xo ^ 8) / (8 * xo ^ 8) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hpo.le h1]
  have hsplit : (w - po * xo) / pn - (w - po * t) / pn = po * (t - xo) / pn := by
    field_simp
    ring
  refine ⟨by linarith, fun heq => ?_⟩
  have hxo' : xo = t := by
    by_contra hne
    have h2 : 0 < t ^ 9 - 9 * t * xo ^ 8 + 8 * xo ^ 9 := by
      rw [ql8_poly]
      exact mul_pos (pow_pos (sub_ne_zero.2 hne |> fun h => abs_pos.2 h |>
        fun h => by simpa [sq_abs] using pow_pos h 2) 1 |> fun h => by simpa using h) hS
    have key' : po * (t - xo) / pn < 1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8) := by
      rw [← hfoc, div_lt_iff₀ (by positivity)]
      have e : (1 / (8 * xo ^ 8) - 1 / (8 * t ^ 8)) * (po * t ^ 9) =
          po * (t ^ 9 - t * xo ^ 8) / (8 * xo ^ 8) := by
        field_simp
      rw [e, lt_div_iff₀ (by positivity)]
      nlinarith [mul_pos hpo h2]
    linarith
  refine ⟨hxo', ?_⟩
  subst hxo'
  linarith

/-- The number `a = 2^{1/9}`. -/
noncomputable def ex15B2a : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 9)

/-- **Example 15.B.2** (MWG, p. 521). The number `r = 2^{8/9} - 2^{1/9}`. -/
noncomputable def ex15B2r : ℝ := (2 : ℝ) ^ ((8 : ℝ) / 9) - (2 : ℝ) ^ ((1 : ℝ) / 9)

theorem ex15B2a_pow : ex15B2a ^ 9 = 2 := by
  rw [ex15B2a, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem ex15B2r_eq : ex15B2r = ex15B2a ^ 8 - ex15B2a := by
  rw [ex15B2r, ex15B2a, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem ex15B2a_bounds : 1.08 < ex15B2a ∧ ex15B2a < 1.081 := by
  have h := ex15B2a_pow
  have hpos : 0 < ex15B2a := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · by_contra hle
    rw [not_lt] at hle
    have : ex15B2a ^ 9 ≤ (1.08 : ℝ) ^ 9 := pow_le_pow_left₀ hpos.le hle 9
    norm_num at this
    linarith
  · by_contra hle
    rw [not_lt] at hle
    have : (1.081 : ℝ) ^ 9 ≤ ex15B2a ^ 9 := pow_le_pow_left₀ (by norm_num) hle 9
    norm_num at this
    linarith

/-- **Example 15.B.2** (MWG, p. 521): `r > 0`; in fact `0.769 < r`. -/
theorem ex15B2r_bounds : 0.769 < ex15B2r := by
  rw [ex15B2r_eq]
  obtain ⟨h1, h2⟩ := ex15B2a_bounds
  have h9 := ex15B2a_pow
  have hpos : 0 < ex15B2a := by linarith
  have h8 : ex15B2a ^ 8 = 2 / ex15B2a := by
    rw [eq_div_iff hpos.ne', ← h9]
    ring
  rw [h8, lt_sub_iff_add_lt, lt_div_iff₀ hpos]
  nlinarith

/-- **Example 15.B.2** (MWG, p. 521). The economy: consumption sets `X₁ = {x₁₁ ≥ 0, x₂₁ > 0}`,
`X₂ = {x₁₂ > 0, x₂₂ ≥ 0}`, utilities `x₁₁ - x₂₁⁻⁸/8` and `-x₁₂⁻⁸/8 + x₂₂`, endowments `(2, r)` and
`(r, 2)`. -/
noncomputable def ex15B2Economy : EdgeworthEconomy where
  X := ![{x | 0 ≤ x 0 ∧ 0 < x 1}, {x | 0 < x 0 ∧ 0 ≤ x 1}]
  u := ![fun x => x 0 - 1 / (8 * x 1 ^ 8), fun x => -(1 / (8 * x 0 ^ 8)) + x 1]
  ω := ![![2, ex15B2r], ![ex15B2r, 2]]

/-- The positivity behind `OCᵢ ≫ 0`: `2s⁹ - s + r > 0` for `s ≥ 0`. -/
theorem ex15B2_pos_aux {s : ℝ} (hs : 0 ≤ s) : 0 < 2 * s ^ 9 - s + ex15B2r := by
  have hr := ex15B2r_bounds
  -- the tangent inequality for `s⁹` at `7/10`
  have h := ql8_poly (7 / 10) s
  have hS : 0 ≤ s ^ 7 + 2 * (7 / 10) * s ^ 6 + 3 * (7 / 10) ^ 2 * s ^ 5 +
      4 * (7 / 10) ^ 3 * s ^ 4 + 5 * (7 / 10) ^ 4 * s ^ 3 + 6 * (7 / 10) ^ 5 * s ^ 2 +
      7 * (7 / 10) ^ 6 * s + 8 * (7 / 10 : ℝ) ^ 7 := by positivity
  have h2 : 0 ≤ s ^ 9 - 9 * s * (7 / 10) ^ 8 + 8 * (7 / 10 : ℝ) ^ 9 := by
    rw [h]
    positivity
  norm_num at h2
  nlinarith

/-- The offer curve of consumer 1 at `p ≫ 0`, in terms of `t > 0` with `t⁹ = p₁/p₂`:
`(2 + r/t⁹ - 1/t⁸, t)`. -/
noncomputable def ex15B2OC1 (t : ℝ) : Fin 2 → ℝ :=
  ![2 + ex15B2r / t ^ 9 - 1 / t ^ 8, t]

/-- The offer curve of consumer 2 at `p ≫ 0` (`t⁹ = p₁/p₂`): `(1/t, 2 + r t⁹ - t⁸)`. -/
noncomputable def ex15B2OC2 (t : ℝ) : Fin 2 → ℝ :=
  ![1 / t, 2 + ex15B2r * t ^ 9 - t ^ 8]

/-- **Exercise 15.B.5** (MWG, p. 541). At `p ≫ 0`, with `t > 0` and `t⁹ = p₁/p₂`, consumer 1
demands exactly `(2 + r/t⁹ - 1/t⁸, t)` and consumer 2 exactly `(1/t, 2 + r t⁹ - t⁸)`; both bundles
are strictly positive. -/
theorem exercise_15_B_5_offerCurves {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {t : ℝ}
    (ht : 0 < t) (ht9 : t ^ 9 = p 0 / p 1) :
    ex15B2Economy.demand 0 p = {ex15B2OC1 t} ∧ ex15B2Economy.demand 1 p = {ex15B2OC2 t} ∧
      (∀ l, 0 < ex15B2OC1 t l) ∧ ∀ l, 0 < ex15B2OC2 t l := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hr := ex15B2r_bounds
  have hpos1 : 0 < 2 + ex15B2r / t ^ 9 - 1 / t ^ 8 := by
    have := ex15B2_pos_aux ht.le
    have e : 2 + ex15B2r / t ^ 9 - 1 / t ^ 8 = (2 * t ^ 9 - t + ex15B2r) / t ^ 9 := by
      field_simp
      ring
    rw [e]
    positivity
  have hpos2 : 0 < 2 + ex15B2r * t ^ 9 - t ^ 8 := by
    have := ex15B2_pos_aux (inv_pos.2 ht).le
    have e : 2 + ex15B2r * t ^ 9 - t ^ 8 = (2 * t⁻¹ ^ 9 - t⁻¹ + ex15B2r) * t ^ 9 := by
      field_simp
      ring
    rw [e]
    positivity
  have hfoc1 : p 1 * t ^ 9 = p 0 := by rw [ht9]; field_simp
  have hfoc2 : p 0 * (1 / t) ^ 9 = p 1 := by
    rw [div_pow, one_pow, ht9]
    field_simp
  have hw1 : p ⬝ᵥ ex15B2Economy.ω 0 = 2 * p 0 + ex15B2r * p 1 := by
    simp [ex15B2Economy, dotProduct, Fin.sum_univ_two, mul_comm]
  have hw2 : p ⬝ᵥ ex15B2Economy.ω 1 = ex15B2r * p 0 + 2 * p 1 := by
    simp [ex15B2Economy, dotProduct, Fin.sum_univ_two, mul_comm]
  have hx1 : (2 * p 0 + ex15B2r * p 1 - p 1 * t) / p 0 = 2 + ex15B2r / t ^ 9 - 1 / t ^ 8 := by
    rw [← hfoc1]
    field_simp
  have hx2 : (ex15B2r * p 0 + 2 * p 1 - p 0 * (1 / t)) / p 1 = 2 + ex15B2r * t ^ 9 - t ^ 8 := by
    rw [← hfoc2]
    field_simp
    ring
  refine ⟨?_, ?_, fun l => ?_, fun l => ?_⟩
  · ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hb⟩, hmax⟩
      have hb' : p 0 * y 0 + p 1 * y 1 ≤ 2 * p 0 + ex15B2r * p 1 := by
        rw [← hw1]
        simpa [dotProduct, Fin.sum_univ_two] using hb
      have hy' : y 0 ≥ 0 ∧ 0 < y 1 := hy
      have hopt := ql8_optimal hp0 hp1 ht hfoc1 hy'.2 hb'
      have hmem : ex15B2OC1 t ∈ budgetSetOn (ex15B2Economy.X 0) p
          (p ⬝ᵥ ex15B2Economy.ω 0) := by
        refine ⟨⟨hpos1.le, ht⟩, ?_⟩
        rw [hw1]
        simp only [ex15B2OC1, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx1, mul_div_cancel₀ _ hp0.ne']
        linarith
      have h2 := hmax _ hmem
      simp only [ex15B2Economy, ex15B2OC1, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← hx1] at h2
      have := hopt.2 (le_antisymm hopt.1 h2)
      have e0 : y 0 = ex15B2OC1 t 0 := this.2.trans hx1
      have e1 : y 1 = ex15B2OC1 t 1 := this.1
      funext l
      fin_cases l
      exacts [e0, e1]
    · rintro rfl
      refine ⟨⟨⟨hpos1.le, ht⟩, ?_⟩, fun y hy => ?_⟩
      · rw [hw1]
        simp only [ex15B2OC1, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx1]
        field_simp
        linarith
      · have hb' : p 0 * y 0 + p 1 * y 1 ≤ 2 * p 0 + ex15B2r * p 1 := by
          rw [← hw1]
          simpa [dotProduct, Fin.sum_univ_two] using hy.2
        have := (ql8_optimal hp0 hp1 ht hfoc1 hy.1.2 hb').1
        simp only [ex15B2Economy, ex15B2OC1, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hx1]
        exact this
  · ext y
    simp only [Set.mem_singleton_iff]
    have hti : 0 < 1 / t := one_div_pos.2 ht
    constructor
    · rintro ⟨⟨hy, hb⟩, hmax⟩
      have hb' : p 1 * y 1 + p 0 * y 0 ≤ ex15B2r * p 0 + 2 * p 1 := by
        rw [hw2] at hb
        simp only [dotProduct, Fin.sum_univ_two] at hb
        linarith
      have hy' : 0 < y 0 ∧ 0 ≤ y 1 := hy
      have hopt := ql8_optimal hp1 hp0 hti hfoc2 hy'.1 hb'
      have hmem : ex15B2OC2 t ∈ budgetSetOn (ex15B2Economy.X 1) p
          (p ⬝ᵥ ex15B2Economy.ω 1) := by
        refine ⟨⟨hti, hpos2.le⟩, ?_⟩
        rw [hw2]
        simp only [ex15B2OC2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx2, mul_div_cancel₀ _ hp1.ne']
        linarith
      have h2 := hmax _ hmem
      simp only [ex15B2Economy, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← hx2] at h2
      have := hopt.2 (by linarith [hopt.1])
      have e0 : y 0 = ex15B2OC2 t 0 := this.1
      have e1 : y 1 = ex15B2OC2 t 1 := this.2.trans hx2
      funext l
      fin_cases l
      exacts [e0, e1]
    · rintro rfl
      refine ⟨⟨⟨hti, hpos2.le⟩, ?_⟩, fun y hy => ?_⟩
      · rw [hw2]
        simp only [ex15B2OC2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [← hx2]
        field_simp
        linarith
      · have hb' : p 1 * y 1 + p 0 * y 0 ≤ ex15B2r * p 0 + 2 * p 1 := by
          have := hy.2
          rw [hw2] at this
          simp only [dotProduct, Fin.sum_univ_two] at this
          linarith
        have := (ql8_optimal hp1 hp0 hti hfoc2 hy.1.1 hb').1
        simp only [ex15B2Economy, ex15B2OC2, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hx2]
        linarith
  · fin_cases l
    · exact hpos1
    · exact ht
  · fin_cases l
    · exact one_div_pos.2 ht
    · exact hpos2

/-- The market-clearing polynomial `P(t) = r t⁹ - t⁸ + t - r` factors as
`(t - 1)(t - a)(t - 1/a) Q(t)` with `a = 2^{1/9}` and `Q` having positive coefficients. -/
theorem ex15B2_factor (t : ℝ) : ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r =
    (t - 1) * (t - ex15B2a) * (t - ex15B2a ^ 8 / 2) *
      ((ex15B2a ^ 8 - ex15B2a) * t ^ 6 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 - ex15B2a ^ 2 - ex15B2a) * t ^ 5 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 + ex15B2a ^ 6 - ex15B2a ^ 3 - ex15B2a ^ 2 - ex15B2a) * t ^ 4 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 + ex15B2a ^ 6 + ex15B2a ^ 5 - ex15B2a ^ 4 - ex15B2a ^ 3 -
          ex15B2a ^ 2 - ex15B2a) * t ^ 3 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 + ex15B2a ^ 6 - ex15B2a ^ 3 - ex15B2a ^ 2 - ex15B2a) * t ^ 2 +
        (ex15B2a ^ 8 + ex15B2a ^ 7 - ex15B2a ^ 2 - ex15B2a) * t + (ex15B2a ^ 8 - ex15B2a)) := by
  rw [ex15B2r_eq]
  set a := ex15B2a
  linear_combination ((-1/2) * a + (1/2) * a ^ 8 + (-1/2) * t + (-1/2) * t * a ^ 2 +
    (1/2) * t ^ 2 * a + (-1/2) * t ^ 2 * a ^ 3 + (1/2) * t ^ 3 * a ^ 2 + (-1/2) * t ^ 3 * a ^ 4 +
    (1/2) * t ^ 4 * a ^ 3 + (-1/2) * t ^ 4 * a ^ 5 + (1/2) * t ^ 5 * a ^ 4 +
    (-1/2) * t ^ 5 * a ^ 6 + (1/2) * t ^ 6 * a ^ 5 + (-1/2) * t ^ 6 * a ^ 7 +
    (1/2) * t ^ 7 * a ^ 6 + (-1/2) * t ^ 7 * a ^ 8 + (1/2) * t ^ 8 + (1/2) * t ^ 8 * a ^ 7) *
    ex15B2a_pow

/-- **Example 15.B.2** (MWG, p. 522; Exercise 15.B.5). The positive roots of the market-clearing
equation `r t⁹ - t⁸ + t - r = 0` are exactly `t = 1`, `t = 2^{1/9}` and `t = 2^{-1/9}`
(`2^{-1/9} = 2^{8/9}/2`). -/
theorem ex15B2_roots {t : ℝ} (ht : 0 < t) :
    ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r = 0 ↔
      t = 1 ∨ t = ex15B2a ∨ t = ex15B2a ^ 8 / 2 := by
  have ha := ex15B2a_bounds
  have ha1 : 1 < ex15B2a := by linarith [ha.1]
  rw [ex15B2_factor]
  set a := ex15B2a
  have hp : ∀ k m : ℕ, k < m → a ^ k < a ^ m := fun k m h => pow_lt_pow_right₀ ha1 h
  have q6 : 0 < a ^ 8 - a := by have := hp 1 8 (by norm_num); simp at this; linarith
  have q5 : 0 < a ^ 8 + a ^ 7 - a ^ 2 - a := by
    have := hp 2 7 (by norm_num); linarith
  have q4 : 0 < a ^ 8 + a ^ 7 + a ^ 6 - a ^ 3 - a ^ 2 - a := by
    have := hp 3 6 (by norm_num); linarith
  have q3 : 0 < a ^ 8 + a ^ 7 + a ^ 6 + a ^ 5 - a ^ 4 - a ^ 3 - a ^ 2 - a := by
    have := hp 4 5 (by norm_num); linarith
  have hQ : 0 < (a ^ 8 - a) * t ^ 6 + (a ^ 8 + a ^ 7 - a ^ 2 - a) * t ^ 5 +
      (a ^ 8 + a ^ 7 + a ^ 6 - a ^ 3 - a ^ 2 - a) * t ^ 4 +
      (a ^ 8 + a ^ 7 + a ^ 6 + a ^ 5 - a ^ 4 - a ^ 3 - a ^ 2 - a) * t ^ 3 +
      (a ^ 8 + a ^ 7 + a ^ 6 - a ^ 3 - a ^ 2 - a) * t ^ 2 + (a ^ 8 + a ^ 7 - a ^ 2 - a) * t +
      (a ^ 8 - a) := by positivity
  rw [mul_eq_zero, or_iff_left hQ.ne', mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero,
    sub_eq_zero]
  tauto

/-- `2^{-1/9}` in the form `2^{8/9}/2`: `(2^{8/9}/2)⁹ = 1/2`. -/
theorem ex15B2a_inv_pow : (ex15B2a ^ 8 / 2) ^ 9 = 1 / 2 := by
  have h := ex15B2a_pow
  have : (ex15B2a ^ 8 / 2) ^ 9 = (ex15B2a ^ 9) ^ 8 / 2 ^ 9 := by ring
  rw [this, h]
  norm_num

/-- Equilibrium prices have `p ≫ 0` in Example 15.B.2: if a price is `≤ 0`, consumer 1 (if
`p₁ ≤ 0`) or consumer 1 (if `p₂ ≤ 0`, via good 2) demands nothing. -/
theorem ex15B2_demand0_empty {p : Fin 2 → ℝ} (hp : ¬ StrictlyPositive p) :
    ex15B2Economy.demand 0 p = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hy, hb⟩, hmax⟩
  have hy' : 0 ≤ y 0 ∧ 0 < y 1 := hy
  simp only [StrictlyPositive, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  fin_cases l
  · -- more of good 1 is affordable and better
    have hmem : y + Pi.single 0 1 ∈ budgetSetOn (ex15B2Economy.X 0) p
        (p ⬝ᵥ ex15B2Economy.ω 0) := by
      refine ⟨⟨by simp; linarith [hy'.1], by simpa using hy'.2⟩, ?_⟩
      rw [dotProduct_add]
      simp only [dotProduct_single, mul_one]
      simp at hl
      linarith
    have := hmax _ hmem
    simp only [ex15B2Economy, Matrix.cons_val_zero, Pi.add_apply, Pi.single_eq_same] at this
    simp only [ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    linarith
  · have hmem : y + Pi.single 1 1 ∈ budgetSetOn (ex15B2Economy.X 0) p
        (p ⬝ᵥ ex15B2Economy.ω 0) := by
      refine ⟨⟨by simpa using hy'.1, by simp; linarith [hy'.2]⟩, ?_⟩
      rw [dotProduct_add]
      simp only [dotProduct_single, mul_one]
      simp at hl
      linarith
    have := hmax _ hmem
    simp only [ex15B2Economy, Matrix.cons_val_zero, Pi.add_apply, Pi.single_eq_same] at this
    simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero] at this
    have hy1 := hy'.2
    have h1 : y 1 ^ 8 < (y 1 + 1) ^ 8 := pow_lt_pow_left₀ (by linarith) hy'.2.le (by norm_num)
    have h2 : 1 / (8 * (y 1 + 1) ^ 8) < 1 / (8 * y 1 ^ 8) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    linarith

/-- **Example 15.B.2** (MWG, pp. 521-522). The Walrasian equilibrium price vectors are exactly the
`p ≫ 0` with `p₁/p₂ ∈ {1, 2, 1/2}`. -/
theorem example_15_B_2 (p : Fin 2 → ℝ) :
    (∃ x, ex15B2Economy.IsDemandEqm p x) ↔
      StrictlyPositive p ∧ (p 0 = p 1 ∨ p 0 = 2 * p 1 ∨ 2 * p 0 = p 1) := by
  have hr := ex15B2r_bounds
  have htot : ex15B2Economy.totalEndowment = ![2 + ex15B2r, ex15B2r + 2] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, ex15B2Economy, Fin.sum_univ_two]
  constructor
  · rintro ⟨x, hbox, hd⟩
    have hp : StrictlyPositive p := by
      by_contra hp
      have := hd 0
      rw [ex15B2_demand0_empty hp] at this
      exact this
    refine ⟨hp, ?_⟩
    set t := (p 0 / p 1) ^ ((1 : ℝ) / 9) with htdef
    have hq : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    have ht : 0 < t := Real.rpow_pos_of_pos hq _
    have ht9 : t ^ 9 = p 0 / p 1 := by
      rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      norm_num
    obtain ⟨hd1, hd2, -, -⟩ := exercise_15_B_5_offerCurves hp ht ht9
    have hx0 := hd 0
    have hx1 := hd 1
    rw [hd1, Set.mem_singleton_iff] at hx0
    rw [hd2, Set.mem_singleton_iff] at hx1
    have hc := congrFun hbox.2 1
    rw [htot, Finset.sum_apply, Fin.sum_univ_two, hx0, hx1] at hc
    simp only [ex15B2OC1, ex15B2OC2, Matrix.cons_val_one, Matrix.cons_val_zero] at hc
    have hP : ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r = 0 := by linarith
    rcases (ex15B2_roots ht).1 hP with h | h | h
    · left
      rw [h, one_pow, eq_comm, div_eq_one_iff_eq (hp 1).ne'] at ht9
      exact ht9
    · right; left
      rw [h, ex15B2a_pow, eq_div_iff (hp 1).ne'] at ht9
      exact ht9.symm
    · right; right
      rw [h, ex15B2a_inv_pow, eq_div_iff (hp 1).ne'] at ht9
      linarith
  · rintro ⟨hp, hrel⟩
    have hq : 0 < p 0 / p 1 := div_pos (hp 0) (hp 1)
    obtain ⟨t, ht, ht9, hP⟩ : ∃ t, 0 < t ∧ t ^ 9 = p 0 / p 1 ∧
        ex15B2r * t ^ 9 - t ^ 8 + t - ex15B2r = 0 := by
      have ha := ex15B2a_bounds
      rcases hrel with h | h | h
      · refine ⟨1, one_pos, ?_, (ex15B2_roots one_pos).2 (Or.inl rfl)⟩
        rw [h, div_self (hp 1).ne', one_pow]
      · refine ⟨ex15B2a, by linarith, ?_, (ex15B2_roots (by linarith)).2 (Or.inr (Or.inl rfl))⟩
        rw [h, ex15B2a_pow, mul_div_cancel_right₀ _ (hp 1).ne']
      · have hpos : 0 < ex15B2a ^ 8 / 2 := div_pos (pow_pos (by linarith [ha.1]) 8) two_pos
        refine ⟨ex15B2a ^ 8 / 2, hpos, ?_, (ex15B2_roots hpos).2 (Or.inr (Or.inr rfl))⟩
        rw [ex15B2a_inv_pow, ← h]
        field_simp [(hp 0).ne']
    obtain ⟨hd1, hd2, hpos1, hpos2⟩ := exercise_15_B_5_offerCurves hp ht ht9
    refine ⟨![ex15B2OC1 t, ex15B2OC2 t], ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩⟩
    · fin_cases i
      · exact ⟨(hpos1 0).le, hpos1 1⟩
      · exact ⟨hpos2 0, (hpos2 1).le⟩
    · rw [htot]
      have h9 : t ^ 9 ≠ 0 := by positivity
      have e0 : ex15B2OC1 t 0 + ex15B2OC2 t 0 = 2 + ex15B2r := by
        simp only [ex15B2OC1, ex15B2OC2, Matrix.cons_val_zero]
        field_simp
        linear_combination (-1 : ℝ) * hP
      have e1 : ex15B2OC1 t 1 + ex15B2OC2 t 1 = ex15B2r + 2 := by
        simp only [ex15B2OC1, ex15B2OC2, Matrix.cons_val_one, Matrix.cons_val_zero]
        linear_combination hP
      funext l
      fin_cases l
      · simpa [Fin.sum_univ_two] using e0
      · simpa [Fin.sum_univ_two] using e1
    · fin_cases i
      · exact (hd1 ▸ Set.mem_singleton (ex15B2OC1 t) : ex15B2OC1 t ∈ ex15B2Economy.demand 0 p)
      · exact (hd2 ▸ Set.mem_singleton (ex15B2OC2 t) : ex15B2OC2 t ∈ ex15B2Economy.demand 1 p)

/-- **Exercise 15.B.5** (MWG, p. 541): the offer curves in the book's `rpow` form,
`OC₁(p) = (2 + r(p₂/p₁) - (p₂/p₁)^{8/9}, (p₂/p₁)^{-1/9})` and
`OC₂(p) = ((p₁/p₂)^{-1/9}, 2 + r(p₁/p₂) - (p₁/p₂)^{8/9})`. -/
theorem exercise_15_B_5_printed {p : Fin 2 → ℝ} (hp : StrictlyPositive p) :
    ex15B2Economy.demand 0 p = {![2 + ex15B2r * (p 1 / p 0) - (p 1 / p 0) ^ ((8 : ℝ) / 9),
      (p 1 / p 0) ^ (-(1 : ℝ) / 9)]} ∧
    ex15B2Economy.demand 1 p = {![(p 0 / p 1) ^ (-(1 : ℝ) / 9),
      2 + ex15B2r * (p 0 / p 1) - (p 0 / p 1) ^ ((8 : ℝ) / 9)]} := by
  set q := p 0 / p 1 with hqd
  have hq : 0 < q := div_pos (hp 0) (hp 1)
  set t := q ^ ((1 : ℝ) / 9) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hq _
  have ht9 : t ^ 9 = q := by
    rw [htdef, ← Real.rpow_mul_natCast hq.le]
    norm_num
  have hinv : p 1 / p 0 = q⁻¹ := by rw [hqd, inv_div]
  obtain ⟨hd1, hd2, -, -⟩ := exercise_15_B_5_offerCurves hp ht ht9
  have e1 : (q⁻¹) ^ ((8 : ℝ) / 9) = 1 / t ^ 8 := by
    rw [Real.inv_rpow hq.le, show (8 : ℝ) / 9 = (1 / 9) * ((8 : ℕ) : ℝ) by norm_num,
      Real.rpow_mul_natCast hq.le]
    exact (one_div (t ^ 8)).symm
  have e2 : (q⁻¹) ^ (-(1 : ℝ) / 9) = t := by
    rw [Real.inv_rpow hq.le, show -(1 : ℝ) / 9 = -((1 : ℝ) / 9) by ring,
      Real.rpow_neg hq.le, inv_inv]
  have e3 : q ^ (-(1 : ℝ) / 9) = 1 / t := by
    rw [show -(1 : ℝ) / 9 = -((1 : ℝ) / 9) by ring, Real.rpow_neg hq.le]
    exact (one_div t).symm
  have e4 : q ^ ((8 : ℝ) / 9) = t ^ 8 := by
    rw [show (8 : ℝ) / 9 = (1 / 9) * ((8 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hq.le]
  constructor
  · rw [hd1, hinv, e1, e2, ← ht9]
    congr 1
  · rw [hd2, e3, e4, ← ht9]
    rfl

/-- **Example 15.B.2** (MWG, p. 521): consumer 1's demand for good 1 may increase with `p₁`. At
`p = (1, 1)` it is `1 + r`, at `p = (2, 1)` it is `2 + 2^{-1/9} - 2^{1/9}`, which is larger. -/
theorem example_15_B_2_increasing :
    ex15B2OC1 1 0 < ex15B2OC1 ex15B2a 0 ∧ (1 : ℝ) ^ 9 = 1 / 1 ∧ ex15B2a ^ 9 = 2 / 1 := by
  have ha := ex15B2a_bounds
  have h9 := ex15B2a_pow
  have hpos : 0 < ex15B2a := by linarith
  refine ⟨?_, by norm_num, by rw [h9]; norm_num⟩
  simp only [ex15B2OC1, Matrix.cons_val_zero, one_pow, div_one]
  rw [h9, ex15B2r_eq]
  have h8 : ex15B2a ^ 8 = 2 / ex15B2a := by
    rw [eq_div_iff hpos.ne', ← h9]
    ring
  rw [h8]
  rw [← sub_pos]
  have : 2 + (2 / ex15B2a - ex15B2a) / 2 - 1 / (2 / ex15B2a) - (2 + (2 / ex15B2a - ex15B2a) - 1)
      = 1 - 1 / ex15B2a := by
    field_simp
    ring
  rw [this, sub_pos, div_lt_one hpos]
  linarith

end MWG.GeneralEquilibriumExamples
