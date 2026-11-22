/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Applications

/-!
# Exercise 16.G.5: education with increasing returns (MWG pp. 576-577)

Education `e = (min{L, T})²` and food `f = (LT)^{1/2}` are produced from labor and land, the
endowment is `(ω_L, ω_T) = (1, 1)`, and utility is `u(e, f) = e^α f^{1-α}` with `α = 1/2`, i.e.
`u = √(ef)`. Food is the numeraire.

* (a) The optimum uses `L_e = T_e = 2/3`, produces `e = 4/9`, `f = 1/3`, `u = √(4/27)`.
* (b) Competitive food production gives factor prices `w_L = w_T = 1/2` (the marginal products at
  `L_f = T_f = 1/3`); the cost-minimizing cost of education is `C(e) = (w_L + w_T)√e`, whose
  marginal cost at `e = 4/9` is `3/4`. At `p_e = 3/4` and income `1 - τ` with the lump-sum tax
  `τ = 1/3` covering the deficit, the consumer demands exactly `e = 4/9` (and `f = 1/3`).
* (c) The tax is `τ = 1/3`.
* (d) Two consumers (one owns the land, one the labor); the deficit of marginal cost pricing,
  `C(e) - C'(e)e = (w_L + w_T)√e/2`, is taxed from the landowner.
* (e) With `w_L = w_T = 1/2` the marginal cost price equilibrium has `e = 4/9`, `f = 1/3`,
  `p_e = 3/4`, landowner transfer `1/3`; the landowner consumes `(1/9, 1/12)` and the laborer
  `(1/3, 1/4)`. It is Pareto optimal: the utilities sum to the maximal `√(4/27)`, which bounds the
  sum of utilities of every feasible allocation.
-/

namespace MWG.WelfareTheorems

/-- **Exercise 16.G.5(a)** (MWG, p. 577). For every division of the endowment `(1, 1)` (labor `L`
and land `T` to education, the rest to food), `ef ≤ 4/27`, with equality at `L = T = 2/3`
(`e = 4/9`, `f = 1/3`). So the optimal allocation of the endowments is `L_e = T_e = 2/3`,
`L_f = T_f = 1/3`. -/
theorem exercise_16_G_5a {L T : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    min L T ^ 2 * Real.sqrt ((1 - L) * (1 - T)) ≤ 4 / 27 ∧
      min (2 / 3 : ℝ) (2 / 3) ^ 2 * Real.sqrt ((1 - 2 / 3) * (1 - 2 / 3)) = 4 / 27 ∧
      min (2 / 3 : ℝ) (2 / 3) ^ 2 = 4 / 9 ∧ Real.sqrt ((1 - 2 / 3) * (1 - 2 / 3) : ℝ) = 1 / 3 := by
  have hsq : Real.sqrt ((1 - 2 / 3) * (1 - 2 / 3) : ℝ) = 1 / 3 := by
    rw [show ((1 - 2 / 3) * (1 - 2 / 3) : ℝ) = (1 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, by rw [hsq]; norm_num, by norm_num, hsq⟩
  set m := min L T with hm
  have hmL : m ≤ L := min_le_left _ _
  have hmT : m ≤ T := min_le_right _ _
  have hm0 : 0 ≤ m := le_min hL0 hT0
  have hm1 : m ≤ 1 := hmL.trans hL1
  have hroot : Real.sqrt ((1 - L) * (1 - T)) ≤ 1 - m := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [mul_le_mul (by linarith : 1 - L ≤ 1 - m) (by linarith : 1 - T ≤ 1 - m)
      (by linarith) (by linarith)]
  calc m ^ 2 * Real.sqrt ((1 - L) * (1 - T)) ≤ m ^ 2 * (1 - m) :=
        mul_le_mul_of_nonneg_left hroot (sq_nonneg m)
    _ ≤ 4 / 27 := by nlinarith [sq_nonneg (m - 2 / 3), mul_nonneg (sq_nonneg (m - 2 / 3)) hm0]

/-- **Exercise 16.G.5(b)** (MWG, p. 577), factor prices. The marginal products of labor and land in
food production `f = √(LT)` at `L = T = 1/3` are both `1/2`; so competitive food production (food
the numeraire) gives `w_L = w_T = 1/2`. -/
theorem exercise_16_G_5b_wages :
    HasDerivAt (fun L : ℝ => Real.sqrt (L * (1 / 3))) (1 / 2) (1 / 3) ∧
      HasDerivAt (fun T : ℝ => Real.sqrt ((1 / 3) * T)) (1 / 2) (1 / 3) := by
  have h1 : HasDerivAt (fun L : ℝ => L * (1 / 3)) (1 / 3) (1 / 3) := by
    simpa using (hasDerivAt_id (1 / 3 : ℝ)).mul_const (1 / 3 : ℝ)
  have h2 : HasDerivAt (fun T : ℝ => (1 / 3) * T) (1 / 3) (1 / 3) := by
    simpa using (hasDerivAt_id (1 / 3 : ℝ)).const_mul (1 / 3 : ℝ)
  have hval : Real.sqrt ((1 / 3 : ℝ) * (1 / 3)) = 1 / 3 := by
    rw [show (1 / 3 : ℝ) * (1 / 3) = (1 / 3) ^ 2 by ring]
    exact Real.sqrt_sq (by norm_num)
  have hne : ((1 / 3 : ℝ) * (1 / 3)) ≠ 0 := by norm_num
  refine ⟨?_, ?_⟩
  · have := h1.sqrt hne
    rw [hval] at this
    convert this using 1
    norm_num
  · have := h2.sqrt hne
    rw [hval] at this
    convert this using 1
    norm_num

/-- **Exercise 16.G.5(b)** (MWG, p. 577), the cost of education. With factor prices `w_L, w_T ≥ 0`,
producing `e ≥ 0` units costs at least `(w_L + w_T)√e`, attained with `L = T = √e`. -/
theorem exercise_16_G_5b_cost {wL wT e : ℝ} (hwL : 0 ≤ wL) (hwT : 0 ≤ wT) (he : 0 ≤ e) :
    min (Real.sqrt e) (Real.sqrt e) ^ 2 = e ∧
      ∀ L T : ℝ, 0 ≤ L → 0 ≤ T → e ≤ min L T ^ 2 → (wL + wT) * Real.sqrt e ≤ wL * L + wT * T := by
  refine ⟨by rw [min_self, Real.sq_sqrt he], fun L T hL hT hle => ?_⟩
  have hs : Real.sqrt e ≤ min L T := by
    rw [Real.sqrt_le_left (le_min hL hT)]; exact hle
  nlinarith [mul_le_mul_of_nonneg_left (hs.trans (min_le_left L T)) hwL,
    mul_le_mul_of_nonneg_left (hs.trans (min_le_right L T)) hwT]

/-- **Exercise 16.G.5(b)** (MWG, p. 577), marginal cost. With `w_L = w_T = 1/2` the cost
`C(e) = √e` has marginal cost `3/4` at the optimal level `e = 4/9`. -/
theorem exercise_16_G_5b_mc :
    HasDerivAt (fun e : ℝ => (1 / 2 + 1 / 2) * Real.sqrt e) (3 / 4) (4 / 9) := by
  have hs : Real.sqrt (4 / 9 : ℝ) = 2 / 3 := by
    rw [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have := (Real.hasDerivAt_sqrt (by norm_num : (4 / 9 : ℝ) ≠ 0)).const_mul (1 / 2 + 1 / 2 : ℝ)
  rw [hs] at this
  convert this using 1
  norm_num

/-- **Exercise 16.G.5(b)-(c)** (MWG, p. 577). At `p_e = 3/4`, `p_f = 1`, the education sector's
deficit at `e = 4/9` is `C(4/9) - p_e·(4/9) = 1/3`; with the lump-sum tax `τ = 1/3` the consumer's
income is `w_L + w_T - τ = 2/3`, and on the budget set `{p_e e + f ≤ 2/3}` utility `√(ef)` is
maximized at `e = 4/9`, `f = 1/3`: the consumer chooses the optimal level of education. -/
theorem exercise_16_G_5bc :
    (1 / 2 + 1 / 2 : ℝ) * (2 / 3) - 3 / 4 * (4 / 9) = 1 / 3 ∧
      (1 / 2 + 1 / 2 - 1 / 3 : ℝ) = 2 / 3 ∧
      3 / 4 * (4 / 9) + 1 / 3 ≤ (2 / 3 : ℝ) ∧
      ∀ e f : ℝ, 0 ≤ e → 0 ≤ f → 3 / 4 * e + f ≤ 2 / 3 →
        Real.sqrt (e * f) ≤ Real.sqrt (4 / 9 * (1 / 3)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun e f he hf hb => ?_⟩
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (3 / 4 * e - f), mul_nonneg he hf]

/-- **Exercise 16.G.5(d)** (MWG, p. 577). With marginal cost pricing `p_e = C'(e)` and cost
`C(e) = (w_L + w_T)√e`, the deficit of the public education sector, to be covered by a tax on the
landowner, is `C(e) - C'(e)e = (w_L + w_T)√e/2` (for `e > 0`). -/
theorem exercise_16_G_5d {wL wT e : ℝ} (he : 0 < e) :
    HasDerivAt (fun e : ℝ => (wL + wT) * Real.sqrt e) ((wL + wT) / (2 * Real.sqrt e)) e ∧
      (wL + wT) * Real.sqrt e - (wL + wT) / (2 * Real.sqrt e) * e =
        (wL + wT) * Real.sqrt e / 2 := by
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  refine ⟨?_, ?_⟩
  · have := (Real.hasDerivAt_sqrt he.ne').const_mul (wL + wT)
    convert this using 1
    field_simp
  · have key : e = Real.sqrt e * Real.sqrt e := (Real.mul_self_sqrt he.le).symm
    have h2 : (wL + wT) / (2 * Real.sqrt e) * e = (wL + wT) * Real.sqrt e / 2 := by
      calc (wL + wT) / (2 * Real.sqrt e) * e
          = (wL + wT) / (2 * Real.sqrt e) * (Real.sqrt e * Real.sqrt e) := by rw [← key]
        _ = (wL + wT) * Real.sqrt e / 2 := by field_simp
    rw [h2]
    ring

/-- **Exercise 16.G.5(e)** (MWG, p. 577), the equilibrium level. With `w_L = w_T = 1/2`, marginal
cost price `p_e = 1/(2√e)`, the laborer's income `1/2`, the landowner's income `1/2 - √e/2` (after
the transfer of (d)), and each consumer spending half her income on education, market clearing
for education, `e = (1/2)(1 - √e/2)/p_e`, holds (for `e > 0`) exactly when `e = 4/9`. -/
theorem exercise_16_G_5e_level {e : ℝ} (he : 0 < e) :
    e = (1 / 2) * ((1 / 2) + (1 / 2 - Real.sqrt e / 2)) / (1 / (2 * Real.sqrt e)) ↔
      e = 4 / 9 := by
  have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hse : Real.sqrt e ^ 2 = e := Real.sq_sqrt he.le
  constructor
  · intro h
    field_simp at h
    -- `e = √e (1 - √e/2)`, i.e. `(3/2) e = √e`, so `√e = 2/3`
    have h2 : Real.sqrt e = 2 / 3 := by nlinarith
    rw [← hse, h2]; norm_num
  · intro h
    have h2 : Real.sqrt e = 2 / 3 := by
      rw [h, show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h2, h]
    norm_num

/-- The geometric mean is superadditive: `√(ab) + √(cd) ≤ √((a + c)(b + d))` for nonnegative
reals. -/
theorem sqrt_mul_add_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  rw [Real.le_sqrt (by positivity) (by positivity), add_sq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), mul_assoc, ← Real.sqrt_mul (by positivity)]
  have h : Real.sqrt (a * b * (c * d)) ≤ (a * d + b * c) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (a * d - b * c)]
  nlinarith

/-- **Exercise 16.G.5(e)** (MWG, p. 577). The marginal cost price equilibrium (`e = 4/9`, `f = 1/3`,
`p_e = 3/4`, wages `1/2`, landowner transfer `1/3`) gives the landowner `(1/9, 1/12)` and the
laborer `(1/3, 1/4)`, each maximizing `√(ef)` on her budget set; it is Pareto optimal: for every
allocation of a producible `(E, F)` (`E = (min{L, T})²`, `F = √((1-L)(1-T))`), the sum of the two
utilities is at most `√(4/27)`, the sum at the equilibrium. -/
theorem exercise_16_G_5e :
    (1 / 9 + 1 / 3 : ℝ) = 4 / 9 ∧ (1 / 12 + 1 / 4 : ℝ) = 1 / 3 ∧
    (∀ e f : ℝ, 0 ≤ e → 0 ≤ f → 3 / 4 * e + f ≤ 1 / 2 - 1 / 3 →
      Real.sqrt (e * f) ≤ Real.sqrt (1 / 9 * (1 / 12))) ∧
    (∀ e f : ℝ, 0 ≤ e → 0 ≤ f → 3 / 4 * e + f ≤ 1 / 2 →
      Real.sqrt (e * f) ≤ Real.sqrt (1 / 3 * (1 / 4))) ∧
    Real.sqrt (1 / 9 * (1 / 12)) + Real.sqrt (1 / 3 * (1 / 4)) = Real.sqrt (4 / 27 : ℝ) ∧
    ∀ (L T e₁ f₁ e₂ f₂ : ℝ), 0 ≤ L → L ≤ 1 → 0 ≤ T → T ≤ 1 → 0 ≤ e₁ → 0 ≤ f₁ → 0 ≤ e₂ →
      0 ≤ f₂ → e₁ + e₂ ≤ min L T ^ 2 → f₁ + f₂ ≤ Real.sqrt ((1 - L) * (1 - T)) →
      Real.sqrt (e₁ * f₁) + Real.sqrt (e₂ * f₂) ≤ Real.sqrt (4 / 27) := by
  refine ⟨by norm_num, by norm_num, fun e f he hf hb => ?_, fun e f he hf hb => ?_, ?_,
    fun L T e₁ f₁ e₂ f₂ hL0 hL1 hT0 hT1 he₁ hf₁ he₂ hf₂ hE hF => ?_⟩
  · apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (3 / 4 * e - f), mul_nonneg he hf]
  · apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (3 / 4 * e - f), mul_nonneg he hf]
  · have h1 : Real.sqrt (1 / 9 * (1 / 12) : ℝ) = Real.sqrt (4 / 27) / 4 := by
      rw [show (1 / 9 * (1 / 12) : ℝ) = 4 / 27 / 4 ^ 2 by norm_num, Real.sqrt_div' _
        (by norm_num : (0 : ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by norm_num)]
    have h2 : Real.sqrt (1 / 3 * (1 / 4) : ℝ) = 3 * Real.sqrt (4 / 27) / 4 := by
      rw [show (1 / 3 * (1 / 4) : ℝ) = 3 ^ 2 * (4 / 27) / 4 ^ 2 by norm_num,
        Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by norm_num),
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [h1, h2]
    ring
  · have hsum := sqrt_mul_add_le he₁ hf₁ he₂ hf₂
    have hmax := (exercise_16_G_5a hL0 hL1 hT0 hT1).1
    refine hsum.trans (Real.sqrt_le_sqrt ?_)
    have hF0 : 0 ≤ Real.sqrt ((1 - L) * (1 - T)) := Real.sqrt_nonneg _
    calc (e₁ + e₂) * (f₁ + f₂) ≤ min L T ^ 2 * Real.sqrt ((1 - L) * (1 - T)) :=
          mul_le_mul hE hF (by positivity) (sq_nonneg _)
      _ ≤ 4 / 27 := hmax

end MWG.WelfareTheorems
