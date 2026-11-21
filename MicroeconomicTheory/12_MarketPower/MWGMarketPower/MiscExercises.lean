/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Cournot

/-!
# Exercises 12.C.9(c) and 12.D.1

MWG, pp. 431, 433.

* `exercise_12_C_9c`: in any Cournot equilibrium with constant unit costs, industry profit
  divided by industry revenue equals `H/ε`, with `H = ∑ⱼ (qⱼ/Q)²` and `ε = −p(Q)/(p'(Q)Q)`.
* `exercise_12_D_1a`-`exercise_12_D_1c`: the conditions under which the strategies (12.D.1)
  sustain the monopoly price, comparing the discounted collusive profit with the best one-period
  (or `K`-period) deviation followed by zero profits: `δγ ≥ 1/2` with demand growth `γ`,
  `δ(1 − γ) ≥ 1/2` when the market ends with probability `γ` each period, and `δ^K ≥ 1/2` when
  a deviation is answered only after `K` periods.
-/

namespace MWG.MarketPower

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Exercise 12.C.9(c)** (MWG, p. 431). In a Cournot equilibrium with constant unit costs `cⱼ`
in which every producing firm satisfies its first-order condition `p'(Q)qⱼ + p(Q) = cⱼ`, the ratio
of industry profit to industry revenue is `H/ε`, where `H = ∑ⱼ (qⱼ/Q)²` is the Herfindahl index
and `ε = −p(Q)/(p'(Q)Q)` is the elasticity of demand, `Q = ∑ⱼ qⱼ` the industry output
(the identity holds for any `Q ≠ 0`). Firms with `qⱼ = 0` contribute nothing. -/
theorem exercise_12_C_9c {c q : ι → ℝ} {P P' Q : ℝ} (hQ0 : Q ≠ 0)
    (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hfoc : ∀ j, q j ≠ 0 → P' * q j + P = c j) :
    (∑ j, (P - c j) * q j) / (P * Q) = (∑ j, (q j / Q) ^ 2) / (-(P / (P' * Q))) := by
  have hterm : ∀ j, (P - c j) * q j = -P' * q j ^ 2 := by
    intro j
    by_cases hj : q j = 0
    · rw [hj]; ring
    · rw [← hfoc j hj]; ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum]
  have hsq : ∑ j, (q j / Q) ^ 2 = (∑ j, q j ^ 2) / Q ^ 2 := by
    rw [Finset.sum_div]; congr 1; funext j; rw [div_pow]
  rw [hsq]
  field_simp

/-- **Exercise 12.D.1(a)** (MWG, p. 433). With demand growing at rate `γ` (`x_t = γᵗx`,
`δγ < 1`) the collusive value from period `t`, `γᵗπᵐ/(2(1 − δγ))`, is at least the best
deviation payoff `γᵗπᵐ` (followed by zero profits) iff `δγ ≥ 1/2`. -/
theorem exercise_12_D_1a {δ γ πm : ℝ} (hγ : 0 < γ) (hπ : 0 < πm) (h1 : δ * γ < 1) (t : ℕ) :
    γ ^ t * πm ≤ γ ^ t * πm / (2 * (1 - δ * γ)) ↔ 1 / 2 ≤ δ * γ := by
  have hpos : 0 < γ ^ t * πm := by positivity
  rw [le_div_iff₀ (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Exercise 12.D.1(b)** (MWG, p. 433). If after each period the market ends with probability
`γ`, expected discounted profits use the factor `δ(1 − γ)`; the monopoly price is sustained iff
`δ(1 − γ) ≥ 1/2`. -/
theorem exercise_12_D_1b {δ γ πm : ℝ} (hπ : 0 < πm) (h1 : δ * (1 - γ) < 1) :
    πm ≤ πm / (2 * (1 - δ * (1 - γ))) ↔ 1 / 2 ≤ δ * (1 - γ) := by
  rw [le_div_iff₀ (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Exercise 12.D.1(c)** (MWG, p. 433). If it takes `K` periods to respond to a deviation, the
deviator earns `πᵐ` for `K` periods, `πᵐ(1 − δ^K)/(1 − δ)`; collusion is sustained iff
`δ^K ≥ 1/2`. -/
theorem exercise_12_D_1c {δ πm : ℝ} (hπ : 0 < πm) (hδ1 : δ < 1) (K : ℕ) :
    πm * (1 - δ ^ K) / (1 - δ) ≤ πm / (2 * (1 - δ)) ↔ 1 / 2 ≤ δ ^ K := by
  have h1δ : 0 < 1 - δ := by linarith
  rw [div_le_div_iff₀ h1δ (by linarith)]
  have e1 : πm * (1 - δ ^ K) * (2 * (1 - δ)) = (πm * (1 - δ)) * (2 * (1 - δ ^ K)) := by ring
  have hp := mul_pos hπ h1δ
  rw [e1]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left (show 1 < 2 * (1 - δ ^ K) by linarith) hp
    linarith
  · intro h
    have := mul_le_mul_of_nonneg_left (show 2 * (1 - δ ^ K) ≤ 1 by linarith) hp.le
    linarith

end MWG.MarketPower
