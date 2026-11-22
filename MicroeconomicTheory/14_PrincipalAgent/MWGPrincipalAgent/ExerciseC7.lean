/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Basic

/-!
# Exercise 14.C.7 (J. Tirole)

MWG, Exercise 14.C.7, p. 509.

A type-`θ` consumer buying `x ∈ [0, 1]` units for a total payment `T` gets `θ v(x) - T` with
`v(x) = (1 - (1 - x)²)/2 = x - x²/2`; `θ_L < θ_H`, a fraction `λ` of consumers is of type `θ_L`;
unit cost `c > 0`.

* `c7_demand`: at a linear price `p ∈ [0, θ]` a type-`θ` consumer buys `1 - p/θ`;
  `c7_surplus`: his surplus is `(θ - p)²/(2θ)`.
* `exercise_14_C_7a_theta`, `exercise_14_C_7a_lambda`: (a) the nondiscriminating monopolist serves
  both types (charges `p < θ_L`) if `θ_L > (θ_H + c)/2`, or if `λ (θ_L - c)²/θ_L >
  (1 - λ)(θ_H - c)²/θ_H` (true for `λ` near `1`); `exercise_14_C_7a_price`: the optimal price among
  those serving both.
* `exercise_14_C_7b`: (b) third-degree discrimination: `p_i = (θ_i + c)/2`.
* `exercise_14_C_7c`: (c) the optimal two-part tariff serving both types (when its profit is
  concave in `p`) has `p = cA/B > c` with `F = (θ_L - p)²/(2θ_L)`.
* `exercise_14_C_7d`: (d) the optimal nonlinear tariff: `x_H = 1 - c/θ_H` (efficient),
  `x_L = 1 - λc/K` with `K = λθ_L - (1 - λ)(θ_H - θ_L)`; `exercise_14_C_7d_compare`: the high type
  buys more than in (b) and (c), the low type less than efficiently.
-/

namespace MWG.PrincipalAgent

/-- `v(x) = x - x²/2`. -/
noncomputable def c7v (x : ℝ) : ℝ := x - x ^ 2 / 2

/-- Demand at a linear price `p ∈ [0, θ]` (MWG, Exercise 14.C.7(a)). -/
theorem c7_demand {θ p : ℝ} (hθ : 0 < θ) (x : ℝ) :
    θ * c7v x - p * x ≤ θ * c7v (1 - p / θ) - p * (1 - p / θ) := by
  have : θ * c7v (1 - p / θ) - p * (1 - p / θ) - (θ * c7v x - p * x) =
      θ / 2 * (x - (1 - p / θ)) ^ 2 := by
    unfold c7v; field_simp; ring
  nlinarith [sq_nonneg (x - (1 - p / θ))]

/-- The consumer's surplus at the price `p`: `(θ - p)²/(2θ)`. -/
theorem c7_surplus {θ p : ℝ} (hθ : 0 < θ) :
    θ * c7v (1 - p / θ) - p * (1 - p / θ) = (θ - p) ^ 2 / (2 * θ) := by
  unfold c7v; field_simp; ring

/-- Demand of a type-`θ` consumer at price `p` (zero when `p ≥ θ`). -/
noncomputable def c7D (θ p : ℝ) : ℝ := if p < θ then 1 - p / θ else 0

/-- The nondiscriminating monopolist's profit at price `p`. -/
noncomputable def c7Pi (θL θH lam c p : ℝ) : ℝ := (p - c) * (lam * c7D θL p + (1 - lam) * c7D θH p)

/-- The profit from one type at a price below its valuation is at most `(θ - c)²/(4θ)`. -/
theorem c7_one_type {θ c p : ℝ} (hθ : 0 < θ) : (p - c) * (1 - p / θ) ≤ (θ - c) ^ 2 / (4 * θ) := by
  have : (θ - c) ^ 2 / (4 * θ) - (p - c) * (1 - p / θ) = (p - (θ + c) / 2) ^ 2 / θ := by
    field_simp; ring
  have : 0 ≤ (p - (θ + c) / 2) ^ 2 / θ := by positivity
  linarith

/-- At prices `p ≥ θ_L` only high types buy, so profit is at most `(1 - λ)(θ_H - c)²/(4θ_H)`. -/
theorem c7_bound_high {θL θH lam c p : ℝ} (hL : 0 < θL) (hLH : θL < θH)
    (hl1 : lam ≤ 1) (hp : θL ≤ p) :
    c7Pi θL θH lam c p ≤ (1 - lam) * ((θH - c) ^ 2 / (4 * θH)) := by
  have hH : 0 < θH := hL.trans hLH
  have hDL : c7D θL p = 0 := by simp [c7D, not_lt.2 hp]
  unfold c7Pi; rw [hDL]
  have hb : 0 ≤ (θH - c) ^ 2 / (4 * θH) := by positivity
  unfold c7D
  split_ifs with h
  · have := c7_one_type (c := c) (p := p) hH
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 1 - lam)]
  · simp only [mul_zero, add_zero]; nlinarith

/-- **Exercise 14.C.7(a)** (MWG, p. 509), "`θ_L` large enough": if `θ_L > (θ_H + c)/2` the price
`(θ_H + c)/2` (optimal when selling to high types only) also sells to low types and beats every
price `p ≥ θ_L`; so every optimal price serves both types. -/
theorem exercise_14_C_7a_theta {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hθ : (θH + c) / 2 < θL) (p : ℝ) (hp : θL ≤ p) :
    c7Pi θL θH lam c p < c7Pi θL θH lam c ((θH + c) / 2) := by
  have hH : 0 < θH := hL.trans hLH
  have hb := c7_bound_high (c := c) hL hLH hl1.le hp
  have hp0 : (θH + c) / 2 < θH := by linarith
  have e : c7Pi θL θH lam c ((θH + c) / 2) = lam * (((θH + c) / 2 - c) * (1 - (θH + c) / 2 / θL)) +
      (1 - lam) * ((θH - c) ^ 2 / (4 * θH)) := by
    simp only [c7Pi, c7D, hθ, hp0, ↓reduceIte]
    field_simp; ring
  rw [e]
  have h1 : 0 < (θH + c) / 2 - c := by linarith
  have h2 : 0 < 1 - (θH + c) / 2 / θL := by rw [sub_pos, div_lt_one hL]; exact hθ
  nlinarith [mul_pos hl0 (mul_pos h1 h2)]

/-- **Exercise 14.C.7(a)** (MWG, p. 509), "`λ` large enough": if
`λ(θ_L - c)²/(4θ_L) > (1 - λ)(θ_H - c)²/(4θ_H)` (which holds for `λ` close to `1` when `c < θ_L`),
the price `(θ_L + c)/2` beats every price `p ≥ θ_L`. -/
theorem exercise_14_C_7a_lambda {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH)
    (hl1 : lam ≤ 1) (hc' : c < θL)
    (hcond : (1 - lam) * ((θH - c) ^ 2 / (4 * θH)) < lam * ((θL - c) ^ 2 / (4 * θL)))
    (p : ℝ) (hp : θL ≤ p) : c7Pi θL θH lam c p < c7Pi θL θH lam c ((θL + c) / 2) := by
  have hH : 0 < θH := hL.trans hLH
  have hb := c7_bound_high (c := c) hL hLH hl1 hp
  have hp1 : (θL + c) / 2 < θL := by linarith
  have hp2 : (θL + c) / 2 < θH := by linarith
  have e : c7Pi θL θH lam c ((θL + c) / 2) = lam * ((θL - c) ^ 2 / (4 * θL)) +
      (1 - lam) * (((θL + c) / 2 - c) * (1 - (θL + c) / 2 / θH)) := by
    simp only [c7Pi, c7D, hp1, hp2, ↓reduceIte]
    field_simp; ring
  rw [e]
  have h1 : 0 < (θL + c) / 2 - c := by linarith
  have h2 : 0 < 1 - (θL + c) / 2 / θH := by rw [sub_pos, div_lt_one hH]; exact hp2
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - lam) (mul_pos h1 h2).le]

/-- **Exercise 14.C.7(a)**, the price when both types are served (MWG, p. 509): among prices
`p ≤ θ_L` the profit is `(p - c)(1 - pA)` with `A = λ/θ_L + (1 - λ)/θ_H`, maximized at
`p* = (1/A + c)/2` (when `p* ≤ θ_L`). -/
theorem exercise_14_C_7a_price {A c p : ℝ} (hA : 0 < A) :
    (p - c) * (1 - p * A) ≤ ((1 / A + c) / 2 - c) * (1 - (1 / A + c) / 2 * A) := by
  have : ((1 / A + c) / 2 - c) * (1 - (1 / A + c) / 2 * A) - (p - c) * (1 - p * A) =
      A * (p - (1 / A + c) / 2) ^ 2 := by field_simp; ring
  nlinarith [mul_nonneg hA.le (sq_nonneg (p - (1 / A + c) / 2))]

/-- **Exercise 14.C.7(b)** (MWG, p. 509). Charging `θ_i`-consumers `p_i = (θ_i + c)/2` is optimal
for a monopolist who can tell the types apart (but charges linear prices). -/
theorem exercise_14_C_7b {θ c : ℝ} (hθ : 0 < θ) (p : ℝ) :
    (p - c) * (1 - p / θ) ≤ ((θ + c) / 2 - c) * (1 - (θ + c) / 2 / θ) := by
  have h := c7_one_type (c := c) (p := p) hθ
  have : ((θ + c) / 2 - c) * (1 - (θ + c) / 2 / θ) = (θ - c) ^ 2 / (4 * θ) := by
    field_simp; ring
  linarith

/-- **Exercise 14.C.7(c)** (MWG, p. 509). The two-part tariff `(F, p)` serving both types sets
`F = (θ_L - p)²/(2θ_L)` (the low type's surplus); its profit
`(θ_L - p)²/(2θ_L) + (p - c)(1 - pA)` is concave in `p` iff `B = 2A - 1/θ_L > 0`, and then it is
maximized at `p* = cA/B`, which exceeds marginal cost `c` (high types buy more, so the unit price
extracts some of their surplus). -/
theorem exercise_14_C_7c {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hl1 : lam < 1)
    (hc : 0 < c) (hB : 0 < 2 * (lam / θL + (1 - lam) / θH) - 1 / θL) (p : ℝ) :
    let A := lam / θL + (1 - lam) / θH
    let B := 2 * A - 1 / θL
    (θL - p) ^ 2 / (2 * θL) + (p - c) * (1 - p * A) ≤
        (θL - c * A / B) ^ 2 / (2 * θL) + (c * A / B - c) * (1 - c * A / B * A) ∧
      c < c * A / B := by
  intro A B
  have hH : 0 < θH := hL.trans hLH
  have hf : ∀ q, (θL - q) ^ 2 / (2 * θL) + (q - c) * (1 - q * A) =
      θL / 2 - c - B / 2 * q ^ 2 + c * A * q := by
    intro q; simp only [B]; field_simp; ring
  have hAL : A < 1 / θL := by
    have h1 : (1 - lam) / θH < (1 - lam) / θL := div_lt_div_of_pos_left (by linarith) hL hLH
    have h2 : lam / θL + (1 - lam) / θL = 1 / θL := by field_simp; ring
    simp only [A]; linarith
  have hBA : B < A := by simp only [B]; linarith
  have hB' : 0 < B := hB
  clear_value A B
  refine ⟨?_, ?_⟩
  · rw [hf, hf]
    have : -(B / 2) * (c * A / B) ^ 2 + c * A * (c * A / B) - (-(B / 2) * p ^ 2 + c * A * p) =
        B / 2 * (p - c * A / B) ^ 2 := by field_simp; ring
    nlinarith [mul_nonneg hB'.le (sq_nonneg (p - c * A / B))]
  · rw [lt_div_iff₀ hB']
    nlinarith

/-- The nonlinear tariff of part (d): quantities `x_H, x_L ∈ [0, 1]` and payments. -/
def C7Feas (θL θH xH TH xL TL : ℝ) : Prop :=
  0 ≤ xH ∧ xH ≤ 1 ∧ 0 ≤ xL ∧ xL ≤ 1 ∧ 0 ≤ θL * c7v xL - TL ∧ 0 ≤ θH * c7v xH - TH ∧
    θH * c7v xL - TL ≤ θH * c7v xH - TH ∧ θL * c7v xH - TH ≤ θL * c7v xL - TL

/-- The monopolist's profit from a nonlinear tariff. -/
def c7Profit (lam c xH TH xL TL : ℝ) : ℝ := lam * (TL - c * xL) + (1 - lam) * (TH - c * xH)

/-- **Exercise 14.C.7(d)** (MWG, p. 509). The fully optimal nonlinear tariff: with
`K = λθ_L - (1 - λ)(θ_H - θ_L) > λc` and `c ≤ θ_H`, the menu `x_H = 1 - c/θ_H`,
`x_L = 1 - λc/K`, `T_L = θ_L v(x_L)`, `T_H = θ_H v(x_H) - (θ_H - θ_L) v(x_L)` is feasible and earns
at least as much as every feasible menu. -/
theorem exercise_14_C_7d {θL θH lam c : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hc : 0 < c) (hcH : c ≤ θH)
    (hK : lam * c < lam * θL - (1 - lam) * (θH - θL)) :
    let K := lam * θL - (1 - lam) * (θH - θL)
    let xH := 1 - c / θH
    let xL := 1 - lam * c / K
    let TL := θL * c7v xL
    let TH := θH * c7v xH - (θH - θL) * c7v xL
    C7Feas θL θH xH TH xL TL ∧
      ∀ xH' TH' xL' TL', C7Feas θL θH xH' TH' xL' TL' →
        c7Profit lam c xH' TH' xL' TL' ≤ c7Profit lam c xH TH xL TL := by
  intro K xH xL TL TH
  have hH : 0 < θH := hL.trans hLH
  have hKpos : 0 < K := by
    have : 0 < lam * c := mul_pos hl0 hc
    simp only [K]; linarith
  have hxH0 : 0 ≤ xH := by simp only [xH]; rw [sub_nonneg, div_le_one hH]; exact hcH
  have hxH1 : xH ≤ 1 := by
    have : 0 ≤ c / θH := by positivity
    simp only [xH]; linarith
  have hxL0 : 0 ≤ xL := by
    simp only [xL]; rw [sub_nonneg, div_le_one hKpos]; exact hK.le
  have hxL1 : xL ≤ 1 := by
    have : 0 ≤ lam * c / K := by positivity
    simp only [xL]; linarith
  have hord : xL ≤ xH := by
    simp only [xL, xH]
    have : c / θH ≤ lam * c / K := by
      rw [div_le_div_iff₀ hH hKpos]
      have : K ≤ lam * θH := by simp only [K]; nlinarith
      nlinarith
    linarith
  have hvmono : c7v xL ≤ c7v xH := by unfold c7v; nlinarith
  refine ⟨⟨hxH0, hxH1, hxL0, hxL1, by simp only [TL]; linarith, ?_, ?_, ?_⟩, ?_⟩
  · simp only [TH]
    have : 0 ≤ c7v xL := by unfold c7v; nlinarith
    nlinarith
  · simp only [TH, TL]; nlinarith
  · simp only [TH, TL]; nlinarith
  · intro xH' TH' xL' TL' hf
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    -- the bound from (i) and (iii)
    have hTL : TL' ≤ θL * c7v xL' := by linarith
    have hTH : TH' ≤ θH * c7v xH' - (θH - θL) * c7v xL' := by linarith
    have bound : c7Profit lam c xH' TH' xL' TL' ≤
        (1 - lam) * (θH * c7v xH' - c * xH') +
          (lam * (θL * c7v xL' - c * xL') - (1 - lam) * (θH - θL) * c7v xL') := by
      unfold c7Profit
      nlinarith [mul_le_mul_of_nonneg_left hTL hl0.le,
        mul_le_mul_of_nonneg_left hTH (by linarith : (0:ℝ) ≤ 1 - lam)]
    have eqv : c7Profit lam c xH TH xL TL =
        (1 - lam) * (θH * c7v xH - c * xH) +
          (lam * (θL * c7v xL - c * xL) - (1 - lam) * (θH - θL) * c7v xL) := by
      unfold c7Profit; simp only [TH, TL]; ring
    -- both pieces are maximized at the candidate (completing squares)
    have hSH : θH * c7v xH' - c * xH' ≤ θH * c7v xH - c * xH := by
      have : θH * c7v xH - c * xH - (θH * c7v xH' - c * xH') = θH / 2 * (xH' - xH) ^ 2 := by
        simp only [xH]; unfold c7v; field_simp; ring
      nlinarith [mul_nonneg hH.le (sq_nonneg (xH' - xH))]
    have hQ : lam * (θL * c7v xL' - c * xL') - (1 - lam) * (θH - θL) * c7v xL' ≤
        lam * (θL * c7v xL - c * xL) - (1 - lam) * (θH - θL) * c7v xL := by
      have : lam * (θL * c7v xL - c * xL) - (1 - lam) * (θH - θL) * c7v xL -
          (lam * (θL * c7v xL' - c * xL') - (1 - lam) * (θH - θL) * c7v xL') =
            K / 2 * (xL' - xL) ^ 2 := by
        have hK0 : K ≠ 0 := hKpos.ne'
        simp only [xL]; unfold c7v; field_simp; simp only [K]; ring
      nlinarith [mul_nonneg hKpos.le (sq_nonneg (xL' - xL))]
    rw [eqv]
    nlinarith [mul_le_mul_of_nonneg_left hSH (by linarith : (0:ℝ) ≤ 1 - lam)]

/-- **Exercise 14.C.7(d)**, comparing quantities (MWG, p. 509). The high type's quantity
`1 - c/θ_H` under the optimal nonlinear tariff exceeds his quantity under third-degree
discrimination (`(θ_H - c)/(2θ_H)`) and is at least that under a two-part tariff with unit price
`p ≥ c`; the low type's quantity `1 - λc/K` is below the efficient `1 - c/θ_L`. -/
theorem exercise_14_C_7d_compare {θL θH lam c p : ℝ} (hL : 0 < θL) (hLH : θL < θH)
    (hl1 : lam < 1) (hc : 0 < c) (hcH : c < θH) (hp : c ≤ p)
    (hK : 0 < lam * θL - (1 - lam) * (θH - θL)) :
    (θH - c) / (2 * θH) < 1 - c / θH ∧ 1 - p / θH ≤ 1 - c / θH ∧
      1 - lam * c / (lam * θL - (1 - lam) * (θH - θL)) < 1 - c / θL := by
  have hH : 0 < θH := hL.trans hLH
  refine ⟨?_, ?_, ?_⟩
  · have e : (θH - c) / (2 * θH) = 1 - c / θH - (θH - c) / (2 * θH) := by field_simp; ring
    have : 0 < (θH - c) / (2 * θH) := div_pos (by linarith) (by positivity)
    linarith
  · have := div_le_div_of_nonneg_right hp hH.le; linarith
  · have : c / θL < lam * c / (lam * θL - (1 - lam) * (θH - θL)) := by
      rw [div_lt_div_iff₀ hL hK]
      nlinarith [mul_pos (mul_pos hc (by linarith : (0:ℝ) < 1 - lam)) (sub_pos.2 hLH)]
    linarith

end MWG.PrincipalAgent
