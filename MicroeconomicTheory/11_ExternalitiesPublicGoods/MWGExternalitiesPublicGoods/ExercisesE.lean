/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.PrivateInfo
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Exercises 11.E.1, 11.E.2 and 11.E.7 (MWG, pp. 381-382)

* **Exercise 11.E.1** (Weitzman's prices versus quantities). `∂π/∂h = β - bh + θ`,
  `∂φ/∂h = γ - ch + η` (`lqπ`, `lqφ`), `E[θ] = E[η] = E[θη] = 0`, `E[θ²] = σ_θ²`. (a) The best quota
  is `ĥ* = (β + γ)/(b + c)` (`exercise_11_E_1a`); (b) under a tax `t` the firm produces
  `(β - t + θ)/b` (`lq_tax_response`), and the best tax is `t* = (cβ - bγ)/(b + c)`
  (`exercise_11_E_1b`); (c) the tax beats the quota by `σ_θ²(b - c)/(2b²)`: the tax is better iff
  `b > c` (when `σ_θ² > 0`), and `σ_η²` is irrelevant (`exercise_11_E_1c`). As in the text's
  linear-quadratic analysis, the levels are not constrained to be nonnegative (departure).
* **Exercise 11.E.2**: two firms with shocks `θ₁, θ₂` (variances `σ₁², σ₂²`, covariance `σ₁₂`) and a
  consumer harmed by the total. The best uniform quota and tax (`exercise_11_E_2`), and the tax
  beats the quota by `((b - c)(σ₁² + σ₂²) - 2cσ₁₂)/(2b²)`, decreasing in `σ₁₂`
  (`exercise_11_E_2_compare`).
* **Exercise 11.E.7**: with the consumer's type known, a nonlinear tax whose total is
  `-φ(h, η̄)` (plus any constant) makes the firm maximize aggregate surplus for every `θ`
  (`exercise_11_E_7`). MWG prints `φ(h, η̄)`; that schedule fails (`exercise_11_E_7_printed`,
  correction).
-/

namespace MWG.ExternalitiesPublicGoods

open MeasureTheory

/-! ## Expectations of quadratic polynomials -/

/-- **Expectation of a quadratic polynomial** in shocks `θ₁, θ₂, η`: by linearity,
`E[A + B₁θ₁ + B₂θ₂ + Cη + D₁θ₁² + D₂θ₂² + D₁₂θ₁θ₂ + E₁θ₁η + E₂θ₂η]` is the same combination of the
moments. -/
theorem quad_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ₁ θ₂ η : Ω → ℝ} (i1 : Integrable θ₁ μ) (i2 : Integrable θ₂ μ) (i3 : Integrable η μ)
    (i11 : Integrable (fun ω => θ₁ ω ^ 2) μ) (i22 : Integrable (fun ω => θ₂ ω ^ 2) μ)
    (i12 : Integrable (fun ω => θ₁ ω * θ₂ ω) μ) (i13 : Integrable (fun ω => θ₁ ω * η ω) μ)
    (i23 : Integrable (fun ω => θ₂ ω * η ω) μ) (A B₁ B₂ C D₁ D₂ D₁₂ E₁ E₂ : ℝ) :
    ∫ ω, (A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 + D₂ * θ₂ ω ^ 2 +
      D₁₂ * (θ₁ ω * θ₂ ω) + E₁ * (θ₁ ω * η ω) + E₂ * (θ₂ ω * η ω)) ∂μ =
    A + B₁ * ∫ ω, θ₁ ω ∂μ + B₂ * ∫ ω, θ₂ ω ∂μ + C * ∫ ω, η ω ∂μ +
      D₁ * ∫ ω, θ₁ ω ^ 2 ∂μ + D₂ * ∫ ω, θ₂ ω ^ 2 ∂μ + D₁₂ * ∫ ω, θ₁ ω * θ₂ ω ∂μ +
      E₁ * ∫ ω, θ₁ ω * η ω ∂μ + E₂ * ∫ ω, θ₂ ω * η ω ∂μ := by
  have c0 : Integrable (fun _ : Ω => A) μ := integrable_const A
  have j1 := i1.const_mul B₁
  have j2 := i2.const_mul B₂
  have j3 := i3.const_mul C
  have j11 := i11.const_mul D₁
  have j22 := i22.const_mul D₂
  have j12 := i12.const_mul D₁₂
  have j13 := i13.const_mul E₁
  have j23 := i23.const_mul E₂
  have k1 : Integrable (fun ω => A + B₁ * θ₁ ω) μ := c0.add j1
  have k2 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω) μ := k1.add j2
  have k3 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω) μ := k2.add j3
  have k4 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2) μ :=
    k3.add j11
  have k5 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 +
      D₂ * θ₂ ω ^ 2) μ := k4.add j22
  have k6 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 +
      D₂ * θ₂ ω ^ 2 + D₁₂ * (θ₁ ω * θ₂ ω)) μ := k5.add j12
  have k7 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 +
      D₂ * θ₂ ω ^ 2 + D₁₂ * (θ₁ ω * θ₂ ω) + E₁ * (θ₁ ω * η ω)) μ := k6.add j13
  rw [integral_add k7 j23, integral_add k6 j13, integral_add k5 j12, integral_add k4 j22,
    integral_add k3 j11, integral_add k2 j3, integral_add k1 j2, integral_add c0 j1]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul]

/-! ## Exercise 11.E.1 -/

/-- The firm's derived profit of Exercise 11.E.1: `π(h, θ) = βh - bh²/2 + θh`, so that
`∂π/∂h = β - bh + θ`. -/
noncomputable def lqπ (β b θ h : ℝ) : ℝ := β * h - b * h ^ 2 / 2 + θ * h

/-- The consumer's derived utility of Exercise 11.E.1: `φ(h, η) = γh - ch²/2 + ηh`, so that
`∂φ/∂h = γ - ch + η`. -/
noncomputable def lqφ (γ c η h : ℝ) : ℝ := γ * h - c * h ^ 2 / 2 + η * h

/-- Under a per-unit tax `t`, the firm's surplus-maximizing response is `h = (β - t + θ)/b`. -/
theorem lq_tax_response {β b θ t : ℝ} (hb : 0 < b) (y : ℝ) :
    lqπ β b θ y - t * y ≤ lqπ β b θ ((β - t + θ) / b) - t * ((β - t + θ) / b) := by
  simp only [lqπ]
  have key : β * y - b * y ^ 2 / 2 + θ * y - t * y = (β - t + θ) ^ 2 / (2 * b) -
      b / 2 * (y - (β - t + θ) / b) ^ 2 := by field_simp; ring
  have key2 : β * ((β - t + θ) / b) - b * ((β - t + θ) / b) ^ 2 / 2 + θ * ((β - t + θ) / b) -
      t * ((β - t + θ) / b) = (β - t + θ) ^ 2 / (2 * b) := by field_simp; ring
  rw [key, key2]
  nlinarith [sq_nonneg (y - (β - t + θ) / b)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Exercise 11.E.1(a)** (MWG, p. 381). With a quota the firm produces exactly `ĥ`; the expected
aggregate surplus is `(β + γ)ĥ - (b + c)ĥ²/2`, maximized by `ĥ* = (β + γ)/(b + c)`. -/
theorem exercise_11_E_1a {θ η : Ω → ℝ} (i1 : Integrable θ μ) (i3 : Integrable η μ)
    (i11 : Integrable (fun ω => θ ω ^ 2) μ) (i13 : Integrable (fun ω => θ ω * η ω) μ)
    (hθ : ∫ ω, θ ω ∂μ = 0) (hη : ∫ ω, η ω ∂μ = 0) {β b γ c : ℝ} (hbc : 0 < b + c) (hq : ℝ) :
    ∫ ω, (lqπ β b (θ ω) hq + lqφ γ c (η ω) hq) ∂μ = (β + γ) * hq - (b + c) * hq ^ 2 / 2 ∧
      (β + γ) * hq - (b + c) * hq ^ 2 / 2 ≤
        (β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 := by
  have hz : Integrable (fun _ : Ω => (0 : ℝ)) μ := integrable_const 0
  have e := quad_integral (μ := μ) i1 hz i3 i11 (by simp) (by simp) i13 (by simp)
    ((β + γ) * hq - (b + c) * hq ^ 2 / 2) hq 0 hq 0 0 0 0 0
  refine ⟨?_, ?_⟩
  · have : (fun ω => lqπ β b (θ ω) hq + lqφ γ c (η ω) hq) = fun ω =>
        (β + γ) * hq - (b + c) * hq ^ 2 / 2 + hq * θ ω + 0 * (0 : ℝ) + hq * η ω +
          0 * θ ω ^ 2 + 0 * (0 : ℝ) ^ 2 + 0 * (θ ω * 0) + 0 * (θ ω * η ω) + 0 * (0 * η ω) := by
      funext ω; simp only [lqπ, lqφ]; ring
    rw [this, e, hθ, hη]; ring
  · have key : (β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 -
        ((β + γ) * hq - (b + c) * hq ^ 2 / 2) = (b + c) / 2 * (hq - (β + γ) / (b + c)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (hq - (β + γ) / (b + c))]

/-- The expected surplus under a tax `t` (Exercise 11.E.1(b)): with `m = (β - t)/b`,
`E[S] = (β + γ)m - (b + c)m²/2 + σ_θ²(b - c)/(2b²)`. -/
theorem exercise_11_E_1_tax_value {θ η : Ω → ℝ} (i1 : Integrable θ μ) (i3 : Integrable η μ)
    (i11 : Integrable (fun ω => θ ω ^ 2) μ) (i13 : Integrable (fun ω => θ ω * η ω) μ)
    (hθ : ∫ ω, θ ω ∂μ = 0) (hη : ∫ ω, η ω ∂μ = 0) (hθη : ∫ ω, θ ω * η ω ∂μ = 0)
    {β b γ c σ2 : ℝ} (hσ : ∫ ω, θ ω ^ 2 ∂μ = σ2) (hb : 0 < b) (t : ℝ) :
    ∫ ω, (lqπ β b (θ ω) ((β - t + θ ω) / b) + lqφ γ c (η ω) ((β - t + θ ω) / b)) ∂μ =
      (β + γ) * ((β - t) / b) - (b + c) * ((β - t) / b) ^ 2 / 2 + σ2 * (b - c) / (2 * b ^ 2) := by
  have hz : Integrable (fun _ : Ω => (0 : ℝ)) μ := integrable_const 0
  set m := (β - t) / b
  have e := quad_integral (μ := μ) i1 hz i3 i11 (by simp) (by simp) i13
    (by simp) ((β + γ) * m - (b + c) * m ^ 2 / 2)
    ((β + γ) / b - (b + c) * m / b + m) 0 m ((b - c) / (2 * b ^ 2)) 0 0 (1 / b) 0
  have : (fun ω => lqπ β b (θ ω) ((β - t + θ ω) / b) + lqφ γ c (η ω) ((β - t + θ ω) / b)) =
      fun ω => (β + γ) * m - (b + c) * m ^ 2 / 2 + ((β + γ) / b - (b + c) * m / b + m) * θ ω +
        0 * (0 : ℝ) + m * η ω + (b - c) / (2 * b ^ 2) * θ ω ^ 2 + 0 * (0 : ℝ) ^ 2 +
        0 * (θ ω * 0) + 1 / b * (θ ω * η ω) + 0 * (0 * η ω) := by
    funext ω; simp only [lqπ, lqφ, m]; field_simp; ring
  rw [this, e, hθ, hη, hθη, hσ]; ring

/-- **Exercise 11.E.1(b)** (MWG, p. 381). The best tax is `t* = (cβ - bγ)/(b + c)` (the tax at which
the expected level `(β - t)/b` equals the best quota): for every `t`, the expected surplus is at
most that at `t*`. -/
theorem exercise_11_E_1b {β b γ c σ2 : ℝ} (hb : 0 < b) (hbc : 0 < b + c) (t : ℝ) :
    (β + γ) * ((β - t) / b) - (b + c) * ((β - t) / b) ^ 2 / 2 + σ2 * (b - c) / (2 * b ^ 2) ≤
      (β + γ) * ((β - (c * β - b * γ) / (b + c)) / b) -
        (b + c) * ((β - (c * β - b * γ) / (b + c)) / b) ^ 2 / 2 + σ2 * (b - c) / (2 * b ^ 2) ∧
      (β - (c * β - b * γ) / (b + c)) / b = (β + γ) / (b + c) := by
  have hm : (β - (c * β - b * γ) / (b + c)) / b = (β + γ) / (b + c) := by
    field_simp; ring
  refine ⟨?_, hm⟩
  rw [hm]
  have key : (β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 -
      ((β + γ) * ((β - t) / b) - (b + c) * ((β - t) / b) ^ 2 / 2) =
        (b + c) / 2 * ((β - t) / b - (β + γ) / (b + c)) ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg ((β - t) / b - (β + γ) / (b + c))]

/-- **Exercise 11.E.1(c)** (MWG, p. 381). At their best levels the tax yields
`σ_θ²(b - c)/(2b²)` more expected surplus than the quota: the tax is better iff `b > c` (the
consumer's marginal cost is flatter than the firm's marginal benefit), the quota iff `b < c`;
the consumer's shock variance `σ_η²` plays no role. -/
theorem exercise_11_E_1c {β b γ c σ2 : ℝ} (hb : 0 < b) (hσ : 0 < σ2) :
    ((β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 +
        σ2 * (b - c) / (2 * b ^ 2)) -
      ((β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2) =
        σ2 * (b - c) / (2 * b ^ 2) ∧
      (0 < σ2 * (b - c) / (2 * b ^ 2) ↔ c < b) := by
  refine ⟨by ring, ?_⟩
  rw [div_pos_iff_of_pos_right (by positivity)]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith
  · intro h; nlinarith

/-! ## Exercise 11.E.2 -/

/-- **Exercise 11.E.2** (MWG, p. 381), expected surplus. Firms `i = 1, 2` with
`∂πᵢ/∂hᵢ = β - bhᵢ + θᵢ`, the consumer with `∂φ/∂H = γ - cH + η` (`H = h₁ + h₂`); shocks with zero
means, `E[θᵢη] = 0`, `E[θᵢ²] = σᵢ²`, `E[θ₁θ₂] = σ₁₂`. A uniform quota `ĥ` gives
`2(β + γ)ĥ - (b + 2c)ĥ²`; a uniform tax with `m = (β - t)/b` gives
`2(β + γ)m - (b + 2c)m² + (σ₁² + σ₂²)/(2b) - c(σ₁² + σ₂² + 2σ₁₂)/(2b²)`. -/
theorem exercise_11_E_2 {θ₁ θ₂ η : Ω → ℝ} (i1 : Integrable θ₁ μ) (i2 : Integrable θ₂ μ)
    (i3 : Integrable η μ) (i11 : Integrable (fun ω => θ₁ ω ^ 2) μ)
    (i22 : Integrable (fun ω => θ₂ ω ^ 2) μ) (i12 : Integrable (fun ω => θ₁ ω * θ₂ ω) μ)
    (i13 : Integrable (fun ω => θ₁ ω * η ω) μ) (i23 : Integrable (fun ω => θ₂ ω * η ω) μ)
    (h1 : ∫ ω, θ₁ ω ∂μ = 0) (h2 : ∫ ω, θ₂ ω ∂μ = 0) (h3 : ∫ ω, η ω ∂μ = 0)
    (h13 : ∫ ω, θ₁ ω * η ω ∂μ = 0) (h23 : ∫ ω, θ₂ ω * η ω ∂μ = 0)
    {β b γ c s1 s2 s12 : ℝ} (hs1 : ∫ ω, θ₁ ω ^ 2 ∂μ = s1) (hs2 : ∫ ω, θ₂ ω ^ 2 ∂μ = s2)
    (hs12 : ∫ ω, θ₁ ω * θ₂ ω ∂μ = s12) (hb : 0 < b) (hq t : ℝ) :
    ∫ ω, (lqπ β b (θ₁ ω) hq + lqπ β b (θ₂ ω) hq + lqφ γ c (η ω) (hq + hq)) ∂μ =
        2 * (β + γ) * hq - (b + 2 * c) * hq ^ 2 ∧
      ∫ ω, (lqπ β b (θ₁ ω) ((β - t + θ₁ ω) / b) + lqπ β b (θ₂ ω) ((β - t + θ₂ ω) / b) +
          lqφ γ c (η ω) ((β - t + θ₁ ω) / b + (β - t + θ₂ ω) / b)) ∂μ =
        2 * (β + γ) * ((β - t) / b) - (b + 2 * c) * ((β - t) / b) ^ 2 + (s1 + s2) / (2 * b) -
          c * (s1 + s2 + 2 * s12) / (2 * b ^ 2) := by
  constructor
  · have e := quad_integral (μ := μ) i1 i2 i3 i11 i22 i12 i13 i23
      (2 * (β + γ) * hq - (b + 2 * c) * hq ^ 2) hq hq (2 * hq) 0 0 0 0 0
    have : (fun ω => lqπ β b (θ₁ ω) hq + lqπ β b (θ₂ ω) hq + lqφ γ c (η ω) (hq + hq)) =
        fun ω => 2 * (β + γ) * hq - (b + 2 * c) * hq ^ 2 + hq * θ₁ ω + hq * θ₂ ω +
          2 * hq * η ω + 0 * θ₁ ω ^ 2 + 0 * θ₂ ω ^ 2 + 0 * (θ₁ ω * θ₂ ω) + 0 * (θ₁ ω * η ω) +
          0 * (θ₂ ω * η ω) := by
      funext ω; simp only [lqπ, lqφ]; ring
    rw [this, e, h1, h2, h3]; ring
  · set m := (β - t) / b
    have e := quad_integral (μ := μ) i1 i2 i3 i11 i22 i12 i13 i23
      (2 * (β + γ) * m - (b + 2 * c) * m ^ 2) (β / b + m - 2 * c * m / b + γ / b - b * m / b)
      (β / b + m - 2 * c * m / b + γ / b - b * m / b) (2 * m)
      (1 / b - 1 / (2 * b) - c / (2 * b ^ 2)) (1 / b - 1 / (2 * b) - c / (2 * b ^ 2))
      (-(c / b ^ 2)) (1 / b) (1 / b)
    have : (fun ω => lqπ β b (θ₁ ω) ((β - t + θ₁ ω) / b) + lqπ β b (θ₂ ω) ((β - t + θ₂ ω) / b) +
        lqφ γ c (η ω) ((β - t + θ₁ ω) / b + (β - t + θ₂ ω) / b)) =
        fun ω => 2 * (β + γ) * m - (b + 2 * c) * m ^ 2 +
          (β / b + m - 2 * c * m / b + γ / b - b * m / b) * θ₁ ω +
          (β / b + m - 2 * c * m / b + γ / b - b * m / b) * θ₂ ω + 2 * m * η ω +
          (1 / b - 1 / (2 * b) - c / (2 * b ^ 2)) * θ₁ ω ^ 2 +
          (1 / b - 1 / (2 * b) - c / (2 * b ^ 2)) * θ₂ ω ^ 2 + -(c / b ^ 2) * (θ₁ ω * θ₂ ω) +
          1 / b * (θ₁ ω * η ω) + 1 / b * (θ₂ ω * η ω) := by
      funext ω; simp only [lqπ, lqφ, m]; field_simp; ring
    rw [this, e, h1, h2, h3, h13, h23, hs1, hs2, hs12]
    field_simp
    ring

/-- **Exercise 11.E.2**, the comparison. The best uniform quota and the best uniform tax both set
the expected level `(β + γ)/(b + 2c)`; the tax then beats the quota by
`((b - c)(σ₁² + σ₂²) - 2cσ₁₂)/(2b²)`, which decreases in the covariance `σ₁₂`: the less correlated
the shocks, the better the tax looks. -/
theorem exercise_11_E_2_compare {β b γ c s1 s2 s12 : ℝ} (hb : 0 < b) (hc : 0 < c) (x : ℝ) :
    2 * (β + γ) * x - (b + 2 * c) * x ^ 2 ≤
        2 * (β + γ) * ((β + γ) / (b + 2 * c)) - (b + 2 * c) * ((β + γ) / (b + 2 * c)) ^ 2 ∧
      ((s1 + s2) / (2 * b) - c * (s1 + s2 + 2 * s12) / (2 * b ^ 2) =
        ((b - c) * (s1 + s2) - 2 * c * s12) / (2 * b ^ 2)) ∧
      ∀ s12' : ℝ, s12 < s12' →
        ((b - c) * (s1 + s2) - 2 * c * s12') / (2 * b ^ 2) <
          ((b - c) * (s1 + s2) - 2 * c * s12) / (2 * b ^ 2) := by
  refine ⟨?_, by field_simp; ring, fun s12' hs => ?_⟩
  · have key : 2 * (β + γ) * ((β + γ) / (b + 2 * c)) - (b + 2 * c) * ((β + γ) / (b + 2 * c)) ^ 2 -
        (2 * (β + γ) * x - (b + 2 * c) * x ^ 2) =
          (b + 2 * c) * (x - (β + γ) / (b + 2 * c)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (x - (β + γ) / (b + 2 * c))]
  · rw [div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith

/-- An instance of the moment hypotheses: two equally likely states with `θ = ±1` (and `η = 0`):
`E[θ] = 0`, `E[θ²] = 1`. -/
theorem exercise_11_E_moments_instance :
    let μ : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
    IsProbabilityMeasure μ ∧ ∫ ω, (if ω then (1 : ℝ) else -1) ∂μ = 0 ∧
      ∫ ω, (if ω then (1 : ℝ) else -1) ^ 2 ∂μ = 1 := by
  intro μ
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [integral_fintype]
    · simp [μ, Measure.real]
    · exact Integrable.of_finite
  · rw [integral_fintype]
    · simp [μ, Measure.real]
    · exact Integrable.of_finite

/-! ## Exercise 11.E.7 -/

/-- **Exercise 11.E.7** (MWG, p. 382), corrected. With the consumer's type known
(`φ(h) = φ(h, η̄)`),
if the firm pays the total tax `T(h) = k - φ(h)` (any constant `k`; `k = φ(0)` makes it
nonnegative for a negative externality), then for every `θ` the firm's choices are exactly the
surplus-maximizing levels. -/
theorem exercise_11_E_7 (pr : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (k θ h : ℝ) :
    (0 ≤ h ∧ ∀ y, 0 ≤ y → pr θ y - (k - φ y) ≤ pr θ h - (k - φ h)) ↔
      (0 ≤ h ∧ ∀ y, 0 ≤ y → φ y + pr θ y ≤ φ h + pr θ h) := by
  constructor
  · rintro ⟨h0, hm⟩; exact ⟨h0, fun y hy => by linarith [hm y hy]⟩
  · rintro ⟨h0, hm⟩; exact ⟨h0, fun y hy => by linarith [hm y hy]⟩

/-- **Correction to Exercise 11.E.7**: the printed schedule `T(h) = φ(h, η̄)` fails. With
`π(h, θ) = θh - h²/2` and `φ(h) = -h` (`∂φ/∂h = -1`), the firm facing `T(h) = φ(h)` chooses
`h = θ + 1`, while aggregate surplus is maximized at `max(θ - 1, 0)`: for every `θ > -1` the levels
differ. -/
theorem exercise_11_E_7_printed (θ : ℝ) (hθ : -1 < θ) :
    IsTaxChoice' (fun h => θ * h - h ^ 2 / 2) (-1) (θ + 1) ∧
      IsTaxChoice' (fun h => θ * h - h ^ 2 / 2) 1 (max (θ - 1) 0) ∧
      θ + 1 ≠ max (θ - 1) 0 := by
  refine ⟨(lq_tax_choice θ (-1) _).2 (by rw [max_eq_left (by linarith)]; ring),
    (lq_tax_choice θ 1 _).2 rfl, fun h => ?_⟩
  rcases le_total (θ - 1) 0 with h1 | h1
  · rw [max_eq_right h1] at h; linarith
  · rw [max_eq_left h1] at h; linarith

end MWG.ExternalitiesPublicGoods
