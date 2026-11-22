/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Euler
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Examples of Euler equations (MWG Examples 20.D.2-20.D.4, Exercises 20.D.5 and 20.D.7)

MWG, Chapter 20, pp. 750-753, Exercises 20.D.5 and 20.D.7 (p. 784), footnote 17. One capital
good: `K = ℝ`.

* **Example 20.D.2** (Ramsey-Solow, `u(k, k') = û(F(k) - k')`): the derivative of `u`
  (`example_20_D_2_deriv`) and the Euler equations `û'(c_t) / (δ û'(c_{t+1})) = F'(k_t)`
  (`example_20_D_2`, `example_20_D_2_ratio`).
* **Example 20.D.3** (cost of adjustment): the Euler equations (`example_20_D_3`) and, iterating,
  `1 + γ'(k₁ - k₀) = ∑_{t ≥ 1} δ^t (F'(k_t) - 1)` (`example_20_D_3_iterated`).
* **Exercise 20.D.5**: `F(k) = k^α`, `γ(x) = (max x 0)^β`; the derivatives
  (`exercise_20_D_5_gamma_deriv_*`, `exercise_20_D_5_F_deriv`) and the steady state
  `k* = (αδ)^{1/(1-α)}` (`exercise_20_D_5_steady_state`).
* **Example 20.D.4** and **Exercise 20.D.7** (`u = ln(2k - k')`, `δ = 1/2`): the Euler equations
  are `k_{t+1} = 3k_t - 2k_{t-1}` (`exercise_20_D_7_euler`), solved by
  `k_t = k₀ + (k₁ - k₀)(2^t - 1)` (`exercise_20_D_7_solution`, `exercise_20_D_7_unique`); the
  claims about `k₁ < k₀`, `k₁ > k₀`, constant consumption and non-optimality
  (`example_20_D_4_*`), optimality of `k₁ = k₀` by Proposition 20.D.7
  (`example_20_D_4_optimal`), and footnote 17 (`footnote_20_17`).

Correction: for `k₁ ≥ 2k₀` the path of Example 20.D.4 is not feasible (consumption
`2k₀ - k₁ ≤ 0`), so "if `k₁ ≥ k₀` the path is feasible" holds only for `k₀ ≤ k₁ < 2k₀`
(`example_20_D_4_infeasible`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-! ### Example 20.D.2 -/

/-- **Example 20.D.2** (MWG, p. 750): `u(k, k') = û(F(k) - k')` has derivative
`(v, w) ↦ û'(F(k) - k') (F'(k) v - w)`. -/
theorem example_20_D_2_deriv {uh F : ℝ → ℝ} {a b uh' F' : ℝ}
    (huh : HasDerivAt uh uh' (F a - b)) (hF : HasDerivAt F F' a) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => uh (F p.1 - p.2)) D (a, b) ∧
      ∀ v w, D (v, w) = uh' * (F' * v - w) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => F p.1 - p.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) F').comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
        - ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) :=
    (hF.hasFDerivAt.comp (a, b) hasFDerivAt_fst).sub hasFDerivAt_snd
  refine ⟨_, huh.hasFDerivAt.comp (a, b) h1, fun v w => ?_⟩
  simp
  ring

/-- **Example 20.D.2** (MWG, p. 750): with `Du_t(v, w) = û'(c_{t+1}) (F'(k_t) v - w)`, where
`c_{t+1} = F(k_t) - k_{t+1}`, the Euler equations are `û'(c_{t+1}) = δ û'(c_{t+2}) F'(k_{t+1})`. -/
theorem example_20_D_2 {δ : ℝ} {uh' F' : ℝ → ℝ} {k : ℕ → ℝ} {F : ℝ → ℝ}
    {Du : ℕ → ℝ × ℝ →L[ℝ] ℝ}
    (hDu : ∀ t v w, Du t (v, w) = uh' (F (k t) - k (t + 1)) * (F' (k t) * v - w)) :
    EulerEq δ Du ↔ ∀ t, uh' (F (k t) - k (t + 1))
      = δ * uh' (F (k (t + 1)) - k (t + 2)) * F' (k (t + 1)) := by
  constructor
  · intro h t
    have := h t 1
    rw [hDu, hDu] at this
    linarith
  · intro h t v
    rw [hDu, hDu, h t]
    ring

/-- **Example 20.D.2** (MWG, p. 750), ratio form: `û'(c_t) / (δ û'(c_{t+1})) = F'(k_t)` (marginal
utilities of consuming or investing are equal), when `δ û'(c_{t+1}) ≠ 0`. -/
theorem example_20_D_2_ratio {δ uc uc' F' : ℝ} (h : δ * uc' ≠ 0) :
    uc = δ * uc' * F' ↔ uc / (δ * uc') = F' := by
  rw [div_eq_iff h]; constructor <;> intro e <;> linarith

/-! ### Example 20.D.3 -/

/-- **Example 20.D.3** (MWG, p. 750): `u(k, k') = F(k) - k' - γ(k' - k)` has derivative
`(v, w) ↦ F'(k) v - w - γ'(k' - k)(w - v)`. -/
theorem example_20_D_3_deriv {F γ : ℝ → ℝ} {a b F' γ' : ℝ} (hF : HasDerivAt F F' a)
    (hγ : HasDerivAt γ γ' (b - a)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => F p.1 - p.2 - γ (p.2 - p.1)) D (a, b) ∧
      ∀ v w, D (v, w) = F' * v - w - γ' * (w - v) := by
  have h1 := hF.hasFDerivAt.comp (a, b) (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (a, b)))
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 - p.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) :=
    hasFDerivAt_snd.sub hasFDerivAt_fst
  have h3 := hγ.hasFDerivAt.comp (a, b) h2
  refine ⟨_, (h1.sub hasFDerivAt_snd).sub h3, fun v w => ?_⟩
  simp
  ring

/-- **Example 20.D.3** (MWG, p. 751): the Euler equations of the cost-of-adjustment problem,
`-1 - γ'(k_t - k_{t-1}) + δ [F'(k_t) + γ'(k_{t+1} - k_t)] = 0`. -/
theorem example_20_D_3 {δ : ℝ} {F' γ' : ℝ → ℝ} {k : ℕ → ℝ} {Du : ℕ → ℝ × ℝ →L[ℝ] ℝ}
    (hDu : ∀ t v w, Du t (v, w) = F' (k t) * v - w - γ' (k (t + 1) - k t) * (w - v)) :
    EulerEq δ Du ↔ ∀ t, -1 - γ' (k (t + 1) - k t)
      + δ * (F' (k (t + 1)) + γ' (k (t + 2) - k (t + 1))) = 0 := by
  constructor
  · intro h t
    have := h t 1
    rw [hDu, hDu] at this
    linarith
  · intro h t v
    rw [hDu, hDu]
    have := h t
    linear_combination v * this

/-- Iterating a first-order recursion `x_t = δ (f_t + x_{t+1})` with bounded `x` and `0 ≤ δ < 1`
gives `x_0 = ∑_{t ≥ 0} δ^{t+1} f_t`. -/
theorem hasSum_of_recursion {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {x f : ℕ → ℝ} {B : ℝ}
    (hx : ∀ t, |x t| ≤ B) (hrec : ∀ t, x t = δ * (f t + x (t + 1))) :
    HasSum (fun t => δ ^ (t + 1) * f t) (x 0) := by
  have hpart : ∀ T, x 0 = ∑ t ∈ Finset.range T, δ ^ (t + 1) * f t + δ ^ T * x T := by
    intro T
    induction T with
    | zero => simp
    | succ T ih => rw [ih, Finset.sum_range_succ, hrec T]; ring
  have htail : Tendsto (fun T => δ ^ T * x T) atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const B
    rw [zero_mul] at hg
    refine squeeze_zero_norm (fun T => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 T)]
    exact mul_le_mul_of_nonneg_left (hx T) (pow_nonneg hδ0 T)
  have hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, δ ^ (t + 1) * f t) atTop (𝓝 (x 0)) := by
    have : Tendsto (fun T => x 0 - δ ^ T * x T) atTop (𝓝 (x 0 - 0)) :=
      tendsto_const_nhds.sub htail
    rw [sub_zero] at this
    exact this.congr fun T => by rw [hpart T]; ring
  -- absolute summability from the bounded recursion
  have habs : Summable fun t => δ ^ (t + 1) * f t := by
    have hf : ∀ t, |δ * f t| ≤ |x t| + δ * |x (t + 1)| := by
      intro t
      have : δ * f t = x t - δ * x (t + 1) := by rw [hrec t]; ring
      rw [this]
      calc |x t - δ * x (t + 1)| ≤ |x t| + |δ * x (t + 1)| := abs_sub _ _
        _ = |x t| + δ * |x (t + 1)| := by rw [abs_mul, abs_of_nonneg hδ0]
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hδ0 hδ1).mul_right (B + δ * B)) fun t => ?_
    rw [Real.norm_eq_abs, pow_succ, mul_assoc, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    refine mul_le_mul_of_nonneg_left ((hf t).trans ?_) (pow_nonneg hδ0 t)
    linarith [hx t, mul_le_mul_of_nonneg_left (hx (t + 1)) hδ0]
  exact (habs.hasSum_iff_tendsto_nat).2 hsum

/-- **Example 20.D.3** (MWG, p. 751): iterating the Euler equations from `t = 1`,
`1 + γ'(k₁ - k₀) = ∑_{t ≥ 1} δ^t (F'(k_t) - 1)`: the cost of an extra unit of capacity at `t = 1`
equals the discounted marginal products of a maintained unit of capacity. Valid when the marginal
adjustment costs `γ'(k_{t+1} - k_t)` along the path are bounded and `0 ≤ δ < 1`. -/
theorem example_20_D_3_iterated {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {F' γ' : ℝ → ℝ}
    {k : ℕ → ℝ} (heul : ∀ t, -1 - γ' (k (t + 1) - k t)
      + δ * (F' (k (t + 1)) + γ' (k (t + 2) - k (t + 1))) = 0)
    {B : ℝ} (hγb : ∀ t, |γ' (k (t + 1) - k t)| ≤ B) :
    HasSum (fun t => δ ^ (t + 1) * (F' (k (t + 1)) - 1)) (1 + γ' (k 1 - k 0)) := by
  have := hasSum_of_recursion (x := fun t => 1 + γ' (k (t + 1) - k t))
    (f := fun t => F' (k (t + 1)) - 1) hδ0 hδ1 (B := 1 + B)
    (fun t => (abs_add_le _ _).trans (by rw [abs_one]; linarith [hγb t]))
    (fun t => by have := heul t; simp only [show t + 1 + 1 = t + 2 by omega]; linarith)
  simpa using this

/-! ### Exercise 20.D.5 -/

/-- The adjustment cost of Exercise 20.D.5: `γ(x) = x^β` for `x ≥ 0` and `0` for `x ≤ 0`. -/
noncomputable def powCost (β : ℝ) (x : ℝ) : ℝ := (max x 0) ^ β

/-- **Exercise 20.D.5** (MWG, p. 784): for `β > 1`, `γ'(0) = 0`. -/
theorem exercise_20_D_5_gamma_deriv_zero {β : ℝ} (hβ : 1 < β) : HasDerivAt (powCost β) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Continuous fun x : ℝ => |x| ^ (β - 1) :=
    continuous_abs.rpow_const fun _ => Or.inr (by linarith)
  have hlim : Tendsto (fun x : ℝ => |x| ^ (β - 1)) (𝓝[≠] 0) (𝓝 0) := by
    have := hc.tendsto 0
    rw [abs_zero, Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have hβ0 : β ≠ 0 := by linarith
  have h0 : powCost β 0 = 0 := by simp [powCost, Real.zero_rpow hβ0]
  rw [slope_def_field, h0, sub_zero, sub_zero, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have : powCost β x = 0 := by simp [powCost, max_eq_right hneg.le, Real.zero_rpow hβ0]
    rw [this, zero_div, abs_zero]
    exact Real.rpow_nonneg (abs_nonneg x) _
  · have : powCost β x = x ^ β := by simp [powCost, max_eq_left hpos.le]
    rw [this, abs_div, abs_of_pos hpos, abs_of_pos (Real.rpow_pos_of_pos hpos β),
      Real.rpow_sub hpos, Real.rpow_one]

/-- **Exercise 20.D.5** (MWG, p. 784): `γ'(x) = β x^{β-1}` for `x > 0`. -/
theorem exercise_20_D_5_gamma_deriv_pos {β x : ℝ} (hx : 0 < x) :
    HasDerivAt (powCost β) (β * x ^ (β - 1)) x := by
  have h := Real.hasDerivAt_rpow_const (x := x) (p := β) (Or.inl hx.ne')
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp [powCost, max_eq_left (le_of_lt (Set.mem_Ioi.1 hy))]

/-- **Exercise 20.D.5** (MWG, p. 784): `γ'(x) = 0` for `x < 0`. -/
theorem exercise_20_D_5_gamma_deriv_neg {β x : ℝ} (hx : x < 0) :
    HasDerivAt (powCost β) 0 x := by
  refine (hasDerivAt_const x ((0 : ℝ) ^ β)).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  simp [powCost, max_eq_right (le_of_lt (Set.mem_Iio.1 hy))]

/-- **Exercise 20.D.5** (MWG, p. 784): `F(k) = k^α` has `F'(k) = α k^{α-1}` for `k > 0`. -/
theorem exercise_20_D_5_F_deriv {α k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun x : ℝ => x ^ α) (α * k ^ (α - 1)) k :=
  Real.hasDerivAt_rpow_const (Or.inl hk.ne')

/-- **Exercise 20.D.5** (MWG, p. 784), the steady state: a constant path `k_t = k > 0` satisfies
the Euler equations of Example 20.D.3 with `F(k) = k^α` and `γ'(0) = 0` if and only if
`k = (αδ)^{1/(1-α)}` (for `0 < α < 1`, `0 < δ`). -/
theorem exercise_20_D_5_steady_state {α δ k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < δ)
    (hk : 0 < k) :
    (-1 - 0 + δ * (α * k ^ (α - 1) + 0) = 0) ↔ k = (α * δ) ^ (1 / (1 - α)) := by
  have hαδ : 0 < α * δ := mul_pos hα0 hδ
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h
    have hk' : k ^ (α - 1) = (α * δ)⁻¹ := by
      field_simp; linarith
    have hk2 : k ^ (1 - α) = α * δ := by
      rw [show (1 : ℝ) - α = -(α - 1) by ring, Real.rpow_neg hk.le, hk', inv_inv]
    rw [← hk2, ← Real.rpow_mul hk.le, mul_one_div_cancel h1α, Real.rpow_one]
  · intro h
    rw [h, ← Real.rpow_mul hαδ.le]
    have : 1 / (1 - α) * (α - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one]
    field_simp
    ring

/-! ### Example 20.D.4 and Exercise 20.D.7 -/

/-- **Exercise 20.D.7** (MWG, p. 784): with `u(k, k') = ln(2k - k')` and `δ = 1/2`, for
`Du_t(v, w) = (2v - w) / c_t` with `c_t = 2k_t - k_{t+1} > 0`, the Euler equations (20.D.9) are
`k_{t+2} = 3k_{t+1} - 2k_t` (MWG's `k_{t+1} = 3k_t - 2k_{t-1}`). -/
theorem exercise_20_D_7_euler {k : ℕ → ℝ} (hc : ∀ t, 0 < 2 * k t - k (t + 1))
    {Du : ℕ → ℝ × ℝ →L[ℝ] ℝ} (hDu : ∀ t v w, Du t (v, w) = (2 * v - w) / (2 * k t - k (t + 1))) :
    EulerEq (1 / 2) Du ↔ ∀ t, k (t + 2) = 3 * k (t + 1) - 2 * k t := by
  constructor
  · intro h t
    have := h t 1
    rw [hDu, hDu] at this
    have h0 := (hc t).ne'
    have h1 := (hc (t + 1)).ne'
    field_simp at this
    simp only [show t + 1 + 1 = t + 2 by omega] at this
    linarith
  · intro h t v
    rw [hDu, hDu, show t + 1 + 1 = t + 2 by omega, h t]
    have h0 := (hc t).ne'
    have : 2 * k (t + 1) - (3 * k (t + 1) - 2 * k t) = 2 * k t - k (t + 1) := by ring
    rw [this]
    field_simp
    ring

/-- The derivative of `u(k, k') = ln(2k - k')` at a point with `2k - k' > 0` (Example 20.D.4). -/
theorem example_20_D_4_deriv {a b : ℝ} (hab : 0 < 2 * a - b) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) D (a, b) ∧
      ∀ v w, D (v, w) = (2 * v - w) / (2 * a - b) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => 2 * p.1 - p.2)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) :=
    (hasFDerivAt_fst.const_mul (2 : ℝ)).sub hasFDerivAt_snd
  have h2 := (Real.hasDerivAt_log hab.ne').comp_hasFDerivAt (a, b) h1
  refine ⟨_, (h2 : HasFDerivAt (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) _ (a, b)),
    fun v w => ?_⟩
  simp
  field_simp

/-- **Exercise 20.D.7** (MWG, p. 784): `k_t = k₀ + (k₁ - k₀)(2^t - 1)` solves
`k_{t+2} = 3k_{t+1} - 2k_t`. -/
theorem exercise_20_D_7_solution (k₀ k₁ : ℝ) (t : ℕ) :
    let k : ℕ → ℝ := fun t => k₀ + (k₁ - k₀) * (2 ^ t - 1)
    k (t + 2) = 3 * k (t + 1) - 2 * k t ∧ k 0 = k₀ ∧ k 1 = k₁ := by
  intro k
  refine ⟨by simp only [k, pow_succ]; ring, by simp [k], by simp only [k]; ring⟩

/-- **Exercise 20.D.7** (MWG, p. 784): every solution of the difference equation is of this
form. -/
theorem exercise_20_D_7_unique {k : ℕ → ℝ} (h : ∀ t, k (t + 2) = 3 * k (t + 1) - 2 * k t)
    (t : ℕ) : k t = k 0 + (k 1 - k 0) * (2 ^ t - 1) := by
  have key : ∀ t, k t = k 0 + (k 1 - k 0) * (2 ^ t - 1) ∧
      k (t + 1) = k 0 + (k 1 - k 0) * (2 ^ (t + 1) - 1) := by
    intro t
    induction t with
    | zero => exact ⟨by simp, by simp; ring⟩
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [show t + 1 + 1 = t + 2 by omega, h t, ih.1, ih.2, pow_succ, pow_succ]
      ring
  exact (key t).1

/-- **Example 20.D.4** (MWG, p. 753): along a solution, consumption `c_t = 2k_t - k_{t+1}` is
constant, equal to `2k₀ - k₁`. -/
theorem example_20_D_4_consumption (k₀ k₁ : ℝ) (t : ℕ) :
    let k : ℕ → ℝ := fun t => k₀ + (k₁ - k₀) * (2 ^ t - 1)
    2 * k t - k (t + 1) = 2 * k₀ - k₁ := by
  intro k
  simp only [k, pow_succ]
  ring

/-- **Example 20.D.4** (MWG, p. 753): if `k₁ < k₀`, `k_t` eventually becomes negative. -/
theorem example_20_D_4_negative {k₀ k₁ : ℝ} (h : k₁ < k₀) :
    ∃ t : ℕ, k₀ + (k₁ - k₀) * (2 ^ t - 1) < 0 := by
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (k₀ / (k₀ - k₁) + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨t, ?_⟩
  have hd : 0 < k₀ - k₁ := by linarith
  have : k₀ < (k₀ - k₁) * (2 ^ t - 1) := by
    rw [div_add_one hd.ne', div_lt_iff₀ hd] at ht
    nlinarith
  nlinarith

/-- **Example 20.D.4** (MWG, p. 753): if `k₁ > k₀`, `k_t` is unbounded. -/
theorem example_20_D_4_unbounded {k₀ k₁ : ℝ} (h : k₀ < k₁) (B : ℝ) :
    ∃ t : ℕ, B < k₀ + (k₁ - k₀) * (2 ^ t - 1) := by
  have hd : 0 < k₁ - k₀ := by linarith
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ((B - k₀) / (k₁ - k₀) + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨t, ?_⟩
  rw [div_add_one hd.ne', div_lt_iff₀ hd] at ht
  nlinarith

/-- **Example 20.D.4** (MWG, p. 753): `k₁ = k₀` is the only choice generating a bounded
solution, so `ψ(k₀) = k₀`. -/
theorem example_20_D_4_bounded_iff {k₀ k₁ : ℝ} :
    (∃ B, ∀ t : ℕ, |k₀ + (k₁ - k₀) * (2 ^ t - 1)| ≤ B) ↔ k₁ = k₀ := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨t, ht⟩ := example_20_D_4_unbounded (k₀ := k₁) (k₁ := k₀) h 0
      -- symmetric bound: use the explicit growth of `|k_t|`
      have hd : 0 < k₀ - k₁ := by linarith
      obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ((B + |k₀|) / (k₀ - k₁) + 1)
        (by norm_num : (1 : ℝ) < 2)
      rw [div_add_one hd.ne', div_lt_iff₀ hd] at hs
      have := hB s
      have h2 := neg_abs_le (k₀ + (k₁ - k₀) * (2 ^ s - 1))
      have h3 := le_abs_self k₀
      nlinarith
    · obtain ⟨t, ht⟩ := example_20_D_4_unbounded h B
      have := (le_abs_self _).trans (hB t)
      linarith
  · intro h
    rw [h]
    exact ⟨|k₀|, fun t => by simp⟩

/-- **Example 20.D.4** (MWG, p. 753): for `k₀ < k₁ < 2k₀` the Euler path is feasible with constant
consumption `2k₀ - k₁ > 0`, but it is not optimal: the stationary path `k₁ = k₀` has the strictly
higher constant consumption `k₀`, hence strictly higher utility `∑ (1/2)^t ln c`. -/
theorem example_20_D_4_not_optimal {k₀ k₁ : ℝ} (h1 : k₀ < k₁) (h2 : k₁ < 2 * k₀) :
    0 < 2 * k₀ - k₁ ∧
      ∑' t : ℕ, (1 / 2 : ℝ) ^ t * Real.log (2 * k₀ - k₁)
        < ∑' t : ℕ, (1 / 2 : ℝ) ^ t * Real.log k₀ := by
  have hc : 0 < 2 * k₀ - k₁ := by linarith
  refine ⟨hc, ?_⟩
  rw [tsum_mul_right, tsum_mul_right]
  have hg : 0 < ∑' t : ℕ, (1 / 2 : ℝ) ^ t := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  exact mul_lt_mul_of_pos_left (Real.log_lt_log hc (by linarith)) hg

/-- **Correction to Example 20.D.4** (MWG, p. 753): for `k₁ ≥ 2k₀` the Euler path is not feasible,
since consumption `2k₀ - k₁` is not positive. -/
theorem example_20_D_4_infeasible {k₀ k₁ : ℝ} (h : 2 * k₀ ≤ k₁) (t : ℕ) :
    ¬ 0 < 2 * (k₀ + (k₁ - k₀) * (2 ^ t - 1)) - (k₀ + (k₁ - k₀) * (2 ^ (t + 1) - 1)) := by
  rw [example_20_D_4_consumption k₀ k₁ t]
  linarith

/-- **Footnote 17** (MWG, p. 753): when `k₁ > k₀`, the supporting prices read off the Euler
equations, `p_t = (1/2)^t / c` with constant consumption `c = 2k₀ - k₁`, violate the
transversality condition: the value `p_{t+1} F(k_t) = p_{t+1} 2k_t` of the output tends to
`(k₁ - k₀)/c ≠ 0`. -/
theorem footnote_20_17 {k₀ k₁ : ℝ} (h1 : k₀ < k₁) (h2 : k₁ < 2 * k₀) :
    let k : ℕ → ℝ := fun t => k₀ + (k₁ - k₀) * (2 ^ t - 1)
    let c := 2 * k₀ - k₁
    Tendsto (fun t : ℕ => (1 / 2 : ℝ) ^ (t + 1) / c * (2 * k t)) atTop (𝓝 ((k₁ - k₀) / c)) ∧
      (k₁ - k₀) / c ≠ 0 := by
  intro k c
  have hc : 0 < c := by simp only [c]; linarith
  refine ⟨?_, div_ne_zero (by linarith) hc.ne'⟩
  have hform : ∀ t : ℕ, (1 / 2 : ℝ) ^ (t + 1) / c * (2 * k t)
      = ((k₁ - k₀) + (2 * k₀ - k₁) * (1 / 2 : ℝ) ^ t) / c := by
    intro t
    have h2t : (1 / 2 : ℝ) ^ t * 2 ^ t = 1 := by rw [← mul_pow]; norm_num
    calc (1 / 2 : ℝ) ^ (t + 1) / c * (2 * k t) = ((1 / 2 : ℝ) ^ t * k t) / c := by
          rw [pow_succ]; ring
      _ = _ := by
          congr 1
          simp only [k]
          linear_combination (k₁ - k₀) * h2t
  have hlim : Tendsto (fun t : ℕ => ((k₁ - k₀) + (2 * k₀ - k₁) * (1 / 2 : ℝ) ^ t) / c) atTop
      (𝓝 (((k₁ - k₀) + (2 * k₀ - k₁) * 0) / c)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))).div_const c)
  rw [mul_zero, add_zero] at hlim
  exact hlim.congr fun t => (hform t).symm

/-- The admissible region of Example 20.D.4: positive consumption `2k - k' > 0`. -/
def logRegion : Set (ℝ × ℝ) := {p | 0 < 2 * p.1 - p.2}

/-- **Example 20.D.4** (MWG, p. 753): by Proposition 20.D.7, the stationary path `k_t = k₀ > 0`
solves (20.D.8) among bounded admissible paths (so `ψ(k₀) = k₀`). -/
theorem example_20_D_4_optimal {k₀ : ℝ} (hk₀ : 0 < k₀) (k' : ℕ → ℝ)
    (hk' : Admissible logRegion k₀ k') {R' : ℝ} (hbdd' : ∀ t, ‖k' t‖ ≤ R')
    (hsum' : Summable fun t => (1 / 2 : ℝ) ^ t * Real.log (2 * k' t - k' (t + 1))) :
    reducedObjective (1 / 2) (fun p => Real.log (2 * p.1 - p.2)) k'
      ≤ reducedObjective (1 / 2) (fun p => Real.log (2 * p.1 - p.2)) (fun _ => k₀) := by
  have hconv : Convex ℝ logRegion := by
    intro x hx y hy a b ha hb hab
    simp only [logRegion, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at *
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1]; linarith
    · nlinarith [mul_pos h hx, mul_nonneg hb hy.le]
  have hconc : ConcaveOn ℝ logRegion (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) := by
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    have h := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 (Set.mem_Ioi.2 hx)
      (Set.mem_Ioi.2 hy) ha hb hab
    simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at h ⊢
    convert h using 2
    ring
  have hD : ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) D
      (k₀, k₀) ∧ ∀ v w, D (v, w) = (2 * v - w) / (2 * k₀ - k₀) :=
    example_20_D_4_deriv (by linarith)
  obtain ⟨D, hDd, hDf⟩ := hD
  refine proposition_20_D_7 (K := ℝ) (by norm_num) (by norm_num) hconc
    ⟨rfl, fun t => by simp only [logRegion, Set.mem_ofPred_eq]; linarith⟩ ?_
    (R := |k₀|) (fun t => by simp [Real.norm_eq_abs]) (ε := k₀ / 3) (by linarith)
    (fun t => ?_) (Du := fun _ => D) (fun t => hDd) ?_ k' hk' hbdd' hsum'
  · simp only [mul_comm]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  · intro p hp
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
    simp only [logRegion, Set.mem_ofPred_eq]
    have h1 := abs_lt.1 hp.1
    have h2 := abs_lt.1 hp.2
    linarith [h1.1, h2.2]
  · intro t v
    rw [hDf, hDf]
    field_simp
    ring

end MWG.EquilibriumTime
