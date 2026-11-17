/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Aggregation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.MeanInequalities

/-!
# Exercise 5.E.4: a uniform population of Leontief technologies (MWG, pp. 163-164)

Each technology `z = (z₁, z₂) ∈ [0, 10]²` produces up to one unit of output with fixed input
requirements `z₁, z₂` per unit; the technologies are uniformly distributed on `[0, 10]²`
(density `1/100`). The integrals over the square are written as iterated interval integrals.

* (a) At input prices `w` and output price `1`, technology `z` produces `1` if `w·z < 1`, `0`
  if `w·z > 1` (anything in `[0, 1]` if `w·z = 1`) and earns `max(0, 1 - w·z)`
  (`exercise_5_E_4a`).
* (b) For `w₁, w₂ ≥ 1/10` the aggregate profit is `π(w₁, w₂, 1) = 1/(600 w₁ w₂)`
  (`exercise_5_E_4b`).
* (c) The aggregate input demands, computed directly, are `z₁(w) = 1/(600 w₁² w₂)` and
  `z₂(w) = 1/(600 w₁ w₂²)`, and they equal `-∂π/∂w_ℓ` (`exercise_5_E_4c`).
* (d) If `π(w) = 1/(600 w₁ w₂)` held for all `w ≫ 0`, it would be the profit function of the
  Cobb-Douglas production function `f(z) = (9 z₁ z₂/200)^{1/3}` (decreasing returns, degree
  `2/3`), with the same input demands (`exercise_5_E_4d`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology MeasureTheory

/-! ### (a) One technology -/

/-- **Exercise 5.E.4(a)** (MWG, p. 163). The technology `z` choosing output `q ∈ [0, 1]` at
input prices `w` (output price `1`) earns `q(1 - w·z) ≤ max(0, 1 - w·z)`; if `w·z < 1` the
unique optimum is `q = 1`, if `w·z > 1` it is `q = 0`, and if `w·z = 1` every `q` is optimal. -/
theorem exercise_5_E_4a (w z : Fin 2 → ℝ) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, q * (1 - w ⬝ᵥ z) ≤ max 0 (1 - w ⬝ᵥ z)) ∧
      (w ⬝ᵥ z < 1 → ∀ q ∈ Set.Icc (0 : ℝ) 1,
        (q * (1 - w ⬝ᵥ z) = max 0 (1 - w ⬝ᵥ z) ↔ q = 1)) ∧
      (1 < w ⬝ᵥ z → ∀ q ∈ Set.Icc (0 : ℝ) 1,
        (q * (1 - w ⬝ᵥ z) = max 0 (1 - w ⬝ᵥ z) ↔ q = 0)) ∧
      (w ⬝ᵥ z = 1 → ∀ q ∈ Set.Icc (0 : ℝ) 1, q * (1 - w ⬝ᵥ z) = max 0 (1 - w ⬝ᵥ z)) := by
  refine ⟨fun q hq => ?_, fun h q hq => ?_, fun h q hq => ?_, fun h q _ => ?_⟩
  · rcases le_total 0 (1 - w ⬝ᵥ z) with h | h
    · rw [max_eq_right h]; nlinarith [hq.1, hq.2]
    · rw [max_eq_left h]; nlinarith [hq.1, hq.2]
  · rw [max_eq_right (by linarith)]
    constructor
    · intro he
      have : (q - 1) * (1 - w ⬝ᵥ z) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    · rintro rfl; ring
  · rw [max_eq_left (by linarith)]
    constructor
    · intro he
      rcases mul_eq_zero.mp he with h' | h'
      · exact h'
      · linarith
    · rintro rfl; ring
  · rw [h]; simp

/-! ### Integrals -/

/-- `∫₀ᵇ max(0, c - at)^{k+1} dt = max(0, c)^{k+2}/((k+2)a)` for `a > 0`, `c ≤ ab`. -/
theorem e4_pow_integral {a c b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hcb : c ≤ a * b) (k : ℕ) :
    ∫ t in (0 : ℝ)..b, (max 0 (c - a * t)) ^ (k + 1) = (max 0 c) ^ (k + 2) / ((k + 2) * a) := by
  have hcont : Continuous fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1) :=
    (continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))).pow _
  rcases le_or_gt c 0 with hc | hc
  · have h0 : Set.EqOn (fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1)) (fun _ => 0)
        (Set.uIcc 0 b) := by
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      have : c - a * t ≤ 0 := by nlinarith [ht.1]
      simp [max_eq_left this]
    rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero, max_eq_left hc]
    simp
  · set t0 := c / a with ht0
    have ht00 : 0 ≤ t0 := div_nonneg hc.le ha.le
    have ht0b : t0 ≤ b := by rw [ht0, div_le_iff₀ ha]; linarith
    have hat0 : a * t0 = c := by rw [ht0]; field_simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 t0)
      (hcont.intervalIntegrable t0 b)]
    have h1 : Set.EqOn (fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1))
        (fun t => (c - a * t) ^ (k + 1)) (Set.uIcc 0 t0) := by
      intro t ht
      rw [Set.uIcc_of_le ht00] at ht
      have : 0 ≤ c - a * t := by nlinarith [ht.2]
      simp only [max_eq_right this]
    have h2 : Set.EqOn (fun t : ℝ => (max 0 (c - a * t)) ^ (k + 1)) (fun _ => 0)
        (Set.uIcc t0 b) := by
      intro t ht
      rw [Set.uIcc_of_le ht0b] at ht
      have : c - a * t ≤ 0 := by nlinarith [ht.1]
      simp [max_eq_left this]
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
      intervalIntegral.integral_zero, add_zero, max_eq_right hc.le]
    have hk : (0 : ℝ) < k + 2 := by positivity
    have hF : ∀ t ∈ Set.uIcc 0 t0, HasDerivAt
        (fun t : ℝ => -(c - a * t) ^ (k + 2) / ((k + 2) * a)) ((c - a * t) ^ (k + 1)) t := by
      intro t _
      have h := ((((hasDerivAt_id t).const_mul a).const_sub c).pow (k + 2)).neg.div_const
        ((k + 2) * a)
      convert h using 1
      · funext x; simp
      · rw [show k + 2 - 1 = k + 1 by omega]
        simp only [id, mul_one]
        push_cast
        field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous fun x : ℝ => (c - a * x) ^ (k + 1)).intervalIntegrable 0 t0)]
    rw [hat0]
    simp only [sub_self, mul_zero, sub_zero]
    rw [zero_pow (by omega)]
    ring

/-- `∫₀ᵇ 1[at < c] dt = max(0, c)/a` for `a > 0`, `c ≤ ab`. -/
theorem e4_step_integral {a c b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hcb : c ≤ a * b) :
    ∫ t in (0 : ℝ)..b, (if a * t < c then (1 : ℝ) else 0) = max 0 c / a := by
  rcases le_or_gt c 0 with hc | hc
  · have h0 : Set.EqOn (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) (fun _ => 0)
        (Set.uIcc 0 b) := by
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      have : ¬ a * t < c := by push Not; nlinarith [ht.1]
      simp only [this, ↓reduceIte]
    rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero, max_eq_left hc,
      zero_div]
  · set t0 := c / a with ht0
    have ht00 : 0 ≤ t0 := div_nonneg hc.le ha.le
    have ht0b : t0 ≤ b := by rw [ht0, div_le_iff₀ ha]; linarith
    have hat0 : a * t0 = c := by rw [ht0]; field_simp
    have hanti : Antitone fun t : ℝ => if a * t < c then (1 : ℝ) else 0 := by
      intro x y hxy
      have : a * x ≤ a * y := mul_le_mul_of_nonneg_left hxy ha.le
      by_cases hy : a * y < c
      · have hx : a * x < c := lt_of_le_of_lt this hy
        simp only [hx, hy, ↓reduceIte, le_refl]
      · simp only [hy, ↓reduceIte]
        split_ifs <;> norm_num
    have i1 : IntervalIntegrable (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) volume 0 t0 :=
      hanti.intervalIntegrable
    have i2 : IntervalIntegrable (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) volume t0 b :=
      hanti.intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ t0 := by
      rw [ae_iff]
      simp
    have h1 : ∫ t in (0 : ℝ)..t0, (if a * t < c then (1 : ℝ) else 0) =
        ∫ _t in (0 : ℝ)..t0, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hmem
      rw [Set.uIoc_of_le ht00] at hmem
      have hlt : x < t0 := lt_of_le_of_ne hmem.2 hx
      have : a * x < c := by rw [← hat0]; exact mul_lt_mul_of_pos_left hlt ha
      simp only [this, ↓reduceIte]
    have h2 : Set.EqOn (fun t : ℝ => if a * t < c then (1 : ℝ) else 0) (fun _ => 0)
        (Set.uIcc t0 b) := by
      intro t ht
      rw [Set.uIcc_of_le ht0b] at ht
      have : ¬ a * t < c := by
        push Not
        rw [← hat0]
        exact mul_le_mul_of_nonneg_left ht.1 ha.le
      simp only [this, ↓reduceIte]
    rw [h1, intervalIntegral.integral_congr h2, intervalIntegral.integral_zero, add_zero,
      intervalIntegral.integral_const, max_eq_right hc.le, ht0]
    simp

/-! ### (b) Aggregate profit -/

/-- **Exercise 5.E.4(b)** (MWG, p. 164). The aggregate profit
`π(w, 1) = (1/100) ∫₀¹⁰∫₀¹⁰ max(0, 1 - w₁z₁ - w₂z₂) dz₂ dz₁` of the population. -/
noncomputable def e4AggProfit (w : Fin 2 → ℝ) : ℝ :=
  (1 / 100) * ∫ s in (0 : ℝ)..10, ∫ t in (0 : ℝ)..10, max 0 (1 - w 0 * s - w 1 * t)

/-- **Exercise 5.E.4(b)** (MWG, p. 164): for `w₁, w₂ ≥ 1/10`, `π(w₁, w₂, 1) = 1/(600 w₁ w₂)`. -/
theorem exercise_5_E_4b {w : Fin 2 → ℝ} (h0 : 1 / 10 ≤ w 0) (h1 : 1 / 10 ≤ w 1) :
    e4AggProfit w = 1 / (600 * w 0 * w 1) := by
  have hw0 : 0 < w 0 := by linarith
  have hw1 : 0 < w 1 := by linarith
  have hinner : Set.EqOn (fun s => ∫ t in (0 : ℝ)..10, max 0 (1 - w 0 * s - w 1 * t))
      (fun s => (max 0 (1 - w 0 * s)) ^ 2 / (2 * w 1)) (Set.uIcc 0 10) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have h := e4_pow_integral hw1 (by norm_num : (0 : ℝ) ≤ 10)
      (show 1 - w 0 * s ≤ w 1 * 10 by nlinarith [hs.1]) 0
    simp only [zero_add, pow_one, Nat.cast_zero] at h
    simpa only [sub_sub] using h
  unfold e4AggProfit
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_div]
  have h := e4_pow_integral hw0 (by norm_num : (0 : ℝ) ≤ 10)
    (show (1 : ℝ) ≤ w 0 * 10 by linarith) 1
  simp only [show (1 : ℕ) + 1 = 2 from rfl, max_eq_right (zero_le_one' ℝ), one_pow] at h
  rw [h]
  push_cast
  field_simp
  ring

/-! ### (c) Aggregate input demand -/

/-- **Exercise 5.E.4(c)** (MWG, p. 164). The aggregate demand for an input with price `a`,
the other input having price `b`: `(1/100) ∫₀¹⁰∫₀¹⁰ s·q(s, t) dt ds`, where technology `(s, t)`
(`s` the requirement of this input) produces `q = 1` iff `as + bt < 1` (the boundary
`as + bt = 1` has measure zero). The demand for `z₁` is `e4AggDemand w₁ w₂`, for `z₂`
`e4AggDemand w₂ w₁`. -/
noncomputable def e4AggDemand (a b : ℝ) : ℝ :=
  (1 / 100) * ∫ s in (0 : ℝ)..10, ∫ t in (0 : ℝ)..10,
    s * (if a * s + b * t < 1 then (1 : ℝ) else 0)

/-- The aggregate demand computed directly: `1/(600 a² b)` for `a, b ≥ 1/10`. -/
theorem e4AggDemand_eq {a b : ℝ} (ha : 1 / 10 ≤ a) (hb : 1 / 10 ≤ b) :
    e4AggDemand a b = 1 / (600 * a ^ 2 * b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hinner : Set.EqOn (fun s => ∫ t in (0 : ℝ)..10,
      s * (if a * s + b * t < 1 then (1 : ℝ) else 0))
      (fun s => s * (max 0 (1 - a * s) / b)) (Set.uIcc 0 10) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have e : (fun t => s * (if a * s + b * t < 1 then (1 : ℝ) else 0)) =
        fun t => s * (if b * t < 1 - a * s then (1 : ℝ) else 0) := by
      funext t
      congr 1
      exact if_congr ⟨fun h => by linarith, fun h => by linarith⟩ rfl rfl
    change ∫ t in (0 : ℝ)..10, s * (if a * s + b * t < 1 then (1 : ℝ) else 0) =
      s * (max 0 (1 - a * s) / b)
    rw [e, intervalIntegral.integral_const_mul, e4_step_integral hb0 (by norm_num)
      (by nlinarith [hs.1])]
  unfold e4AggDemand
  rw [intervalIntegral.integral_congr hinner]
  set s0 := 1 / a with hs0
  have hs00 : 0 ≤ s0 := by positivity
  have hs010 : s0 ≤ 10 := by rw [hs0, div_le_iff₀ ha0]; linarith
  have has0 : a * s0 = 1 := by rw [hs0]; field_simp
  have hcont : Continuous fun s : ℝ => s * (max 0 (1 - a * s) / b) :=
    continuous_id.mul ((continuous_const.max
      (continuous_const.sub (continuous_const.mul continuous_id))).div_const _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 s0)
    (hcont.intervalIntegrable s0 10)]
  have h1 : Set.EqOn (fun s : ℝ => s * (max 0 (1 - a * s) / b))
      (fun s => s * (1 - a * s) / b) (Set.uIcc 0 s0) := by
    intro s hs
    rw [Set.uIcc_of_le hs00] at hs
    have : 0 ≤ 1 - a * s := by nlinarith [hs.2]
    simp only [max_eq_right this]
    ring
  have h2 : Set.EqOn (fun s : ℝ => s * (max 0 (1 - a * s) / b)) (fun _ => 0)
      (Set.uIcc s0 10) := by
    intro s hs
    rw [Set.uIcc_of_le hs010] at hs
    have : 1 - a * s ≤ 0 := by nlinarith [hs.1]
    simp [max_eq_left this]
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_congr h2,
    intervalIntegral.integral_zero, add_zero]
  have hF : ∀ s ∈ Set.uIcc 0 s0, HasDerivAt (fun s : ℝ => (s ^ 2 / 2 - a * s ^ 3 / 3) / b)
      (s * (1 - a * s) / b) s := by
    intro s _
    have h := ((((hasDerivAt_id s).pow 2).div_const 2).sub
      (((hasDerivAt_id s).pow 3).const_mul a |>.div_const 3)).div_const b
    convert h using 1
    · funext x; simp
    · simp only [id]
      push_cast
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun x : ℝ => x * (1 - a * x) / b).intervalIntegrable 0 s0), hs0]
  field_simp
  ring

/-- **Exercise 5.E.4(c)** (MWG, p. 164). For `w₁, w₂ ≥ 1/10` the aggregate input demands are
`z₁(w) = 1/(600 w₁² w₂)` and `z₂(w) = 1/(600 w₁ w₂²)` (computed directly), and they agree with
`-∂π/∂w₁`, `-∂π/∂w₂` from (b) (Hotelling's lemma), which verifies (b). -/
theorem exercise_5_E_4c {w : Fin 2 → ℝ} (h0 : 1 / 10 ≤ w 0) (h1 : 1 / 10 ≤ w 1) :
    e4AggDemand (w 0) (w 1) = 1 / (600 * w 0 ^ 2 * w 1) ∧
      e4AggDemand (w 1) (w 0) = 1 / (600 * w 0 * w 1 ^ 2) ∧
      HasDerivAt (fun x => 1 / (600 * x * w 1)) (-e4AggDemand (w 0) (w 1)) (w 0) ∧
      HasDerivAt (fun x => 1 / (600 * w 0 * x)) (-e4AggDemand (w 1) (w 0)) (w 1) := by
  have hw0 : 0 < w 0 := by linarith
  have hw1 : 0 < w 1 := by linarith
  have d1 := e4AggDemand_eq h0 h1
  have d2 := e4AggDemand_eq h1 h0
  refine ⟨d1, by rw [d2]; ring, ?_, ?_⟩
  · rw [d1]
    have h := (hasDerivAt_inv hw0.ne').const_mul (1 / (600 * w 1))
    convert h using 1
    · funext x; ring
    · ring
  · rw [d2]
    have h := (hasDerivAt_inv hw1.ne').const_mul (1 / (600 * w 0))
    convert h using 1
    · funext x; ring
    · ring

/-! ### (d) The aggregate production function -/

/-- The Cobb-Douglas production function `f(z) = (9 z₁ z₂/200)^{1/3}`. -/
noncomputable def e4Prod (z : Fin 2 → ℝ) : ℝ := (9 / 200 * (z 0 * z 1)) ^ ((3 : ℕ)⁻¹ : ℝ)

/-- **Exercise 5.E.4(d)** (MWG, p. 164). If the profit function `1/(600 w₁ w₂)` of (b) held for
all `w ≫ 0`, the underlying aggregate production function would be
`f(z) = (9 z₁ z₂/200)^{1/3}`: for every `w ≫ 0`, `max_{z ≥ 0} f(z) - w·z = 1/(600 w₁ w₂)`,
attained at the input demands `(1/(600 w₁² w₂), 1/(600 w₁ w₂²))` of (c). -/
theorem exercise_5_E_4d {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    (∀ z : Fin 2 → ℝ, 0 ≤ z → e4Prod z - w ⬝ᵥ z ≤ 1 / (600 * w 0 * w 1)) ∧
      e4Prod ![1 / (600 * w 0 ^ 2 * w 1), 1 / (600 * w 0 * w 1 ^ 2)] -
        w ⬝ᵥ ![1 / (600 * w 0 ^ 2 * w 1), 1 / (600 * w 0 * w 1 ^ 2)] = 1 / (600 * w 0 * w 1) := by
  have hw0 := hw 0
  have hw1 := hw 1
  set K := 1 / (600 * w 0 * w 1) with hK
  have hK0 : 0 < K := by positivity
  have hdot : ∀ z : Fin 2 → ℝ, w ⬝ᵥ z = w 0 * z 0 + w 1 * z 1 := fun z => by
    simp [dotProduct, Fin.sum_univ_two]
  -- `f(z) = 3 (K · w₁z₁ · w₂z₂)^{1/3}`
  have hcube : ((27 : ℝ)) ^ ((3 : ℕ)⁻¹ : ℝ) = 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have hf : ∀ z : Fin 2 → ℝ, 0 ≤ z →
      e4Prod z = 3 * (K * (w 0 * z 0) * (w 1 * z 1)) ^ ((3 : ℕ)⁻¹ : ℝ) := by
    intro z hz
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have e : 9 / 200 * (z 0 * z 1) = 27 * (K * (w 0 * z 0) * (w 1 * z 1)) := by
      rw [hK]; field_simp; ring
    rw [e4Prod, e, Real.mul_rpow (by norm_num) (by positivity), hcube]
  refine ⟨fun z hz => ?_, ?_⟩
  · have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hamgm := Real.geom_mean_le_arith_mean3_weighted (w₁ := (3 : ℕ)⁻¹) (w₂ := (3 : ℕ)⁻¹)
      (w₃ := (3 : ℕ)⁻¹) (p₁ := K) (p₂ := w 0 * z 0) (p₃ := w 1 * z 1) (by norm_num)
      (by norm_num) (by norm_num) hK0.le (by positivity) (by positivity) (by norm_num)
    rw [← Real.mul_rpow hK0.le (by positivity), ← Real.mul_rpow (by positivity)
      (by positivity)] at hamgm
    rw [hf z hz, hdot]
    push_cast at hamgm
    linarith
  · have hz : (0 : Fin 2 → ℝ) ≤ ![1 / (600 * w 0 ^ 2 * w 1), 1 / (600 * w 0 * w 1 ^ 2)] := by
      intro i
      fin_cases i
      · change 0 ≤ 1 / (600 * w 0 ^ 2 * w 1); positivity
      · change 0 ≤ 1 / (600 * w 0 * w 1 ^ 2); positivity
    rw [hf _ hz, hdot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : w 0 * (1 / (600 * w 0 ^ 2 * w 1)) = K := by rw [hK]; field_simp
    have e2 : w 1 * (1 / (600 * w 0 * w 1 ^ 2)) = K := by rw [hK]; field_simp
    rw [e1, e2, show K * K * K = K ^ 3 by ring,
      Real.pow_rpow_inv_natCast hK0.le (by norm_num)]
    ring

end MWG.Production
