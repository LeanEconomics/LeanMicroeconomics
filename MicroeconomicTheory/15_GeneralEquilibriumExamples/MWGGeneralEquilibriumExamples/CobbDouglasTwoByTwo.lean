/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.TwoByTwo
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Cobb-Douglas 2 × 2 model; Exercises 15.D.6(c), 15.D.6(d), 15.D.8 (MWG pp. 532-544)

The 2 × 2 production model of Section 15.D (`TwoByTwo`) with Cobb-Douglas technologies, and the
remaining parts of Exercise 15.D.6.

* The Cobb-Douglas technology `f(z) = z₁^α z₂^(1-α)`, `0 < α < 1`, with unit input vector
  `a(w) = (r^(1-α), r^(-α))`, `r = α w₂/((1-α) w₁)`, and unit cost
  `c(w) = (w₁/α)^α (w₂/(1-α))^(1-α)`: cost minimization and uniqueness of the minimizer by the
  weighted AM-GM inequality and its equality case (`cdtA_min`, `cdtA_unique`); the general
  Cobb-Douglas 2 × 2 model satisfies the standing assumptions (`cdtModel_isModel`) and factor
  intensity when `α₂ < α₁` (`cdtModel_factorIntensity`). The model of **Exercise 15.D.8** is
  `cdModel` (`α = (2/3, 1/3)`).
* **Exercise 15.D.8**: at `p = (1, 1)`, for every `z̄ ≫ 0` the equilibrium exists and is unique
  (`exercise_15_D_8`), with the three regions of `ρ = z̄₁/z̄₂`: diversified for `1/2 < ρ < 2`
  (`exercise_15_D_8_diversified`, `exercise_15_D_8_outputs`), specialized in good 1 for `ρ ≥ 2`
  (`exercise_15_D_8_spec0`) and in good 2 for `ρ ≤ 1/2` (`exercise_15_D_8_spec1`).
* **Exercise 15.D.6(c)**: as printed the claim is false for the model as formalized (the
  Leontief model, which satisfies all standing assumptions and factor intensity, has
  unit-dollar isoquants meeting in two points: `exercise_15_D_6c_counterexample`). Corrected
  statement (`TwoByTwo.exercise_15_D_6c`): with ray-surjectivity (every factor ratio is
  cost-minimizing at some factor prices) and differentiability of `fⱼ` along rays, the
  isoquants meet at most once in the interior of `ℝ²₊`; it applies to `cdModel`
  (`exercise_15_D_6c_cdModel`). The graphical construction of the cone is not a claim.
* **Exercise 15.D.6(d)**: outside the diversification cone the equilibrium is specialized in the
  good intensive in the abundant factor, with factor prices `w = (pⱼ/gⱼ(ω))(ω, 1)` where `ω`
  makes good `j`'s cost-minimizing ratio equal to `z̄₁/z̄₂` (sufficiency:
  `TwoByTwo.exercise_15_D_6d_spec0`, `…_spec1`, `…_of_ray`, existence `…_exists`; every
  equilibrium has this form: `…_spec0_unique`, `…_spec1_unique`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice Filter Topology

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas production function
`f(z) = z₁^α z₂^(1-α)` (real powers; `0` on the axes when `0 < α < 1`). -/
noncomputable def cdtF (α : ℝ) (z : Fin 2 → ℝ) : ℝ := z 0 ^ α * z 1 ^ (1 - α)

/-- **Exercise 15.D.8** (MWG, p. 544). The cost-minimizing factor ratio of the Cobb-Douglas
technology, `r(w) = α w₂ / ((1 - α) w₁)`. -/
noncomputable def cdtRatio (α : ℝ) (w : Fin 2 → ℝ) : ℝ := α * w 1 / ((1 - α) * w 0)

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas unit input vector
`a(w) = (r^(1-α), r^(-α))` with `r = r(w)`. -/
noncomputable def cdtA (α : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![cdtRatio α w ^ (1 - α), cdtRatio α w ^ (-α)]

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas unit cost
`c(w) = (w₁/α)^α (w₂/(1-α))^(1-α)`. -/
noncomputable def cdtCost (α : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  (w 0 / α) ^ α * (w 1 / (1 - α)) ^ (1 - α)

variable {α : ℝ}

theorem cdtRatio_pos (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    0 < cdtRatio α w := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  unfold cdtRatio
  positivity

/-- The Cobb-Douglas unit input vector is strictly positive. -/
theorem cdtA_pos (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    (l : Fin 2) : 0 < cdtA α w l := by
  have hr := cdtRatio_pos hα0 hα1 hw
  fin_cases l
  · exact Real.rpow_pos_of_pos hr _
  · exact Real.rpow_pos_of_pos hr _

/-- The factor ratio of the Cobb-Douglas unit input vector is `a₁(w)/a₂(w) = r(w)`. -/
theorem cdtA_ratio (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdtA α w 0 / cdtA α w 1 = cdtRatio α w := by
  have hr := cdtRatio_pos hα0 hα1 hw
  simp only [cdtA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Real.rpow_sub hr, show 1 - α - -α = 1 by ring, Real.rpow_one]

/-- `f(a(w)) = 1`: the Cobb-Douglas unit input vector produces one unit. -/
theorem cdtF_cdtA (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdtF α (cdtA α w) = 1 := by
  have hr := cdtRatio_pos hα0 hα1 hw
  simp only [cdtF, cdtA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le, ← Real.rpow_add hr,
    show (1 - α) * α + -α * (1 - α) = 0 by ring, Real.rpow_zero]

/-- The Cobb-Douglas production function is nonnegative on `ℝ²₊`. -/
theorem cdtF_nonneg {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) : 0 ≤ cdtF α z :=
  mul_nonneg (Real.rpow_nonneg (hz 0) _) (Real.rpow_nonneg (hz 1) _)

/-- The Cobb-Douglas production function is homogeneous of degree one on `ℝ²₊`. -/
theorem cdtF_smul {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) {t : ℝ} (ht : 0 ≤ t) :
    cdtF α (t • z) = t * cdtF α z := by
  simp only [cdtF, Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow ht (hz 0), Real.mul_rpow ht (hz 1)]
  have h : t ^ α * t ^ (1 - α) = t := by
    rw [← Real.rpow_add' ht (by ring_nf; norm_num), show α + (1 - α) = 1 by ring,
      Real.rpow_one]
  calc t ^ α * z 0 ^ α * (t ^ (1 - α) * z 1 ^ (1 - α))
      = (t ^ α * t ^ (1 - α)) * (z 0 ^ α * z 1 ^ (1 - α)) := by ring
    _ = t * (z 0 ^ α * z 1 ^ (1 - α)) := by rw [h]

/-- The unit cost is positive. -/
theorem cdtCost_pos (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    0 < cdtCost α w := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  unfold cdtCost
  positivity

/-- The weighted AM-GM rewriting: `(w₁z₁/α)^α (w₂z₂/(1-α))^(1-α) = c(w) f(z)`. -/
theorem cdt_geom (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) :
    (w 0 / α * z 0) ^ α * (w 1 / (1 - α) * z 1) ^ (1 - α) = cdtCost α w * cdtF α z := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  rw [Real.mul_rpow (by positivity) (hz 0), Real.mul_rpow (by positivity) (hz 1)]
  unfold cdtCost cdtF
  ring

/-- The arithmetic side: `α (w₁z₁/α) + (1-α)(w₂z₂/(1-α)) = w·z`. -/
theorem cdt_arith (hα0 : 0 < α) (hα1 : α < 1) (w z : Fin 2 → ℝ) :
    α * (w 0 / α * z 0) + (1 - α) * (w 1 / (1 - α) * z 1) = w ⬝ᵥ z := by
  have : (1 - α) ≠ 0 := by linarith
  rw [TwoByTwo.dot_two]
  field_simp

/-- **Cost minimization** (weighted AM-GM): `c(w) f(z) ≤ w·z` for `z ∈ ℝ²₊`, `w ≫ 0`. -/
theorem cdtCost_mul_le (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) : cdtCost α w * cdtF α z ≤ w ⬝ᵥ z := by
  have h0 := hw 0
  have h1 := hw 1
  have : 0 < 1 - α := by linarith
  rw [← cdt_geom hα0 hα1 hw hz, ← cdt_arith hα0 hα1 w z]
  exact Real.geom_mean_le_arith_mean2_weighted hα0.le this.le
    (mul_nonneg (by positivity) (hz 0)) (mul_nonneg (by positivity) (hz 1)) (by ring)

/-- At the unit input vector the two AM-GM terms agree: `w₁a₁/α = w₂a₂/(1-α)`. -/
theorem cdtA_balanced (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    w 0 / α * cdtA α w 0 = w 1 / (1 - α) * cdtA α w 1 := by
  have hr := cdtRatio_pos hα0 hα1 hw
  have h0 := hw 0
  have : (1 - α) ≠ 0 := by linarith
  have key : cdtRatio α w ^ (1 - α) = cdtRatio α w * cdtRatio α w ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
  simp only [cdtA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key]
  unfold cdtRatio
  field_simp

/-- `w·a(w) = c(w)`: the unit input vector costs exactly the unit cost. -/
theorem cdt_dot_A (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    w ⬝ᵥ cdtA α w = cdtCost α w := by
  have hbal := cdtA_balanced hα0 hα1 hw
  have hg := cdt_geom hα0 hα1 hw (fun l => (cdtA_pos hα0 hα1 hw l).le)
  rw [cdtF_cdtA hα0 hα1 hw, mul_one, ← hbal] at hg
  have hs : 0 < w 0 / α * cdtA α w 0 :=
    mul_pos (div_pos (hw 0) hα0) (cdtA_pos hα0 hα1 hw 0)
  rw [← Real.rpow_add hs, show α + (1 - α) = 1 by ring, Real.rpow_one] at hg
  rw [← cdt_arith hα0 hα1 w, ← hbal, ← hg]
  ring

/-- **Cost minimization**: `w·a(w) ≤ w·z` whenever `f(z) ≥ 1`, `z ∈ ℝ²₊`. -/
theorem cdtA_min (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) (hf : 1 ≤ cdtF α z) :
    w ⬝ᵥ cdtA α w ≤ w ⬝ᵥ z := by
  rw [cdt_dot_A hα0 hα1 hw]
  have hc := cdtCost_pos hα0 hα1 hw
  calc cdtCost α w = cdtCost α w * 1 := (mul_one _).symm
    _ ≤ cdtCost α w * cdtF α z := mul_le_mul_of_nonneg_left hf hc.le
    _ ≤ w ⬝ᵥ z := cdtCost_mul_le hα0 hα1 hw hz

/-- **Uniqueness of the cost minimizer** (equality case of weighted AM-GM). -/
theorem cdtA_unique (hα0 : 0 < α) (hα1 : α < 1) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) (hf : 1 ≤ cdtF α z)
    (hle : w ⬝ᵥ z ≤ w ⬝ᵥ cdtA α w) : z = cdtA α w := by
  have h0 := hw 0
  have h1 := hw 1
  have hβ : 0 < 1 - α := by linarith
  have hc := cdtCost_pos hα0 hα1 hw
  rw [cdt_dot_A hα0 hα1 hw] at hle
  have hx : 0 ≤ w 0 / α * z 0 := mul_nonneg (by positivity) (hz 0)
  have hy : 0 ≤ w 1 / (1 - α) * z 1 := mul_nonneg (by positivity) (hz 1)
  have hgm := Real.geom_mean_le_arith_mean2_weighted hα0.le hβ.le hx hy (by ring)
  rw [cdt_geom hα0 hα1 hw hz, cdt_arith hα0 hα1 w z] at hgm
  have hcf : cdtCost α w ≤ cdtCost α w * cdtF α z := by
    calc cdtCost α w = cdtCost α w * 1 := (mul_one _).symm
      _ ≤ cdtCost α w * cdtF α z := mul_le_mul_of_nonneg_left hf hc.le
  have heq : (w 0 / α * z 0) ^ α * (w 1 / (1 - α) * z 1) ^ (1 - α) =
      α * (w 0 / α * z 0) + (1 - α) * (w 1 / (1 - α) * z 1) := by
    rw [cdt_geom hα0 hα1 hw hz, cdt_arith hα0 hα1 w z]
    linarith
  have hxy := (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hα0 hβ hx hy (by ring)).1 heq
  have hsum := cdt_arith hα0 hα1 w z
  rw [← hxy] at hsum
  -- both terms equal the unit cost
  have hxc : w 0 / α * z 0 = cdtCost α w := by
    have : w 0 / α * z 0 = w ⬝ᵥ z := by linarith
    linarith
  have hbal := cdtA_balanced hα0 hα1 hw
  have hdA := cdt_arith hα0 hα1 w (cdtA α w)
  rw [← hbal, cdt_dot_A hα0 hα1 hw] at hdA
  have hxa : w 0 / α * cdtA α w 0 = cdtCost α w := by linarith
  funext l
  fin_cases l
  · have : w 0 / α * z 0 = w 0 / α * cdtA α w 0 := by rw [hxc, hxa]
    exact mul_left_cancel₀ (div_pos h0 hα0).ne' this
  · have : w 1 / (1 - α) * z 1 = w 1 / (1 - α) * cdtA α w 1 := by rw [← hxy, hxc, ← hbal, hxa]
    exact mul_left_cancel₀ (div_pos h1 hβ).ne' this

/-- The Cobb-Douglas unit input vector is continuous in the relative factor price. -/
theorem cdtA_continuousOn (hα0 : 0 < α) (hα1 : α < 1) (l : Fin 2) :
    ContinuousOn (fun t : ℝ => cdtA α ![t, 1] l) (Set.Ioi 0) := by
  have hβ : 0 < 1 - α := by linarith
  have hbase : ContinuousOn (fun t : ℝ => cdtRatio α ![t, 1]) (Set.Ioi 0) := by
    simp only [cdtRatio, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    exact (mul_pos hβ (Set.mem_Ioi.1 ht)).ne'
  have hne : ∀ t ∈ Set.Ioi (0 : ℝ), cdtRatio α ![t, 1] ≠ 0 := fun t ht =>
    (cdtRatio_pos hα0 hα1 (TwoByTwo.relPrice_pos (Set.mem_Ioi.1 ht))).ne'
  fin_cases l
  · exact hbase.rpow_const fun t ht => Or.inl (hne t ht)
  · exact hbase.rpow_const fun t ht => Or.inl (hne t ht)

/-- **Exercise 15.D.8** (MWG, p. 544), general form. The 2 × 2 model with Cobb-Douglas
technologies `fⱼ(z) = z₁^{αⱼ} z₂^{1-αⱼ}`. -/
noncomputable def cdtModel (α : Fin 2 → ℝ) : TwoByTwo where
  f := fun j => cdtF (α j)
  a := fun j => cdtA (α j)

/-- The Cobb-Douglas model with exponents in `(0, 1)` satisfies the standing assumptions of the
2 × 2 model. -/
theorem cdtModel_isModel {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1) :
    (cdtModel α).IsModel where
  f_nonneg := fun _ _ hz => cdtF_nonneg hz
  hom := fun _ _ hz _ ht => cdtF_smul hz ht
  a_mem := fun j _ hw =>
    ⟨fun l => (cdtA_pos (hα j).1 (hα j).2 hw l).le, cdtF_cdtA (hα j).1 (hα j).2 hw⟩
  a_min := fun j _ hw _ hz hf => cdtA_min (hα j).1 (hα j).2 hw hz hf
  a_unique := fun j _ hw _ hz hf hle => cdtA_unique (hα j).1 (hα j).2 hw hz hf hle
  a_pos := fun j _ l hw => cdtA_pos (hα j).1 (hα j).2 hw l
  a_cont := fun j l => cdtA_continuousOn (hα j).1 (hα j).2 l

/-- The unit cost of the Cobb-Douglas model is `cⱼ(w) = (w₁/αⱼ)^{αⱼ} (w₂/(1-αⱼ))^{1-αⱼ}`. -/
theorem cdtModel_c {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1) (j : Fin 2)
    {w : Fin 2 → ℝ} (hw : StrictlyPositive w) : (cdtModel α).c j w = cdtCost (α j) w :=
  cdt_dot_A (hα j).1 (hα j).2 hw

/-- The factor intensity condition holds in the Cobb-Douglas model when `α₂ < α₁`. -/
theorem cdtModel_factorIntensity {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1)
    (h : α 1 < α 0) : (cdtModel α).FactorIntensity := by
  intro w hw
  change cdtA (α 1) w 0 / cdtA (α 1) w 1 < cdtA (α 0) w 0 / cdtA (α 0) w 1
  rw [cdtA_ratio (hα 1).1 (hα 1).2 hw, cdtA_ratio (hα 0).1 (hα 0).2 hw]
  unfold cdtRatio
  have h0 := hw 0
  have h1 := hw 1
  have hb0 : 0 < 1 - α 0 := by linarith [(hα 0).2]
  have hb1 : 0 < 1 - α 1 := by linarith [(hα 1).2]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos h0 h1) (mul_pos h1 (sub_pos.2 h))]

/-- **Exercise 15.D.8** (MWG, p. 544). The model of the exercise:
`f₁(z) = z₁^{2/3} z₂^{1/3}` and `f₂(z) = z₁^{1/3} z₂^{2/3}`. -/
noncomputable def cdModel : TwoByTwo := cdtModel ![2 / 3, 1 / 3]

theorem cdModel_alpha : ∀ j, 0 < (![2 / 3, 1 / 3] : Fin 2 → ℝ) j ∧
    (![2 / 3, 1 / 3] : Fin 2 → ℝ) j < 1 := by
  intro j
  fin_cases j <;> norm_num

/-- **Exercise 15.D.8** (MWG, p. 544). The Cobb-Douglas model of the exercise satisfies the
standing assumptions of the 2 × 2 model. -/
theorem cdModel_isModel : cdModel.IsModel := cdtModel_isModel cdModel_alpha

/-- **Exercise 15.D.8** (MWG, p. 544). The factor ratios in the exercise's model:
`a₁₁/a₂₁ = 2w₂/w₁` and `a₁₂/a₂₂ = w₂/(2w₁)`. -/
theorem cdModel_ratio {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdModel.a 0 w 0 / cdModel.a 0 w 1 = 2 * w 1 / w 0 ∧
      cdModel.a 1 w 0 / cdModel.a 1 w 1 = w 1 / (2 * w 0) := by
  have h0 := (hw 0).ne'
  constructor
  · change cdtA (2 / 3) w 0 / cdtA (2 / 3) w 1 = _
    rw [cdtA_ratio (by norm_num) (by norm_num) hw]
    unfold cdtRatio
    field_simp
    ring
  · change cdtA (1 / 3) w 0 / cdtA (1 / 3) w 1 = _
    rw [cdtA_ratio (by norm_num) (by norm_num) hw]
    unfold cdtRatio
    field_simp
    ring

/-- **Exercise 15.D.8** (MWG, p. 544). The exercise's model satisfies the factor intensity
condition (good 1 is relatively intensive in factor 1: `2w₂/w₁ > w₂/(2w₁)`). -/
theorem cdModel_factorIntensity : cdModel.FactorIntensity :=
  cdtModel_factorIntensity cdModel_alpha (by norm_num)

namespace TwoByTwo

variable {M : TwoByTwo}

/-! ### Exercise 15.D.6(d): specialization -/

/-- The ratio of unit costs depends only on the relative factor price:
`c₁(w)/c₂(w) = g₁(w₁/w₂)/g₂(w₁/w₂)`. -/
theorem c_ratio_eq_g (hM : M.IsModel) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    M.c 0 w / M.c 1 w = M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) := by
  rw [c_eq_g hM 0 hw, c_eq_g hM 1 hw, mul_div_mul_left _ _ (hw 1).ne']

/-- Two strictly positive factor price vectors with the same relative price and the same unit
cost of some good are equal. -/
theorem eq_of_relPrice_eq_of_c_eq (hM : M.IsModel) (j : Fin 2) {w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (hr : w 0 / w 1 = w' 0 / w' 1)
    (hc : M.c j w = M.c j w') : w = w' := by
  rw [c_eq_g hM j hw, c_eq_g hM j hw', hr] at hc
  have hg := c_pos hM j (relPrice_pos (div_pos (hw' 0) (hw' 1)))
  have h1 : w 1 = w' 1 := mul_right_cancel₀ hg.ne' hc
  have h0 : w 0 = w' 0 := by
    rw [h1] at hr
    exact (div_left_inj' (hw' 1).ne').1 hr
  funext l
  fin_cases l
  · exact h0
  · exact h1

/-- If good 1 breaks even at `w` and good 2 makes no profit, the relative price of factor 1 is
at most its value `ŵ₁/ŵ₂` at the factor prices `ŵ` solving (15.D.7). -/
theorem relPrice_le_of_spec0 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hw : StrictlyPositive w) (h0 : M.c 0 w = p 0) (h1 : p 1 ≤ M.c 1 w) :
    w 0 / w 1 ≤ what 0 / what 1 := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  rw [← (unitCost_ratio_strictMono hM hFI).le_iff_le hω hωh]
  change M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) ≤ M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1)
  rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, h0]
  have hp0 : 0 < p 0 := hc 0 ▸ c_pos hM 0 hwhat
  have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
  exact div_le_div_of_nonneg_left hp0.le hp1 h1

/-- If good 2 breaks even at `w` and good 1 makes no profit, the relative price of factor 1 is
at least `ŵ₁/ŵ₂`. -/
theorem relPrice_ge_of_spec1 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hw : StrictlyPositive w) (h0 : p 0 ≤ M.c 0 w) (h1 : M.c 1 w = p 1) :
    what 0 / what 1 ≤ w 0 / w 1 := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  rw [← (unitCost_ratio_strictMono hM hFI).le_iff_le hωh hω]
  change M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1) ≤ M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1)
  rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, h1]
  have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
  exact div_le_div_of_nonneg_right h0 hp1.le

/-- **Exercise 15.D.6(d)** (MWG, p. 543), sufficiency, specialization in good 1. Let `ŵ ≫ 0` solve
(15.D.7), `cⱼ(ŵ) = pⱼ`, and `z̄ ≫ 0`. If `w ≫ 0` has `c₁(w) = p₁`, the factor ratio of good 1 at
`w` equals the endowment ratio, `a₁₁(w)/a₂₁(w) = z̄₁/z̄₂`, and `w₁/w₂ ≤ ŵ₁/ŵ₂`, then the economy
specialized in good 1, `z = (z̄, 0)`, is a factor market equilibrium at `w` (with output
`q₁ = z̄₁/a₁₁(w)`, and `c₂(w) ≥ p₂`). -/
theorem exercise_15_D_6d_spec0 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hw : StrictlyPositive w) (hc0 : M.c 0 w = p 0)
    (hk : M.a 0 w 0 / M.a 0 w 1 = zbar 0 / zbar 1) (hle : w 0 / w 1 ≤ what 0 / what 1) :
    IsFactorEqm M.f p zbar w ![zbar, 0] := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  have a00 := hM.a_pos 0 w 0 hw
  have a01 := hM.a_pos 0 w 1 hw
  have hz0 := hz 0
  have hz1 := hz 1
  -- the second good makes no profit
  have hc1 : p 1 ≤ M.c 1 w := by
    have hmono := ((unitCost_ratio_strictMono hM hFI).le_iff_le hω hωh).2 hle
    change M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) ≤
      M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1) at hmono
    rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, hc0] at hmono
    have hp0 : 0 < p 0 := hc 0 ▸ c_pos hM 0 hwhat
    have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
    exact (div_le_div_iff_of_pos_left hp0 (c_pos hM 1 hw) hp1).1 hmono
  have hzq : zbar = (zbar 0 / M.a 0 w 0) • M.a 0 w := by
    rw [div_eq_div_iff a01.ne' hz1.ne'] at hk
    have e0 : zbar 0 = zbar 0 / M.a 0 w 0 * M.a 0 w 0 := by field_simp
    have e1 : zbar 1 = zbar 0 / M.a 0 w 0 * M.a 0 w 1 := by field_simp; linarith
    funext l
    fin_cases l
    · exact e0
    · exact e1
  rw [exercise_15_D_6a hM]
  refine ⟨hw, ![zbar 0 / M.a 0 w 0, 0], fun j => ?_, fun j => ?_, fun j hj => ?_, fun j => ?_, ?_⟩
  · fin_cases j
    · exact (div_pos hz0 a00).le
    · exact le_rfl
  · fin_cases j
    · exact hc0.ge
    · exact hc1
  · fin_cases j
    · exact hc0.symm
    · exact absurd hj (lt_irrefl 0)
  · fin_cases j
    · exact hzq
    · simp
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, add_zero]
    exact hzq.symm

/-- **Exercise 15.D.6(d)** (MWG, p. 543), sufficiency, specialization in good 2: if `c₂(w) = p₂`,
`a₁₂(w)/a₂₂(w) = z̄₁/z̄₂` and `w₁/w₂ ≥ ŵ₁/ŵ₂`, then `z = (0, z̄)` is a factor market equilibrium
at `w`. -/
theorem exercise_15_D_6d_spec1 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hw : StrictlyPositive w) (hc1 : M.c 1 w = p 1)
    (hk : M.a 1 w 0 / M.a 1 w 1 = zbar 0 / zbar 1) (hge : what 0 / what 1 ≤ w 0 / w 1) :
    IsFactorEqm M.f p zbar w ![0, zbar] := by
  have hω := div_pos (hw 0) (hw 1)
  have hωh := div_pos (hwhat 0) (hwhat 1)
  have a10 := hM.a_pos 1 w 0 hw
  have a11 := hM.a_pos 1 w 1 hw
  have hz0 := hz 0
  have hz1 := hz 1
  have hc0 : p 0 ≤ M.c 0 w := by
    have hmono := ((unitCost_ratio_strictMono hM hFI).le_iff_le hωh hω).2 hge
    change M.g 0 (what 0 / what 1) / M.g 1 (what 0 / what 1) ≤
      M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) at hmono
    rw [← c_ratio_eq_g hM hw, ← c_ratio_eq_g hM hwhat, hc 0, hc 1, hc1] at hmono
    have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
    exact (div_le_div_iff_of_pos_right hp1).1 hmono
  have hzq : zbar = (zbar 0 / M.a 1 w 0) • M.a 1 w := by
    rw [div_eq_div_iff a11.ne' hz1.ne'] at hk
    have e0 : zbar 0 = zbar 0 / M.a 1 w 0 * M.a 1 w 0 := by field_simp
    have e1 : zbar 1 = zbar 0 / M.a 1 w 0 * M.a 1 w 1 := by field_simp; linarith
    funext l
    fin_cases l
    · exact e0
    · exact e1
  rw [exercise_15_D_6a hM]
  refine ⟨hw, ![0, zbar 0 / M.a 1 w 0], fun j => ?_, fun j => ?_, fun j hj => ?_, fun j => ?_, ?_⟩
  · fin_cases j
    · exact le_rfl
    · exact (div_pos hz0 a10).le
  · fin_cases j
    · exact hc0
    · exact hc1.ge
  · fin_cases j
    · exact absurd hj (lt_irrefl 0)
    · exact hc1.symm
  · fin_cases j
    · simp
    · exact hzq
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul, zero_add]
    exact hzq.symm

/-- Strictly above the diversification cone, a relative factor price at which good 1's factor
ratio equals the endowment ratio is below `ŵ₁/ŵ₂`. -/
theorem relPrice_lt_of_above_cone (hM : M.IsModel) {w what : Fin 2 → ℝ}
    (hwhat : StrictlyPositive what) (hw : StrictlyPositive w) {ρ : ℝ}
    (hρ : M.a 0 what 0 / M.a 0 what 1 < ρ) (hk : M.a 0 w 0 / M.a 0 w 1 = ρ) :
    w 0 / w 1 < what 0 / what 1 := by
  by_contra h
  rw [not_lt] at h
  have hint := intensity_antitone hM 0 (div_pos (hwhat 0) (hwhat 1)) h
  rw [← a_eq_rel hM 0 hw, ← a_eq_rel hM 0 hwhat] at hint
  linarith

/-- Strictly below the diversification cone, a relative factor price at which good 2's factor
ratio equals the endowment ratio is above `ŵ₁/ŵ₂`. -/
theorem relPrice_gt_of_below_cone (hM : M.IsModel) {w what : Fin 2 → ℝ}
    (hwhat : StrictlyPositive what) (hw : StrictlyPositive w) {ρ : ℝ}
    (hρ : ρ < M.a 1 what 0 / M.a 1 what 1) (hk : M.a 1 w 0 / M.a 1 w 1 = ρ) :
    what 0 / what 1 < w 0 / w 1 := by
  by_contra h
  rw [not_lt] at h
  have hint := intensity_antitone hM 1 (div_pos (hw 0) (hw 1)) h
  rw [← a_eq_rel hM 1 hw, ← a_eq_rel hM 1 hwhat] at hint
  linarith

/-- Ray-surjectivity of good `j`'s technology: every factor ratio `ρ > 0` is the
cost-minimizing ratio `a_{1j}(ω, 1)/a_{2j}(ω, 1)` at some relative factor price `ω > 0`. -/
def RaySurjective (M : TwoByTwo) (j : Fin 2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ ω : ℝ, 0 < ω ∧ M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ

/-- The factor prices of the specialized equilibrium: `(p₁/g₁(ω)) (ω, 1)`; its unit cost of good
1 is `p₁` and its unit input vector of good 1 is `a₁(ω, 1)`. -/
theorem smul_relPrice_facts (hM : M.IsModel) (j : Fin 2) {ω t : ℝ} (hω : 0 < ω) (ht : 0 < t) :
    StrictlyPositive (t • ![ω, 1]) ∧ M.c j (t • ![ω, 1]) = t * M.g j ω ∧
      M.a j (t • ![ω, 1]) = M.a j ![ω, 1] ∧
      (t • ![ω, 1]) 0 / (t • ![ω, 1]) 1 = ω := by
  refine ⟨fun l => ?_, c_smul hM j (relPrice_pos hω) ht, a_smul hM j (relPrice_pos hω) ht, ?_⟩
  · simpa using mul_pos ht (relPrice_pos hω l)
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp

/-- **Exercise 15.D.6(d)** (MWG, p. 543), the factor prices of the economy specialized in good 1.
Strictly above the cone, `z̄₁/z̄₂ > a₁₁(ŵ)/a₂₁(ŵ)`, let `ω > 0` make good 1's factor ratio equal
to `z̄₁/z̄₂`. Then `w = (p₁/g₁(ω)) (ω, 1)` and `z = (z̄, 0)` form a factor market equilibrium. -/
theorem exercise_15_D_6d_spec0_of_ray (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hρ : M.a 0 what 0 / M.a 0 what 1 < zbar 0 / zbar 1)
    {ω : ℝ} (hω : 0 < ω) (hk : M.a 0 ![ω, 1] 0 / M.a 0 ![ω, 1] 1 = zbar 0 / zbar 1) :
    IsFactorEqm M.f p zbar ((p 0 / M.g 0 ω) • ![ω, 1]) ![zbar, 0] := by
  have hp0 : 0 < p 0 := hc 0 ▸ c_pos hM 0 hwhat
  have hg : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  obtain ⟨hw, hcw, haw, hrw⟩ := smul_relPrice_facts hM 0 hω (div_pos hp0 hg)
  have hk' : M.a 0 ((p 0 / M.g 0 ω) • ![ω, 1]) 0 / M.a 0 ((p 0 / M.g 0 ω) • ![ω, 1]) 1 =
      zbar 0 / zbar 1 := by rw [haw]; exact hk
  refine exercise_15_D_6d_spec0 hM hFI hwhat hc hz hw ?_ hk'
    (relPrice_lt_of_above_cone hM hwhat hw hρ hk').le
  rw [hcw]
  exact div_mul_cancel₀ _ hg.ne'

/-- **Exercise 15.D.6(d)** (MWG, p. 543), the factor prices of the economy specialized in good 2:
strictly below the cone, with `ω > 0` making good 2's factor ratio equal to `z̄₁/z̄₂`,
`w = (p₂/g₂(ω)) (ω, 1)` and `z = (0, z̄)` form a factor market equilibrium. -/
theorem exercise_15_D_6d_spec1_of_ray (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what) (hc : ∀ j, M.c j what = p j)
    (hz : StrictlyPositive zbar) (hρ : zbar 0 / zbar 1 < M.a 1 what 0 / M.a 1 what 1)
    {ω : ℝ} (hω : 0 < ω) (hk : M.a 1 ![ω, 1] 0 / M.a 1 ![ω, 1] 1 = zbar 0 / zbar 1) :
    IsFactorEqm M.f p zbar ((p 1 / M.g 1 ω) • ![ω, 1]) ![0, zbar] := by
  have hp1 : 0 < p 1 := hc 1 ▸ c_pos hM 1 hwhat
  have hg : 0 < M.g 1 ω := c_pos hM 1 (relPrice_pos hω)
  obtain ⟨hw, hcw, haw, hrw⟩ := smul_relPrice_facts hM 1 hω (div_pos hp1 hg)
  have hk' : M.a 1 ((p 1 / M.g 1 ω) • ![ω, 1]) 0 / M.a 1 ((p 1 / M.g 1 ω) • ![ω, 1]) 1 =
      zbar 0 / zbar 1 := by rw [haw]; exact hk
  refine exercise_15_D_6d_spec1 hM hFI hwhat hc hz hw ?_ hk'
    (relPrice_gt_of_below_cone hM hwhat hw hρ hk').le
  rw [hcw]
  exact div_mul_cancel₀ _ hg.ne'

/-- **Exercise 15.D.6(d)** (MWG, p. 543), existence. With ray-surjectivity of good 1's technology,
for every endowment `z̄ ≫ 0` on or above the diversification cone there is an equilibrium
specialized in good 1. -/
theorem exercise_15_D_6d_spec0_exists (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : M.RaySurjective 0) {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : M.a 0 what 0 / M.a 0 what 1 ≤ zbar 0 / zbar 1) :
    ∃ w, IsFactorEqm M.f p zbar w ![zbar, 0] := by
  rcases eq_or_lt_of_le hρ with h | h
  · exact ⟨what, exercise_15_D_6d_spec0 hM hFI hwhat hc hz hwhat (hc 0) h le_rfl⟩
  · obtain ⟨ω, hω, hk⟩ := hs _ (div_pos (hz 0) (hz 1))
    exact ⟨_, exercise_15_D_6d_spec0_of_ray hM hFI hwhat hc hz h hω hk⟩

/-- **Exercise 15.D.6(d)** (MWG, p. 543), existence: with ray-surjectivity of good 2's technology,
for every `z̄ ≫ 0` on or below the cone there is an equilibrium specialized in good 2. -/
theorem exercise_15_D_6d_spec1_exists (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : M.RaySurjective 1) {p zbar what : Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : zbar 0 / zbar 1 ≤ M.a 1 what 0 / M.a 1 what 1) :
    ∃ w, IsFactorEqm M.f p zbar w ![0, zbar] := by
  rcases eq_or_lt_of_le hρ with h | h
  · exact ⟨what, exercise_15_D_6d_spec1 hM hFI hwhat hc hz hwhat (hc 1) h.symm le_rfl⟩
  · obtain ⟨ω, hω, hk⟩ := hs _ (div_pos (hz 0) (hz 1))
    exact ⟨_, exercise_15_D_6d_spec1_of_ray hM hFI hwhat hc hz h hω hk⟩

/-- **Exercise 15.D.6(d)** (MWG, p. 543), uniqueness. If `z̄ ≫ 0` lies on or above the
diversification cone, `z̄₁/z̄₂ ≥ a₁₁(ŵ)/a₂₁(ŵ)`, then every factor market equilibrium is
specialized in good 1, `z = (z̄, 0)`, with `c₁(w) = p₁` and good 1's factor ratio at `w` equal to
the endowment ratio (which, with `c₁(w) = p₁`, pins down `w` when that ratio determines the
relative factor price). -/
theorem exercise_15_D_6d_spec0_unique (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : M.a 0 what 0 / M.a 0 what 1 ≤ zbar 0 / zbar 1) (h : IsFactorEqm M.f p zbar w z) :
    z = ![zbar, 0] ∧ M.c 0 w = p 0 ∧ M.a 0 w 0 / M.a 0 w 1 = zbar 0 / zbar 1 := by
  obtain ⟨hw, q, hq, hpc, hqp, hzq, hsum⟩ := (exercise_15_D_6a hM p zbar w z).1 h
  have hnot : ¬ ∀ j, 0 < q j := fun hall => by
    have := (exercise_15_D_6b hM hFI hwhat hc hz hq hpc hqp hw hsum).1 hall
    linarith [this.2]
  have hs0 := congrFun hsum 0
  have hs1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs0 hs1
  have hz0 := hz 0
  have hz1 := hz 1
  rcases eq_or_lt_of_le (hq 0) with hq0 | hq0
  · -- specialization in good 2 is impossible above the cone
    exfalso
    rw [← hq0, zero_mul, zero_add] at hs0 hs1
    have hq1 : 0 < q 1 := by
      rcases eq_or_lt_of_le (hq 1) with h1 | h1
      · rw [← h1, zero_mul] at hs0
        linarith
      · exact h1
    have hge := relPrice_ge_of_spec1 hM hFI hwhat hc hw (hpc 0) (hqp 1 hq1).symm
    have hint := intensity_antitone hM 1 (div_pos (hwhat 0) (hwhat 1)) hge
    rw [← a_eq_rel hM 1 hw, ← a_eq_rel hM 1 hwhat] at hint
    have hk : zbar 0 / zbar 1 = M.a 1 w 0 / M.a 1 w 1 := by
      rw [← hs0, ← hs1, mul_div_mul_left _ _ hq1.ne']
    have := hFI what hwhat
    linarith
  · have hq1 : q 1 = 0 := by
      by_contra h1
      exact hnot fun j => by
        fin_cases j
        · exact hq0
        · exact lt_of_le_of_ne (hq 1) (Ne.symm h1)
    rw [hq1, zero_mul, add_zero] at hs0 hs1
    have hsum' := hsum
    rw [Fin.sum_univ_two, hq1, zero_smul, add_zero] at hsum'
    have e0 : z 0 = zbar := (hzq 0).trans hsum'
    have e1 : z 1 = 0 := by rw [hzq 1, hq1, zero_smul]
    refine ⟨?_, (hqp 0 hq0).symm, ?_⟩
    · funext j
      fin_cases j
      · exact e0
      · exact e1
    · rw [← hs0, ← hs1, mul_div_mul_left _ _ hq0.ne']

/-- **Exercise 15.D.6(d)** (MWG, p. 543), uniqueness below the cone: if
`z̄₁/z̄₂ ≤ a₁₂(ŵ)/a₂₂(ŵ)`, every equilibrium is specialized in good 2, `z = (0, z̄)`, with
`c₂(w) = p₂` and good 2's factor ratio at `w` equal to the endowment ratio. -/
theorem exercise_15_D_6d_spec1_unique (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w what : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hρ : zbar 0 / zbar 1 ≤ M.a 1 what 0 / M.a 1 what 1) (h : IsFactorEqm M.f p zbar w z) :
    z = ![0, zbar] ∧ M.c 1 w = p 1 ∧ M.a 1 w 0 / M.a 1 w 1 = zbar 0 / zbar 1 := by
  obtain ⟨hw, q, hq, hpc, hqp, hzq, hsum⟩ := (exercise_15_D_6a hM p zbar w z).1 h
  have hnot : ¬ ∀ j, 0 < q j := fun hall => by
    have := (exercise_15_D_6b hM hFI hwhat hc hz hq hpc hqp hw hsum).1 hall
    linarith [this.1]
  have hs0 := congrFun hsum 0
  have hs1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs0 hs1
  have hz0 := hz 0
  have hz1 := hz 1
  rcases eq_or_lt_of_le (hq 1) with hq1 | hq1
  · exfalso
    rw [← hq1, zero_mul, add_zero] at hs0 hs1
    have hq0 : 0 < q 0 := by
      rcases eq_or_lt_of_le (hq 0) with h0 | h0
      · rw [← h0, zero_mul] at hs0
        linarith
      · exact h0
    have hle := relPrice_le_of_spec0 hM hFI hwhat hc hw (hqp 0 hq0).symm (hpc 1)
    have hint := intensity_antitone hM 0 (div_pos (hw 0) (hw 1)) hle
    rw [← a_eq_rel hM 0 hw, ← a_eq_rel hM 0 hwhat] at hint
    have hk : zbar 0 / zbar 1 = M.a 0 w 0 / M.a 0 w 1 := by
      rw [← hs0, ← hs1, mul_div_mul_left _ _ hq0.ne']
    have := hFI what hwhat
    linarith
  · have hq0 : q 0 = 0 := by
      by_contra h0
      exact hnot fun j => by
        fin_cases j
        · exact lt_of_le_of_ne (hq 0) (Ne.symm h0)
        · exact hq1
    rw [hq0, zero_mul, zero_add] at hs0 hs1
    have hsum' := hsum
    rw [Fin.sum_univ_two, hq0, zero_smul, zero_add] at hsum'
    have e0 : z 0 = 0 := by rw [hzq 0, hq0, zero_smul]
    have e1 : z 1 = zbar := (hzq 1).trans hsum'
    refine ⟨?_, (hqp 1 hq1).symm, ?_⟩
    · funext j
      fin_cases j
      · exact e0
      · exact e1
    · rw [← hs0, ← hs1, mul_div_mul_left _ _ hq1.ne']

/-! ### Exercise 15.D.6(c): unit-dollar isoquants -/

/-- **Exercise 15.D.6(c)** (MWG, p. 543). The unit-dollar isoquant of good `j`: the factor
combinations `z ∈ ℝ²₊` producing one dollar's worth of good `j`, `pⱼ fⱼ(z) = 1`. -/
def unitDollarIsoquant (M : TwoByTwo) (p : Fin 2 → ℝ) (j : Fin 2) : Set (Fin 2 → ℝ) :=
  {z | z ∈ nonnegOrthant 2 ∧ p j * M.f j z = 1}

/-- Differentiability of good `j`'s production function along the ray `t ↦ fⱼ(t, 1)`, `t > 0`. -/
def RayDifferentiable (M : TwoByTwo) (j : Fin 2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → DifferentiableAt ℝ (fun t : ℝ => M.f j ![t, 1]) ρ

/-- Duality between production and unit cost: `fⱼ(z) cⱼ(w) ≤ w·z` for `z ∈ ℝ²₊`, `w ≫ 0`. -/
theorem f_mul_c_le (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) : M.f j z * M.c j w ≤ w ⬝ᵥ z := by
  have hs := hM.f_nonneg j z hz
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, zero_mul]
    exact dotProduct_nonneg_of_nonneg (fun l => (hw l).le) hz
  · have hz' : (M.f j z)⁻¹ • z ∈ nonnegOrthant 2 := fun l => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hs) (hz l)
    have hf1 : 1 ≤ M.f j ((M.f j z)⁻¹ • z) := by
      rw [hM.hom j z hz _ (inv_nonneg.2 hs), inv_mul_cancel₀ h.ne']
    have := hM.a_min j w hw _ hz' hf1
    rw [dotProduct_smul, smul_eq_mul] at this
    unfold c
    have := mul_le_mul_of_nonneg_left this hs
    rwa [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul] at this

/-- Homogeneity along rays: `fⱼ(z) = z₂ fⱼ(z₁/z₂, 1)` for `z ≫ 0`. -/
theorem f_eq_ray (hM : M.IsModel) (j : Fin 2) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    M.f j z = z 1 * M.f j ![z 0 / z 1, 1] := by
  have h1 := hz 1
  have e : z = z 1 • ![z 0 / z 1, 1] := by
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  conv_lhs => rw [e]
  exact hM.hom j _ (fun l => (relPrice_pos (div_pos (hz 0) h1) l).le) _ h1.le

/-- Along the ray of good `j`'s cost-minimizing factor ratio `ρ = a_{1j}(ω, 1)/a_{2j}(ω, 1)`:
`fⱼ(ρ, 1) a_{2j}(ω, 1) = 1`. -/
theorem rayF_mul_a (hM : M.IsModel) (j : Fin 2) {ω ρ : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ) : M.f j ![ρ, 1] * M.a j ![ω, 1] 1 = 1 := by
  have hp := relPrice_pos hω
  have a0 := hM.a_pos j _ 0 hp
  have a1 := hM.a_pos j _ 1 hp
  have hρ : 0 < ρ := hk ▸ div_pos a0 a1
  have e : M.a j ![ω, 1] = M.a j ![ω, 1] 1 • ![ρ, 1] := by
    rw [← hk]
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  have h1 := (hM.a_mem j _ hp).2
  rw [e, hM.hom j _ (fun l => (relPrice_pos hρ l).le) _ a1.le] at h1
  linarith

/-- The line `(ωt + 1)/gⱼ(ω)` lies above `t ↦ fⱼ(t, 1)` on `t ≥ 0`:
`fⱼ(t, 1) gⱼ(ω) ≤ ωt + 1`. -/
theorem rayF_mul_g_le (hM : M.IsModel) (j : Fin 2) {ω t : ℝ} (hω : 0 < ω) (ht : 0 ≤ t) :
    M.f j ![t, 1] * M.g j ω ≤ ω * t + 1 := by
  have hz : (![t, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · exact ht
    · exact zero_le_one
  have := f_mul_c_le hM j (relPrice_pos hω) hz
  simpa [g, dot_two] using this

/-- ... with equality at the cost-minimizing ratio: `fⱼ(ρ, 1) gⱼ(ω) = ωρ + 1`. -/
theorem rayF_mul_g_eq (hM : M.IsModel) (j : Fin 2) {ω ρ : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ) : M.f j ![ρ, 1] * M.g j ω = ω * ρ + 1 := by
  have hp := relPrice_pos hω
  have a1 := hM.a_pos j _ 1 hp
  have hF := rayF_mul_a hM j hω hk
  have ha0 : M.a j ![ω, 1] 0 = ρ * M.a j ![ω, 1] 1 := by
    rw [← hk]; field_simp
  rw [g_eq, ha0]
  linear_combination (ω * ρ + 1) * hF

/-- With ray-surjectivity, `fⱼ(ρ, 1) > 0` for every `ρ > 0`. -/
theorem rayF_pos (hM : M.IsModel) {j : Fin 2} (hs : M.RaySurjective j) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < M.f j ![ρ, 1] := by
  obtain ⟨ω, hω, hk⟩ := hs ρ hρ
  have hF := rayF_mul_a hM j hω hk
  have a1 := hM.a_pos j _ 1 (relPrice_pos hω)
  by_contra h
  rw [not_lt] at h
  nlinarith

/-- The slope of the isoquant along the ray: if `fⱼ(·, 1)` has derivative `F'` at the
cost-minimizing ratio `ρ` of the relative factor price `ω`, then `F' = ω/gⱼ(ω)` (the line of
`rayF_mul_g_le` touches the graph at `ρ`, so the difference has a local maximum there). -/
theorem rayF_deriv_eq (hM : M.IsModel) (j : Fin 2) {ω ρ F' : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ)
    (hd : HasDerivAt (fun t : ℝ => M.f j ![t, 1]) F' ρ) : F' = ω / M.g j ω := by
  have hp := relPrice_pos hω
  have hg : 0 < M.g j ω := c_pos hM j hp
  have hρ : 0 < ρ := hk ▸ div_pos (hM.a_pos j _ 0 hp) (hM.a_pos j _ 1 hp)
  have hder : HasDerivAt (fun t : ℝ => M.f j ![t, 1] - (ω * t + 1) / M.g j ω)
      (F' - ω * 1 / M.g j ω) ρ :=
    hd.sub ((((hasDerivAt_id ρ).const_mul ω).add_const 1).div_const (M.g j ω))
  have hmax : IsLocalMax (fun t : ℝ => M.f j ![t, 1] - (ω * t + 1) / M.g j ω) ρ := by
    filter_upwards [Ioi_mem_nhds hρ] with t ht
    have h1 := rayF_mul_g_le hM j hω (Set.mem_Ioi.1 ht).le
    have h2 := rayF_mul_g_eq hM j hω hk
    have e1 : M.f j ![t, 1] ≤ (ω * t + 1) / M.g j ω := by rw [le_div_iff₀ hg]; exact h1
    have e2 : M.f j ![ρ, 1] = (ω * ρ + 1) / M.g j ω := by rw [eq_div_iff hg.ne']; exact h2
    linarith
  have := hmax.hasDerivAt_eq_zero hder
  rw [mul_one] at this
  linarith

/-- Under factor intensity, at a common ratio `ρ` the relative factor price making `ρ`
cost-minimizing for good 1 exceeds the one for good 2. -/
theorem rayPrice_lt (hM : M.IsModel) (hFI : M.FactorIntensity) {ω₀ ω₁ ρ : ℝ} (hω₀ : 0 < ω₀)
    (hω₁ : 0 < ω₁) (hk₀ : M.a 0 ![ω₀, 1] 0 / M.a 0 ![ω₀, 1] 1 = ρ)
    (hk₁ : M.a 1 ![ω₁, 1] 0 / M.a 1 ![ω₁, 1] 1 = ρ) : ω₁ < ω₀ := by
  by_contra h
  rw [not_lt] at h
  have h1 := intensity_antitone hM 0 hω₀ h
  have h2 := hFI _ (relPrice_pos hω₁)
  linarith

/-- **Exercise 15.D.6(c)** (MWG, p. 543), key step. Under factor intensity, ray-surjectivity and
ray-differentiability, `ρ ↦ f₁(ρ, 1)/f₂(ρ, 1)` is strictly increasing on `(0, ∞)`: its derivative
is `F₁F₂ (ω₁/(ω₁ρ+1) - ω₂/(ω₂ρ+1))/F₂² > 0` because `ω₁(ρ) > ω₂(ρ)`. -/
theorem rayF_ratio_strictMono (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : ∀ j, M.RaySurjective j) (hd : ∀ j, M.RayDifferentiable j) :
    StrictMonoOn (fun t => M.f 0 ![t, 1] / M.f 1 ![t, 1]) (Set.Ioi 0) := by
  have hder : ∀ ρ ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t => M.f 0 ![t, 1] / M.f 1 ![t, 1])
      ((deriv (fun t : ℝ => M.f 0 ![t, 1]) ρ * M.f 1 ![ρ, 1] -
        M.f 0 ![ρ, 1] * deriv (fun t : ℝ => M.f 1 ![t, 1]) ρ) / M.f 1 ![ρ, 1] ^ 2) ρ :=
    fun ρ hρ => ((hd 0 ρ hρ).hasDerivAt).div ((hd 1 ρ hρ).hasDerivAt)
      (rayF_pos hM (hs 1) hρ).ne'
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun ρ hρ => (hder ρ hρ).continuousAt.continuousWithinAt) fun ρ hρ => ?_
  rw [interior_Ioi] at hρ
  rw [(hder ρ hρ).deriv]
  apply div_pos _ (pow_pos (rayF_pos hM (hs 1) hρ) 2)
  obtain ⟨ω₀, hω₀, hk₀⟩ := hs 0 ρ hρ
  obtain ⟨ω₁, hω₁, hk₁⟩ := hs 1 ρ hρ
  have hρ' : 0 < ρ := hρ
  have d0 := rayF_deriv_eq hM 0 hω₀ hk₀ (hd 0 ρ hρ).hasDerivAt
  have d1 := rayF_deriv_eq hM 1 hω₁ hk₁ (hd 1 ρ hρ).hasDerivAt
  have F0 := rayF_mul_g_eq hM 0 hω₀ hk₀
  have F1 := rayF_mul_g_eq hM 1 hω₁ hk₁
  have hg0 : 0 < M.g 0 ω₀ := c_pos hM 0 (relPrice_pos hω₀)
  have hg1 : 0 < M.g 1 ω₁ := c_pos hM 1 (relPrice_pos hω₁)
  have hlt := rayPrice_lt hM hFI hω₀ hω₁ hk₀ hk₁
  rw [d0, d1]
  rw [eq_comm, ← div_eq_iff hg0.ne'] at F0
  rw [eq_comm, ← div_eq_iff hg1.ne'] at F1
  rw [← F0, ← F1]
  have : ω₀ / M.g 0 ω₀ * ((ω₁ * ρ + 1) / M.g 1 ω₁) -
      (ω₀ * ρ + 1) / M.g 0 ω₀ * (ω₁ / M.g 1 ω₁) = (ω₀ - ω₁) / (M.g 0 ω₀ * M.g 1 ω₁) := by
    field_simp
    ring
  rw [this]
  exact div_pos (sub_pos.2 hlt) (mul_pos hg0 hg1)

/-- **Exercise 15.D.6(c)** (MWG, p. 543), corrected. Under factor intensity, and if every factor
ratio `ρ > 0` is cost-minimizing for each good at some relative factor price (ray-surjectivity)
and each `fⱼ(·, 1)` is differentiable on `(0, ∞)`, the unit-dollar isoquants of the two goods
intersect at most once in the interior of `ℝ²₊`. -/
theorem exercise_15_D_6c (hM : M.IsModel) (hFI : M.FactorIntensity)
    (hs : ∀ j, M.RaySurjective j) (hd : ∀ j, M.RayDifferentiable j) {p z z' : Fin 2 → ℝ}
    (hz : StrictlyPositive z) (hz' : StrictlyPositive z')
    (h0 : z ∈ M.unitDollarIsoquant p 0) (h1 : z ∈ M.unitDollarIsoquant p 1)
    (h0' : z' ∈ M.unitDollarIsoquant p 0) (h1' : z' ∈ M.unitDollarIsoquant p 1) : z = z' := by
  have hρ := div_pos (hz 0) (hz 1)
  have hρ' := div_pos (hz' 0) (hz' 1)
  have e0 := h0.2
  have e1 := h1.2
  have e0' := h0'.2
  have e1' := h1'.2
  rw [f_eq_ray hM 0 hz] at e0
  rw [f_eq_ray hM 1 hz] at e1
  rw [f_eq_ray hM 0 hz'] at e0'
  rw [f_eq_ray hM 1 hz'] at e1'
  have hF1 := rayF_pos hM (hs 1) hρ
  have hF1' := rayF_pos hM (hs 1) hρ'
  have hp0 : p 0 ≠ 0 := by rintro h; rw [h, zero_mul] at e0; exact zero_ne_one e0
  -- the ratio `F₁/F₂` equals `p₂/p₁` on both rays
  have hr : M.f 0 ![z 0 / z 1, 1] / M.f 1 ![z 0 / z 1, 1] = p 1 / p 0 := by
    rw [div_eq_div_iff hF1.ne' hp0]
    have := hz 1
    have : z 1 * (M.f 0 ![z 0 / z 1, 1] * p 0 - p 1 * M.f 1 ![z 0 / z 1, 1]) = 0 := by
      linear_combination e0 - e1
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hr' : M.f 0 ![z' 0 / z' 1, 1] / M.f 1 ![z' 0 / z' 1, 1] = p 1 / p 0 := by
    rw [div_eq_div_iff hF1'.ne' hp0]
    have := hz' 1
    have : z' 1 * (M.f 0 ![z' 0 / z' 1, 1] * p 0 - p 1 * M.f 1 ![z' 0 / z' 1, 1]) = 0 := by
      linear_combination e0' - e1'
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hρeq : z 0 / z 1 = z' 0 / z' 1 :=
    (rayF_ratio_strictMono hM hFI hs hd).injOn hρ hρ' (hr.trans hr'.symm)
  rw [← hρeq] at e0'
  have hz1 : z 1 = z' 1 := by
    have hne : p 0 * M.f 0 ![z 0 / z 1, 1] ≠ 0 := by
      intro h
      have : p 0 * (z 1 * M.f 0 ![z 0 / z 1, 1]) = z 1 * (p 0 * M.f 0 ![z 0 / z 1, 1]) := by ring
      rw [this, h, mul_zero] at e0
      exact zero_ne_one e0
    have : (p 0 * M.f 0 ![z 0 / z 1, 1]) * z 1 = (p 0 * M.f 0 ![z 0 / z 1, 1]) * z' 1 := by
      linear_combination e0 - e0'
    exact mul_left_cancel₀ hne this
  have hz0 : z 0 = z' 0 := by
    rw [hz1] at hρeq
    exact (div_left_inj' (hz' 1).ne').1 hρeq
  funext l
  fin_cases l
  · exact hz0
  · exact hz1

end TwoByTwo

/-- **Exercise 15.D.6(c)** (MWG, p. 543), as printed, is false for the 2 × 2 model as formalized
(`TwoByTwo.IsModel` with factor intensity): in the Leontief model at prices `p = (1, 2)` both
unit-dollar isoquants contain the distinct points `(2, 1)` and `(3, 1)`. -/
theorem exercise_15_D_6c_counterexample :
    leontiefModel.IsModel ∧ leontiefModel.FactorIntensity ∧
      (![2, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 0 ∧
      (![2, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 1 ∧
      (![3, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 0 ∧
      (![3, 1] : Fin 2 → ℝ) ∈ leontiefModel.unitDollarIsoquant ![1, 2] 1 ∧
      StrictlyPositive (![2, 1] : Fin 2 → ℝ) ∧ StrictlyPositive (![3, 1] : Fin 2 → ℝ) ∧
      (![2, 1] : Fin 2 → ℝ) ≠ ![3, 1] := by
  refine ⟨leontiefModel_isModel, leontiefModel_factorIntensity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    norm_num [leontiefModel]
  · intro l; fin_cases l <;> norm_num
  · intro l; fin_cases l <;> norm_num
  · intro h
    have := congrFun h 0
    norm_num at this

/-- The Cobb-Douglas model satisfies ray-surjectivity: the cost-minimizing ratio
`αⱼ/((1-αⱼ)ω)` takes every value `ρ > 0` (at `ω = αⱼ/((1-αⱼ)ρ)`). -/
theorem cdtModel_raySurjective {α : Fin 2 → ℝ} (hα : ∀ j, 0 < α j ∧ α j < 1) (j : Fin 2) :
    (cdtModel α).RaySurjective j := by
  intro ρ hρ
  have ha := (hα j).1
  have hb : 0 < 1 - α j := by linarith [(hα j).2]
  refine ⟨α j / ((1 - α j) * ρ), by positivity, ?_⟩
  change cdtA (α j) _ 0 / cdtA (α j) _ 1 = ρ
  rw [cdtA_ratio (hα j).1 (hα j).2 (TwoByTwo.relPrice_pos (by positivity))]
  simp only [cdtRatio, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

/-- The Cobb-Douglas model is differentiable along rays: `fⱼ(t, 1) = t^{αⱼ}`. -/
theorem cdtModel_rayDifferentiable (α : Fin 2 → ℝ) (j : Fin 2) :
    (cdtModel α).RayDifferentiable j := by
  intro ρ hρ
  have e : (fun t : ℝ => (cdtModel α).f j ![t, 1]) = fun t => t ^ (α j) := by
    funext t
    simp [cdtModel, cdtF]
  rw [e]
  exact (Real.hasDerivAt_rpow_const (Or.inl hρ.ne')).differentiableAt

/-- **Exercise 15.D.6(c)** (MWG, p. 543), non-vacuity of the corrected statement: in the
Cobb-Douglas model of Exercise 15.D.8 the unit-dollar isoquants of the two goods intersect at
most once in the interior of `ℝ²₊`, at any output prices. -/
theorem exercise_15_D_6c_cdModel {p z z' : Fin 2 → ℝ} (hz : StrictlyPositive z)
    (hz' : StrictlyPositive z') (h0 : z ∈ cdModel.unitDollarIsoquant p 0)
    (h1 : z ∈ cdModel.unitDollarIsoquant p 1) (h0' : z' ∈ cdModel.unitDollarIsoquant p 0)
    (h1' : z' ∈ cdModel.unitDollarIsoquant p 1) : z = z' :=
  TwoByTwo.exercise_15_D_6c cdModel_isModel cdModel_factorIntensity
    (cdtModel_raySurjective cdModel_alpha) (cdtModel_rayDifferentiable _) hz hz' h0 h1 h0' h1'

/-! ### Exercise 15.D.8: the equilibria of the Cobb-Douglas model at `p = (1, 1)` -/

/-- Exponent bookkeeping: `(x^a)^b (x^c)^d = 1` when `ab + cd = 0`, `x > 0`. -/
theorem cd8_rpow_pair {x a b c d : ℝ} (hx : 0 < x) (h : a * b + c * d = 0) :
    (x ^ a) ^ b * (x ^ c) ^ d = 1 := by
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx, h, Real.rpow_zero]

/-- The unit cost of good 1 in Exercise 15.D.8: `c₁(w) = (3w₁/2)^{2/3} (3w₂)^{1/3}`. -/
theorem cd8_c0 {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdModel.c 0 w = (w 0 / (2 / 3)) ^ ((2 : ℝ) / 3) * (w 1 / (1 / 3)) ^ ((1 : ℝ) / 3) := by
  change (cdtModel ![2 / 3, 1 / 3]).c 0 w = _
  rw [cdtModel_c cdModel_alpha 0 hw]
  simp only [cdtCost, Matrix.cons_val_zero]
  norm_num

/-- The unit cost of good 2 in Exercise 15.D.8: `c₂(w) = (3w₁)^{1/3} (3w₂/2)^{2/3}`. -/
theorem cd8_c1 {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    cdModel.c 1 w = (w 0 / (1 / 3)) ^ ((1 : ℝ) / 3) * (w 1 / (2 / 3)) ^ ((2 : ℝ) / 3) := by
  change (cdtModel ![2 / 3, 1 / 3]).c 1 w = _
  rw [cdtModel_c cdModel_alpha 1 hw]
  simp only [cdtCost, Matrix.cons_val_one, Matrix.cons_val_zero]
  norm_num

/-- **Exercise 15.D.8** (MWG, p. 544). The factor prices solving (15.D.7) at `p = (1, 1)`:
`ŵ = (2^{2/3}/3) (1, 1)`. -/
noncomputable def cd8What : Fin 2 → ℝ := ![(2 : ℝ) ^ ((2 : ℝ) / 3) / 3, (2 : ℝ) ^ ((2 : ℝ) / 3) / 3]

/-- **Exercise 15.D.8** (MWG, p. 544). The factor prices when the economy specializes in good 1
(`ρ = z̄₁/z̄₂ ≥ 2`): `w = ∇f₁(z̄) = ((2/3) ρ^{-1/3}, (1/3) ρ^{2/3})`. -/
noncomputable def cd8WSpec0 (ρ : ℝ) : Fin 2 → ℝ :=
  ![2 / 3 * ρ ^ (-(1 : ℝ) / 3), 1 / 3 * ρ ^ ((2 : ℝ) / 3)]

/-- **Exercise 15.D.8** (MWG, p. 544). The factor prices when the economy specializes in good 2
(`ρ = z̄₁/z̄₂ ≤ 1/2`): `w = ∇f₂(z̄) = ((1/3) ρ^{-2/3}, (2/3) ρ^{1/3})`. -/
noncomputable def cd8WSpec1 (ρ : ℝ) : Fin 2 → ℝ :=
  ![1 / 3 * ρ ^ (-(2 : ℝ) / 3), 2 / 3 * ρ ^ ((1 : ℝ) / 3)]

/-- **Exercise 15.D.8** (MWG, p. 544). The diversified factor allocation:
`z₁ = ((2z̄₁ - z̄₂)/3) (2, 1)` and `z₂ = ((2z̄₂ - z̄₁)/3) (1, 2)`. -/
noncomputable def cd8ZDiv (zbar : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![((2 * zbar 0 - zbar 1) / 3) • ![2, 1], ((2 * zbar 1 - zbar 0) / 3) • ![1, 2]]

theorem cd8What_pos : StrictlyPositive cd8What := fun l => by
  have : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos two_pos _
  fin_cases l <;> simp [cd8What, this]

/-- At `ŵ` both unit costs equal the output prices `p = (1, 1)`. -/
theorem cd8What_c : ∀ j, cdModel.c j cd8What = (![1, 1] : Fin 2 → ℝ) j := by
  have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) / 3 / (2 / 3) = (2 : ℝ) ^ (-(1 : ℝ) / 3) := by
    rw [show -(1 : ℝ) / 3 = 2 / 3 - 1 by norm_num, Real.rpow_sub_one two_ne_zero]
    ring
  have h3 : (2 : ℝ) ^ ((2 : ℝ) / 3) / 3 / (1 / 3) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by ring
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [cd8_c0 cd8What_pos]
    simp only [cd8What, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h2, h3]
    exact cd8_rpow_pair two_pos (by norm_num)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [cd8_c1 cd8What_pos]
    simp only [cd8What, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h2, h3]
    exact cd8_rpow_pair two_pos (by norm_num)

/-- The diversification cone at `ŵ` is `1/2 < z̄₁/z̄₂ < 2`. -/
theorem cd8What_ratio : cdModel.a 0 cd8What 0 / cdModel.a 0 cd8What 1 = 2 ∧
    cdModel.a 1 cd8What 0 / cdModel.a 1 cd8What 1 = 1 / 2 := by
  obtain ⟨h0, h1⟩ := cdModel_ratio cd8What_pos
  have hs : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) / 3 := by positivity
  rw [h0, h1]
  simp only [cd8What, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · field_simp
  · field_simp

theorem cd8WSpec0_pos {ρ : ℝ} (hρ : 0 < ρ) : StrictlyPositive (cd8WSpec0 ρ) := fun l => by
  have h1 : 0 < ρ ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  have h2 : 0 < ρ ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  fin_cases l
  · simp only [cd8WSpec0, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; positivity
  · simp only [cd8WSpec0, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    positivity

theorem cd8WSpec1_pos {ρ : ℝ} (hρ : 0 < ρ) : StrictlyPositive (cd8WSpec1 ρ) := fun l => by
  have h1 : 0 < ρ ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  have h2 : 0 < ρ ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  fin_cases l
  · simp only [cd8WSpec1, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; positivity
  · simp only [cd8WSpec1, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    positivity

/-- At `w = ((2/3) ρ^{-1/3}, (1/3) ρ^{2/3})`, `c₁(w) = 1`. -/
theorem cd8WSpec0_c0 {ρ : ℝ} (hρ : 0 < ρ) : cdModel.c 0 (cd8WSpec0 ρ) = 1 := by
  rw [cd8_c0 (cd8WSpec0_pos hρ)]
  simp only [cd8WSpec0, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show 2 / 3 * ρ ^ (-(1 : ℝ) / 3) / (2 / 3) = ρ ^ (-(1 : ℝ) / 3) by ring,
    show 1 / 3 * ρ ^ ((2 : ℝ) / 3) / (1 / 3) = ρ ^ ((2 : ℝ) / 3) by ring]
  exact cd8_rpow_pair hρ (by norm_num)

/-- At `w = ((1/3) ρ^{-2/3}, (2/3) ρ^{1/3})`, `c₂(w) = 1`. -/
theorem cd8WSpec1_c1 {ρ : ℝ} (hρ : 0 < ρ) : cdModel.c 1 (cd8WSpec1 ρ) = 1 := by
  rw [cd8_c1 (cd8WSpec1_pos hρ)]
  simp only [cd8WSpec1, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show 1 / 3 * ρ ^ (-(2 : ℝ) / 3) / (1 / 3) = ρ ^ (-(2 : ℝ) / 3) by ring,
    show 2 / 3 * ρ ^ ((1 : ℝ) / 3) / (2 / 3) = ρ ^ ((1 : ℝ) / 3) by ring]
  exact cd8_rpow_pair hρ (by norm_num)

/-- The relative factor price of the good-1 specialization prices is `2/ρ`. -/
theorem cd8WSpec0_rel {ρ : ℝ} (hρ : 0 < ρ) : cd8WSpec0 ρ 0 / cd8WSpec0 ρ 1 = 2 / ρ := by
  have h : ρ ^ ((2 : ℝ) / 3) = ρ * ρ ^ (-(1 : ℝ) / 3) := by
    rw [show (2 : ℝ) / 3 = 1 + -(1 : ℝ) / 3 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h1 : 0 < ρ ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  simp only [cd8WSpec0, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h]
  field_simp

/-- The relative factor price of the good-2 specialization prices is `1/(2ρ)`. -/
theorem cd8WSpec1_rel {ρ : ℝ} (hρ : 0 < ρ) : cd8WSpec1 ρ 0 / cd8WSpec1 ρ 1 = 1 / (2 * ρ) := by
  have h : ρ ^ ((1 : ℝ) / 3) = ρ * ρ ^ (-(2 : ℝ) / 3) := by
    rw [show (1 : ℝ) / 3 = 1 + -(2 : ℝ) / 3 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h1 : 0 < ρ ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hρ _
  simp only [cd8WSpec1, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h]
  field_simp

/-- **Exercise 15.D.8** (MWG, p. 544), diversified region. For `z̄ ≫ 0` with
`1/2 < z̄₁/z̄₂ < 2`, the factor market equilibria at `p = (1, 1)` are exactly
`w = (2^{2/3}/3)(1, 1)`, `z₁ = ((2z̄₁ - z̄₂)/3)(2, 1)`, `z₂ = ((2z̄₂ - z̄₁)/3)(1, 2)`. -/
theorem exercise_15_D_8_diversified {zbar w : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (hz : StrictlyPositive zbar) (hlo : 1 / 2 < zbar 0 / zbar 1) (hhi : zbar 0 / zbar 1 < 2) :
    IsFactorEqm cdModel.f ![1, 1] zbar w z ↔ w = cd8What ∧ z = cd8ZDiv zbar := by
  have hM := cdModel_isModel
  have hFI := cdModel_factorIntensity
  have hz0 := hz 0
  have hz1 := hz 1
  obtain ⟨hk0, hk1⟩ := cd8What_ratio
  have a01 := hM.a_pos 0 cd8What 1 cd8What_pos
  have a10 := hM.a_pos 1 cd8What 0 cd8What_pos
  -- `a₁(ŵ) = a₂₁(ŵ) (2, 1)` and `a₂(ŵ) = a₁₂(ŵ) (1, 2)`
  have ha0 : cdModel.a 0 cd8What = cdModel.a 0 cd8What 1 • ![2, 1] := by
    have e : cdModel.a 0 cd8What 0 = 2 * cdModel.a 0 cd8What 1 := by
      rw [div_eq_iff a01.ne'] at hk0; exact hk0
    funext l
    fin_cases l
    · simp [e, mul_comm]
    · simp
  have ha1 : cdModel.a 1 cd8What = cdModel.a 1 cd8What 0 • ![1, 2] := by
    have e : cdModel.a 1 cd8What 1 = 2 * cdModel.a 1 cd8What 0 := by
      have a11 := hM.a_pos 1 cd8What 1 cd8What_pos
      rw [div_eq_iff a11.ne'] at hk1; linarith
    funext l
    fin_cases l
    · simp
    · simp [e, mul_comm]
  have hX : 0 < 2 * zbar 0 - zbar 1 := by
    rw [lt_div_iff₀ hz1] at hlo; linarith
  have hY : 0 < 2 * zbar 1 - zbar 0 := by
    rw [div_lt_iff₀ hz1] at hhi; linarith
  constructor
  · intro h
    obtain ⟨hw, q, hq, hpc, hqp, hzq, hsum⟩ := (TwoByTwo.exercise_15_D_6a hM _ zbar w z).1 h
    have hall := (TwoByTwo.exercise_15_D_6b hM hFI cd8What_pos cd8What_c hz hq hpc hqp hw
      hsum).2 ⟨by rw [hk1]; exact hlo, by rw [hk0]; exact hhi⟩
    have hwe : w = cd8What := TwoByTwo.factor_price_equalization hM hFI hw cd8What_pos
      (fun j => (hqp j (hall j)).symm) cd8What_c
    subst hwe
    rw [Fin.sum_univ_two, ha0, ha1, smul_smul, smul_smul] at hsum
    have s0 := congrFun hsum 0
    have s1 := congrFun hsum 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at s0 s1
    have eX : q 0 * cdModel.a 0 cd8What 1 = (2 * zbar 0 - zbar 1) / 3 := by linarith
    have eY : q 1 * cdModel.a 1 cd8What 0 = (2 * zbar 1 - zbar 0) / 3 := by linarith
    have e0 : z 0 = ((2 * zbar 0 - zbar 1) / 3) • ![2, 1] := by
      rw [hzq 0, ha0, smul_smul, eX]
    have e1 : z 1 = ((2 * zbar 1 - zbar 0) / 3) • ![1, 2] := by
      rw [hzq 1, ha1, smul_smul, eY]
    refine ⟨rfl, ?_⟩
    funext j
    fin_cases j
    · exact e0
    · exact e1
  · rintro ⟨rfl, rfl⟩
    set q : Fin 2 → ℝ := ![(2 * zbar 0 - zbar 1) / 3 / cdModel.a 0 cd8What 1,
      (2 * zbar 1 - zbar 0) / 3 / cdModel.a 1 cd8What 0] with hqdef
    have hq : ∀ j, 0 < q j := fun j => by
      fin_cases j
      · simp only [hqdef, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; positivity
      · simp only [hqdef, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        positivity
    have e0 : q 0 • cdModel.a 0 cd8What = ((2 * zbar 0 - zbar 1) / 3) • ![2, 1] := by
      rw [ha0, smul_smul]
      congr 1
      simp only [hqdef, Matrix.cons_val_zero]
      field_simp
    have e1 : q 1 • cdModel.a 1 cd8What = ((2 * zbar 1 - zbar 0) / 3) • ![1, 2] := by
      rw [ha1, smul_smul]
      congr 1
      simp only [hqdef, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp
    have hzform : cd8ZDiv zbar = fun j => q j • cdModel.a j cd8What := by
      funext j
      fin_cases j
      · exact e0.symm
      · exact e1.symm
    rw [hzform, TwoByTwo.interior_eqm_iff hM cd8What_pos hq]
    refine ⟨fun j => (cd8What_c j).symm, ?_⟩
    rw [Fin.sum_univ_two, e0, e1]
    funext l
    fin_cases l
    · simp; ring
    · simp; ring

/-- **Exercise 15.D.8** (MWG, p. 544), outputs in the diversified region:
`q₁ = 2^{2/3}(2z̄₁ - z̄₂)/3` and `q₂ = 2^{2/3}(2z̄₂ - z̄₁)/3`. -/
theorem exercise_15_D_8_outputs {zbar : Fin 2 → ℝ} (hlo : zbar 1 ≤ 2 * zbar 0)
    (hhi : zbar 0 ≤ 2 * zbar 1) :
    cdModel.f 0 (cd8ZDiv zbar 0) = (2 : ℝ) ^ ((2 : ℝ) / 3) * ((2 * zbar 0 - zbar 1) / 3) ∧
      cdModel.f 1 (cd8ZDiv zbar 1) = (2 : ℝ) ^ ((2 : ℝ) / 3) * ((2 * zbar 1 - zbar 0) / 3) := by
  have hM := cdModel_isModel
  have n0 : (![2, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> norm_num
  have n1 : (![1, 2] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> norm_num
  constructor
  · change cdModel.f 0 (((2 * zbar 0 - zbar 1) / 3) • ![2, 1]) = _
    rw [hM.hom 0 _ n0 _ (by linarith)]
    change _ * cdtF (2 / 3) ![2, 1] = _
    simp only [cdtF, Matrix.cons_val_zero, Matrix.cons_val_one, Real.one_rpow, mul_one]
    norm_num
    ring
  · change cdModel.f 1 (((2 * zbar 1 - zbar 0) / 3) • ![1, 2]) = _
    rw [hM.hom 1 _ n1 _ (by linarith)]
    change _ * cdtF (1 / 3) ![1, 2] = _
    simp only [cdtF, Matrix.cons_val_zero, Matrix.cons_val_one, Real.one_rpow, one_mul]
    norm_num
    ring

/-- **Exercise 15.D.8** (MWG, p. 544), specialization in good 1. For `z̄ ≫ 0` with
`ρ = z̄₁/z̄₂ ≥ 2` the factor market equilibria at `p = (1, 1)` are exactly
`w = ((2/3) ρ^{-1/3}, (1/3) ρ^{2/3})`, `z = (z̄, 0)`. -/
theorem exercise_15_D_8_spec0 {zbar w : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (hz : StrictlyPositive zbar) (hρ : 2 ≤ zbar 0 / zbar 1) :
    IsFactorEqm cdModel.f ![1, 1] zbar w z ↔
      w = cd8WSpec0 (zbar 0 / zbar 1) ∧ z = ![zbar, 0] := by
  have hM := cdModel_isModel
  have hFI := cdModel_factorIntensity
  have hρ0 : 0 < zbar 0 / zbar 1 := div_pos (hz 0) (hz 1)
  have hW := cd8WSpec0_pos hρ0
  have hkW : cdModel.a 0 (cd8WSpec0 (zbar 0 / zbar 1)) 0 /
      cdModel.a 0 (cd8WSpec0 (zbar 0 / zbar 1)) 1 = zbar 0 / zbar 1 := by
    rw [(cdModel_ratio hW).1]
    have hrel := cd8WSpec0_rel hρ0
    have h0 := hW 0
    have h1 := hW 1
    have hz0 := (hz 0).ne'
    have hz1 := (hz 1).ne'
    field_simp at hrel ⊢
    linarith
  constructor
  · intro h
    obtain ⟨hz', hc0, hk⟩ := TwoByTwo.exercise_15_D_6d_spec0_unique hM hFI cd8What_pos cd8What_c
      hz (by rw [cd8What_ratio.1]; exact hρ) h
    have hw := h.1
    refine ⟨TwoByTwo.eq_of_relPrice_eq_of_c_eq hM 0 hw hW ?_ ?_, hz'⟩
    · rw [(cdModel_ratio hw).1] at hk
      rw [(cdModel_ratio hW).1] at hkW
      have h0 := hw 0
      have h1 := hw 1
      have h0' := hW 0
      have h1' := hW 1
      rw [div_eq_div_iff h1.ne' h1'.ne']
      rw [← hkW, div_eq_div_iff h0.ne' h0'.ne'] at hk
      linarith
    · rw [hc0, cd8WSpec0_c0 hρ0]
      rfl
  · rintro ⟨rfl, rfl⟩
    refine TwoByTwo.exercise_15_D_6d_spec0 hM hFI cd8What_pos cd8What_c hz hW
      (cd8WSpec0_c0 hρ0) hkW ?_
    rw [cd8WSpec0_rel hρ0]
    have : cd8What 0 / cd8What 1 = 1 := div_self (cd8What_pos 1).ne'
    rw [this, div_le_one hρ0]
    exact hρ

/-- **Exercise 15.D.8** (MWG, p. 544), specialization in good 2. For `z̄ ≫ 0` with
`ρ = z̄₁/z̄₂ ≤ 1/2` the factor market equilibria at `p = (1, 1)` are exactly
`w = ((1/3) ρ^{-2/3}, (2/3) ρ^{1/3})`, `z = (0, z̄)`. -/
theorem exercise_15_D_8_spec1 {zbar w : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (hz : StrictlyPositive zbar) (hρ : zbar 0 / zbar 1 ≤ 1 / 2) :
    IsFactorEqm cdModel.f ![1, 1] zbar w z ↔
      w = cd8WSpec1 (zbar 0 / zbar 1) ∧ z = ![0, zbar] := by
  have hM := cdModel_isModel
  have hFI := cdModel_factorIntensity
  have hρ0 : 0 < zbar 0 / zbar 1 := div_pos (hz 0) (hz 1)
  have hW := cd8WSpec1_pos hρ0
  have hkW : cdModel.a 1 (cd8WSpec1 (zbar 0 / zbar 1)) 0 /
      cdModel.a 1 (cd8WSpec1 (zbar 0 / zbar 1)) 1 = zbar 0 / zbar 1 := by
    rw [(cdModel_ratio hW).2]
    have hrel := cd8WSpec1_rel hρ0
    have h0 := hW 0
    have h1 := hW 1
    have hz0 := (hz 0).ne'
    have hz1 := (hz 1).ne'
    field_simp at hrel ⊢
    linarith
  constructor
  · intro h
    obtain ⟨hz', hc1, hk⟩ := TwoByTwo.exercise_15_D_6d_spec1_unique hM hFI cd8What_pos cd8What_c
      hz (by rw [cd8What_ratio.2]; exact hρ) h
    have hw := h.1
    refine ⟨TwoByTwo.eq_of_relPrice_eq_of_c_eq hM 1 hw hW ?_ ?_, hz'⟩
    · rw [(cdModel_ratio hw).2] at hk
      rw [(cdModel_ratio hW).2] at hkW
      have h0 := hw 0
      have h1 := hw 1
      have h0' := hW 0
      have h1' := hW 1
      rw [div_eq_div_iff h1.ne' h1'.ne']
      rw [← hkW, div_eq_div_iff (by positivity) (by positivity)] at hk
      linarith
    · rw [hc1, cd8WSpec1_c1 hρ0]
      rfl
  · rintro ⟨rfl, rfl⟩
    refine TwoByTwo.exercise_15_D_6d_spec1 hM hFI cd8What_pos cd8What_c hz hW
      (cd8WSpec1_c1 hρ0) hkW ?_
    rw [cd8WSpec1_rel hρ0]
    have : cd8What 0 / cd8What 1 = 1 := div_self (cd8What_pos 1).ne'
    rw [this, le_div_iff₀ (by positivity)]
    linarith

/-- **Exercise 15.D.8** (MWG, p. 544), summary: for every `z̄ ≫ 0` there is exactly one factor
market equilibrium at `p = (1, 1)`, given by the formula of the region of `ρ = z̄₁/z̄₂`
(`ρ ≥ 2`: specialization in good 1; `ρ ≤ 1/2`: specialization in good 2; otherwise
diversified). -/
theorem exercise_15_D_8 {zbar : Fin 2 → ℝ} (hz : StrictlyPositive zbar) :
    ∃! wz : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ), IsFactorEqm cdModel.f ![1, 1] zbar wz.1 wz.2 := by
  by_cases h2 : 2 ≤ zbar 0 / zbar 1
  · refine ⟨(cd8WSpec0 (zbar 0 / zbar 1), ![zbar, 0]), (exercise_15_D_8_spec0 hz h2).2
      ⟨rfl, rfl⟩, fun wz h => ?_⟩
    obtain ⟨h1, h2⟩ := (exercise_15_D_8_spec0 hz h2).1 h
    exact Prod.ext h1 h2
  by_cases h1 : zbar 0 / zbar 1 ≤ 1 / 2
  · refine ⟨(cd8WSpec1 (zbar 0 / zbar 1), ![0, zbar]), (exercise_15_D_8_spec1 hz h1).2
      ⟨rfl, rfl⟩, fun wz h => ?_⟩
    obtain ⟨e1, e2⟩ := (exercise_15_D_8_spec1 hz h1).1 h
    exact Prod.ext e1 e2
  rw [not_le] at h1 h2
  refine ⟨(cd8What, cd8ZDiv zbar), (exercise_15_D_8_diversified hz h1 h2).2 ⟨rfl, rfl⟩,
    fun wz h => ?_⟩
  obtain ⟨e1, e2⟩ := (exercise_15_D_8_diversified hz h1 h2).1 h
  exact Prod.ext e1 e2

end MWG.GeneralEquilibriumExamples
