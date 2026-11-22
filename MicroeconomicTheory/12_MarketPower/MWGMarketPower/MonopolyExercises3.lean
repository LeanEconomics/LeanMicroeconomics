/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.MonopolyExercises
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Exercises 12.B.2(c) and 12.B.5

MWG, Exercises 12.B.2(c) and 12.B.5(a)-(b), p. 429.

* 12.B.2(c): constant-elasticity demand `x(p) = αp^{-ε}`, unit cost `c > 0`, `ε > 1`, with `α`
  adjusted so that the competitive quantity `x(c) = X` is the same for every `ε` (`α = Xc^ε`).
  The deadweight loss is, in closed form,
  `DWL(ε) = Xc(1 − ((ε − 1)/ε)^{ε−1}(2ε − 1)/ε)/(ε − 1)` (`ceDWL`); it equals the book's
  integral `∫_{qᵐ}^{X}(p(s) − c) ds` (`exercise_12_B_2c_derivation`). It is positive, strictly
  DECREASING in `ε` on `(1, ∞)`, tends to `+∞` as `ε → 1⁺` and to `0` as `ε → ∞`, with
  `(ε − 1)DWL(ε) → Xc(1 − 2/e)`. The "computer" part is numerical; two exact values
  (`ε = 2, 3`) are proved.
* 12.B.5 (a verbal "argue" exercise) is formalized with the following models (correction 52).
  The monopolist cannot discern preferences, so it offers ONE menu `M ⊆ ℕ × ℝ` of
  (number of units, total payment) offers to every consumer, always containing the null offer
  `(0, 0)`; any nonlinear price schedule `T` is the menu `{(k, T k)}`, and a single per-unit
  price `p` is the menu `{(k, pk)}`. Unit cost is a constant `c`.
  (a) Unit demand: consumer `i` values one unit at `vᵢ` and further units at zero; each consumer
  picks a utility-maximizing offer. For any menu and any optimal choices there is a per-unit price
  `p ≥ 0` and optimal choices at `p` with at least the same profit (`exercise_12_B_5a`; needs
  `c ≥ 0`).
  (b) Multiple units and costless resale in a competitive resale market: given the resale price
  `ρ`, each consumer chooses an offer from `M` and a final consumption `xᵢ`, trading `xᵢ − kᵢ`
  at `ρ`; the resale market clears. Then the purchases maximize `ρk − T` (arbitrage) and the
  consumptions are the demands at the single price `ρ`, and the profit is at most the profit of
  the single per-unit price `ρ` (`exercise_12_B_5b`). Without resale the claim fails: a bundle
  beats every single price (`exercise_12_B_5b_needs_resale`).
-/

namespace MWG.MarketPower

open Set Filter Topology

/-! ### Exercise 12.B.2(c) -/

/-- The deadweight loss of constant-elasticity monopoly with unit cost `c` and elasticity `ε`
when `α` is chosen so that the competitive quantity `x(c)` equals `X`:
`Xc(1 − ((ε − 1)/ε)^{ε−1}(2ε − 1)/ε)/(ε − 1)`. -/
noncomputable def ceDWL (X c ε : ℝ) : ℝ :=
  X * c * ((1 - ((ε - 1) / ε) ^ (ε - 1) * ((2 * ε - 1) / ε)) / (ε - 1))

/-- The deadweight loss per unit of `Xc`: `ceDWL X c ε = Xc · ceDWLShape ε`. -/
noncomputable def ceDWLShape (ε : ℝ) : ℝ :=
  (1 - ((ε - 1) / ε) ^ (ε - 1) * ((2 * ε - 1) / ε)) / (ε - 1)

theorem ceDWL_eq (X c ε : ℝ) : ceDWL X c ε = X * c * ceDWLShape ε := rfl

/-- **Exercise 12.B.2(c), derivation** (MWG, p. 429). With `α = Xc^ε` the competitive quantity
is `x(c) = X` and the monopoly quantity `qᵐ = α(pᵐ)^{-ε}` (with `pᵐ = εc/(ε − 1)`) is below `X`;
the deadweight loss `∫_{qᵐ}^{X}(p(s) − c) ds`, with inverse demand `p(s) = α^{1/ε}s^{-1/ε}`, is
`ceDWL X c ε`. -/
theorem exercise_12_B_2c_derivation {X c ε : ℝ} (hX : 0 < X) (hc : 0 < c) (hε : 1 < ε) :
    X * c ^ ε * c ^ (-ε) = X ∧ X * c ^ ε * (ε * c / (ε - 1)) ^ (-ε) < X ∧
    ∫ s in (X * c ^ ε * (ε * c / (ε - 1)) ^ (-ε))..X,
      ((X * c ^ ε) ^ (1 / ε) * s ^ (-(1 / ε)) - c) = ceDWL X c ε := by
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  set r := (ε - 1) / ε with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hε0]; linarith
  have hpm : ε * c / (ε - 1) = c / r := by rw [hr]; field_simp
  have hqm : X * c ^ ε * (ε * c / (ε - 1)) ^ (-ε) = X * r ^ ε := by
    rw [hpm, Real.rpow_neg (by positivity), Real.div_rpow hc.le hr0.le]
    have : 0 < c ^ ε := Real.rpow_pos_of_pos hc _
    field_simp
  have hrε : r ^ ε < 1 := Real.rpow_lt_one hr0.le hr1 hε0
  have hcX : X * c ^ ε * c ^ (-ε) = X := by
    rw [mul_assoc, ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, mul_one]
  refine ⟨hcX, ?_, ?_⟩
  · rw [hqm]; nlinarith
  have hα : 0 < X * c ^ ε := mul_pos hX (Real.rpow_pos_of_pos hc _)
  have hqm0 : 0 < X * r ^ ε := mul_pos hX (Real.rpow_pos_of_pos hr0 _)
  rw [hqm, (exercise_12_B_2b_dwl (c := c) hα hε hqm0 (by nlinarith)).2]
  have h1 : (X * c ^ ε) ^ (1 / ε) = X ^ (1 / ε) * c := by
    rw [Real.mul_rpow hX.le (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le,
      mul_one_div_cancel hε0.ne', Real.rpow_one]
  have h2 : (X * r ^ ε) ^ (1 - 1 / ε) = X ^ (1 - 1 / ε) * r ^ (ε - 1) := by
    rw [Real.mul_rpow hX.le (Real.rpow_nonneg hr0.le _), ← Real.rpow_mul hr0.le]
    congr 2; field_simp
  have h3 : X ^ (1 / ε) * X ^ (1 - 1 / ε) = X := by
    rw [← Real.rpow_add hX, show 1 / ε + (1 - 1 / ε) = 1 by ring, Real.rpow_one]
  have h4 : r ^ ε = r ^ (ε - 1) * r := by
    rw [← Real.rpow_add_one hr0.ne', sub_add_cancel]
  unfold ceDWL
  rw [h1, h2, ← hr, h4]
  have h6 : 1 - 1 / ε = (ε - 1) / ε := by field_simp
  rw [h6]
  set R := r ^ (ε - 1)
  have h7 : X ^ (1 / ε) * X ^ ((ε - 1) / ε) = X := by rw [← h6]; exact h3
  rw [hr]
  field_simp
  linear_combination (ε ^ 2 * (1 - R)) * h7

/-- The key bounds behind 12.B.2(c): for `ε > 1` and `y = −(ε − 1) log((ε − 1)/ε)`
(so that `((ε − 1)/ε)^{ε−1} = e^{−y}`), `1 − 1/ε < y < 1`. -/
theorem ceDWL_y_bounds {ε : ℝ} (hε : 1 < ε) :
    1 - ε⁻¹ < -((ε - 1) * Real.log ((ε - 1) / ε)) ∧
      -((ε - 1) * Real.log ((ε - 1) / ε)) < 1 := by
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  have hr0 : 0 < (ε - 1) / ε := by positivity
  have hr1 : (ε - 1) / ε ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hε0.ne'] at h; linarith
  have h1 := Real.log_lt_sub_one_of_pos hr0 hr1
  have hq0 : 0 < ε / (ε - 1) := by positivity
  have hq1 : ε / (ε - 1) ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hε1.ne'] at h; linarith
  have h2 := Real.log_lt_sub_one_of_pos hq0 hq1
  have hL : Real.log ((ε - 1) / ε) = -Real.log (ε / (ε - 1)) := by
    rw [← Real.log_inv, inv_div]
  have e1 : (ε - 1) / ε - 1 = -ε⁻¹ := by field_simp; ring
  have e2 : ε / (ε - 1) - 1 = (ε - 1)⁻¹ := by field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  constructor
  · have : (ε - 1) * ε⁻¹ < (ε - 1) * -Real.log ((ε - 1) / ε) :=
      mul_lt_mul_of_pos_left (by linarith) hε1
    have e3 : (ε - 1) * ε⁻¹ = 1 - ε⁻¹ := by field_simp
    linarith
  · rw [hL]
    have : (ε - 1) * Real.log (ε / (ε - 1)) < (ε - 1) * (ε - 1)⁻¹ :=
      mul_lt_mul_of_pos_left h2 hε1
    rw [mul_inv_cancel₀ hε1.ne'] at this
    linarith

/-- The power in `ceDWL` as an exponential: `((ε − 1)/ε)^{ε−1} = exp(log((ε − 1)/ε)(ε − 1))`. -/
theorem ceDWL_rpow_eq {ε : ℝ} (hε : 1 < ε) :
    ((ε - 1) / ε) ^ (ε - 1) = Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) :=
  Real.rpow_def_of_pos (div_pos (by linarith) (by linarith)) _

/-- `exp(log((ε − 1)/ε)(ε − 1)) · e^{y} = 1` with `y = −(ε − 1) log((ε − 1)/ε)`. -/
theorem ceDWL_exp_mul (ε : ℝ) :
    Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) *
      Real.exp (-((ε - 1) * Real.log ((ε - 1) / ε))) = 1 := by
  rw [← Real.exp_add, show Real.log ((ε - 1) / ε) * (ε - 1) +
    -((ε - 1) * Real.log ((ε - 1) / ε)) = 0 by ring, Real.exp_zero]

/-- **Exercise 12.B.2(c), positivity** (MWG, p. 429). The deadweight loss is positive. -/
theorem ceDWLShape_pos {ε : ℝ} (hε : 1 < ε) : 0 < ceDWLShape ε := by
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  obtain ⟨hlo, -⟩ := ceDWL_y_bounds hε
  set y := -((ε - 1) * Real.log ((ε - 1) / ε))
  set E := Real.exp (Real.log ((ε - 1) / ε) * (ε - 1))
  have hE : E * Real.exp y = 1 := ceDWL_exp_mul ε
  have hE0 : 0 < E := Real.exp_pos _
  have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hεy : ε - 1 < ε * y := by
    have := mul_lt_mul_of_pos_left hlo hε0
    rw [mul_sub, mul_inv_cancel₀ hε0.ne', mul_one] at this
    exact this
  have k1 : E * ε * (y + 1) ≤ E * ε * Real.exp y :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have k2 : E * (2 * ε - 1) < E * (ε * (y + 1)) := mul_lt_mul_of_pos_left (by linarith) hE0
  have key : E * (2 * ε - 1) < ε := by nlinarith
  unfold ceDWLShape
  rw [ceDWL_rpow_eq hε]
  apply div_pos _ hε1
  rw [sub_pos, ← mul_div_assoc, div_lt_one hε0]
  exact key

/-- The derivative of the exponential form of `ceDWLShape` at `x > 1`. -/
theorem ceDWLShape_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun ε => (1 - Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) *
      ((2 * ε - 1) / ε)) / (ε - 1))
      ((Real.exp (Real.log ((x - 1) / x) * (x - 1)) *
        (1 - (2 * x - 1) * ((x - 1) * Real.log ((x - 1) / x))) / x - 1) / (x - 1) ^ 2) x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hg := ((hasDerivAt_id' x).sub_const 1).div (hasDerivAt_id' x) hx0.ne'
  have hL := hg.log (div_pos hx1 hx0).ne'
  have hA := hL.mul ((hasDerivAt_id' x).sub_const 1)
  have hE := hA.exp
  have hB := (((hasDerivAt_id' x).const_mul 2).sub_const 1).div (hasDerivAt_id' x) hx0.ne'
  have hN := (hasDerivAt_const x (1 : ℝ)).sub (hE.mul hB)
  have hF := hN.div ((hasDerivAt_id' x).sub_const 1) hx1.ne'
  refine hF.congr_deriv ?_
  simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

/-- **Exercise 12.B.2(c), monotonicity** (MWG, p. 429). The deadweight loss per unit of `Xc`
is strictly decreasing in `ε` on `(1, ∞)`. -/
theorem ceDWLShape_strictAntiOn : StrictAntiOn ceDWLShape (Ioi 1) := by
  set F := fun ε : ℝ => (1 - Real.exp (Real.log ((ε - 1) / ε) * (ε - 1)) *
      ((2 * ε - 1) / ε)) / (ε - 1) with hFdef
  have hEq : ∀ ε, 1 < ε → ceDWLShape ε = F ε := by
    intro ε hε; unfold ceDWLShape; rw [ceDWL_rpow_eq hε]
  have hanti : StrictAntiOn F (Ioi 1) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 1)
      (f' := fun x => (Real.exp (Real.log ((x - 1) / x) * (x - 1)) *
        (1 - (2 * x - 1) * ((x - 1) * Real.log ((x - 1) / x))) / x - 1) / (x - 1) ^ 2)
      (fun x hx => (ceDWLShape_hasDerivAt hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioi] at hx; exact (ceDWLShape_hasDerivAt hx).hasDerivWithinAt
    · rw [interior_Ioi] at hx
      have hx' : 1 < x := hx
      have hx0 : 0 < x := by linarith
      have hx1 : 0 < x - 1 := by linarith
      obtain ⟨-, hhi⟩ := ceDWL_y_bounds hx'
      set L := Real.log ((x - 1) / x)
      set y := -((x - 1) * L)
      set E := Real.exp (L * (x - 1))
      have hE : E * Real.exp y = 1 := ceDWL_exp_mul x
      have hE0 : 0 < E := Real.exp_pos _
      have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
      have k1 : E * x * (y + 1) ≤ E * x * Real.exp y :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have k2 : E * (1 + (2 * x - 1) * y) < E * (x * (y + 1)) := by
        apply mul_lt_mul_of_pos_left _ hE0
        nlinarith
      have key : E * (1 - (2 * x - 1) * ((x - 1) * L)) < x := by
        have : E * (1 - (2 * x - 1) * ((x - 1) * L)) = E * (1 + (2 * x - 1) * y) := by
          simp only [y]; ring
        rw [this]; nlinarith
      apply div_neg_of_neg_of_pos _ (by positivity)
      rw [sub_neg, div_lt_one hx0]
      exact key
  intro a ha b hb hab
  rw [hEq a ha, hEq b hb]
  exact hanti ha hb hab

/-- `(ε − 1) · ceDWLShape ε = 1 − e^{−y}(2ε − 1)/ε` for `ε > 1`, with
`y = −(ε − 1) log((ε − 1)/ε)`. -/
theorem ceDWLShape_scaled_eq {ε : ℝ} (hε : 1 < ε) :
    (ε - 1) * ceDWLShape ε =
      1 - Real.exp (-(-((ε - 1) * Real.log ((ε - 1) / ε)))) * ((2 * ε - 1) / ε) := by
  have hε1 : 0 < ε - 1 := by linarith
  unfold ceDWLShape
  rw [ceDWL_rpow_eq hε, neg_neg, mul_comm (ε - 1) (Real.log _)]
  field_simp

/-- **Exercise 12.B.2(c), the limit `ε → ∞`** (MWG, p. 429): `(ε − 1) · DWL/(Xc) → 1 − 2/e`. -/
theorem ceDWLShape_scaled_tendsto :
    Tendsto (fun ε => (ε - 1) * ceDWLShape ε) atTop (𝓝 (1 - Real.exp (-1) * 2)) := by
  have hlow : Tendsto (fun ε : ℝ => 1 - ε⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      tendsto_inv_atTop_zero
  have hy : Tendsto (fun ε : ℝ => -((ε - 1) * Real.log ((ε - 1) / ε))) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with ε hε using (ceDWL_y_bounds hε).1.le
    · filter_upwards [eventually_gt_atTop 1] with ε hε using (ceDWL_y_bounds hε).2.le
  have hB : Tendsto (fun ε : ℝ => 2 - ε⁻¹) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2)).sub
      tendsto_inv_atTop_zero
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
    (((Real.continuous_exp.tendsto (-1)).comp hy.neg).mul hB)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with ε hε
  have hε0 : 0 < ε := by linarith
  rw [ceDWLShape_scaled_eq hε]
  simp only [Function.comp_apply]
  congr 2
  field_simp

/-- **Exercise 12.B.2(c), the limit `ε → ∞`** (MWG, p. 429): the deadweight loss vanishes. -/
theorem ceDWLShape_tendsto_atTop : Tendsto ceDWLShape atTop (𝓝 0) := by
  have hinv : Tendsto (fun ε : ℝ => (ε - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have h := ceDWLShape_scaled_tendsto.mul hinv
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with ε hε
  have hε1 : 0 < ε - 1 := by linarith
  field_simp

/-- **Exercise 12.B.2(c), the limit `ε → 1⁺`** (MWG, p. 429): the deadweight loss becomes
unbounded. -/
theorem ceDWLShape_tendsto_one : Tendsto ceDWLShape (𝓝[>] 1) atTop := by
  have hsub : Tendsto (fun ε : ℝ => ε - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => ε - 1) (𝓝 1) (𝓝 0) :=
        (continuous_sub_right (1 : ℝ)).tendsto' 1 0 (by norm_num)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Set.mem_Ioi.2 (sub_pos.2 (Set.mem_Ioi.1 hε))
  have hlog : Tendsto (fun ε : ℝ => Real.log ((ε - 1)⁻¹)) (𝓝[>] 1) atTop :=
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hsub)
  have hlow : Tendsto (fun ε : ℝ => (Real.log ((ε - 1)⁻¹) - 1) / 2) (𝓝[>] 1) atTop :=
    (tendsto_atTop_add_const_right _ (-1) hlog).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 1 < ε := hε
  have hε0 : 0 < ε := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := ceDWL_y_bounds hε'
  set L := Real.log ((ε - 1) / ε)
  set y := -((ε - 1) * L)
  set E := Real.exp (L * (ε - 1))
  have hE : E * Real.exp y = 1 := ceDWL_exp_mul ε
  have hE0 : 0 < E := Real.exp_pos _
  have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hL : L = -Real.log (ε / (ε - 1)) := by
    simp only [L]; rw [← Real.log_inv, inv_div]
  have hlogle : Real.log ((ε - 1)⁻¹) ≤ -L := by
    rw [hL, neg_neg]
    apply Real.log_le_log (by positivity)
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left (by positivity) hε'.le
  have hEy : E * (y + 1) ≤ 1 := by nlinarith
  have hB0 : 0 < (2 * ε - 1) / ε := by
    apply div_pos _ hε0; linarith
  -- `(1 + y)(1 − EB) ≥ 1 + y − B = (ε − 1)(−L − 1/ε)`
  have h1 : (y + 1) * (1 - E * ((2 * ε - 1) / ε)) ≥ y + 1 - (2 * ε - 1) / ε := by
    nlinarith [mul_le_mul_of_nonneg_right hEy hB0.le]
  have h2 : y + 1 - (2 * ε - 1) / ε = (ε - 1) * (-L - ε⁻¹) := by
    simp only [y]; field_simp; ring
  have hpos : 0 < -L - ε⁻¹ := by
    have : (ε - 1) * ε⁻¹ < (ε - 1) * -L := by
      have e3 : (ε - 1) * ε⁻¹ = 1 - ε⁻¹ := by field_simp
      rw [e3]; simp only [y] at hlo; linarith
    linarith [lt_of_mul_lt_mul_left this hε1.le]
  have hS : (ε - 1) * ceDWLShape ε = 1 - E * ((2 * ε - 1) / ε) := by
    have e4 : (ε - 1) * Real.log ((ε - 1) / ε) = L * (ε - 1) := by simp only [L]; ring
    rw [ceDWLShape_scaled_eq hε', neg_neg, e4]
  have hinv : ε⁻¹ < 1 := inv_lt_one_of_one_lt₀ hε'
  -- `(y + 1)(ε − 1)·shape ≥ (ε − 1)(−L − 1/ε)` and `y + 1 < 2`
  have h3 : (y + 1) * ceDWLShape ε ≥ -L - ε⁻¹ := by
    have : (ε - 1) * ((y + 1) * ceDWLShape ε) ≥ (ε - 1) * (-L - ε⁻¹) := by
      nlinarith
    exact le_of_mul_le_mul_left this hε1
  have hsh : 0 < ceDWLShape ε := ceDWLShape_pos hε'
  have hy2 : y + 1 < 2 := by linarith
  nlinarith

/-- **Exercise 12.B.2(c)** (MWG, p. 429). Holding the competitive quantity `x(c) = X > 0` fixed
(with `c > 0`), the deadweight loss `ceDWL X c ε` is positive and strictly decreasing in `ε` on
`(1, ∞)`; it tends to `+∞` as `ε → 1⁺` and to `0` as `ε → ∞`, and
`(ε − 1) · DWL(ε) → Xc(1 − 2/e)`. -/
theorem exercise_12_B_2c {X c : ℝ} (hX : 0 < X) (hc : 0 < c) :
    (∀ ε, 1 < ε → 0 < ceDWL X c ε) ∧ StrictAntiOn (ceDWL X c) (Ioi 1) ∧
    Tendsto (ceDWL X c) (𝓝[>] 1) atTop ∧ Tendsto (ceDWL X c) atTop (𝓝 0) ∧
    Tendsto (fun ε => (ε - 1) * ceDWL X c ε) atTop (𝓝 (X * c * (1 - Real.exp (-1) * 2))) := by
  have hXc : 0 < X * c := mul_pos hX hc
  refine ⟨fun ε hε => ?_, fun a ha b hb hab => ?_, ?_, ?_, ?_⟩
  · rw [ceDWL_eq]; exact mul_pos hXc (ceDWLShape_pos hε)
  · rw [ceDWL_eq, ceDWL_eq]
    exact mul_lt_mul_of_pos_left (ceDWLShape_strictAntiOn ha hb hab) hXc
  · exact ceDWLShape_tendsto_one.const_mul_atTop hXc
  · have h := ceDWLShape_tendsto_atTop.const_mul (X * c)
    rw [mul_zero] at h
    exact h
  · have h := ceDWLShape_scaled_tendsto.const_mul (X * c)
    refine h.congr fun ε => ?_
    rw [ceDWL_eq]; ring

/-- **Exercise 12.B.2(c), a computed value** (MWG, p. 429): at `ε = 2` the deadweight loss is
`Xc/4`. -/
theorem exercise_12_B_2c_eps2 (X c : ℝ) : ceDWL X c 2 = X * c / 4 := by
  unfold ceDWL
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

/-- **Exercise 12.B.2(c), a computed value** (MWG, p. 429): at `ε = 3` the deadweight loss is
`7Xc/54`, below its value `Xc/4` at `ε = 2`. -/
theorem exercise_12_B_2c_eps3 (X c : ℝ) : ceDWL X c 3 = 7 * X * c / 54 := by
  unfold ceDWL
  rw [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
  ring

/-! ### Exercise 12.B.5 -/

/-- The utility of a unit-demand consumer with valuation `v` from the offer `o = (k, t)`
(`k` units for the total payment `t`): `v − t` if `k ≥ 1` and `−t` if `k = 0`. -/
noncomputable def unitUtility (v : ℝ) (o : ℕ × ℝ) : ℝ := (if o.1 = 0 then 0 else v) - o.2

/-- In 12.B.5(a), a per-unit price high enough that nobody buys does at least as well as an
outcome in which every consumer's contribution `tᵢ − ckᵢ` to profit is nonpositive. -/
theorem unitMenu_highPrice {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (o : Fin n → ℕ × ℝ)
    (hle : ∀ i, (o i).2 - c * (o i).1 ≤ 0) :
    ∃ p, 0 ≤ p ∧ ∃ x : Fin n → ℕ,
      (∀ i, ∀ k : ℕ, unitUtility (v i) (k, p * k) ≤ unitUtility (v i) (x i, p * x i)) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (p * x i - c * x i) := by
  have hsum : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg (v i)
  refine ⟨c + ∑ i, |v i|, by linarith, fun _ => 0, fun i k => ?_, ?_⟩
  · have hvi : v i ≤ c + ∑ j, |v j| := by
      have := Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j))
        (Finset.mem_univ i)
      linarith [le_abs_self (v i)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [unitUtility]
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      simp only [unitUtility, hk.ne', ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
      nlinarith
  · simp only [Nat.cast_zero, mul_zero, sub_zero, Finset.sum_const_zero]
    exact Finset.sum_nonpos fun i _ => hle i

/-- The core of 12.B.5(a): if all buyers pay the same `P`, all non-buyers receive the same
`S ≥ 0`, buyers value the good at least at `P + S` and non-buyers at most at `P + S`, then a
single per-unit price does at least as well. -/
theorem unitMenu_core {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (o : Fin n → ℕ × ℝ)
    {P S : ℝ} (hS : 0 ≤ S) (hb : ∀ i, (o i).1 ≠ 0 → (o i).2 = P ∧ P + S ≤ v i)
    (hn : ∀ i, (o i).1 = 0 → (o i).2 = -S ∧ v i ≤ P + S) :
    ∃ p, 0 ≤ p ∧ ∃ x : Fin n → ℕ,
      (∀ i, ∀ k : ℕ, unitUtility (v i) (k, p * k) ≤ unitUtility (v i) (x i, p * x i)) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (p * x i - c * x i) := by
  by_cases hpc : c ≤ P + S
  · refine ⟨P + S, by linarith, fun i => if (o i).1 = 0 then 0 else 1, fun i k => ?_, ?_⟩
    · by_cases hi : (o i).1 = 0
      · obtain ⟨-, hv⟩ := hn i hi
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [unitUtility, hi]
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          simp only [unitUtility, hi, hk.ne', ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
          nlinarith
      · obtain ⟨-, hv⟩ := hb i hi
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp only [unitUtility, hi, ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero,
            Nat.cast_one, mul_one, one_ne_zero]
          linarith
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          simp only [unitUtility, hi, hk.ne', ↓reduceIte, Nat.cast_one, mul_one, one_ne_zero]
          nlinarith
    · refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : (o i).1 = 0
      · obtain ⟨ht, -⟩ := hn i hi
        simp only [hi, ht, ↓reduceIte, Nat.cast_zero, mul_zero, sub_zero]
        linarith
      · obtain ⟨ht, -⟩ := hb i hi
        have hk1 : (1 : ℝ) ≤ (o i).1 := by exact_mod_cast Nat.pos_of_ne_zero hi
        simp only [hi, ht, ↓reduceIte, Nat.cast_one, mul_one]
        nlinarith
  · push Not at hpc
    refine unitMenu_highPrice v hc o fun i => ?_
    by_cases hi : (o i).1 = 0
    · obtain ⟨ht, -⟩ := hn i hi
      rw [ht, hi]; simp only [Nat.cast_zero, mul_zero, sub_zero]; linarith
    · obtain ⟨ht, -⟩ := hb i hi
      have hk1 : (1 : ℝ) ≤ (o i).1 := by exact_mod_cast Nat.pos_of_ne_zero hi
      rw [ht]; nlinarith

/-- **Exercise 12.B.5(a)** (MWG, p. 429). Many consumers, each wanting at most one unit
(valuation `vᵢ` for one unit, nothing for more), and a monopolist with unit cost `c ≥ 0` who
cannot discern preferences and so offers the same menu `M` of (units, total payment) offers to
everyone, including the null offer `(0, 0)`. Whatever the menu and whatever utility-maximizing
choices the consumers make, there is a per-unit price `p ≥ 0` and utility-maximizing choices
at `p` that give at least the same profit: the monopolist does no better than a single price. -/
theorem exercise_12_B_5a {n : ℕ} (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (M : Set (ℕ × ℝ))
    (h0 : ((0 : ℕ), (0 : ℝ)) ∈ M) (o : Fin n → ℕ × ℝ)
    (ho : ∀ i, o i ∈ M ∧ ∀ o' ∈ M, unitUtility (v i) o' ≤ unitUtility (v i) (o i)) :
    ∃ p, 0 ≤ p ∧ ∃ x : Fin n → ℕ,
      (∀ i, ∀ k : ℕ, unitUtility (v i) (k, p * k) ≤ unitUtility (v i) (x i, p * x i)) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (p * x i - c * x i) := by
  have hu : ∀ i j, unitUtility (v i) (o j) = (if (o j).1 = 0 then 0 else v i) - (o j).2 :=
    fun _ _ => rfl
  have hu0 : ∀ i, unitUtility (v i) ((0 : ℕ), (0 : ℝ)) = 0 := fun i => by simp [unitUtility]
  by_cases hB : ∃ j, (o j).1 ≠ 0
  · obtain ⟨j, hj⟩ := hB
    have hbuy : ∀ i, (o i).1 ≠ 0 → (o i).2 = (o j).2 := by
      intro i hi
      have h1 := (ho i).2 (o j) (ho j).1
      have h2 := (ho j).2 (o i) (ho i).1
      rw [hu, hu] at h1 h2
      simp only [hi, hj, ↓reduceIte] at h1 h2
      linarith
    by_cases hN : ∃ m, (o m).1 = 0
    · obtain ⟨m, hm⟩ := hN
      have hS : 0 ≤ -(o m).2 := by
        have := (ho m).2 _ h0
        rw [hu0, hu] at this; simp only [hm, ↓reduceIte] at this; linarith
      refine unitMenu_core v hc o hS (fun i hi => ⟨hbuy i hi, ?_⟩) (fun i hi => ⟨?_, ?_⟩)
      · have := (ho i).2 (o m) (ho m).1
        rw [hu, hu] at this; simp only [hm, hi, ↓reduceIte] at this
        rw [hbuy i hi] at this; linarith
      · have h1 := (ho i).2 (o m) (ho m).1
        have h2 := (ho m).2 (o i) (ho i).1
        rw [hu, hu] at h1 h2
        simp only [hi, hm, ↓reduceIte] at h1 h2
        linarith
      · have h2 := (ho i).2 (o j) (ho j).1
        have h3 := (ho m).2 (o i) (ho i).1
        rw [hu, hu] at h2 h3
        simp only [hi, hm, hj, ↓reduceIte] at h2 h3
        linarith
    · push Not at hN
      refine unitMenu_core v hc o le_rfl (fun i hi => ⟨hbuy i hi, ?_⟩)
        (fun i hi => absurd hi (hN i))
      have := (ho i).2 _ h0
      rw [hu0, hu] at this; simp only [hi, ↓reduceIte] at this
      rw [hbuy i hi] at this; linarith
  · push Not at hB
    refine unitMenu_highPrice v hc o fun i => ?_
    have := (ho i).2 _ h0
    rw [hu0, hu] at this; simp only [hB i, ↓reduceIte] at this
    rw [hB i]; simp only [Nat.cast_zero, mul_zero, sub_zero]; linarith

/-- **Exercise 12.B.5(a), an instance** (MWG, p. 429): valuations `3` and `1`, unit cost `1/2`,
the menu `{(0, 0), (1, 2), (2, 3)}`; the first consumer buys one unit for `2`, the second buys
nothing, and these choices are utility-maximizing (so `exercise_12_B_5a` applies). -/
theorem exercise_12_B_5a_instance :
    ∀ i : Fin 2, ![((1 : ℕ), (2 : ℝ)), ((0 : ℕ), (0 : ℝ))] i ∈
        ({(0, 0), (1, 2), (2, 3)} : Set (ℕ × ℝ)) ∧
      ∀ o' ∈ ({(0, 0), (1, 2), (2, 3)} : Set (ℕ × ℝ)),
        unitUtility (![3, 1] i) o' ≤
          unitUtility (![3, 1] i) (![((1 : ℕ), (2 : ℝ)), ((0 : ℕ), (0 : ℝ))] i) := by
  intro i
  fin_cases i
  · refine ⟨by simp, ?_⟩
    rintro o' (rfl | rfl | rfl) <;> norm_num [unitUtility]
  · refine ⟨by simp, ?_⟩
    rintro o' (rfl | rfl | rfl) <;> norm_num [unitUtility]

/-- A resale equilibrium for 12.B.5(b). Consumer `i` has utility `uᵢ(y) − (payment)` from
consuming `y` units. The monopolist offers the same menu `M` of (units, total payment) offers to
everyone. Given the competitive resale price `ρ`, each consumer chooses an offer `oᵢ = (kᵢ, tᵢ)`
from `M` and a final consumption `xᵢ`, selling (or buying) `kᵢ − xᵢ` units costlessly at `ρ`,
to maximize `uᵢ(xᵢ) − tᵢ − ρ(xᵢ − kᵢ)`; the resale market clears, `∑ xᵢ = ∑ kᵢ`. -/
def IsResaleEquilibrium {n : ℕ} (u : Fin n → ℕ → ℝ) (M : Set (ℕ × ℝ)) (ρ : ℝ)
    (o : Fin n → ℕ × ℝ) (x : Fin n → ℕ) : Prop :=
  (∀ i, o i ∈ M ∧ ∀ o' ∈ M, ∀ y : ℕ,
    u i y - o'.2 - ρ * ((y : ℝ) - o'.1) ≤ u i (x i) - (o i).2 - ρ * ((x i : ℝ) - (o i).1)) ∧
  ∑ i, x i = ∑ i, (o i).1

/-- **Exercise 12.B.5(b), costless resale separates purchase from consumption** (MWG, p. 429).
A profile is a resale equilibrium iff every consumer's purchase maximizes its resale value
`ρk − t` over the menu (arbitrage), every consumer's consumption is its demand at the single
per-unit price `ρ`, and the resale market clears. -/
theorem isResaleEquilibrium_iff {n : ℕ} (u : Fin n → ℕ → ℝ) (M : Set (ℕ × ℝ)) (ρ : ℝ)
    (o : Fin n → ℕ × ℝ) (x : Fin n → ℕ) :
    IsResaleEquilibrium u M ρ o x ↔
      (∀ i, o i ∈ M ∧ ∀ o' ∈ M, ρ * o'.1 - o'.2 ≤ ρ * (o i).1 - (o i).2) ∧
      (∀ i, ∀ k : ℕ, u i k - ρ * k ≤ u i (x i) - ρ * x i) ∧ ∑ i, x i = ∑ i, (o i).1 := by
  constructor
  · rintro ⟨h, hcl⟩
    refine ⟨fun i => ⟨(h i).1, fun o' ho' => ?_⟩, fun i k => ?_, hcl⟩
    · have := (h i).2 o' ho' (x i); linarith
    · have := (h i).2 (o i) (h i).1 k; linarith
  · rintro ⟨ha, hd, hcl⟩
    refine ⟨fun i => ⟨(ha i).1, fun o' ho' y => ?_⟩, hcl⟩
    have h1 := (ha i).2 o' ho'
    have h2 := hd i y
    linarith

/-- **Exercise 12.B.5(b)** (MWG, p. 429). Many consumers with arbitrary multi-unit utilities
`uᵢ`, a monopolist with unit cost `c` who cannot discern preferences and offers one menu `M`
(any nonlinear price schedule) containing `(0, 0)`, and costless resale in a competitive resale
market. In any resale equilibrium with resale price `ρ`, the consumptions are the demands at the
single per-unit price `ρ`, and the monopolist's profit is at most the profit `∑ (ρ − c)xᵢ` of
charging the single per-unit price `ρ`. -/
theorem exercise_12_B_5b {n : ℕ} (u : Fin n → ℕ → ℝ) (c : ℝ) (M : Set (ℕ × ℝ))
    (h0 : ((0 : ℕ), (0 : ℝ)) ∈ M) {ρ : ℝ} {o : Fin n → ℕ × ℝ} {x : Fin n → ℕ}
    (heq : IsResaleEquilibrium u M ρ o x) :
    (∀ i, ∀ k : ℕ, u i k - ρ * k ≤ u i (x i) - ρ * x i) ∧
      ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (ρ * x i - c * x i) := by
  obtain ⟨ha, hd, hcl⟩ := (isResaleEquilibrium_iff u M ρ o x).1 heq
  refine ⟨hd, ?_⟩
  have ht : ∀ i, (o i).2 ≤ ρ * (o i).1 := by
    intro i; have := (ha i).2 _ h0; simp only [Nat.cast_zero, mul_zero, sub_zero] at this
    linarith
  have hcl' : ∑ i, ((x i : ℕ) : ℝ) = ∑ i, (((o i).1 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, hcl]
  calc ∑ i, ((o i).2 - c * (o i).1) ≤ ∑ i, (ρ * (o i).1 - c * (o i).1) :=
        Finset.sum_le_sum fun i _ => by linarith [ht i]
    _ = (ρ - c) * ∑ i, (((o i).1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = (ρ - c) * ∑ i, ((x i : ℕ) : ℝ) := by rw [hcl']
    _ = ∑ i, (ρ * x i - c * x i) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- **Exercise 12.B.5(b), an instance** (MWG, p. 429): two consumers, each valuing one unit at
`3` and further units at nothing; the menu `{(0, 0), (1, 3), (2, 5)}` offers a quantity
discount. With resale price `ρ = 5/2` the first consumer buys the bundle of two for `5` and
resells one unit to the second: this is a resale equilibrium, and its profit `5 − 2c` equals the
profit of the single per-unit price `5/2`. -/
theorem exercise_12_B_5b_instance (c : ℝ) :
    IsResaleEquilibrium (fun _ k => if k = 0 then 0 else 3)
      ({(0, 0), (1, 3), (2, 5)} : Set (ℕ × ℝ)) (5 / 2)
      ![((2 : ℕ), (5 : ℝ)), ((0 : ℕ), (0 : ℝ))] ![1, 1] ∧
    ∑ i, ((![((2 : ℕ), (5 : ℝ)), ((0 : ℕ), (0 : ℝ))] i).2 -
      c * (![((2 : ℕ), (5 : ℝ)), ((0 : ℕ), (0 : ℝ))] i).1) =
      ∑ i : Fin 2, ((5 / 2 : ℝ) * (![1, 1] i : ℕ) - c * (![1, 1] i : ℕ)) := by
  refine ⟨(isResaleEquilibrium_iff _ _ _ _ _).2 ⟨fun i => ?_, fun i k => ?_, by decide⟩, ?_⟩
  · fin_cases i
    · refine ⟨by simp, ?_⟩
      rintro o' (rfl | rfl | rfl) <;> norm_num
    · refine ⟨by simp, ?_⟩
      rintro o' (rfl | rfl | rfl) <;> norm_num
  · fin_cases i <;>
    · rcases k with _ | _ | k
      · norm_num
      · norm_num
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        push_cast
        norm_num
        linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  · simp [Fin.sum_univ_two]
    ring

/-- **Exercise 12.B.5(b), the resale market is needed** (MWG, p. 429). Without resale a
nonlinear schedule can beat every single price: one consumer with `u(0) = 0`, `u(1) = 3`,
`u(k) = 4` for `k ≥ 2`, zero cost. The bundle offer `(2, 4)` (with `(0, 0)`) is accepted and
yields profit `4`, while at every per-unit price `p` every utility-maximizing quantity `x`
yields profit `px ≤ 3`. -/
theorem exercise_12_B_5b_needs_resale :
    (∀ o' ∈ ({(0, 0), (2, 4)} : Set (ℕ × ℝ)),
      (fun k : ℕ => if k = 0 then (0 : ℝ) else if k = 1 then 3 else 4) o'.1 - o'.2 ≤
        (if (2 : ℕ) = 0 then (0 : ℝ) else if (2 : ℕ) = 1 then 3 else 4) - 4) ∧
    ∀ p : ℝ, ∀ x : ℕ, (∀ k : ℕ, (if k = 0 then (0 : ℝ) else if k = 1 then 3 else 4) - p * k ≤
      (if x = 0 then (0 : ℝ) else if x = 1 then 3 else 4) - p * x) → p * x ≤ 3 := by
  refine ⟨?_, fun p x hx => ?_⟩
  · rintro o' (rfl | rfl) <;> norm_num
  · have h0 := hx 0
    have h1 := hx 1
    rcases x with _ | _ | x
    · simp
    · norm_num at h0 ⊢; linarith
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.cast_zero,
        mul_zero, sub_zero, Nat.cast_one, mul_one] at h0 h1
      have hx2 : x + 1 + 1 ≠ 1 := by omega
      simp only [hx2, ↓reduceIte] at h0 h1
      push_cast at h0 h1 ⊢
      have hxn : (0 : ℝ) ≤ x := x.cast_nonneg
      nlinarith

end MWG.MarketPower
