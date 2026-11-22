/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.MyersonSatterthwaite
import MWGMechanismDesign.OptimalAuction
import MWGMechanismDesign.OptimalContract
import MWGMechanismDesign.TradeExercises

/-!
# MWG's own proof of the Myerson-Satterthwaite theorem

MWG, Section 23.E, pp. 895-896 (proof of Proposition 23.E.1), and Exercise 23.E.6(b) (p. 922).

Agent `0` is the seller (MWG's agent 1) and agent `1` the buyer (MWG's agent 2); types are
independent with densities `φᵢ > 0` on `[θ̲ᵢ, θ̄ᵢ]` (`TypeDensity`), `Jᵢ(θ) = θ - (1 - Φᵢ)/φᵢ`
(`TypeDensity.virtualValue`) and `Kᵢ(θ) = θ + Φᵢ/φᵢ` (`TypeDensity.virtualCost`).

* **Step 1**, every display: (23.E.5) `eq_23_E_5`; `U₁(θ̲₁) = U₁(θ̄₁) - ∫∫ y₁φ₂`
  (`eq_23_E_5_seller_U`, with `ȳ₁(θ₁) = ∫ y₁(θ₁, ·)φ₂` in `mss_interimBenefit_seller`); (23.E.6)
  `eq_23_E_6` (from the general `mss_payment_from_top`); `∫∫ (θ₁ + Φ₁/φ₁)φ₁φ₂ = ∫ (θ₁φ₁ + Φ₁)
  = [θ₁Φ₁] = θ̄₁` (`mss_integral_virtualCost`, `mss_expect_virtualCost`); (23.E.7) `eq_23_E_7`;
  `E[-t₁] + E[-t₂] = 0` and `[U₁(θ̄₁) - θ̄₁] + U₂(θ̲₂) = ∫∫ y₂[J₂ - K₁]φ₁φ₂` (`eq_23_E_sum`);
  (23.E.4) `eq_23_E_4`, with a non-vacuity instance (`eq_23_E_4_instance`, posted price `1/2`).
* **Step 2**, every display: the left side of (23.E.4) as MWG's iterated integral with inner
  limit `Min{θ₂, θ̄₁}` (`mss_step2_display1`, via `mss_step2_inner`); the bracket evaluation
  (`mss_step2_display23`); the split at `θ̄₁` (`mss_step2_display4`); the vanishing of
  `[(θ₂ - θ̄₁)(Φ₂ - 1)]_{θ̄₁}^{θ̄₂}` (`mss_step2_display5`); `-∫_{θ̲₂}^{θ̄₁}[1 - Φ₂]Φ₁ < 0`
  (`mss_step2_neg`); together `mss_step2`.
* **Proposition 23.E.1** by MWG's route (`proposition_23_E_1_mwg`), with the hypotheses of
  `proposition_23_E_1`.
* **Exercise 23.E.6(b)**, uniqueness: among linear strategies `aθ + d` with `a > 0` the only
  symmetric Bayesian Nash equilibrium is `2θ/3` (`exercise_23_E_6b_unique`).

**Checks against the printed proof.** Every display of pp. 895-896 is correct as printed,
reading `φᵢ = 0` outside `[θ̲ᵢ, θ̄ᵢ]` and `Φᵢ = 0` below, `= 1` above (our `TypeDensity`
convention): this is needed when `θ₂ < θ̲₁` (the inner interval `[θ̲₁, Min{θ₂, θ̄₁}]` is reversed;
the inner integral is `0`) and when `θ̄₁ > θ̄₂` (the second integral of the fourth display runs
over a reversed interval, where its integrand vanishes). **Departures.** MWG evaluate
`∫(θφ + Φ) = [θΦ]` and `∫[(θ₂ - θ̄₁)φ₂ + Φ₂ - 1] = [(θ₂ - θ̄₁)(Φ₂ - 1)]` by the
fundamental theorem of calculus, which needs `Φ' = φ`, i.e. `φ` continuous; we prove both
identities for measurable densities by Fubini (`mss_integral_cdf`, `mss_integral_key`). In
Step 1 the expectations `E[y₂J₂]`, `E[y₂K₁]` are assumed to exist (they do for bounded
measurable `y`: `mss_integrable_y_mul`); `y₁ + y₂ = 1` and `t₁ + t₂ = 0` are needed on `Θ` only. In
Exercise 23.E.6(b) uniqueness is proved among strictly increasing linear strategies; for
constant strategies ties have positive probability and the tie rule of the mechanism matters.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-! ### The distribution function outside and inside `[θ̲, θ̄]` -/

/-- MWG's seller term `θ + Φ(θ)/φ(θ)` of (23.E.4) (MWG, p. 895), a "virtual cost". -/
noncomputable def TypeDensity.virtualCost (D : TypeDensity) (x : ℝ) : ℝ :=
  x + D.cdf x / D.dens x

/-- The density vanishes on the open interval `(a, θ̲)` below the support. -/
theorem mss_integral_below (D : TypeDensity) {a : ℝ} (ha : a ≤ D.lo) (g : ℝ → ℝ)
    (hg : ∀ x, x < D.lo → g x = 0) : ∫ x in a..D.lo, g x = 0 := by
  rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ)) fun x hx => hg x hx.2]
  simp

/-- The density vanishes on the open interval `(θ̄, a)` above the support. -/
theorem mss_integral_above (D : TypeDensity) {a : ℝ} (ha : D.hi ≤ a) (g : ℝ → ℝ)
    (hg : ∀ x, D.hi < x → g x = 0) : ∫ x in D.hi..a, g x = 0 := by
  rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ)) fun x hx => hg x hx.1]
  simp

/-- `Φ(x) = 0` for `x ≤ θ̲`. -/
theorem mss_cdf_of_le (D : TypeDensity) {x : ℝ} (hx : x ≤ D.lo) : D.cdf x = 0 := by
  rw [TypeDensity.cdf, intervalIntegral.integral_symm,
    mss_integral_below D hx _ fun s hs => D.dens_eq_zero s fun h => absurd h.1 (not_le.2 hs),
    neg_zero]

/-- `Φ(x) = 1` for `x ≥ θ̄`. -/
theorem mss_cdf_of_ge (D : TypeDensity) {x : ℝ} (hx : D.hi ≤ x) : D.cdf x = 1 := by
  rw [TypeDensity.cdf, ← intervalIntegral.integral_add_adjacent_intervals
    D.integrable_dens.intervalIntegrable D.integrable_dens.intervalIntegrable, D.integral_dens,
    mss_integral_above D hx _ fun s hs => D.dens_eq_zero s fun h => absurd h.2 (not_le.2 hs),
    add_zero]

/-- `Φ(θ̲) = 0`. -/
theorem mss_cdf_lo (D : TypeDensity) : D.cdf D.lo = 0 := mss_cdf_of_le D le_rfl

/-- `Φ(θ̄) = 1`. -/
theorem mss_cdf_hi (D : TypeDensity) : D.cdf D.hi = 1 := mss_cdf_of_ge D le_rfl

/-- `Φ(x) > 0` for `x > θ̲`. -/
theorem mss_cdf_pos (D : TypeDensity) {x : ℝ} (hx : D.lo < x) : 0 < D.cdf x := by
  rcases le_or_gt x D.hi with h | h
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on D.integrable_dens.intervalIntegrable
      (fun s hs => D.dens_pos s ⟨hs.1.le, hs.2.le.trans h⟩) hx
  · rw [mss_cdf_of_ge D h.le]; exact one_pos

/-- `1 - Φ(x) > 0` for `x < θ̄`. -/
theorem mss_one_sub_cdf_pos (D : TypeDensity) {x : ℝ} (hx : x < D.hi) : 0 < 1 - D.cdf x := by
  rcases le_or_gt D.lo x with h | h
  · exact oc_one_sub_cdf_pos D ⟨h, hx.le⟩ hx
  · rw [mss_cdf_of_le D h.le]; exact by norm_num

/-- `0 ≤ Φ(x) ≤ 1` for every `x`. -/
theorem mss_cdf_mem (D : TypeDensity) (x : ℝ) : 0 ≤ D.cdf x ∧ D.cdf x ≤ 1 := by
  rcases le_or_gt x D.lo with h | h
  · rw [mss_cdf_of_le D h]; norm_num
  rcases le_or_gt D.hi x with h' | h'
  · rw [mss_cdf_of_ge D h']; norm_num
  exact ⟨(mss_cdf_pos D h).le, by linarith [mss_one_sub_cdf_pos D h']⟩

/-- `x ↦ g(x)φ(x)` is integrable on every interval when `g` is continuous. -/
theorem mss_ii_mul_dens (D : TypeDensity) {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * D.dens x) volume a b :=
  D.integrable_dens.intervalIntegrable.continuousOn_mul hg.continuousOn

/-- `Φ` is integrable on every interval. -/
theorem mss_ii_cdf (D : TypeDensity) (a b : ℝ) : IntervalIntegrable D.cdf volume a b :=
  D.continuous_cdf.intervalIntegrable a b

/-- The Fubini identity behind MWG's integrations by parts on pp. 895-896: for `θ̲ < a`,
`∫_{θ̲}^{a} Φ(x) dx = ∫_{θ̲}^{a} (a - s)φ(s) ds`. -/
theorem mss_integral_cdf (D : TypeDensity) {a : ℝ} (ha : D.lo < a) :
    ∫ x in D.lo..a, D.cdf x = ∫ s in D.lo..a, (a - s) * D.dens s := by
  set U := uniformDensity D.lo a ha with hU
  have := U.isProbabilityMeasure
  have hw : IntervalIntegrable D.dens volume D.lo a := D.integrable_dens.intervalIntegrable
  have h := td_integral_integral_eq U.measure ha.le U.measure_compl_Icc hw
  have hUlo : U.lo = D.lo := rfl
  have hUhi : U.hi = a := rfl
  have hne : a - D.lo ≠ 0 := (sub_pos.2 ha).ne'
  rw [U.integral_eq, hUlo, hUhi] at h
  have hL : ∫ x in D.lo..a, (∫ s in D.lo..x, D.dens s) * U.dens x =
      (a - D.lo)⁻¹ * ∫ x in D.lo..a, D.cdf x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ha.le] at hx
    change (∫ s in D.lo..x, D.dens s) * (Set.Icc D.lo a).indicator (fun _ => (a - D.lo)⁻¹) x = _
    rw [Set.indicator_of_mem hx, TypeDensity.cdf]
    ring
  have hR : ∫ s in D.lo..a, D.dens s * U.measure.real (Set.Ici s) =
      (a - D.lo)⁻¹ * ∫ s in D.lo..a, (a - s) * D.dens s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ha.le] at hx
    rw [U.measureReal_Ici hx, hU, oa_uniform_cdf ha hx]
    field_simp
    ring
  rw [hL, hR] at h
  have := mul_left_cancel₀ (inv_ne_zero hne) h
  exact this

/-- The key computation in Step 2 of MWG's proof (p. 896), for every upper limit `a` and
constant `c`: `∫_{θ̲}^{a} ((c - x)φ(x) - Φ(x)) dx = (c - a)Φ(a)`, i.e.
`[(c - x)Φ(x)]_{θ̲}^{a}` (MWG's integration by parts, valid also for `a` outside `[θ̲, θ̄]`
with `φ = 0` there). -/
theorem mss_integral_key (D : TypeDensity) (a c : ℝ) :
    ∫ x in D.lo..a, ((c - x) * D.dens x - D.cdf x) = (c - a) * D.cdf a := by
  rcases le_or_gt a D.lo with ha | ha
  · rw [mss_cdf_of_le D ha, mul_zero, intervalIntegral.integral_symm,
      mss_integral_below D ha _ fun x hx => by
        rw [D.dens_eq_zero x fun h => absurd h.1 (not_le.2 hx), mss_cdf_of_le D hx.le]; ring,
      neg_zero]
  have h1 : IntervalIntegrable (fun x => (c - x) * D.dens x) volume D.lo a :=
    mss_ii_mul_dens D (continuous_const.sub continuous_id) _ _
  have h2 : IntervalIntegrable (fun x => (a - x) * D.dens x) volume D.lo a :=
    mss_ii_mul_dens D (continuous_const.sub continuous_id) _ _
  rw [intervalIntegral.integral_sub h1 (mss_ii_cdf D _ _), mss_integral_cdf D ha,
    ← intervalIntegral.integral_sub h1 h2]
  have e : ∀ x, (c - x) * D.dens x - (a - x) * D.dens x = (c - a) * D.dens x := fun x => by ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, TypeDensity.cdf]

/-! ### `θ - (1 - Φ)/φ` and `θ + Φ/φ` -/

/-- On `[θ̲, θ̄]`, `J(x)φ(x) = xφ(x) - (1 - Φ(x))` for `J(x) = x - (1 - Φ(x))/φ(x)`. -/
theorem mss_virtualValue_mul (D : TypeDensity) {x : ℝ} (hx : x ∈ Set.Icc D.lo D.hi) :
    D.virtualValue x * D.dens x = x * D.dens x - (1 - D.cdf x) := by
  have := (D.dens_pos x hx).ne'
  simp only [TypeDensity.virtualValue]
  field_simp

/-- On `[θ̲, θ̄]`, `K(x)φ(x) = xφ(x) + Φ(x)` for `K(x) = x + Φ(x)/φ(x)`. -/
theorem mss_virtualCost_mul (D : TypeDensity) {x : ℝ} (hx : x ∈ Set.Icc D.lo D.hi) :
    D.virtualCost x * D.dens x = x * D.dens x + D.cdf x := by
  have := (D.dens_pos x hx).ne'
  simp only [TypeDensity.virtualCost]
  field_simp

/-- `J` is measurable. -/
theorem mss_measurable_virtualValue (D : TypeDensity) : Measurable D.virtualValue :=
  measurable_id.sub (((continuous_const.sub D.continuous_cdf).measurable).div D.measurable_dens)

/-- `K` is measurable. -/
theorem mss_measurable_virtualCost (D : TypeDensity) : Measurable D.virtualCost :=
  measurable_id.add (D.continuous_cdf.measurable.div D.measurable_dens)

/-- A function `g` with `g φ = h` on `[θ̲, θ̄]` and `h` integrable on `[θ̲, θ̄]` is integrable
for the type distribution (even if `g` itself is unbounded, as `Φ/φ` may be). -/
theorem mss_integrable_of_mul_dens (D : TypeDensity) {g h : ℝ → ℝ}
    (hh : IntervalIntegrable h volume D.lo D.hi)
    (e : ∀ x ∈ Set.Icc D.lo D.hi, g x * D.dens x = h x) : Integrable g D.measure := by
  rw [TypeDensity.measure, integrable_withDensity_iff_integrable_smul
    D.measurable_dens.real_toNNReal]
  have heq : (fun x => (D.dens x).toNNReal • g x) = (Set.Icc D.lo D.hi).indicator h := by
    funext x
    by_cases hx : x ∈ Set.Icc D.lo D.hi
    · rw [Set.indicator_of_mem hx, NNReal.smul_def, Real.coe_toNNReal _ (D.dens_nonneg x),
        smul_eq_mul, mul_comm, e x hx]
    · rw [Set.indicator_of_notMem hx, D.dens_eq_zero x hx]; simp
  rw [heq, integrable_indicator_iff measurableSet_Icc, integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le).1 hh

/-- `J(θ)` has an expectation. -/
theorem mss_integrable_virtualValue (D : TypeDensity) : Integrable D.virtualValue D.measure :=
  mss_integrable_of_mul_dens D
    ((mss_ii_mul_dens D continuous_id _ _).sub
      ((continuous_const.sub D.continuous_cdf).intervalIntegrable _ _))
    fun _ hx => mss_virtualValue_mul D hx

/-- `K(θ)` has an expectation. -/
theorem mss_integrable_virtualCost (D : TypeDensity) : Integrable D.virtualCost D.measure :=
  mss_integrable_of_mul_dens D
    ((mss_ii_mul_dens D continuous_id _ _).add (mss_ii_cdf D _ _))
    fun _ hx => mss_virtualCost_mul D hx

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 896), the display after (23.E.6):
`∫∫ (θ₁ + Φ₁(θ₁)/φ₁(θ₁)) φ₁(θ₁)φ₂(θ₂) dθ₂ dθ₁ = ∫ (θ₁φ₁(θ₁) + Φ₁(θ₁)) dθ₁ = [θ₁Φ₁(θ₁)] = θ̄₁`.
Here for one type distribution: `E[K(θ)] = ∫_{θ̲}^{θ̄} (xφ + Φ) = θ̄Φ(θ̄) - θ̲Φ(θ̲) = θ̄` (proved by
the Fubini identity, not by differentiating `xΦ(x)`, which needs `φ` continuous). -/
theorem mss_integral_virtualCost (D : TypeDensity) :
    ∫ x, D.virtualCost x ∂D.measure = ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) ∧
      ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) = D.hi * D.cdf D.hi - D.lo * D.cdf D.lo ∧
      D.hi * D.cdf D.hi - D.lo * D.cdf D.lo = D.hi := by
  have h1 : ∫ x, D.virtualCost x ∂D.measure = ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) := by
    rw [D.integral_eq]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le D.lo_lt_hi.le] at hx
    exact mss_virtualCost_mul D hx
  have h2 : ∫ x in D.lo..D.hi, (x * D.dens x + D.cdf x) = D.hi := by
    have := mss_integral_key D D.hi 0
    rw [mss_cdf_hi] at this
    have e : ∀ x, (0 - x) * D.dens x - D.cdf x = -(x * D.dens x + D.cdf x) := fun x => by ring
    simp only [e, intervalIntegral.integral_neg] at this
    linarith
  refine ⟨h1, ?_, ?_⟩ <;> rw [mss_cdf_hi, mss_cdf_lo] <;> [rw [h2]; skip] <;> ring

/-! ### Bayesian incentive compatible social choice functions with densities -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (23.D.15) for any measurable weight `G` (MWG, p. 891, used on p. 895 with
`G = θ + Φ/φ`): `E[yᵢ(θ)G(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(x)G(x)φᵢ(x) dx`. -/
theorem mss_expect_mul (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) {G : ℝ → ℝ} (hG : Measurable G)
    (hyG : Integrable (fun θ => y θ i * G (θ i)) (Measure.pi fun j => (D j).measure)) :
    ∫ θ, y θ i * G (θ i) ∂Measure.pi (fun j => (D j).measure) =
      ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        G x * (D i).dens x := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc (D i).lo (D i).hi) := ((proposition_23_D_2 hint).1 hf i).1
  rw [← integral_integral_update (Θ := fun _ => ℝ) (fun j => (D j).measure) i hyG]
  simp only [update_self]
  simp_rw [integral_mul_const]
  have h := integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i
    (F := fun x => interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x * G x)
    (((D i).aestronglyMeasurable_of_monotoneOn hmono).mul hG.aestronglyMeasurable)
  rw [(D i).integral_eq] at h
  exact h

/-- With independent types with densities, `E[-tᵢ(θ)] = E[-t̄ᵢ(θᵢ)]` for a Bayesian incentive
compatible social choice function (MWG, p. 896). -/
theorem mss_expected_transfer (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι)
    (ht : Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure)) :
    ∫ θ, -t θ i ∂Measure.pi (fun j => (D j).measure) =
      ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t i x ∂(D i).measure := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [integral_neg, integral_neg, re_expected_transfer (fun j => (D j).measure) i ht]
  congr 1
  set E := D i with hE
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc E.lo E.hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
  have hprim : ContinuousOn (fun x => ∫ s in E.lo..x,
      interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) (Set.Icc E.lo E.hi) := by
    rw [← Set.uIcc_of_le hle]
    refine intervalIntegral.continuousOn_primitive_interval ?_
    rw [Set.uIcc_of_le hle]
    exact hmono.integrableOn_isCompact isCompact_Icc
  have hG : AEStronglyMeasurable (fun x =>
      interimU (Measure.pi fun j => (D j).measure) allocV y t i E.lo +
        (∫ s in E.lo..x, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) -
        x * interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x) E.measure :=
    (aestronglyMeasurable_const.add ((hprim.aestronglyMeasurable measurableSet_Icc).mono_ac
      E.absolutelyContinuous)).sub
      (continuous_id.aestronglyMeasurable.mul (E.aestronglyMeasurable_of_monotoneOn hmono))
  refine integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i (hG.congr ?_)
  filter_upwards [mem_ae_iff.2 E.measure_compl_Icc] with x hx
  exact (re_interimTransfer_eq hint hf i hx).symm

/-- For a Bayesian incentive compatible `f`, the functions `ȳᵢ`, `xȳᵢ(x)φᵢ(x)` and `ȳᵢΦᵢ` are
integrable on `[θ̲ᵢ, θ̄ᵢ]` (`ȳᵢ` is monotone there, hence bounded). -/
theorem mss_ybar_ii (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) :
    IntervalIntegrable (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i) volume
        (D i).lo (D i).hi ∧
      IntervalIntegrable (fun x => x * interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).dens x) volume (D i).lo (D i).hi ∧
      IntervalIntegrable (fun x => interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).cdf x) volume (D i).lo (D i).hi := by
  set yb := interimBenefit (Measure.pi fun j => (D j).measure) allocV y i with hyb
  set E := D i with hE
  have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
  have hmono : MonotoneOn yb (Set.Icc E.lo E.hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hybI : IntervalIntegrable yb volume E.lo E.hi := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]; exact hmono
  set Cy := |yb E.lo| + |yb E.hi| with hCy
  have hyb_bd : ∀ x ∈ Set.Icc E.lo E.hi, |yb x| ≤ Cy := by
    intro x hx
    have h1 := hmono ⟨le_rfl, hle⟩ hx hx.1
    have h2 := hmono hx ⟨hle, le_rfl⟩ hx.2
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (yb E.lo), le_abs_self (yb E.hi), abs_nonneg (yb E.lo),
      abs_nonneg (yb E.hi)]
  have hybm : AEStronglyMeasurable yb (volume.restrict (Set.Ioc E.lo E.hi)) := hybI.1.1
  refine ⟨hybI, ?_, hybI.mul_continuousOn E.continuous_cdf.continuousOn⟩
  exact re_intervalIntegrable_mul_dens E (continuous_id.aestronglyMeasurable.mul hybm)
    ((|E.lo| + |E.hi|) * Cy) fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (re_abs_le_of_mem ⟨hx.1.le, hx.2⟩) (hyb_bd x ⟨hx.1.le, hx.2⟩)
        (abs_nonneg _) (by positivity)

/-- **(23.E.6)**, general form (MWG, p. 895): for a Bayesian incentive compatible `f` with
independent types with densities, agent `i`'s expected payment, computed from the TOP type
(`Uᵢ(θᵢ) = Uᵢ(θ̄ᵢ) - ∫_{θᵢ}^{θ̄ᵢ} ȳᵢ`), is
`E[-t̄ᵢ(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(θ)(θ + Φᵢ(θ)/φᵢ(θ))φᵢ(θ) dθ - Uᵢ(θ̄ᵢ)`. -/
theorem mss_payment_from_top (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t i x ∂(D i).measure =
      (∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        (D i).virtualCost x * (D i).dens x) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).hi := by
  obtain ⟨h0, h1, h2⟩ := mss_ybar_ii D hint hf i
  have hle : (D i).lo ≤ (D i).hi := (D i).lo_lt_hi.le
  have hU := ((proposition_23_D_2 hint).1 hf i).2 (D i).hi ⟨hle, le_rfl⟩
  rw [eq_23_D_14 D hint hf i]
  have hJ : ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure)
      allocV y i x * (D i).virtualValue x * (D i).dens x =
      ∫ x in (D i).lo..(D i).hi, ((x * interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).dens x + interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).cdf x) - interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    rw [mul_assoc, mss_virtualValue_mul (D i) hx]
    ring
  have hK : ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure)
      allocV y i x * (D i).virtualCost x * (D i).dens x =
      ∫ x in (D i).lo..(D i).hi, (x * interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).dens x + interimBenefit (Measure.pi fun j => (D j).measure)
        allocV y i x * (D i).cdf x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    rw [mul_assoc, mss_virtualCost_mul (D i) hx]
    ring
  rw [hJ, hK, intervalIntegral.integral_sub (h1.add h2) h0, hU]
  ring

/-! ### Step 1 of MWG's proof: (23.E.4)-(23.E.7)

Agent `0` is the seller (MWG's agent 1) and agent `1` the buyer (MWG's agent 2). -/

/-- `x ↦ (s, x)` is measurable. -/
theorem mss_measurable_vec1 (s : ℝ) : Measurable fun x : ℝ => (![s, x] : Fin 2 → ℝ) := by
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · exact measurable_const
  · exact measurable_id

/-- `x ↦ (x, b)` is measurable. -/
theorem mss_measurable_vec0 (b : ℝ) : Measurable fun x : ℝ => (![x, b] : Fin 2 → ℝ) := by
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · exact measurable_id
  · exact measurable_const

/-- `update θ 0 s = (s, θ₁)`. -/
theorem mss_update0 (θ : Fin 2 → ℝ) (s : ℝ) : update θ 0 s = ![s, θ 1] := by
  funext j; fin_cases j <;> simp

/-- `update θ 1 b = (θ₀, b)`. -/
theorem mss_update1 (θ : Fin 2 → ℝ) (b : ℝ) : update θ 1 b = ![θ 0, b] := by
  funext j; fin_cases j <;> simp

/-- The seller's expected trading probability as MWG's inner integral (p. 895):
`ȳ₁(θ₁) = ∫_{θ̲₂}^{θ̄₂} y₁(θ₁, θ₂)φ₂(θ₂) dθ₂` (here `ȳ₀(s) = ∫ y₀(s, x)φ₁(x) dx`). -/
theorem mss_interimBenefit_seller (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y) (s : ℝ) :
    interimBenefit (Measure.pi fun j => (D j).measure) allocV y 0 s =
      ∫ x in (D 1).lo..(D 1).hi, y ![s, x] 0 * (D 1).dens x := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [interimBenefit, ← (D 1).integral_eq]
  simp only [allocV, mss_update0]
  exact integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 1
    (F := fun x => y ![s, x] 0)
    (((measurable_pi_apply 0).comp (hym.comp (mss_measurable_vec1 s))).aestronglyMeasurable)

/-- **(23.E.5)** (MWG, p. 895): for a Bayesian incentive compatible `f`, the buyer's expected
payment is `E[-t̄₂(θ₂)] = ∫∫ y₂(θ₁, θ₂)(θ₂ - (1 - Φ₂(θ₂))/φ₂(θ₂))φ₁φ₂ - U₂(θ̲₂)` (the double
integral is the expectation under the product of the densities; it is assumed to exist). -/
theorem eq_23_E_5 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hyJ : Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure)) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t 1 x ∂(D 1).measure =
      ∫ θ, y θ 1 * (D 1).virtualValue (θ 1) ∂Measure.pi (fun j => (D j).measure) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t 1 (D 1).lo := by
  rw [eq_23_D_14 D hint hf 1, eq_23_D_15 D hint hf 1 hyJ]

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 895), "because (23.D.12) implies that
`U₁(θ̲₁) = U₁(θ̄₁) - ∫∫ y₁(θ₁, θ₂)φ₂(θ₂) dθ₂ dθ₁`": for a Bayesian incentive compatible `f` with
`y` measurable, `U₀(θ̲₀) = U₀(θ̄₀) - ∫_{θ̲₀}^{θ̄₀} ∫_{θ̲₁}^{θ̄₁} y₀(s, x)φ₁(x) dx ds`. -/
theorem eq_23_E_5_seller_U (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) :
    interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).lo =
      interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi -
        ∫ s in (D 0).lo..(D 0).hi, ∫ x in (D 1).lo..(D 1).hi, y ![s, x] 0 * (D 1).dens x := by
  have hU := ((proposition_23_D_2 hint).1 hf 0).2 (D 0).hi ⟨(D 0).lo_lt_hi.le, le_rfl⟩
  simp only [mss_interimBenefit_seller D hym] at hU
  linarith

/-- **(23.E.6)** (MWG, p. 895): for a Bayesian incentive compatible `f`, the seller's expected
payment is `E[-t̄₁(θ₁)] = ∫∫ y₁(θ₁, θ₂)(θ₁ + Φ₁(θ₁)/φ₁(θ₁))φ₁φ₂ - U₁(θ̄₁)` (expectation assumed
to exist). -/
theorem eq_23_E_6 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hyK : Integrable (fun θ => y θ 0 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t 0 x ∂(D 0).measure =
      ∫ θ, y θ 0 * (D 0).virtualCost (θ 0) ∂Measure.pi (fun j => (D j).measure) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi := by
  rw [mss_payment_from_top D hint hf 0,
    mss_expect_mul D hint hf 0 (mss_measurable_virtualCost (D 0)) hyK]

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 896): `∫∫ (θ₁ + Φ₁/φ₁)φ₁φ₂ = θ̄₁`, as an
expectation under the product of the two densities. -/
theorem mss_expect_virtualCost (D : Fin 2 → TypeDensity) :
    ∫ θ, (D 0).virtualCost (θ 0) ∂Measure.pi (fun j => (D j).measure) = (D 0).hi := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 0
    (mss_measurable_virtualCost (D 0)).aestronglyMeasurable]
  obtain ⟨h1, h2, h3⟩ := mss_integral_virtualCost (D 0)
  rw [h1, h2, h3]

/-- **(23.E.7)** (MWG, p. 896): if moreover `y₁ + y₂ = 1` on `Θ`, the seller's expected payment
is `E[-t̄₁(θ₁)] = θ̄₁ - ∫∫ y₂(θ₁, θ₂)(θ₁ + Φ₁(θ₁)/φ₁(θ₁))φ₁φ₂ - U₁(θ̄₁)`. -/
theorem eq_23_E_7 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hsum : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → y θ 0 + y θ 1 = 1)
    (hyK : Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t 0 x ∂(D 0).measure =
      (D 0).hi - ∫ θ, y θ 1 * (D 0).virtualCost (θ 0) ∂Measure.pi (fun j => (D j).measure) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hK : Integrable (fun θ => (D 0).virtualCost (θ 0)) (Measure.pi fun j => (D j).measure) :=
    integrable_comp_eval (mss_integrable_virtualCost (D 0))
  have hae : (fun θ => (D 0).virtualCost (θ 0) - y θ 1 * (D 0).virtualCost (θ 0)) =ᵐ[
      Measure.pi fun j => (D j).measure] fun θ => y θ 0 * (D 0).virtualCost (θ 0) := by
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    rw [show y θ 0 = 1 - y θ 1 by linarith [hsum θ hθ]]
    ring
  rw [eq_23_E_6 D hint hf ((hK.sub hyK).congr hae), ← integral_congr_ae hae,
    integral_sub hK hyK, mss_expect_virtualCost D]

/-- **Proof of Proposition 23.E.1, Step 1** (MWG, p. 896): budget balance `t₁ + t₂ = 0` gives
`E[-t₁] + E[-t₂] = 0`, and adding (23.E.5) and (23.E.7),
`[U₁(θ̄₁) - θ̄₁] + U₂(θ̲₂) = ∫∫ y₂[(θ₂ - (1 - Φ₂)/φ₂) - (θ₁ + Φ₁/φ₁)]φ₁φ₂`. -/
theorem eq_23_E_sum (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (hsum : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → y θ 0 + y θ 1 = 1)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hyJ : Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure))
    (hyK : Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    ∫ θ, -t θ 0 ∂Measure.pi (fun j => (D j).measure) +
        ∫ θ, -t θ 1 ∂Measure.pi (fun j => (D j).measure) = 0 ∧
      interimU (Measure.pi fun j => (D j).measure) allocV y t 0 (D 0).hi - (D 0).hi +
        interimU (Measure.pi fun j => (D j).measure) allocV y t 1 (D 1).lo =
      ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hbbE : ∫ θ, -t θ 0 ∂Measure.pi (fun j => (D j).measure) +
      ∫ θ, -t θ 1 ∂Measure.pi (fun j => (D j).measure) = 0 := by
    rw [← integral_add (f := fun θ => -t θ 0) (g := fun θ => -t θ 1) (ht 0).neg (ht 1).neg,
      integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    linarith [hbb θ hθ]
  refine ⟨hbbE, ?_⟩
  rw [mss_expected_transfer D hint hf 0 (ht 0), mss_expected_transfer D hint hf 1 (ht 1),
    eq_23_E_7 D hint hf hsum hyK, eq_23_E_5 D hint hf hyJ] at hbbE
  simp_rw [mul_sub]
  rw [integral_sub hyJ hyK]
  linarith

/-- **(23.E.4)**, Step 1 of MWG's proof of Proposition 23.E.1 (MWG, p. 895). In any Bayesian
incentive compatible and interim individually rational social choice function with
`y₁ + y₂ = 1` and `t₁ + t₂ = 0` (on `Θ`), independent types with densities `φᵢ > 0`,
`∫∫ y₂(θ₁, θ₂)[(θ₂ - (1 - Φ₂(θ₂))/φ₂(θ₂)) - (θ₁ + Φ₁(θ₁)/φ₁(θ₁))]φ₁φ₂ ≥ 0`
(the two expectations involved are assumed to exist; `mss_integrable_y_mul` proves this for
bounded measurable `y`). Agent `0` is the seller, agent `1` the buyer. -/
theorem eq_23_E_4 (D : Fin 2 → TypeDensity) {y t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (hsum : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → y θ 0 + y θ 1 = 1)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) y t (fun i => (D i).lo)
      fun i => (D i).hi)
    (hyJ : Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure))
    (hyK : Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure)) :
    0 ≤ ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
      ∂Measure.pi (fun j => (D j).measure) := by
  rw [← (eq_23_E_sum D hint hf ht hsum hbb hyJ hyK).2]
  have h0 := hir.1 (D 0).hi ⟨(D 0).lo_lt_hi.le, le_rfl⟩
  have h1 := hir.2 (D 1).lo ⟨le_rfl, (D 1).lo_lt_hi.le⟩
  linarith

/-- For `y` measurable with `|y₂| ≤ 1` on `Θ`, the expectations `E[y₂J₂(θ₂)]`, `E[y₂K₁(θ₁)]` and
`E[y₂(J₂(θ₂) - K₁(θ₁))]` of (23.E.4)-(23.E.7) exist (`J₂ = θ - (1 - Φ₂)/φ₂`,
`K₁ = θ + Φ₁/φ₁`). -/
theorem mss_integrable_y_mul (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable fun θ => y θ 1)
    (hb : ∀ θ, InTypes (fun i => (D i).lo) (fun i => (D i).hi) θ → |y θ 1| ≤ 1) :
    Integrable (fun θ => y θ 1 * (D 1).virtualValue (θ 1)) (Measure.pi fun j => (D j).measure) ∧
      Integrable (fun θ => y θ 1 * (D 0).virtualCost (θ 0))
        (Measure.pi fun j => (D j).measure) ∧
      Integrable (fun θ => y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0)))
        (Measure.pi fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hbd : ∀ᵐ θ ∂Measure.pi (fun j => (D j).measure), ‖y θ 1‖ ≤ 1 := by
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    rw [Real.norm_eq_abs]; exact hb θ hθ
  have hJ : Integrable (fun θ : Fin 2 → ℝ => (D 1).virtualValue (θ 1))
      (Measure.pi fun j => (D j).measure) :=
    integrable_comp_eval (mss_integrable_virtualValue (D 1))
  have hK : Integrable (fun θ : Fin 2 → ℝ => (D 0).virtualCost (θ 0))
      (Measure.pi fun j => (D j).measure) :=
    integrable_comp_eval (mss_integrable_virtualCost (D 0))
  exact ⟨hJ.bdd_mul hym.aestronglyMeasurable hbd, hK.bdd_mul hym.aestronglyMeasurable hbd,
    (hJ.sub hK).bdd_mul hym.aestronglyMeasurable hbd⟩

/-! ### Step 2 of MWG's proof -/

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), the inner integral over the seller's
type. With the efficient trading rule (`y₂ = 1` if `θ₂ > θ₁`, `0` if `θ₂ < θ₁`, ties free) and
a buyer type `b ∈ [θ̲₂, θ̄₂]`,
`E_{θ₁}[y₂(θ₁, b)(J₂(b) - K₁(θ₁))] = (J₂(b) - Min{b, θ̄₁})Φ₁(Min{b, θ̄₁})`. -/
theorem mss_step2_inner (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y) (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y)
    {b : ℝ} (hb : b ∈ Set.Icc (D 1).lo (D 1).hi) :
    ∫ θ', y (update θ' 1 b) 1 * ((D 1).virtualValue (update θ' 1 b 1) -
        (D 0).virtualCost (update θ' 1 b 0)) ∂Measure.pi (fun j => (D j).measure) =
      ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  set E := D 0 with hE
  set c := (D 1).virtualValue b with hc
  simp only [mss_update1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 0
    (F := fun x => y ![x, b] 1 * (c - E.virtualCost x))
    ((((measurable_pi_apply 1).comp (hym.comp (mss_measurable_vec0 b))).mul
      (measurable_const.sub (mss_measurable_virtualCost E))).aestronglyMeasurable),
    E.integral_eq]
  set m' := max E.lo (min b E.hi) with hm'
  have hm'mem : m' ∈ Set.Icc E.lo E.hi :=
    ⟨le_max_left _ _, max_le E.lo_lt_hi.le (min_le_right _ _)⟩
  have hmem : ∀ x ∈ Set.Icc E.lo E.hi,
      InTypes (fun i => (D i).lo) (fun i => (D i).hi) ![x, b] := by
    intro x hx j; fin_cases j
    · exact hx
    · exact hb
  rw [intervalIntegral.integral_congr_ae (g := Set.indicator {x | x ≤ m'}
    fun x => (c - x) * E.dens x - E.cdf x), intervalIntegral.integral_indicator hm'mem,
    mss_integral_key]
  · rcases le_or_gt E.lo b with h | h
    · rw [hm', max_eq_right (le_min h E.lo_lt_hi.le)]
    · rw [hm', max_eq_left ((min_le_left _ _).trans h.le), mss_cdf_of_le E le_rfl,
        mss_cdf_of_le E ((min_le_left _ _).trans h.le)]
      ring
  filter_upwards [Measure.ae_ne volume b] with x hxb hx
  rw [Set.uIoc_of_le E.lo_lt_hi.le] at hx
  have hxI : x ∈ Set.Icc E.lo E.hi := ⟨hx.1.le, hx.2⟩
  obtain ⟨-, -, -, h1, h2⟩ := heff _ (hmem x hxI)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1 h2
  by_cases hxm : x ≤ m'
  · rw [Set.indicator_of_mem (show x ∈ {x | x ≤ m'} from hxm)]
    have hxlt : x < b := by
      rcases lt_or_gt_of_ne hxb with h | h
      · exact h
      · exfalso
        have : m' ≤ max E.lo b := max_le_max le_rfl (min_le_left _ _)
        rcases le_total E.lo b with h' | h'
        · rw [max_eq_right h'] at this; linarith
        · rw [max_eq_left h'] at this; linarith [hx.1]
    rw [h1 hxlt, one_mul, sub_mul, mss_virtualCost_mul E hxI]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ {x | x ≤ m'} from hxm)]
    have hbx : b < x := by
      push Not at hxm
      have : min b E.hi < x := lt_of_le_of_lt (le_max_right _ _) hxm
      rcases le_total b E.hi with h' | h'
      · rw [min_eq_left h'] at this; exact this
      · rw [min_eq_right h'] at this; linarith [hx.2]
    rw [h2 hbx, zero_mul, zero_mul]

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), first display: with the efficient
trading rule the left side of (23.E.4) can be written as
`∫_{θ̲₂}^{θ̄₂} ∫_{θ̲₁}^{Min{θ₂, θ̄₁}} [((θ₂ - (1 - Φ₂)/φ₂) - θ₁)φ₁(θ₁) - Φ₁(θ₁)]φ₂(θ₂) dθ₁ dθ₂`
(when `θ₂ < θ̲₁` the inner interval is reversed and the inner integral is `0`, as `φ₁ = 0`
and `Φ₁ = 0` below `θ̲₁`). -/
theorem mss_step2_display1 (D : Fin 2 → TypeDensity) {y : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hym : Measurable y)
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y) :
    ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) =
      ∫ b in (D 1).lo..(D 1).hi, (∫ x in (D 0).lo..min b (D 0).hi,
        (((D 1).virtualValue b - x) * (D 0).dens x - (D 0).cdf x)) * (D 1).dens b := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hy1 : Measurable fun θ => y θ 1 := (measurable_pi_apply 1).comp hym
  have hF := (mss_integrable_y_mul D hy1 fun θ hθ => by
    obtain ⟨-, h0, h1, -, -⟩ := heff θ hθ
    exact abs_le.2 ⟨by linarith, h1⟩).2.2
  set H : ℝ → ℝ := fun b => ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi)
    with hH
  have hHm : Measurable H :=
    ((mss_measurable_virtualValue (D 1)).sub (measurable_id.min measurable_const)).mul
      ((D 0).continuous_cdf.measurable.comp (measurable_id.min measurable_const))
  rw [← integral_integral_update (Θ := fun _ => ℝ) (fun j => (D j).measure) 1 hF,
    integral_congr_ae (g := fun θ => H (θ 1)) ?_,
    integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) 1 hHm.aestronglyMeasurable,
    (D 1).integral_eq]
  · refine intervalIntegral.integral_congr fun b _ => ?_
    simp only [hH]
    rw [mss_integral_key]
  filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
    with θ hθ
  exact mss_step2_inner D hym heff (hθ 1)

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), second and third displays: the inner
integral is `[((θ₂ - (1 - Φ₂)/φ₂) - θ₁)Φ₁(θ₁)]_{θ̲₁}^{Min{θ₂, θ̄₁}}`, which equals
`((θ₂ - (1 - Φ₂)/φ₂) - Min{θ₂, θ̄₁})Φ₁(Min{θ₂, θ̄₁})`. -/
theorem mss_step2_display23 (D : Fin 2 → TypeDensity) :
    ∫ b in (D 1).lo..(D 1).hi, (∫ x in (D 0).lo..min b (D 0).hi,
        (((D 1).virtualValue b - x) * (D 0).dens x - (D 0).cdf x)) * (D 1).dens b =
      ∫ b in (D 1).lo..(D 1).hi,
        ((((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) -
          ((D 1).virtualValue b - (D 0).lo) * (D 0).cdf (D 0).lo) * (D 1).dens b) ∧
    ∫ b in (D 1).lo..(D 1).hi,
        ((((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) -
          ((D 1).virtualValue b - (D 0).lo) * (D 0).cdf (D 0).lo) * (D 1).dens b) =
      ∫ b in (D 1).lo..(D 1).hi,
        ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) * (D 1).dens b := by
  refine ⟨intervalIntegral.integral_congr fun b _ => ?_,
    intervalIntegral.integral_congr fun b _ => ?_⟩
  · rw [mss_integral_key, mss_cdf_lo]
    ring
  · rw [mss_cdf_lo]
    ring

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), fourth display: splitting the
buyer's types at `θ̄₁` (where `θ̲₂ < θ̄₁`),
`∫_{θ̲₂}^{θ̄₂} ((θ₂ - (1 - Φ₂)/φ₂) - Min{θ₂, θ̄₁})Φ₁(Min{θ₂, θ̄₁})φ₂ dθ₂
 = -∫_{θ̲₂}^{θ̄₁} [1 - Φ₂(θ₂)]Φ₁(θ₂) dθ₂ + ∫_{θ̄₁}^{θ̄₂} [(θ₂ - θ̄₁)φ₂(θ₂) + (Φ₂(θ₂) - 1)] dθ₂`.
(If `θ̄₁ > θ̄₂` the second interval is reversed; the identity holds with `φ₂ = 0`, `Φ₂ = 1`
above `θ̄₂`.) -/
theorem mss_step2_display4 (D : Fin 2 → TypeDensity) (hov : (D 1).lo < (D 0).hi) :
    ∫ b in (D 1).lo..(D 1).hi,
        ((D 1).virtualValue b - min b (D 0).hi) * (D 0).cdf (min b (D 0).hi) * (D 1).dens b =
      -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) +
        ∫ b in (D 0).hi..(D 1).hi, ((b - (D 0).hi) * (D 1).dens b + ((D 1).cdf b - 1)) := by
  set E := D 1 with hE
  set F := D 0 with hF
  set G : ℝ → ℝ := fun b => (E.virtualValue b - min b F.hi) * F.cdf (min b F.hi) * E.dens b
    with hG
  have e1 : ∀ x ∈ Set.uIoc E.lo F.hi, G x = -((1 - E.cdf x) * F.cdf x) := by
    intro x hx
    rw [Set.uIoc_of_le hov.le] at hx
    simp only [hG, min_eq_left hx.2]
    rcases le_or_gt x E.hi with h | h
    · rw [mul_right_comm, sub_mul, mss_virtualValue_mul E ⟨hx.1.le, h⟩]; ring
    · rw [E.dens_eq_zero x fun h' => absurd h'.2 (not_le.2 h), mss_cdf_of_ge E h.le]; ring
  have e2 : ∀ x ∈ Set.uIoc F.hi E.hi, G x = (x - F.hi) * E.dens x + (E.cdf x - 1) := by
    intro x hx
    rcases Set.mem_uIoc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [hG, min_eq_right h1.le, mss_cdf_hi, mul_one]
      rw [sub_mul, mss_virtualValue_mul E ⟨hov.le.trans h1.le, h2⟩]; ring
    · simp only [hG]
      rw [E.dens_eq_zero x fun h' => absurd h'.2 (not_le.2 h1), mss_cdf_of_ge E h1.le]; ring
  have i1 : IntervalIntegrable (fun x => -((1 - E.cdf x) * F.cdf x)) volume E.lo F.hi :=
    (((continuous_const.sub E.continuous_cdf).mul F.continuous_cdf).neg).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => (x - F.hi) * E.dens x + (E.cdf x - 1)) volume
      F.hi E.hi :=
    (mss_ii_mul_dens E (continuous_id.sub continuous_const) _ _).add
      ((E.continuous_cdf.sub continuous_const).intervalIntegrable _ _)
  have j1 : IntervalIntegrable G volume E.lo F.hi := by
    rw [intervalIntegrable_iff] at i1 ⊢
    exact i1.congr_fun (fun x hx => (e1 x hx).symm) measurableSet_uIoc
  have j2 : IntervalIntegrable G volume F.hi E.hi := by
    rw [intervalIntegrable_iff] at i2 ⊢
    exact i2.congr_fun (fun x hx => (e2 x hx).symm) measurableSet_uIoc
  rw [← intervalIntegral.integral_add_adjacent_intervals j1 j2,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e1),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e2),
    intervalIntegral.integral_neg]

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), fifth display:
`∫_{θ̄₁}^{θ̄₂} [(θ₂ - θ̄₁)φ₂(θ₂) + (Φ₂(θ₂) - 1)] dθ₂ = [(θ₂ - θ̄₁)(Φ₂(θ₂) - 1)]_{θ̄₁}^{θ̄₂} = 0`
(for any `θ̄₁`; proved by the Fubini identity rather than by differentiating, which would need
`φ₂` continuous). -/
theorem mss_step2_display5 (D : Fin 2 → TypeDensity) :
    ∫ b in (D 0).hi..(D 1).hi, ((b - (D 0).hi) * (D 1).dens b + ((D 1).cdf b - 1)) =
      ((D 1).hi - (D 0).hi) * ((D 1).cdf (D 1).hi - 1) -
        ((D 0).hi - (D 0).hi) * ((D 1).cdf (D 0).hi - 1) ∧
    ((D 1).hi - (D 0).hi) * ((D 1).cdf (D 1).hi - 1) -
        ((D 0).hi - (D 0).hi) * ((D 1).cdf (D 0).hi - 1) = 0 := by
  set E := D 1 with hE
  set a := (D 0).hi with ha
  have hz : ((E.hi - a) * (E.cdf E.hi - 1) - (a - a) * (E.cdf a - 1)) = 0 := by
    rw [mss_cdf_hi]; ring
  refine ⟨?_, hz⟩
  rw [hz]
  have k1 := mss_integral_key E E.hi a
  have k2 := mss_integral_key E a a
  have ii : ∀ u v : ℝ, IntervalIntegrable (fun x => (a - x) * E.dens x - E.cdf x) volume u v :=
    fun u v => (mss_ii_mul_dens E (continuous_const.sub continuous_id) _ _).sub (mss_ii_cdf E _ _)
  have k3 := intervalIntegral.integral_interval_sub_left (ii E.lo E.hi) (ii E.lo a)
  rw [k1, k2, mss_cdf_hi] at k3
  have e : ∀ x, (x - a) * E.dens x + (E.cdf x - 1) = -((a - x) * E.dens x - E.cdf x) - 1 :=
    fun x => by ring
  simp only [e]
  rw [intervalIntegral.integral_sub (f := fun x => -((a - x) * E.dens x - E.cdf x))
    (g := fun _ => (1 : ℝ)) (ii a E.hi).neg intervalIntegrable_const,
    intervalIntegral.integral_neg, ← k3, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896), last display:
`-∫_{θ̲₂}^{θ̄₁} [1 - Φ₂(θ₂)]Φ₁(θ₂) dθ₂ < 0` "because `θ̄₁ > θ̲₂` and `θ̲₁ < θ̄₂`". -/
theorem mss_step2_neg (D : Fin 2 → TypeDensity) (h01 : (D 0).lo < (D 1).hi)
    (h10 : (D 1).lo < (D 0).hi) :
    -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) < 0 := by
  set E := D 1 with hE
  set F := D 0 with hF
  set g : ℝ → ℝ := fun b => (1 - E.cdf b) * F.cdf b with hg
  have gc : Continuous g := (continuous_const.sub E.continuous_cdf).mul F.continuous_cdf
  have g0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (by linarith [(mss_cdf_mem E x).2])
    (mss_cdf_mem F x).1
  set a := max F.lo E.lo with ha
  set b := min F.hi E.hi with hb
  have hab : a < b := max_lt (lt_min F.lo_lt_hi h01) (lt_min h10 E.lo_lt_hi)
  have h1 : E.lo ≤ a := le_max_right _ _
  have h2 : b ≤ F.hi := min_le_left _ _
  have p1 : 0 ≤ ∫ x in E.lo..a, g x := intervalIntegral.integral_nonneg h1 fun x _ => g0 x
  have p3 : 0 ≤ ∫ x in b..F.hi, g x := intervalIntegral.integral_nonneg h2 fun x _ => g0 x
  have p2 : 0 < ∫ x in a..b, g x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (gc.intervalIntegrable _ _)
      (fun x hx => mul_pos (mss_one_sub_cdf_pos E (lt_of_lt_of_le hx.2 (min_le_right _ _)))
        (mss_cdf_pos F (lt_of_le_of_lt (le_max_left _ _) hx.1))) hab
  have s1 := intervalIntegral.integral_add_adjacent_intervals (a := E.lo) (b := a) (c := F.hi)
    (gc.intervalIntegrable (μ := volume) _ _) (gc.intervalIntegrable (μ := volume) _ _)
  have s2 := intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b) (c := F.hi)
    (gc.intervalIntegrable (μ := volume) _ _) (gc.intervalIntegrable (μ := volume) _ _)
  change -(∫ x in E.lo..F.hi, g x) < 0
  linarith

/-- **Proof of Proposition 23.E.1, Step 2** (MWG, p. 896): condition (23.E.4) cannot be
satisfied by the efficient trading rule (`y₂ = 1` whenever `θ₂ > θ₁`, `y₂ = 0` whenever
`θ₂ < θ₁`): its left side equals `-∫_{θ̲₂}^{θ̄₁} [1 - Φ₂(θ₂)]Φ₁(θ₂) dθ₂ < 0` when
`(θ̲₁, θ̄₁) ∩ (θ̲₂, θ̄₂) ≠ ∅`. -/
theorem mss_step2 (D : Fin 2 → TypeDensity) (h01 : (D 0).lo < (D 1).hi)
    (h10 : (D 1).lo < (D 0).hi) {y : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y) :
    ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) =
      -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) ∧
    ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) < 0 := by
  have h : ∫ θ, y θ 1 * ((D 1).virtualValue (θ 1) - (D 0).virtualCost (θ 0))
        ∂Measure.pi (fun j => (D j).measure) =
      -(∫ b in (D 1).lo..(D 0).hi, (1 - (D 1).cdf b) * (D 0).cdf b) := by
    rw [mss_step2_display1 D hym heff, (mss_step2_display23 D).1, (mss_step2_display23 D).2,
      mss_step2_display4 D h10, (mss_step2_display5 D).1, (mss_step2_display5 D).2, add_zero]
  exact ⟨h, h ▸ mss_step2_neg D h01 h10⟩

/-- **Proposition 23.E.1** (MWG, p. 895), the Myerson-Satterthwaite theorem, by MWG's own
two-step proof: Step 1 (`eq_23_E_4`) says that any Bayesian incentive compatible, interim
individually rational social choice function with `y₁ + y₂ = 1` and `t₁ + t₂ = 0` satisfies
(23.E.4); Step 2 (`mss_step2`) says that the efficient trading rule violates (23.E.4). Same
hypotheses as `proposition_23_E_1` (the expectations in (23.E.4) exist because `y` is
measurable and `y₂ ∈ [0, 1]`). -/
theorem proposition_23_E_1_mwg (D : Fin 2 → TypeDensity)
    (hov : (Set.Ioo (D 0).lo (D 0).hi ∩ Set.Ioo (D 1).lo (D 1).hi).Nonempty)
    {y t : (Fin 2 → ℝ) → Fin 2 → ℝ} (hym : Measurable y)
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (heff : ExPostEfficientTrade (fun i => (D i).lo) (fun i => (D i).hi) y)
    (hbb : BudgetBalancedOn (fun i => (D i).lo) (fun i => (D i).hi) t)
    (hbic : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hir : InterimIR (Measure.pi fun j => (D j).measure) y t (fun i => (D i).lo)
      fun i => (D i).hi) : False := by
  obtain ⟨z, ⟨hz0, hz0'⟩, ⟨hz1, hz1'⟩⟩ := hov
  obtain ⟨hyJ, hyK, -⟩ := mss_integrable_y_mul D ((measurable_pi_apply 1).comp hym)
    fun θ hθ => by
      obtain ⟨-, h0, h1, -, -⟩ := heff θ hθ
      exact abs_le.2 ⟨by linarith, h1⟩
  have h1 := eq_23_E_4 D hint hbic ht (fun θ hθ => (heff θ hθ).1) hbb hir hyJ hyK
  have h2 := (mss_step2 D (hz0.trans hz1') (hz1.trans hz0') hym heff).2
  linarith

/-- Non-vacuity of Step 1 (`eq_23_E_4`): with both types uniform on `[0, 1]`, the posted-price
rule at `1/2` satisfies every hypothesis of (23.E.4) (Bayesian incentive compatibility, interim
individual rationality, `y₁ + y₂ = 1`, budget balance, the expectations existing). -/
theorem eq_23_E_4_instance :
    InterimIntegrable (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) allocV
      postY postT (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) ∧
    BayesianICOn (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) allocV
      postY postT (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) ∧
    (∀ i, Integrable (fun θ => postT θ i)
      (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure)) ∧
    (∀ θ, postY θ 0 + postY θ 1 = 1) ∧
    BudgetBalancedOn (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) postT ∧
    InterimIR (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) postY postT
      (fun i => ((fun _ : Fin 2 => uniform01) i).lo)
      (fun i => ((fun _ : Fin 2 => uniform01) i).hi) ∧
    Integrable (fun θ => postY θ 1 * uniform01.virtualValue (θ 1))
      (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) ∧
    Integrable (fun θ => postY θ 1 * uniform01.virtualCost (θ 0))
      (Measure.pi fun j => ((fun _ : Fin 2 => uniform01) j).measure) := by
  have := uniform01.isProbabilityMeasure
  obtain ⟨hint, -, hbic, -, hir, hbb, -⟩ := proposition_23_E_1_instance_no_eff
  have hq : ∀ θ, 0 ≤ postQ θ ∧ postQ θ ≤ 1 := fun θ => by
    simp only [postQ]; split_ifs <;> norm_num
  obtain ⟨hyJ, hyK, -⟩ := mss_integrable_y_mul (fun _ : Fin 2 => uniform01) (y := postY)
    (by simpa [postY] using measurable_postQ) fun θ _ => by
      simp only [postY, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact abs_le.2 ⟨by linarith [(hq θ).1], (hq θ).2⟩
  refine ⟨hint, hbic, fun i => ?_, fun θ => by simp [postY], hbb, hir, hyJ, hyK⟩
  refine ms_integrable_of_bound (fun _ : Fin 2 => uniform01.measure) ms_unif_hyps.1 ?_ 1
    fun θ _ => ?_
  · fin_cases i
    · simpa [postT] using measurable_postQ.div_const 2
    · simpa [postT] using measurable_postQ.div_const 2
  · fin_cases i <;> simp only [postT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_neg] <;>
      rw [abs_le] <;> constructor <;> linarith [hq θ]

/-! ### Exercise 23.E.6(b): uniqueness of the symmetric linear equilibrium -/

/-- Exercise 23.E.6(b) with a general linear strategy of the other partner: the expected utility
of a partner with valuation `θ` who bids `β` when the other (valuation `s ~ U[0, 1]`) bids
`as + d`: if `β ≥ as + d` he buys the other's unit at `β` (utility `2θ - β`), otherwise the other
buys his unit and pays `as + d`. -/
noncomputable def partnerEULin (a d β θ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, if a * s + d ≤ β then 2 * θ - β else a * s + d

/-- `partnerEULin` against `b(s) = 2s/3` is `partnerEU`. -/
theorem partnerEULin_two_thirds (β θ : ℝ) : partnerEULin (2 / 3) 0 β θ = partnerEU β θ := by
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : 2 / 3 * s + 0 = 2 * s / 3 := by ring
  simp only [e]

/-- Closed form of `partnerEULin` for a bid `β = ap + d` with `p ∈ [0, 1]` (the bidder wins
exactly when the other's valuation is at most `p`), `a > 0`:
`(2θ - β)p + a(1 - p²)/2 + d(1 - p)`. -/
theorem partnerEULin_eq {a d θ p : ℝ} (ha : 0 < a) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    partnerEULin a d (a * p + d) θ =
      (2 * θ - (a * p + d)) * p + a * (1 - p ^ 2) / 2 + d * (1 - p) := by
  set g : ℝ → ℝ := fun s => if a * s + d ≤ a * p + d then 2 * θ - (a * p + d) else a * s + d
    with hg
  have e1 : ∀ x ∈ Set.uIoc 0 p, g x = 2 * θ - (a * p + d) := by
    intro x hx
    rw [Set.uIoc_of_le hp.1] at hx
    have : a * x + d ≤ a * p + d := by nlinarith [hx.2]
    simp only [hg, this, ite_true]
  have e2 : ∀ x ∈ Set.uIoc p 1, g x = a * x + d := by
    intro x hx
    rw [Set.uIoc_of_le hp.2] at hx
    have : ¬a * x + d ≤ a * p + d := by nlinarith [hx.1]
    simp only [hg, this, ite_false]
  have j1 : IntervalIntegrable g volume 0 p := by
    have i1 : IntervalIntegrable (fun _ : ℝ => 2 * θ - (a * p + d)) volume 0 p :=
      intervalIntegrable_const
    rw [intervalIntegrable_iff] at i1 ⊢
    exact i1.congr_fun (fun x hx => (e1 x hx).symm) measurableSet_uIoc
  have j2 : IntervalIntegrable g volume p 1 := by
    have i2 : IntervalIntegrable (fun x : ℝ => a * x + d) volume p 1 :=
      (continuous_const.mul continuous_id |>.add continuous_const).intervalIntegrable _ _
    rw [intervalIntegrable_iff] at i2 ⊢
    exact i2.congr_fun (fun x hx => (e2 x hx).symm) measurableSet_uIoc
  change ∫ s in (0 : ℝ)..1, g s = _
  rw [← intervalIntegral.integral_add_adjacent_intervals j1 j2,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e1),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall e2),
    intervalIntegral.integral_add (f := fun x => a * x) (g := fun _ => d)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  ring

/-- In a symmetric linear equilibrium, the derivative of the bidder's objective in the winning
probability vanishes at every interior type: `2θ - 3aθ - 2d = 0`. -/
theorem partner_foc {a d θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (heq : ∀ β, partnerEULin a d β θ ≤ partnerEULin a d (a * θ + d) θ) :
    2 * θ - 3 * a * θ - 2 * d = 0 := by
  set D := 2 * θ - 3 * a * θ - 2 * d with hD
  set m := min θ (1 - θ) with hm
  have hm0 : 0 < m := lt_min hθ.1 (by linarith [hθ.2])
  set ε := m / (3 * a + 2 * |D| + 2) with hε
  have hden : 0 < 3 * a + 2 * |D| + 2 := by positivity
  have hε0 : 0 < ε := div_pos hm0 hden
  have hεD : |ε * D| ≤ m / 2 := by
    rw [abs_mul, abs_of_pos hε0, hε, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
    nlinarith [abs_nonneg D]
  have hεa : 3 * a * ε ≤ m := by
    rw [hε, mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith [abs_nonneg D]
  have hm1 : m ≤ 1 := (min_le_left _ _).trans hθ.2.le
  have hp : θ + ε * D ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 := abs_le.1 hεD
    have h2 : m ≤ θ := min_le_left _ _
    have h3 : m ≤ 1 - θ := min_le_right _ _
    constructor <;> linarith [h1.1, h1.2]
  have h := heq (a * (θ + ε * D) + d)
  rw [partnerEULin_eq ha hp, partnerEULin_eq ha ⟨hθ.1.le, hθ.2.le⟩] at h
  have key : ε * D ^ 2 * (1 - 3 * a * ε / 2) ≤ 0 := by nlinarith
  have hpos : 0 < 1 - 3 * a * ε / 2 := by linarith
  have : D ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos (mul_pos hε0 hc) hpos
    linarith
  nlinarith [sq_nonneg D]

/-- **Exercise 23.E.6(b)** (MWG, p. 922), uniqueness: among strictly increasing linear
strategies `b(θ) = aθ + d` (`a > 0`), `b(θ) = 2θ/3` is the only symmetric Bayesian Nash
equilibrium of "the highest bidder buys the other's unit and pays his bid" with valuations
uniform on `[0, 1]`: if no type `θ ∈ [0, 1]` gains by any bid `β` when the other partner uses
`b`, then `a = 2/3` and `d = 0`; conversely `b(θ) = 2θ/3` is an equilibrium
(`exercise_23_E_6b`). (With `a > 0` ties have probability zero, so the tie rule is
irrelevant.) -/
theorem exercise_23_E_6b_unique {a d : ℝ} (ha : 0 < a) :
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ β, partnerEULin a d β θ ≤ partnerEULin a d (a * θ + d) θ) ↔
      a = 2 / 3 ∧ d = 0 := by
  constructor
  · intro heq
    have h1 := partner_foc ha (θ := 1 / 2) ⟨by norm_num, by norm_num⟩
      (heq (1 / 2) ⟨by norm_num, by norm_num⟩)
    have h2 := partner_foc ha (θ := 1 / 4) ⟨by norm_num, by norm_num⟩
      (heq (1 / 4) ⟨by norm_num, by norm_num⟩)
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩ θ hθ β
    rw [partnerEULin_two_thirds, partnerEULin_two_thirds,
      show 2 / 3 * θ + 0 = 2 * θ / 3 by ring]
    exact exercise_23_E_6b hθ β

end MWG.MechanismDesign
