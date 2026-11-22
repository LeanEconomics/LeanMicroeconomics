/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.LinearBIC
import MWGMechanismDesign.ExpectedExternality
import MWGMechanismDesign.TypeDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The revenue equivalence theorem

MWG, Section 23.D, pp. 889-891, and Exercises 23.D.2, 23.D.3 (p. 921).

The auction setting (p. 889): `I` buyers, `yᵢ(θ)` buyer `i`'s probability of getting the good,
`vᵢ(y) = yᵢ` (`allocV`), linear utilities `θᵢyᵢ + tᵢ`, independent types `P = ∏ᵢ μᵢ`.

* `re_expected_transfer`: `E[tᵢ(θ)] = E[t̄ᵢ(θᵢ)]`; `re_interimTransfer_eq`: for a Bayesian
  incentive compatible `f`, `t̄ᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ - θᵢȳᵢ(θᵢ)` on `Θᵢ`.
* **Proposition 23.D.3** (`proposition_23_D_3`), at the level of social choice functions as in
  MWG's proof: two Bayesian incentive compatible social choice functions with the same `y` and the
  same `Uᵢ(θ̲ᵢ)` have the same expected payment from every buyer, hence the same expected revenue.
  Only `μᵢ([θ̲ᵢ, θ̄ᵢ]ᶜ) = 0` is used, not densities.
* With densities (`TypeDensity`): (23.D.14) `eq_23_D_14`, (23.D.15) `eq_23_D_15`, (23.D.16)
  `eq_23_D_16`, with `Jᵢ(θ) = θ - (1 - Φᵢ(θ))/φᵢ(θ)` (`TypeDensity.virtualValue`). MWG's
  integration by parts is replaced by the Fubini identity `TypeDensity.integral_integral_eq`;
  (23.D.15)-(23.D.16) assume that `E[yᵢ(θ)Jᵢ(θᵢ)]` exists (`eq_23_D_16_instance`: it does, and
  all other hypotheses hold, for the first-price rule with uniform types).
* Two buyers uniform on `[0, 1]` (`unif2`): Exercise 23.D.3 (`exercise_23_D_3`,
  `exercise_23_D_3_revenue_equivalence`): the first-price equilibrium social choice function
  (23.B.9)-(23.B.14) and the second-price one are Bayesian incentive compatible, have the same
  `y`, `Uᵢ(0) = 0`, and expected revenue `1/3` each.
* Exercise 23.D.2: the expected externality mechanism for bilateral trade with uniform types has
  `ξᵢ(a) = (1 - a²)/2` and transfers `t₀ = (θ₁² - θ₀²)/2 = -t₁` (`exercise_23_D_2a`); truth
  telling is a Bayesian Nash equilibrium (`exercise_23_D_2b`, via `agv_bayesianIC`).

No corrections; departures: the revenue equivalence theorem needs no densities, and integrability
hypotheses (expectations exist) are explicit.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The auction setting (MWG, p. 889): an outcome is `(y, t)` with `y = (y₁, …, y_I)` the buyers'
probabilities of getting the good, and buyer `i`'s benefit is `vᵢ(y) = yᵢ`. -/
def allocV : ι → (ι → ℝ) → ℝ := fun i y => y i

/-- Points of `[a, b]` are bounded by `|a| + |b|`. -/
theorem re_abs_le_of_mem {x a b : ℝ} (h : x ∈ Set.Icc a b) : |x| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, h.1]
  · linarith [le_abs_self b, abs_nonneg a, h.2]

/-- With independent types, `θ ↦ E_{θ₋ᵢ}[g(θᵢ, θ₋ᵢ)]` is integrable when `g` is. -/
theorem re_integrable_integral_update (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {g : (ι → ℝ) → ℝ} (hg : Integrable g (Measure.pi μ)) :
    Integrable (fun θ => ∫ θ', g (update θ' i (θ i)) ∂Measure.pi μ) (Measure.pi μ) := by
  have hmap := map_splice (Θ := fun _ => ℝ) μ i
  have hgm : AEStronglyMeasurable g
      (((Measure.pi μ).prod (Measure.pi μ)).map (splice i)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  have hint : Integrable (g ∘ splice i) ((Measure.pi μ).prod (Measure.pi μ)) := by
    rw [← integrable_map_measure hgm (measurable_splice i).aemeasurable, hmap]
    exact hg
  exact hint.integral_prod_left

omit [DecidableEq ι] in
/-- If each `μᵢ` is concentrated on `[θ̲ᵢ, θ̄ᵢ]`, almost every profile lies in `Θ`. -/
theorem re_ae_mem (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) :
    ∀ᵐ θ ∂Measure.pi μ, ∀ i, θ i ∈ Set.Icc (lo i) (hi i) := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ x ∂μ i, x ∈ Set.Icc (lo i) (hi i) := mem_ae_iff.2 (hsupp i)
  exact Measure.tendsto_eval_ae_ae.eventually h

/-- If each `μᵢ` is concentrated on `[θ̲ᵢ, θ̄ᵢ]` and `a ∈ Θᵢ`, almost every `(a, θ₋ᵢ)` lies in
`Θ`. -/
theorem re_ae_update_mem (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {lo hi : ι → ℝ}
    (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0) {i : ι} {a : ℝ}
    (ha : a ∈ Set.Icc (lo i) (hi i)) :
    ∀ᵐ θ ∂Measure.pi μ, ∀ j, update θ i a j ∈ Set.Icc (lo j) (hi j) := by
  filter_upwards [re_ae_mem μ hsupp] with θ hθ j
  by_cases hj : j = i
  · subst hj; simpa using ha
  · simpa [hj] using hθ j

/-- With independent types, `E[tᵢ(θ)] = E_{θᵢ}[t̄ᵢ(θᵢ)]` (MWG, p. 890). -/
theorem re_expected_transfer (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {t : (ι → ℝ) → ι → ℝ} (i : ι) (ht : Integrable (fun θ => t θ i) (Measure.pi μ)) :
    ∫ θ, t θ i ∂Measure.pi μ = ∫ θ, interimTransfer (Measure.pi μ) t i (θ i) ∂Measure.pi μ :=
  (integral_integral_update (Θ := fun _ => ℝ) μ i ht).symm

omit [Fintype ι] in
/-- For a Bayesian incentive compatible `f = (y, t)` in the linear model, the expected transfer of
type `θᵢ ∈ Θᵢ` is determined by `y` and `Uᵢ(θ̲ᵢ)`:
`t̄ᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} v̄ᵢ - θᵢv̄ᵢ(θᵢ)` (MWG, pp. 889-890). -/
theorem re_interimTransfer_eq {K : Type*} {P : Measure (ι → ℝ)} {vk : ι → K → ℝ}
    {k : (ι → ℝ) → K} {t : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ}
    (hint : InterimIntegrable P vk k t lo hi) (hf : BayesianICOn P vk k t lo hi) (i : ι) {x : ℝ}
    (hx : x ∈ Set.Icc (lo i) (hi i)) :
    interimTransfer P t i x = interimU P vk k t i (lo i) + (∫ s in (lo i)..x,
      interimBenefit P vk k i s) - x * interimBenefit P vk k i x := by
  have := ((proposition_23_D_2 hint).1 hf i).2 x hx
  simp only [interimU] at this ⊢
  linarith

/-- **Proposition 23.D.3** (MWG, p. 890), the revenue equivalence theorem, at the level of social
choice functions as in MWG's proof. Buyers' valuations are independent (`P = ∏ᵢ μᵢ`) with `μᵢ`
concentrated on `[θ̲ᵢ, θ̄ᵢ]`. If two Bayesian incentive compatible social choice functions
`(y, t)` and `(y, t')` have (i) the same allocation probabilities `y(θ)` and (ii) the same
`Uᵢ(θ̲ᵢ)` for every buyer, then each buyer's expected payment is the same, so the seller's expected
revenue `∑ᵢ E[-tᵢ(θ)]` is the same. Densities are not needed (only the support condition); the
integrability hypotheses say that the expectations exist. -/
theorem proposition_23_D_3 (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {lo hi : ι → ℝ} (hsupp : ∀ i, μ i (Set.Icc (lo i) (hi i))ᶜ = 0)
    {y : (ι → ℝ) → ι → ℝ} {t t' : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi μ) allocV y t lo hi)
    (hint' : InterimIntegrable (Measure.pi μ) allocV y t' lo hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi μ))
    (ht' : ∀ i, Integrable (fun θ => t' θ i) (Measure.pi μ))
    (hf : BayesianICOn (Measure.pi μ) allocV y t lo hi)
    (hf' : BayesianICOn (Measure.pi μ) allocV y t' lo hi)
    (hU : ∀ i, interimU (Measure.pi μ) allocV y t i (lo i) =
      interimU (Measure.pi μ) allocV y t' i (lo i)) :
    (∀ i, ∫ θ, -t θ i ∂Measure.pi μ = ∫ θ, -t' θ i ∂Measure.pi μ) ∧
      ∑ i, ∫ θ, -t θ i ∂Measure.pi μ = ∑ i, ∫ θ, -t' θ i ∂Measure.pi μ := by
  have hi : ∀ i, ∫ θ, -t θ i ∂Measure.pi μ = ∫ θ, -t' θ i ∂Measure.pi μ := by
    intro i
    rw [integral_neg, integral_neg, re_expected_transfer μ i (ht i),
      re_expected_transfer μ i (ht' i)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [re_ae_mem μ hsupp] with θ hθ
    rw [re_interimTransfer_eq hint hf i (hθ i), re_interimTransfer_eq hint' hf' i (hθ i), hU i]
  exact ⟨hi, Finset.sum_congr rfl fun i _ => hi i⟩

/-! ### Densities: (23.D.14)-(23.D.16) -/

/-- MWG's virtual valuation `θ - (1 - Φ(θ))/φ(θ)` of (23.D.14). -/
noncomputable def TypeDensity.virtualValue (D : TypeDensity) (x : ℝ) : ℝ :=
  x - (1 - D.cdf x) / D.dens x

/-- The distribution is absolutely continuous with respect to Lebesgue measure on `[θ̲, θ̄]`. -/
theorem TypeDensity.absolutelyContinuous (D : TypeDensity) :
    D.measure ≪ volume.restrict (Set.Icc D.lo D.hi) := by
  have h : (fun x => ((D.dens x).toNNReal : ENNReal)) =
      (Set.Icc D.lo D.hi).indicator fun x => ((D.dens x).toNNReal : ENNReal) := by
    funext x
    by_cases hx : x ∈ Set.Icc D.lo D.hi
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, D.dens_eq_zero x hx]; simp
  rw [TypeDensity.measure, h, withDensity_indicator measurableSet_Icc]
  exact withDensity_absolutelyContinuous _ _

/-- A function bounded on `(θ̲, θ̄]` and a.e. strongly measurable there, times the density, is
integrable on `[θ̲, θ̄]`. -/
theorem re_intervalIntegrable_mul_dens (D : TypeDensity) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc D.lo D.hi))) (C : ℝ)
    (hC : ∀ x ∈ Set.Ioc D.lo D.hi, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * D.dens x) volume D.lo D.hi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le D.lo_lt_hi.le]
  refine Integrable.bdd_mul (c := C) D.integrable_dens.integrableOn hg ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
    rw [Real.norm_eq_abs]; exact hC x hx

/-- The distribution function is continuous. -/
theorem TypeDensity.continuous_cdf (D : TypeDensity) : Continuous D.cdf :=
  intervalIntegral.continuous_primitive (fun _ _ => D.integrable_dens.intervalIntegrable) D.lo

/-- **(23.D.14)** (MWG, p. 890). For a Bayesian incentive compatible `f = (y, t)` with independent
types with densities, buyer `i`'s expected payment is
`E[-t̄ᵢ(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(θ)(θ - (1 - Φᵢ(θ))/φᵢ(θ))φᵢ(θ) dθ - Uᵢ(θ̲ᵢ)`. -/
theorem eq_23_D_14 (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι) :
    ∫ x, -interimTransfer (Measure.pi fun j => (D j).measure) t i x ∂(D i).measure =
      (∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        (D i).virtualValue x * (D i).dens x) -
        interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo := by
  set yb := interimBenefit (Measure.pi fun j => (D j).measure) allocV y i with hyb
  set U0 := interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo with hU0
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
  -- integrability of the pieces
  have hA : IntervalIntegrable (fun x => x * yb x * E.dens x) volume E.lo E.hi :=
    re_intervalIntegrable_mul_dens E (continuous_id.aestronglyMeasurable.mul hybm)
      ((|E.lo| + |E.hi|) * Cy) fun x hx => by
        rw [abs_mul]
        exact mul_le_mul (re_abs_le_of_mem ⟨hx.1.le, hx.2⟩) (hyb_bd x ⟨hx.1.le, hx.2⟩)
          (abs_nonneg _) (by positivity)
  have hprim : ContinuousOn (fun x => ∫ s in E.lo..x, yb s) (Set.uIcc E.lo E.hi) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [Set.uIcc_of_le hle, integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hybI)
  have hC : IntervalIntegrable (fun x => (∫ s in E.lo..x, yb s) * E.dens x) volume E.lo E.hi := by
    refine re_intervalIntegrable_mul_dens E ?_ (Cy * (E.hi - E.lo)) fun x hx => ?_
    · refine (hprim.mono ?_).aestronglyMeasurable measurableSet_Ioc
      rw [Set.uIcc_of_le hle]; exact Set.Ioc_subset_Icc_self
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E.lo) (b := x) (f := yb)
        (C := Cy) fun s hs => by
          rw [Set.uIoc_of_le hx.1.le] at hs
          rw [Real.norm_eq_abs]; exact hyb_bd s ⟨hs.1.le, hs.2.trans hx.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - E.lo)] at this
      have : 0 ≤ Cy := by positivity
      nlinarith [hx.2]
  have hB : IntervalIntegrable (fun x => U0 * E.dens x) volume E.lo E.hi :=
    E.intervalIntegrable_dens.const_mul U0
  have hEI : IntervalIntegrable (fun x => yb x * (1 - E.cdf x)) volume E.lo E.hi :=
    hybI.mul_continuousOn (continuous_const.sub E.continuous_cdf).continuousOn
  rw [E.integral_eq]
  have hL : ∫ x in E.lo..E.hi,
      -interimTransfer (Measure.pi fun j => (D j).measure) t i x * E.dens x =
      ∫ x in E.lo..E.hi, ((x * yb x * E.dens x - U0 * E.dens x) -
        (∫ s in E.lo..x, yb s) * E.dens x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    rw [re_interimTransfer_eq hint hf i hx]
    ring
  have hR : ∫ x in E.lo..E.hi, yb x * E.virtualValue x * E.dens x =
      ∫ x in E.lo..E.hi, (x * yb x * E.dens x - yb x * (1 - E.cdf x)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    have := (E.dens_pos x hx).ne'
    simp only [TypeDensity.virtualValue]
    field_simp
  rw [hL, hR, intervalIntegral.integral_sub (hA.sub hB) hC, intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_sub hA hEI, E.integral_integral_eq hybI,
    intervalIntegral.integral_const_mul, E.integral_dens]
  ring

/-- A function monotone on `[θ̲, θ̄]` is a.e. strongly measurable for the type distribution. -/
theorem TypeDensity.aestronglyMeasurable_of_monotoneOn (D : TypeDensity) {g : ℝ → ℝ}
    (hg : MonotoneOn g (Set.Icc D.lo D.hi)) : AEStronglyMeasurable g D.measure :=
  (hg.integrableOn_isCompact isCompact_Icc).aestronglyMeasurable.mono_ac D.absolutelyContinuous

/-- **(23.D.15)** (MWG, p. 891), the multiple-integral form: with independent types with
densities, `E[yᵢ(θ)Jᵢ(θᵢ)] = ∫_{θ̲ᵢ}^{θ̄ᵢ} ȳᵢ(θ)Jᵢ(θ)φᵢ(θ) dθ`, where
`Jᵢ(θ) = θ - (1 - Φᵢ(θ))/φᵢ(θ)`. (The integrability hypothesis says the expectation exists.) -/
theorem eq_23_D_15 (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi) (i : ι)
    (hyJ : Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
      (Measure.pi fun j => (D j).measure)) :
    ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) =
      ∫ x in (D i).lo..(D i).hi, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
        (D i).virtualValue x * (D i).dens x := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hmono : MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc (D i).lo (D i).hi) := ((proposition_23_D_2 hint).1 hf i).1
  have hJ : Measurable (D i).virtualValue :=
    measurable_id.sub (((continuous_const.sub (D i).continuous_cdf).measurable).div
      (D i).measurable_dens)
  rw [← integral_integral_update (Θ := fun _ => ℝ) (fun j => (D j).measure) i hyJ]
  simp only [update_self]
  simp_rw [integral_mul_const]
  have h := integral_eval_pi (Θ := fun _ => ℝ) (fun j => (D j).measure) i
    (F := fun x => interimBenefit (Measure.pi fun j => (D j).measure) allocV y i x *
      (D i).virtualValue x)
    (((D i).aestronglyMeasurable_of_monotoneOn hmono).mul hJ.aestronglyMeasurable)
  rw [(D i).integral_eq] at h
  exact h

/-- **(23.D.16)** (MWG, p. 891). With independent types with densities, the seller's expected
revenue from a Bayesian incentive compatible `f = (y, t)` is
`∑ᵢ E[-tᵢ(θ)] = ∑ᵢ E[yᵢ(θ)Jᵢ(θᵢ)] - ∑ᵢ Uᵢ(θ̲ᵢ)`, `Jᵢ(θ) = θ - (1 - Φᵢ(θ))/φᵢ(θ)`. Hence any two
Bayesian incentive compatible social choice functions with the same `y` and the same `Uᵢ(θ̲ᵢ)`
generate the same expected revenue. (The integrability hypotheses say the expectations exist.) -/
theorem eq_23_D_16 (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (ht : ∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure))
    (hyJ : ∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
      (Measure.pi fun j => (D j).measure)) :
    ∑ i, ∫ θ, -t θ i ∂Measure.pi (fun j => (D j).measure) =
      ∑ i, ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) -
        ∑ i, interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eq_23_D_15 D hint hf i (hyJ i), ← eq_23_D_14 D hint hf i, integral_neg, integral_neg,
    re_expected_transfer (fun j => (D j).measure) i (ht i)]
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

/-! ### Two agents with types uniform on `[0, 1]` -/

/-- The prior of two agents whose types are independent and uniform on `[0, 1]`. -/
noncomputable abbrev unif2 : Measure (Fin 2 → ℝ) := Measure.pi fun _ : Fin 2 => uniform01.measure

/-- `update (x, x) 0 a = (a, x)`. -/
theorem re_update_vec0 (x a : ℝ) : update ![x, x] 0 a = ![a, x] := by
  funext j; fin_cases j <;> simp

/-- `update (x, x) 1 a = (x, a)`. -/
theorem re_update_vec1 (x a : ℝ) : update ![x, x] 1 a = ![x, a] := by
  funext j; fin_cases j <;> simp

/-- With two agents whose types are independent and uniform on `[0, 1]`,
`E_{θ₋ᵢ}[G(a, θ₋ᵢ)] = ∫_0^1 G(update (x, x) i a) dx`. -/
theorem re_unif2_update {G : (Fin 2 → ℝ) → ℝ} (hG : Measurable G) (i : Fin 2) (a : ℝ) :
    ∫ θ', G (update θ' i a) ∂unif2 = ∫ x in (0 : ℝ)..1, G (update ![x, x] i a) := by
  have := uniform01.isProbabilityMeasure
  set c : Fin 2 := if i = 0 then 1 else 0 with hc
  have hG' : (fun θ' => G (update θ' i a)) =
      fun θ' => (fun x => G (update ![x, x] i a)) (θ' c) := by
    funext θ'
    congr 1
    funext j
    fin_cases i <;> fin_cases j <;> simp [c]
  have hm : Measurable fun x : ℝ => G (update ![x, x] i a) := by fun_prop
  rw [hG']
  exact (integral_eval_pi (Θ := fun _ => ℝ) (fun _ => uniform01.measure) c
    (F := fun x => G (update ![x, x] i a)) hm.aestronglyMeasurable).trans (uniform01_integral _)

/-- With two agents whose types are independent and uniform on `[0, 1]`,
`E[F(θ)] = ∫_0^1 ∫_0^1 F(a, x) dx da`. -/
theorem re_unif2_integral {F : (Fin 2 → ℝ) → ℝ} (hF : Integrable F unif2) :
    ∫ θ, F θ ∂unif2 = ∫ a in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F ![a, x] := by
  have := uniform01.isProbabilityMeasure
  have hmp := measurePreserving_finTwoArrow uniform01.measure
  have h1 := hmp.integral_comp' (g := fun p => F (MeasurableEquiv.finTwoArrow.symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  have hI : Integrable (fun p => F (MeasurableEquiv.finTwoArrow.symm p))
      (uniform01.measure.prod uniform01.measure) :=
    (hmp.integrable_comp_emb MeasurableEquiv.finTwoArrow.measurableEmbedding).1 (by
      simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]; exact hF)
  rw [h1, integral_prod _ hI, uniform01_integral]
  simp_rw [uniform01_integral]
  rfl

/-- `∫_0^1 1{x ≤ a} g(x) dx = ∫_0^a g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_le {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x ≤ a then g x else 0) = ∫ x in (0 : ℝ)..a, g x := by
  have e : (fun x => if x ≤ a then g x else 0) = (Set.Iic a).indicator g := by
    funext x; simp [Set.indicator_apply]
  rw [e, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le ha.1,
    setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic, inf_eq_right.2 ha.2]

/-- `∫_0^1 1{x < a} g(x) dx = ∫_0^a g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_lt {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if x < a then g x else 0) = ∫ x in (0 : ℝ)..a, g x := by
  have e : (fun x => if x < a then g x else 0) = (Set.Iio a).indicator g := by
    funext x; simp [Set.indicator_apply]
  have hs : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio a = Set.Ioo 0 a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith [ha.2]⟩, h2⟩
  rw [e, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le ha.1,
    setIntegral_indicator measurableSet_Iio, hs, integral_Ioc_eq_integral_Ioo]

/-- `∫_0^1 1{a < x} g(x) dx = ∫_a^1 g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_gt {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if a < x then g x else 0) = ∫ x in a..1, g x := by
  have e : (fun x => if a < x then g x else 0) = (Set.Ioi a).indicator g := by
    funext x; simp [Set.indicator_apply]
  have hs : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi a = Set.Ioc a 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [ha.1], h2⟩, h1⟩
  rw [e, intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le ha.2,
    setIntegral_indicator measurableSet_Ioi, hs]

/-- The allocation of Examples 23.B.4-23.B.6 for two agents: agent `1` gets the good iff
`θ₀ < θ₁` (ties go to agent `0`). -/
noncomputable def twoY : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![if θ 1 ≤ θ 0 then 1 else 0, if θ 0 < θ 1 then 1 else 0]

/-- The transfers (23.B.12)-(23.B.14) of the first-price sealed-bid auction equilibrium
(Example 23.B.5): the winner pays half his valuation, `tᵢ = -θᵢyᵢ/2`. -/
noncomputable def firstPriceT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![-(θ 0 * twoY θ 0 / 2), -(θ 1 * twoY θ 1 / 2)]

/-- The transfers of the second-price sealed-bid auction (Example 23.B.6): the winner pays the
other's valuation, `t₀ = -θ₁y₀`, `t₁ = -θ₀y₁`. -/
noncomputable def secondPriceT : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun θ => ![-(θ 1 * twoY θ 0), -(θ 0 * twoY θ 1)]

/-- `twoY` is measurable. -/
theorem measurable_twoY (i : Fin 2) : Measurable fun θ => twoY θ i := by
  fin_cases i
  · exact Measurable.ite (measurableSet_le (measurable_pi_apply 1) (measurable_pi_apply 0))
      measurable_const measurable_const
  · exact Measurable.ite (measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 1))
      measurable_const measurable_const

/-- `twoY` is a probability and gives the good to someone. -/
theorem twoY_props (θ : Fin 2 → ℝ) :
    twoY θ 0 + twoY θ 1 = 1 ∧ 0 ≤ twoY θ 1 ∧ twoY θ 1 ≤ 1 ∧ 0 ≤ twoY θ 0 ∧ twoY θ 0 ≤ 1 := by
  simp only [twoY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases h : θ 0 < θ 1
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

/-- `E_{θ₋₀}[y₀(a, θ₋₀)] = a` and `E_{θ₋₁}[y₁(a, θ₋₁)] = a` for `a ∈ [0, 1]`. -/
theorem twoY_interimBenefit {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    interimBenefit unif2 allocV twoY i a = a := by
  unfold interimBenefit
  rw [re_unif2_update (G := fun θ => allocV i (twoY θ)) (measurable_twoY i) i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, allocV, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [re_integral_ite_le ha]; simp
  · simp only [Fin.mk_one, re_update_vec1, allocV, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [re_integral_ite_lt ha]; simp

/-- A measurable function bounded on `[0, 1]²` is integrable for two independent uniform types,
and so is `θ' ↦ F(a, θ'₋ᵢ)` for `a ∈ [0, 1]`. -/
theorem re_unif2_integrable {F : (Fin 2 → ℝ) → ℝ} (hF : Measurable F) (C : ℝ)
    (hC : ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → |F θ| ≤ C) :
    Integrable F unif2 ∧ ∀ (i : Fin 2), ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun θ' => F (update θ' i a)) unif2 := by
  have := uniform01.isProbabilityMeasure
  have hsupp : ∀ _ : Fin 2, uniform01.measure (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    fun _ => uniform01.measure_compl_Icc
  refine ⟨Integrable.of_bound hF.aestronglyMeasurable C ?_, fun i a ha =>
    Integrable.of_bound (hF.comp measurable_update_left).aestronglyMeasurable C ?_⟩
  · filter_upwards [re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
      (hi := fun _ => 1) hsupp] with θ hθ
    rw [Real.norm_eq_abs]; exact hC θ hθ
  · filter_upwards [re_ae_update_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
      (hi := fun _ => 1) hsupp ha] with θ hθ
    rw [Real.norm_eq_abs]; exact hC _ hθ

/-- **Exercise 23.D.3**, the common computation (MWG, p. 921). With two buyers whose valuations
are independent and uniform on `[0, 1]`, allocation `twoY`, and transfers `t` (measurable, bounded
on `[0, 1]²`) whose interim expectations are `t̄ᵢ(a) = c - a²/2`: `f = (twoY, t)` is Bayesian
incentive compatible, `Uᵢ(0) = c`, and the expected revenue is `∑ᵢ E[-tᵢ] = 1/3 - 2c`. -/
theorem re_twoY_bic {t : (Fin 2 → ℝ) → Fin 2 → ℝ} (htm : ∀ i, Measurable fun θ => t θ i)
    (htb : ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → ∀ i, |t θ i| ≤ 1)
    (c : ℝ) (htt : ∀ i, ∀ a ∈ Set.Icc (0 : ℝ) 1, interimTransfer unif2 t i a = c - a ^ 2 / 2) :
    InterimIntegrable unif2 allocV twoY t (fun _ => 0) (fun _ => 1) ∧
      BayesianICOn unif2 allocV twoY t (fun _ => 0) (fun _ => 1) ∧
      (∀ i, interimU unif2 allocV twoY t i 0 = c) ∧
      ∑ i, ∫ θ, -t θ i ∂unif2 = 1 / 3 - 2 * c := by
  have := uniform01.isProbabilityMeasure
  have hyb : ∀ i θ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) → |allocV i (twoY θ)| ≤ 1 := by
    intro i θ _
    obtain ⟨h1, h2, h3, h4, h5⟩ := twoY_props θ
    fin_cases i
    · exact abs_le.2 ⟨by simp [allocV]; linarith, h5⟩
    · exact abs_le.2 ⟨by simp [allocV]; linarith, h3⟩
  have hint : InterimIntegrable unif2 allocV twoY t (fun _ => 0) (fun _ => 1) := fun i a ha =>
    ⟨(re_unif2_integrable (measurable_twoY i) 1 (hyb i)).2 i a ha,
      (re_unif2_integrable (htm i) 1 fun θ hθ => htb θ hθ i).2 i a ha⟩
  have hU : ∀ i, ∀ a ∈ Set.Icc (0 : ℝ) 1, interimU unif2 allocV twoY t i a = a ^ 2 / 2 + c := by
    intro i a ha
    rw [interimU, twoY_interimBenefit ha, htt i a ha]; ring
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hbic : BayesianICOn unif2 allocV twoY t (fun _ => 0) (fun _ => 1) := by
    refine (proposition_23_D_2 hint).2 fun i => ⟨fun a ha b hb hab => ?_, fun θ hθ => ?_⟩
    · rw [twoY_interimBenefit ha, twoY_interimBenefit hb]; exact hab
    · rw [hU i θ hθ, hU i 0 h0, intervalIntegral.integral_congr (g := fun s => s) fun s hs => by
        rw [Set.uIcc_of_le hθ.1] at hs
        exact twoY_interimBenefit ⟨hs.1, hs.2.trans hθ.2⟩ i, integral_id]
      ring
  refine ⟨hint, hbic, fun i => by rw [hU i 0 h0]; ring, ?_⟩
  have hrev : ∀ i, ∫ θ, -t θ i ∂unif2 = 1 / 6 - c := by
    intro i
    rw [integral_neg, re_expected_transfer (fun _ : Fin 2 => uniform01.measure) i
      ((re_unif2_integrable (htm i) 1 fun θ hθ => htb θ hθ i).1)]
    rw [integral_congr_ae (g := fun θ => c - (θ i) ^ 2 / 2) ?_]
    · rw [integral_eval_pi (Θ := fun _ => ℝ) (fun _ : Fin 2 => uniform01.measure) i
        (F := fun x => c - x ^ 2 / 2) (by fun_prop), uniform01_integral,
        intervalIntegral.integral_sub intervalIntegrable_const
          (((continuous_pow 2).div_const 2).intervalIntegrable 0 1),
        intervalIntegral.integral_const, intervalIntegral.integral_div, integral_pow]
      norm_num
    · filter_upwards [re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
        (hi := fun _ => 1) fun _ => uniform01.measure_compl_Icc] with θ hθ
      exact htt i (θ i) (hθ i)
  rw [Fin.sum_univ_two, hrev 0, hrev 1]
  ring

/-- The first-price transfers have `t̄ᵢ(a) = -a ⋅ a/2 = -a²/2` on `[0, 1]` (MWG, p. 868). -/
theorem firstPriceT_interim (i : Fin 2) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    interimTransfer unif2 firstPriceT i a = -(a ^ 2 / 2) := by
  have hm : Measurable fun θ => firstPriceT θ i := by
    fin_cases i
    · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
    · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
  unfold interimTransfer
  rw [re_unif2_update (G := fun θ => firstPriceT θ i) hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, firstPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(a * (if x ≤ a then (1 : ℝ) else 0) / 2) =
        if x ≤ a then -(a / 2) else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_le ha]; simp; ring
  · simp only [Fin.mk_one, re_update_vec1, firstPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(a * (if x < a then (1 : ℝ) else 0) / 2) =
        if x < a then -(a / 2) else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_lt ha]; simp; ring

/-- The second-price transfers have `t̄ᵢ(a) = -∫_0^a x dx = -a²/2` on `[0, 1]`. -/
theorem secondPriceT_interim (i : Fin 2) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    interimTransfer unif2 secondPriceT i a = -(a ^ 2 / 2) := by
  have hm : Measurable fun θ => secondPriceT θ i := by
    fin_cases i
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 1)).neg
  unfold interimTransfer
  rw [re_unif2_update (G := fun θ => secondPriceT θ i) hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0, secondPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(x * (if x ≤ a then (1 : ℝ) else 0)) =
        if x ≤ a then -x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_le ha, intervalIntegral.integral_neg, integral_id]; ring
  · simp only [Fin.mk_one, re_update_vec1, secondPriceT, twoY, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have e : ∀ x : ℝ, -(x * (if x < a then (1 : ℝ) else 0)) =
        if x < a then -x else 0 := fun x => by split_ifs <;> ring
    simp only [e]
    rw [re_integral_ite_lt ha, intervalIntegral.integral_neg, integral_id]; ring

/-- **Exercise 23.D.3** (MWG, p. 921), with Examples 23.B.5, 23.B.6 and the remark on p. 891. With
two buyers whose valuations are independent and uniform on `[0, 1]`, the social choice function
(23.B.9)-(23.B.14) implemented by the first-price auction equilibrium `bᵢ = θᵢ/2` and the
second-price auction social choice function are both Bayesian incentive compatible, have the same
allocation `y` (the higher valuation wins), give a zero-valuation buyer `Uᵢ(0) = 0`, and both
yield expected revenue `1/3`; Proposition 23.D.3 applies to them. -/
theorem exercise_23_D_3 :
    BayesianICOn unif2 allocV twoY firstPriceT (fun _ => 0) (fun _ => 1) ∧
      BayesianICOn unif2 allocV twoY secondPriceT (fun _ => 0) (fun _ => 1) ∧
      (∀ i, interimU unif2 allocV twoY firstPriceT i 0 = 0) ∧
      (∀ i, interimU unif2 allocV twoY secondPriceT i 0 = 0) ∧
      ∑ i, ∫ θ, -firstPriceT θ i ∂unif2 = 1 / 3 ∧ ∑ i, ∫ θ, -secondPriceT θ i ∂unif2 = 1 / 3 := by
  have bd : ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, |firstPriceT θ i| ≤ 1) ∧ ∀ i, |secondPriceT θ i| ≤ 1 := by
    intro θ hθ
    obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
    obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp only [firstPriceT, secondPriceT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;>
      constructor <;> nlinarith
  have hfm : ∀ i, Measurable fun θ => firstPriceT θ i := by
    intro i; fin_cases i
    · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
    · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
  have hsm : ∀ i, Measurable fun θ => secondPriceT θ i := by
    intro i; fin_cases i
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 1)).neg
  obtain ⟨-, h1, h2, h3⟩ := re_twoY_bic hfm (fun θ hθ => (bd θ hθ).1) 0
    fun i a ha => (firstPriceT_interim i ha).trans (by ring)
  obtain ⟨-, h4, h5, h6⟩ := re_twoY_bic hsm (fun θ hθ => (bd θ hθ).2) 0
    fun i a ha => (secondPriceT_interim i ha).trans (by ring)
  exact ⟨h1, h4, h2, h5, h3.trans (by norm_num), h6.trans (by norm_num)⟩

/-- Measurability and bounds of the first- and second-price transfers on `[0, 1]²`. -/
theorem re_price_facts :
    (∀ i, Measurable fun θ => firstPriceT θ i) ∧ (∀ i, Measurable fun θ => secondPriceT θ i) ∧
      ∀ θ : Fin 2 → ℝ, (∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) →
        (∀ i, |firstPriceT θ i| ≤ 1) ∧ ∀ i, |secondPriceT θ i| ≤ 1 := by
  refine ⟨fun i => ?_, fun i => ?_, fun θ hθ => ?_⟩
  · fin_cases i
    · exact (((measurable_pi_apply 0).mul (measurable_twoY 0)).div_const 2).neg
    · exact (((measurable_pi_apply 1).mul (measurable_twoY 1)).div_const 2).neg
  · fin_cases i
    · exact ((measurable_pi_apply 1).mul (measurable_twoY 0)).neg
    · exact ((measurable_pi_apply 0).mul (measurable_twoY 1)).neg
  · obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
    obtain ⟨a0, b0⟩ := hθ 0
    obtain ⟨a1, b1⟩ := hθ 1
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp only [firstPriceT, secondPriceT, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_le] <;>
      constructor <;> nlinarith

/-- **Exercise 23.D.3** via **Proposition 23.D.3** (MWG, pp. 890-891, 921): the first-price and
second-price social choice functions of Examples 23.B.5-23.B.6 satisfy all hypotheses of
`proposition_23_D_3`, which gives equal expected payments buyer by buyer (a proved instance of
the revenue equivalence theorem's hypotheses). -/
theorem exercise_23_D_3_revenue_equivalence :
    ∀ i, ∫ θ, -firstPriceT θ i ∂unif2 = ∫ θ, -secondPriceT θ i ∂unif2 := by
  have := uniform01.isProbabilityMeasure
  obtain ⟨hfm, hsm, bd⟩ := re_price_facts
  obtain ⟨hi1, hb1, hu1, -⟩ := re_twoY_bic hfm (fun θ hθ => (bd θ hθ).1) 0
    fun i a ha => (firstPriceT_interim i ha).trans (by ring)
  obtain ⟨hi2, hb2, hu2, -⟩ := re_twoY_bic hsm (fun θ hθ => (bd θ hθ).2) 0
    fun i a ha => (secondPriceT_interim i ha).trans (by ring)
  exact (proposition_23_D_3 (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) (fun _ => uniform01.measure_compl_Icc) hi1 hi2
    (fun i => (re_unif2_integrable (hfm i) 1 fun θ hθ => (bd θ hθ).1 i).1)
    (fun i => (re_unif2_integrable (hsm i) 1 fun θ hθ => (bd θ hθ).2 i).1) hb1 hb2
    fun i => by rw [hu1 i, hu2 i]).1

/-- Non-vacuity of (23.D.14)-(23.D.16): the first-price social choice function with two buyers
uniform on `[0, 1]` satisfies all their hypotheses (here `Jᵢ(θ) = 2θ - 1` on `[0, 1]`). -/
theorem eq_23_D_16_instance :
    InterimIntegrable (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure) allocV twoY
      firstPriceT (fun i => ((fun _ => uniform01) i).lo) (fun i => ((fun _ => uniform01) i).hi) ∧
    BayesianICOn (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure) allocV twoY
      firstPriceT (fun i => ((fun _ => uniform01) i).lo) (fun i => ((fun _ => uniform01) i).hi) ∧
    (∀ i, Integrable (fun θ => firstPriceT θ i)
      (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure)) ∧
    ∀ i, Integrable (fun θ => twoY θ i * ((fun _ => uniform01) i).virtualValue (θ i))
      (Measure.pi fun j : Fin 2 => ((fun _ => uniform01) j).measure) := by
  obtain ⟨hfm, -, bd⟩ := re_price_facts
  obtain ⟨hi1, hb1, -, -⟩ := re_twoY_bic hfm (fun θ hθ => (bd θ hθ).1) 0
    fun i a ha => (firstPriceT_interim i ha).trans (by ring)
  refine ⟨hi1, hb1, fun i => (re_unif2_integrable (hfm i) 1 fun θ hθ => (bd θ hθ).1 i).1,
    fun i => ?_⟩
  have hJ : Measurable uniform01.virtualValue :=
    measurable_id.sub (((continuous_const.sub uniform01.continuous_cdf).measurable).div
      uniform01.measurable_dens)
  refine (re_unif2_integrable ((measurable_twoY i).mul (hJ.comp (measurable_pi_apply i))) 1
    fun θ hθ => ?_).1
  have hc := uniform01_cdf (hθ i)
  have hd : uniform01.dens (θ i) = 1 := by
    change (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 - 0 : ℝ)⁻¹) (θ i) = 1
    rw [Set.indicator_of_mem (hθ i)]; norm_num
  obtain ⟨-, h2, h3, h4, h5⟩ := twoY_props θ
  have hy : |twoY θ i| ≤ 1 :=
    (Fin.forall_fin_two (p := fun i => |twoY θ i| ≤ 1)).2
      ⟨abs_le.2 ⟨by linarith, h5⟩, abs_le.2 ⟨by linarith, h3⟩⟩ i
  obtain ⟨a, b⟩ := hθ i
  change |twoY θ i * uniform01.virtualValue (θ i)| ≤ 1
  rw [TypeDensity.virtualValue, hc, hd, div_one, abs_mul]
  exact (mul_le_mul hy (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

/-! ### Exercise 23.D.2: the expected externality mechanism for bilateral trade -/

/-- `∫_0^1 1{a ≤ x} g(x) dx = ∫_a^1 g` for `a ∈ [0, 1]`. -/
theorem re_integral_ite_ge {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (if a ≤ x then g x else 0) = ∫ x in a..1, g x := by
  rw [← re_integral_ite_gt ha g]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := a))] with x hx _
  have hx' : x ≠ a := hx
  by_cases h : a < x
  · simp [h, h.le]
  · have : ¬a ≤ x := fun h' => h (lt_of_le_of_ne h' hx'.symm)
    simp [h, this]

/-- Bilateral trade in the quasilinear form of Section 23.D (Example 23.B.4): `k = true` means
trade; the seller (agent `0`) values the good at `θ₀` and the buyer (agent `1`) at `θ₁`, so
`v₀(k, θ₀) = θ₀` if no trade and `v₁(k, θ₁) = θ₁` if trade (zero otherwise). -/
def bilatV : Fin 2 → Bool → ℝ → ℝ :=
  fun i k x => if k then (if i = 0 then 0 else x) else (if i = 0 then x else 0)

/-- The efficient trading rule: trade iff `θ₀ < θ₁`. -/
noncomputable def bilatK (θ : Fin 2 → ℝ) : Bool := decide (θ 0 < θ 1)

/-- The trading rule `bilatK` satisfies (23.D.6). -/
theorem bilatK_efficient : EfficientProject (Θ := fun _ => ℝ) bilatV bilatK := by
  intro θ k'
  simp only [Fin.sum_univ_two, bilatV, bilatK]
  by_cases h : θ 0 < θ 1
  · cases k'
    · simp [h]; linarith
    · simp [h]
  · cases k'
    · simp [h]
    · simp [h]; linarith [not_lt.1 h]

/-- The integrand of `ξᵢ` is a function of the profile `(a, θ₋ᵢ)`. -/
theorem bilat_xi_integrand (θ' : Fin 2 → ℝ) (i : Fin 2) (a : ℝ) :
    ∑ j ∈ Finset.univ.erase i, bilatV j (bilatK (update θ' i a)) (θ' j) =
      (fun σ : Fin 2 → ℝ => ∑ j ∈ Finset.univ.erase i, bilatV j (bilatK σ) (σ j))
        (update θ' i a) :=
  Finset.sum_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Exercise 23.D.2(a)**, the expected externalities (MWG, p. 921). With `θ₀, θ₁` independent
and uniform on `[0, 1]`, `ξ₀(a) = E[θ₁ 1{a < θ₁}] = (1 - a²)/2` and
`ξ₁(b) = E[θ₀ 1{b ≤ θ₀}] = (1 - b²)/2` for `a, b ∈ [0, 1]`. -/
theorem exercise_23_D_2a_xi (i : Fin 2) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    expectedExternality unif2 bilatV bilatK i a = (1 - a ^ 2) / 2 := by
  have hm : Measurable fun σ : Fin 2 → ℝ =>
      ∑ j ∈ Finset.univ.erase i, bilatV j (bilatK σ) (σ j) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have hs : MeasurableSet {σ : Fin 2 → ℝ | bilatK σ = true} := by
      simp only [bilatK, decide_eq_true_eq]
      exact measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 1)
    have e : (fun σ : Fin 2 → ℝ => bilatV j (bilatK σ) (σ j)) = fun σ =>
        if bilatK σ = true then (if j = 0 then 0 else σ j) else (if j = 0 then σ j else 0) := by
      funext σ; simp only [bilatV]
    rw [e]
    exact Measurable.ite hs (by split_ifs <;> fun_prop) (by split_ifs <;> fun_prop)
  unfold expectedExternality
  simp only [bilat_xi_integrand]
  rw [re_unif2_update hm i a]
  fin_cases i
  · simp only [Fin.zero_eta, re_update_vec0]
    have e : ∀ x : ℝ, ∑ j ∈ Finset.univ.erase (0 : Fin 2),
        bilatV j (bilatK ![a, x]) (![a, x] j) = if a < x then x else 0 := by
      intro x
      rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide, Finset.sum_singleton]
      by_cases h : a < x <;> simp [bilatV, bilatK, h]
    simp only [e]
    rw [re_integral_ite_gt ha, integral_id]; ring
  · simp only [Fin.mk_one, re_update_vec1]
    have e : ∀ x : ℝ, ∑ j ∈ Finset.univ.erase (1 : Fin 2),
        bilatV j (bilatK ![x, a]) (![x, a] j) = if a ≤ x then x else 0 := by
      intro x
      rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide, Finset.sum_singleton]
      by_cases h : x < a
      · simp [bilatV, bilatK, h, not_le.2 h]
      · simp [bilatV, bilatK, h, not_lt.1 h]
    simp only [e]
    rw [re_integral_ite_ge ha, integral_id]; ring

/-- **Exercise 23.D.2(a)** (MWG, p. 921). The expected externality transfers (23.D.8)-(23.D.9)
for bilateral trade with types uniform on `[0, 1]` are `t₀(θ) = (θ₁² - θ₀²)/2` and
`t₁(θ) = (θ₀² - θ₁²)/2` on `[0, 1]²`. -/
theorem exercise_23_D_2a {θ : Fin 2 → ℝ} (hθ : ∀ j, θ j ∈ Set.Icc (0 : ℝ) 1) :
    agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ 0 = (θ 1 ^ 2 - θ 0 ^ 2) / 2 ∧
      agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ 1 =
        (θ 0 ^ 2 - θ 1 ^ 2) / 2 := by
  simp only [agvTransfer, agvH, Fintype.card_fin]
  rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide,
    show Finset.univ.erase (1 : Fin 2) = {0} by decide, Finset.sum_singleton,
    Finset.sum_singleton, exercise_23_D_2a_xi 0 (hθ 0), exercise_23_D_2a_xi 1 (hθ 1)]
  constructor <;> ring

/-- **Exercise 23.D.2(b)** (MWG, p. 921). Truth telling is a Bayesian Nash equilibrium of the
expected externality mechanism for bilateral trade with types independent and uniform on
`[0, 1]` (the mechanism is also budget balanced and its trading rule is ex post efficient).
Types are real numbers here, as in Section 23.D; outside `[0, 1]` the prior gives no mass. -/
theorem exercise_23_D_2b (m : Fin 2 → ℝ) :
    BayesianIC (indepBeliefs unif2) (qlU (Θ := fun _ => ℝ) bilatV m)
        (fun θ => (bilatK θ, agvTransfer unif2 bilatV bilatK (agvH unif2 bilatV bilatK) θ)) ∧
      BudgetBalanced (Θ := fun _ => ℝ) (agvTransfer unif2 bilatV bilatK
        (agvH unif2 bilatV bilatK)) := by
  have := uniform01.isProbabilityMeasure
  have hsupp : ∀ _ : Fin 2, uniform01.measure (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    fun _ => uniform01.measure_compl_Icc
  have hae := re_ae_mem (fun _ : Fin 2 => uniform01.measure) (lo := fun _ => 0)
    (hi := fun _ => 1) hsupp
  refine ⟨agv_bayesianIC unif2 m bilatK_efficient (agvH_indepOwn _ _ _) ?_ ?_,
    agv_budgetBalanced (by simp) _ _ _⟩
  · intro i a θi j
    have hs : MeasurableSet {θ' : Fin 2 → ℝ | bilatK (update θ' i a) = true} := by
      simp only [bilatK, decide_eq_true_eq]
      exact measurableSet_lt (by fun_prop) (by fun_prop)
    have e : (fun θ' : Fin 2 → ℝ => bilatV j (bilatK (update θ' i a)) (update θ' i θi j)) =
        fun θ' => if bilatK (update θ' i a) = true then (if j = 0 then 0 else update θ' i θi j)
          else (if j = 0 then update θ' i θi j else 0) := by
      funext θ'; simp only [bilatV]
    rw [e]
    refine Integrable.of_bound (Measurable.ite hs (by split_ifs <;> fun_prop)
      (by split_ifs <;> fun_prop)).aestronglyMeasurable (|θi| + 1) ?_
    filter_upwards [hae] with θ' hθ'
    have hb : |update θ' i θi j| ≤ |θi| + 1 := by
      by_cases hj : j = i
      · subst hj; simp
      · rw [update_of_ne hj, abs_le]
        constructor <;> linarith [(hθ' j).1, (hθ' j).2, abs_nonneg θi]
    rw [Real.norm_eq_abs]
    split_ifs <;> simp [hb] <;> linarith [abs_nonneg θi]
  · intro i
    have hxi : ∀ j, Integrable (fun θ : Fin 2 → ℝ =>
        expectedExternality unif2 bilatV bilatK j (θ j)) unif2 := by
      intro j
      refine Integrable.congr (f := fun θ : Fin 2 → ℝ => (1 - θ j ^ 2) / 2)
        (Integrable.of_bound ((measurable_const.sub ((measurable_pi_apply j).pow_const 2)).div_const
          2).aestronglyMeasurable 1 ?_) ?_
      · filter_upwards [hae] with θ hθ
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [(hθ j).1, (hθ j).2]
      · filter_upwards [hae] with θ hθ
        exact (exercise_23_D_2a_xi j (hθ j)).symm
    exact (integrable_finsetSum _ fun j _ => hxi j).const_mul _

end MWG.MechanismDesign
