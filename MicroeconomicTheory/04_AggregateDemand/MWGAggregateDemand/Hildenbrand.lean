/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.LShaped
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hildenbrand's law of demand

MWG, Section 4.C, Proposition 4.C.4 (p. 113), and Exercises 4.C.7, 4.C.10 (p. 124).

A continuum of consumers with identical preferences and demand `x̃(p, w)`, wealth uniformly
distributed on `[0, w̄]`; aggregate demand `x(p) = ∫₀^w̄ x̃(p, w) dw` (`hildenbrandDemand`).

* `young_square`: if `c, d ≥ 0` on `(0, a]` and `c(w) ≤ w'` implies `w ≤ d(w')`, then
  `a² ≤ ∫₀^a c + ∫₀^a d` (a Young-type inequality; the square `(0, a]²` is covered by
  `{w' < c(w)}` and `{w ≤ d(w')}`).
* `proposition_4_C_4`: the aggregate demand satisfies the inequality of the ULD,
  `(p' - p)·[x(p') - x(p)] ≤ 0`, for every individual demand satisfying Walras' law and the
  weak axiom (any preference-generated demand), with no differentiability. With
  `c(w) = p'·x̃(p, w)`, `d(w) = p·x̃(p', w)`, the left side is `w̄² - ∫c - ∫d`.
* `proposition_4_C_4_strict_counterexample`: the strict part of the ULD (Definition 4.C.2)
  fails in general: for an L-shaped preference with a bent expansion path the aggregate
  demands at two price vectors differ while `(p' - p)·[x(p') - x(p)] = 0`. The book's proof
  needs the extra hypothesis that the Slutsky matrix is negative definite off the price ray
  (correction 4); under it the strict part is `proposition_4_C_4_strict` in
  `HildenbrandStrict`.
* `hildenbrand_mean_income_effect`: the book's key step,
  `∫₀^w̄ (v·D_w x̃)(v·x̃) dw = ½ (v·x̃(p, w̄))²` when `x̃(p, 0) = 0`.
* `exercise_4_C_10`: the covariance matrix `C`, adapted to the continuum of consumers, is
  positive semidefinite: `v·C v = (v·x̃(p, w̄) - 2 v·x̄)²/(2 w̄)`.
* `exercise_4_C_7_unimodal`: for a unimodal (tent) wealth density the conclusion fails.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand MeasureTheory
open scoped ENNReal

variable {L : ℕ}

/-- **Proposition 4.C.4** (MWG, p. 113), the measure-theoretic core (a Young-type
inequality). Let `c, d` be measurable, nonnegative and integrable on `(0, a]`, and suppose that
`c(w) ≤ w'` implies `w ≤ d(w')` for `w, w' ∈ (0, a]`. Then `a² ≤ ∫₀^a c + ∫₀^a d`. -/
theorem young_square {a : ℝ} (ha : 0 ≤ a) {c d : ℝ → ℝ} (hc : Measurable c) (hd : Measurable d)
    (hc0 : ∀ w ∈ Set.Ioc 0 a, 0 ≤ c w) (hd0 : ∀ w ∈ Set.Ioc 0 a, 0 ≤ d w)
    (hci : IntegrableOn c (Set.Ioc 0 a)) (hdi : IntegrableOn d (Set.Ioc 0 a))
    (h : ∀ w ∈ Set.Ioc 0 a, ∀ w' ∈ Set.Ioc 0 a, c w ≤ w' → w ≤ d w') :
    a ^ 2 ≤ (∫ w in Set.Ioc 0 a, c w) + ∫ w in Set.Ioc 0 a, d w := by
  set μ := volume.restrict (Set.Ioc (0 : ℝ) a) with hμ
  set F : ℝ → ℝ → ℝ≥0∞ := fun x y => (Set.Iio (c x)).indicator 1 y with hFdef
  set G : ℝ → ℝ → ℝ≥0∞ := fun x y => (Set.Iic (d y)).indicator 1 x with hGdef
  have hFm : Measurable (Function.uncurry F) := by
    have : Function.uncurry F = {q : ℝ × ℝ | q.2 < c q.1}.indicator 1 := by
      funext q
      simp [F, Set.indicator, Function.uncurry]
    rw [this]
    exact measurable_one.indicator (measurableSet_lt measurable_snd (hc.comp measurable_fst))
  have hGm : Measurable (Function.uncurry G) := by
    have : Function.uncurry G = {q : ℝ × ℝ | q.1 ≤ d q.2}.indicator 1 := by
      funext q
      simp [G, Set.indicator, Function.uncurry]
    rw [this]
    exact measurable_one.indicator (measurableSet_le measurable_fst (hd.comp measurable_snd))
  have hcover : ∀ x ∈ Set.Ioc 0 a, ∀ y ∈ Set.Ioc 0 a, (1 : ℝ≥0∞) ≤ F x y + G x y := by
    intro x hx y hy
    by_cases hlt : y < c x
    · simp [F, hlt]
    · push Not at hlt
      have := h x hx y hy hlt
      simp [G, this]
  have hF : ∀ x, ∫⁻ y, F x y ∂μ ≤ ENNReal.ofReal (c x) := by
    intro x
    simp only [F]
    rw [lintegral_indicator_one measurableSet_Iio, hμ, Measure.restrict_apply measurableSet_Iio]
    calc volume (Set.Iio (c x) ∩ Set.Ioc 0 a) ≤ volume (Set.Ioo 0 (c x)) :=
          measure_mono fun y hy => ⟨hy.2.1, hy.1⟩
      _ = ENNReal.ofReal (c x) := by rw [Real.volume_Ioo, sub_zero]
  have hG : ∀ y, ∫⁻ x, G x y ∂μ ≤ ENNReal.ofReal (d y) := by
    intro y
    simp only [G]
    rw [lintegral_indicator_one measurableSet_Iic, hμ, Measure.restrict_apply measurableSet_Iic]
    calc volume (Set.Iic (d y) ∩ Set.Ioc 0 a) ≤ volume (Set.Ioc 0 (d y)) :=
          measure_mono fun x hx => ⟨hx.2.1, hx.1⟩
      _ = ENNReal.ofReal (d y) := by rw [Real.volume_Ioc, sub_zero]
  have hμuniv : μ Set.univ = ENNReal.ofReal a := by
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero]
  have key : ENNReal.ofReal a * ENNReal.ofReal a ≤
      ∫⁻ x, ENNReal.ofReal (c x) ∂μ + ∫⁻ y, ENNReal.ofReal (d y) ∂μ := by
    calc ENNReal.ofReal a * ENNReal.ofReal a = ∫⁻ _x, ∫⁻ _y, (1 : ℝ≥0∞) ∂μ ∂μ := by
          simp [hμuniv]
      _ ≤ ∫⁻ x, ∫⁻ y, (F x y + G x y) ∂μ ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
          exact hcover x hx y hy
      _ = ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ + ∫⁻ x, ∫⁻ y, G x y ∂μ ∂μ := by
          have h1 : Measurable fun x => ∫⁻ y, F x y ∂μ := hFm.lintegral_prod_right'
          rw [← lintegral_add_left h1]
          congr 1
          funext x
          exact lintegral_add_left (hFm.of_uncurry_left) _
      _ = ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ + ∫⁻ y, ∫⁻ x, G x y ∂μ ∂μ := by
          rw [lintegral_lintegral_swap hGm.aemeasurable]
      _ ≤ ∫⁻ x, ENNReal.ofReal (c x) ∂μ + ∫⁻ y, ENNReal.ofReal (d y) ∂μ :=
          add_le_add (lintegral_mono hF) (lintegral_mono hG)
  have hcnn : 0 ≤ᵐ[μ] c :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hc0)
  have hdnn : 0 ≤ᵐ[μ] d :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hd0)
  rw [← ofReal_integral_eq_lintegral_ofReal hci hcnn,
    ← ofReal_integral_eq_lintegral_ofReal hdi hdnn,
    ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (integral_nonneg_of_ae hcnn)
      (integral_nonneg_of_ae hdnn)] at key
  rw [sq]
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (integral_nonneg_of_ae hcnn)
    (integral_nonneg_of_ae hdnn))).mp key

/-- **Proposition 4.C.4** (MWG, p. 113). Aggregate demand of a continuum of consumers with the
common demand function `x̃` and wealth uniformly distributed on `[0, w̄]`:
`x(p) = ∫₀^w̄ x̃(p, w) dw` (the book's normalization; the average divides by `w̄`). -/
noncomputable def hildenbrandDemand (x : DemandFunction L) (wb : ℝ) (p : Fin L → ℝ) :
    Fin L → ℝ :=
  fun l => ∫ w in Set.Ioc 0 wb, x p w l

/-- Integrating a price-weighted bundle: `∫ q·x̃(p, w) dw = q·x(p)`. -/
theorem integral_dot_hildenbrand {x : DemandFunction L} {p : Fin L → ℝ} {wb : ℝ}
    (hint : ∀ l, IntegrableOn (fun w => x p w l) (Set.Ioc 0 wb)) (q : Fin L → ℝ) :
    ∫ w in Set.Ioc 0 wb, q ⬝ᵥ x p w = q ⬝ᵥ hildenbrandDemand x wb p := by
  simp only [dotProduct, hildenbrandDemand]
  rw [integral_finsetSum _ fun l _ => (hint l).const_mul (q l)]
  exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _

/-- **Proposition 4.C.4** (MWG, p. 113). Let `x̃` satisfy Walras' law and the weak axiom and take
values in `ℝ^L_+` (as any demand function generated by a locally nonsatiated preference does),
with `w ↦ x̃(p, w)` measurable and integrable on `(0, w̄]`. Then the aggregate demand
`x(p) = ∫₀^w̄ x̃(p, w) dw` satisfies `(p' - p)·[x(p') - x(p)] ≤ 0` for all `p, p' ≫ 0`. No
differentiability is used. (The strict part of the ULD can fail:
`proposition_4_C_4_strict_counterexample`.) -/
theorem proposition_4_C_4 {x : DemandFunction L} (hWA : WeakAxiom x) (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) {wb : ℝ} (hwb : 0 ≤ wb)
    (hmeas : ∀ p, StrictlyPositive p → ∀ l, Measurable fun w => x p w l)
    (hint : ∀ p, StrictlyPositive p → ∀ l, IntegrableOn (fun w => x p w l) (Set.Ioc 0 wb))
    {p p' : Fin L → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') :
    (p' - p) ⬝ᵥ (hildenbrandDemand x wb p' - hildenbrandDemand x wb p) ≤ 0 := by
  have hm : ∀ q r, StrictlyPositive r → Measurable fun w => q ⬝ᵥ x r w := by
    intro q r hr
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ => (hmeas r hr l).const_mul (q l)
  have hi : ∀ q r, StrictlyPositive r → IntegrableOn (fun w => q ⬝ᵥ x r w) (Set.Ioc 0 wb) := by
    intro q r hr
    simp only [dotProduct]
    exact integrable_finsetSum _ fun l _ => (hint r hr l).const_mul (q l)
  have hnn : ∀ q r, StrictlyPositive q → StrictlyPositive r → ∀ w ∈ Set.Ioc 0 wb,
      0 ≤ q ⬝ᵥ x r w := fun q r hq hr w hw =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hq l).le (hX r w ⟨hr, hw.1⟩ l)
  have hrp : ∀ w ∈ Set.Ioc 0 wb, ∀ w' ∈ Set.Ioc 0 wb,
      p' ⬝ᵥ x p w ≤ w' → w ≤ p ⬝ᵥ x p' w' := by
    intro w hw w' hw' hle
    by_cases heq : x p w = x p' w'
    · rw [← heq, hW p w ⟨hp, hw.1⟩]
    · exact (hWA p' w' p w ⟨hp', hw'.1⟩ ⟨hp, hw.1⟩ hle heq).le
  have hyoung := young_square hwb (hm p' p hp) (hm p p' hp') (hnn p' p hp' hp) (hnn p p' hp hp')
    (hi p' p hp) (hi p p' hp') hrp
  have hwal : ∀ r, StrictlyPositive r → ∫ w in Set.Ioc 0 wb, r ⬝ᵥ x r w = wb ^ 2 / 2 := by
    intro r hr
    rw [setIntegral_congr_fun measurableSet_Ioc (fun w hw => hW r w ⟨hr, hw.1⟩),
      ← intervalIntegral.integral_of_le hwb, integral_id]
    ring
  have hexp : (p' - p) ⬝ᵥ (hildenbrandDemand x wb p' - hildenbrandDemand x wb p) =
      p' ⬝ᵥ hildenbrandDemand x wb p' - p' ⬝ᵥ hildenbrandDemand x wb p -
        p ⬝ᵥ hildenbrandDemand x wb p' + p ⬝ᵥ hildenbrandDemand x wb p := by
    simp only [sub_dotProduct, dotProduct_sub]
    ring
  rw [hexp, ← integral_dot_hildenbrand (hint p' hp'), ← integral_dot_hildenbrand (hint p hp),
    ← integral_dot_hildenbrand (hint p' hp'), ← integral_dot_hildenbrand (hint p hp),
    hwal p' hp', hwal p hp]
  linarith

/-- **Proposition 4.C.4** (MWG, p. 113), the key step of the book's proof (the mean income
effect). If `φ(w) = v·x̃(p, w)` has derivative `φ'(w) = v·D_w x̃(p, w)` (continuous) on
`[0, w̄]` and `x̃(p, 0) = 0`, then `∫₀^w̄ (v·D_w x̃)(v·x̃) dw = ½ (v·x̃(p, w̄))² ≥ 0`. -/
theorem hildenbrand_mean_income_effect {φ φ' : ℝ → ℝ} {wb : ℝ}
    (hφ : ∀ w ∈ Set.uIcc 0 wb, HasDerivAt φ (φ' w) w)
    (hcont : ContinuousOn φ' (Set.uIcc 0 wb)) (h0 : φ 0 = 0) :
    ∫ w in (0 : ℝ)..wb, φ' w * φ w = φ wb ^ 2 / 2 := by
  have hder : ∀ w ∈ Set.uIcc 0 wb, HasDerivAt (fun t => φ t ^ 2 / 2) (φ' w * φ w) w := by
    intro w hw
    have := ((hφ w hw).pow 2).div_const 2
    convert this using 1
    push_cast
    ring
  have hφc : ContinuousOn φ (Set.uIcc 0 wb) :=
    fun w hw => (hφ w hw).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.mul hφc).intervalIntegrable]
  simp [h0]

/-- `∫ₐᵇ (c w + e) dw`. -/
theorem integral_affine (c e a b : ℝ) :
    ∫ w in a..b, (c * w + e) = c * ((b ^ 2 - a ^ 2) / 2) + e * (b - a) := by
  have h1 : IntervalIntegrable (fun w : ℝ => c * w) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Exercise 4.C.10** (MWG, p. 124). The matrix `C` of (4.C.8) adapted to the continuum of
consumers of Proposition 4.C.4: consumer `w ∈ [0, w̄]` (density `1/w̄`) holds the share
`α(w) = w/W` of mean wealth `W = w̄/2`. For a direction `v`, let `φ(w) = v·x̃(p, w)` with
derivative `ψ(w) = v·D_w x̃(p, w)`, `x̃(p, 0) = 0`, `b = v·x̄` the per-capita aggregate
(`x̄ = (1/w̄) ∫ x̃`), and `β` the aggregate wealth effect in direction `v` (any value). Then
`v·C v = (1/w̄) ∫₀^w̄ α(w) [ψ(w) - β][φ(w)/α(w) - b] dw = (φ(w̄) - 2b)²/(2 w̄) ≥ 0`, so `C` is
positive semidefinite. -/
theorem exercise_4_C_10 {φ ψ : ℝ → ℝ} {wb β : ℝ} (hwb : 0 < wb)
    (hφ : ∀ w ∈ Set.uIcc 0 wb, HasDerivAt φ (ψ w) w) (hψ : ContinuousOn ψ (Set.uIcc 0 wb))
    (h0 : φ 0 = 0) :
    (1 / wb) * ∫ w in (0 : ℝ)..wb, (ψ w - β) *
        (φ w - (2 * w / wb) * ((1 / wb) * ∫ t in (0 : ℝ)..wb, φ t)) =
      (φ wb - 2 * ((1 / wb) * ∫ t in (0 : ℝ)..wb, φ t)) ^ 2 / (2 * wb) ∧
    0 ≤ (1 / wb) * ∫ w in (0 : ℝ)..wb, (ψ w - β) *
        (φ w - (2 * w / wb) * ((1 / wb) * ∫ t in (0 : ℝ)..wb, φ t)) := by
  set Φ := ∫ t in (0 : ℝ)..wb, φ t with hΦ
  set b := (1 / wb) * Φ with hb
  have hφc : ContinuousOn φ (Set.uIcc 0 wb) :=
    fun w hw => (hφ w hw).continuousAt.continuousWithinAt
  have hI1 := hildenbrand_mean_income_effect hφ hψ h0
  -- `∫ w ψ(w) = w̄ φ(w̄) - ∫ φ`
  have hder : ∀ w ∈ Set.uIcc 0 wb, HasDerivAt (fun t => t * φ t) (φ w + w * ψ w) w := by
    intro w hw
    have := (hasDerivAt_id' w).mul (hφ w hw)
    convert this using 1
    ring
  have hwψ : ContinuousOn (fun w => w * ψ w) (Set.uIcc 0 wb) := continuousOn_id.mul hψ
  have hI2' := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hφc.add hwψ).intervalIntegrable
  rw [intervalIntegral.integral_add hφc.intervalIntegrable hwψ.intervalIntegrable] at hI2'
  simp only [zero_mul, sub_zero] at hI2'
  have hI2 : ∫ w in (0 : ℝ)..wb, w * ψ w = wb * φ wb - Φ := by rw [hΦ]; linarith
  have hexp : ∀ w, (ψ w - β) * (φ w - (2 * w / wb) * b) =
      ψ w * φ w - (2 * b / wb) * (w * ψ w) - β * φ w + (2 * β * b / wb) * (w + 0) := by
    intro w
    ring
  have hψφ : ContinuousOn (fun w => ψ w * φ w) (Set.uIcc 0 wb) := hψ.mul hφc
  have hint : ∫ w in (0 : ℝ)..wb, (ψ w - β) * (φ w - (2 * w / wb) * b) =
      φ wb ^ 2 / 2 - (2 * b / wb) * (wb * φ wb - Φ) - β * Φ + (2 * β * b / wb) * (wb ^ 2 / 2) := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hI1, hI2, ← hΦ]
    · have := integral_affine 1 0 0 wb
      simp only [one_mul] at this
      rw [this]
      ring
    · exact hψφ.intervalIntegrable
    · exact (hwψ.intervalIntegrable).const_mul _
    · exact (hψφ.intervalIntegrable).sub ((hwψ.intervalIntegrable).const_mul _)
    · exact (hφc.intervalIntegrable).const_mul _
    · exact (hψφ.intervalIntegrable.sub ((hwψ.intervalIntegrable).const_mul _)).sub
        ((hφc.intervalIntegrable).const_mul _)
    · exact ((continuous_id.add continuous_const).intervalIntegrable _ _).const_mul _
  have hval : (1 / wb) * ∫ w in (0 : ℝ)..wb, (ψ w - β) * (φ w - (2 * w / wb) * b) =
      (φ wb - 2 * b) ^ 2 / (2 * wb) := by
    rw [hint, hb]
    field_simp
    ring
  exact ⟨hval, hval ▸ div_nonneg (sq_nonneg _) (by linarith)⟩

/-! ### The strict ULD can fail -/

/-- The kink curve `φ(t) = max(t/3, t - 1)` of the counterexample. -/
noncomputable def hildKink (t : ℝ) : ℝ := max (t / 3) (t - 1)

theorem strictMono_hildKink : StrictMono hildKink := by
  have h1 : StrictMono fun t : ℝ => (1 / 3) * t + 0 := strictMono_affine (by norm_num)
  have h2 : StrictMono fun t : ℝ => 1 * t + (-1) := strictMono_affine one_pos
  have := strictMono_max_fun h1 h2
  convert this using 2 with t
  simp only [hildKink]
  ring_nf

/-- The L-shaped utility `min(max(x₁/3, x₁ - 1), x₂)`: expansion path along the ray of slope
`1/3` up to `(3/2, 1/2)`, then along a line of slope `1`. -/
noncomputable def hildU : (Fin 2 → ℝ) → ℝ := minUtility hildKink id

/-- `∫₀ᵇ f` for a continuous function that is affine on `[0, m]` and on `[m, b]`. -/
theorem integral_two_piece {f : ℝ → ℝ} (hf : Continuous f) {m b c₁ e₁ c₂ e₂ : ℝ} (hm : 0 ≤ m)
    (hmb : m ≤ b) (h1 : ∀ w ∈ Set.Icc 0 m, f w = c₁ * w + e₁)
    (h2 : ∀ w ∈ Set.Icc m b, f w = c₂ * w + e₂) :
    ∫ w in Set.Ioc 0 b, f w =
      (c₁ * (m ^ 2 / 2) + e₁ * m) + (c₂ * ((b ^ 2 - m ^ 2) / 2) + e₂ * (b - m)) := by
  rw [← intervalIntegral.integral_of_le (hm.trans hmb),
    ← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 m)
      (hf.intervalIntegrable m b),
    intervalIntegral.integral_congr (g := fun w => c₁ * w + e₁)
      (fun w hw => h1 w (by rwa [Set.uIcc_of_le hm] at hw)),
    intervalIntegral.integral_congr (g := fun w => c₂ * w + e₂)
      (fun w hw => h2 w (by rwa [Set.uIcc_of_le hmb] at hw)),
    integral_affine, integral_affine]
  ring

/-- **Proposition 4.C.4** (MWG, p. 113), correction: the strict part of the ULD fails in
general. Every consumer has the L-shaped utility `hildU` (single-valued demand satisfying the
weak axiom and Walras' law), wealth is uniform on `[0, 4]`, `p = (1, 1)` and
`p' = (13/10, 1/2)`. Then `x(p) = (11/2, 5/2)`, `x(p') = (21/4, 47/20)`: the aggregate demands
differ, but `(p' - p)·[x(p') - x(p)] = 0`. -/
theorem proposition_4_C_4_strict_counterexample {x : DemandFunction 2}
    (hx : ∀ p w, PWDomain p w → x p w ∈ walrasianDemand hildU p w) :
    hildenbrandDemand x 4 ![1, 1] = ![11 / 2, 5 / 2] ∧
      hildenbrandDemand x 4 ![13 / 10, 1 / 2] = ![21 / 4, 47 / 20] ∧
      (![13 / 10, 1 / 2] - ![1, 1]) ⬝ᵥ
          (hildenbrandDemand x 4 ![13 / 10, 1 / 2] - hildenbrandDemand x 4 ![1, 1]) = 0 ∧
      hildenbrandDemand x 4 ![13 / 10, 1 / 2] ≠ hildenbrandDemand x 4 ![1, 1] := by
  have hk := strictMono_hildKink
  have hid : StrictMono (id : ℝ → ℝ) := strictMono_id
  have hp : StrictlyPositive (![1, 1] : Fin 2 → ℝ) := by intro l; fin_cases l <;> simp
  have hp' : StrictlyPositive (![13 / 10, 1 / 2] : Fin 2 → ℝ) := by
    intro l; fin_cases l <;> norm_num
  have dem : ∀ (q : Fin 2 → ℝ) (v : ℝ) (y : Fin 2 → ℝ), StrictlyPositive q → 0 < v →
      0 ≤ y 0 → 0 ≤ y 1 → hildKink (y 0) = y 1 → q ⬝ᵥ y = v → x q v = y := by
    intro q v y hq hv hy0 hy1 hky hb
    have h := walrasianDemand_minUtility hk hid hq hy0 hy1 hky hb
    have := hx q v ⟨hq, hv⟩
    rw [hildU, h] at this
    exact this
  have hx0 : ∀ w, 0 < w →
      x ![1, 1] w = ![min (3 * w / 4) ((w + 1) / 2), max (w / 4) ((w - 1) / 2)] := by
    intro w hw
    apply dem _ _ _ hp hw
    · simp only [Matrix.cons_val_zero, le_min_iff]
      constructor <;> linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, le_max_iff]
      left; linarith
    · simp only [hildKink, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        min_def, max_def]
      split_ifs <;> linarith
    · simp only [dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, min_def, max_def]
      split_ifs <;> linarith
  have hx1 : ∀ w, 0 < w → x ![13 / 10, 1 / 2] w =
      ![min (15 * w / 22) ((10 * w + 5) / 18), max (5 * w / 22) ((10 * w - 13) / 18)] := by
    intro w hw
    apply dem _ _ _ hp' hw
    · simp only [Matrix.cons_val_zero, le_min_iff]
      constructor <;> linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, le_max_iff]
      left; linarith
    · simp only [hildKink, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        min_def, max_def]
      split_ifs <;> linarith
    · simp only [dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, min_def, max_def]
      split_ifs <;> linarith
  have hA : hildenbrandDemand x 4 ![1, 1] = ![11 / 2, 5 / 2] := by
    funext l
    fin_cases l
    · change ∫ w in Set.Ioc 0 4, x ![1, 1] w 0 = 11 / 2
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun w => min (3 * w / 4) ((w + 1) / 2))
        (fun w hw => by simp only [hx0 w hw.1, Matrix.cons_val_zero])]
      rw [integral_two_piece (m := 2) (c₁ := 3 / 4) (e₁ := 0) (c₂ := 1 / 2) (e₂ := 1 / 2)
        (by fun_prop) (by norm_num) (by norm_num)
        (fun w hw => by rw [min_eq_left (by linarith [hw.2])]; ring)
        (fun w hw => by rw [min_eq_right (by linarith [hw.1])]; ring)]
      norm_num
    · change ∫ w in Set.Ioc 0 4, x ![1, 1] w 1 = 5 / 2
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun w => max (w / 4) ((w - 1) / 2))
        (fun w hw => by simp only [hx0 w hw.1, Matrix.cons_val_one, Matrix.cons_val_fin_one])]
      rw [integral_two_piece (m := 2) (c₁ := 1 / 4) (e₁ := 0) (c₂ := 1 / 2) (e₂ := -1 / 2)
        (by fun_prop) (by norm_num) (by norm_num)
        (fun w hw => by rw [max_eq_left (by linarith [hw.2])]; ring)
        (fun w hw => by rw [max_eq_right (by linarith [hw.1])]; ring)]
      norm_num
  have hB : hildenbrandDemand x 4 ![13 / 10, 1 / 2] = ![21 / 4, 47 / 20] := by
    funext l
    fin_cases l
    · change ∫ w in Set.Ioc 0 4, x ![13 / 10, 1 / 2] w 0 = 21 / 4
      rw [setIntegral_congr_fun measurableSet_Ioc
        (g := fun w => min (15 * w / 22) ((10 * w + 5) / 18))
        (fun w hw => by simp only [hx1 w hw.1, Matrix.cons_val_zero])]
      rw [integral_two_piece (m := 11 / 5) (c₁ := 15 / 22) (e₁ := 0) (c₂ := 5 / 9) (e₂ := 5 / 18)
        (by fun_prop) (by norm_num) (by norm_num)
        (fun w hw => by rw [min_eq_left (by linarith [hw.2])]; ring)
        (fun w hw => by rw [min_eq_right (by linarith [hw.1])]; ring)]
      norm_num
    · change ∫ w in Set.Ioc 0 4, x ![13 / 10, 1 / 2] w 1 = 47 / 20
      rw [setIntegral_congr_fun measurableSet_Ioc
        (g := fun w => max (5 * w / 22) ((10 * w - 13) / 18))
        (fun w hw => by simp only [hx1 w hw.1, Matrix.cons_val_one, Matrix.cons_val_fin_one])]
      rw [integral_two_piece (m := 11 / 5) (c₁ := 5 / 22) (e₁ := 0) (c₂ := 5 / 9)
        (e₂ := -13 / 18) (by fun_prop) (by norm_num) (by norm_num)
        (fun w hw => by rw [max_eq_left (by linarith [hw.2])]; ring)
        (fun w hw => by rw [max_eq_right (by linarith [hw.1])]; ring)]
      norm_num
  refine ⟨hA, hB, ?_, ?_⟩
  · rw [hA, hB, dotProduct_two]
    norm_num
  · rw [hA, hB]
    intro h
    have := congrFun h 0
    norm_num at this

/-! ### Exercise 4.C.7: a unimodal counterexample -/

/-- Aggregate demand when wealth has density `f` on `(a, b]`: `∫ₐᵇ x̃(p, w) f(w) dw`. -/
noncomputable def densityDemand (x : DemandFunction L) (f : ℝ → ℝ) (a b : ℝ) (p : Fin L → ℝ) :
    Fin L → ℝ :=
  fun l => ∫ w in Set.Ioc a b, x p w l * f w

/-- The tent density on `[5/2, 7/2]` with peak at `3` (zero elsewhere). -/
noncomputable def tentDensity (w : ℝ) : ℝ := 2 - 4 * |w - 3|

/-- `∫ (c w + e) dw` against the tent density: `3c + e` (the density has mass one and mean 3). -/
theorem integral_tent (c e : ℝ) :
    ∫ w in Set.Ioc (5 / 2 : ℝ) (7 / 2), (c * w + e) * tentDensity w = 3 * c + e := by
  have hq : ∀ A B C a b : ℝ, ∫ w in a..b, (A * w ^ 2 + B * w + C) =
      A * ((b ^ 3 - a ^ 3) / 3) + B * ((b ^ 2 - a ^ 2) / 2) + C * (b - a) := by
    intro A B C a b
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
    · norm_num
      ring
    all_goals first
      | exact ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
      | exact ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      | exact intervalIntegrable_const
      | exact (((continuous_const.mul (continuous_pow 2)).add
          (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  have hcont : Continuous fun w : ℝ => (c * w + e) * tentDensity w := by
    unfold tentDensity
    fun_prop
  rw [← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 3) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_congr (a := 5 / 2) (b := 3)
      (g := fun w => (4 * c) * w ^ 2 + (4 * e - 10 * c) * w + (-10 * e)) (fun w hw => by
        rw [Set.uIcc_of_le (by norm_num)] at hw
        simp only [tentDensity, abs_of_nonpos (by linarith [hw.2] : w - 3 ≤ 0)]
        ring),
    intervalIntegral.integral_congr (a := 3) (b := 7 / 2)
      (g := fun w => (-4 * c) * w ^ 2 + (14 * c - 4 * e) * w + (14 * e)) (fun w hw => by
        rw [Set.uIcc_of_le (by norm_num)] at hw
        simp only [tentDensity, abs_of_nonneg (by linarith [hw.1] : 0 ≤ w - 3)]
        ring),
    hq, hq]
  ring

/-- **Exercise 4.C.7** (MWG, p. 124), second part. A unimodal wealth density for which the
conclusion of Proposition 4.C.4 fails: every consumer has consumer 1's L-shaped preference of
Example 4.C.1 and wealth has the tent density `2 - 4|w - 3|` on `[5/2, 7/2]` (mass one, single
peak at `3`). At `p = (1, 1/2)`, `p' = (1/2, 1)`, demand is affine in `w` on that interval, the
aggregate demands are `(11/6, 7/3)` and `(3/2, 9/4)`, and
`(p' - p)·[x(p') - x(p)] = 1/8 > 0`. -/
theorem exercise_4_C_7_unimodal {x1 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ex41U1 p w) :
    (∫ w in Set.Ioc (5 / 2 : ℝ) (7 / 2), tentDensity w) = 1 ∧
      densityDemand x1 tentDensity (5 / 2) (7 / 2) ex41P = ![11 / 6, 7 / 3] ∧
      densityDemand x1 tentDensity (5 / 2) (7 / 2) ex41P' = ![3 / 2, 9 / 4] ∧
      (ex41P' - ex41P) ⬝ᵥ (densityDemand x1 tentDensity (5 / 2) (7 / 2) ex41P' -
        densityDemand x1 tentDensity (5 / 2) (7 / 2) ex41P) = 1 / 8 := by
  have hk := strictMono_ex41Kink
  have hid : StrictMono (id : ℝ → ℝ) := strictMono_id
  have dem : ∀ (q : Fin 2 → ℝ) (v : ℝ) (y : Fin 2 → ℝ), StrictlyPositive q → 0 < v →
      0 ≤ y 0 → 0 ≤ y 1 → ex41Kink (y 0) = y 1 → q ⬝ᵥ y = v → x1 q v = y := by
    intro q v y hq hv hy0 hy1 hky hb
    have h := walrasianDemand_minUtility hk hid hq hy0 hy1 hky hb
    have := hx1 q v ⟨hq, hv⟩
    rw [ex41U1, h] at this
    exact this
  have hP : ∀ w ∈ Set.Ioc (5 / 2 : ℝ) (7 / 2),
      x1 ex41P w = ![8 / 9 * w + -5 / 6, 2 / 9 * w + 5 / 3] := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    apply dem _ _ _ ex41P_pos (by linarith)
    · simp only [Matrix.cons_val_zero]; linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith
    · simp only [ex41Kink, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        min_def]
      split_ifs <;> linarith
    · simp only [dotProduct_two, ex41P, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
  have hP' : ∀ w ∈ Set.Ioc (5 / 2 : ℝ) (7 / 2),
      x1 ex41P' w = ![4 / 3 * w + -5 / 2, 1 / 3 * w + 5 / 4] := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    apply dem _ _ _ ex41P'_pos (by linarith)
    · simp only [Matrix.cons_val_zero]; linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith
    · simp only [ex41Kink, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        min_def]
      split_ifs <;> linarith
    · simp only [dotProduct_two, ex41P', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
  have hcomp : ∀ (q : Fin 2 → ℝ) (c e : ℝ) (l : Fin 2),
      (∀ w ∈ Set.Ioc (5 / 2 : ℝ) (7 / 2), x1 q w l = c * w + e) →
      densityDemand x1 tentDensity (5 / 2) (7 / 2) q l = 3 * c + e := by
    intro q c e l h
    simp only [densityDemand]
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun w => (c * w + e) * tentDensity w)
      (fun w hw => by simp only [h w hw])]
    exact integral_tent c e
  have hA : densityDemand x1 tentDensity (5 / 2) (7 / 2) ex41P = ![11 / 6, 7 / 3] := by
    funext l
    fin_cases l
    · exact (hcomp ex41P (8 / 9) (-5 / 6) 0
        (fun w hw => by rw [hP w hw]; rfl)).trans (by norm_num)
    · exact (hcomp ex41P (2 / 9) (5 / 3) 1
        (fun w hw => by rw [hP w hw]; rfl)).trans (by norm_num)
  have hB : densityDemand x1 tentDensity (5 / 2) (7 / 2) ex41P' = ![3 / 2, 9 / 4] := by
    funext l
    fin_cases l
    · exact (hcomp ex41P' (4 / 3) (-5 / 2) 0
        (fun w hw => by rw [hP' w hw]; rfl)).trans (by norm_num)
    · exact (hcomp ex41P' (1 / 3) (5 / 4) 1
        (fun w hw => by rw [hP' w hw]; rfl)).trans (by norm_num)
  refine ⟨?_, hA, hB, ?_⟩
  · have := integral_tent 0 1
    simpa using this
  · rw [hA, hB, dotProduct_two]
    norm_num [ex41P, ex41P']

end MWG.AggregateDemand
