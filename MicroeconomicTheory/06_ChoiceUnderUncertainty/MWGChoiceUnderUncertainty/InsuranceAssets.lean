/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.RiskAversion
import UtilityForMoney.Insurance
import Mathlib.Analysis.Convex.Continuous

/-!
# Insurance and the demand for risky assets

MWG, Section 6.C, pp. 187-189: Example 6.C.1 (insurance; full insurance at actuarially fair
prices), Exercise 6.C.1 (incomplete insurance at unfair prices), Example 6.C.2 (a risk averter
always holds some of an actuarially favorable asset) with footnote 17, and Example 6.C.3 with
Exercise 6.C.4 (the portfolio utility `U(α) = ∫ u(α · z) dF(z)` is increasing, concave and
continuous).

The insurance objective is `(1 - π) u(w - αq) + π u(w - αq - D + α)` over `α ≥ 0` (MWG's
domain, not Kreps's unrestricted coverage). Bernoulli utilities are defined on the whole line,
so wealth levels need not be restricted. Asset returns have a distribution with compact support
(the convention of `MoneyLotteries`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- Expected utility of buying `α` units of insurance (MWG, p. 188). -/
def insuranceEU (u : ℝ → ℝ) (w D π q α : ℝ) : ℝ :=
  (1 - π) * u (w - α * q) + π * u (w - α * q - D + α)

/-- **Example 6.C.1** (MWG, p. 187). Expected wealth with `α` units of insurance is
`w - πD + α(π - q)`. -/
theorem example_6_C_1_expected_wealth (w D π q α : ℝ) :
    (1 - π) * (w - α * q) + π * (w - α * q - D + α) = w - π * D + α * (π - q) := by ring

/-- A first-order necessary condition at a maximum over `[x, ∞)`: the derivative is `≤ 0`. -/
theorem deriv_nonpos_of_max_Ici {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hmax : ∀ y, x ≤ y → f y ≤ f x) : f' ≤ 0 := by
  by_contra hpos
  have hpos : 0 < f' := lt_of_not_ge hpos
  have hev := hf.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)
  obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0' : (0 : ℝ) < t := ht0
  have := hmax (x + t) (by linarith)
  rw [smul_eq_mul] at ht
  have : t⁻¹ * (f (x + t) - f x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0'.le) (by linarith)
  linarith

/-- The derivative of the insurance objective in `α`. -/
theorem insuranceEU_hasDerivAt {u : ℝ → ℝ} (w D π q α : ℝ)
    (h1 : DifferentiableAt ℝ u (w - α * q)) (h2 : DifferentiableAt ℝ u (w - D + α * (1 - q))) :
    HasDerivAt (insuranceEU u w D π q)
      (-q * (1 - π) * deriv u (w - α * q) + π * (1 - q) * deriv u (w - D + α * (1 - q))) α := by
  have ha : HasDerivAt (fun a : ℝ => w - a * q) (-q) α := by
    simpa using ((hasDerivAt_id' α).mul_const q).const_sub w
  have hb : HasDerivAt (fun a : ℝ => w - D + a * (1 - q)) (1 - q) α := by
    simpa using ((hasDerivAt_id' α).mul_const (1 - q)).const_add (w - D)
  have hu1 : HasDerivAt (fun a => u (w - a * q)) (deriv u (w - α * q) * -q) α :=
    h1.hasDerivAt.comp α ha
  have hu2 : HasDerivAt (fun a => u (w - D + a * (1 - q)))
      (deriv u (w - D + α * (1 - q)) * (1 - q)) α := h2.hasDerivAt.comp α hb
  have hfun : insuranceEU u w D π q =
      fun a => (1 - π) * u (w - a * q) + π * u (w - D + a * (1 - q)) := by
    funext a
    unfold insuranceEU
    rw [show w - a * q - D + a = w - D + a * (1 - q) by ring]
  rw [hfun]
  convert (hu1.const_mul (1 - π)).add (hu2.const_mul π) using 1
  ring

/-- **Example 6.C.1** (MWG, p. 188), the first-order condition: at an optimum `α* ≥ 0`,
`-q(1 - π)u'(w - α*q) + π(1 - q)u'(w - D + α*(1 - q)) ≤ 0`, with equality if `α* > 0`. -/
theorem example_6_C_1_foc {u : ℝ → ℝ} {w D π q a : ℝ} (ha : 0 ≤ a)
    (hopt : ∀ b, 0 ≤ b → insuranceEU u w D π q b ≤ insuranceEU u w D π q a)
    (h1 : DifferentiableAt ℝ u (w - a * q)) (h2 : DifferentiableAt ℝ u (w - D + a * (1 - q))) :
    -q * (1 - π) * deriv u (w - a * q) + π * (1 - q) * deriv u (w - D + a * (1 - q)) ≤ 0 ∧
    (0 < a →
      -q * (1 - π) * deriv u (w - a * q) + π * (1 - q) * deriv u (w - D + a * (1 - q)) = 0) := by
  have hd := insuranceEU_hasDerivAt w D π q a h1 h2
  refine ⟨deriv_nonpos_of_max_Ici hd fun b hb => hopt b (ha.trans hb), fun hpos => ?_⟩
  have hloc : IsLocalMax (insuranceEU u w D π q) a := by
    filter_upwards [lt_mem_nhds hpos] with b hb
    exact hopt b hb.le
  exact hloc.hasDerivAt_eq_zero hd

/-- **Example 6.C.1** (MWG, pp. 188-189). With actuarially fair insurance (`q = π`) a strictly
risk-averse decision maker insures completely: `α = D` is the unique optimum, giving final
wealth `w - πD` in both states. -/
theorem example_6_C_1 {u : ℝ → ℝ} (hc : StrictConcaveOn ℝ univ u) {π : ℝ} (h0 : 0 < π)
    (h1 : π < 1) (w D : ℝ) :
    (∀ α, insuranceEU u w D π π α ≤ insuranceEU u w D π π D) ∧
    (∀ α, insuranceEU u w D π π α = insuranceEU u w D π π D → α = D) ∧
    insuranceEU u w D π π D = u (w - π * D) := by
  have hD : insuranceEU u w D π π D = u (w - π * D) := by
    unfold insuranceEU
    rw [show w - D * π - D + D = w - π * D by ring, show w - D * π = w - π * D by ring]
    ring
  have key (α : ℝ) (hα : α ≠ D) : insuranceEU u w D π π α < u (w - π * D) := by
    have hne : w - α * π ≠ w - α * π - D + α := by
      intro h; exact hα (by linarith)
    have := hc.2 (mem_univ (w - α * π)) (mem_univ (w - α * π - D + α)) hne
      (show 0 < 1 - π by linarith) h0 (by ring)
    simp only [smul_eq_mul] at this
    rw [show (1 - π) * (w - α * π) + π * (w - α * π - D + α) = w - π * D by ring] at this
    exact this
  refine ⟨fun α => ?_, fun α hα => ?_, hD⟩
  · by_cases hα : α = D
    · rw [hα]
    · rw [hD]; exact (key α hα).le
  · by_contra hne
    have := key α hne
    rw [hα, hD] at this
    exact lt_irrefl _ this

/-- **Exercise 6.C.1** (MWG, p. 209). If insurance is not actuarially fair (`q > π`), a
strictly increasing, concave, differentiable Bernoulli utility never insures completely: every
optimum over `α ≥ 0` has `α < D`. -/
theorem exercise_6_C_1 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) (hi : StrictMono u)
    (hd : Differentiable ℝ u) {w D π q a : ℝ} (hD : 0 < D) (h0 : 0 ≤ π) (h1 : π ≤ 1)
    (hq : π < q)
    (hopt : ∀ b, 0 ≤ b → insuranceEU u w D π q b ≤ insuranceEU u w D π q a) : a < D := by
  have hfull : insuranceEU u w D π q D = u (w - D * q) := by
    unfold insuranceEU
    rw [show w - D * q - D + D = w - D * q by ring]
    ring
  rcases lt_trichotomy a D with hlt | heq | hgt
  · exact hlt
  · exfalso
    subst heq
    have hloc : IsLocalMax (insuranceEU u w a π q) a := by
      filter_upwards [lt_mem_nhds hD] with b hb
      exact hopt b hb.le
    have hder := insuranceEU_hasDerivAt (u := u) w a π q a (hd _) (hd _)
    have hz := hloc.hasDerivAt_eq_zero hder
    rw [show w - a + a * (1 - q) = w - a * q by ring] at hz
    have hpos := Kreps.UtilityForMoney.deriv_pos_of_concave_strictMono hc hi (hd (w - a * q))
    have : (π - q) * deriv u (w - a * q) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  · exfalso
    have hmean := hc.2 (mem_univ (w - a * q)) (mem_univ (w - a * q - D + a))
      (sub_nonneg.mpr h1) h0 (by ring)
    simp only [smul_eq_mul] at hmean
    rw [show (1 - π) * (w - a * q) + π * (w - a * q - D + a) = w - π * D + a * (π - q) by ring]
      at hmean
    have hlt : w - π * D + a * (π - q) < w - D * q := by nlinarith
    have := hi hlt
    have hopt' := hopt D hD.le
    rw [hfull] at hopt'
    change (1 - π) * u (w - a * q) + π * u (w - a * q - D + a) ≥ u (w - D * q) at hopt'
    linarith

/-- Expected utility from investing `α` in the risky asset with return distribution `F`
(MWG, Example 6.C.2, p. 188): `∫ u(w + α(z - 1)) dF(z)`. -/
noncomputable def assetEU (u : ℝ → ℝ) (w : ℝ) (μ : Measure ℝ) (α : ℝ) : ℝ :=
  ∫ z, u (w + α * (z - 1)) ∂μ

/-- Integrability of the asset objective for a continuous Bernoulli utility. -/
theorem assetEU_integrable {u : ℝ → ℝ} (hu : Continuous u) {μ : Measure ℝ}
    (hμ : IsMoneyLottery univ μ) (w α : ℝ) : Integrable (fun z => u (w + α * (z - 1))) μ :=
  hμ.integrable (S := univ) (u := fun z => u (w + α * (z - 1))) (by fun_prop)

/-- **Footnote 17** (MWG, p. 189). For a concave Bernoulli utility the asset objective is
concave in `α`. -/
theorem footnote_6_17 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) {μ : Measure ℝ}
    (hμ : IsMoneyLottery univ μ) (w : ℝ) : ConcaveOn ℝ univ (assetEU u w μ) := by
  have hcont : Continuous u := by
    have := hc.continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  have := hμ.1
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [assetEU, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((assetEU_integrable hcont hμ w a).const_mul s) ((assetEU_integrable hcont hμ w b).const_mul t)]
  apply integral_mono ((assetEU_integrable hcont hμ w a).const_mul s |>.add
    ((assetEU_integrable hcont hμ w b).const_mul t)) (assetEU_integrable hcont hμ w _)
  intro z
  have := hc.2 (mem_univ (w + a * (z - 1))) (mem_univ (w + b * (z - 1))) hs ht hst
  simp only [smul_eq_mul] at this
  convert this using 2
  have : s * (w + a * (z - 1)) + t * (w + b * (z - 1)) = (s + t) * w + (s * a + t * b) * (z - 1)
    := by ring
  rw [this, hst, one_mul]

/-- **Example 6.C.2** (MWG, p. 189). If the risky asset's mean return exceeds the safe return,
`∫ z dF > 1`, a strictly increasing, concave Bernoulli utility differentiable at `w > 0` gains
from investing a small amount: some `α ∈ (0, w]` gives strictly higher expected utility than
`α = 0`. Hence every optimal portfolio has `α* > 0`. -/
theorem example_6_C_2 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) (hi : StrictMono u)
    {w : ℝ} (hw : 0 < w) (hdw : DifferentiableAt ℝ u w) {μ : Measure ℝ}
    (hμ : IsMoneyLottery univ μ) (hmean : 1 < ∫ z, z ∂μ) :
    ∃ α ∈ Ioc 0 w, assetEU u w μ 0 < assetEU u w μ α := by
  have := hμ.1
  have hcont : Continuous u := by
    have := hc.continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  obtain ⟨a, b, -, hae⟩ := hμ.ae_mem
  set d := deriv u w
  have hd : 0 < d := Kreps.UtilityForMoney.deriv_pos_of_concave_strictMono hc hi hdw
  set m := ∫ z, z ∂μ - 1
  have hm : 0 < m := by simp only [m]; linarith
  set K := |a - 1| + |b - 1| + 1
  have hK : 0 < K := by positivity
  set ε := d * m / (2 * K)
  have hε : 0 < ε := by positivity
  have hlo := hdw.hasDerivAt.isLittleO.bound hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set α := min w (δ / (2 * K))
  have hα : 0 < α := lt_min hw (by positivity)
  refine ⟨α, ⟨hα, min_le_left _ _⟩, ?_⟩
  have hbnd : ∀ z ∈ Icc a b, |z - 1| ≤ K := by
    intro z hz
    rcases le_total 1 z with h | h
    · rw [abs_of_nonneg (by linarith)]
      have : z - 1 ≤ |b - 1| := (by linarith [hz.2] : z - 1 ≤ b - 1).trans (le_abs_self _)
      linarith [abs_nonneg (a - 1)]
    · rw [abs_of_nonpos (by linarith)]
      have : 1 - z ≤ |a - 1| := (by linarith [hz.1] : 1 - z ≤ 1 - a).trans
        (by rw [abs_sub_comm]; exact le_abs_self _)
      linarith [abs_nonneg (b - 1)]
  have hpt : ∀ z ∈ Icc a b, u w + d * (α * (z - 1)) - ε * (α * K) ≤ u (w + α * (z - 1)) := by
    intro z hz
    have hz1 := hbnd z hz
    have hsmall : dist (w + α * (z - 1)) w < δ := by
      rw [Real.dist_eq, show w + α * (z - 1) - w = α * (z - 1) by ring, abs_mul,
        abs_of_pos hα]
      calc α * |z - 1| ≤ α * K := mul_le_mul_of_nonneg_left hz1 hα.le
        _ ≤ δ / (2 * K) * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK.le
        _ < δ := by field_simp; linarith
    have hb := hball hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show w + α * (z - 1) - w = α * (z - 1) by ring,
      smul_eq_mul] at hb
    have h2 : |α * (z - 1)| ≤ α * K := by
      rw [abs_mul, abs_of_pos hα]; exact mul_le_mul_of_nonneg_left hz1 hα.le
    have h3 := neg_abs_le (u (w + α * (z - 1)) - u w - α * (z - 1) * d)
    nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
  have hint : ∫ z, (u w + d * (α * (z - 1)) - ε * (α * K)) ∂μ ≤
      ∫ z, u (w + α * (z - 1)) ∂μ := integral_mono_ae (μ := μ)
    (((integrable_const (u w)).add ((hμ.integrable_id.sub (integrable_const 1)).const_mul α
      |>.const_mul d)).sub (integrable_const (ε * (α * K))))
    (assetEU_integrable hcont hμ w α) (hae.mono fun z hz => hpt z hz)
  have hcalc : ∫ z, (u w + d * (α * (z - 1)) - ε * (α * K)) ∂μ =
      u w + d * α * m - ε * (α * K) := by
    rw [integral_sub, integral_add, integral_const_mul, integral_const_mul, integral_sub]
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, m]; ring
    all_goals first
      | exact integrable_const _
      | exact hμ.integrable_id
      | exact (hμ.integrable_id.sub (integrable_const 1)).const_mul α
      | exact ((hμ.integrable_id.sub (integrable_const 1)).const_mul α).const_mul d
      | exact (integrable_const _).add (((hμ.integrable_id.sub (integrable_const 1)).const_mul
          α).const_mul d)
  rw [hcalc] at hint
  have h0 : assetEU u w μ 0 = u w := by simp [assetEU]
  rw [h0]
  have hεK : ε * K = d * m / 2 := by simp only [ε]; field_simp
  have : u w < u w + d * α * m - ε * (α * K) := by
    have : ε * (α * K) = α * (d * m / 2) := by rw [← hεK]; ring
    rw [this]; nlinarith [mul_pos hd hm]
  exact this.trans_le hint

/-- The utility of a portfolio `α ∈ ℝ^N_+` of risky assets with jointly distributed returns
(MWG, Example 6.C.3, p. 189, and Exercise 6.C.4, p. 210): `U(α) = ∫ u(α₁z₁ + ⋯ + α_N z_N) dF`. -/
noncomputable def portfolioU {N : ℕ} (u : ℝ → ℝ) (μ : Measure (Fin N → ℝ)) (α : Fin N → ℝ) :
    ℝ :=
  ∫ z, u (∑ n, α n * z n) ∂μ

variable {N : ℕ} {u : ℝ → ℝ} {μ : Measure (Fin N → ℝ)} {K : Set (Fin N → ℝ)}

/-- The portfolio payoff is nonnegative for nonnegative holdings and returns. -/
theorem portfolio_payoff_nonneg {α z : Fin N → ℝ} (hα : 0 ≤ α) (hz : 0 ≤ z) :
    0 ≤ ∑ n, α n * z n :=
  Finset.sum_nonneg fun n _ => mul_nonneg (hα n) (hz n)

/-- The portfolio integrand is integrable when returns are supported in a compact set of
nonnegative vectors. -/
theorem portfolio_integrable [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0) {α : Fin N → ℝ} (hα : 0 ≤ α) :
    Integrable (fun z => u (∑ n, α n * z n)) μ := by
  have hr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.mp hμK |>.mono fun x hx => by simpa using hx)
  have hc : ContinuousOn (fun z : Fin N → ℝ => u (∑ n, α n * z n)) K :=
    hu.comp (by fun_prop) fun z hz => portfolio_payoff_nonneg hα (hKn z hz)
  have := hc.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, hr] at this

/-- **Exercise 6.C.4(a)** (MWG, p. 210). For a nondecreasing `u`, the portfolio utility is
nondecreasing in the holdings. -/
theorem exercise_6_C_4a [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hm : MonotoneOn u (Ici 0)) (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0)
    {α β : Fin N → ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) : portfolioU u μ α ≤ portfolioU u μ β := by
  have hβ : 0 ≤ β := hα.trans hαβ
  apply integral_mono_ae (portfolio_integrable hu hK hKn hμK hα)
    (portfolio_integrable hu hK hKn hμK hβ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
  have hz' : 0 ≤ z := hKn z (by simpa using hz)
  exact hm (portfolio_payoff_nonneg hα hz') (portfolio_payoff_nonneg hβ hz')
    (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hαβ n) (hz' n))

/-- **Exercise 6.C.4(b)** (MWG, p. 210). For a concave `u`, the portfolio utility is concave on
`ℝ^N_+`. -/
theorem exercise_6_C_4b [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hc : ConcaveOn ℝ (Ici 0) u) (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0) :
    ConcaveOn ℝ (Ici 0) (portfolioU u μ) := by
  refine ⟨convex_Ici 0, fun α hα β hβ s t hs ht hst => ?_⟩
  have hα' : 0 ≤ α := hα
  have hβ' : 0 ≤ β := hβ
  have hIα := portfolio_integrable hu hK hKn hμK hα'
  have hIβ := portfolio_integrable hu hK hKn hμK hβ'
  have hγ : 0 ≤ s • α + t • β := add_nonneg (smul_nonneg hs hα') (smul_nonneg ht hβ')
  simp only [portfolioU, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIα.const_mul s)
    (hIβ.const_mul t)]
  apply integral_mono_ae ((hIα.const_mul s).add (hIβ.const_mul t))
    (portfolio_integrable hu hK hKn hμK hγ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
  have hz' : 0 ≤ z := hKn z (by simpa using hz)
  have := hc.2 (show ∑ n, α n * z n ∈ Ici (0 : ℝ) from portfolio_payoff_nonneg hα' hz')
    (show ∑ n, β n * z n ∈ Ici (0 : ℝ) from portfolio_payoff_nonneg hβ' hz') hs ht hst
  simp only [smul_eq_mul] at this
  convert this using 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- **Exercise 6.C.4(c)** (MWG, p. 210). For a continuous `u`, the portfolio utility is
continuous on `ℝ^N_+`. -/
theorem exercise_6_C_4c [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0) :
    ContinuousOn (portfolioU u μ) (Ici 0) := by
  intro α0 hα0
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  set A := ‖α0‖ + 1
  set R := N * A * |C|
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (hu.mono Icc_subset_Ici_self)
  set s' : Set (Fin N → ℝ) := Ici 0 ∩ Metric.closedBall α0 1
  have hs' : s' ∈ 𝓝[Ici 0] α0 := inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds α0 one_pos)
  have hae : ∀ᵐ z ∂μ, z ∈ K := measure_eq_zero_iff_ae_notMem.mp hμK |>.mono fun x hx => by
    simpa using hx
  have hcont : ContinuousOn (portfolioU u μ) s' := by
    apply continuousOn_of_dominated (bound := fun _ => M)
    · intro α hα
      exact (portfolio_integrable hu hK hKn hμK hα.1).aestronglyMeasurable
    · intro α hα
      filter_upwards [hae] with z hz
      apply hM
      refine ⟨portfolio_payoff_nonneg hα.1 (hKn z hz), ?_⟩
      have hαn : ‖α‖ ≤ A := by
        have := Metric.mem_closedBall.mp hα.2
        calc ‖α‖ ≤ ‖α - α0‖ + ‖α0‖ := norm_le_norm_sub_add α α0
          _ ≤ 1 + ‖α0‖ := by rw [← dist_eq_norm]; linarith
          _ = A := by ring
      calc ∑ n, α n * z n ≤ ∑ _n : Fin N, A * |C| := by
            apply Finset.sum_le_sum
            intro n _
            calc α n * z n ≤ |α n * z n| := le_abs_self _
              _ = |α n| * |z n| := abs_mul _ _
              _ ≤ A * |C| := by
                apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
                · exact (norm_le_pi_norm α n).trans hαn
                · exact ((norm_le_pi_norm z n).trans (hC z hz)).trans (le_abs_self C)
        _ = R := by simp [R]; ring
    · exact integrable_const M
    · filter_upwards [hae] with z hz
      exact hu.comp (by fun_prop) fun α hα => portfolio_payoff_nonneg hα.1 (hKn z hz)
  exact (hcont α0 ⟨hα0, Metric.mem_closedBall_self zero_le_one⟩).mono_of_mem_nhdsWithin hs'

end MWG.ChoiceUnderUncertainty
