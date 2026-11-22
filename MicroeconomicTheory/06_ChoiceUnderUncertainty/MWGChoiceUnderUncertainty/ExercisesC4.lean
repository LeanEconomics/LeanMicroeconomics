/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ExercisesC3
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Exercises 6.C.9 (precautionary saving) and 6.C.20

MWG, pp. 210-213. Exercise 6.C.9 (Kimball): uncertainty about second-period income and
precautionary saving, absolute prudence `-v'''/v''`, and its relation to decreasing absolute
risk aversion. Exercise 6.C.20: the second derivative of the certainty equivalent of the
symmetric gamble `x ± ε` tends to `-r_A(x)`.

Corrections: in 6.C.9(c) the strict inequality needs a nondegenerate `y` (for `y ≡ 0` it is an
equality); in 6.C.9(d), with "decreasing" read as nonincreasing (as throughout Section 6.C), the
conclusion is `-v'''/v'' ≥ -v''/v'`, with equality for constant absolute risk aversion; it is
strict where `r_A' < 0`. The expectation of second-period utility is over a compactly supported
distribution of `y` (the convention of `MoneyLotteries`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- The tangent line of a concave differentiable function lies above it. -/
theorem concave_le_tangent {f : ℝ → ℝ} (hc : ConcaveOn ℝ univ f) {z₀ : ℝ}
    (hd : DifferentiableAt ℝ f z₀) (z : ℝ) : f z ≤ f z₀ + deriv f z₀ * (z - z₀) := by
  rcases lt_trichotomy z₀ z with h | rfl | h
  · have := hc.slope_le_deriv (mem_univ z₀) (mem_univ z) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.deriv_le_slope (mem_univ z) (mem_univ z₀) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- Expected second-period utility `E v(x + y)` is differentiable in `x` with derivative
`E v'(x + y)` when `v'` is continuous and `y` has compact support. -/
theorem hasDerivAt_expected {v : ℝ → ℝ} (hd : Differentiable ℝ v) (hc' : Continuous (deriv v))
    {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y, v (x + y) ∂μ) (∫ y, deriv v (x₀ + y) ∂μ) x₀ := by
  have := hμ.1
  obtain ⟨a, b, -, hae⟩ := hμ.ae_mem
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := x₀ - 1 + a) (b := x₀ + 1 + b)).exists_bound_of_continuousOn
    hc'.continuousOn
  have hcv : Continuous v := hd.continuous
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun x y => v (x + y)) (F' := fun x y => deriv v (x + y))
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => (hμ.integrable (S := univ) (u := fun y => v (x + y))
      (by fun_prop)).aestronglyMeasurable)
    (hμ.integrable (S := univ) (u := fun y => v (x₀ + y)) (by fun_prop))
    (hμ.integrable (S := univ) (u := fun y => deriv v (x₀ + y)) (by fun_prop)).aestronglyMeasurable
    ?_ (integrable_const C) ?_).2
  · filter_upwards [hae] with y hy x hx
    apply hC
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · exact Eventually.of_forall fun y x _ => ((hd (x + y)).hasDerivAt.comp_add_const x y)

/-- **Exercise 6.C.9(a)** (MWG, p. 211). Let `x₀` maximize `u(w - x) + v(x)` and `x*` maximize
`u(w - x) + E[v(x + y)]`, with `u, v` concave and differentiable (`v'` continuous). If
`E[v'(x₀ + y)] > v'(x₀)`, then `x* > x₀`. -/
theorem exercise_6_C_9a {u v : ℝ → ℝ} (hu : ConcaveOn ℝ univ u) (hv : ConcaveOn ℝ univ v)
    (hud : Differentiable ℝ u) (hvd : Differentiable ℝ v) (hv' : Continuous (deriv v))
    {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) {w x₀ xs : ℝ}
    (h₀ : ∀ x, u (w - x) + v x ≤ u (w - x₀) + v x₀)
    (hs : ∀ x, u (w - x) + ∫ y, v (x + y) ∂μ ≤ u (w - xs) + ∫ y, v (xs + y) ∂μ)
    (hprec : deriv v x₀ < ∫ y, deriv v (x₀ + y) ∂μ) : x₀ < xs := by
  have := hμ.1
  have hcv : Continuous v := hvd.continuous
  have hdu (x : ℝ) : HasDerivAt (fun x => u (w - x)) (-deriv u (w - x)) x := by
    exact (hud (w - x)).hasDerivAt.comp_const_sub w x
  -- first-order condition at the certainty optimum
  have hfoc : deriv u (w - x₀) = deriv v x₀ := by
    have hloc : IsLocalMax (fun x => u (w - x) + v x) x₀ := Eventually.of_forall h₀
    have := hloc.hasDerivAt_eq_zero ((hdu x₀).add (hvd x₀).hasDerivAt)
    linarith
  set G := fun x => u (w - x) + ∫ y, v (x + y) ∂μ
  have hGd : HasDerivAt G (-deriv u (w - x₀) + ∫ y, deriv v (x₀ + y) ∂μ) x₀ :=
    (hdu x₀).add (hasDerivAt_expected hvd hv' hμ x₀)
  -- below `x₀`, `G` is strictly smaller than `G x₀`
  have hbelow (x : ℝ) (hx : x < x₀) : G x < G x₀ := by
    have h1 := concave_le_tangent hu (hud (w - x₀)) (w - x)
    have h2 : ∫ y, v (x + y) ∂μ ≤ ∫ y, (v (x₀ + y) + deriv v (x₀ + y) * (x - x₀)) ∂μ :=
      integral_mono (hμ.integrable (S := univ) (u := fun y => v (x + y)) (by fun_prop))
        ((hμ.integrable (S := univ) (u := fun y => v (x₀ + y)) (by fun_prop)).add
          ((hμ.integrable (S := univ) (u := fun y => deriv v (x₀ + y)) (by fun_prop)).mul_const _))
        fun y => by
          have := concave_le_tangent hv (hvd (x₀ + y)) (x + y)
          rw [show x + y - (x₀ + y) = x - x₀ by ring] at this
          exact this
    rw [integral_add (hμ.integrable (S := univ) (u := fun y => v (x₀ + y)) (by fun_prop))
      ((hμ.integrable (S := univ) (u := fun y => deriv v (x₀ + y)) (by fun_prop)).mul_const _),
      integral_mul_const] at h2
    simp only [G]
    rw [show w - x - (w - x₀) = -(x - x₀) by ring] at h1
    nlinarith [mul_pos (sub_pos.mpr hprec) (sub_pos.mpr hx)]
  rcases lt_trichotomy x₀ xs with h | h | h
  · exact h
  · exfalso
    subst h
    have hloc : IsLocalMax G x₀ := Eventually.of_forall hs
    have := hloc.hasDerivAt_eq_zero hGd
    linarith
  · exfalso
    have := hbelow xs h
    linarith [hs x₀]

/-- The coefficient of absolute prudence `-v'''(x)/v''(x)` (MWG, Exercise 6.C.9(b), p. 211). -/
noncomputable def prudence (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv (deriv v)) x / deriv (deriv v) x

/-- Absolute prudence of `v` is the Arrow-Pratt coefficient of `-v'`. -/
theorem prudence_eq_arrowPratt (v : ℝ → ℝ) (x : ℝ) :
    prudence v x = arrowPratt (fun t => -deriv v t) x := by
  have h1 : deriv (fun t => -deriv v t) = fun t => -deriv (deriv v) t :=
    funext fun t => deriv.fun_neg
  have h2 : deriv (fun t => -deriv (deriv v) t) x = -deriv (deriv (deriv v)) x := deriv.fun_neg
  unfold prudence arrowPratt
  rw [h1, h2]
  by_cases h : deriv (deriv v) x = 0
  · simp [h]
  · field_simp

/-- **Exercise 6.C.9(b)** (MWG, p. 211). If the absolute prudence of `v₁` is nowhere larger than
that of `v₂`, then `E[v₁'(x₀ + y)] > v₁'(x₀)` implies `E[v₂'(x₀ + y)] > v₂'(x₀)` (stated for
the distribution `F` of final wealth `x₀ + y`). Here `v_i'` is twice continuously
differentiable with `v_i'' < 0`. -/
theorem exercise_6_C_9b {v₁ v₂ : ℝ → ℝ} (d1 : ∀ x, ContDiffAt ℝ 2 (fun t => -deriv v₁ t) x)
    (d2 : ∀ x, ContDiffAt ℝ 2 (fun t => -deriv v₂ t) x) (n1 : ∀ x, deriv (deriv v₁) x < 0)
    (n2 : ∀ x, deriv (deriv v₂) x < 0) (hP : ∀ x, prudence v₁ x ≤ prudence v₂ x)
    {ν : Measure ℝ} (hν : IsMoneyLottery univ ν) (x₀ : ℝ)
    (h1 : deriv v₁ x₀ < ∫ t, deriv v₁ t ∂ν) : deriv v₂ x₀ < ∫ t, deriv v₂ t ∂ν := by
  have hpos (v : ℝ → ℝ) (n : ∀ x, deriv (deriv v) x < 0) (x : ℝ) (_ : x ∈ univ) :
      0 < deriv (fun t => -deriv v t) x := by
    rw [deriv.fun_neg]; linarith [n x]
  have T := proposition_6_C_2 convex_univ isOpen_univ univ_nonempty (fun x _ => d1 x)
    (fun x _ => d2 x) (hpos v₁ n1) (hpos v₂ n2)
  have hV : MoreRiskAverseV univ (fun t => -deriv v₁ t) (fun t => -deriv v₂ t) :=
    (T.out 1 5).mp fun x _ => by rw [← prudence_eq_arrowPratt, ← prudence_eq_arrowPratt]; exact hP x
  by_contra hcon
  have hle : -deriv v₂ x₀ ≤ ∫ t, -deriv v₂ t ∂ν := by
    rw [integral_neg]; linarith [not_lt.mp hcon]
  have := hV ν x₀ hν (mem_univ _) hle
  rw [integral_neg] at this
  linarith

/-- **Exercise 6.C.9(c)** (MWG, p. 211), corrected. If `v''' > 0` and `E[y] = 0` with `y` not
identically zero, then `E[v'(x + y)] > v'(x)` for every `x`. -/
theorem exercise_6_C_9c {v : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv v))
    (h3 : ∀ x, 0 < deriv (deriv (deriv v)) x)
    {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) (hmean : ∫ y, y ∂μ = 0)
    (hnd : μ ≠ Measure.dirac 0) (x : ℝ) : deriv v x < ∫ y, deriv v (x + y) ∂μ := by
  have := hμ.1
  have hsc : StrictConvexOn ℝ univ (deriv v) :=
    (strictMono_of_deriv_pos h3).strictConvexOn_univ_of_deriv hd2.continuous
  have hcont : Continuous (deriv v) := hd2.continuous
  have hj := hsc.ae_eq_const_or_map_average_lt hcont.continuousOn isClosed_univ
    (Eventually.of_forall fun y => mem_univ (x + y))
    (hμ.integrable (S := univ) (u := fun y => x + y) (by fun_prop))
    (hμ.integrable (S := univ) (u := fun y => deriv v (x + y)) (by fun_prop))
  simp only [average_eq_integral] at hj
  rw [integral_add (integrable_const x) hμ.integrable_id, hmean, integral_const] at hj
  simp only [probReal_univ, one_smul, add_zero] at hj
  rcases hj with hconst | hlt
  · exfalso
    apply hnd
    apply eq_dirac_of_ae_eq_const
    filter_upwards [hconst] with y hy
    simp only [Function.const_apply] at hy
    linarith
  · exact hlt

/-- **Exercise 6.C.9(c)**: the strict inequality fails for the degenerate `y ≡ 0`. -/
theorem exercise_6_C_9c_degenerate (v : ℝ → ℝ) (x : ℝ) :
    ∫ y, deriv v (x + y) ∂(Measure.dirac (0 : ℝ)) = deriv v x := by
  rw [integral_dirac, add_zero]

/-- **Exercise 6.C.9(d)** (MWG, p. 211), corrected. If `r_A = -v''/v'` is (weakly) decreasing,
`v' > 0` and `v'' < 0`, then `-v'''/v'' ≥ -v''/v'` and hence `v''' > 0`; the first inequality is
strict where `r_A' < 0`. -/
theorem exercise_6_C_9d {v : ℝ → ℝ} (hd1 : Differentiable ℝ (deriv v))
    (hd2 : Differentiable ℝ (deriv (deriv v))) (hp : ∀ x, 0 < deriv v x)
    (hn : ∀ x, deriv (deriv v) x < 0) (x : ℝ) :
    (deriv (arrowPratt v) x ≤ 0 → arrowPratt v x ≤ prudence v x ∧
      0 < deriv (deriv (deriv v)) x) ∧
    (deriv (arrowPratt v) x < 0 → arrowPratt v x < prudence v x) := by
  have hr : HasDerivAt (arrowPratt v)
      (-(deriv (deriv (deriv v)) x * deriv v x - deriv (deriv v) x * deriv (deriv v) x) /
        deriv v x ^ 2) x := by
    have := ((hd2 x).hasDerivAt.neg).div (hd1 x).hasDerivAt (hp x).ne'
    convert this using 1
    · funext t; simp only [arrowPratt, Pi.div_apply, Pi.neg_apply]
    · rw [Pi.neg_apply]; ring
  rw [hr.deriv]
  set A := deriv v x
  set B := deriv (deriv v) x
  set C := deriv (deriv (deriv v)) x
  have hA : 0 < A := hp x
  have hB : B < 0 := hn x
  have hB2 : 0 < B * B := mul_pos_of_neg_of_neg hB hB
  have hA2 : 0 < A ^ 2 := by positivity
  have hgoal : arrowPratt v x = -B / A := rfl
  have hpr : prudence v x = C / -B := by
    change -C / B = C / -B
    rw [neg_div, div_neg]
  rw [hgoal, hpr]
  constructor
  · intro h
    have key : B * B ≤ C * A := by
      by_contra hk
      have : 0 < -(C * A - B * B) / A ^ 2 := div_pos (by linarith) hA2
      linarith
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ hA (by linarith)]; nlinarith
    · by_contra hc
      have : C * A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hA.le
      linarith
  · intro h
    have key : B * B < C * A := by
      by_contra hk
      have : 0 ≤ -(C * A - B * B) / A ^ 2 := div_nonneg (by linarith) hA2.le
      linarith
    rw [div_lt_div_iff₀ hA (by linarith)]; nlinarith

/-- **Exercise 6.C.9(d)**: with constant absolute risk aversion (`v = -e^{-x}`) the two sides
are equal, so the printed strict inequality fails under weakly decreasing `r_A`. -/
theorem exercise_6_C_9d_cara (x : ℝ) :
    prudence (Kreps.UtilityForMoney.ExponentialUtility 1) x =
      arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 1) x := by
  have h1 : deriv (Kreps.UtilityForMoney.ExponentialUtility 1) = fun t => Real.exp (-t) := by
    funext t
    simpa using (Kreps.UtilityForMoney.exponentialUtility_hasDerivAt 1 t).deriv
  have h2 : deriv (fun t => Real.exp (-t)) = fun t => -Real.exp (-t) := by
    funext t
    simpa using ((hasDerivAt_neg t).exp).deriv
  have h3 : deriv (fun t => -Real.exp (-t)) = fun t => Real.exp (-t) := by
    funext t; rw [deriv.fun_neg, h2]; ring
  unfold prudence arrowPratt
  rw [h1, h2, h3]
  field_simp

/-- **Exercise 6.C.20** (MWG, p. 213). Let `c(ε)` be the certainty equivalent of the gamble
paying `x + ε` or `x - ε` with probability `1/2` each (`u(c(ε)) = (u(x+ε) + u(x-ε))/2` near
`ε = 0`), twice continuously differentiable at `0`. For `u` twice continuously differentiable
and strictly increasing with `u'(x) > 0`, `c''(ε) → -r_A(x)` as `ε → 0`. -/
theorem exercise_6_C_20 {u c : ℝ → ℝ} {x : ℝ} (hu : ContDiff ℝ 2 u) (hi : StrictMono u)
    (hp : 0 < deriv u x) (hc : ContDiffAt ℝ 2 c 0)
    (he : ∀ᶠ ε in 𝓝 0, u (c ε) = (u (x + ε) + u (x - ε)) / 2) :
    Tendsto (fun ε => deriv (deriv c) ε) (𝓝 0) (𝓝 (-arrowPratt u x)) := by
  have hc0 : c 0 = x := by
    have h0 := he.self_of_nhds
    simp only [add_zero, sub_zero] at h0
    have : u (c 0) = u x := by rw [h0]; ring
    exact hi.injective this
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu2 : Differentiable ℝ (deriv u) := hu.differentiable_deriv_two
  have hc1 : ContDiffAt ℝ 1 (deriv c) 0 := hc.derivWithin (m := 1) (by norm_num)
  have hc2 : ContinuousAt (deriv (deriv c)) 0 :=
    (hc1.derivWithin (m := 0) (by norm_num)).continuousAt
  have hcd : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ c ε :=
    (hc.eventually (by simp)).mono fun ε h => h.differentiableAt (by norm_num)
  set S := fun ε : ℝ => (u (x + ε) + u (x - ε)) / 2
  have hS1 : deriv S = fun ε => (deriv u (x + ε) - deriv u (x - ε)) / 2 := by
    funext ε
    have h1 := (hu1 (x + ε)).hasDerivAt.comp_const_add x ε
    have h2 := (hu1 (x - ε)).hasDerivAt.comp_const_sub x ε
    exact ((h1.add h2).div_const 2).deriv.trans (by ring)
  have hS2 : deriv (deriv S) 0 = deriv (deriv u) x := by
    rw [hS1]
    have h1 := (hu2 (x + 0)).hasDerivAt.comp_const_add x 0
    have h2 := (hu2 (x - 0)).hasDerivAt.comp_const_sub x 0
    have h3 : HasDerivAt (fun ε => (deriv u (x + ε) - deriv u (x - ε)) / 2)
        ((deriv (deriv u) (x + 0) - -deriv (deriv u) (x - 0)) / 2) 0 := (h1.sub h2).div_const 2
    rw [h3.deriv]
    simp only [add_zero, sub_zero]; ring
  -- derivatives of `u ∘ c` near `0`
  have hg1 : ∀ᶠ ε in 𝓝 (0 : ℝ), deriv (fun e => u (c e)) ε = deriv u (c ε) * deriv c ε := by
    filter_upwards [hcd] with ε hε
    exact ((hu1 (c ε)).hasDerivAt.comp ε hε.hasDerivAt).deriv
  have hgS : deriv (fun e => u (c e)) =ᶠ[𝓝 0] deriv S :=
    Filter.EventuallyEq.deriv (show (fun e => u (c e)) =ᶠ[𝓝 0] S from he)
  have hfirst : deriv u x * deriv c 0 = 0 := by
    have := hgS.self_of_nhds
    rw [hg1.self_of_nhds, hc0, hS1] at this
    simpa using this
  have hc'0 : deriv c 0 = 0 := by
    rcases mul_eq_zero.mp hfirst with h | h
    · linarith
    · exact h
  have hsecond : deriv (fun ε => deriv u (c ε) * deriv c ε) 0 = deriv (deriv u) x * deriv c 0 *
      deriv c 0 + deriv u x * deriv (deriv c) 0 := by
    have hcd0 : DifferentiableAt ℝ c 0 := hc.differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun ε => deriv u (c ε)) (deriv (deriv u) (c 0) * deriv c 0) 0 :=
      (hu2 (c 0)).hasDerivAt.comp 0 hcd0.hasDerivAt
    have h2 : HasDerivAt (deriv c) (deriv (deriv c) 0) 0 :=
      (hc1.differentiableAt (by norm_num)).hasDerivAt
    have h3 : HasDerivAt (fun ε => deriv u (c ε) * deriv c ε)
        (deriv (deriv u) (c 0) * deriv c 0 * deriv c 0 + deriv u (c 0) * deriv (deriv c) 0) 0 :=
      h1.mul h2
    rw [h3.deriv, hc0]
  have hval : deriv (deriv c) 0 = -arrowPratt u x := by
    have hcomb : (fun ε => deriv u (c ε) * deriv c ε) =ᶠ[𝓝 0] deriv S :=
      (show deriv (fun e => u (c e)) =ᶠ[𝓝 0] fun ε => deriv u (c ε) * deriv c ε from
        hg1).symm.trans hgS
    have h := hcomb.deriv_eq
    rw [hsecond, hS2, hc'0] at h
    unfold arrowPratt
    field_simp
    linarith
  rw [← hval]
  exact hc2.tendsto

/-- A concrete instance of Exercise 6.C.20: for `u(x) = -e^{-x}`, `c(ε) = x - ln cosh ε` is the
certainty equivalent of `x ± ε`, twice continuously differentiable. -/
theorem exercise_6_C_20_instance (x : ℝ) :
    ContDiffAt ℝ 2 (fun ε => x - Real.log (Real.cosh ε)) 0 ∧
      ∀ ε, Kreps.UtilityForMoney.ExponentialUtility 1 (x - Real.log (Real.cosh ε)) =
        (Kreps.UtilityForMoney.ExponentialUtility 1 (x + ε) +
          Kreps.UtilityForMoney.ExponentialUtility 1 (x - ε)) / 2 := by
  constructor
  · apply contDiffAt_const.sub
    exact (Real.contDiffAt_log.mpr (Real.cosh_pos 0).ne').comp 0 Real.contDiff_cosh.contDiffAt
  · intro ε
    simp only [Kreps.UtilityForMoney.ExponentialUtility, neg_mul, one_mul]
    rw [show -(x - Real.log (Real.cosh ε)) = -x + Real.log (Real.cosh ε) by ring, Real.exp_add,
      Real.exp_log (Real.cosh_pos ε), Real.cosh_eq, show -(x + ε) = -x + -ε by ring,
      show -(x - ε) = -x + ε by ring, Real.exp_add, Real.exp_add]
    ring

end MWG.ChoiceUnderUncertainty
