/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.BudgetBalance
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# The differentiable case of dominant strategy implementation

MWG, Section 23.C, "The differentiable case", pp. 881-882 (with footnote 26), and Exercises
23.C.9 and 23.C.10(c)-(d) (p. 920).

`K = ℝ`; agent `i`'s valuation `vᵢ(k, θᵢ)` has continuous partial derivatives `∂vᵢ/∂k`,
`∂²vᵢ/∂k²`, `∂²vᵢ/∂k∂θᵢ` with `∂²vᵢ/∂k² < 0` and `∂²vᵢ/∂k∂θᵢ ≠ 0` (`SmallTypeEnv`); types lie
in boxes `θᵢ ∈ [θ̲ᵢ, θ̄ᵢ]`. A profile is `θ : ι → ℝ`, and the derivative of a function of `θ` with
respect to `θᵢ` is the derivative of its slice `s ↦ g(update θ i s)`.

* (23.C.13) `eq_23_C_13`: the first-order condition of truth telling at interior types.
* (23.C.14) `eq_23_C_14`: the transfer formula, by the fundamental theorem of calculus.
* (23.C.15) `eq_23_C_15`: the first-order condition of an efficient project rule.
* Implicit function theorem (p. 882): an efficient `k*` is differentiable in each `θᵢ` at interior
  types, continuous along each coordinate of the box, and `∂k*/∂θᵢ ≠ 0`
  (`efficient_slice_hasDerivAt`, `efficient_slice_continuousOn`, `efficient_slice_deriv_ne_zero`);
  proved with Mathlib's bivariate implicit function theorem.
* The Groves form (p. 882): a strategy-proof `f = (k*, t)` with efficient `k*` and differentiable
  transfers has `tᵢ(θ) = tᵢ(θ̲ᵢ, θ₋ᵢ) + ∑_{j≠i} vⱼ(k*(θ), θⱼ) - ∑_{j≠i} vⱼ(k*(θ̲ᵢ, θ₋ᵢ), θⱼ)`
  (`differentiable_case_groves`), so it is a Groves mechanism, and conversely
  (`differentiable_case_groves_iff`). Footnote 26 (any differentiable `k*`):
  `footnote_23_26`. The proof shows that `tᵢ - ∑_{j≠i} vⱼ(k*(·), θⱼ)` has zero `θᵢ`-derivative.
* Budget balance with `I = 2` (p. 882): impossible (`differentiable_case_no_budget_balance`).
* **Exercise 23.C.9**: with `∂²v/∂k∂θ > 0`, a `C¹` social choice function is strategy-proof iff
  `k` is nondecreasing in each `θᵢ` and the transfers satisfy the integral formula
  (`exercise_23_C_9`).
* **Exercise 23.C.10(c)**: for `I = 2`, `V* = V₁(θ₂) + V₂(θ₁)` forces `∂²V*/∂θ₁∂θ₂ = 0`
  (`exercise_23_C_10c`), and conversely (`exercise_23_C_10c_sufficient`); in the differentiable
  case an efficient, budget balanced, strategy-proof rule forces `V* = ∑ᵢ Vᵢ(θ₋ᵢ)` for any `I ≥ 2`
  (`exercise_23_C_10c_decomposition`); the `I`-fold finite-difference form is
  `mixedDifference_eq_zero`. **(d)**: `exercise_23_C_10d`.

**Departures.** (1) Valuations, the project rule and the transfers are functions on all of `ℝ`
(resp. `ℝ^I`); the box enters through strategy-proofness and efficiency, which are required only
on the box. (2) The `I = 2` impossibility is proved through the decomposition
`V*(θ) = -h₁(θ₂) - h₂(θ₁)` and a strictly nonzero mixed *difference* of `V*`, not through
(23.C.16)-(23.C.17): those take second derivatives of `tᵢ` and `k*`, which need more smoothness
than MWG assume (`f` is only `C¹`, and the implicit function theorem gives `k*` only `C¹` when
`v` is `C²`). Exercise 23.C.10(d) is proved the same way (the finite-difference form of (c)).
(3) Exercise 23.C.9 does not need `∂²v/∂k² < 0`, and its "only if" for monotonicity needs no
differentiability.
-/

namespace MWG.MechanismDesign

open Function Finset

open scoped Topology

/-! ## One-dimensional lemmas -/

/-- **(23.C.13)**, one-dimensional form (MWG, p. 881). If reporting `r ∈ [a, b]` is never better
than reporting the true type `s ∈ (a, b)`, and `k`, `t` are differentiable at `s`, then
`∂v(k(s), s)/∂k · k'(s) + t'(s) = 0`. -/
theorem dc_foc_slice {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x) {k t : ℝ → ℝ} {a b s k' t' : ℝ}
    (hIC : ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s) (hs : s ∈ Set.Ioo a b)
    (hk : HasDerivAt k k' s) (ht : HasDerivAt t t' s) : vk (k s) s * k' + t' = 0 := by
  have hmax : IsLocalMax (fun r => v (k r) s + t r) s :=
    Filter.eventually_of_mem (Icc_mem_nhds hs.1 hs.2) fun r hr => hIC r hr
  exact hmax.hasDerivAt_eq_zero (((hv (k s) s).comp s hk).add ht)

/-- **(23.C.14)**, one-dimensional form (MWG, p. 881). For a `C¹` slice `(k, t)` along which
truth telling is optimal on `[a, b]`, `t(θ) = t(a) - ∫ₐ^θ ∂v(k(s), s)/∂k · k'(s) ds`. -/
theorem dc_integral_slice {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x)
    (hcvk : Continuous fun p : ℝ × ℝ => vk p.1 p.2) {k t : ℝ → ℝ} {a b : ℝ}
    (hk : ContDiff ℝ 1 k) (ht : ContDiff ℝ 1 t)
    (hIC : ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s) :
    ∀ θ ∈ Set.Icc a b, t θ = t a - ∫ s in a..θ, vk (k s) s * deriv k s := by
  intro θ hθ
  have hg : Continuous fun s => vk (k s) s * deriv k s :=
    (hcvk.comp (hk.continuous.prodMk continuous_id)).mul (hk.continuous_deriv_one)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := t)
    (f' := fun s => -(vk (k s) s * deriv k s)) hθ.1 ht.continuous.continuousOn
    (fun x hx => ?_) (hg.neg.intervalIntegrable _ _)
  · rw [intervalIntegral.integral_neg] at hint
    linarith
  · have hx' : x ∈ Set.Ioo a b := ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2⟩
    have hkd := (hk.differentiable (by norm_num) x).hasDerivAt
    have htd := (ht.differentiable (by norm_num) x).hasDerivAt
    have hfoc := dc_foc_slice hv (hIC x (Set.Ioo_subset_Icc_self hx')) hx' hkd htd
    have : deriv t x = -(vk (k x) x * deriv k x) := by linarith
    rw [← this]
    exact htd

/-- A function monotone on `[a, b]` (`a < b`) and differentiable at `x ∈ [a, b]` has
`f'(x) ≥ 0`. -/
theorem dc_deriv_nonneg_of_monotoneOn {k : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hm : MonotoneOn k (Set.Icc a b)) (hx : x ∈ Set.Icc a b) (hd : DifferentiableAt ℝ k x) :
    0 ≤ deriv k x := by
  rw [← hd.derivWithin (uniqueDiffOn_Icc hab x hx)]
  exact hm.derivWithin_nonneg

/-- **Exercise 23.C.9**, one-dimensional form (MWG, p. 920). Let `∂v/∂k` be continuous and
strictly increasing in `θ` on `[a, b]`, and let `k`, `t` be `C¹`. Truth telling is optimal on
`[a, b]` iff `k` is nondecreasing on `[a, b]` and
`t(θ) = t(a) - ∫ₐ^θ ∂v(k(s), s)/∂k · k'(s) ds` on `[a, b]`. -/
theorem dc_sp_slice_iff {v vk : ℝ → ℝ → ℝ} {a b : ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x)
    (hcvk : Continuous fun p : ℝ × ℝ => vk p.1 p.2)
    (hmono : ∀ x, StrictMonoOn (vk x) (Set.Icc a b)) {k t : ℝ → ℝ}
    (hk : ContDiff ℝ 1 k) (ht : ContDiff ℝ 1 t) :
    (∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s) ↔
      MonotoneOn k (Set.Icc a b) ∧
        ∀ θ ∈ Set.Icc a b, t θ = t a - ∫ s in a..θ, vk (k s) s * deriv k s := by
  constructor
  · intro hIC
    refine ⟨fun s hs r hr hsr => ?_, dc_integral_slice hv hcvk hk ht hIC⟩
    rcases hsr.lt_or_eq with hlt | heq
    · by_contra hcon
      rw [not_le] at hcon
      -- `φ(x) = v(x, r) - v(x, s)` is strictly increasing
      have hφ : StrictMono fun x => v x r - v x s := by
        apply strictMono_of_deriv_pos
        intro x
        rw [((hv x r).fun_sub (hv x s)).deriv]
        exact sub_pos.2 (hmono x hs hr hlt)
      have h1 := hIC s hs r hr
      have h2 := hIC r hr s hs
      have h3 := hφ hcon
      simp only at h3
      linarith
    · rw [heq]
  · rintro ⟨hm, hform⟩ s hs r hr
    have hg : Continuous fun x => vk (k x) x * deriv k x :=
      (hcvk.comp (hk.continuous.prodMk continuous_id)).mul (hk.continuous_deriv_one)
    have hgs : Continuous fun x => vk (k x) s * deriv k x :=
      (hcvk.comp (hk.continuous.prodMk continuous_const)).mul (hk.continuous_deriv_one)
    -- `v(k(s), s) - v(k(r), s) = ∫_r^s ∂v(k(x), s)/∂k · k'(x) dx`
    have hv_int : ∫ x in r..s, vk (k x) s * deriv k x = v (k s) s - v (k r) s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => v (k x) s)
        (fun x _ => (hv (k x) s).comp x (hk.differentiable (by norm_num) x).hasDerivAt)
        (hgs.intervalIntegrable _ _)
    -- `t(s) - t(r) = -∫_r^s ∂v(k(x), x)/∂k · k'(x) dx`
    have ht_int : t s - t r = -∫ x in r..s, vk (k x) x * deriv k x := by
      rw [hform s hs, hform r hr, ← intervalIntegral.integral_interval_sub_left
        (hg.intervalIntegrable a s) (hg.intervalIntegrable a r)]
      ring
    have hdiff : 0 ≤ ∫ x in r..s, (vk (k x) s - vk (k x) x) * deriv k x := by
      rcases lt_trichotomy r s with hrs | hrs | hrs
      · have hab : a < b := lt_of_le_of_lt hr.1 (lt_of_lt_of_le hrs hs.2)
        apply intervalIntegral.integral_nonneg hrs.le
        intro x hx
        have hxI : x ∈ Set.Icc a b := ⟨le_trans hr.1 hx.1, le_trans hx.2 hs.2⟩
        apply mul_nonneg
        · exact sub_nonneg.2 ((hmono (k x)).monotoneOn hxI hs hx.2)
        · exact dc_deriv_nonneg_of_monotoneOn hab hm hxI
            (hk.differentiable (by norm_num) x)
      · rw [hrs, intervalIntegral.integral_same]
      · have hab : a < b := lt_of_le_of_lt hs.1 (lt_of_lt_of_le hrs hr.2)
        rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_nonneg hrs.le
        intro x hx
        have hxI : x ∈ Set.Icc a b := ⟨le_trans hs.1 hx.1, le_trans hx.2 hr.2⟩
        have h1 : vk (k x) s ≤ vk (k x) x := (hmono (k x)).monotoneOn hs hxI hx.1
        have h2 := dc_deriv_nonneg_of_monotoneOn hab hm hxI (hk.differentiable (by norm_num) x)
        nlinarith
    have e2 : ∫ x in r..s, (vk (k x) s - vk (k x) x) * deriv k x =
        (∫ x in r..s, vk (k x) s * deriv k x) - ∫ x in r..s, vk (k x) x * deriv k x := by
      rw [← intervalIntegral.integral_sub (hgs.intervalIntegrable r s)
        (hg.intervalIntegrable r s)]
      congr 1
      funext x
      ring
    rw [e2, hv_int] at hdiff
    linarith

/-- The implicit function theorem for a real function of two real variables with continuous
partial derivatives (from Mathlib's `implicitFunctionOfBivariate`): if `∂G/∂x(s₀, x₀) ≠ 0`,
there is `ψ`, strictly differentiable at `s₀` with `ψ'(s₀) = -(∂G/∂s)/(∂G/∂x)`, `ψ(s₀) = x₀`,
and `G(s, ψ(s)) = G(s₀, x₀)` near `s₀`. -/
theorem dc_implicit {G Gs Gx : ℝ → ℝ → ℝ}
    (hGs : ∀ s x, HasDerivAt (fun r => G r x) (Gs s x) s)
    (hGx : ∀ s x, HasDerivAt (fun y => G s y) (Gx s x) x)
    (hcs : Continuous fun p : ℝ × ℝ => Gs p.1 p.2)
    (hcx : Continuous fun p : ℝ × ℝ => Gx p.1 p.2) {s0 x0 : ℝ} (hne : Gx s0 x0 ≠ 0) :
    ∃ ψ : ℝ → ℝ, HasStrictDerivAt ψ (-(Gs s0 x0) / Gx s0 x0) s0 ∧ ψ s0 = x0 ∧
      ∀ᶠ s in 𝓝 s0, G s (ψ s) = G s0 x0 := by
  let u : ℝ × ℝ := (s0, x0)
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun s x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gs s x)
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ :=
    fun s x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gx s x)
  have df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (G · v.2) (f₁ v.1 v.2) v.1 :=
    Filter.Eventually.of_forall fun v => (hGs v.1 v.2).hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (G v.1 ·) (f₂ v.1 v.2) v.2 :=
    Filter.Eventually.of_forall fun v => (hGx v.1 v.2).hasFDerivAt
  have cf₁ : ContinuousAt (Function.uncurry f₁) u :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp hcs).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry f₂) u :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp hcx).continuousAt
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (Gx s0 x0) hne)
  have he : (e : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gx s0 x0) := by
    ext; simp [e]
  have if₂ : (f₂ u.1 u.2).IsInvertible := ⟨e, he⟩
  refine ⟨implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂) df₁ df₂ cf₁ cf₂ if₂, ?_, ?_, ?_⟩
  · have h := (hasStrictFDerivAt_implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂)
      df₁ df₂ cf₁ cf₂ if₂).hasStrictDerivAt
    convert h using 1
    change _ = (-(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gx s0 x0)).inverse ∘L
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Gs s0 x0)) 1
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp [e]
    field_simp
  · have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂)
      df₁ df₂ cf₁ cf₂ if₂).self_of_nhds
    exact h.1 rfl
  · exact eventually_apply_implicitFunctionOfBivariate (f₁ := f₁) (f₂ := f₂) df₁ df₂ cf₁ cf₂ if₂

/-- The implicit function theorem applied to a root function: if `κ(s)` is a root of `G(s, ·)`
for `s ∈ S`, each `G(s, ·)` is injective, and `∂G/∂x(s₀, κ(s₀)) ≠ 0`, then `κ` agrees near `s₀`
(within `S`) with a function strictly differentiable at `s₀` with derivative
`-(∂G/∂s)/(∂G/∂x)`. -/
theorem dc_implicit_root {G Gs Gx : ℝ → ℝ → ℝ}
    (hGs : ∀ s x, HasDerivAt (fun r => G r x) (Gs s x) s)
    (hGx : ∀ s x, HasDerivAt (fun y => G s y) (Gx s x) x)
    (hcs : Continuous fun p : ℝ × ℝ => Gs p.1 p.2)
    (hcx : Continuous fun p : ℝ × ℝ => Gx p.1 p.2) {κ : ℝ → ℝ} {S : Set ℝ}
    (hroot : ∀ s ∈ S, G s (κ s) = 0) (hinj : ∀ s, Injective (G s)) {s0 : ℝ} (hs0 : s0 ∈ S)
    (hne : Gx s0 (κ s0) ≠ 0) :
    ∃ ψ : ℝ → ℝ, HasStrictDerivAt ψ (-(Gs s0 (κ s0)) / Gx s0 (κ s0)) s0 ∧ ψ s0 = κ s0 ∧
      κ =ᶠ[𝓝[S] s0] ψ := by
  obtain ⟨ψ, hψ, hψ0, hev⟩ := dc_implicit hGs hGx hcs hcx hne
  refine ⟨ψ, hψ, hψ0, ?_⟩
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [hev] with s hs hsS
  rw [hroot s0 hs0] at hs
  exact hinj s ((hroot s hsS).trans hs.symm)

/-- A strictly concave function (`S'' < 0`) with `S'(c) = 0` has its unique maximum at `c`. -/
theorem dc_strict_max {S S' S'' : ℝ → ℝ} (hS : ∀ x, HasDerivAt S (S' x) x)
    (hS' : ∀ x, HasDerivAt S' (S'' x) x) (hneg : ∀ x, S'' x < 0) {c : ℝ} (hc : S' c = 0)
    {x : ℝ} (hx : x ≠ c) : S x < S c := by
  have hanti : StrictAnti S' := strictAnti_of_deriv_neg fun y => by
    rw [(hS' y).deriv]; exact hneg y
  have hcont : Continuous S := continuous_iff_continuousAt.2 fun y => (hS y).continuousAt
  rcases hx.lt_or_gt with h | h
  · have hm : StrictMonoOn S (Set.Icc x c) :=
      strictMonoOn_of_deriv_pos (convex_Icc x c) hcont.continuousOn fun y hy => by
        rw [interior_Icc] at hy
        rw [(hS y).deriv, ← hc]
        exact hanti hy.2
    exact hm ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
  · have hm : StrictAntiOn S (Set.Icc c x) :=
      strictAntiOn_of_deriv_neg (convex_Icc c x) hcont.continuousOn fun y hy => by
        rw [interior_Icc] at hy
        rw [(hS y).deriv, ← hc]
        exact hanti hy.1
    exact hm ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h

/-- The Groves form, one-dimensional form (MWG, p. 882). Along a slice on which truth telling
is optimal, if `k` and `t` are continuous on `[a, b]` and differentiable on `(a, b)`, and the
efficiency condition `∂v(k(s), s)/∂k + w'(k(s)) = 0` holds (`w` = the others' total valuation),
then `t - w ∘ k` is constant: `t(θ) = t(a) + w(k(θ)) - w(k(a))`. -/
theorem dc_groves_slice {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x) {w wk : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (wk x) x) {k t : ℝ → ℝ} {a b : ℝ}
    (hkc : ContinuousOn k (Set.Icc a b)) (htc : ContinuousOn t (Set.Icc a b))
    (hkd : ∀ s ∈ Set.Ioo a b, DifferentiableAt ℝ k s)
    (htd : ∀ s ∈ Set.Ioo a b, DifferentiableAt ℝ t s)
    (hIC : ∀ s ∈ Set.Icc a b, ∀ r ∈ Set.Icc a b, v (k r) s + t r ≤ v (k s) s + t s)
    (hfoc : ∀ s ∈ Set.Ioo a b, vk (k s) s + wk (k s) = 0) :
    ∀ θ ∈ Set.Icc a b, t θ = t a + w (k θ) - w (k a) := by
  intro θ hθ
  rcases hθ.1.eq_or_lt with h | h
  · rw [← h]; ring
  · have hwc : Continuous w := continuous_iff_continuousAt.2 fun x => (hw x).continuousAt
    have hsub : Set.Icc a θ ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hθ.2
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => t s - w (k s))
      (fun s => deriv t s - wk (k s) * deriv k s) h
      ((htc.mono hsub).sub (hwc.comp_continuousOn (hkc.mono hsub)))
      (fun x hx => ((htd x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2⟩).hasDerivAt).sub
        ((hw (k x)).comp x (hkd x ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2⟩).hasDerivAt))
    have hc' : c ∈ Set.Ioo a b := ⟨hc.1, lt_of_lt_of_le hc.2 hθ.2⟩
    have h1 := dc_foc_slice hv (hIC c (Set.Ioo_subset_Icc_self hc')) hc'
      (hkd c hc').hasDerivAt (htd c hc').hasDerivAt
    have h2 : vk (k c) c = -wk (k c) := by linarith [hfoc c hc']
    rw [h2] at h1
    have h0 : deriv t c - wk (k c) * deriv k c = 0 := by linarith
    rw [h0, eq_comm, div_eq_zero_iff] at hslope
    rcases hslope with hs | hs
    · linarith
    · exfalso; linarith

/-- The mixed difference of the maximal total valuation is strictly positive when both
valuations have increasing differences between the types used, the maximiser is unique at
`(b₁, b₂)` and the efficient project moves with each type. -/
theorem dc_mixed_pos {w1 w2 : ℝ → ℝ → ℝ} {κ : ℝ → ℝ → ℝ} {a1 b1 a2 b2 : ℝ}
    (hAA : ∀ x, w1 x a1 + w2 x a2 ≤ w1 (κ a1 a2) a1 + w2 (κ a1 a2) a2)
    (hBB : ∀ x, x ≠ κ b1 b2 → w1 x b1 + w2 x b2 < w1 (κ b1 b2) b1 + w2 (κ b1 b2) b2)
    (hm1 : Monotone fun x => w1 x b1 - w1 x a1) (hm2 : Monotone fun x => w2 x b2 - w2 x a2)
    (hne1 : κ a1 b2 ≠ κ b1 b2) (hne2 : κ b1 a2 ≠ κ b1 b2) :
    0 < (w1 (κ b1 b2) b1 + w2 (κ b1 b2) b2) - (w1 (κ a1 b2) a1 + w2 (κ a1 b2) b2) -
      (w1 (κ b1 a2) b1 + w2 (κ b1 a2) a2) + (w1 (κ a1 a2) a1 + w2 (κ a1 a2) a2) := by
  rcases le_or_gt (κ a1 b2) (κ b1 a2) with h | h
  · have e1 := hm2 h
    have e2 := hBB (κ b1 a2) hne2
    have e3 := hAA (κ a1 b2)
    simp only at e1
    linarith
  · have e1 := hm1 h.le
    have e2 := hBB (κ a1 b2) hne1
    have e3 := hAA (κ b1 a2)
    simp only at e1
    linarith

/-- If `∂v/∂k(x, a) < ∂v/∂k(x, b)` for every `x`, then `v(x, b) - v(x, a)` is nondecreasing in
`x` (increasing differences). -/
theorem dc_delta_monotone {v vk : ℝ → ℝ → ℝ}
    (hv : ∀ x θ, HasDerivAt (fun y => v y θ) (vk x θ) x) {a b : ℝ}
    (hlt : ∀ x, vk x a < vk x b) : Monotone fun x => v x b - v x a :=
  monotone_of_deriv_nonneg (fun x => ((hv x b).sub (hv x a)).differentiableAt) fun x => by
    rw [((hv x b).fun_sub (hv x a)).deriv]
    exact (sub_pos.2 (hlt x)).le

/-- A continuous function on `ℝ × ℝ` that never vanishes has a constant sign. -/
theorem dc_sign_of_ne {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hne : ∀ p, f p ≠ 0) :
    (∀ p, 0 < f p) ∨ ∀ p, f p < 0 := by
  rcases (hne 0).lt_or_gt with h0 | h0
  · right
    intro p
    rcases (hne p).lt_or_gt with hp | hp
    · exact hp
    · obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ (0 : ℝ × ℝ))
        (Set.mem_univ p) hf.continuousOn ⟨h0.le, hp.le⟩
      exact absurd hz (hne z)
  · left
    intro p
    rcases (hne p).lt_or_gt with hp | hp
    · obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ p)
        (Set.mem_univ (0 : ℝ × ℝ)) hf.continuousOn ⟨hp.le, h0.le⟩
      exact absurd hz (hne z)
    · exact hp

/-! ## The environment -/

/-- **The differentiable case** (MWG, p. 881). `K = ℝ`; agent `i`'s valuation `vᵢ(k, θᵢ)` has
partial derivatives `vkᵢ = ∂vᵢ/∂k`, `vkkᵢ = ∂²vᵢ/∂k²`, `vkθᵢ = ∂²vᵢ/∂k∂θᵢ`, continuous in
`(k, θᵢ)`, with `∂²vᵢ/∂k² < 0` and `∂²vᵢ/∂k∂θᵢ ≠ 0` everywhere. (This is what MWG use of
"`vᵢ` twice continuously differentiable".) -/
structure SmallTypeEnv (ι : Type*) where
  /-- The valuation `vᵢ(k, θᵢ)`. -/
  v : ι → ℝ → ℝ → ℝ
  /-- `∂vᵢ/∂k`. -/
  vk : ι → ℝ → ℝ → ℝ
  /-- `∂²vᵢ/∂k²`. -/
  vkk : ι → ℝ → ℝ → ℝ
  /-- `∂²vᵢ/∂k∂θᵢ`. -/
  vkθ : ι → ℝ → ℝ → ℝ
  hasDerivAt_v : ∀ i x θ, HasDerivAt (fun y => v i y θ) (vk i x θ) x
  hasDerivAt_vk : ∀ i x θ, HasDerivAt (fun y => vk i y θ) (vkk i x θ) x
  hasDerivAt_vkθ : ∀ i x θ, HasDerivAt (fun s => vk i x s) (vkθ i x θ) θ
  continuous_vk : ∀ i, Continuous fun p : ℝ × ℝ => vk i p.1 p.2
  continuous_vkk : ∀ i, Continuous fun p : ℝ × ℝ => vkk i p.1 p.2
  continuous_vkθ : ∀ i, Continuous fun p : ℝ × ℝ => vkθ i p.1 p.2
  vkk_neg : ∀ i x θ, vkk i x θ < 0
  vkθ_ne : ∀ i x θ, vkθ i x θ ≠ 0

/-- The quadratic environment `vᵢ(k, θᵢ) = θᵢk - k²/2` (`∂²v/∂k² = -1`, `∂²v/∂k∂θ = 1`): an
instance of `SmallTypeEnv`. -/
noncomputable def quadEnv (ι : Type*) : SmallTypeEnv ι where
  v := fun _ x θ => θ * x - x ^ 2 / 2
  vk := fun _ x θ => θ - x
  vkk := fun _ _ _ => -1
  vkθ := fun _ _ _ => 1
  hasDerivAt_v := fun _ x θ => by
    have h := ((hasDerivAt_id x).const_mul θ).fun_sub ((hasDerivAt_pow 2 x).div_const 2)
    convert h using 1
    · funext y; simp only [id]
    · norm_num
  hasDerivAt_vk := fun _ x θ => by simpa using (hasDerivAt_id x).const_sub θ
  hasDerivAt_vkθ := fun _ x θ => by simpa using (hasDerivAt_id θ).sub_const x
  continuous_vk := fun _ => by fun_prop
  continuous_vkk := fun _ => continuous_const
  continuous_vkθ := fun _ => continuous_const
  vkk_neg := fun _ _ _ => by norm_num
  vkθ_ne := fun _ _ _ => one_ne_zero

variable {ι : Type*}

/-- **The differentiable case** (MWG, p. 881). The box of types: `θᵢ ∈ [θ̲ᵢ, θ̄ᵢ]` for all `i`. -/
def InBox (lo hi : ι → ℝ) (θ : ι → ℝ) : Prop :=
  ∀ i, θ i ∈ Set.Icc (lo i) (hi i)

/-- Changing one coordinate within its interval stays in the box. -/
theorem inBox_update [DecidableEq ι] {lo hi θ : ι → ℝ} (hθ : InBox lo hi θ) {i : ι} {s : ℝ}
    (hs : s ∈ Set.Icc (lo i) (hi i)) : InBox lo hi (update θ i s) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hs
  · simpa [update_of_ne h] using hθ j

/-- **Definition 23.C.3** on the box (MWG, p. 871): `f = (k, t)` with `K = ℝ` and quasilinear
utilities `vᵢ(k, θᵢ) + tᵢ` is strategy-proof when types range over the box. -/
def StrategyProofOnBox [DecidableEq ι] (v : ι → ℝ → ℝ → ℝ) (lo hi : ι → ℝ)
    (k : (ι → ℝ) → ℝ) (t : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ i θ, InBox lo hi θ → ∀ s ∈ Set.Icc (lo i) (hi i),
    v i (k (update θ i s)) (θ i) + t (update θ i s) i ≤ v i (k θ) (θ i) + t θ i

/-- **(23.C.7)** on the box (MWG, p. 877): `k` is efficient at every profile of the box. -/
def EfficientOnBox [Fintype ι] (v : ι → ℝ → ℝ → ℝ) (lo hi : ι → ℝ) (k : (ι → ℝ) → ℝ) :
    Prop :=
  ∀ θ, InBox lo hi θ → ∀ x, ∑ i, v i x (θ i) ≤ ∑ i, v i (k θ) (θ i)

/-- An efficient project rule (23.C.7) on all profiles is efficient on the box. -/
theorem EfficientProject.efficientOnBox [Fintype ι] {v : ι → ℝ → ℝ → ℝ}
    {k : (ι → ℝ) → ℝ} (hk : EfficientProject v k) (lo hi : ι → ℝ) :
    EfficientOnBox v lo hi k :=
  fun θ _ x => hk θ x

/-- `StrategyProofOnBox` is `StrategyProof` (Definition 23.C.3) for the quasilinear utilities
`qlU` with type sets `Θᵢ = [θ̲ᵢ, θ̄ᵢ]`. -/
theorem strategyProofOnBox_iff [DecidableEq ι] (v : ι → ℝ → ℝ → ℝ) (m : ι → ℝ)
    (lo hi : ι → ℝ) (k : (ι → ℝ) → ℝ) (t : (ι → ℝ) → ι → ℝ) :
    StrategyProofOnBox v lo hi k t ↔
      StrategyProof (Θ := fun i => Set.Icc (lo i) (hi i))
        (qlU (fun i x (θi : Set.Icc (lo i) (hi i)) => v i x θi) m)
        (fun θ => (k fun i => θ i, t fun i => θ i)) := by
  have hupd : ∀ (θ : (i : ι) → Set.Icc (lo i) (hi i)) i (a : Set.Icc (lo i) (hi i)),
      (fun j => (update θ i a j : ℝ)) = update (fun j => (θ j : ℝ)) i a := by
    intro θ i a
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [update_of_ne h]
  constructor
  · intro hSP i θ θh
    simp only [qlU, hupd]
    have := hSP i (fun j => θ j) (fun j => (θ j).2) θh θh.2
    linarith
  · intro hSP i θ hθ s hs
    have := hSP i (fun j => ⟨θ j, hθ j⟩) ⟨s, hs⟩
    simp only [qlU, hupd] at this
    linarith

/-- Strategy-proofness on the box gives optimality of truth telling along every slice. -/
theorem sp_slice [DecidableEq ι] {v : ι → ℝ → ℝ → ℝ} {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ}
    {t : (ι → ℝ) → ι → ℝ} (hSP : StrategyProofOnBox v lo hi k t) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) :
    ∀ s ∈ Set.Icc (lo i) (hi i), ∀ r ∈ Set.Icc (lo i) (hi i),
      v i (k (update θ i r)) s + t (update θ i r) i ≤
        v i (k (update θ i s)) s + t (update θ i s) i := by
  intro s hs r hr
  have := hSP i (update θ i s) (inBox_update hθ hs) r hr
  simpa only [update_idem, update_self] using this

/-- `∑ⱼ gⱼ((θ with θᵢ = s)ⱼ) = gᵢ(s) + ∑_{j≠i} gⱼ(θⱼ)`. -/
theorem sum_update_split [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι)
    (s : ℝ) : ∑ j, g j (update θ i s j) = g i s + ∑ j ∈ univ.erase i, g j (θ j) := by
  rw [← add_sum_erase _ _ (mem_univ i), update_self]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **(23.C.13)** (MWG, p. 881). If `f = (k, t)` is strategy-proof on the box and `k`, `tᵢ` are
differentiable in `θᵢ` at an interior type, then
`∂vᵢ(k(θ), θᵢ)/∂k · ∂k(θ)/∂θᵢ + ∂tᵢ(θ)/∂θᵢ = 0`. -/
theorem eq_23_C_13 [DecidableEq ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ}
    {t : (ι → ℝ) → ι → ℝ} (hSP : StrategyProofOnBox E.v lo hi k t) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) {i : ι} (hθi : θ i ∈ Set.Ioo (lo i) (hi i)) {dk dt : ℝ}
    (hk : HasDerivAt (fun s => k (update θ i s)) dk (θ i))
    (ht : HasDerivAt (fun s => t (update θ i s) i) dt (θ i)) :
    E.vk i (k θ) (θ i) * dk + dt = 0 := by
  have h := dc_foc_slice (E.hasDerivAt_v i) (k := fun s => k (update θ i s))
    (t := fun s => t (update θ i s) i)
    (fun r hr => sp_slice hSP hθ i (θ i) (Set.Ioo_subset_Icc_self hθi) r hr) hθi hk ht
  simpa only [update_eq_self] using h

/-- **(23.C.14)** (MWG, p. 881). If `f = (k, t)` is `C¹` and strategy-proof on the box, then
`tᵢ(θᵢ, θ₋ᵢ) = tᵢ(θ̲ᵢ, θ₋ᵢ) - ∫_{θ̲ᵢ}^{θᵢ} ∂vᵢ(k(s, θ₋ᵢ), s)/∂k · ∂k(s, θ₋ᵢ)/∂s ds`. -/
theorem eq_23_C_14 [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ}
    {t : (ι → ℝ) → ι → ℝ} (hk : ContDiff ℝ 1 k) (ht : ∀ i, ContDiff ℝ 1 fun θ => t θ i)
    (hSP : StrategyProofOnBox E.v lo hi k t) (i : ι) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    t θ i = t (update θ i (lo i)) i -
      ∫ s in lo i..θ i, E.vk i (k (update θ i s)) s * deriv (fun y => k (update θ i y)) s := by
  have h := dc_integral_slice (E.hasDerivAt_v i) (E.continuous_vk i)
    (k := fun s => k (update θ i s)) (t := fun s => t (update θ i s) i)
    (hk.comp (contDiff_update 1 θ i)) ((ht i).comp (contDiff_update 1 θ i))
    (sp_slice hSP hθ i) (θ i) (hθ i)
  simpa only [update_eq_self] using h

/-- (23.C.15) for any valuations differentiable in `k`: an efficient project rule satisfies
`∑ⱼ ∂vⱼ(k(θ), θⱼ)/∂k = 0` on the box. -/
theorem efficient_foc [Fintype ι] {v vk : ι → ℝ → ℝ → ℝ}
    (hv : ∀ i x θ, HasDerivAt (fun y => v i y θ) (vk i x θ) x) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox v lo hi k) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    ∑ j, vk j (k θ) (θ j) = 0 := by
  have hmax : IsLocalMax (fun x => ∑ j, v j x (θ j)) (k θ) :=
    Filter.Eventually.of_forall fun x => hk θ hθ x
  exact hmax.hasDerivAt_eq_zero (HasDerivAt.fun_sum fun j _ => hv j (k θ) (θ j))

/-- **(23.C.15)** (MWG, p. 882). An efficient project rule satisfies
`∑ⱼ ∂vⱼ(k*(θ), θⱼ)/∂k = 0` at every profile of the box. -/
theorem eq_23_C_15 [Fintype ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ}
    (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    ∑ j, E.vk j (k θ) (θ j) = 0 :=
  efficient_foc E.hasDerivAt_v hk hθ

/-- **Exercise 23.C.9** (MWG, p. 920). Suppose `∂²vᵢ/∂k∂θᵢ > 0`. A `C¹` social choice function
`f = (k, t)` is truthfully implementable in dominant strategies (on the box) iff for all `i`,
`k(θ)` is nondecreasing in `θᵢ` and
`tᵢ(θᵢ, θ₋ᵢ) = tᵢ(θ̲ᵢ, θ₋ᵢ) - ∫_{θ̲ᵢ}^{θᵢ} ∂vᵢ(k(s, θ₋ᵢ), s)/∂k · ∂k(s, θ₋ᵢ)/∂s ds`. -/
theorem exercise_23_C_9 [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    (hpos : ∀ i x θ, 0 < E.vkθ i x θ)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ} (hk : ContDiff ℝ 1 k)
    (ht : ∀ i, ContDiff ℝ 1 fun θ => t θ i) :
    StrategyProofOnBox E.v lo hi k t ↔ ∀ i θ, InBox lo hi θ →
      MonotoneOn (fun s => k (update θ i s)) (Set.Icc (lo i) (hi i)) ∧
        t θ i = t (update θ i (lo i)) i - ∫ s in lo i..θ i,
          E.vk i (k (update θ i s)) s * deriv (fun y => k (update θ i y)) s := by
  have hmono : ∀ i x, StrictMonoOn (E.vk i x) (Set.Icc (lo i) (hi i)) := fun i x =>
    (strictMono_of_deriv_pos fun θ => by
      rw [(E.hasDerivAt_vkθ i x θ).deriv]; exact hpos i x θ).strictMonoOn _
  have hslice := fun i θ => dc_sp_slice_iff (E.hasDerivAt_v i) (E.continuous_vk i) (hmono i)
    (k := fun s => k (update θ i s)) (t := fun s => t (update θ i s) i)
    (hk.comp (contDiff_update 1 θ i)) ((ht i).comp (contDiff_update 1 θ i))
  constructor
  · intro hSP i θ hθ
    have h := (hslice i θ).1 (sp_slice hSP hθ i)
    refine ⟨h.1, ?_⟩
    have h2 := h.2 (θ i) (hθ i)
    simpa only [update_eq_self] using h2
  · intro h i θ hθ s hs
    have hIC := (hslice i θ).2 ⟨(h i θ hθ).1, fun y hy => by
      have h2 := (h i (update θ i y) (inBox_update hθ hy)).2
      simpa only [update_idem, update_self] using h2⟩
    have h3 := hIC (θ i) (hθ i) s hs
    simpa only [update_eq_self] using h3

/-- **Footnote 26** (MWG, p. 882). The Groves form for any project rule that is efficient and
differentiable (continuous along each coordinate of the box and differentiable at interior
types), with valuations differentiable in `k` and differentiable transfers: if `f = (k, t)` is
strategy-proof on the box, then
`tᵢ(θ) = tᵢ(θ̲ᵢ, θ₋ᵢ) + ∑_{j≠i} vⱼ(k(θ), θⱼ) - ∑_{j≠i} vⱼ(k(θ̲ᵢ, θ₋ᵢ), θⱼ)`.
(No concavity or single-crossing assumption is used.) -/
theorem footnote_23_26 [Fintype ι] [DecidableEq ι] {v vk : ι → ℝ → ℝ → ℝ}
    (hv : ∀ i x θ, HasDerivAt (fun y => v i y θ) (vk i x θ) x) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ} (hk : EfficientOnBox v lo hi k)
    (hSP : StrategyProofOnBox v lo hi k t)
    (hkc : ∀ i θ, InBox lo hi θ →
      ContinuousOn (fun s => k (update θ i s)) (Set.Icc (lo i) (hi i)))
    (hkd : ∀ i θ, InBox lo hi θ → ∀ s ∈ Set.Ioo (lo i) (hi i),
      DifferentiableAt ℝ (fun s => k (update θ i s)) s)
    (ht : ∀ i, Differentiable ℝ fun θ => t θ i) (i : ι) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    t θ i = t (update θ i (lo i)) i + ∑ j ∈ univ.erase i, v j (k θ) (θ j) -
      ∑ j ∈ univ.erase i, v j (k (update θ i (lo i))) (θ j) := by
  have hupd : Differentiable ℝ (update θ i) :=
    (contDiff_update 1 θ i).differentiable (by norm_num)
  have htd : Differentiable ℝ fun s => t (update θ i s) i := (ht i).comp hupd
  have h := dc_groves_slice (hv i) (w := fun x => ∑ j ∈ univ.erase i, v j x (θ j))
    (wk := fun x => ∑ j ∈ univ.erase i, vk j x (θ j))
    (fun x => HasDerivAt.fun_sum fun j _ => hv j x (θ j)) (hkc i θ hθ)
    htd.continuous.continuousOn (hkd i θ hθ) (fun s _ => htd s) (sp_slice hSP hθ i)
    (fun s hs => by
      have h0 := efficient_foc hv hk (inBox_update hθ (Set.Ioo_subset_Icc_self hs))
      rwa [sum_update_split (fun j x => vk j (k (update θ i s)) x)] at h0)
    (θ i) (hθ i)
  simp only [update_eq_self] at h
  exact h

/-- The others' types are unchanged by the update of `θᵢ`. -/
theorem sum_erase_update [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (θ : ι → ℝ) (i : ι)
    (s : ℝ) : ∑ j ∈ univ.erase i, g j (update θ i s j) = ∑ j ∈ univ.erase i, g j (θ j) :=
  sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Implicit function theorem** (MWG, p. 882). In the differentiable case, an efficient
project rule `k*` agrees, along the `θᵢ`-coordinate through any profile of the box, with a
function strictly differentiable at `θᵢ` with derivative
`∂k*/∂θᵢ = -(∂²vᵢ/∂k∂θᵢ)/(∑ⱼ ∂²vⱼ/∂k²)`. -/
theorem efficient_slice_implicit [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) {s0 : ℝ} (hs0 : s0 ∈ Set.Icc (lo i) (hi i)) :
    ∃ ψ : ℝ → ℝ, HasStrictDerivAt ψ (-(E.vkθ i (k (update θ i s0)) s0) /
        (E.vkk i (k (update θ i s0)) s0 +
          ∑ j ∈ univ.erase i, E.vkk j (k (update θ i s0)) (θ j))) s0 ∧
      ψ s0 = k (update θ i s0) ∧
      (fun s => k (update θ i s)) =ᶠ[𝓝[Set.Icc (lo i) (hi i)] s0] ψ := by
  have hGx : ∀ s x, HasDerivAt (fun y => E.vk i y s + ∑ j ∈ univ.erase i, E.vk j y (θ j))
      (E.vkk i x s + ∑ j ∈ univ.erase i, E.vkk j x (θ j)) x := fun s x =>
    (E.hasDerivAt_vk i x s).add (HasDerivAt.fun_sum fun j _ => E.hasDerivAt_vk j x (θ j))
  have hneg : ∀ s x, E.vkk i x s + ∑ j ∈ univ.erase i, E.vkk j x (θ j) < 0 := fun s x =>
    add_neg_of_neg_of_nonpos (E.vkk_neg i x s)
      (sum_nonpos fun j _ => (E.vkk_neg j x (θ j)).le)
  have hinj : ∀ s, Injective fun y => E.vk i y s + ∑ j ∈ univ.erase i, E.vk j y (θ j) :=
    fun s => (strictAnti_of_deriv_neg fun x => by
      rw [(hGx s x).deriv]; exact hneg s x).injective
  have hcx : Continuous fun p : ℝ × ℝ =>
      E.vkk i p.2 p.1 + ∑ j ∈ univ.erase i, E.vkk j p.2 (θ j) :=
    ((E.continuous_vkk i).comp continuous_swap).add (continuous_finsetSum _ fun j _ =>
      (E.continuous_vkk j).comp (continuous_snd.prodMk continuous_const))
  obtain ⟨ψ, h1, h2, h3⟩ := dc_implicit_root
    (G := fun s x => E.vk i x s + ∑ j ∈ univ.erase i, E.vk j x (θ j))
    (fun s x => (E.hasDerivAt_vkθ i x s).add_const _) hGx
    ((E.continuous_vkθ i).comp continuous_swap) hcx
    (κ := fun s => k (update θ i s)) (S := Set.Icc (lo i) (hi i))
    (fun s hs => by
      have h0 := efficient_foc E.hasDerivAt_v hk (inBox_update hθ hs)
      rwa [sum_update_split (fun j x => E.vk j (k (update θ i s)) x)] at h0)
    hinj hs0 (hneg s0 _).ne
  exact ⟨ψ, h1, h2, h3⟩

/-- **Implicit function theorem** (MWG, p. 882): an efficient `k*` is continuous along each
coordinate of the box. -/
theorem efficient_slice_continuousOn [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) :
    ContinuousOn (fun s => k (update θ i s)) (Set.Icc (lo i) (hi i)) := by
  intro s0 hs0
  obtain ⟨ψ, h1, h2, h3⟩ := efficient_slice_implicit E hk hθ i hs0
  exact h1.hasDerivAt.continuousAt.continuousWithinAt.congr_of_eventuallyEq h3 h2.symm

/-- **Implicit function theorem** (MWG, p. 882): at interior types an efficient `k*` is
differentiable in `θᵢ`, with `∂k*/∂θᵢ = -(∂²vᵢ/∂k∂θᵢ)/(∑ⱼ ∂²vⱼ/∂k²)`. -/
theorem efficient_slice_hasDerivAt [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) {s0 : ℝ} (hs0 : s0 ∈ Set.Ioo (lo i) (hi i)) :
    HasDerivAt (fun s => k (update θ i s)) (-(E.vkθ i (k (update θ i s0)) s0) /
        (E.vkk i (k (update θ i s0)) s0 +
          ∑ j ∈ univ.erase i, E.vkk j (k (update θ i s0)) (θ j))) s0 := by
  obtain ⟨ψ, h1, -, h3⟩ := efficient_slice_implicit E hk hθ i (Set.Ioo_subset_Icc_self hs0)
  rw [nhdsWithin_eq_nhds.2 (Icc_mem_nhds hs0.1 hs0.2)] at h3
  exact h1.hasDerivAt.congr_of_eventuallyEq h3

/-- **Implicit function theorem** (MWG, p. 882): `∂k*(θ)/∂θᵢ ≠ 0` at interior types. -/
theorem efficient_slice_deriv_ne_zero [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ}
    (hθ : InBox lo hi θ) (i : ι) (hθi : θ i ∈ Set.Ioo (lo i) (hi i)) :
    deriv (fun s => k (update θ i s)) (θ i) ≠ 0 := by
  rw [(efficient_slice_hasDerivAt E hk hθ i hθi).deriv]
  have hneg : E.vkk i (k (update θ i (θ i))) (θ i) +
      ∑ j ∈ univ.erase i, E.vkk j (k (update θ i (θ i))) (θ j) < 0 :=
    add_neg_of_neg_of_nonpos (E.vkk_neg _ _ _) (sum_nonpos fun j _ => (E.vkk_neg _ _ _).le)
  exact div_ne_zero (neg_ne_zero.2 (E.vkθ_ne _ _ _)) hneg.ne

/-- **The Groves form in the differentiable case** (MWG, p. 882). If `f = (k*, t)` with `k*`
efficient and differentiable transfers is strategy-proof on the box, then
`tᵢ(θ) = tᵢ(θ̲ᵢ, θ₋ᵢ) + ∑_{j≠i} vⱼ(k*(θ), θⱼ) - ∑_{j≠i} vⱼ(k*(θ̲ᵢ, θ₋ᵢ), θⱼ)`. The
differentiability of `k*` comes from the implicit function theorem. -/
theorem differentiable_case_groves [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (hSP : StrategyProofOnBox E.v lo hi k t)
    (ht : ∀ i, Differentiable ℝ fun θ => t θ i) (i : ι) {θ : ι → ℝ} (hθ : InBox lo hi θ) :
    t θ i = t (update θ i (lo i)) i + ∑ j ∈ univ.erase i, E.v j (k θ) (θ j) -
      ∑ j ∈ univ.erase i, E.v j (k (update θ i (lo i))) (θ j) :=
  footnote_23_26 E.hasDerivAt_v hk hSP (fun i _ hθ => efficient_slice_continuousOn E hk hθ i)
    (fun i _ hθ _ hs => (efficient_slice_hasDerivAt E hk hθ i hs).differentiableAt) ht i hθ

/-- **Proposition 23.C.4** on the box (MWG, p. 877): a Groves mechanism is strategy-proof on the
box. -/
theorem groves_strategyProofOnBox [Fintype ι] [DecidableEq ι] {v : ι → ℝ → ℝ → ℝ}
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox v lo hi k)
    {h : ι → (ι → ℝ) → ℝ} (hh : IndepOwn h) :
    StrategyProofOnBox v lo hi k (grovesTransfer v k h) := by
  intro i θ hθ s _
  simp only [grovesTransfer]
  rw [hh, sum_erase_update (fun j x => v j (k (update θ i s)) x)]
  have e1 := (add_sum_erase univ (fun j => v j (k (update θ i s)) (θ j)) (mem_univ i)).symm
  have e2 := (add_sum_erase univ (fun j => v j (k θ) (θ j)) (mem_univ i)).symm
  have := hk θ hθ (k (update θ i s))
  linarith

/-- **The Groves characterisation in the differentiable case** (MWG, p. 882): with `k*`
efficient and differentiable transfers, `f = (k*, t)` is strategy-proof on the box iff it is a
Groves mechanism there, i.e. `tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ) + hᵢ(θ₋ᵢ)` (23.C.8). -/
theorem differentiable_case_groves_iff [Fintype ι] [DecidableEq ι] (E : SmallTypeEnv ι)
    {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (ht : ∀ i, Differentiable ℝ fun θ => t θ i) :
    StrategyProofOnBox E.v lo hi k t ↔ ∃ h : ι → (ι → ℝ) → ℝ, IndepOwn h ∧
      ∀ θ, InBox lo hi θ → t θ = grovesTransfer E.v k h θ := by
  constructor
  · intro hSP
    refine ⟨fun i θ => t (update θ i (lo i)) i -
      ∑ j ∈ univ.erase i, E.v j (k (update θ i (lo i))) (θ j), fun i θ a => ?_,
      fun θ hθ => funext fun i => ?_⟩
    · simp only [update_idem]
      rw [sum_erase_update (fun j x => E.v j (k (update θ i (lo i))) x)]
    · rw [differentiable_case_groves E hk hSP ht i hθ]
      simp only [grovesTransfer]
      ring
  · rintro ⟨h, hh, hth⟩ i θ hθ s hs
    rw [hth θ hθ, hth _ (inBox_update hθ hs)]
    exact groves_strategyProofOnBox hk hh i θ hθ s hs

/-- **Exercise 23.C.10(c)** (MWG, p. 920), the decomposition in the differentiable case: with
`I ≥ 2`, if `f = (k*, t)` (efficient `k*`, differentiable transfers) is strategy-proof and budget
balanced on the box, then `V*(θ) = ∑ᵢ vᵢ(k*(θ), θᵢ) = ∑ᵢ Vᵢ(θ₋ᵢ)` on the box. -/
theorem exercise_23_C_10c_decomposition [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (E : SmallTypeEnv ι) {lo hi : ι → ℝ} {k : (ι → ℝ) → ℝ} {t : (ι → ℝ) → ι → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (ht : ∀ i, Differentiable ℝ fun θ => t θ i)
    (hSP : StrategyProofOnBox E.v lo hi k t) (hBB : ∀ θ, InBox lo hi θ → ∑ i, t θ i = 0) :
    ∃ V : ι → (ι → ℝ) → ℝ, IndepOwn V ∧
      ∀ θ, InBox lo hi θ → ∑ i, E.v i (k θ) (θ i) = ∑ i, V i θ := by
  obtain ⟨h, hh, hth⟩ := (differentiable_case_groves_iff E hk ht).1 hSP
  have hI' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hI
  refine ⟨fun i θ => -h i θ / ((Fintype.card ι : ℝ) - 1), fun i θ a => by simp [hh i θ a],
    fun θ hθ => ?_⟩
  have h0 := hBB θ hθ
  rw [hth θ hθ, sum_grovesTransfer] at h0
  have hne : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by linarith
  rw [← sum_div, sum_neg_distrib, eq_div_iff hne]
  linarith

/-- **Exercise 23.C.10(c)** (MWG, p. 920), `I = 2`: if `V*(θ₁, θ₂) = V₁(θ₂) + V₂(θ₁)` then
`∂²V*/∂θ₁∂θ₂ = 0` everywhere. -/
theorem exercise_23_C_10c {F : ℝ → ℝ → ℝ} {A B : ℝ → ℝ} (h : ∀ x y, F x y = A y + B x)
    (x y : ℝ) : deriv (fun y' => deriv (fun x' => F x' y') x) y = 0 := by
  simp only [h, deriv_const_add, deriv_const]

/-- **Exercise 23.C.10(c)** (MWG, p. 920), "(In fact, this is a sufficient condition as
well.)", `I = 2`: if `∂²V*/∂θ₁∂θ₂ = 0` everywhere (with the partial derivatives existing), then
`V*(θ₁, θ₂) = V₁(θ₂) + V₂(θ₁)`; by Exercise 23.C.10(a) (`exercise_23_C_10a_if`) an efficient,
budget balanced, strategy-proof rule then exists. -/
theorem exercise_23_C_10c_sufficient {F Fx Fxy : ℝ → ℝ → ℝ}
    (hF : ∀ x y, HasDerivAt (fun x' => F x' y) (Fx x y) x)
    (hFx : ∀ x y, HasDerivAt (fun y' => Fx x y') (Fxy x y) y) (h0 : ∀ x y, Fxy x y = 0) :
    ∃ A B : ℝ → ℝ, ∀ x y, F x y = A y + B x := by
  have hc : ∀ x y, Fx x y = Fx x 0 := fun x y =>
    is_const_of_deriv_eq_zero (f := fun y' => Fx x y')
      (fun y' => (hFx x y').differentiableAt) (fun y' => by rw [(hFx x y').deriv, h0]) y 0
  refine ⟨fun y => F 0 y - F 0 0, fun x => F x 0, fun x y => ?_⟩
  have := is_const_of_deriv_eq_zero (f := fun x' => F x' y - F x' 0)
    (fun x' => ((hF x' y).sub (hF x' 0)).differentiableAt)
    (fun x' => by rw [((hF x' y).fun_sub (hF x' 0)).deriv, hc x' y, sub_self]) x 0
  linarith

/-- Two-agent profiles: changing agent 1's type (index `0`). -/
theorem vec2_update0 (x y z : ℝ) : update ![x, y] 0 z = ![z, y] := by
  funext j; fin_cases j <;> rfl

/-- Two-agent profiles: changing agent 2's type (index `1`). -/
theorem vec2_update1 (x y z : ℝ) : update ![x, y] 1 z = ![x, z] := by
  funext j; fin_cases j <;> rfl

/-- A two-agent profile is in the box when each type is in its interval. -/
theorem vec2_inBox {lo hi : Fin 2 → ℝ} {x y : ℝ} (hx : x ∈ Set.Icc (lo 0) (hi 0))
    (hy : y ∈ Set.Icc (lo 1) (hi 1)) : InBox lo hi ![x, y] := by
  intro j; fin_cases j <;> simpa

/-- In the differentiable case, for each agent there are two types `a ≠ b` in the box with
`∂vᵢ/∂k(x, a) < ∂vᵢ/∂k(x, b)` for every `x` (by the constant sign of `∂²vᵢ/∂k∂θᵢ`). -/
theorem smallTypeEnv_exists_pair (E : SmallTypeEnv ι) (i : ι) {lo hi : ℝ} (hlt : lo < hi) :
    ∃ a b, a ∈ Set.Icc lo hi ∧ b ∈ Set.Icc lo hi ∧ a ≠ b ∧ ∀ x, E.vk i x a < E.vk i x b := by
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlt.le⟩
  have hhi : hi ∈ Set.Icc lo hi := ⟨hlt.le, le_rfl⟩
  rcases dc_sign_of_ne (E.continuous_vkθ i) (fun p => E.vkθ_ne i p.1 p.2) with h | h
  · refine ⟨lo, hi, hlo, hhi, hlt.ne, fun x => ?_⟩
    exact strictMono_of_deriv_pos (fun θ => by
      rw [(E.hasDerivAt_vkθ i x θ).deriv]; exact h (x, θ)) hlt
  · refine ⟨hi, lo, hhi, hlo, hlt.ne', fun x => ?_⟩
    exact strictAnti_of_deriv_neg (fun θ => by
      rw [(E.hasDerivAt_vkθ i x θ).deriv]; exact h (x, θ)) hlt

/-- In the differentiable case the efficient total valuation has a unique maximiser. -/
theorem smallTypeEnv_strict_max [Fintype ι] [Nonempty ι] (E : SmallTypeEnv ι) {lo hi : ι → ℝ}
    {k : (ι → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) {θ : ι → ℝ} (hθ : InBox lo hi θ)
    {x : ℝ} (hx : x ≠ k θ) : ∑ i, E.v i x (θ i) < ∑ i, E.v i (k θ) (θ i) :=
  dc_strict_max (S := fun y => ∑ i, E.v i y (θ i)) (S' := fun y => ∑ i, E.vk i y (θ i))
    (S'' := fun y => ∑ i, E.vkk i y (θ i))
    (fun y => HasDerivAt.fun_sum fun i _ => E.hasDerivAt_v i y (θ i))
    (fun y => HasDerivAt.fun_sum fun i _ => E.hasDerivAt_vk i y (θ i))
    (fun y => sum_neg (fun i _ => E.vkk_neg i y (θ i)) univ_nonempty)
    (eq_23_C_15 E hk hθ) hx

/-- **Exercise 23.C.10(d)** (MWG, p. 920). Under the small-type assumptions with `I = 2`, the
maximal total valuation `V*` of an efficient project rule is not of the form `V₁(θ₂) + V₂(θ₁)`
on any box with nondegenerate type intervals: its mixed difference over suitable corner types
is nonzero (the finite-difference form of (c)). -/
theorem exercise_23_C_10d (E : SmallTypeEnv (Fin 2)) {lo hi : Fin 2 → ℝ}
    (hlt : ∀ i, lo i < hi i) {k : (Fin 2 → ℝ) → ℝ} (hk : EfficientOnBox E.v lo hi k) :
    ¬∃ V : Fin 2 → (Fin 2 → ℝ) → ℝ, IndepOwn V ∧
      ∀ θ, InBox lo hi θ → ∑ i, E.v i (k θ) (θ i) = ∑ i, V i θ := by
  rintro ⟨V, hV, hdec⟩
  obtain ⟨a1, b1, ha1, hb1, hab1, hlt1⟩ := smallTypeEnv_exists_pair E 0 (hlt 0)
  obtain ⟨a2, b2, ha2, hb2, hab2, hlt2⟩ := smallTypeEnv_exists_pair E 1 (hlt 1)
  have hbox : ∀ x y, x ∈ Set.Icc (lo 0) (hi 0) → y ∈ Set.Icc (lo 1) (hi 1) →
      InBox lo hi ![x, y] := fun x y hx hy => vec2_inBox hx hy
  -- the first-order condition at the corners
  have hfoc : ∀ x y, x ∈ Set.Icc (lo 0) (hi 0) → y ∈ Set.Icc (lo 1) (hi 1) →
      E.vk 0 (k ![x, y]) x + E.vk 1 (k ![x, y]) y = 0 := fun x y hx hy => by
    have := eq_23_C_15 E hk (hbox x y hx hy)
    simpa [Fin.sum_univ_two] using this
  have hne1 : k ![a1, b2] ≠ k ![b1, b2] := by
    intro h
    have e1 := hfoc a1 b2 ha1 hb2
    have e2 := hfoc b1 b2 hb1 hb2
    rw [h] at e1
    have := hlt1 (k ![b1, b2])
    linarith
  have hne2 : k ![b1, a2] ≠ k ![b1, b2] := by
    intro h
    have e1 := hfoc b1 a2 hb1 ha2
    have e2 := hfoc b1 b2 hb1 hb2
    rw [h] at e1
    have := hlt2 (k ![b1, b2])
    linarith
  have hpos := dc_mixed_pos (w1 := E.v 0) (w2 := E.v 1) (κ := fun x y => k ![x, y])
    (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)
    (fun x => by simpa [Fin.sum_univ_two] using hk _ (hbox a1 a2 ha1 ha2) x)
    (fun x hx => by
      simpa [Fin.sum_univ_two] using smallTypeEnv_strict_max E hk (hbox b1 b2 hb1 hb2) hx)
    (dc_delta_monotone (E.hasDerivAt_v 0) hlt1) (dc_delta_monotone (E.hasDerivAt_v 1) hlt2)
    hne1 hne2
  have hd : ∀ x y, x ∈ Set.Icc (lo 0) (hi 0) → y ∈ Set.Icc (lo 1) (hi 1) →
      E.v 0 (k ![x, y]) x + E.v 1 (k ![x, y]) y = V 0 ![x, y] + V 1 ![x, y] :=
    fun x y hx hy => by simpa [Fin.sum_univ_two] using hdec _ (hbox x y hx hy)
  have hV0 : ∀ x x' y, V 0 ![x, y] = V 0 ![x', y] := fun x x' y => by
    rw [← hV 0 ![x', y] x, vec2_update0]
  have hV1 : ∀ x y y', V 1 ![x, y] = V 1 ![x, y'] := fun x y y' => by
    rw [← hV 1 ![x, y'] y, vec2_update1]
  rw [hd b1 b2 hb1 hb2, hd a1 b2 ha1 hb2, hd b1 a2 hb1 ha2, hd a1 a2 ha1 ha2,
    hV0 b1 a1 b2, hV0 b1 a1 a2, hV1 b1 b2 a2, hV1 a1 b2 a2] at hpos
  linarith

/-- **Budget balance in the differentiable case** (MWG, p. 882). With `I = 2`, nondegenerate
type intervals and the small-type assumptions, no social choice function `f = (k*, t)` with an
efficient project rule (23.C.15) and differentiable transfers is strategy-proof and budget
balanced on the box. (Proved through the Groves form and `exercise_23_C_10d`, not through
(23.C.16)-(23.C.17), which need second derivatives that MWG's assumptions do not provide.) -/
theorem differentiable_case_no_budget_balance (E : SmallTypeEnv (Fin 2)) {lo hi : Fin 2 → ℝ}
    (hlt : ∀ i, lo i < hi i) {k : (Fin 2 → ℝ) → ℝ} {t : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hk : EfficientOnBox E.v lo hi k) (ht : ∀ i, Differentiable ℝ fun θ => t θ i)
    (hSP : StrategyProofOnBox E.v lo hi k t) :
    ¬∀ θ, InBox lo hi θ → ∑ i, t θ i = 0 := fun hBB =>
  exercise_23_C_10d E hlt hk
    (exercise_23_C_10c_decomposition (by simp) E hk ht hSP hBB)

/-- The efficient project rule of the quadratic environment, `k*(θ) = ∑ᵢθᵢ/I`. -/
noncomputable def quadK [Fintype ι] (θ : ι → ℝ) : ℝ :=
  (∑ i, θ i) / Fintype.card ι

/-- The quadratic environment's `k*(θ) = ∑ᵢθᵢ/I` satisfies (23.C.7). -/
theorem quadK_efficient [Fintype ι] [Nonempty ι] :
    EfficientProject (quadEnv ι).v (quadK (ι := ι)) := by
  intro θ x
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  simp only [quadEnv, quadK, sum_sub_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul]
  set s := ∑ i, θ i
  set n : ℝ := (Fintype.card ι : ℝ)
  have : 0 ≤ (n * x - s) ^ 2 / (2 * n) := by positivity
  have e : s * (s / n) - n * ((s / n) ^ 2 / 2) - (s * x - n * (x ^ 2 / 2)) =
      (n * x - s) ^ 2 / (2 * n) := by field_simp; ring
  linarith

/-- **The differentiable case**, non-vacuity (MWG, pp. 881-882 and Exercise 23.C.9): in the
quadratic environment the Groves mechanism `tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ)` with
`k*(θ) = ∑ᵢθᵢ/I` is `C¹`, efficient, strategy-proof on any box, has `∂²v/∂k∂θ > 0`, and `k*` is
nondecreasing in each `θᵢ`; so the hypotheses of `eq_23_C_14`, `exercise_23_C_9`,
`differentiable_case_groves` and `differentiable_case_no_budget_balance` (all but budget
balance) are jointly satisfiable. -/
theorem differentiable_case_instance [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lo hi : ι → ℝ) :
    EfficientOnBox (quadEnv ι).v lo hi quadK ∧
      StrategyProofOnBox (quadEnv ι).v lo hi quadK
        (grovesTransfer (quadEnv ι).v quadK fun _ _ => 0) ∧
      ContDiff ℝ 1 (quadK (ι := ι)) ∧
      (∀ i, ContDiff ℝ 1 fun θ => grovesTransfer (quadEnv ι).v quadK (fun _ _ => 0) θ i) ∧
      (∀ i x θ, 0 < (quadEnv ι).vkθ i x θ) ∧
      ∀ i (θ : ι → ℝ), Monotone fun s => quadK (update θ i s) := by
  have hk := quadK_efficient.efficientOnBox (ι := ι) lo hi
  have hcd : ContDiff ℝ 1 (quadK (ι := ι)) := by
    unfold quadK
    fun_prop
  refine ⟨hk, groves_strategyProofOnBox hk fun _ _ _ => rfl, hcd, fun i => ?_,
    fun _ _ _ => one_pos, fun i θ s s' hss' => ?_⟩
  · simp only [grovesTransfer, quadEnv, add_zero]
    exact ContDiff.sum fun j _ => ((contDiff_apply ℝ ℝ j).mul hcd).sub
      ((hcd.pow 2).div_const 2)
  · simp only [quadK]
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [sum_update_split (fun _ x => x), sum_update_split (fun _ x => x)]
    gcongr

end MWG.MechanismDesign
