/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Tools
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# General versus partial equilibrium: a tax incidence example (MWG Section 15.E, pp. 538-540)

`N` towns, each with one price-taking firm with production function `f`; `M` units of labor move
freely between towns; the consumption good is the numeraire. Town 1 taxes labor at rate `t`.

* p. 539: without the tax the equilibrium has `z = M/N` in every town and `w̄ = f'(M/N)`
  (`no_tax_eqm`, unique when `f'` is strictly decreasing).
* The partial equilibrium view: with the wage fixed at `w̄`, town 1's employment falls
  (`partial_eqm_employment_falls`).
* (15.E.1)-(15.E.5): along any differentiable path of general equilibria `w'(0) = -1/N` and
  `z'(0) = -1/(N f''(M/N))` (`general_eqm_wage_derivative`); the wage effect vanishes as `N → ∞`
  (`wage_effect_vanishes`).
* p. 540, footnote 17: aggregate profits `(N - 1)π(w(t)) + π(w(t) + t)` have zero derivative at
  `t = 0` (`aggregate_profit_derivative`): the burden of a small tax falls on labor, whose income
  falls at the rate at which tax revenue rises (`labor_bears_burden`).
* An instance: the quadratic technology `f(z) = a z - b z²/2` has explicit equilibrium paths
  (`quadratic_eqm_path`).
-/

namespace MWG.GeneralEquilibriumExamples

open Filter Topology

/-- **Section 15.E** (MWG, p. 539). The general equilibrium conditions (15.E.1)-(15.E.3) at tax
rate `t` in town 1, for the common wage `w`, the employment `z` of each untaxed firm and the
employment `z₁` of the taxed firm (with marginal product `f'`). -/
def IsTaxEqm (f' : ℝ → ℝ) (N M t w z z₁ : ℝ) : Prop :=
  (N - 1) * z + z₁ = M ∧ f' z = w ∧ f' z₁ = w + t

/-- **Section 15.E** (MWG, p. 539). Without the tax, `z = z₁ = M/N` and `w̄ = f'(M/N)` is an
equilibrium; if `f'` is strictly decreasing (strictly concave `f`) it is the only one. -/
theorem no_tax_eqm {f' : ℝ → ℝ} {N M : ℝ} (hN : 0 < N) :
    IsTaxEqm f' N M 0 (f' (M / N)) (M / N) (M / N) ∧
      (StrictAnti f' → ∀ w z z₁, IsTaxEqm f' N M 0 w z z₁ →
        z = M / N ∧ z₁ = M / N ∧ w = f' (M / N)) := by
  refine ⟨⟨by field_simp; ring, rfl, by ring⟩, fun hf w z z₁ ⟨h1, h2, h3⟩ => ?_⟩
  have hzz : z = z₁ := hf.injective (by rw [h2, h3, add_zero])
  have hz : z = M / N := by
    rw [eq_div_iff hN.ne']
    rw [← hzz] at h1
    linarith
  exact ⟨hz, hzz ▸ hz, by rw [← h2, hz]⟩

/-- **Section 15.E** (MWG, p. 539). The partial equilibrium view: with the wage in town 1 held at
`w̄`, the taxed firm's labor demand `z₁` solves `f'(z₁) = t + w̄`; for `t > 0` and `f'` strictly
decreasing, it falls below `M/N`. -/
theorem partial_eqm_employment_falls {f' : ℝ → ℝ} (hf : StrictAnti f') {N M t z₁ : ℝ}
    (ht : 0 < t) (h : f' z₁ = t + f' (M / N)) : z₁ < M / N := by
  by_contra hle
  rw [not_lt] at hle
  have := hf.antitone hle
  linarith

/-- **(15.E.4)-(15.E.5)** (MWG, p. 539). Let `w, z, z₁` be paths of general equilibria (15.E.1)-
(15.E.3) for small taxes `t`, differentiable at `t = 0` with `z(0) = z₁(0) = M/N`, and let `f'` be
differentiable at `M/N` with `f''(M/N) ≠ 0`. Then `w'(0) = -1/N` and `z'(0) = -1/(N f''(M/N))`. -/
theorem general_eqm_wage_derivative {f' : ℝ → ℝ} {f'' N M : ℝ} (hN : 0 < N)
    (hf' : HasDerivAt f' f'' (M / N)) (hf'' : f'' ≠ 0) {w z z₁ : ℝ → ℝ} {w' z' z₁' : ℝ}
    (hw : HasDerivAt w w' 0) (hz : HasDerivAt z z' 0) (hz₁ : HasDerivAt z₁ z₁' 0)
    (hz0 : z 0 = M / N) (hz₁0 : z₁ 0 = M / N)
    (heq : ∀ᶠ t in 𝓝 (0 : ℝ), IsTaxEqm f' N M t (w t) (z t) (z₁ t)) :
    w' = -1 / N ∧ z' = -1 / (N * f'') := by
  -- differentiate (15.E.1)
  have h1 : (N - 1) * z' + z₁' = 0 := by
    have hd := (hz.const_mul (N - 1)).add hz₁
    have hc : HasDerivAt (fun t => (N - 1) * z t + z₁ t) 0 0 :=
      (hasDerivAt_const (0 : ℝ) M).congr_of_eventuallyEq
        (heq.mono fun t ht => ht.1)
    exact hd.unique hc
  -- differentiate (15.E.2)
  have h2 : f'' * z' = w' := by
    have hd := HasDerivAt.comp (0 : ℝ) (by rwa [hz0]) hz
    have hc : HasDerivAt (f' ∘ z) w' 0 := hw.congr_of_eventuallyEq (heq.mono fun t ht => ht.2.1)
    exact hd.unique hc
  -- differentiate (15.E.3)
  have h3 : f'' * z₁' = w' + 1 := by
    have hd := HasDerivAt.comp (0 : ℝ) (by rwa [hz₁0]) hz₁
    have hc : HasDerivAt (f' ∘ z₁) (w' + 1) 0 :=
      (hw.add (hasDerivAt_id (0 : ℝ))).congr_of_eventuallyEq
        (heq.mono fun t ht => by simp [ht.2.2])
    exact hd.unique hc
  -- (15.E.4): `-f''(N - 1) z' = w' + 1`, and (15.E.5)
  have hw' : w' = -1 / N := by
    rw [eq_div_iff hN.ne']
    have : z₁' = -((N - 1) * z') := by linarith
    rw [this] at h3
    nlinarith
  refine ⟨hw', ?_⟩
  have h4 : f'' * z' * N = -1 := by rw [h2, hw']; field_simp
  rw [eq_div_iff (mul_ne_zero hN.ne' hf'')]
  linear_combination h4

/-- **Section 15.E** (MWG, p. 540). The general equilibrium fall in the wage, `-1/N`, vanishes as
the number of towns grows. -/
theorem wage_effect_vanishes : Tendsto (fun N : ℕ => -1 / (N : ℝ)) atTop (𝓝 0) := by
  have := (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop
    (𝓝 0)).neg
  rw [neg_zero] at this
  convert this using 2 with n
  ring

/-- **Section 15.E** (MWG, p. 540, footnote 17). Let `π` be the profit function of a firm,
differentiable at `w̄ = w(0)`, and let `w'(0) = -1/N`. Aggregate profits
`(N - 1)π(w(t)) + π(w(t) + t)` (the taxed firm's profit is `π(w(t) + t)`) have derivative
`(N - 1)π'(w̄)w'(0) + π'(w̄)(w'(0) + 1) = π'(w̄)(-(N-1)/N + (N-1)/N) = 0` at `t = 0`. -/
theorem aggregate_profit_derivative {π₀ w : ℝ → ℝ} {π' N : ℝ} (hN : 0 < N)
    (hπ : HasDerivAt π₀ π' (w 0)) (hw : HasDerivAt w (-1 / N) 0) :
    HasDerivAt (fun t => (N - 1) * π₀ (w t) + π₀ (w t + t)) 0 0 ∧
      (N - 1) * π' * (-1 / N) + π' * (-1 / N + 1) = π' * (-(N - 1) / N + (N - 1) / N) := by
  have h1 := (HasDerivAt.comp (0 : ℝ) hπ hw).const_mul (N - 1)
  have h2 := HasDerivAt.comp (0 : ℝ) (by simpa using hπ) (hw.add (hasDerivAt_id (0 : ℝ)))
  have hsum := h1.add h2
  refine ⟨?_, by field_simp; ring⟩
  convert hsum using 1
  · funext t
    simp
  · field_simp
    ring

/-- **Section 15.E** (MWG, p. 540). At the margin labor bears the whole tax: labor income `M w(t)`
falls at the rate `M/N` at which tax revenue `t z₁(t)` rises (`z₁(0) = M/N`). -/
theorem labor_bears_burden {w z₁ : ℝ → ℝ} {z₁' N M : ℝ} (hN : 0 < N)
    (hw : HasDerivAt w (-1 / N) 0) (hz₁ : HasDerivAt z₁ z₁' 0) (hz₁0 : z₁ 0 = M / N) :
    HasDerivAt (fun t => M * w t) (-(M / N)) 0 ∧ HasDerivAt (fun t => t * z₁ t) (M / N) 0 := by
  constructor
  · convert hw.const_mul M using 1
    field_simp
  · convert (hasDerivAt_id (0 : ℝ)).mul hz₁ using 1
    · rfl
    · rw [hz₁0]
      simp

/-- **Section 15.E** (MWG, pp. 539-540), an instance. With the quadratic technology
`f(z) = a z - b z²/2` (`b > 0`, marginal product `f'(z) = a - b z`), the paths
`z(t) = (M + t/b)/N`, `z₁(t) = z(t) - t/b`, `w(t) = a - b z(t)` are general equilibria for every
`t`, with `w'(0) = -1/N`, and `z(0) = z₁(0) = M/N`. -/
theorem quadratic_eqm_path {a b N M : ℝ} (hb : 0 < b) (hN : 0 < N) :
    (∀ t, IsTaxEqm (fun z => a - b * z) N M t (a - b * ((M + t / b) / N)) ((M + t / b) / N)
      ((M + t / b) / N - t / b)) ∧
    HasDerivAt (fun t => a - b * ((M + t / b) / N)) (-1 / N) 0 ∧
    (M + 0 / b) / N = M / N ∧ (M + 0 / b) / N - 0 / b = M / N := by
  refine ⟨fun t => ⟨?_, rfl, ?_⟩, ?_, by simp, by simp⟩
  · field_simp; ring
  · field_simp; ring
  · have h := ((((hasDerivAt_id (0 : ℝ)).div_const b).const_add M).div_const N).const_mul b
    have h2 := h.const_sub a
    convert h2 using 1
    · funext t
      simp
    · field_simp

end MWG.GeneralEquilibriumExamples
