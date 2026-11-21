/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Screen
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real

/-!
# The monopolistic screening model

MWG, Section 14.C (small type), pp. 500-501, problem (14.C.10).

The firm offers wage-task pairs `(w_i, t_i)` to workers of types `θ_H > θ_L > 0` with utility
`w - g(t, θ)` and reservation utility `ū`; its profit from a type-`θ_i` worker is `π_i(t) - w`.
Problem (14.C.10) is the program `Screen` with `c = ū`, so all results of `Screen` apply.

* `footnote_21_misprint`: MWG's example `π_i(t) = θ_i (1 - μt)` (p. 500) violates the stated
  assumption `π'_H(t) ≥ π'_L(t) > 0`; the intended `θ_i (1 + μt)` of Exercise 13.D.1 satisfies it
  (`footnote_21_corrected`), and tends to `θ_i` as `μ → 0` (footnote 21, `footnote_21_limit`).
* `maskin_riley`: the Maskin-Riley monopolist (p. 500) is (14.C.10) with `t_i = x_i`, `w_i = -T_i`,
  `ū = 0`, `g(t, θ) = -v(t, θ)`, `π_i(t) = -c t`.
* `baron_myerson`: the Baron-Myerson regulator (p. 501) is (14.C.10) with `t_i = p_i`, `w_i = T_i`,
  `ū = 0`, `g(t, θ) = -(t - θ) x(t)` and `π_i(t)` the consumer surplus at price `t`.
-/

namespace MWG.PrincipalAgent

open Filter Topology

/-- **Footnote 21 / p. 500, misprint.** For `μ > 0` and `θ_H > θ_L > 0`, the profit functions
`π_i(t) = θ_i (1 - μ t)` printed on p. 500 have `π'_i = -θ_i μ < 0` and `π'_H < π'_L`, violating the
assumption `π'_H(t) ≥ π'_L(t) > 0` they are meant to illustrate. -/
theorem footnote_21_misprint {θL θH μ : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hμ : 0 < μ) (t : ℝ) :
    HasDerivAt (fun t => θL * (1 - μ * t)) (-(θL * μ)) t ∧
      HasDerivAt (fun t => θH * (1 - μ * t)) (-(θH * μ)) t ∧
      -(θL * μ) < 0 ∧ -(θH * μ) < -(θL * μ) := by
  refine ⟨?_, ?_, by nlinarith, by nlinarith⟩
  · have := (((hasDerivAt_id t).const_mul μ).const_sub 1).const_mul θL
    simpa using this
  · have := (((hasDerivAt_id t).const_mul μ).const_sub 1).const_mul θH
    simpa using this

/-- **Footnote 21, corrected** (Exercise 13.D.1): `π_i(t) = θ_i (1 + μ t)` has
`π'_H = θ_H μ ≥ π'_L = θ_L μ > 0`. -/
theorem footnote_21_corrected {θL θH μ : ℝ} (hL : 0 < θL) (hLH : θL < θH) (hμ : 0 < μ) (t : ℝ) :
    HasDerivAt (fun t => θL * (1 + μ * t)) (θL * μ) t ∧
      HasDerivAt (fun t => θH * (1 + μ * t)) (θH * μ) t ∧ 0 < θL * μ ∧ θL * μ ≤ θH * μ := by
  refine ⟨?_, ?_, by positivity, by nlinarith⟩
  · have := (((hasDerivAt_id t).const_mul μ).const_add 1).const_mul θL
    simpa using this
  · have := (((hasDerivAt_id t).const_mul μ).const_add 1).const_mul θH
    simpa using this

/-- **Footnote 21** (MWG, p. 500): the Section 13.D model `π_i(t) = θ_i` is the limit `μ → 0`. -/
theorem footnote_21_limit (θ t : ℝ) :
    Tendsto (fun μ : ℝ => θ * (1 + μ * t)) (𝓝 0) (𝓝 θ) := by
  have : Tendsto (fun μ : ℝ => θ * (1 + μ * t)) (𝓝 0) (𝓝 (θ * (1 + 0 * t))) :=
    ((tendsto_id.mul_const t).const_add 1).const_mul θ
  simpa using this

/-- **Maskin and Riley (1984b)** (MWG, p. 500). A consumer of type `θ` buying `x` units for a
payment `T` gets `v(x, θ) - T`, and `0` by not buying; the monopolist with unit cost `c` offers
`(x_i, T_i)`. Its profit and the consumers' participation and self-selection constraints are those
of (14.C.10) with `t_i = x_i`, `w_i = -T_i`, `ū = 0`, `g(t, θ) = -v(t, θ)`, `π_i(t) = -c t`. -/
theorem maskin_riley (vx : ℝ → ℝ → ℝ) (cost θL θH lam xH TH xL TL : ℝ) :
    let P : Screen := ⟨fun t => -cost * t, fun t => -cost * t, fun t θ => -vx t θ, θL, θH, lam, 0⟩
    let K : HIContract := ⟨-TH, xH, -TL, xL⟩
    P.Pi K = lam * (TH - cost * xH) + (1 - lam) * (TL - cost * xL) ∧
    (P.Feas K ↔ 0 ≤ xH ∧ 0 ≤ xL ∧ 0 ≤ vx xL θL - TL ∧ 0 ≤ vx xH θH - TH ∧
      vx xL θH - TL ≤ vx xH θH - TH ∧ vx xH θL - TH ≤ vx xL θL - TL) := by
  intro P K
  refine ⟨by simp only [P, K, Screen.Pi]; ring, ?_⟩
  simp only [Screen.Feas, Screen.C1, Screen.C2, Screen.C3, Screen.C4, P, K]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, by linarith, by linarith, by linarith,
      by linarith⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, by linarith, by linarith, by linarith,
      by linarith⟩

/-- **Baron and Myerson (1982)** (MWG, p. 501). A regulated monopolist with unit cost `θ` facing
demand `x(p)` is offered price-transfer pairs `(p_i, T_i)`; it earns `(p - θ) x(p) + T` and can shut
down (earning `0`); the regulator maximizes consumer surplus `CS(p) - T` (`CS(p) = ∫_p^∞ x`). This
is (14.C.10) with `t_i = p_i`, `w_i = T_i`, `ū = 0`, `g(t, θ) = -(t - θ) x(t)`, `π_i(t) = CS(t)`. -/
theorem baron_myerson (x CS : ℝ → ℝ) (θL θH lam pH TH pL TL : ℝ) :
    let P : Screen := ⟨CS, CS, fun t θ => -((t - θ) * x t), θL, θH, lam, 0⟩
    let K : HIContract := ⟨TH, pH, TL, pL⟩
    P.Pi K = lam * (CS pH - TH) + (1 - lam) * (CS pL - TL) ∧
    (P.Feas K ↔ 0 ≤ pH ∧ 0 ≤ pL ∧ 0 ≤ (pL - θL) * x pL + TL ∧ 0 ≤ (pH - θH) * x pH + TH ∧
      (pL - θH) * x pL + TL ≤ (pH - θH) * x pH + TH ∧
      (pH - θL) * x pH + TH ≤ (pL - θL) * x pL + TL) := by
  intro P K
  refine ⟨by simp only [P, K, Screen.Pi], ?_⟩
  simp only [Screen.Feas, Screen.C1, Screen.C2, Screen.C3, Screen.C4, P, K]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, by linarith, by linarith, by linarith,
      by linarith⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, by linarith, by linarith, by linarith,
      by linarith⟩

end MWG.PrincipalAgent
