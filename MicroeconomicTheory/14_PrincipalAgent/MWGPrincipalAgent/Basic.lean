/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Tangent lines and Jensen's inequality for densities

Tools used throughout MWG Chapter 14 (pp. 477-510). MWG appeals to Jensen's inequality
(Section M.C) on pp. 481, 486 and 488; Chapter 6 (risk aversion) is not a dependency of this
project, so the facts needed are proved here.

* `tpa_tangent_le`, `tpa_tangent_lt`: a concave (strictly concave) function lies (strictly)
  below its tangent line; `tpa_tangent_ge_convex`, `tpa_tangent_gt_convex`: the convex versions.
* `tpa_jensen`: `∫ v(w) p dν ≤ v(∫ w p dν)` for a concave differentiable `v` and a probability
  density `p` with respect to an arbitrary measure `ν`.
* `tpa_jensen_eq`: for strictly concave `v`, equality forces `w` to be constant `ν`-a.e.
* `tpa_jensen_two`: the two-point version used in Section 14.C.
-/

namespace MWG.PrincipalAgent

open MeasureTheory Set

/-- A concave function lies below its tangent line: if `h` is concave on `S` and has derivative
`d` within `S` at `x ∈ S`, then `h y ≤ h x + d (y - x)` for `y ∈ S`. -/
theorem tpa_tangent_le {S : Set ℝ} {h : ℝ → ℝ} {x y d : ℝ} (hc : ConcaveOn ℝ S h)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivWithinAt h d S x) : h y ≤ h x + d * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have := hc.slope_le_of_hasDerivWithinAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.le_slope_of_hasDerivWithinAt hy hx hxy hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- A strictly concave function lies strictly below its tangent line away from the point of
tangency. -/
theorem tpa_tangent_lt {S : Set ℝ} {h : ℝ → ℝ} {x y d : ℝ} (hc : StrictConcaveOn ℝ S h)
    (hx : x ∈ S) (hy : y ∈ S) (hne : y ≠ x) (hd : HasDerivWithinAt h d S x) :
    h y < h x + d * (y - x) := by
  rcases lt_or_gt_of_ne hne with hxy | hxy
  · have := hc.lt_slope_of_hasDerivWithinAt hy hx hxy hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
    linarith
  · have := hc.slope_lt_of_hasDerivWithinAt hx hy hxy hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at this
    linarith

/-- A convex function lies above its tangent line. -/
theorem tpa_tangent_ge_convex {S : Set ℝ} {h : ℝ → ℝ} {x y d : ℝ} (hc : ConvexOn ℝ S h)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivWithinAt h d S x) : h x + d * (y - x) ≤ h y := by
  have := tpa_tangent_le hc.neg hx hy hd.neg
  simp only [Pi.neg_apply] at this
  linarith

/-- A strictly convex function lies strictly above its tangent line away from the point of
tangency. -/
theorem tpa_tangent_gt_convex {S : Set ℝ} {h : ℝ → ℝ} {x y d : ℝ} (hc : StrictConvexOn ℝ S h)
    (hx : x ∈ S) (hy : y ∈ S) (hne : y ≠ x) (hd : HasDerivWithinAt h d S x) :
    h x + d * (y - x) < h y := by
  have := tpa_tangent_lt hc.neg hx hy hne hd.neg
  simp only [Pi.neg_apply] at this
  linarith

/-- The tangent-line bound integrated against a density: the integrand of the right side. -/
theorem tpa_tangent_integrable {α : Type*} [MeasurableSpace α] {ν : Measure α} {p w : α → ℝ}
    (hp : Integrable p ν) (hw : Integrable (fun x => w x * p x) ν) (a b m : ℝ) :
    Integrable (fun x => (a + b * (w x - m)) * p x) ν := by
  have : (fun x => (a + b * (w x - m)) * p x) =
      fun x => (a - b * m) * p x + b * (w x * p x) := by
    funext x; ring
  rw [this]
  exact (hp.const_mul _).add (hw.const_mul _)

/-- The integral of the tangent line against a probability density. -/
theorem tpa_tangent_integral {α : Type*} [MeasurableSpace α] {ν : Measure α} {p w : α → ℝ}
    (hp : Integrable p ν) (hp1 : ∫ x, p x ∂ν = 1) (hw : Integrable (fun x => w x * p x) ν)
    (a b m : ℝ) :
    ∫ x, (a + b * (w x - m)) * p x ∂ν = a + b * ((∫ x, w x * p x ∂ν) - m) := by
  have : (fun x => (a + b * (w x - m)) * p x) =
      fun x => (a - b * m) * p x + b * (w x * p x) := by
    funext x; ring
  rw [this, integral_add (hp.const_mul _) (hw.const_mul _), integral_const_mul,
    integral_const_mul, hp1]
  ring

/-- **Jensen's inequality** (MWG, Section M.C; used on pp. 481, 486, 488) for a probability
density `p` with respect to an arbitrary measure `ν` and a concave differentiable `v`:
`∫ v(w) p ≤ v(∫ w p)`. -/
theorem tpa_jensen {α : Type*} [MeasurableSpace α] {ν : Measure α} {p w : α → ℝ}
    {v dv : ℝ → ℝ} (hv : ConcaveOn ℝ univ v) (hdv : ∀ m, HasDerivAt v (dv m) m)
    (hp0 : ∀ x, 0 ≤ p x) (hp : Integrable p ν) (hp1 : ∫ x, p x ∂ν = 1)
    (hw : Integrable (fun x => w x * p x) ν) (hvw : Integrable (fun x => v (w x) * p x) ν) :
    ∫ x, v (w x) * p x ∂ν ≤ v (∫ x, w x * p x ∂ν) := by
  set m := ∫ x, w x * p x ∂ν
  have key : ∀ x, v (w x) * p x ≤ (v m + dv m * (w x - m)) * p x := fun x =>
    mul_le_mul_of_nonneg_right
      (tpa_tangent_le hv (mem_univ _) (mem_univ _) (hdv m).hasDerivWithinAt) (hp0 x)
  calc ∫ x, v (w x) * p x ∂ν ≤ ∫ x, (v m + dv m * (w x - m)) * p x ∂ν :=
        integral_mono hvw (tpa_tangent_integrable hp hw _ _ _) key
    _ = v m := by rw [tpa_tangent_integral hp hp1 hw]; simp [m]

/-- **Strict Jensen** (MWG, pp. 481, 486): for a strictly concave `v` and a density that is
positive everywhere, `∫ v(w) p = v(∫ w p)` only if `w` equals the constant `∫ w p` `ν`-a.e. -/
theorem tpa_jensen_eq {α : Type*} [MeasurableSpace α] {ν : Measure α} {p w : α → ℝ}
    {v dv : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v) (hdv : ∀ m, HasDerivAt v (dv m) m)
    (hp0 : ∀ x, 0 < p x) (hp : Integrable p ν) (hp1 : ∫ x, p x ∂ν = 1)
    (hw : Integrable (fun x => w x * p x) ν) (hvw : Integrable (fun x => v (w x) * p x) ν)
    (heq : ∫ x, v (w x) * p x ∂ν = v (∫ x, w x * p x ∂ν)) :
    ∀ᵐ x ∂ν, w x = ∫ x, w x * p x ∂ν := by
  set m := ∫ x, w x * p x ∂ν
  set G : α → ℝ := fun x => (v m + dv m * (w x - m)) * p x - v (w x) * p x
  have hG0 : 0 ≤ G := fun x => by
    have := mul_le_mul_of_nonneg_right
      (tpa_tangent_le hv.concaveOn (mem_univ m) (mem_univ (w x)) (hdv m).hasDerivWithinAt)
      (hp0 x).le
    change 0 ≤ G x
    simp only [G]; linarith
  have hGi : Integrable G ν := (tpa_tangent_integrable hp hw _ _ _).sub hvw
  have hG : ∫ x, G x ∂ν = 0 := by
    simp only [G]
    rw [integral_sub (tpa_tangent_integrable hp hw _ _ _) hvw,
      tpa_tangent_integral hp hp1 hw, heq]
    simp [m]
  filter_upwards [(integral_eq_zero_iff_of_nonneg hG0 hGi).1 hG] with x hx
  by_contra hne
  have hlt := mul_lt_mul_of_pos_right
    (tpa_tangent_lt hv (mem_univ m) (mem_univ (w x)) hne (hdv m).hasDerivWithinAt) (hp0 x)
  simp only [G, Pi.zero_apply] at hx
  linarith

/-- Two-point Jensen inequality (MWG, Section 14.C, pp. 490-491): for concave `v` and
`0 ≤ λ ≤ 1`, `λ v(a) + (1 - λ) v(b) ≤ v(λ a + (1 - λ) b)`. -/
theorem tpa_jensen_two {v : ℝ → ℝ} (hv : ConcaveOn ℝ univ v) {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (a b : ℝ) : lam * v a + (1 - lam) * v b ≤ v (lam * a + (1 - lam) * b) := by
  have := hv.2 (mem_univ a) (mem_univ b) h0 (by linarith : 0 ≤ 1 - lam) (by ring)
  simpa [smul_eq_mul] using this

/-- Strict two-point Jensen inequality: if `v` is strictly concave, `0 < λ < 1` and `a ≠ b`. -/
theorem tpa_jensen_two_lt {v : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) {a b : ℝ} (hab : a ≠ b) :
    lam * v a + (1 - lam) * v b < v (lam * a + (1 - lam) * b) := by
  have := hv.2 (mem_univ a) (mem_univ b) hab h0 (by linarith : 0 < 1 - lam) (by ring)
  simpa [smul_eq_mul] using this

end MWG.PrincipalAgent
